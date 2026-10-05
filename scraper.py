#!/usr/bin/env python3
"""
Toolify category -> tool websites -> Discord invite links.

Walks a page range of a Toolify category, collects the external tool links (the
<a> wrapping each "Try ..." button div), opens every tool site in Chrome, waits
for it to finish loading (including any Cloudflare check) and extracts the
Discord server invite links found on it.

The range starts at the ?page= of the URL (1 if absent) and ends at <end-page>:
    python scraper.py "https://www.toolify.ai/category/ai-writing-assistants?page=5" 17
    python scraper.py <category-url> <end-page> -o links.txt --csv report.csv -c 6

The invite links are written to output.txt, one per line. An existing output.txt
is kept: links already in it are skipped, new ones are appended.

Status shown per site (and in the --csv report):
    ok                  page loaded and was scanned
    load_timeout        page was scanned, but had not finished loading after --timeout seconds
    no_response / load_error / error: ...   page could not be opened (dead domain, network error)
    cloudflare_failed   Cloudflare's check was not passed within --cf-timeout seconds
    cloudflare_blocked  Cloudflare refused the visit outright
Sites that fail to load are retried once in a fresh browser before they are reported.

Chrome is driven through nodriver (plain CDP, no webdriver), which is what lets
it pass Cloudflare. Headless Chrome does not pass, so the browser runs as a
normal window that is kept out of sight: on Linux on a private virtual screen
(Xvfb), on Windows positioned far off-screen (only a taskbar button shows).
It uses a throwaway profile that is deleted on exit, so no history is kept.
Pass --show to watch the browser on the real screen instead.
"""

import argparse
import asyncio
import csv
import json
import os
import random
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

import nodriver as uc
from nodriver import cdp

# The "Try <tool>" button on a Toolify category page; the link we want is the <a> around it.
TRY_BUTTON_CLASS = "cursor-pointer flex-shrink-0 px-6 py-2 text-base flex items-center justify-center"

INVITE_RE = re.compile(
    r"(?:https?://)?(?:www\.|ptb\.|canary\.)?"
    r"(?:discord\.gg(?:/invite)?|discord(?:app)?\.com/invite)/([A-Za-z0-9-]{2,})",
    re.I,
)
DISCORD_HOSTS = ("discord.com", "discordapp.com", "discord.gg")

# Keeps background tabs running at full speed so pages (and Cloudflare checks) finish
# loading while other tabs are in front.
BROWSER_ARGS = [
    "--disable-background-timer-throttling",
    "--disable-backgrounding-occluded-windows",
    "--disable-renderer-backgrounding",
    "--window-size=1366,900",
    "--mute-audio",
]

PAGE_STATE_JS = """
(() => {
  const title = document.title || '';
  // _cf_chl_opt alone is not enough: Cloudflare also defines it (without cType) on normal pages.
  const opt = window._cf_chl_opt;
  const challenge = !!(opt && (opt.cType || opt.cRay))
    || !!document.querySelector('#challenge-form, #challenge-running, #challenge-stage, #challenge-error-text')
    || /^just a moment/i.test(title);
  const blocked = !challenge && !!document.querySelector('#cf-error-details')
    && /attention required|access denied|you have been blocked/i.test(title + ' ' + document.body.innerText.slice(0, 400));
  return JSON.stringify({ready: document.readyState, url: location.href, challenge, blocked});
})()
"""

LISTING_JS = """
(() => {
  const selector = 'div.' + %s.trim().split(/\\s+/).map(c => CSS.escape(c)).join('.');
  const tools = [];
  for (const div of document.querySelectorAll(selector)) {
    const a = div.closest('a[href]');
    if (a && /^https?:/i.test(a.href)) tools.push({name: div.innerText.trim().replace(/^Try\\s+/i, ''), url: a.href});
  }
  return JSON.stringify(tools);
})()
""" % json.dumps(TRY_BUTTON_CLASS)

EXTRACT_JS = """
(() => {
  const RE = /(?:https?:\\/\\/)?(?:www\\.|ptb\\.|canary\\.)?(?:discord\\.gg(?:\\/invite)?|discord(?:app)?\\.com\\/invite)\\/[A-Za-z0-9-]{2,}/gi;
  const invites = new Set(), candidates = new Set();
  const roots = [document];
  for (let i = 0; i < roots.length; i++)
    for (const el of roots[i].querySelectorAll('*')) if (el.shadowRoot) roots.push(el.shadowRoot);
  for (const root of roots) {
    for (const a of root.querySelectorAll('a[href]')) {
      const href = a.href || '';
      const hit = href.match(RE);
      if (hit) { hit.forEach(h => invites.add(h)); continue; }
      if (!/^https?:/i.test(href)) continue;
      // Links like example.com/discord that only redirect to the invite.
      const text = (a.textContent || '').trim();
      const label = [text.length < 60 ? text : '', a.getAttribute('aria-label'), a.title,
        ...[...a.querySelectorAll('img[alt], svg title')].map(n => n.getAttribute('alt') || n.textContent)].join(' ');
      if (/discord/i.test(href) || /discord/i.test(label)) candidates.add(href);
    }
  }
  // Raw markup catches invites outside <a> tags (buttons, onclick handlers, embedded JSON).
  const html = document.documentElement.outerHTML.replace(/\\\\u002F/gi, '/').replace(/\\\\\\//g, '/');
  for (const m of html.matchAll(RE)) invites.add(m[0]);
  return JSON.stringify({invites: [...invites], candidates: [...candidates]});
})()
"""

SCROLL_JS = "window.scrollTo(0, document.documentElement.scrollHeight * %f)"

PAGE_ATTEMPTS = 3  # tries per Toolify listing page before it is skipped
UNHEALTHY_STREAK = 10  # this many failed sites in a row means the browser, not the sites, is the problem


def log(msg):
    print(msg, flush=True)


def page_url(base_url, page):
    parts = urlsplit(base_url)
    query = [(k, v) for k, v in parse_qsl(parts.query, keep_blank_values=True) if k != "page"]
    query.append(("page", str(page)))
    return urlunsplit(parts._replace(query=urlencode(query)))


def normalize_invites(raw_links):
    """Give every invite an https:// scheme and drop duplicates of the same invite code."""
    seen, out = set(), []
    for raw in raw_links:
        m = INVITE_RE.search(raw)
        if not m or m.group(1) in seen:
            continue
        seen.add(m.group(1))
        out.append("https://" + re.sub(r"^https?://", "", m.group(0), flags=re.I))
    return out


def start_page(url):
    """Page number in the URL's ?page= parameter (1 when there is none)."""
    values = [v for k, v in parse_qsl(urlsplit(url).query, keep_blank_values=True) if k == "page"]
    return int(values[-1]) if values else 1


def start_virtual_display():
    """Start a private Xvfb screen and point Chrome at it, so no window shows on the desktop."""
    if not shutil.which("Xvfb"):
        sys.exit("Xvfb is needed to run without a visible browser (sudo apt install xvfb), or pass --show.")
    read_fd, write_fd = os.pipe()
    xvfb = subprocess.Popen(
        ["Xvfb", "-displayfd", str(write_fd), "-screen", "0", "1440x1000x24", "-nolisten", "tcp"],
        pass_fds=[write_fd], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    os.close(write_fd)
    with os.fdopen(read_fd) as pipe:
        display = pipe.readline().strip()
    if not display:
        sys.exit("Could not start Xvfb.")
    os.environ["DISPLAY"] = f":{display}"
    os.environ.pop("WAYLAND_DISPLAY", None)
    return xvfb


async def js(tab, expression, timeout=15):
    """Evaluate JS in the tab and return its value, or None if the page is mid-navigation."""
    try:
        result, errors = await asyncio.wait_for(
            tab.send(cdp.runtime.evaluate(expression=expression, return_by_value=True)), timeout
        )
    except Exception:
        return None
    if errors or result is None:
        return None
    return result.value


async def page_state(tab):
    raw = await js(tab, PAGE_STATE_JS, timeout=5)
    return json.loads(raw) if raw else None


async def navigate(tab, url):
    """Start a navigation; returns Chrome's error text (e.g. net::ERR_NAME_NOT_RESOLVED) or None."""
    try:
        result = await asyncio.wait_for(tab.send(cdp.page.navigate(url)), 30)
    except asyncio.TimeoutError:
        return None
    return result[2] if result and len(result) > 2 else None


async def click_turnstile(tab):
    """Click the Cloudflare "Verify you are human" checkbox if the challenge is showing one."""
    try:
        doc = await asyncio.wait_for(tab.send(cdp.dom.get_document(depth=-1, pierce=True)), 10)
        stack, frame = [doc], None
        while stack and frame is None:
            node = stack.pop()
            if node.node_name == "IFRAME" and node.attributes:
                attrs = dict(zip(node.attributes[::2], node.attributes[1::2]))
                if "challenges.cloudflare.com" in attrs.get("src", ""):
                    frame = node
            stack.extend(node.children or [])
            stack.extend(node.shadow_roots or [])
            if node.content_document:
                stack.append(node.content_document)
        if frame is None:
            return False
        quad = (await tab.send(cdp.dom.get_box_model(node_id=frame.node_id))).content
        width, height = quad[2] - quad[0], quad[5] - quad[1]
        if width < 100 or height < 30:  # hidden / non-interactive widget, nothing to click
            return False
        x = quad[0] + 28 + random.uniform(-3, 3)
        y = quad[1] + height / 2 + random.uniform(-3, 3)
        await tab.bring_to_front()
        for step in range(1, 9):
            await tab.send(cdp.input_.dispatch_mouse_event("mouseMoved", x=x * step / 8, y=y * step / 8))
            await asyncio.sleep(random.uniform(0.02, 0.06))
        await tab.mouse_click(x, y)
        return True
    except Exception:
        return False


async def wait_until_loaded(tab, timeout, cf_timeout):
    """
    Wait for the page to finish loading, sitting through any Cloudflare challenge first.
    Returns 'ok', 'load_timeout' (page answers but never finished loading), 'no_response'
    (page never answered at all), 'load_error', 'cloudflare_failed' or 'cloudflare_blocked'.
    """
    deadline = time.monotonic() + timeout
    cf_since = last_click = None
    responded = False
    while True:
        now = time.monotonic()
        state = await page_state(tab)
        responded = responded or state is not None
        if state and state["challenge"]:
            if cf_since is None:
                cf_since = now
            if now - cf_since > cf_timeout:
                return "cloudflare_failed"
            # Most challenges clear on their own in a real browser; only click if it lingers.
            if now - cf_since > 5 and (last_click is None or now - last_click > 8):
                if await click_turnstile(tab):
                    last_click = now
        else:
            if cf_since is not None:  # challenge just cleared, the real page is loading now
                cf_since = None
                deadline = now + timeout
            if state and state["blocked"]:
                return "cloudflare_blocked"
            if state and state["url"].startswith("chrome-error://"):
                return "load_error"
            if state and state["ready"] == "complete" and state["url"] != "about:blank":
                return "ok"
            if now > deadline:
                return "load_timeout" if responded else "no_response"
        await asyncio.sleep(0.5)


async def extract(tab):
    raw = await js(tab, EXTRACT_JS)
    data = json.loads(raw) if raw else {"invites": [], "candidates": []}
    return normalize_invites(data["invites"]), data["candidates"]


def rank_candidates(candidates, current_url):
    """Redirect-style links worth following, most promising first."""
    out = []
    for url in candidates:
        parts = urlsplit(url)
        host = parts.netloc.lower()
        if host.endswith(DISCORD_HOSTS) or url.split("#")[0] == current_url.split("#")[0]:
            continue  # non-invite discord.com pages never turn into invites
        out.append(url)
    looks_like_redirect = lambda u: not (
        urlsplit(u).path.rstrip("/").lower().endswith("discord") or "discord" in urlsplit(u).netloc.lower()
    )
    return sorted(dict.fromkeys(out), key=lambda u: (looks_like_redirect(u), len(u)))


async def resolve_candidate(tab, url, timeout=12):
    """Follow a link like example.com/discord and report the invite it lands on, if any."""
    await navigate(tab, url)
    deadline = time.monotonic() + timeout
    settled_since = None
    while time.monotonic() < deadline:
        state = await page_state(tab)
        if state:
            if INVITE_RE.search(state["url"]):
                return normalize_invites([state["url"]])
            if state["ready"] == "complete" and not state["challenge"]:
                settled_since = settled_since or time.monotonic()
                if time.monotonic() - settled_since > 2.5:
                    return (await extract(tab))[0]  # no redirect; maybe a community page
            else:
                settled_since = None
        await asyncio.sleep(0.5)
    return []


async def collect_tools(browser, base_url, first_page, last_page, args):
    tab = await browser.get("about:blank")
    tools, seen, skipped = [], set(), []
    for page in range(first_page, last_page + 1):
        url = page_url(base_url, page)
        found = []
        for attempt in range(1, PAGE_ATTEMPTS + 1):
            await navigate(tab, url)
            status = await wait_until_loaded(tab, args.timeout, args.cf_timeout)
            deadline = time.monotonic() + 15
            while status == "ok" and not found and time.monotonic() < deadline:
                found = json.loads(await js(tab, LISTING_JS) or "[]")
                if not found:
                    await asyncio.sleep(0.5)
            if found:
                break
            if attempt < PAGE_ATTEMPTS:
                log(f"[page {page}] no tool links ({status}), retrying ({attempt}/{PAGE_ATTEMPTS})")
                if status != "ok":
                    await asyncio.sleep(5 * attempt)  # load errors are usually a brief network drop
        if not found:
            log(f"[page {page}] no tool links ({status}) after {PAGE_ATTEMPTS} attempts, skipping this page")
            skipped.append(page)
            continue
        new = 0
        for tool in found:
            if tool["url"] not in seen:
                seen.add(tool["url"])
                tools.append({"page": page, **tool})
                new += 1
        log(f"[page {page}] {len(found)} tool links ({new} new)")
        await asyncio.sleep(random.uniform(1.0, 2.5))
    if skipped:
        log(f"Pages skipped because they never loaded: {', '.join(map(str, skipped))}")
    return tools


async def scrape_site(browser, tool, args):
    result = {**tool, "final_url": "", "status": "", "discord_invites": []}
    tab = await browser.get("about:blank", new_tab=True)
    try:
        await tab.send(cdp.page.enable())

        async def dismiss_dialog(event):  # alert()/confirm() would otherwise freeze the page
            try:
                await tab.send(cdp.page.handle_java_script_dialog(accept=False))
            except Exception:
                pass

        tab.add_handler(cdp.page.JavascriptDialogOpening, dismiss_dialog)

        error = await navigate(tab, tool["url"])
        if error and "ERR_ABORTED" not in error:
            result["status"] = f"error: {error}"
            return result
        status = await wait_until_loaded(tab, args.timeout, args.cf_timeout)
        result["status"] = status
        state = await page_state(tab)
        result["final_url"] = state["url"] if state else ""
        if status.startswith("cloudflare") or status in ("load_error", "no_response"):
            return result

        await asyncio.sleep(2)  # let client-side rendering settle
        invites, candidates = await extract(tab)
        if not invites:
            # Footers (where the Discord icon usually lives) are often lazy-rendered on scroll.
            for fraction in (0.25, 0.5, 0.75, 1.0):
                await js(tab, SCROLL_JS % fraction)
                await asyncio.sleep(0.5)
            await asyncio.sleep(1)
            invites, more = await extract(tab)
            candidates += more
        if not invites:
            for candidate in rank_candidates(candidates, result["final_url"])[:3]:
                invites = await resolve_candidate(tab, candidate)
                if invites:
                    break
        result["discord_invites"] = invites
        return result
    finally:
        try:
            await tab.close()
        except Exception:
            pass


RUNNING_BROWSERS = set()  # pids of the Chrome instances currently open


async def launch_browser(profile_root):
    browser = await uc.start(
        user_data_dir=tempfile.mkdtemp(dir=profile_root),
        browser_args=BROWSER_ARGS,
        sandbox=os.geteuid() != 0 if hasattr(os, "geteuid") else True,
    )
    RUNNING_BROWSERS.add(browser._process_pid)
    return browser


async def close_browser(browser):
    pid = browser._process_pid
    browser.stop()
    await asyncio.sleep(2)
    RUNNING_BROWSERS.discard(pid)


def settled(result):
    """True when the visit gave a trustworthy answer and needs no second try."""
    return bool(result["discord_invites"]) or result["status"] in ("ok", "cloudflare_blocked")


async def scrape_batch(browser, batch, args, record):
    """
    Visit a batch of (tool, attempt) pairs in one browser. Settled results go straight to
    record(); the pairs worth another try in a fresh browser are returned.
    """
    semaphore = asyncio.Semaphore(args.concurrency)
    unsettled, skipped = [], []
    streak = 0  # failures in a row; a long streak means the browser itself has gone bad

    async def worker(tool, attempt):
        nonlocal streak
        async with semaphore:
            if streak >= UNHEALTHY_STREAK:
                skipped.append((tool, attempt))
                return
            try:
                result = await asyncio.wait_for(
                    scrape_site(browser, tool, args), args.timeout * 2 + args.cf_timeout + 60
                )
            except Exception as exc:
                result = {**tool, "final_url": "", "status": f"error: {type(exc).__name__}", "discord_invites": []}
            if settled(result):
                streak = 0
                record(result)
            else:
                streak += 1
                unsettled.append((tool, attempt, result))

    await asyncio.gather(*(worker(tool, attempt) for tool, attempt in batch))

    browser_went_bad = streak >= UNHEALTHY_STREAK
    if browser_went_bad:
        log("  browser stopped responding, restarting it")
    retry = skipped
    for tool, attempt, result in unsettled:
        # A lone load_timeout is just a slow site (it was scanned anyway); in a bad browser it means nothing.
        if attempt < 2 and (browser_went_bad or result["status"] != "load_timeout"):
            retry.append((tool, attempt + 1))
        else:
            record(result)
    return retry


async def run(args, profile_root):
    browser = await launch_browser(profile_root)
    try:
        tools = await collect_tools(browser, args.url, args.first_page, args.end_page, args)
    finally:
        await close_browser(browser)
    log(f"\n{len(tools)} tool sites to visit\n")

    # One invite link per line. Links already in the file are kept and never written twice.
    existing = ""
    if os.path.exists(args.output):
        with open(args.output, encoding="utf-8") as f:
            existing = f.read()
    written = {m.group(1) for m in INVITE_RE.finditer(existing)}
    already = len(written)
    out = open(args.output, "a", encoding="utf-8")
    if existing and not existing.endswith("\n"):
        out.write("\n")
    report = writer = None
    if args.csv:
        report = open(args.csv, "w", newline="", encoding="utf-8")
        writer = csv.writer(report)
        writer.writerow(["page", "tool", "tool_url", "final_url", "status", "discord_invites"])
    results = []

    def record(result):
        results.append(result)
        invites = result["discord_invites"]
        for invite in invites:
            code = INVITE_RE.search(invite).group(1)
            if code not in written:  # already in the file, or linked from an earlier site
                written.add(code)
                out.write(invite + "\n")
        out.flush()
        if writer:
            writer.writerow([result["page"], result["name"], result["url"], result["final_url"],
                             result["status"], " ".join(invites)])
            report.flush()
        outcome = ", ".join(invites) if invites else f"no Discord invite ({result['status']})"
        log(f"[{len(results)}/{len(tools)}] {result['name']} | {result['url']} -> {outcome}")

    # A browser that has visited hundreds of sites slows down until nothing loads any more,
    # so every batch gets a fresh one. Failed sites go to the back of the queue for one more try.
    queue = [(tool, 1) for tool in tools]
    while queue:
        batch, queue = queue[:args.restart_every], queue[args.restart_every:]
        browser = await launch_browser(profile_root)
        try:
            retry = await scrape_batch(browser, batch, args, record)
        finally:
            await close_browser(browser)
        if retry:
            log(f"  {len(retry)} sites did not load, they will be retried in a fresh browser")
            queue += retry
    out.close()
    if report:
        report.close()

    with_invite = [r for r in results if r["discord_invites"]]
    log(f"\nDone: {len(with_invite)}/{len(results)} sites have a Discord invite. "
        f"{len(written) - already} new invite links added to {args.output} ({len(written)} in total)")
    statuses = {}
    for r in results:
        statuses[r["status"]] = statuses.get(r["status"], 0) + 1
    log("Sites by load status: " + ", ".join(f"{k}: {v}" for k, v in sorted(statuses.items(), key=lambda kv: -kv[1])))


def main():
    parser = argparse.ArgumentParser(description="Extract Discord invite links from the tools of a Toolify category.")
    parser.add_argument("url", help="Toolify category URL; its ?page= is the first page, e.g. "
                                    "https://www.toolify.ai/category/ai-writing-assistants?page=1")
    parser.add_argument("end_page", type=int, help="last page to scrape")
    parser.add_argument("-o", "--output", default="output.txt", help="text file with one invite link per line (default: %(default)s)")
    parser.add_argument("--csv", metavar="FILE", help="also write a per-site report (tool, URL, status, invites) to this CSV")
    parser.add_argument("-c", "--concurrency", type=int, default=4, help="tool sites open at once (default: %(default)s)")
    parser.add_argument("--timeout", type=int, default=45, help="seconds to wait for a page to load (default: %(default)s)")
    parser.add_argument("--cf-timeout", type=int, default=45, help="seconds to wait for a Cloudflare check (default: %(default)s)")
    parser.add_argument("--restart-every", type=int, default=60, metavar="N",
                        help="start a fresh browser every N sites (default: %(default)s)")
    parser.add_argument("--show", action="store_true", help="show the browser window instead of keeping it out of sight")
    args = parser.parse_args()
    try:
        args.first_page = start_page(args.url)
    except ValueError:
        sys.exit("Input Error: the page number in the URL is not a number.")
    if args.first_page < 1 or args.first_page > args.end_page:
        sys.exit(f"Input Error: start page {args.first_page} (from the URL) must be between 1 and the end page {args.end_page}.")

    def interrupt(*_):  # make kill / closing the terminal clean up like Ctrl-C does
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupt)
    if hasattr(signal, "SIGHUP"):
        signal.signal(signal.SIGHUP, interrupt)

    for stream in (sys.stdout, sys.stderr):  # tool names with emoji etc. must not crash a Windows console
        stream.reconfigure(errors="replace")

    xvfb = None
    if not args.show:
        if sys.platform.startswith("linux"):
            xvfb = start_virtual_display()
        else:
            # No Xvfb on Windows/macOS: park the window far off-screen instead (same spot Windows
            # uses for minimized windows). Only its taskbar button remains.
            BROWSER_ARGS.append("--window-position=-32000,-32000")
    profile = tempfile.mkdtemp(prefix="toolify_scraper_")  # throwaway profiles: no history survives the run
    try:
        uc.loop().run_until_complete(run(args, profile))
    except KeyboardInterrupt:
        sys.exit(130)
    finally:
        for pid in RUNNING_BROWSERS:  # only non-empty when the run was interrupted
            try:
                os.kill(pid, getattr(signal, "SIGKILL", signal.SIGTERM))  # no SIGKILL on Windows
            except OSError:
                pass
        # A Chrome that is still shutting down writes parts of its profile back,
        # so keep deleting until the folder has stayed gone for a while.
        gone = 0
        for _ in range(30):
            shutil.rmtree(profile, ignore_errors=True)
            time.sleep(0.5)
            gone = 0 if os.path.exists(profile) else gone + 1
            if gone >= 4:
                break
        if xvfb:
            xvfb.terminate()


if __name__ == "__main__":
    main()
