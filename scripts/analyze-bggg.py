#!/usr/bin/env python3
"""Analyze eflambe .bggg (Brendan Gregg stack) profiler output to find bottlenecks.

The .bggg format is one sampled call stack per line:

    <0.82.0>;eflambe:apply/2;mod:func/2;lib:helper/1  3

Frames are ';'-separated, root (process) first and leaf (innermost) last,
followed by a space and the sample count for that exact stack.

This script STREAMS the file (constant memory, safe for multi-GB outputs) and
reports:
  * total samples
  * top functions by SELF time  (leaf of stack — where CPU is actually spent)
  * top functions by INCLUSIVE time (anywhere in stack — hot paths)
  * for the hottest inclusive functions: their callers and callees
  * optionally: a flamegraph.pl-compatible file (leaf-first, reversed)

Usage:
  scripts/analyze-bggg.py <file.bggg> [options]

Options:
  --top N            number of entries per table (default 15)
  --hot N            how many hottest inclusive functions to break down (default 8)
  --filter SUBSTR    drop frames containing SUBSTR from analysis (repeatable).
                     e.g. --filter eflambe:  to hide profiler instrumentation.
  --subset N         only read the first N lines (for quick experiments)
  --flame OUT        also write OUT in flamegraph.pl input format (leaf first)
  --quiet            only print tables, no progress on stderr
"""

import argparse
import sys
from collections import Counter


def parse_line(line):
    """Return (frames, count) or None for malformed lines."""
    sp = line.rfind(" ")
    if sp < 0:
        return None
    try:
        count = int(line[sp + 1:])
    except ValueError:
        return None
    if count <= 0:
        return None
    frames = line[:sp].split(";")
    if not frames:
        return None
    return frames, count


def analyze(path, filters, top, hot, flame_out, subset, quiet):
    def log(msg):
        if not quiet:
            print(msg, file=sys.stderr, flush=True)

    def kept(frame):
        return not any(f in frame for f in filters)

    log(f"pass 1/2: counting self & inclusive samples in {path}")
    self_cnt = Counter()
    incl_cnt = Counter()
    total = 0
    lines = 0
    nstacks = 0
    with open(path, "r", errors="replace") as fh:
        for line in fh:
            if subset and lines >= subset:
                break
            lines += 1
            parsed = parse_line(line)
            if parsed is None:
                continue
            frames, count = parsed
            total += count
            nstacks += 1
            leaf = frames[-1]
            if kept(leaf):
                self_cnt[leaf] += count
            seen = set()
            for f in frames:
                if f not in seen and kept(f):
                    incl_cnt[f] += count
                    seen.add(f)
    log(f"      {lines} lines, {nstacks} stacks, {total} samples, "
        f"{len(incl_cnt)} distinct functions")
    if total == 0:
        print("no samples found", file=sys.stderr)
        return

    hotfuncs = [f for f, _ in incl_cnt.most_common(hot)]

    # caller[callee] = samples where callee was directly above caller...
    # defined relative to the stack: caller = frame just ABOVE f (closer to
    # root), callee = frame just BELOW f (closer to leaf).
    callers = {f: Counter() for f in hotfuncs}
    callees = {f: Counter() for f in hotfuncs}

    log("pass 2/2: breaking down hot functions"
        + (" and writing flame file" if flame_out else ""))
    fo = open(flame_out, "w") if flame_out else None
    try:
        with open(path, "r", errors="replace") as fh:
            for i, line in enumerate(fh):
                if subset and i >= subset:
                    break
                parsed = parse_line(line)
                if parsed is None:
                    continue
                frames, count = parsed
                if fo:
                    # flamegraph.pl wants leaf-first order
                    fo.write(";".join(reversed(frames)) + f" {count}\n")
                # find positions of hot frames
                pos = {}
                for f in hotfuncs:
                    try:
                        pos[f] = frames.index(f)
                    except ValueError:
                        pass
                for f, idx in pos.items():
                    if idx > 0:
                        callers[f][frames[idx - 1]] += count
                    if idx + 1 < len(frames):
                        callees[f][frames[idx + 1]] += count
    finally:
        if fo:
            fo.close()

    pct = lambda c: f"{100.0 * c / total:5.1f}%"

    print()
    print(f"Total: {total} samples across {nstacks} distinct stacks "
          f"({lines} lines read)")
    if subset:
        print(f"(NOTE: subset of first {subset} lines only)")
    print()

    print("== SELF time (where the CPU actually is, leaf of stack) ==")
    print(f"{'samples':>10}  {'pct':>6}  function")
    for f, c in self_cnt.most_common(top):
        print(f"{c:>10}  {pct(c)}  {f}")

    print()
    print("== INCLUSIVE time (function anywhere in stack) ==")
    print(f"{'samples':>10}  {'pct':>6}  function")
    for f, c in incl_cnt.most_common(top):
        print(f"{c:>10}  {pct(c)}  {f}")

    print()
    print("== BREAKDOWN of hottest inclusive functions ==")
    for f in hotfuncs:
        c = incl_cnt[f]
        print(f"\n### {f}  ({c} samples, {pct(c)} of total)")
        top_callers = [(g, k) for g, k in callers[f].most_common(5)
                       if not any(x in g for x in filters)]
        top_callees = [(g, k) for g, k in callees[f].most_common(5)
                       if not any(x in g for x in filters)]
        if top_callers:
            print("  called from:")
            for g, k in top_callers:
                print(f"    {100.0 * k / c:5.1f}%  {g}")
        if top_callees:
            print("  calls:")
            for g, k in top_callees:
                print(f"    {100.0 * k / c:5.1f}%  {g}")

    if flame_out:
        print(f"\nWrote flamegraph.pl input to {flame_out}\n"
              f"  (render: flamegraph.pl < {flame_out} > flame.svg)")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("file", help="path to .bggg file")
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--hot", type=int, default=8)
    ap.add_argument("--filter", action="append", default=[],
                    help="drop frames containing this substring (repeatable)")
    ap.add_argument("--subset", type=int, default=0)
    ap.add_argument("--flame", metavar="OUT", default=None)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    analyze(args.file, args.filter, args.top, args.hot,
            args.flame, args.subset or None, args.quiet)


if __name__ == "__main__":
    main()
