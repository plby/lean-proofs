#!/usr/bin/env python3
"""Compile only the task modules with stock Lean options and cached dependencies."""
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
PACKAGES = Path('/root/code/lean-proofs/src/latest/.lake/packages')
LEAN = '/root/code/lean-4.33.0-linux/bin/lean'
BUILD = ROOT / '.lake/build/lib/lean'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', action='store_true',
                        help='Remove only the selected task-module artifacts before compilation.')
    parser.add_argument('--all', action='store_true', help='Build the endpoint, all helpers, and audit.')
    parser.add_argument('modules', nargs='*')
    args = parser.parse_args()
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(BUILD)] + [str(PACKAGES / p / '.lake/build/lib/lean')
        for p in ['mathlib', 'batteries', 'Qq', 'aesop', 'proofwidgets',
                  'importGraph', 'LeanSearchClient', 'plausible', 'Cli']])
    names = []
    seen = set()

    def visit(name):
        if name in seen:
            return
        if name != 'ErdosProblems.Erdos192' and not name.startswith('ErdosProblems.Erdos192.'):
            raise ValueError(f'Not a task-owned module: {name}')
        seen.add(name)
        source = ROOT / (name.replace('.', '/') + '.lean')
        if args.all:
            for line in source.read_text().splitlines():
                if line.startswith('import ErdosProblems.Erdos192'):
                    visit(line.removeprefix('import ').strip())
        names.append(name)

    for name in args.modules or ['ErdosProblems.Erdos192.Audit']:
        visit(name)
    if args.clean:
        for name in names:
            stem = BUILD / name.replace('.', '/')
            for suffix in ['.olean', '.olean.server', '.olean.private', '.ilean']:
                stem.with_name(stem.name + suffix).unlink(missing_ok=True)
    start = time.monotonic()
    results = []
    for name in names:
        source = ROOT / (name.replace('.', '/') + '.lean')
        target = BUILD / (name.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [LEAN, '-o', str(target), str(source)]
        tick = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - tick
        print(result.stdout, end='', flush=True)
        print(f'{name}: {elapsed:.3f}s (exit {result.returncode})', flush=True)
        results.append(dict(module=name, command=command, seconds=elapsed,
                            exit_code=result.returncode, output=result.stdout))
        if result.returncode:
            sys.exit(result.returncode)
    report = dict(clean=args.clean, cached_dependencies=str(PACKAGES),
                  wall_seconds=time.monotonic() - start,
                  peak_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  lean_version=subprocess.check_output([LEAN, '--version'], text=True).strip(),
                  modules=results)
    destination = ROOT / '.lake/erdos192-build-report.json'
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'modules'}, indent=2), flush=True)


if __name__ == '__main__':
    main()
