#!/usr/bin/env python3
"""Fresh builds of the same client, never swapping the working tree.
Cites: D-CH-25, D-RT-28, D-TL-17, AT-FD-2, AT-FD-11.
Scope: the current Init-based discrete implementation, not the full higher root.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'build' / 'seal-check'


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "summary.json").unlink(missing_ok=True)
    records = []

    def run(directory, label, args, *, stub=False, rejection=None):
        env = os.environ.copy()
        env.pop('LEAN_PATH', None)
        env['CATEGORY_MADNESS_STUB'] = '1' if stub else '0'
        start = time.monotonic()
        result = subprocess.run(args, cwd=directory, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - start, 3)
        (OUT / f'{label}.log').write_text(result.stdout)
        if rejection:
            if result.returncode == 0 or rejection not in result.stdout:
                raise RuntimeError(f'{label}: expected {rejection}; see {OUT / (label + ".log")}')
        elif result.returncode != 0:
            raise RuntimeError(f'{label}: failed; see {OUT / (label + ".log")}')
        records.append(dict(check=label, seconds=elapsed, exit_code=result.returncode,
                            expected_rejection=rejection))
        print(f'seal: {label}: {"rejected as expected" if rejection else "passed"} ({elapsed}s)', flush=True)
        return result.stdout

    audit = (ROOT / 'scripts/SealAudit.lean').read_text()
    signatures = {}
    with tempfile.TemporaryDirectory(prefix='seal-', dir=OUT) as temp:
        dirs = {}
        for mode in ('real', 'stub'):
            directory = Path(temp) / mode
            directory.mkdir()
            dirs[mode] = directory
            layers = ['Interface', 'Theory'] + (['Kernel', 'Root'] if mode == 'real' else [])
            for layer in layers:
                shutil.copytree(ROOT / layer, directory / layer)
                shutil.copy2(ROOT / f'{layer}.lean', directory / f'{layer}.lean')
            if mode == 'stub':
                for path in (ROOT / 'Interface-Stub').rglob('*.lean'):
                    target = directory / 'Interface' / path.relative_to(ROOT / 'Interface-Stub')
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(path, target)
            # This fragment imports only Init; source files and Lean options are unchanged.
            config = 'name = "SealCheck"\ndefaultTargets = ["Theory"]\n'
            config += '[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n'
            config += ''.join(f'[[lean_lib]]\nname = "{layer}"\n' for layer in layers)
            (directory / 'lakefile.toml').write_text(config)
            shutil.copy2(ROOT / 'lean-toolchain', directory / 'lean-toolchain')
            (directory / 'Audit.lean').write_text(audit)
            run(directory, f'{mode}-build', ['lake', 'build', 'Interface', 'Theory'], stub=mode == 'stub')
            output = run(directory, f'{mode}-audit', ['lake', 'env', 'lean', 'Audit.lean'],
                         stub=mode == 'stub')
            signatures[mode] = sorted(line.split('SIGNATURE ', 1)[1]
                                      for line in output.splitlines() if 'SIGNATURE ' in line)
            shutil.copy2(ROOT / 'Prototype/Negative/ImplementationEquation.lean', directory / 'Equation.lean')
            run(directory, f'{mode}-opaque-equation', ['lake', 'env', 'lean', 'Equation.lean'],
                stub=mode == 'stub', rejection='Type mismatch')
        if not signatures['real'] or signatures['real'] != signatures['stub']:
            raise RuntimeError('public signatures differ or are empty')
        print(f'seal: identical public signatures ({len(signatures["real"])} declarations)', flush=True)
        run(dirs['stub'], 'stub-in-real-audit', ['lake', 'env', 'lean', 'Audit.lean'],
            rejection='AXIOM_REJECTED')
        for fixture, rejection in [('ProjectAxiom', 'AXIOM_REJECTED'),
                                   ('Sorry', 'AXIOM_REJECTED'), ('PrivateLeak', 'SEAL_LEAK')]:
            directory = dirs['real']
            shutil.copy2(ROOT / f'Prototype/Negative/{fixture}.lean', directory / 'Injected.lean')
            run(directory, f'{fixture}-compile', ['lake', 'env', 'lean', '-o',
                '.lake/build/lib/lean/Injected.olean', 'Injected.lean'])
            (directory / 'NegativeAudit.lean').write_text('import Injected\n' + audit)
            run(directory, f'{fixture}-audit', ['lake', 'env', 'lean', 'NegativeAudit.lean'],
                rejection=rejection)
    files = [p for layer in ['Kernel', 'Root', 'Interface', 'Interface-Stub', 'Theory']
             for p in (ROOT / layer).rglob('*.lean')]
    files += [ROOT / 'scripts/SealAudit.lean', ROOT / 'scripts/check_seal.py',
              ROOT / 'scripts/swap_test.sh', ROOT / 'lean-toolchain', ROOT / 'lakefile.toml']
    files += [ROOT / f'{layer}.lean' for layer in ['Kernel', 'Root', 'Interface', 'Theory']]
    files += list((ROOT / 'Prototype/Negative').glob('*.lean'))
    summary = dict(source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in sorted(files)},
                   public_signature_count=len(signatures['real']),
                   public_signature_sha256=hashlib.sha256('\n'.join(signatures['real']).encode()).hexdigest(),
                   checks=records)
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('seal: all checks passed; evidence in build/seal-check', flush=True)


if __name__ == '__main__':
    main()
