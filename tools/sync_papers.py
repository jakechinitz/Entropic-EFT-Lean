"""Sync the current publication set and the empirical data into this repository.

Run on a machine that has the author's workspace ("Sol and Fable"):

    python tools/sync_papers.py --workspace "PATH/TO/Sol and Fable" [--sources]

It reads 01 Current Papers/PUBLICATION SET.json and copies:
- each paper's current PDF and source into papers/<key>/;
- the Empirical Results reproduction package into data/empirical/package/;
- with --sources, the research folders cited by the empirical paper's audit table into data/empirical/sources/.

It applies the filter described in data/README.md, then rewrites papers/MANIFEST.json and
data/empirical/sources_index.json. Review the diff and commit. Lean sources are never touched.
"""
import argparse, hashlib, json, os, re, shutil
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NAMES = {'full': ('full', 'Entropic_Scalar_EFT'), 'compact': ('compact', 'Entropic_Scalar_EFT_Compact'),
         'empirical': ('empirical-results', 'Empirical_Results'), 'cdt': ('microstructure-cdt', 'Microstructure_CDT')}
PACKAGE = ['manifest.json', 'current_verification.json', 'numerical_review.json',
           'refresh_verified_results.py', 'reproduce_review.py', 'README.txt']
KEEP = {'.py', '.json', '.md', '.txt', '.csv', '.tsv', '.tex', '.yaml', '.yml', '.toml', '.sha256', '.sh', '.ps1',
        '.dat', '.npy', '.npz'}
SKIP_DIRS = {'.lake', '.git', '__pycache__', 'toolchain', 'node_modules', 'source_snapshots', 'snapshots', '.venv',
             'source_snapshot', 'repository_snapshot', 'dependencies', 'site-packages'}
SKIP_PREFIX = ('Previous', 'analysis_20', 'run_20', 'runs', 'logs', 'inputs', 'formalization', 'verification_runs',
               'workspace')
CAP = 1_000_000

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

def cp(src, dst):
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy2(src, dst)

def papers(ws):
    cpd = os.path.join(ws, '01 Current Papers')
    for p in json.load(open(os.path.join(cpd, 'PUBLICATION SET.json')))['papers']:
        d, stem = NAMES[p['key']]
        src, out = os.path.join(cpd, p['folder']), os.path.join(REPO, 'papers', d)
        cp(os.path.join(src, p['main_pdf']), os.path.join(out, stem + '.pdf'))
        cp(os.path.join(src, p['main_tex']), os.path.join(out, 'source', p['main_tex']))
        if p['key'] == 'empirical':
            for f in sorted(os.listdir(src)):
                if f[:2].isdigit() and f.endswith('.tex'):
                    cp(os.path.join(src, f), os.path.join(out, 'source', f))
            for f in sorted(os.listdir(os.path.join(src, 'figures'))):
                cp(os.path.join(src, 'figures', f), os.path.join(out, 'source', 'figures', f))
            for f in PACKAGE:
                cp(os.path.join(src, f), os.path.join(REPO, 'data', 'empirical', 'package', f))
        if p['key'] == 'cdt':
            for f in sorted(os.listdir(os.path.join(src, 'chapters'))):
                cp(os.path.join(src, 'chapters', f), os.path.join(out, 'source', 'chapters', f))
    man = {'files': {}}
    for r, _, fs in os.walk(os.path.join(REPO, 'papers')):
        for f in fs:
            if f in ('README.md', 'MANIFEST.json'):
                continue
            q = os.path.join(r, f)
            man['files'][os.path.relpath(q, os.path.join(REPO, 'papers'))] = {'sha256': sha(q), 'bytes': os.path.getsize(q)}
    json.dump(man, open(os.path.join(REPO, 'papers', 'MANIFEST.json'), 'w'), indent=1, sort_keys=True)

def sources(ws):
    tex = open(os.path.join(REPO, 'papers', 'empirical-results', 'source', '06_interpretation_and_audit.tex'),
               encoding='utf-8').read()
    paths = sorted(set(re.findall(r'\\path\{(02 Research/[^}]*)\}', tex)))
    root = os.path.join(REPO, 'data', 'empirical', 'sources')
    excluded = []
    for rel in paths:
        src = os.path.join(ws, rel)
        if os.path.isfile(src):
            cp(src, os.path.join(root, rel[len('02 Research/'):]))
            continue
        for r, dirs, files in os.walk(src):
            keep = [x for x in dirs if x not in SKIP_DIRS and not x.startswith(SKIP_PREFIX)]
            excluded += [[os.path.relpath(os.path.join(r, x), ws) + '/', 'dir'] for x in dirs if x not in keep]
            dirs[:] = keep
            for f in files:
                q = os.path.join(r, f)
                ok = os.path.splitext(f)[1].lower() in KEEP and os.path.getsize(q) <= CAP
                if ok:
                    cp(q, os.path.join(root, os.path.relpath(q, os.path.join(ws, '02 Research'))))
                else:
                    excluded.append([os.path.relpath(q, ws), os.path.getsize(q)])
    inc = sorted(os.path.relpath(os.path.join(r, f), root) for r, _, fs in os.walk(root) for f in fs)
    json.dump({'included_count': len(inc), 'included': inc, 'excluded': excluded},
              open(os.path.join(REPO, 'data', 'empirical', 'sources_index.json'), 'w'), indent=1)

if __name__ == '__main__':
    a = argparse.ArgumentParser()
    a.add_argument('--workspace', required=True)
    a.add_argument('--sources', action='store_true')
    o = a.parse_args()
    papers(o.workspace)
    if o.sources:
        sources(o.workspace)
    print('synced; review with git status')
