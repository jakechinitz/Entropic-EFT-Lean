"""Freeze hashes of the finished audit, numerical dependencies and manuscript."""
from pathlib import Path
import sys,hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
sys.path.insert(0,str(QUIET))
import live_quiet_fast,quiet_fit,weak_endpoints
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while b:=f.read(1024*1024):h.update(b)
    return h.hexdigest()
paper=ROOT/'01 Current Papers/Astra Full/Astra Quantum gravity completion (merged).tex'
before=json.loads((HERE/'manuscript_before.json').read_text(encoding='utf-8-sig'))['Hash'].lower()
assert sha(paper)==before
copies={name:{'new':sha(HERE/name),'preserved_source':sha(QUIET/name)} for name in ['seed_exact.py','quiet_fit.py','live_quiet_fast.py']}
assert all(v['new']==v['preserved_source'] for v in copies.values())
files={}
for path in HERE.rglob('*'):
    if path.is_file() and '__pycache__' not in path.parts and path.name!='final_manifest.json':
        files[str(path.relative_to(ROOT))]={'sha256':sha(path),'bytes':path.stat().st_size}
deps={}
for module in list(sys.modules.values()):
    if getattr(module,'__file__',None):
        p=Path(module.__file__).resolve()
        if p.is_file() and p.is_relative_to(HERE.parent) and not p.is_relative_to(HERE):deps[str(p.relative_to(ROOT))]=sha(p)
for relative in ['Halo stock director bridge 2026-10-21/weak_stationarity_weights.npz',
                 'Halo stock director bridge 2026-10-21/stars_seed_8192.npz',
                 'Halo and growth followup 2026-10-21/precession_extension_stock/library.npz',
                 'Halo and growth followup 2026-10-21/precession_validation/results.json']:
    p=HERE.parent/relative;deps[str(p.relative_to(ROOT))]=sha(p)
out={'manuscript_unchanged':True,'manuscript_sha256':before,'a0_SI':1.230729e-10,
     'unchanged_stage_copies':copies,'files':files,'preserved_dependencies':deps}
assert not (HERE/'final_manifest.json').exists()
(HERE/'final_manifest.json').write_text(json.dumps(out,indent=2));print(json.dumps({'files':len(files),'dependencies':len(deps),'manuscript_unchanged':True}))
