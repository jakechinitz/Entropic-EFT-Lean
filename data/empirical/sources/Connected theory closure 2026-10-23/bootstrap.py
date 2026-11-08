from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, importlib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
for name in ('results', 'figures', 'formalization', 'logs', 'source_records'):
    (HERE/name).mkdir(exist_ok=True)
paths = [
 '01 Current Papers/Astra Full/Entropic Scalar EFT.tex',
 '01 Current Papers/Astra Compact/Astra Quantum gravity completion compact.tex',
 '01 Current Papers/Empirical Results/Empirical_Results.tex',
 '01 Current Papers/Microstructure CDT/MICROSTRUCTURE_CDT.tex',
 '02 Research/Unified empirical program 2026-10-23/execution_register.json',
 '02 Research/Unified empirical program 2026-10-23/results/cosmology_final.json',
 '02 Research/Unified empirical program 2026-10-23/cosmology_engine.py',
 '02 Research/Vacuum exhaustion completion 2026-10-22/RESULTS.txt',
 '02 Research/Stock adjustment resolution 2026-10-21/START HERE.txt',
 '02 Research/Cluster reciprocity audit 2026-10-22/CLUSTER_RECIPROCITY_AUDIT.txt',
]
lean = ROOT/'02 Research/Unified closure 2026-10-21/formalization'
paths += [str(p.relative_to(ROOT)).replace('\\','/') for p in (lean/'Entropic').rglob('*.lean')]
rows=[]
for rel in paths:
    p=ROOT/rel
    rows.append({'path':rel,'bytes':p.stat().st_size,
                 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
versions={}
for name in ['numpy','scipy','sympy','matplotlib']:
    mod=importlib.import_module(name); versions[name]=mod.__version__
record={'created_utc':datetime.now(timezone.utc).isoformat(),
        'github_head':'432da8c4a8b169a17146b53e4155d6b37915a12f',
        'inputs':rows,'versions':versions}
out=HERE/'source_records/input_manifest.json'
if out.exists():
    raise RuntimeError('Input manifest already exists; preserve it.')
out.write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({'inputs':len(rows),'versions':versions}))
