from pathlib import Path
import shutil, hashlib, json, datetime, re
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
stamp=datetime.datetime.now().strftime('%Y%m%d_%H%M%S')+'_dynamics_clusters'
records=[]
for name in ['Astra Full','Empirical Results']:
    folder=ROOT/'01 Current Papers'/name
    dest=folder/'Previous PDFs'/stamp
    dest.mkdir(parents=True)
    files=list(folder.glob('*.tex'))+list(folder.glob('*.pdf'))+list(folder.glob('*.zip'))
    for f in files:
        shutil.copy2(f,dest/f.name)
        records.append({'path':str(f.relative_to(ROOT)),'backup':str((dest/f.name).relative_to(ROOT)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
    if (folder/'figures').exists(): shutil.copytree(folder/'figures',dest/'figures')
formal=ROOT/'02 Research/Unified closure 2026-10-21/formalization'
sources=[('Unified empirical program 2026-10-23','EmpiricalCertificates'),('Unified empirical program 2026-10-23','MuseProjection'),('Connected theory closure 2026-10-23','ConnectedClosure'),('Effective dynamics and coupling 2026-10-23','EffectiveContact'),('Conservative cluster merger 2026-10-23','MergerContact'),('Cluster outlier closure 2026-10-23','ClusterOutliers')]
for f in [formal/'Entropic.lean',formal/'README.md']:
    dest=HERE/'before_lean'/f.name;dest.parent.mkdir(exist_ok=True)
    shutil.copy2(f,dest)
    records.append({'path':str(f.relative_to(ROOT)),'backup':str(dest.relative_to(ROOT)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
mods=[]
for folder,name in sources:
    src=ROOT/'02 Research'/folder/'formalization'/f'{name}.lean'
    dest=formal/'Entropic/Extensions20261023'/src.name
    dest.parent.mkdir(exist_ok=True)
    assert not dest.exists(),dest
    shutil.copy2(src,dest)
    mods.append({'module':f'Entropic.Extensions20261023.{name}','source':str(src.relative_to(ROOT)),'path':str(dest.relative_to(formal)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'theorems':len(re.findall(r'^theorem\s+',src.read_text(encoding='utf-8'),re.M))})
entry=formal/'Entropic.lean'
with entry.open('a',encoding='utf-8',newline='\n') as f:
    f.write('\n-- Effective dynamics and empirical certificates, 2026-10-23.\n'+'\n'.join('import '+m['module'] for m in mods)+'\n')
(HERE/'preservation.json').write_text(json.dumps({'stamp':stamp,'files':records},indent=2),encoding='utf-8')
(HERE/'lean_modules.json').write_text(json.dumps(mods,indent=2),encoding='utf-8')
print(json.dumps({'preserved':len(records),'stamp':stamp,'modules':len(mods),'theorems':sum(m['theorems'] for m in mods)}))
