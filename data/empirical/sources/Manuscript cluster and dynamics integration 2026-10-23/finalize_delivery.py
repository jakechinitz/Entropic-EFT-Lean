"""Package checked manuscripts and proofs, retaining all earlier archive entries."""
from pathlib import Path
import datetime,difflib,hashlib,json,shutil,zipfile
import pymupdf

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
MAIN=ROOT/'01 Current Papers/Astra Full'
EMP=ROOT/'01 Current Papers/Empirical Results'
LIB=ROOT/'02 Research/Unified closure 2026-10-21/formalization'
STAMP=datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
CI=json.loads((HERE/'pinned_lean_verification.json').read_text(encoding='utf-8'))
assert CI['success'] and CI['build']=='success' and CI['axiom_audit']=='success'
SHA=CI['commit'];PR='https://github.com/jakechinitz/Entropic-EFT-Lean/pull/4'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def writejson(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def preserve(p):
    if p.exists():
        d=p.parent/'Previous PDFs'/(STAMP+'_delivery_metadata');d.mkdir(parents=True,exist_ok=True)
        shutil.copy2(p,d/p.name)

qa_dir=Path((HERE/'latest_pdf_review.txt').read_text(encoding='utf-8'))
qa=json.loads((qa_dir/'qa.json').read_text(encoding='utf-8'))
assert all(not x['off_page_words'] for x in qa.values())
pages={k:len(pymupdf.open(p)) for k,p in [('main',MAIN/'Entropic Scalar EFT.pdf'),('empirical',EMP/'Empirical_Results.pdf')]}
assert pages=={k:v['pages'] for k,v in qa.items()}

mods=json.loads((HERE/'lean_modules.json').read_text(encoding='utf-8'))
for m in mods:
    m['original_source_sha256']=m['sha256']
    m['integrated_sha256']=digest(LIB/m['path'])
    m['path']=Path(m['path']).as_posix()
    m['proof_scope']='Conditional mathematical certificate; not an observational likelihood or physical selection theorem.'
writejson(HERE/'integrated_lean_sources.json',mods)

preserved=json.loads((HERE/'preservation.json').read_text(encoding='utf-8'))
diffdir=HERE/'final_diffs';diffdir.mkdir(exist_ok=True)
changes=[]
for row in preserved['files']:
    before=ROOT/row['backup'];after=ROOT/row['path']
    assert digest(before)==row['sha256'],str(before)
    if after.suffix=='.tex' and after.exists():
        old=before.read_text(encoding='utf-8').splitlines(keepends=True)
        new=after.read_text(encoding='utf-8').splitlines(keepends=True)
        d=''.join(difflib.unified_diff(old,new,fromfile=row['backup'],tofile=row['path']))
        (diffdir/(after.parent.name+'_'+after.stem+'.diff')).write_text(d,encoding='utf-8')
        changes.append({'path':row['path'],'old_sha256':row['sha256'],'new_sha256':digest(after),'changed':bool(d)})
for name in ['05b_clusters.tex','05c_cross_sector.tex']:
    p=EMP/name;changes.append({'path':p.relative_to(ROOT).as_posix(),'new_file':True,'sha256':digest(p)})
writejson(HERE/'final_changes.json',changes)

for p in [MAIN/'START HERE.txt',EMP/'README.txt',EMP/'manifest.json',EMP/'current_verification.json']:
    preserve(p)

main_readme=f'''ENTROPIC SCALAR EFT - CURRENT FULL PAPER
23 October 2026

Entropic Scalar EFT.pdf is the current {pages['main']}-page full paper. Its editable
standalone LaTeX source is beside it. Previous sources, PDFs and archives remain
under Previous PDFs.

The paper integrates the exponential-allocation cosmological fit, the selected
constant-floor depletion action, finite-work and warm-fluid coupling, conservative
cluster encounters, observed X-COP/MENeaCS and Bullet targets, and cross-sector
empirical checks. Cluster outlier mechanisms remain conditional requirements.
The floor, contact target/rate, nonlinear spatial evolution and independently
measured release history retain the limitations stated in the manuscript.

The proof extension adds six modules with 119 explicit theorem declarations.
The full pinned Lean 4.35.0 build, prohibited-source scan, axiom audit and citation
check passed at commit {SHA}.
The extension is in the review branch at {PR};
it has not been merged into the repository default branch.

Build from the workspace root:
  python .organization/build_pdfs.py --paper astra
  python .organization/publication_set.py check
Outside the workspace, compile the standalone source with pdflatex twice.

Entropic_EFT_source_and_proofs.zip includes the current full paper, the current
proof sources under research/formalization_2026-10-23/, and the dated integration
records. Earlier archive entries, including the earlier compact edition and proof
projects, are preserved as historical snapshots. The compact and CDT papers were
not edited in this integration.

Current integration records:
  02 Research/Manuscript cluster and dynamics integration 2026-10-23/
Working proof library:
  02 Research/Unified closure 2026-10-21/formalization/

No scientific simulation or likelihood optimization was rerun for typesetting.
Saved results were inspected, arithmetic refreshed, proofs checked, both PDFs
rebuilt and visually reviewed. Archive MANIFEST.json hashes every other entry.
'''
(MAIN/'START HERE.txt').write_text(main_readme,encoding='utf-8')

emp_readme=f'''EMPIRICAL RESULTS: HISTORY-DEPENDENT GRAVITY AND COSMOLOGICAL RELEASE
23 October 2026 - current {pages['empirical']}-page edition

CONTENTS
Empirical_Results.tex and numbered TeX inputs: editable manuscript, including
05b_clusters.tex and 05c_cross_sector.tex. figures/ contains supplied figures.
Empirical_Results_Source.zip includes current sources, figures, records and PDF.
numerical_review.json preserves the original benchmark; current_verification.json
identifies the current exponential-allocation fit and imported research results.
manifest.json hashes the current package files. No previous PDF is discarded.

BUILD
From the Sol and Fable workspace:
  python .organization/build_pdfs.py --paper empirical
  python .organization/publication_set.py check
The helper preserves PDFs and keeps compiler files under 05 Build Files/PDF builds.
For standalone typesetting, compile Empirical_Results.tex with pdfLaTeX twice in
the supplied source directory; supplied figures require no simulation or Python.

REPRODUCTION
  python refresh_verified_results.py --workspace "C:/PATH/TO/Sol and Fable"
This imports the saved exponential-allocation fit, updates the redshift arithmetic
and figures, and preserves prior outputs. --legacy-linear selects the historical
linear-depletion benchmark. NumPy, SciPy and Matplotlib are required.

reproduce_review.py reproduces the original finite-ensemble, LMC, dwarf and release
review, then invokes the current supplement. It requires the source workspace
named in the provenance appendix. Original simulations and data archives are not
redistributed here. Neither script runs a new cosmological optimization or N-body
simulation. The current positive-allocation fit has chi-square 2227.8006205 versus
2228.3158253 for the matched LCDM pipeline; its approximations remain explicit.

PROOFS AND SCOPE
Six integrated modules add 119 explicit theorem declarations. The full pinned
Lean 4.35.0 build, source scan, axiom audit and citation check passed at
{SHA}. Review branch:
{PR}
This is not a merge into the default branch. Proven conservation, positivity and
conditional inventory identities do not certify observed cluster fits, numerical
simulations, or the physical selection of the constitutive/contact laws.

VALIDATION
Both publication PDFs were compiled with resolved cross-references and citations.
All empirical pages and the changed main-paper pages were rendered and inspected;
all pages were checked for text outside the page. The supplied writing guide was
used for the integration. The dated T5 record includes source hashes, exact diffs,
proof logs and PDF review. Original source bytes and prior artifacts are preserved.
'''
(EMP/'README.txt').write_text(emp_readme,encoding='utf-8')

current=json.loads((EMP/'current_verification.json').read_text(encoding='utf-8'))
current['lean']['extensions_pinned']=CI
current['lean']['extensions_standalone']=json.loads((HERE/'lean_validation_integrated.json').read_text(encoding='utf-8'))
current['lean']['extensions_source_manifest']=mods
current['source_hashes'][(HERE/'pinned_lean_verification.json').relative_to(ROOT).as_posix()]=digest(HERE/'pinned_lean_verification.json')
current['source_hashes'][(HERE/'lean_validation_integrated.json').relative_to(ROOT).as_posix()]=digest(HERE/'lean_validation_integrated.json')
current['scope']='Arithmetic refresh and saved-result import; no new simulation or cosmological optimization. Integrated proofs pass standalone 4.19 and pinned 4.35 repository checks.'
writejson(EMP/'current_verification.json',current)

coverage={
 'depletion_and_coupling':{'main':'O.3; Section 20; closure table','empirical':'Cosmology: self-limiting completion and coupling','sources':['Connected theory closure 2026-10-23','Effective dynamics and coupling 2026-10-23']},
 'clusters_and_outliers':{'main':'Section 18; closure table','empirical':'Clusters: conservative dynamics and observed targets','sources':['Conservative cluster merger 2026-10-23','Observed cluster tests 2026-10-23','Cluster outlier closure 2026-10-23'],'status':'Conditional mechanisms and observed targets; no claim of fitted cluster population'},
 'broader_empirical_program':{'main':'Section 27; N.8; O.12','empirical':'Acceleration, cosmology, independent checks across scales','sources':['Unified empirical program 2026-10-23']},
 'formalization':{'main':'R.1','empirical':'Scope of verification; T5','modules':mods,'ci':CI}}
writejson(HERE/'integration_coverage.json',coverage)
final={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pages':pages,'pdf_review':str(qa_dir.relative_to(ROOT)),
       'off_page_words':{k:len(v['off_page_words']) for k,v in qa.items()},'proofs':CI,
       'source_and_pdf_hashes':{p.relative_to(ROOT).as_posix():digest(p) for p in [MAIN/'Entropic Scalar EFT.tex',MAIN/'Entropic Scalar EFT.pdf',EMP/'Empirical_Results.tex',EMP/'Empirical_Results.pdf']},
       'saved_simulations_rerun':False,'new_likelihood_optimization':False,'outlier_explanations':'Possible and conditional; not presented as established solutions'}
writejson(HERE/'final_verification.json',final)

empfiles=sorted([p for p in EMP.iterdir() if p.is_file() and p.suffix in {'.tex','.py','.json','.txt','.cmd','.pdf'} and p.name!='manifest.json']+list((EMP/'figures').glob('*')))
manifest={'updated_utc':final['created_utc'],'pages':pages['empirical'],'figures':len(list((EMP/'figures').glob('*.pdf')))+len([p for p in (EMP/'figures').glob('*.png') if not p.with_suffix('.pdf').exists()]),
          'pdf_sha256':digest(EMP/'Empirical_Results.pdf'),'lean_commit':SHA,'lean_pr':PR,
          'verification_scope':current['scope'],'files':{p.relative_to(EMP).as_posix():digest(p) for p in empfiles}}
writejson(EMP/'manifest.json',manifest)
empzip=EMP/'Empirical_Results_Source.zip';preserve(empzip)
with zipfile.ZipFile(empzip,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for p in empfiles+[EMP/'manifest.json']:z.write(p,p.relative_to(EMP).as_posix())
    for name in ['pinned_lean_verification.json','integrated_lean_sources.json','integration_coverage.json','final_verification.json']:
        z.write(HERE/name,'integration_records/'+name)

mainzip=MAIN/'Entropic_EFT_source_and_proofs.zip';preserve(mainzip)
with zipfile.ZipFile(mainzip) as z:entries={n:z.read(n) for n in z.namelist()}
def replace_entry(name,data):
    if name in entries and entries[name]!=data:
        entries['editorial/before_dynamics_clusters_20261023/'+name]=entries[name]
    entries[name]=data
for p in [MAIN/'Entropic Scalar EFT.tex',MAIN/'Entropic Scalar EFT.pdf',MAIN/'START HERE.txt']:
    replace_entry('paper/'+p.name,p.read_bytes())
replace_entry('START HERE.txt',main_readme.encode('utf-8'))
snapshot=HERE/'repository_snapshot'
for row in json.loads((HERE/'repository_source_manifest.json').read_text())['files']:
    p=snapshot/row['path'];b=p.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['sha']
    entries['research/formalization_2026-10-23/'+row['path']]=b
for p in HERE.iterdir():
    if p.is_file() and p.suffix in {'.py','.json','.txt','.tex','.log'}:
        entries['editorial/dynamics_clusters/'+p.name]=p.read_bytes()
for p in diffdir.glob('*.diff'):entries['editorial/dynamics_clusters/final_diffs/'+p.name]=p.read_bytes()
entries['editorial/dynamics_clusters/pdf_qa.json']=(qa_dir/'qa.json').read_bytes()
replace_entry('editorial/final_verification.json',(HERE/'final_verification.json').read_bytes())
entries['editorial/before_dynamics_clusters_20261023/MANIFEST.json']=entries['MANIFEST.json']
entries['MANIFEST.json']=json.dumps([{'path':n,'bytes':len(v),'sha256':hashlib.sha256(v).hexdigest()} for n,v in sorted(entries.items()) if n!='MANIFEST.json'],indent=2).encode('utf-8')
with zipfile.ZipFile(mainzip,'w',compression=zipfile.ZIP_DEFLATED) as z:
    for n,v in sorted(entries.items()):z.writestr(n,v)
for p in [mainzip,empzip]:
    with zipfile.ZipFile(p) as z:assert z.testzip() is None
writejson(HERE/'package_verification.json',{'archives':{p.relative_to(ROOT).as_posix():{'sha256':digest(p),'bytes':p.stat().st_size} for p in [mainzip,empzip]},'preserved_archive_entries':True})
print(json.dumps({'pages':pages,'commit':SHA,'main_zip_bytes':mainzip.stat().st_size,'empirical_zip_bytes':empzip.stat().st_size}))
