from pathlib import Path
import datetime, hashlib, json, re, shutil, zipfile, difflib
import pymupdf

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PAPER=ROOT/'01 Current Papers/Empirical Results'
BASE=PAPER/'Previous PDFs/20261023_155659_fifteen_tests'
STAMP=datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
PRESERVE=HERE/'metadata_before_finalization'/STAMP
PRESERVE.mkdir(parents=True)
for name in ['README.txt','current_verification.json','manifest.json','Empirical_Results_Source.zip']:
    shutil.copy2(PAPER/name,PRESERVE/name)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write_json(p,data): p.write_text(json.dumps(data,indent=2,ensure_ascii=True)+'\n',encoding='utf-8')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
review=Path((HERE/'latest_review.txt').read_text(encoding='utf-8'))
qa=json.loads((review/'qa.json').read_text())
coverage=json.loads((HERE/'coverage.json').read_text())
texts={p.name:p.read_text(encoding='utf-8') for p in PAPER.glob('*.tex')}
full='\n'.join(texts.values())
labels=re.findall(r'\\label\{([^}]+)\}',full)
refs=re.findall(r'\\(?:eqref|ref|pageref)\{([^}]+)\}',full)
assert len(labels)==len(set(labels)), 'Duplicate labels'
assert not set(refs)-set(labels), sorted(set(refs)-set(labels))
assert {r['id'] for r in coverage}=={f'S{i:02}' for i in range(1,16)}
for row in coverage:
    assert len(re.findall(r'^'+row['id']+r' &',texts['01_results_and_basis.tex'],re.M))==1
    assert row['location_label'] in labels
assert qa['coverage_count']==15 and not qa['off_page_words']
assert sha(PAPER/'Empirical_Results.pdf')==qa['pdf_sha256']
for p in (PAPER/'figures').rglob('*'):
    if p.is_file():
        old_manifest=json.loads((BASE/'manifest.json').read_text())
        key=p.relative_to(PAPER).as_posix()
        assert sha(p)==old_manifest['files'][key], f'Changed figure {key}'
build=max((ROOT/'05 Build Files/PDF builds/empirical').iterdir(),key=lambda p:p.stat().st_mtime)
log=(build/'Empirical_Results.log').read_text(encoding='utf-8',errors='replace')
bad=re.findall(r'^.*(?:Overfull|Missing character|undefined references|undefined citations|LaTeX Error|multiply defined).*$',
               log,re.M|re.I)
assert not bad,bad
diffdir=HERE/'source_diffs';diffdir.mkdir(exist_ok=True)
changes=[]
for name,after in texts.items():
    old=BASE/name
    before=old.read_text(encoding='utf-8') if old.exists() else ''
    if before!=after:
        patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),
                    fromfile='before/'+name,tofile='after/'+name))
        (diffdir/(name+'.diff')).write_text(patch,encoding='utf-8')
        changes.append(name)
verification={
 'updated_utc':now,
 'scope':'Editorial organization and explicit coverage of the existing fifteen-test register; no new simulation, likelihood fit, or Lean proof.',
 'pages':qa['pages'],'previous_pages':41,'test_families':15,
 'parts':{'I':'Distinctive predictions and discriminating tests','II':'Recovery of established phenomenology'},
 'coverage':[dict(r,section_resolves=True) for r in coverage],
 'status_snapshot_note':'Status snapshots come from the original program register; subsequent cluster and local-dynamics work is described in the current paper.',
 'pdf_sha256':qa['pdf_sha256'],
 'layout':dict(qa,render_review=str(review.relative_to(ROOT)),all_contact_sheets_inspected=True,
               detailed_pages_inspected=[3,20,22],cross_references_resolve=True,build_log_problems=bad),
 'build_directory':str(build.relative_to(ROOT)),
 'source_changes':changes,
 'source_sha256':{p.name:sha(p) for p in PAPER.glob('*.tex')},
 'science_unchanged':{'figure_hashes_unchanged':True,'simulations_rerun':False,'fits_rerun':False,'lean_modified':False},
 'preserved_originals':str(BASE.relative_to(ROOT)),
 'lean_commit_unchanged':'a6552daf39daf83d5159fcbcda698d1801731d24'
}
write_json(HERE/'final_verification.json',verification)
report="""EMPIRICAL FIFTEEN-TEST ORGANIZATION
23 October 2026

All fifteen registered test families are represented once in Table 1, with
resolved links to their discussion. The printed contents and body use:
I. Distinctive predictions and discriminating tests
II. Recovery of established phenomenology

The first group identifies specific comparisons and predictions; it does not
assert that all conventional physics fails. The second group records benchmark
recovery and compatibility. The table separates the role of each test from its
actual evidence. High-redshift residual tension, model-dependent dwarf odds,
historical constant selection, and unfinished likelihoods remain explicit.

The common CMB/galaxy relation states the mass-conversion and survival factors.
ACT projected lensing is distinguished from the uncompleted full-shape and
nonlinear growth tests. The prior cluster/dynamics integration is retained.

The PDF has 42 pages (previously 41). All pages were rendered; the four contact
sheets and the detailed overview/new section/Part II pages were inspected.
No off-page text, overfull boxes, undefined references, or undefined citations
were found. The source archive includes the new chapter and exact editorial
diffs. All original source bytes and the prior archive/PDF are preserved.

No empirical fits, simulations, or Lean proofs were rerun for this edit.
"""
(HERE/'REVIEW.txt').write_text(report,encoding='utf-8')
readme=(PAPER/'README.txt').read_text(encoding='utf-8')
readme=readme.replace('current 41-page edition','current 42-page edition')
readme=readme.replace('05b_clusters.tex and 05c_cross_sector.tex. figures/ contains supplied figures.',
 '05b_clusters.tex, 05c_cross_sector.tex and 05d_distinctive.tex.\nfigures/ contains supplied figures.')
readme=readme.replace('\nBUILD\n','\nORGANIZATION\nTable 1 covers all fifteen registered test families and links to each discussion.\nPart I: Distinctive predictions and discriminating tests.\nPart II: Recovery of established phenomenology.\nThe status of each test is stated separately; coverage does not mean all tests\npassed. The T6 record documents this editorial organization and PDF review.\n\nBUILD\n')
readme += '\nThe latest T6 edit reorganizes existing evidence without rerunning simulations,\nlikelihood fits or Lean proofs. All 42 empirical pages were rendered and checked;\nall fifteen overview entries and their section links are present and resolved.\n'
(PAPER/'README.txt').write_text(readme,encoding='utf-8')
current=json.loads((PAPER/'current_verification.json').read_text())
current['editorial_organization_20261023']={
 'updated_utc':now,'pages':42,'families':15,
 'parts':verification['parts'],'coverage_record':str((HERE/'coverage.json').relative_to(ROOT)),
 'verification_record':str((HERE/'final_verification.json').relative_to(ROOT)),
 'pdf_sha256':qa['pdf_sha256'],
 'scientific_result_scope':'Previously saved verification and evidence retained. This edit reruns no scientific fits, simulations or proofs.',
 'coverage_status':'All fifteen present; evidence and outstanding tests remain distinguished.'
}
write_json(PAPER/'current_verification.json',current)
manifest=json.loads((PAPER/'manifest.json').read_text())
manifest.update(updated_utc=now,pages=42,pdf_sha256=qa['pdf_sha256'],test_families=15,
                editorial_verification=str((HERE/'final_verification.json').relative_to(ROOT)))
files=[p for p in PAPER.iterdir() if p.is_file() and p.name not in {'manifest.json','Empirical_Results_Source.zip'}]
files += [p for p in (PAPER/'figures').rglob('*') if p.is_file()]
manifest['files']={p.relative_to(PAPER).as_posix():sha(p) for p in sorted(files)}
write_json(PAPER/'manifest.json',manifest)
# Preserve older embedded integration records and update current package members.
with zipfile.ZipFile(PRESERVE/'Empirical_Results_Source.zip') as previous:
    entries={n:previous.read(n) for n in previous.namelist()}
for p in files+[PAPER/'manifest.json']:
    entries[p.relative_to(PAPER).as_posix()]=p.read_bytes()
for p in [HERE/'coverage.json',HERE/'preservation.json',HERE/'final_verification.json',HERE/'REVIEW.txt']:
    entries['fifteen_test_records/'+p.name]=p.read_bytes()
for p in diffdir.iterdir():
    if p.is_file(): entries['fifteen_test_records/source_diffs/'+p.name]=p.read_bytes()
built=HERE/('Empirical_Results_Source_'+STAMP+'.zip')
with zipfile.ZipFile(built,'w',compression=zipfile.ZIP_DEFLATED) as package:
    for name,data in sorted(entries.items()): package.writestr(name,data)
with zipfile.ZipFile(built) as package:
    assert package.testzip() is None
    for name,digest in manifest['files'].items():
        assert hashlib.sha256(package.read(name)).hexdigest()==digest,name
shutil.copy2(built,PAPER/'Empirical_Results_Source.zip')
write_json(HERE/'package_validation.json',{
 'updated_utc':now,'source_archive_sha256':sha(PAPER/'Empirical_Results_Source.zip'),
 'pdf_sha256':qa['pdf_sha256'],'zip_crc_passed':True,'manifest_matches_archive':True,
 'archive_members':len(entries),'previous_embedded_records_preserved':True})
print(json.dumps({'pages':42,'coverage':15,'changed_sources':changes,'archive_members':len(entries),'validated':True}))

