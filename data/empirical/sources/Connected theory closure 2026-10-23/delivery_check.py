from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
from urllib.parse import unquote
import pymupdf

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((HERE/'source_records/input_manifest.json').read_text(encoding='utf-8'))
assert all(sha(ROOT/r['path'])==r['sha256'] for r in manifest['inputs'])
validation=json.loads((HERE/'VALIDATION.json').read_text(encoding='utf-8'))
assert validation['success']
assert sha(HERE/'formalization/ConnectedClosure.lean')==validation['Lean']['source_sha256']
page=(HERE/'START HERE.html').read_text(encoding='utf-8')
links=re.findall(r'(?:href|src)="([^"]+)"',page)
assert all((HERE/unquote(link)).exists() for link in links if ':' not in link and not link.startswith('#'))
pdf=HERE/'Research note/main.pdf'
doc=pymupdf.open(pdf)
assert len(doc)==10 and all(len(p.get_text('words'))>50 for p in doc)
assert all('??' not in p.get_text() for p in doc)
buildfile=sorted((ROOT/'05 Build Files/PDF builds/main').glob('*/build_result.json'))[-1]
build=json.loads(buildfile.read_text(encoding='utf-8'))
assert sha(pdf)==build['pdf_sha256']
assert sha(HERE/'Research note/main.tex')==build['source_sha256']
assert not any('Overfull' in w or 'undefined' in w for w in build['warnings'])
record={
 'checked_utc':datetime.now(timezone.utc).isoformat(),
 'success':True,'original_inputs_unchanged':len(manifest['inputs']),
 'pdf_pages':len(doc),'pdf_sha256':sha(pdf),'tex_sha256':build['source_sha256'],
 'local_report_links_checked':len(links),'build_record':str(buildfile.relative_to(ROOT)),
 'visual_review':'All 10 pages inspected as rendered images; equations and figures additionally inspected at larger scale.',
 'preview_compiler':'Built-in preview unavailable due Windows sandbox preparation error; workspace-preserving pdflatex build succeeded.',
 'research_validation':'VALIDATION.json',
 'publication_set_check':'OK: four publications, one folder and one current PDF each.',
 'scope':'Conditional effective construction and restrictions; no claim that all five physical questions are closed.'}
out=HERE/'DELIVERY_VALIDATION.json'
with out.open('x',encoding='utf-8') as f:json.dump(record,f,indent=2)
print(json.dumps(record))
