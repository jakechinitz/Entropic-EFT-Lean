"""Check saved deliverables; never rerun simulations or alter input science."""
from pathlib import Path
from datetime import datetime, timezone
from html.parser import HTMLParser
from urllib.parse import unquote, urlparse
import hashlib, json, re, subprocess
import fitz

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
manifest=json.loads((HERE/'source_records/input_manifest.json').read_text(encoding='utf-8'))
assert all(sha(ROOT/r['path'])==r['sha256'] for r in manifest['inputs'])
validation=json.loads((HERE/'VALIDATION.json').read_text(encoding='utf-8'))
assert validation['checks_passed'] and validation['Lean']['theorems']==36
assert sha(HERE/'formalization/EffectiveContact.lean')==validation['Lean']['source_sha256']

class Links(HTMLParser):
    def __init__(self): super().__init__(); self.links=[]
    def handle_starttag(self,tag,attrs):
        self.links.extend(v for k,v in attrs if k in ('href','src'))
parser=Links(); parser.feed((HERE/'START HERE.html').read_text(encoding='utf-8'))
for link in parser.links:
    if not urlparse(link).scheme: assert (HERE/unquote(link)).is_file(), link

pdf=HERE/'Research note/main.pdf'
doc=fitz.open(pdf)
assert len(doc)==12
assert '??' not in ''.join(p.get_text() for p in doc)
assert all(len(p.get_text().strip())>100 for p in doc)
render=HERE/'Research note/Review render 20261023_124908'
previous=HERE/'Research note/Review render 20261023_124239'
changed=[i for i in range(1,13) if sha(render/f'page-{i:02}.png')!=sha(previous/f'page-{i:02}.png')]
assert changed==[6], changed
latest_log=max((ROOT/'05 Build Files/PDF builds/main').glob('*/main.log'),key=lambda p:p.stat().st_mtime)
log=latest_log.read_text(encoding='utf-8',errors='replace')
assert 'Overfull' not in log and 'undefined references' not in log
assert not re.search(r'^! ',log,re.M)
publication=subprocess.run(['python',str(ROOT/'.organization/publication_set.py'),'check'],cwd=ROOT,text=True,capture_output=True)
assert publication.returncode==0 and 'OK:' in publication.stdout

sources=list(HERE.glob('*.py'))+list((HERE/'Research note').glob('*.tex'))+[HERE/'formalization/EffectiveContact.lean']
outputs=[pdf,HERE/'START HERE.html',HERE/'VALIDATION.json',HERE/'REPRODUCE.txt']
report={
    'checked_utc':datetime.now(timezone.utc).isoformat(),
    'checks_passed':True,
    'unchanged_input_hashes':len(manifest['inputs']),
    'pdf_pages':len(doc),
    'html_local_links_verified':len(parser.links),
    'build_log':str(latest_log.relative_to(ROOT)),
    'final_render':str(render.relative_to(ROOT)),
    'visual_review':'All twelve pages reviewed in preceding render; only page 6 changed in final numeric synchronization and was reviewed separately.',
    'changed_render_pages':changed,
    'publication_check':publication.stdout.strip(),
    'sources':[{'path':str(p.relative_to(HERE)),'sha256':sha(p)} for p in sources],
    'outputs':[{'path':str(p.relative_to(HERE)),'sha256':sha(p)} for p in outputs],
    'scope':'Effective construction with conditional algebra certificates and separate numerical benchmarks; not a combined halo/void prediction or native microphysical derivation.'
}
with (HERE/'DELIVERY_VALIDATION.json').open('x',encoding='utf-8') as out:
    json.dump(report,out,indent=2)
print(json.dumps({k:report[k] for k in ['checks_passed','unchanged_input_hashes','pdf_pages','changed_render_pages','publication_check']}))
