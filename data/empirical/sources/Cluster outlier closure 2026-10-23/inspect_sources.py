from pathlib import Path
import urllib.request, hashlib, json, concurrent.futures
import pymupdf

HERE=Path(__file__).resolve().parent
D=HERE/'source_records';D.mkdir(exist_ok=True)
sources={'XRISM_A1795_2026':'https://arxiv.org/pdf/2606.08097',
         'XRISM_A2029_2025':'https://arxiv.org/pdf/2505.06533',
         'XRISM_A2029_2026':'https://arxiv.org/pdf/2608.14415'}
def fetch(item):
    name,url=item;p=D/(name+'.pdf')
    if not p.exists():
        with urllib.request.urlopen(url,timeout=60) as response:
            data=response.read()
        if not data.startswith(b'%PDF'): raise ValueError(url)
        p.write_bytes(data)
    with pymupdf.open(p) as doc:
        (D/(name+'.txt')).write_text('\n'.join(page.get_text() for page in doc),encoding='utf-8')
    return {'name':name,'url':url,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: records=list(pool.map(fetch,sources.items()))
(D/'manifest.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
print(json.dumps(records,indent=2))
