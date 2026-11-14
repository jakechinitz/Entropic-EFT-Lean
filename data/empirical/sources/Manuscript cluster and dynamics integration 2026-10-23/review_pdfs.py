from pathlib import Path
import json,subprocess,datetime,re
import pymupdf as fitz
from PIL import Image,ImageOps,ImageDraw
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OUT=HERE/'pdf_review'/datetime.datetime.now().strftime('%Y%m%d_%H%M%S');OUT.mkdir(parents=True)
patterns=['18. Cluster Stock','Joint empirical checks','A constitutive completion before exhaustion','Finite work, recharge','Response time, noise','Direct perturbations and matched','Formal proofs and extension checks']
report={}
for key,rel in [('main','Astra Full/Entropic Scalar EFT.pdf'),('empirical','Empirical Results/Empirical_Results.pdf')]:
 p=ROOT/'01 Current Papers'/rel;doc=fitz.open(p);texts=[page.get_text() for page in doc]
 (OUT/(key+'.txt')).write_text('\n\f\n'.join(texts),encoding='utf-8')
 if key=='empirical': pages=list(range(len(doc)))
 else:
  pages=set([0,1,7,8])
  for i,t in enumerate(texts):
   if i>5 and any(x in t for x in patterns): pages.update(range(max(0,i-1),min(len(doc),i+5)))
  pages=sorted(pages)
 issues=[]
 for i,page in enumerate(doc):
  for w in page.get_text('words'):
   if w[0]<-1 or w[1]<-1 or w[2]>page.rect.width+1 or w[3]>page.rect.height+1:issues.append({'page':i+1,'word':w[4],'bbox':w[:4]})
 imgs=[]
 folder=OUT/key;folder.mkdir()
 for i in pages:
  pref=folder/f'page-{i+1:03}'
  subprocess.run(['pdftoppm','-f',str(i+1),'-l',str(i+1),'-scale-to','1100','-singlefile','-png',str(p),str(pref)],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
  imgs.append((i+1,pref.with_suffix('.png')))
 sheets=[]
 for start in range(0,len(imgs),12):
  batch=imgs[start:start+12];sheet=Image.new('RGB',(1200,1680),'#e7e9ed');draw=ImageDraw.Draw(sheet)
  for j,(num,path) in enumerate(batch):
   im=Image.open(path).convert('RGB');im.thumbnail((390,390))
   x=(j%3)*400+(400-im.width)//2;y=(j//3)*420+22
   sheet.paste(im,(x,y));draw.text(((j%3)*400+12,(j//3)*420+5),f'{key} page {num}',fill='black')
  name=folder/f'contact-{start//12+1:02}.png';sheet.save(name);sheets.append(str(name))
 report[key]={'pages':len(doc),'rendered_pages':[n for n,_ in imgs],'off_page_words':issues,'contact_sheets':sheets}
 (OUT/'qa.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
 print(key,len(doc),'pages; rendered',len(pages),'off page',len(issues),flush=True)
(HERE/'latest_pdf_review.txt').write_text(str(OUT),encoding='utf-8')
