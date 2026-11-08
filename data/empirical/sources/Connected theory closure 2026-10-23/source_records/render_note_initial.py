from pathlib import Path
import json
import pymupdf
from PIL import Image,ImageOps,ImageDraw

HERE=Path(__file__).resolve().parent
out=HERE/'Research note'/'Review render'
out.mkdir(exist_ok=False)
doc=pymupdf.open(HERE/'Research note'/'main.pdf')
records=[]
thumbs=[]
for i,page in enumerate(doc):
    path=out/f'page-{i+1:02d}.png'
    pix=page.get_pixmap(matrix=pymupdf.Matrix(1.5,1.5))
    pix.save(path)
    records.append({'page':i+1,'words':len(page.get_text('words')),'width':page.rect.width,'height':page.rect.height})
    im=Image.open(path).convert('RGB')
    im.thumbnail((408,545))
    thumb=Image.new('RGB',(428,575),'#dbe2e8')
    thumb.paste(im,((428-im.width)//2,10))
    ImageDraw.Draw(thumb).text((15,555),f'Page {i+1}',fill='black')
    thumbs.append(thumb)
for start in range(0,len(thumbs),4):
    sheet=Image.new('RGB',(856,1150),'white')
    for j,im in enumerate(thumbs[start:start+4]):sheet.paste(im,((j%2)*428,(j//2)*575))
    sheet.save(out/f'contact-{start//4+1:02d}.png')
(out/'page_inventory.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
print(json.dumps({'pages':len(doc),'directory':str(out)}))
