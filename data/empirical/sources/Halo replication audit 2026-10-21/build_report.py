"""Build the separate research report from final, checked narrative content."""
from pathlib import Path
import json
from reportlab.platypus import SimpleDocTemplate,Paragraph,Spacer,Table,TableStyle,PageBreak,Image,KeepTogether
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib import colors
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
HERE=Path(__file__).resolve().parent
pdfmetrics.registerFont(TTFont('ReportArial','C:/Windows/Fonts/arial.ttf'))
pdfmetrics.registerFont(TTFont('ReportArialBold','C:/Windows/Fonts/arialbd.ttf'))
pdfmetrics.registerFontFamily('ReportArial',normal='ReportArial',bold='ReportArialBold')
INK=colors.HexColor('#183744');ACCENT=colors.HexColor('#136f87');LIGHT=colors.HexColor('#eaf1f4')
styles={
 'title':ParagraphStyle('title',fontName='ReportArialBold',fontSize=25,leading=29,textColor=INK,spaceAfter=16),
 'h1':ParagraphStyle('h1',fontName='ReportArialBold',fontSize=17,leading=21,textColor=INK,spaceAfter=12),
 'h2':ParagraphStyle('h2',fontName='ReportArialBold',fontSize=11.3,leading=15,textColor=ACCENT,spaceBefore=10,spaceAfter=5),
 'body':ParagraphStyle('body',fontName='ReportArial',fontSize=10.3,leading=14.5,textColor=INK,spaceAfter=9),
 'small':ParagraphStyle('small',fontName='ReportArial',fontSize=8.8,leading=12,textColor=INK,spaceAfter=7),
 'cell':ParagraphStyle('cell',fontName='ReportArial',fontSize=9.1,leading=12,textColor=INK),
 'code':ParagraphStyle('code',fontName='Courier',fontSize=8.8,leading=12,textColor=INK,spaceAfter=9),
}

def footer(canvas,doc):
    canvas.saveState();canvas.setStrokeColor(colors.HexColor('#c5d4db'));canvas.line(42,39,570,39)
    canvas.setFont('ReportArial',8);canvas.setFillColor(INK);canvas.drawString(42,26,'HALO TILT RESEARCH  |  21 OCTOBER 2026  |  Manuscript and a0 unchanged')
    canvas.drawRightString(570,26,str(doc.page));canvas.restoreState()

def table(rows,widths):
    data=[[Paragraph(str(c),styles['cell']) for c in row] for row in rows]
    t=Table(data,colWidths=widths,hAlign='LEFT',repeatRows=1)
    t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),LIGHT),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),
        ('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7),
        ('LINEBELOW',(0,0),(-1,0),.6,ACCENT),('LINEBELOW',(0,1),(-1,-1),.3,colors.HexColor('#d4dfe4'))]))
    return t

if __name__=='__main__':
    content=json.loads((HERE/'REPORT CONTENT.json').read_text());story=[]
    for i,page in enumerate(content['pages']):
        if i:story.append(PageBreak())
        for block in page:
            kind=block['type']
            if kind in styles:story.append(Paragraph(block['text'],styles[kind]))
            elif kind=='space':story.append(Spacer(1,block['height']))
            elif kind=='table':story.append(table(block['rows'],block['widths']));story.append(Spacer(1,10))
            elif kind=='image':story.append(Image(str(HERE/block['path']),width=block['width'],height=block['height']));story.append(Spacer(1,8))
    out=HERE/'Halo tilt - independent phase replication audit.pdf'
    assert not out.exists(), 'Preserve existing PDF versions.'
    SimpleDocTemplate(str(out),pagesize=(612,792),leftMargin=42,rightMargin=42,topMargin=43,bottomMargin=53,
        title='Halo tilt: independent phase replication audit',author='Research calculations with Codex').build(story,onFirstPage=footer,onLaterPages=footer)
    print(out)
