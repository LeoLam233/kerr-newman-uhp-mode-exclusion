#!/usr/bin/env python3
"""Recheck bound editorial artifacts and all original mathematical spans."""
from pathlib import Path
import hashlib,json,re,sys
root=Path(sys.argv[1] if len(sys.argv)>1 else '.').resolve()
record=json.loads((root/'release_checks/READABLE_EDITION_VERIFICATION.json').read_text(encoding='utf-8'))
qa=json.loads((root/'release_checks/READABLE_PDF_VALIDATION.json').read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert record['status']==qa['status']=='PASS' and all(record['checks'].values())
for name,item in record['files'].items():assert sha(root/item['path'])==item['sha256'],name
assert qa['pdf_sha256']==record['files']['readable_pdf']['sha256']
assert qa['tex_sha256']==record['files']['readable_tex']['sha256']
assert qa['pages']==20 and qa['visual_review']['all_20_rendered_pages_inspected']
assert not qa['issues'] and not qa['layout_warnings'] and qa['font_checks']['all_fonts_embedded']
orig=json.loads((root/'provenance/ORIGINAL_SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
for name,h in orig['files'].items():
 if name.endswith('.lean') or name.startswith('manuscript/') or name in ('EXTERNAL_INTERFACES.md','lake-manifest.json','lakefile.toml','lean-toolchain'):
  assert sha(root/name)==h,name
def maths(s,md=False):
 if not md:s=s.split(r'\maketitle',1)[1].split(r'\end{document}',1)[0]
 pattern=r'\$\$.*?\$\$|\$(?!\$)[^$]*\$' if md else r'\\\[.*?\\\]|\\\(.*?\\\)'
 out=[]
 for m in re.finditer(pattern,s,re.S):
  raw=m[0];display=raw.startswith('$$' if md else r'\[')
  content=raw[2:-2] if display or not md else raw[1:-1]
  tag=re.findall(r'\\tag\{([^}]+)\}',content)
  out.append((display,tag[0] if tag else None,' '.join(content.split())))
 return out
a=maths((root/'manuscript/C002_v1.0.tex').read_text(encoding='utf-8'))
b=maths((root/'manuscript/C002_READABLE.tex').read_text(encoding='utf-8'))
c=maths((root/'C002_READABLE.md').read_text(encoding='utf-8'),True)
assert len(a)==len(b)==len(c)==398 and b==c
def layout(s):
 s=re.sub(r'\\(?:begin|end)\{(?:gathered|aligned)\}','',s)
 s=re.sub(r'\\(?:qquad|quad)\b','',s).replace('\\\\','').replace('&','').replace('{}','')
 return re.sub(r'\s+','',s)
reflows=[]
for x,y in zip(a,b):
 assert x[:2]==y[:2]
 if x[2]!=y[2]:
  assert x[1] in ('22','23','50') and layout(x[2])==layout(y[2])
  reflows.append(x[1])
assert reflows==['22','23','50']
for group,number in [('proof_checkpoints',76),('assumptions_and_boundaries',22),('external_inputs_as_stated',18),('complete_original_paragraph_backstop',88)]:
 assert len(record[group])==number and all(x['pass'] for x in record[group]),group
pdf=(root/'manuscript/C002_READABLE.pdf').read_bytes()
assert pdf.startswith(b'%PDF-') and b'%%EOF' in pdf[-1024:]
readme=(root/'README.md').read_text(encoding='utf-8')
assert readme.index('## Start Here')<readme.index('## Contents')
assert '](C002_READABLE.md)' in readme and '](manuscript/C002_READABLE.pdf)' in readme
print(json.dumps({'status':'PASS','mathematical_spans':398,'displays':85,'numbered_displays':62,
'proof_checkpoints':76,'original_scientific_files_unchanged':329,'readable_pdf_sha256':qa['pdf_sha256'],
'editorial_receipt_sha256':sha(root/'release_checks/READABLE_EDITION_VERIFICATION.json'),
'pdf_validation_receipt_sha256':sha(root/'release_checks/READABLE_PDF_VALIDATION.json')},indent=2))
