import pathlib, subprocess, json, sys
root=pathlib.Path.cwd()
results=[]
for p in sorted((root/'validation/controls_angular').glob('*.lean')):
    cmd=['lake','env','lean','-j1','-DwarningAsError=true',str(p.relative_to(root))]
    r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    expected=0 if p.stem=='Positive' else 1
    log=root/'reports/angular_controls'/f'{p.stem}.log'
    log.write_text('$ '+' '.join(cmd)+'\n'+r.stdout+f'\nEXIT:{r.returncode}\n')
    ok=(r.returncode==0) if expected==0 else (r.returncode!=0 and 'error:' in r.stdout)
    results.append(dict(file=str(p.relative_to(root)),expected='pass' if expected==0 else 'reject',exit=r.returncode,matched=ok,log=str(log.relative_to(root))))
    print(p.name,r.returncode,ok,flush=True)
(root/'reports/angular_controls/results.json').write_text(json.dumps(results,indent=2)+'\n')
sys.exit(0 if all(x['matched'] for x in results) else 1)
