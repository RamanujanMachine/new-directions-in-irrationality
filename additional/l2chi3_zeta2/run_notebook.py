"""Run every notebook cell through IPython without opening local sockets."""
from pathlib import Path
import json, time, sys, os
path=Path(sys.argv[1]).resolve()
runtime=path.parent/'notebook_outputs'/'ipython_runtime'
runtime.mkdir(parents=True,exist_ok=True)
os.environ['IPYTHONDIR']=str(runtime)
from IPython.core.interactiveshell import InteractiveShell
from IPython.utils.capture import capture_output
os.chdir(path.parent)
nb=json.loads(path.read_text())
shell=InteractiveShell.instance()
started=time.monotonic()
def save():path.write_text(json.dumps(nb,indent=1,ensure_ascii=False)+'\n')
for i,cell in enumerate(nb['cells']):
    if cell['cell_type']!='code':continue
    source=cell['source'];source=''.join(source) if isinstance(source,list) else source
    print(f'CELL {i}: {source.splitlines()[0][:90]}',flush=True)
    begun=time.monotonic()
    with capture_output(stdout=True,stderr=True,display=True) as captured:
        execution=shell.run_cell(source,store_history=True,silent=False)
    cell['execution_count']=execution.execution_count
    cell['outputs']=[]
    for name,content in [('stdout',captured.stdout),('stderr',captured.stderr)]:
        if content:
            cell['outputs'].append(dict(output_type='stream',name=name,text=content))
            print(content,end='',flush=True)
    for output in captured.outputs:
        cell['outputs'].append(dict(output_type='display_data',data=output.data,metadata=output.metadata))
    error=execution.error_before_exec or execution.error_in_exec
    if error:
        cell['outputs'].append(dict(output_type='error',ename=type(error).__name__,
                                   evalue=str(error),traceback=[str(error)]))
        save();raise RuntimeError(f'cell {i}: {error}')
    cell['metadata']['execution_seconds']=time.monotonic()-begun
    save();print(f'CELL {i} DONE ({time.monotonic()-begun:.2f}s)',flush=True)
nb['metadata']['execution_verified']=True
nb['metadata']['execution_engine']='IPython InteractiveShell (sequential persistent namespace)'
nb['metadata']['execution_seconds']=time.monotonic()-started
save();print(f'ALL CELLS PASSED in {time.monotonic()-started:.2f}s',flush=True)
