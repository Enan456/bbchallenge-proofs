import pathlib, sys

for f, ns, src in [
    ('Dossier2RawTM.lean', 'Dossier2RawTM', 'abstract_d2.lean'),
    ('Dossier3RawTM.lean', 'Dossier3RawTM', 'abstract_d3.lean'),
]:
    p = pathlib.Path(f'/Users/enan/Documents/bbchallenge-proofs/busy-beaver-core/BusyBeaverCore/{f}')
    s = p.read_text()
    text = pathlib.Path(src).read_text()
    MARK = '-- ABSTRACT-BEGIN (generated)'
    if MARK in s:
        i = s.index(MARK)
        j = s.index(f'end QIG.{ns}', i)
        s = s[:i] + s[j:]
        s = '\n'.join(ln for ln in s.split('\n')
                      if not (ln.startswith(f'#print axioms QIG.{ns}.meta')
                              or ln.startswith(f'#print axioms QIG.{ns}.dossier')
                              or ln.startswith(f'#print axioms QIG.{ns}.cprobe_safe_of_safe')
                              or ln.startswith(f'#print axioms QIG.{ns}.bprobe_safe_of_safe')))
    end = f'end QIG.{ns}'
    s = s.replace(end, text + '\n\n' + end)
    n = '2' if ns == 'Dossier2RawTM' else '3'
    s = s.rstrip() + f'''
#print axioms QIG.{ns}.meta_transport
#print axioms QIG.{ns}.dossier{n}_nonhalting_of_safeMetaOrbit
'''
    p.write_text(s)
    print(f'abstract layer inserted into {f}')
