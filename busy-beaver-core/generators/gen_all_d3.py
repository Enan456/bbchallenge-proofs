import pathlib, sys
sys.path.insert(0, '.')
from epicompile import Compiler, emit_episode
from plans_d2 import plans
from mirror_plans import mirror_plan

MARK = '-- EPISODES-BEGIN (generated)'
HELPERS = '''
/-- Constructive De Morgan for closed intervals. -/
theorem not_and_le' {a b q : Int} (h : ¬(a ≤ q ∧ q ≤ b)) :
    q < a ∨ b < q := by
  by_cases hx : a ≤ q
  · right
    by_cases hy : q ≤ b
    · exact absurd ⟨hx, hy⟩ h
    · omega
  · left
    omega
'''

cp = Compiler(mirror=True)
cp.A(MARK)
cp.A(HELPERS)
names = []
for pl0 in plans():
    pl = mirror_plan(pl0)
    emit_episode(cp, pl['name'], pl['doc'], pl['guards'], pl['in_shape'],
                 pl['segments'], pl['out_head'], pl['steps'],
                 pl['out_shape'], nat_vars=pl['nat_vars'])
    cp.A("")
    names.append(pl['name'])
text = "\n".join(cp.L)

p = pathlib.Path('/Users/enan/Documents/bbchallenge-proofs/busy-beaver-core/BusyBeaverCore/Dossier3RawTM.lean')
s = p.read_text()
if MARK in s:
    i = s.index(MARK)
    j = s.index('end QIG.Dossier3RawTM', i)
    s = s[:i] + s[j:]
    s = '\n'.join(ln for ln in s.split('\n')
                  if not ln.startswith('#print axioms QIG.Dossier3RawTM.episode_'))
end = 'end QIG.Dossier3RawTM'
s = s.replace(end, text + '\n' + end)
s = s.rstrip() + '\n' + '\n'.join(
    f'#print axioms QIG.Dossier3RawTM.{n}' for n in names) + '\n'
p.write_text(s)
print(f'inserted {len(names)} D3 episodes, {len(cp.L)} lines')
