"""Export five-point data and rational PSD witnesses; Lean recomputes all checks."""
import sys,json,math
from fractions import Fraction as Q
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'proofs/s3/0.400695372__c2/five_point'
sys.path.insert(0,str(DATA))
from field import F,interval
import numpy as np
OUT=ROOT/'lean/Fast/Five';OUT.mkdir(exist_ok=True)
cert=json.loads((DATA/'n5_field_certificate.json').read_text());cover=json.loads((DATA/'n5_cut2_exact_cover.json').read_text())
def rat(v):
 v=Q(v)
 return str(v.numerator) if v.denominator==1 and v>=0 else f'({v.numerator})' if v.denominator==1 else f'(({v.numerator} : Rat) / {v.denominator})'
def fk(x):return '⟨'+', '.join(rat(v) for v in F(x).v)+'⟩'
def arr(xs):return '#['+', '.join(xs)+']'
def lst(xs):return '['+', '.join(xs)+']'
def mat(A):return arr([arr([fk(v) for v in row]) for row in A])
lo,hi=interval(80)
source=['import Fast.Five.Check','set_option maxRecDepth 10000','namespace Fast.Five.Data',f'def encLo : Int := {int(lo*2**80)}',f'def encHi : Int := {int(hi*2**80)}','def encM : Nat := 80','def low : Rat := (encLo : Rat) / 2^encM','def high : Rat := (encHi : Rat) / 2^encM']
for bi,b in enumerate(cert['blocks']):
 W=[[F(v) for v in row] for row in b['basis']];Y=[[F(v) for v in row] for row in b['matrix']];k=len(Y);d=len(W)
 WY=[[sum((a*c for a,c in zip(row,col)),F(0)) for col in zip(*Y)] for row in W]
 expanded=[[sum((a*c for a,c in zip(row,col)),F(0)) for col in W] for row in WY]
 gram=np.linalg.cholesky(np.array([[float(v) for v in row] for row in Y])-0.05*np.eye(k));den=10**6;G=[[round(float(v)*den) for v in row] for row in gram]
 # Confirm rational interval row dominance before emitting.
 def low(v):return v.v[0]+sum(a*(lo**i if a>=0 else hi**i) for i,a in enumerate(v.v[1:],1))
 def high(v):return v.v[0]+sum(a*(hi**i if a>=0 else lo**i) for i,a in enumerate(v.v[1:],1))
 R=[[Y[i][j]-Q(sum(a*c for a,c in zip(G[i],G[j])),den**2) for j in range(k)] for i in range(k)]
 assert all(low(R[i][i])>sum(max(-low(R[i][j]),high(R[i][j])) for j in range(k) if j!=i) for i in range(k))
 sparse=arr([lst([f'({j}, {fk(v)})' for j,v in enumerate(row) if v]) for row in W])
 source.append(f'''def block{bi} : Block := {{
  roots := {b['t']}, flagSize := {b['f']}, ty := {b['type']}
  flags := {arr(list(map(str,b['flags'])))}
  basis := {sparse}
  matrix := {mat(Y)}
  expanded := {mat(expanded)}
  gram := {arr([lst([str(v) if v>=0 else f'({v})' for v in row]) for row in G])}
  gramDen := {den}
}}''')
source.append('def blocks : Array Block := '+arr([f'block{i}' for i in range(len(cert['blocks']))]))
source.extend(['def wHalf : Rat := 890169 / 200000','def wTwice : Rat := 135203 / 250000','def nu : Array Rat := #[3991657/1000000,3991657/1000000,2903639/500000,544009/250000]'])
patterns={p:i for i,p in enumerate(cover['patterns'])};pruned=cover['pruned']
source.append('def patterns : Array Nat := '+arr([str(sum(1<<i for i,c in enumerate(p) if c=='+')) for p in patterns]))
def tree(prefix):
 if prefix in patterns:return f'(.retained {patterns[prefix]})'
 if prefix in pruned:
  w={int(k):Q(v) for k,v in pruned[prefix].items()};den=math.lcm(*(v.denominator for v in w.values()));ints={k:int(v*den) for k,v in w.items()};g=math.gcd(*ints.values())
  return '(.excluded '+lst([f'({k},{v//g})' for k,v in ints.items()])+')'
 assert len(prefix)<20
 return '(.branch '+tree(prefix+'+')+' '+tree(prefix+'-')+')'
source.append('def cover : Cover := '+tree(''))
source.append('''def endpointOk (p : Pattern) : Bool :=
  decide (0 ≤ lower low high (K.bstar.sub (score blocks wHalf wTwice nu p K.bstar))) &&
  decide (0 ≤ lower low high ((K.ofRat (1-9/10000)).sub (score blocks wHalf wTwice nu p K.one)))
end Fast.Five.Data''')
(OUT/'Data.lean').write_text('\n\n'.join(source)+'\n')
# Separate compiler processes release the kernel evaluator's caches between batches.
CHECKS=OUT/'Checks';CHECKS.mkdir(exist_ok=True)
imports=[]
header=['import Fast.Five.Data','set_option maxRecDepth 10000',
        'set_option maxHeartbeats 0','namespace Fast.Five.Checked']
def emit(name, declarations):
 imports.append('import Fast.Five.Checks.'+name)
 (CHECKS/(name+'.lean')).write_text('\n\n'.join(header+declarations+['end Fast.Five.Checked'])+'\n')
def checked(name,expr):return f'theorem {name} : {expr} = true := by decide +kernel'
emit('Base',[checked('enclosure','enclosureOk Data.encLo Data.encHi Data.encM')]+
 [checked(f'shape{i}',f'blockShape Data.block{i}') for i in range(len(cert['blocks']))])
emit('Cover',[checked('cover','coverOk Data.patterns Data.cover 0 0')])
aggregates=[]
def family(name,expressions,statement):
 names=[f'{name}_{i}' for i in range(len(expressions))]
 for i in range(0,len(expressions),4):
  emit(name.capitalize()+str(i//4),[checked(names[j],expressions[j])
       for j in range(i,min(i+4,len(expressions)))])
 chain='true'
 for expr in reversed(expressions):chain=f'({expr} && {chain})'
 aggregates.append(f'theorem {name} : {statement} = true := by\n'
   f'  change {chain} = true\n  simp only ['+', '.join(names)+', Bool.true_and]')
for bi,b in enumerate(cert['blocks']):
 family(f'psd{bi}',[f'psdRow Data.low Data.high Data.block{bi} {i}' for i in range(len(b['matrix']))],
        f'(List.range {len(b["matrix"])}).all (psdRow Data.low Data.high Data.block{bi})')
 family(f'expanded{bi}',[f'expandedRow Data.block{bi} {i}' for i in range(len(b['basis']))],
        f'(List.range {len(b["basis"])}).all (expandedRow Data.block{bi})')
family('endpoints',[f'Data.endpointOk Data.patterns[{i}]!' for i in range(len(patterns))],
       'Data.patterns.toList.all Data.endpointOk')
(OUT/'Checked.lean').write_text('\n'.join(imports)+'\n\n'+
 '\n\n'.join(header[1:]+aggregates+['end Fast.Five.Checked'])+'\n')
print('Exported',OUT/'Data.lean','and',len(imports),'check batches')
