"""Independent SymPy 1.14 fixtures for exact polynomial algorithms."""
import json
from pathlib import Path
import sympy as s
assert s.__version__ == '1.14.0'
x,y,z,a=s.symbols('x y z a')
refs={'algebraic':[],'finite':[],'intervals':[],'boxes':[],'dispersion':[],'roots':[]}
for expr,gens,ext in [
 ('x**4+1',[x],['sqrt(2)']),
 ('x**2-2*y**2',[x,y],['sqrt(2)']),
 ('(x+y+sqrt(2))*(x-sqrt(2)*y+1)',[x,y],['sqrt(2)']),
 ('(x+y+sqrt(2)*z)*(x-sqrt(2)*y+z)',[x,y,z],['sqrt(2)']),
 ('3*(x+sqrt(2)*y)**3*(x-sqrt(2)*y+1)/2',[x,y],['sqrt(2)']),
 ('(x+1)*(y+1)*(x-y)',[x,y],['sqrt(2)']),
 ('(x+sqrt(2)*y)*(x+I*y)',[x,y],['sqrt(2)','I']),
 ('x**6-2',[x],['2**(1/3)']),
]:
 f=s.Poly(expr,*gens,extension=[s.sympify(t) for t in ext]);print('algebraic',expr,flush=True)
 c,fs=(s.Poly(expr,*gens).factor_list() if expr=='(x+1)*(y+1)*(x-y)' else f.factor_list())
 refs['algebraic'].append(dict(expr=expr,gens=list(map(str,gens)),extension=ext,content=str(c),factors=[[str(g.as_expr()),k] for g,k in fs],norm=str(f.norm().as_expr())))
for modulus in [2,3,5,7]:
 for aa,bb,gens in [('(x+y)*(x*y+1)','(x+y)*(y+1)',[x,y]),('x*y+y','x*y**2+y**2',[x,y]),('(x+y)*(y+z)','(x+y)*(y+z+1)',[x,y,z]),('0','x+y',[x,y]),('0','0',[x,y]),('x+1','x*y+1',[x,y])]:
  f,g=(s.Poly(e,*gens,modulus=modulus) for e in [aa,bb]);refs['finite'].append(dict(a=aa,b=bb,gens=list(map(str,gens)),p=modulus,gcd=str(f.gcd(g).as_expr()),lcm=str(f.lcm(g).as_expr()) if not(f.is_zero and g.is_zero) else '0',subresultants=[str(h.as_expr()) for h in f.subresultants(g)],discriminant=str(f.discriminant().as_expr()),discriminantExact=str(s.Poly(s.discriminant(s.sympify(aa),gens[0]),*gens,modulus=modulus).as_expr())))
for expr in ['sqrt(2)+sqrt(3)','1/(sqrt(2)-sqrt(3))','cos(pi/7)','sin(3*pi/7)','tan(pi/7)','sqrt(2)+cos(pi/7)','sqrt(3-sqrt(2))','GoldenRatio+sqrt(2)']:
 v=s.sympify(expr,locals={'TribonacciConstant':s.S.TribonacciConstant})
 try: iv=s.polys.numberfields.isolate(v,eps=s.Rational(1,1000))
 except NameError:
  iv=next(iv for iv,m in s.Poly(s.minpoly(v,x),x).intervals(eps=s.Rational(1,1000)) if iv[0]<s.N(v,85)<iv[1])
 refs['intervals'].append(dict(expr=expr,interval=list(map(str,iv))))
for expr in ['sqrt(2)','(1+I)**(1/3)','(-2+I)**(1/3)','(-2-I)**(1/3)','(1-2*I)**(1/3)','(I)**(1/3)','(-I)**(1/3)','(-2)**(1/3)','1/(2+I)','1/(2-I)','sin(-3*pi/7)','cos(11*pi/7)','exp(2*I*pi/7)','GoldenRatio','TribonacciConstant']:
 v=s.sympify(expr,locals={'TribonacciConstant':s.S.TribonacciConstant});re,im=v.as_real_imag();refs['boxes'].append(dict(expr=expr,re=str(s.Rational(str(s.N(re,85)))),im=str(s.Rational(str(s.N(im,85))))))
from sympy.polys.dispersion import dispersionset
for expr,ext in [('x**4+1',['sqrt(2)']),('x**3-2',['2**(1/3)']),('(x-sqrt(2))*(x-sqrt(2)-3)',['sqrt(2)']),('(x-I)*(x-I-2)',['I'])]:
 f=s.Poly(expr,x,extension=[s.sympify(t) for t in ext]);g=f.shift(-2)
 refs['dispersion'].append(dict(a=str(f.as_expr()),b=str(g.as_expr()),extension=ext,shifts=sorted(map(int,dispersionset(f,g)))))
for expr in ['x**3-8*x+16','(x**2-2)*(10**60*x**2-2*10**60-1)','x**3/8-x+2']:
 f=s.sympify(expr);refs['roots'].append(dict(expr=expr,roots=[str(s.CRootOf(f,i)) for i in range(s.degree(f,x))]))
f=s.Poly(x**3-x+s.sqrt(2)/10**15,x,extension=s.sqrt(2))
refs['liftedRoots']=[dict(expr=str(f.as_expr()),roots=list(map(str,f.real_roots())))]
path=Path(__file__).resolve().parents[3]/'packages/symjs/tests/polys/continuation.references.json'
path.write_text(json.dumps(refs,indent=2)+'\n')

methods=[]
for modulus,expr in [(5,'x**3+x+1'),(5,'(x+1)**5'),(7,'(x**2+2*x)**3+2*(x**2+2*x)+1'),(5,'(x+2)**2*(x-1)'),(5,'0')]:
 f=s.Poly(expr,x,modulus=modulus)
 row=dict(expr=expr,p=modulus,sqfPart=str(f.sqf_part().as_expr()),sturm=[str(g.as_expr()) for g in f.sturm()],groundRoots=[[str(c),k] for c,k in f.ground_roots().items()])
 if not f.is_zero:
  row['decompose']=[str(g.as_expr()) for g in f.decompose()]
  if f.TC()!=0:row['revert']=str(f.revert(5).as_expr())
 methods.append(row)
path.with_name('finite-methods.references.json').write_text(json.dumps(methods,indent=2)+'\n')
