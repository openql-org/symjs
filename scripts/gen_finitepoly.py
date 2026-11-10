"""Generate independent finite-field polynomial references with SymPy 1.14.0."""
import json
from pathlib import Path
import sympy as s

assert s.__version__ == '1.14.0'
x,y = s.symbols('x y')
refs = {'unary': [], 'binary': [], 'ground': [], 'cancel': [], 'construct': []}
def result(call):
    try:
        value = call()
        return {'result': str(value)}
    except Exception as e:
        return {'error': type(e).__name__}

for p in [2,3,5,7]:
    for expression in ['0','1','2*x+2','x**5+2*x**3+3*x+1','(x+1)**6*(x+2)**3']:
        f = s.Poly(s.sympify(expression),x,modulus=p)
        for op, call in [('construct', lambda:f),('neg',lambda:-f),('diff',f.diff),
            ('monic',f.monic),('primitive',f.primitive),('content',f.content),
            ('factorList',f.factor_list),('sqfList',f.sqf_list),('integrate',f.integrate),
            ('eval',lambda:f.eval(3)),('pow',lambda:f**3)]:
            refs['unary'].append(dict(p=p,input=expression,op=op,**result(call)))
    for a,b in [('x**3+2*x+1','2*x+1'),('x**4-1','x**2-1'),('0','x+1'),('x+1','0')]:
        f,g=(s.Poly(s.sympify(e),x,modulus=p) for e in [a,b])
        for op,call in [('add',lambda:f+g),('sub',lambda:f-g),('mul',lambda:f*g),
            ('div',lambda:f.div(g)),('gcd',lambda:f.gcd(g)),('lcm',lambda:f.lcm(g)),
            ('exquo',lambda:f.exquo(g)),('gcdex',lambda:f.gcdex(g))]:
            refs['binary'].append(dict(p=p,a=a,b=b,op=op,**result(call)))
    f=s.Poly(3*x**2+4*x+2,x,modulus=p)
    for c in [0,2,7]:
        for op,call in [('addGround',lambda:f.add_ground(c)),('subGround',lambda:f.sub_ground(c)),
            ('mulGround',lambda:f.mul_ground(c)),('quoGround',lambda:f.quo_ground(c)),
            ('exquoGround',lambda:f.exquo_ground(c))]:
            refs['ground'].append(dict(p=p,c=c,op=op,**result(call)))
    for expression in ['(x**2+1)/(x+1)','(x**2+2*x+1)/(2*x+2)','1/(2*x+1)','2/x','2/3']:
        refs['cancel'].append(dict(p=p,input=expression,**result(lambda:s.cancel(s.sympify(expression),domain=s.GF(p)))))
for expression,gens,p in [('7*x**2+10*x-8',[x],5),('x*y+7*x+5*y+10',[x,y],5),('x+1',[x],1),('x/2',[x],5),('2.0*x+1',[x],5)]:
    refs['construct'].append(dict(input=expression,gens=list(map(str,gens)),p=p,**result(lambda:s.Poly(s.sympify(expression),*gens,modulus=p))))
f=s.Poly(x**2*y+x*y**2+y+1,x,y,modulus=5);g=s.Poly(2*x*y+1,x,y,modulus=5)
refs['multi_div'] = str(f.div(g))
refs['multi_add'] = str(s.Poly(x+1,x,modulus=5)+s.Poly(y,y,modulus=5))
refs['multi_eval'] = str(f.eval(x,2))
refs['multi_diff'] = str(f.diff(y))
refs['multi_integrate'] = str(f.integrate(y))
refs['factor_domain'] = str(s.factor(x**2+1,domain=s.GF(2)))
refs['gcd_domain'] = str(s.gcd(x**2+1,x+1,domain=s.GF(2)))
refs['lcm_domain'] = str(s.lcm(x**2+1,x+1,domain=s.GF(2)))
Path('packages/symjs/tests/polys/sympoly.finite.references.json').write_text(json.dumps(refs,indent=2)+'\n')
