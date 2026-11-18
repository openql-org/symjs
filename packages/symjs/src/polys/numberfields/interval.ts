// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Rational outward interval arithmetic for the interval evaluation used by
// SymPy 1.14 polys/numberfields/utilities.py (BSD-3-Clause; see LICENSE).
import { Add, Constant, ExtensionExpr, Fn, Mul, Pow, Rational, type Expr } from '../../core/nodes';
import { at, defined, expectType, first } from '../../core/guard';
import { isReal } from '../../core/assumptions';
import { add, mul } from '../../core/ops';
import { expand } from '../../simplify/expand';
import { freeSymbols } from '../../core/traverse';
import { iroot, lcm } from '../../core/numbers';
import { NotImplementedError } from '../../core/errors';
import { UPoly } from '../poly';
import { isolateComplexRootsSqf, isolateRealRoots, refineRealRoot } from '../rootisolation';

export type RationalInterval = readonly [Rational,Rational];
export type AlgebraicBox = readonly [RationalInterval,RationalInterval];
const Q = (p: bigint,q=1n): Rational => Rational.of(p,q);
const zero=Q(0n),one=Q(1n),Z: RationalInterval=[zero,zero];
const plus=(a:Rational,b:Rational):Rational=>Q(a.p*b.q+b.p*a.q,a.q*b.q);
const times=(a:Rational,b:Rational):Rational=>Q(a.p*b.p,a.q*b.q);
const neg=(a:Rational):Rational=>Q(-a.p,a.q);
const inv=(a:Rational):Rational=>Q(a.q,a.p);
const abs=(a:Rational):Rational=>a.p<0n?neg(a):a;
const cmp=(a:Rational,b:Rational):number=>a.p*b.q<b.p*a.q?-1:a.p*b.q>b.p*a.q?1:0;
/** Round outward to keep Taylor-series denominators bounded. */
function dyadic(a:RationalInterval,bits:number):RationalInterval {
  const scale=1n<<BigInt(bits);
  const floor=(v:Rational):bigint=>{const n=v.p*scale;return n/v.q-(n<0n&&n%v.q!==0n?1n:0n);};
  return [Q(floor(a[0]),scale),Q(-floor(neg(a[1])),scale)];
}
const sum=(a:RationalInterval,b:RationalInterval):RationalInterval=>[plus(a[0],b[0]),plus(a[1],b[1])];
const negative=(a:RationalInterval):RationalInterval=>[neg(a[1]),neg(a[0])];
function product(a:RationalInterval,b:RationalInterval):RationalInterval {
  const cs=[times(a[0],b[0]),times(a[0],b[1]),times(a[1],b[0]),times(a[1],b[1])].sort(cmp);
  return [first(cs),at(cs,3)];
}
function reciprocal(a:RationalInterval):RationalInterval {
  if(a[0].p<=0n&&a[1].p>=0n) throw new RangeError('interval denominator contains zero');
  return [inv(a[1]),inv(a[0])];
}
const boxAdd=(a:AlgebraicBox,b:AlgebraicBox):AlgebraicBox=>[sum(a[0],b[0]),sum(a[1],b[1])];
const boxMul=(a:AlgebraicBox,b:AlgebraicBox):AlgebraicBox=>[sum(product(a[0],b[0]),negative(product(a[1],b[1]))),sum(product(a[0],b[1]),product(a[1],b[0]))];
const roundBox=(a:AlgebraicBox,bits:number):AlgebraicBox=>[dyadic(a[0],bits+8),dyadic(a[1],bits+8)];
function integerPower(a:AlgebraicBox,n:bigint,bits:number):AlgebraicBox {
  if(n<0n){
    const square=(v:RationalInterval):RationalInterval=>[v[0].p<=0n&&v[1].p>=0n?zero:cmp(abs(v[0]),abs(v[1]))<0?times(v[0],v[0]):times(v[1],v[1]),cmp(abs(v[0]),abs(v[1]))>0?times(v[0],v[0]):times(v[1],v[1])];
    const d=reciprocal(sum(square(a[0]),square(a[1])));
    return integerPower(roundBox([product(a[0],d),negative(product(a[1],d))],bits),-n,bits);
  }
  let r:AlgebraicBox=[[one,one],Z],b=a;
  for(let k=n;k;k>>=1n){if(k&1n)r=roundBox(boxMul(r,b),bits);b=roundBox(boxMul(b,b),bits);}
  return r;
}
function root(a:Rational,n:bigint,bits:number):RationalInterval {
  const scale=1n<<BigInt(bits), value=a.p*scale**n/a.q, r=iroot(value,n);
  return [Q(r,scale),Q(r**n*a.q===a.p*scale**n?r:r+1n,scale)];
}
function atanReciprocal(n:bigint,eps:Rational):RationalInterval {
  let power=Q(1n,n),value=zero;
  for(let k=0n;;k++){
    const term=times(power,Q(1n,2n*k+1n));value=plus(value,k%2n?neg(term):term);
    power=times(power,Q(1n,n*n));
    const error=times(power,Q(1n,2n*k+3n));
    if(cmp(error,eps)<0)return [plus(value,neg(error)),plus(value,error)];
  }
}
function pi(bits:number):RationalInterval {
  const eps=Q(1n,1n<<BigInt(bits+8));
  return dyadic(sum(product([Q(16n),Q(16n)],atanReciprocal(5n,eps)),product([Q(-4n),Q(-4n)],atanReciprocal(239n,eps))),bits+4);
}
function trig(c:Rational,cosine:boolean,bits:number):RationalInterval {
  const residue=((c.p%(2n*c.q))+2n*c.q)%(2n*c.q);
  const angle=Q(residue>c.q?residue-2n*c.q:residue,c.q);
  return sinCosInterval(product([angle,angle],pi(bits)),cosine,bits);
}
function sinCosInterval(input:RationalInterval,cosine:boolean,bits:number):RationalInterval {
  const iv=dyadic(input,bits+8);
  const x=times(plus(iv[0],iv[1]),Q(1n,2n)),radius=times(plus(iv[1],neg(iv[0])),Q(1n,2n));
  let term=cosine?one:x,value=term;
  const x2=times(x,x),eps=Q(1n,1n<<BigInt(bits));
  for(let k=0n;;k++){
    const a=2n*k+(cosine?1n:2n);
    term=times(neg(term),times(x2,Q(1n,a*(a+1n))));
    const error=abs(term);
    if(k>=1n&&cmp(error,eps)<0){const e=plus(error,radius);return dyadic([plus(value,neg(e)),plus(value,e)],bits+4);}
    value=plus(value,term);
  }
}
function atanPoint(x:Rational,bits:number):RationalInterval {
  if(x.p<0n)return negative(atanPoint(neg(x),bits));
  if(cmp(x,one)>0)return sum(product(pi(bits),[Q(1n,2n),Q(1n,2n)]),negative(atanPoint(inv(x),bits)));
  const sqrt=root(plus(one,times(x,x)),2n,bits),u=dyadic(product([x,x],reciprocal(sum([one,one],sqrt))),bits+8);
  const t=times(plus(u[0],u[1]),Q(1n,2n)),radius=times(plus(u[1],neg(u[0])),Q(1n,2n));
  let power=t,value=t;
  const t2=times(t,t),eps=Q(1n,1n<<BigInt(bits));
  for(let k=1n;;k++){
    power=times(power,t2);
    const next=times(power,Q(1n,2n*k+1n));
    if(cmp(abs(next),eps)<0){const error=plus(abs(next),radius);return dyadic([times(Q(2n),plus(value,neg(error))),times(Q(2n),plus(value,error))],bits+4);}
    value=plus(value,k%2n?neg(next):next);
  }
}
function argument(box:AlgebraicBox,bits:number):RationalInterval {
  const [x,y]=box,atan=(v:RationalInterval):RationalInterval=>[atanPoint(v[0],bits)[0],atanPoint(v[1],bits)[1]];
  if(x[0].p>0n)return atan(product(y,reciprocal(x)));
  if(x[1].p<0n&&y[0].p>0n)return sum(pi(bits),atan(product(y,reciprocal(x))));
  if(x[1].p<0n&&y[1].p<0n)return sum(negative(pi(bits)),atan(product(y,reciprocal(x))));
  if(y[0].p>0n)return sum(product(pi(bits),[Q(1n,2n),Q(1n,2n)]),negative(atan(product(x,reciprocal(y)))));
  if(y[1].p<0n)return sum(product(pi(bits),[Q(-1n,2n),Q(-1n,2n)]),negative(atan(product(x,reciprocal(y)))));
  throw new RangeError('argument interval crosses the branch cut');
}
/** A certified rational rectangle containing the algebraic expression. @internal */
export function algebraicEnclosure(expression:Expr,bits:number):AlgebraicBox {
  const eps=Q(1n,1n<<BigInt(bits));
  const visit=(e:Expr):AlgebraicBox=>{
    if(e instanceof Rational)return [[e,e],Z];
    if(e instanceof Constant&&e.name==='I')return [Z,[one,one]];
    if(e instanceof Constant&&(e.name==='GoldenRatio'||e.name==='TribonacciConstant')){
      const f=e.name==='GoldenRatio'?[1n,-1n,-1n]:[1n,-1n,-1n,-1n];
      const intervals=isolateRealRoots([[f,1]]),[a,b]=at(intervals,intervals.length-1)[0];
      return [refineRealRoot(f,a,b,{eps}),Z];
    }
    if(e instanceof Pow&&e.base instanceof Constant&&e.base.name==='E'){
      const factors=e.exp instanceof Mul?e.exp.args:[e.exp];
      let c=one,imaginary=false,hasPi=false;
      for(const f of factors){if(f instanceof Constant&&f.name==='I')imaginary=true;else if(f instanceof Constant&&f.name==='pi')hasPi=true;else if(f instanceof Rational)c=times(c,f);else throw new NotImplementedError('exponential exponent must be a rational multiple of I*pi');}
      if(!imaginary||!hasPi)throw new NotImplementedError('algebraic exponential must be a root of unity');
      return [trig(c,true,bits),trig(c,false,bits)];
    }
    if(e instanceof Add)return e.args.reduce<AlgebraicBox>((a,b)=>roundBox(boxAdd(a,visit(b)),bits),[Z,Z]);
    if(e instanceof Mul)return e.args.reduce<AlgebraicBox>((a,b)=>roundBox(boxMul(a,visit(b)),bits),[[one,one],Z]);
    if(e instanceof Pow&&e.exp instanceof Rational){
      const a=visit(e.base),n=e.exp;
      if(n.isInteger)return integerPower(a,n.p,bits);
      if(isReal(e.base)!==true&&(a[1][0].p!==0n||a[1][1].p!==0n)){
        const square=(v:RationalInterval):RationalInterval=>v[0].p<=0n&&v[1].p>=0n?[zero,cmp(abs(v[0]),abs(v[1]))>0?times(v[0],v[0]):times(v[1],v[1])]:product(v,v);
        const absoluteSquared=sum(square(a[0]),square(a[1]));
        const lo=root(absoluteSquared[0],2n*n.q,bits),hi=root(absoluteSquared[1],2n*n.q,bits),magnitude:RationalInterval=[lo[0],hi[1]];
        const angle=product(argument(a,bits),[Q(1n,n.q),Q(1n,n.q)]);
        return integerPower([product(magnitude,sinCosInterval(angle,true,bits)),product(magnitude,sinCosInterval(angle,false,bits))],n.p,bits);
      }
      if(a[0][0].p<0n&&a[0][1].p>0n)throw new RangeError('root interval crosses the branch point');
      const negativeBase=a[0][1].p<0n,iv=negativeBase?negative(a[0]):a[0];
      const lo=root(iv[0],n.q,bits),hi=root(iv[1],n.q,bits),magnitude:RationalInterval=[lo[0],hi[1]];
      const value:AlgebraicBox=negativeBase?[product(magnitude,trig(Q(1n,n.q),true,bits)),product(magnitude,trig(Q(1n,n.q),false,bits))]:[magnitude,Z];
      return integerPower(value,n.p,bits);
    }
    if(e instanceof Fn&&['re','im','conjugate'].includes(e.name)){
      const value=visit(first(e.args));
      return e.name==='re'?[value[0],Z]:e.name==='im'?[value[1],Z]:[value[0],negative(value[1])];
    }
    if(e instanceof Fn&&['sin','cos','tan'].includes(e.name)){
      const arg=first(e.args),factors=arg instanceof Mul?arg.args:[arg];
      let c=one,hasPi=false;
      for(const f of factors){if(f instanceof Constant&&f.name==='pi')hasPi=true;else if(f instanceof Rational)c=times(c,f);else throw new NotImplementedError('trigonometric argument must be a rational multiple of pi');}
      if(!hasPi)throw new NotImplementedError('trigonometric argument must contain pi');
      const s=trig(c,false,bits),t=trig(c,true,bits);
      return [e.name==='sin'?s:e.name==='cos'?t:product(s,reciprocal(t)),Z];
    }
    if(e instanceof ExtensionExpr&&e.name==='CRootOf'){
      const def=at(e.args,0),index=expectType(at(e.args,1),(v):v is Rational=>v instanceof Rational,'root index');
      const gen=first([...freeSymbols(def)]),p=defined(UPoly.fromExpr(def,gen),'rational root polynomial');
      const den=p.coeffs.reduce((d,c)=>lcm(d,c.q),1n),ints=[...p.coeffs].reverse().map((c)=>c.p*den/c.q);
      const reals=isolateRealRoots([[ints,1]]),i=Number(index.p);
      if(i<reals.length){const [a,b]=at(reals,i)[0];return [a.equals(b)?[a,b]:refineRealRoot(ints,a,b,{eps}),Z];}
      const iv=at(isolateComplexRootsSqf(ints),i-reals.length).refineSize(eps,eps);
      return [[iv.ax,iv.bx],[iv.ay,iv.by]];
    }
    throw new NotImplementedError('unsupported algebraic interval expression');
  };
  return visit(expression);
}

/** Certified comparison of distinct real algebraic values. @internal */
export function compareAlgebraicReal(a:Expr,b:Expr):number {
  const delta=expand(add(a,mul(-1,b)));
  if(delta instanceof Rational)return delta.p<0n?-1:delta.p>0n?1:0;
  for(let bits=32;;bits*=2){
    try {
      const [iv]=algebraicEnclosure(delta,bits);
      if(iv[0].p>0n)return 1;
      if(iv[1].p<0n)return -1;
    } catch(error){if(!(error instanceof RangeError))throw error;}
  }
}
