#!/usr/bin/env python3
"""Exact rational identities supporting PROOF.txt.

Requires SymPy and ramanujantools. This is separate from the standalone
arithmetic certificate, which requires only python-flint.
"""
import argparse,json,pickle,time
from pathlib import Path
import sympy as s
from ramanujantools import Matrix,Position
from ramanujantools.cmf import MeijerG,pFq

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cache-dir',type=Path,default=Path(__file__).resolve().parent/'symbolic_cache')
    args=parser.parse_args();args.cache_dir.mkdir(parents=True,exist_ok=True)
    n=s.Symbol('n');t=s.Symbol('t');started=time.monotonic()
    gs=(-1,-1,2,s.Rational(7,3),s.Rational(5,2),0,0,0,s.Rational(1,3),s.Rational(1,2))
    gd=(-10,-8,12,6,5,0,1,2,0,2)
    fs=gs[:5]+(1,1,s.Rational(4,3),s.Rational(3,2));fd=gd[:5]+(1,2,0,2)
    def load(name,cmf,axes,start,direction):
        path=args.cache_dir/(name+'.pickle')
        if path.exists():return pickle.loads(path.read_bytes())
        value=cmf.trajectory_matrix(Position(dict(zip(axes,direction))),Position(dict(zip(axes,start))))
        path.write_bytes(pickle.dumps(value));return value
    G=load('MG55',MeijerG(5,2,5,5,1),s.symbols('a0:5')+s.symbols('b0:5'),gs,gd)
    M=load('PFQ54',pFq(5,4,1),s.symbols('x0:5')+s.symbols('y0:4'),fs,fd)
    assert all(G[3,j]==0 for j in range(3));Q=G[:3,:3]
    K=Matrix([
        [(19440*n**4+13812*n**3+3219*n**2+308*n+11)/3,(6*n+1)*(720*n**2+443*n+46)/6,-5*(216*n**2+75*n+7)/6],
        [-(4320*n**3+4410*n**2+1045*n+69)/6,(360*n**2+115*n+8)/2,1],
        [-(1080*n**2+315*n+7)/6,-2,0],[3,0,0]])
    ar=s.rf(12*n+2,12)*s.rf(6*n+s.Rational(7,3),6)*s.rf(5*n+s.Rational(5,2),5)/(s.rf(2*n+1,2)*s.rf(2*n+s.Rational(3,2),2)*s.rf(10*n+2,10)*s.rf(8*n+2,8)*(n+1))
    c=s.factor(1/ar)
    residual=(M*K.subs({n:n+1})*Q.T-c*K).applyfunc(s.cancel)
    assert residual==s.zeros(4,3)
    print('Twelve forward/dual pairing identities vanish.',flush=True)
    g=3936600*(8*n+1)*(9*n+1)*(15*n+2)*(20*n+3)*(24*n+1)**2/((2*n+1)*(3*n+1)**2*(6*n+1)*(8*n+3)*(9*n+2)*(10*n+3)*(12*n+1)*(15*n+1)*(15*n+4)*(18*n+1)**2*(24*n+5)*(30*n+7))
    terms=[(12,s.Rational(2,3),-1),(8,1,1),(5,s.Rational(1,3),-1),(8,s.Rational(1,3),1),(6,1,-1),(5,1,1),(4,s.Rational(1,6),1),(9,s.Rational(1,2),-1),(6,s.Rational(2,3),1),(5,s.Rational(2,3),1),(4,s.Rational(1,3),-1)]
    det=s.Integer(2)**8*3**30*g.subs(n,n+1)/g*s.prod(s.rf(A*n+b,A)**m for A,b,m in terms)
    assert s.cancel(Q.det()-det)==0
    print('The exact gamma-product normalization identity vanishes.',flush=True)
    num=[(-2*n-1,-1,10*n+1),(-s.Rational(4,3),-1,6*n+1),(-2*n-s.Rational(3,2),-1,3*n+1)]
    den=[(0,1,10*n+2),(-n,1,9*n+2)]
    def power_sum(a,step,L,k):
        a,step,L=map(s.sympify,(a,step,L))
        return step**k*(s.bernoulli(k+1,a/step+L)-s.bernoulli(k+1,a/step))/(k+1)
    S=[s.factor(sum(power_sum(*z,k) for z in den)-sum(power_sum(*z,k) for z in num)) for k in (1,2,3)]
    coeff=[1,S[0],(S[0]**2+S[1])/2,(S[0]**3+3*S[0]*S[1]+2*S[2])/6]
    assert s.factor(sum(K[j,0]*coeff[j] for j in range(4)))==0
    ratio=(t+12*n+2)/(t+2*n+1)*(t+6*n+s.Rational(7,3))/(t+s.Rational(4,3))*(t+5*n+s.Rational(5,2))/(t+2*n+s.Rational(3,2))*(t-10*n-1)/(t+1)*(t-8*n-1)/(t+n+1)
    aa=[s.sympify(a)+n*d for a,d in zip(fs[:5],fd[:5])]
    bb=[s.sympify(b)+n*d for b,d in zip(fs[5:],fd[5:])]
    assert s.cancel(ratio-s.prod(t+a for a in aa)/((t+1)*s.prod(t+b for b in bb)))==0
    result=dict(all_symbolic_checks_passed=True,pairing_zero_entries=12,determinant_gamma_residual='0',forward_infinity_residue='0',forward_gamma_shift_residual='0',c=str(c),seconds=time.monotonic()-started)
    (Path(__file__).resolve().parent/'symbolic_pairing_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
