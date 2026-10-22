#!/usr/bin/env python3
"""Exact algebraic checks for the initial state and recessive MG integral.

The analytic argument (beta integrals, absolute convergence and asymptotic
integration) is written in ANALYTIC_PROOF.txt. Optional Barnes quadrature is
an independent numerical regression, not a premise of that argument.
"""
import argparse, json, time
from pathlib import Path
import sympy as s
from flint import arb, ctx

def verify(matrix_file, quadrature=False):
    begun=time.monotonic()
    n,w,t=s.symbols('n w t')
    C,Z=s.symbols('C Z')
    data=json.loads(Path(matrix_file).read_text())
    Q=s.Matrix([[s.sympify(z,locals={'n':n}) for z in row]
                 for row in data['MG55']])[:3,:3]
    D=s.Matrix([[243648,-498096,264600]])
    X=s.Matrix([[190344,-389162,206743]])
    Y=s.Matrix([[400824,-819330,435234]])

    # Derive Bhat_0 directly from the six simple poles; no fitted constants.
    F0=(t+1)**2/((-t)*(1-t)*(s.Rational(1,3)-t)*(s.Rational(4,3)-t)
                 *(s.Rational(1,2)-t)*(s.Rational(3,2)-t))
    groups=[(s.S.Zero,[0,1]),(s.Rational(1,3),[0,1]),(s.Rational(1,2),[0,1])]
    rows=s.zeros(4,3); decomp=[0,0,0]
    for cl,(offset,indices) in enumerate(groups):
        for j in indices:
            rho=offset+j
            v=-s.cancel((t-rho)*F0).subs(t,rho)
            h=sum((1/(offset+l)**2 for l in range(1 if cl==0 else 0,j+1)),s.S.Zero)
            for k in range(3):
                rows[0,k]-=v*h*rho**k
                rows[cl+1,k]+=v*rho**k
                decomp[k]+=v*rho**k/(rho-t)
    assert all(s.cancel(t**k*F0-decomp[k])==0 for k in range(3))
    assert all(sum(rows[j,k] for j in (1,2,3))==0 for k in range(3))
    Bhat=s.Matrix([list(rows.row(j)) for j in (0,2,3)])
    state=s.Matrix([[1,s.Rational(9,2)*C+3*Z,2*Z]])*Bhat
    assert (D*state.T)[0]==3888
    assert s.expand((X*state.T)[0])==3888*C
    assert s.expand((Y*state.T)[0])==3888*Z

    # Three beta ratios and the fourth beta integral recover the Barnes kernel.
    pairs=[(2*n,10*n+2),(s.Rational(1,3),6*n+2),
           (2*n+s.Rational(1,2),3*n+2)]
    kernel=(s.gamma(w)*s.gamma(w+n)*s.gamma(w+2*n)*s.gamma(w+s.Rational(1,3))
            *s.gamma(w+2*n+s.Rational(1,2))*s.gamma(10*n+2-w)*s.gamma(8*n+2-w)
            /(s.gamma(w+12*n+2)*s.gamma(w+6*n+s.Rational(7,3))
              *s.gamma(w+5*n+s.Rational(5,2))))
    beta_product=s.prod(s.gamma(w+a)/s.gamma(w+a+b) for a,b in pairs)
    assert s.cancel(kernel-beta_product*s.gamma(w)*s.gamma(w+n)
                    *s.gamma(10*n+2-w)*s.gamma(8*n+2-w))==0
    assert s.expand((w+n)+(8*n+2-w))==9*n+2
    mellin_a=10*n+2
    numerator_powers=[s.expand(a-1+mellin_a) for a,b in pairs]+[11*n+1]
    assert numerator_powers==[12*n+1,10*n+s.Rational(4,3),12*n+s.Rational(3,2),11*n+1]
    prefactor=s.gamma(9*n+2)/(s.gamma(6*n+2)*s.gamma(3*n+2))
    bound_pairs=[(2*n,10*n+2),(s.Rational(1,3),6*n+2),
                 (2*n+s.Rational(1,2),3*n+2),(11*n+2,8*n+2)]
    beta_bound=prefactor*s.prod(s.gamma(a)*s.gamma(b)/s.gamma(a+b) for a,b in bound_pairs)
    gamma_bound=(s.gamma(s.Rational(1,3))*s.gamma(9*n+2)*s.gamma(2*n)
                 *s.gamma(10*n+2)*s.gamma(2*n+s.Rational(1,2))*s.gamma(11*n+2)*s.gamma(8*n+2)
                 /(s.gamma(12*n+2)*s.gamma(6*n+s.Rational(7,3))
                   *s.gamma(5*n+s.Rational(5,2))*s.gamma(19*n+4)))
    assert s.cancel(beta_bound-gamma_bound)==0
    eta=s.Rational(9**9*2**4*10**10*11**11*8**8,12**12*6**6*5**5*19**19)
    assert 9+2+10+2+11+8==12+6+5+19
    assert 0<eta<s.Rational(1,1000000)

    # Bounds on theta derivatives of H_z^(-a), using 0<=h<=1.
    a,h=s.symbols('a h')
    first=-a*h; second=s.expand(first**2-a*h*(1-h))
    assert s.expand(second-(a*(a+1)*h**2-a*h))==0
    derivative_bounds=[s.S.One,mellin_a,s.expand(mellin_a*(mellin_a+2))]

    # Actual unscaled roots: the entire state decays, the nonminimal modes grow.
    scale=s.limit(Q[0,0],n,s.oo)
    assert scale==156660580321280
    T=s.Matrix(3,3,lambda i,j:s.limit(n**i*Q[i,j]/Q[0,0]/(n+1)**j,n,s.oo))
    x=s.Symbol('x');p=s.Poly(T.charpoly(x).as_expr(),x)
    assert p.all_coeffs()==[1,-s.Rational(162060225797,305977695940),
        s.Rational(40100849267287098349209,374489401651004369934400),
        -s.Rational(25,7161587766945221818712445059146)]
    lo=s.Rational('3.25999287587431764165969620794e-29')-s.Rational('1e-58')
    hi=lo+2*s.Rational('1e-58')
    assert p.eval(lo)<0<p.eval(hi) and s.discriminant(p.as_expr(),x)<0
    assert scale*hi<eta<1
    assert scale**2*(-p.all_coeffs()[-1])/hi>1
    e=s.Matrix([[1,0,0]])
    observation=s.Matrix.vstack(e,e*T,e*T*T).det()
    assert observation!=0

    ctx.prec=256
    ball=lambda z:arb(int(s.numer(z)))/int(s.denom(z))
    real_interval=ball(lo).union(ball(hi))
    large_mod=ball(scale)*(-ball(p.all_coeffs()[-1])/real_interval).sqrt()
    initial_values=[]
    cv=(arb(2).zeta(arb(1)/3)-arb(2).zeta(arb(2)/3))/9;zv=arb(2).zeta()
    for entry in state:
        initial_values.append(ball(entry.coeff(C))*cv+ball(entry.coeff(Z))*zv+ball(entry.subs({C:0,Z:0})))
    assert initial_values[0]>0
    regressions=[]
    if quadrature:
        import mpmath as mp
        for dps in (50,80):
            mp.mp.dps=dps
            cc=(mp.zeta(2,mp.mpf(1)/3)-mp.zeta(2,mp.mpf(2)/3))/9;zz=mp.zeta(2)
            for k in range(3):
                def integrand(y):
                    ss=mp.mpc(-.5,y)
                    f=(ss+1)**2/((-ss)*(1-ss)*(mp.mpf(1)/3-ss)*(mp.mpf(4)/3-ss)
                                   *(mp.mpf(1)/2-ss)*(mp.mpf(3)/2-ss))
                    return mp.pi*mp.re(ss**k*f)/mp.cosh(mp.pi*y)**2
                integral=mp.quad(integrand,[0,1,3,8,mp.inf])
                exact=mp.mpf(str(s.N(state[k].subs({C:str(cc),Z:str(zz)}),dps)))
                difference=abs(integral-exact)
                assert difference<mp.mpf(10)**(-dps+6)
                regressions.append(dict(dps=dps,k=k,barnes=mp.nstr(integral,35),
                                        absolute_difference=mp.nstr(difference,8)))
    return dict(algebraic_checks_passed=True,initial_state=[str(z) for z in state],
        initial_state_values=[z.str(30) for z in initial_values],
        denominator_initial_pairing='3888',C_initial_pairing='3888*C',Z_initial_pairing='3888*Z',
        positive_integral_prefactor=str(prefactor),integral_numerator_exponents=list(map(str,numerator_powers)),
        beta_bound=str(gamma_bound),beta_exponential_base=str(eta),
        beta_exponential_base_decimal=ball(eta).str(30),log_beta_base=ball(eta).log().str(30),
        derivative_bounds=list(map(str,derivative_bounds)),unscaled_small_root=(ball(scale)*real_interval).str(30),
        unscaled_other_root_modulus=large_mod.str(30),observation_determinant=str(observation),
        analytic_assumptions_remaining=[],
        interpretation='The written positive-integral argument proves recessiveness; exact initial values identify both dual limits.',
        quadrature_role='Independent numerical regression only; no quadrature is used as a proof premise.',
        quadrature_regressions=regressions,seconds=time.monotonic()-begun)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--matrices',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--quadrature',action='store_true')
    args=parser.parse_args()
    folder=Path(__file__).resolve().parent
    matrices=args.matrices or (folder/'notebook_outputs/exact_matrices.json')
    result=verify(matrices,args.quadrature)
    target=args.output or folder/'analytic_limit_result.json'
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
