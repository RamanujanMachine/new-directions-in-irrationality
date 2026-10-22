#!/usr/bin/env python3
"""Conditional positive-delta arithmetic certificate for the specified MG55 ray.

Requires Python 3.10+ and python-flint. No numerical target values or observed
prime valuations are inputs. Default run recomputes 1,158 exact dual chambers
and the forward bounds; about six minutes on the development machine.

The mathematical lemmas justifying this finite calculation are in PROOF.txt.
Only the limit and error rate are analytic assumptions. Interrupted runs resume
from a checkpoint bound to the SHA256 of this file; --fresh discards that cache.
"""
import argparse,hashlib,json,math,time
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from flint import fmpq as Q, fmpq_mat as Mat, arb, ctx
J=5


GAMMA=[[12, '2/3', -1], [8, '1', 1], [5, '1/3', -1], [8, '1/3', 1], [6, '1', -1], [5, '1', 1], [4, '1/6', 1], [9, '1/2', -1], [6, '2/3', 1], [5, '2/3', 1], [4, '1/3', -1]]

GAMMA_CONSTANT=52708129816230144

NONVANISHING={'scope': 'Exact nonzero evaluation of the rational three-consecutive-column determinant. Therefore it vanishes at only finitely many n; together with the fixed readout determinant this supplies infinitely many nonzero errors for every nonzero fixed mixture.', 'Q0': [['33134470494113265094822158549/101544012423478625', '1149023549983998483051406866/1562215575745825', '-2260235960860916506330466676/600852144517625'], ['3381503995827857395882195659/10977731072808500', '190120812262917053411793303/84444085175450', '255280621821754797650639421/16239247149125'], ['40918696764765654021173289/663144570928840', '6435216689897315510132013/5101112084068', '12929524885498886211929391/980983093090']], 'Q1': [['2333587742808374761877390652393461240832/142477313395059410047039375', '138193876084407075096438790730174379264/884952257112170248739375', '8607877940978977256442996241789944101376/6194665799785191741175625'], ['14177626252700960086117268790801413284128/101871279077467478183633153125', '2006365731574024205959048565259297358656/632740863835201727848653125', '236319967208750935311864334743377942680704/4429186046846412094940571875'], ['-5425557236209125232650198139313520476208/20374255815493495636726630625', '-290290269235070602777106726268103686816/126548172767040345569730625', '-15122547257964799477651558650507637767744/885837209369282418988114375']], 'determinant_at_n0': '-2091300253601094307522404926786910050752593888802048297/255217484616350899365532475817984000', 'native_matrix_sha256': 'a9b1b0fa4630fd74092c1d42f6c8da70ef9272a11b4b116021a2465e814026c9', 'readout_determinant': '-117573120'}

FORWARD_INITIAL={'F0': [['41/3', '35/3', '35/3', '35/3'], ['1807/16', '1339/16', '8495/144', '37819/1296'], ['2353/54', '818/27', '3649/216', '311/432']], 'F0K0': [['-188/3', '1153/9', '-1225/18'], ['-6355/12', '155897/144', '-55211/96'], ['-5567/27', '136555/324', '-72539/324']], 'nine_residuals_zero': True}

def walls(e):
    t=F(2,3) if e==1 else F(1,3)
    lines=[(-10,F(0)),(0,F(0)),(-8,F(0)),(1,F(0)),
           (2,F(0)),(12,F(0)),(0,t),(6,t),(2,F(1,2)),(5,F(1,2))]
    cuts={F(0),F(1)}
    for u,a in lines:
        for v,b in lines:
            if u==v:continue
            for k in range(-25,26):
                x=(b-a+k)/(u-v)
                if 0<x<1:cuts.add(x)
    return sorted(cuts)

def projected_bound(gens,which,A=None,B=None):
    first=None
    for weight,v in sorted(gens,key=lambda z:z[0]):
        if which=='TH':u=(v[1],v[2])
        elif which=='CT':u=(v[0],v[1])
        elif which=='CH':u=(v[0],v[2])
        else:u=(v[0],(A+B)*v[2]+3*B*v[1])
        if not any(u):continue
        if first is None:first=(weight,u);continue
        w,a=first
        if a[0]*u[1]-a[1]*u[0]:return w+weight
    return 10**6

def intervals(e):
    theta=F(1,3) if e==1 else F(2,3)
    return [(-10,0,F(-1),F(-1),F(0)),(-8,1,F(-1),F(-1),F(0)),
            (2,12,F(0),F(1),F(0)),(0,6,F(1,3),F(4,3),theta),
            (2,5,F(1,2),F(3,2),F(1,2))]

def signatures(a,b,e,L=0):
    x=a+(b-a)*F(503,1009)+L;data=intervals(e)
    cuts={F(0),F(1)};boundaries=[]
    for u,v,off0,off1,theta in data:
        for slope in (u,v):
            for h in range(math.floor(slope*x-theta)-1,math.ceil(slope*x-theta)+1):
                y=slope*x-h-theta
                if 0<=y<=1:
                    cuts.add(y);boundaries.append((y,off0%1))
    cuts=sorted(cuts);packets=set()
    def add(y,z=None):
        lists=[]
        for u,v,a0,b0,theta in data:
            lo=u*x-y;hi=v*x-y
            q0=math.ceil(lo-theta);q1=math.floor(hi-theta)
            if q0+theta==lo and not(z is not None and z>=a0):q0+=1
            if q1+theta==hi and not(z is not None and z<=b0):q1-=1
            lists.append(tuple(F(q)+theta for q in range(q0,q1+1)))
        ns=tuple(sorted(lists[0]+lists[1]));ds=tuple((t,c) for roots,c in zip(lists[2:],(0,1,2)) for t in roots)
        packets.add((ns,ds,int(y==0 and z==0)))
    for u,v in zip(cuts,cuts[1:]):add((u+v)/2)
    # r=0,1,p-1 additionally matter for the terminal polynomial s.
    boundaries.extend([(F(0),F(0)),(F(1),F(0))])
    for y,off in boundaries:
        for z in [F(i)+off for i in range(-2,3)]:
            if(y==0 and z<0)or(y==1 and z>=0):continue
            add(y,z)
    return packets

@lru_cache(None)
def harmonic(t):
    r=t%1;j=math.floor(t)
    if r==0:return sum((Q(1,i*i) for i in range(1,j+1)),Q(0))
    return sum((Q(r.denominator**2,(r.denominator*i+r.numerator)**2) for i in range(j+1)),Q(0))

@lru_cache(None)
def vectors(ns,ds,jmin):
    if not ds:return ()
    h=len(ns)-len(ds);rs=[]
    for t,c in ds:
        r=Q(1)
        for u in ns:r*=Q((t-u).numerator,(t-u).denominator)
        for u,_ in ds:
            if u!=t:r/=Q((t-u).numerator,(t-u).denominator)
        rs.append((Q(t.numerator,t.denominator),c,r,harmonic(t)))
    out=[]
    for j in range(jmin,J+1):
        v=[Q(0)]*4
        for t,c,r,H in rs:
            z=r*t**j;v[0]-=z*H;v[3]+=z
            if c:v[c]+=z
        if any(v):out.append((h+1+j,tuple(v)))
    regular=min(h+1+max(jmin,-h-1),h+2+jmin)
    out.append((regular+2,(Q(1),Q(0),Q(0),Q(0))))
    for k in range(4):out.append((h+J+2,tuple(Q(int(i==k)) for i in range(4))))
    return tuple(out)

def cell(a,b,e,L=0):
    packets=signatures(a,b,e,L);gens=set()
    for ns,ds,jmin in packets:gens.update(vectors(ns,ds,jmin))
    tw,pivot=min(((w,v) for w,v in gens if v[3]),key=lambda z:(z[0],abs(z[1][3])))
    assert tw==0 and pivot[3] in (1,-1),(a,b,e,L,tw,pivot)
    gens={(w,tuple(v[k]-v[3]*pivot[k]/pivot[3] for k in range(3))) for w,v in gens}
    bounds=[projected_bound(gens,s)-(0 if s=='TH' else 2) for s in ('TH','CT','CH')]
    return dict(mod6=e,lift=L,lo=str(a),hi=str(b),bounds=bounds,common_bound=min(bounds),packet_count=len(packets))

def determinant_profile(x,e):
    val=0
    for A,b,m in GAMMA:
        b=F(b);d=b.denominator
        residue=(b.numerator*pow(e,-1,d))%d if d>1 else 0
        theta=F(residue,d) if residue else F(1)
        val+=m*math.floor(A*x+1-theta)
    return val

def highcounts(x,y,e,z=None):
    tt=F(2,3) if e==1 else F(1,3)
    data=[(-12,-2,F(0),F(-1),F(-1)),(-6,0,tt,F(-4,3),F(-4,3)),(-5,-2,F(1,2),F(-3,2),F(-3,2)),(0,10,F(0),F(0),F(1)),(-1,8,F(0),F(0),F(1))]
    nums=[];dens=[]
    for i,(u,v,theta,a0,b0) in enumerate(data):
        lo=math.ceil(u*x-y-theta);hi=math.floor(v*x-y-theta)
        if lo==u*x-y-theta and not(z is not None and z>=a0):lo+=1
        if hi==v*x-y-theta and not(z is not None and z<=b0):hi-=1
        roots=[F(j)+theta for j in range(lo,hi+1)]
        (nums if i<3 else dens).extend(roots)
    return nums,dens

def baseline(a,b,e,L=0):
    x=a+(b-a)*F(503,1009)+L;cuts={F(0),F(1)};boundaries=[]
    tt=F(2,3) if e==1 else F(1,3)
    for u,theta in [(-12,0),(-2,0),(-6,tt),(0,tt),(-5,F(1,2)),(-2,F(1,2)),(0,0),(10,0),(-1,0),(8,0)]:
        for h in range(math.floor(u*x-theta)-1,math.ceil(u*x-theta)+1):
            y=u*x-h-theta
            if 0<=y<=1:
                cuts.add(y)
                off=(F(theta)*e)%1
                boundaries.append((y,off))
    cuts=sorted(cuts);hmin=0
    for u,v in zip(cuts,cuts[1:]):
        ns,ds=highcounts(x,(u+v)/2,e)
        if ds:hmin=min(hmin,len(ns)-len(ds))
    bulk=hmin
    for y,off in boundaries:
        for z in [F(i)+off for i in range(-3,3)]:
            if(y==0 and z<0)or(y==1 and z>=0):continue
            ns,ds=highcounts(x,y,e,z)
            if ds:hmin=min(hmin,len(ns)-len(ds))
    return dict(forward_bulk_bound=bulk,forward_bound=hmin,determinant_profile=determinant_profile(x,e),combined_bulk_bound=bulk+determinant_profile(x,e),combined_bound=hmin+determinant_profile(x,e))


def ball(q):
    q=F(q);return arb(q.numerator)/q.denominator

def auxiliary_checks():
    assert sum(A*m for A,b,m in GAMMA)==0
    assert 10+6+3==10+9
    for e in (1,5):
        W=set(walls(e))
        for A,b,m in GAMMA:
            b=F(b);d=b.denominator
            r=(b.numerator*pow(e,-1,d))%d if d>1 else 0
            theta=F(r,d) if r else F(1)
            for j in range(A+2):
                x=(j-1+theta)/A
                assert not(0<x<1) or x in W
    # Exceptional primes. Legendre errors and rational coboundaries are O(log n).
    slopes=[]
    for p,forward,expected in [(2,-6,12),(3,-9,18)]:
        c=GAMMA_CONSTANT;v=0
        while c%p==0:c//=p;v+=1
        for A,b,m in GAMMA:
            den=F(b).denominator
            if den%p:
                vp=F(1,p-1)
            else:
                vp=0
                while den%p==0:den//=p;vp-=1
            v+=m*A*vp
        assert v+forward==expected
        slopes.append([p,forward,str(v),str(expected)])
    Q0=Mat([[Q(z) for z in r] for r in NONVANISHING['Q0']])
    Q1=Mat([[Q(z) for z in r] for r in NONVANISHING['Q1']])
    e0=Mat([[1],[0],[0]]);T0=Q0.inv().transpose();T1=Q1.inv().transpose()
    cols=[e0,T0*e0,T0*T1*e0]
    det=Mat([[c[j,0] for c in cols] for j in range(3)]).det()
    assert det==Q(NONVANISHING['determinant_at_n0']) and det
    D=[243648,-498096,264600];C=[190344,-389162,206743];Z=[400824,-819330,435234]
    assert Mat([D,C,Z]).det()==-117573120
    K0=Mat([[Q(11,3),Q(23,3),Q(-35,6)],
            [Q(-23,2),Q(4),Q(1)], [Q(-7,6),Q(-2),Q(0)], [Q(3),Q(0),Q(0)]])
    F0=Mat([[Q(z) for z in r] for r in FORWARD_INITIAL['F0']])
    want=Mat([[Q(x,-3888) for x in D],
              [(Q(9,2)*C[i]+3*Z[i])/(-3888) for i in range(3)],
              [Q(2*x,-3888) for x in Z]])
    assert F0*K0==want
    return dict(exceptional_prime_slopes=slopes,nonvanishing_determinant=str(det),initial_readout_residuals=9)

def rates(beta):
    # Unique positive saddle of the terminating denominator sum.
    P=lambda x:-180*x**3-720*x**2+6480*x+28800
    lo,hi=F(6),F(7)
    assert P(lo)>0>P(hi)
    for _ in range(220):
        mid=(lo+hi)/2
        if P(mid)>0:lo=mid
        else:hi=mid
    x=ball(lo).union(ball(hi));f=lambda z:z*z.log()
    alpha_f=f(x+12)+f(x+6)+f(x+5)-2*f(x+2)-2*f(x)-f(10-x)-f(x+1)-f(8-x)
    d=arb(GAMMA_CONSTANT).log()+sum((m*A*arb(A).log() for A,b,m in GAMMA),arb(0))
    alpha=alpha_f+d
    coeff=[F(1),-F(162060225797,305977695940),F(40100849267287098349209,374489401651004369934400),-F(25,7161587766945221818712445059146)]
    r=F('3.25999287587431764165969620794e-29');rl,rh=r-F('1e-58'),r+F('1e-58')
    poly=lambda z:sum(c*z**(3-i) for i,c in enumerate(coeff))
    assert poly(rl)<0<poly(rh)
    assert 3*rl**2+2*coeff[1]*rh+coeff[2]>0
    b,c,d0=coeff[1:]
    assert b*b*c*c-4*c*c*c-4*b*b*b*d0-27*d0*d0+18*b*c*d0<0
    E=(ball(-d0)/ball(rh)).log()/2-ball(rh).log()
    H=alpha-beta;delta=E/H-1
    assert beta>ball(F('-1.3335'))
    assert alpha<ball(F('63.13604'))
    assert E>ball(F('64.47615'))
    assert H<ball(F('64.46954'))
    assert delta>ball(F('0.0001'))
    return dict(content_rate_lower=str(beta),forward_height_rate=str(alpha_f),determinant_rate=str(d),raw_cofactor_rate=str(alpha),accepted_error_rate_lower=str(E),reduced_height_rate_upper=str(H),delta_lower=str(delta),advertised_delta='0.00010',saddle_interval=[str(lo),str(hi)])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh',action='store_true')
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent/'positive_certificate_run')
    args=parser.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    ctx.prec=256;aux=auxiliary_checks();T=20
    sha=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    checkpoint=args.output_dir/'checkpoint.json'
    saved=json.loads(checkpoint.read_text()) if checkpoint.exists() and not args.fresh else {}
    cache=saved.get('cells',{}) if saved.get('source_sha256')==sha else {}
    started=time.monotonic()
    def get(a,b,e,L):
        key=f'{e}:{L}:{a}:{b}'
        if key not in cache:
            cache[key]=cell(a,b,e,L)
            checkpoint.write_text(json.dumps(dict(source_sha256=sha,cells=cache),indent=2)+'\n')
        return cache[key]
    head=[];tail=[];finite=F(0)
    for e in (1,5):
        W=walls(e)
        for a,b in zip(W,W[1:]):
            for L in (0,1):
                dual=get(a,b,e,L)['common_bound'];forward=baseline(a,b,e,L)['combined_bound']
                v=max(dual,forward)
                rec=dict(mod6=e,lo=str(a),hi=str(b),lift=L,dual=dual,forward=forward,bound=v)
                if L==0:
                    head.append(rec)
                    if not a:assert v==0
                    else:finite+=v*(1/a-1/b)/2
                else:tail.append(rec)
        print(f'Base chambers for p mod 6 = {e} checked.',flush=True)
    for L in range(1,T):
        for r in tail:
            a,b=F(r['lo']),F(r['hi']);v=r['forward']
            if L==1:v=r['bound']
            elif r['dual']>r['forward']:
                v=max(v,get(a,b,r['mod6'],L)['common_bound'])
            finite+=v*(1/(L+a)-1/(L+b))/2
        print(f'Lift {L}/{T-1}: {len(cache)} exact chambers; {time.monotonic()-started:.1f}s',flush=True)
    beta=12*arb(2).log()+18*arb(3).log()+ball(finite)
    tail_integral=arb(0)
    for r in tail:
        a,b=F(r['lo']),F(r['hi'])
        tail_integral+=r['forward']*(ball(T+b).digamma()-ball(T+a).digamma())/2
    beta+=tail_integral
    result=dict(certificate_checks_passed=True,analytic_assumptions=['The endpoint/CMF readouts converge to C and zeta(2).','Their errors have exponential upper rate E as stated in PROOF.txt.'],
                source_sha256=sha,tail_start=T,exact_dual_chambers=len(cache),
                rational_finite_prime_density=str(finite),periodic_forward_tail_density=str(tail_integral),
                auxiliary_checks=aux,**rates(beta),seconds=time.monotonic()-started)
    (args.output_dir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.output_dir/'base_chambers.json').write_text(json.dumps(dict(head=head,tail=tail),indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
