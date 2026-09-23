"""angle A2 numerical checks.
 (1) threshold constants for beta=0.01 (Regions I/II/III)
 (2) lens-corner proximity: p on arc1, q on arc2, |pq|=1 => arc-dist to common corner <= 1/sin(phi0/2)
 (3) LP values of the final theorem
"""
import numpy as np
from math import *
b=0.01; r3=sqrt(3)/2
print("== (1) constants, beta=",b)
tI=r3-2*b
print("Region I  S\\D same-side arc:",degrees(asin(tI)+asin(b)),"< 60;  D same-side arc:",degrees(asin(tI+b)),"< 60")
tII=r3+3*b; s=sqrt(1-tII**2)
print("Region II s=",s," proximity 2s+4.5b=",2*s+4.5*b,"<1 ; single-rung 2s+3b=",2*s+3*b,"<1")
th_lo=degrees(acos(r3+3*b)); th_hi=degrees(acos(r3-2*b))
m=min(2*th_lo,90-th_hi); print("Region III theta0 in",(th_lo,th_hi)," min corner angle",m,"> 360/7=",360/7)
print("mixed-T turning lower bound t-asin(b) with t>=tII:",tII-asin(b),"rad")
print("\n== (2) lens corner check")
rng=np.random.default_rng(1)
worst=0
for trial in range(4000):
    D2=rng.uniform(200,5000); lam=rng.uniform(0.0,1.94); d=lam*D2
    phi0=acos(d/(2*D2))
    # p on arc1 (centre (-d/2,0)), q on arc2 (centre (d/2,0)); choose phi, solve psi so |pq|=1
    phi=rng.uniform(-phi0,phi0)
    p=np.array([-d/2+D2*cos(phi),D2*sin(phi)])
    psis=np.linspace(-phi0,phi0,20001)
    Q=np.stack([d/2-D2*np.cos(psis),D2*np.sin(psis)],1)
    dist=np.linalg.norm(Q-p,axis=1)-1
    idx=np.where(np.sign(dist[:-1])!=np.sign(dist[1:]))[0]
    for i in idx:
        psi=psis[i]
        # arc distances to corners (0,+h) at angle +phi0, (0,-h) at -phi0
        dp=[D2*(phi0-phi),D2*(phi+phi0)]; dq=[D2*(phi0-psi),D2*(psi+phi0)]
        cd=min(max(dp[0],dq[0]),max(dp[1],dq[1]))
        bound=1/sin(phi0/2)
        worst=max(worst,cd/bound)
print("max (arc-dist to common corner)/(1/sin(phi0/2)) =",worst,"(must be <=1)")
print("\n== (3) final LPs")
k=lambda kk: 9/(7.5-kk)
print("Region I  k=1   :",k(1),"=18/13",18/13)
print("Region II k=5/4 :",k(1.25),"; k=4/3:",k(4/3),"=54/37",54/37)
# Region III: max T s.t. T<=1.5s-0.5p, T<=s+2p+6r, s+r=1
from scipy.optimize import linprog
res=linprog([0,0,0,-1],A_ub=[[-1.5,0.5,0,1],[-1,-2,-6,1],[-1,1,0,0]],b_ub=[0,0,0],A_eq=[[1,0,1,0]],b_eq=[1],bounds=[(0,None)]*4)
print("Region III LP (s,p,r,T):",res.x.round(4),"T=",-res.fun,"=7/5")
