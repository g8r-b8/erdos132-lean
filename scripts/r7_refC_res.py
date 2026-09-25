"""REF_C (R7): where do the arc-gap resonances of the l-analysis sit in terms of G = 2R sin(theta0 - pi/6)?

(*) opposite-sign unbroken arc gap: j alpha2 = k alpha1 -+ 2 phi, sin(phi) = s/Delta (A3), l = j - k in {-1, 0, 1}.
  l = +1 : 2 phi = alpha2 + k (alpha2 - alpha1)      (d > 0)
  l = -1 : 2 phi = alpha1 - (k-1)(alpha2 - alpha1)   (d <= 0)
For each k <= 3 (Lemma AI: |Z| <= 4) solve for tau at given R (60 digits) and print G, R d.
Question relevant to Theorem W case 4: can arc gaps (l = +1, k >= 1) coexist with singleton gaps (G = 1 or G >= 2)?
"""
from mpmath import mp, mpf, sqrt, asin, acos, sin, pi, findroot
mp.dps = 60

def quantities(R, tau):
    t = -R + sqrt(R * R + 1 + 2 * R * tau)
    D = R + t
    s = sqrt(1 - tau * tau)
    a2 = 2 * asin(1 / (2 * R)); a1 = 2 * asin(1 / (2 * D))
    phi = asin(s / D)
    G = 2 * R * sin(acos(tau) - pi / 6)
    return t, D, s, a1, a2, phi, G

for R in [mpf(10) ** 4, mpf(10) ** 6, mpf(10) ** 9]:
    print('R = %.0e' % float(R))
    for l, ks in [(+1, [0, 1, 2, 3]), (-1, [1, 2, 3])]:
        for k in ks:
            def f(tau):
                t, D, s, a1, a2, phi, G = quantities(R, tau)
                if l == 1:
                    return 2 * phi - (a2 + k * (a2 - a1))
                return 2 * phi - (a1 - (k - 1) * (a2 - a1))
            tau0 = findroot(f, sqrt(3) / 2)
            t, D, s, a1, a2, phi, G = quantities(R, tau0)
            print('   l=%+d k=%d j=%d : G = %s   R d = %s   tau - sqrt3/2 = %s' % (
                l, k, k + l, mp.nstr(G, 12), mp.nstr(R * (2 * s - 1), 12), mp.nstr(tau0 - sqrt(3) / 2, 6)))
print('Consequence: l=+1,k resonance has G = k+1 - O(1/R) (below k+1) -- see output; k=1 gives G < 2 ?')
