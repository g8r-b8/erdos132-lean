"""R6 referee: float stress test of the receiver bounds (sanity only).
Random concave piecewise-linear f on [-3,3] with f(0)=0 (max), f<=0, |f'|<=eps (flat/cornered boundary); y=(0,-h).
Fan receiver a = y + u(psi_a), |psi_a-180| <= 33: directions on C(a,1) at or above the graph (possible S-neighbours)
must lie within 37.1 deg of vertical => with y's direction no 3 points pairwise >= 60 deg fit => m_a <= 1.
Cap receiver b = y + u(180 +- 1.15), h >= 0.4825: no point of C(b,1) reaches the graph => m_b = 0."""
import numpy as np, math
rng = np.random.default_rng(7); eps = math.tan(0.02)
th = np.radians(np.arange(-180, 180, 0.05)); U = np.stack([np.sin(th), np.cos(th)], 1)
worst_fan, worst_cap = 0.0, -9.0
for it in range(20000):
    kr, kl = rng.integers(0, 4, 2)
    xr = np.concatenate([[0], np.sort(rng.uniform(0, 3, kr)), [3.0]])
    sr = -np.sort(rng.uniform(0, eps, kr + 1))                     # slopes 0 >= s1 >= s2 ... (concave)
    vr = np.concatenate([[0], np.cumsum(sr * np.diff(xr))])
    xl = np.concatenate([[0], np.sort(rng.uniform(0, 3, kl)), [3.0]])
    sl = -np.sort(rng.uniform(0, eps, kl + 1))
    vl = np.concatenate([[0], np.cumsum(sl * np.diff(xl))])
    X = np.concatenate([-xl[::-1], xr[1:]]); V = np.concatenate([vl[::-1], vr[1:]])
    f = lambda x: np.interp(x, X, V)
    h = rng.uniform(0, 1); y = np.array([0.0, -h])
    psi = math.radians(180 + rng.uniform(-33, 33)); a = y + np.array([math.sin(psi), math.cos(psi)])
    Q = a + U; above = Q[:, 1] >= f(Q[:, 0])
    if above.any(): worst_fan = max(worst_fan, np.degrees(np.abs(th[above])).max())
    hb = rng.uniform(0.4825, 1); pb = math.radians(180 + rng.uniform(-1.15, 1.15))
    b = np.array([0.0, -hb]) + np.array([math.sin(pb), math.cos(pb)]); Qb = b + U
    worst_cap = max(worst_cap, (Qb[:, 1] - f(Qb[:, 0])).max())
print(f"fan receiver: max deviation from vertical of an on/above-graph direction = {worst_fan:.2f} deg (bound 37.1)")
print(f"cap receiver: max (q_z - f(q_x)) over C(b,1) = {worst_cap:.4f} (must be < 0)")
assert worst_fan < 37.1 and worst_cap < 0
