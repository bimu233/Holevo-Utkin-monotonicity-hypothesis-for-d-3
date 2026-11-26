"""
Numerical companion to README.md (Holevo-Utkin, d = 3 monotonicity hypothesis).

Checks, in high precision (mpmath):
  1. the identity  -M'(phi)/sin(6 phi) = (alpha/18) * f[y1,y2,y3],  f(t) = t^(alpha-1),  y_j = x_j(phi)^2;
  2. e3 = y1*y2*y3 = (1 + cos 6phi)/108;
  3. the closed forms of Phi(0) and Phi(pi/6), and that the minimum of Phi over [0, pi/6]
     sits at the endpoint predicted by the sign of (alpha-3)(alpha-4)(alpha-5);
  4. the constants 1/6, 2/9, 5/24 at alpha = 3, 4, 5;
  5. the small-(alpha-2) slope (2/9)((8/3) ln 2 - 1).

Usage:  python verify.py
Requires: mpmath
"""
import mpmath as mp

mp.mp.dps = 40
TWO_THIRDS = mp.mpf(2) / 3


def x(phi, j):
    return mp.sqrt(TWO_THIRDS) * mp.cos(phi + 2 * mp.pi * (j - 1) / 3)


def M(phi, a):
    return sum(abs(x(phi, j)) ** (2 * a) for j in (1, 2, 3))


def Phi_direct(phi, a):
    """-M'(phi)/sin(6 phi) by numerical differentiation (phi in the open interval)."""
    return -mp.diff(lambda t: M(t, a), phi) / mp.sin(6 * phi)


def divdiff3(f, ys):
    """Second divided difference at three distinct nodes."""
    return sum(f(ys[j]) / mp.fprod([ys[j] - ys[i] for i in range(3) if i != j]) for j in range(3))


def Phi_formula(phi, a):
    ys = [x(phi, j) ** 2 for j in (1, 2, 3)]
    return a / 18 * divdiff3(lambda t: t ** (a - 1), ys)


def Phi_at_0(a):
    return a / 9 * (2 * TWO_THIRDS ** (a - 1) - (a - TWO_THIRDS) * mp.mpf(6) ** (2 - a))


def Phi_at_pi6(a):
    return a * (a - 2) * mp.mpf(2) ** (3 - a) / 18


def main():
    print("1-2. identity and e3 formula on a 12-point grid of phi in (0, pi/6)")
    worst_id = worst_e3 = mp.mpf(0)
    for a in ["2.1", "2.5", "3", "3.7", "6.3", "10", "25.5", "1.5", "0.7"]:
        a = mp.mpf(a)
        for k in range(1, 13):
            phi = mp.pi / 6 * k / 13
            L, R = Phi_direct(phi, a), Phi_formula(phi, a)
            worst_id = max(worst_id, abs(L - R) / abs(R))
            ys = [x(phi, j) ** 2 for j in (1, 2, 3)]
            worst_e3 = max(worst_e3, abs(ys[0] * ys[1] * ys[2] - (1 + mp.cos(6 * phi)) / 108))
    print(f"   max relative error of identity: {mp.nstr(worst_id, 3)}")
    print(f"   max abs error of e3 formula:    {mp.nstr(worst_e3, 3)}\n")

    print("3-4. location and value of min Phi on [0, pi/6] (400-point grid + closed-form endpoints)")
    print("   alpha | sign(a-3)(a-4)(a-5) | predicted argmin | grid min      | Phi(0)        | Phi(pi/6)")
    for a in ["2.01", "2.5", "2.9", "3", "3.5", "4", "4.5", "5", "5.5", "8", "15"]:
        a = mp.mpf(a)
        s = (a - 3) * (a - 4) * (a - 5)
        pred = "constant" if s == 0 else ("phi=pi/6" if s > 0 else "phi=0")
        grid = [Phi_formula(mp.pi / 6 * k / 400, a) for k in range(1, 400)]
        g = min(grid + [Phi_at_0(a), Phi_at_pi6(a)])
        print(f"   {mp.nstr(a, 4):>5} | {'+' if s > 0 else ('-' if s < 0 else '0'):^19} | {pred:^16} | "
              f"{mp.nstr(g, 10):<13} | {mp.nstr(Phi_at_0(a), 10):<13} | {mp.nstr(Phi_at_pi6(a), 10)}")
    print()

    print("5. slope of C(alpha) as alpha -> 2+")
    for eps in ["1e-3", "1e-5", "1e-7"]:
        eps = mp.mpf(eps)
        print(f"   C(2+{mp.nstr(eps, 1)})/eps = {mp.nstr(Phi_at_0(2 + eps) / eps, 12)}")
    print(f"   predicted (2/9)((8/3)ln2 - 1) = {mp.nstr(mp.mpf(2) / 9 * (mp.mpf(8) / 3 * mp.log(2) - 1), 12)}")


if __name__ == "__main__":
    main()
