# A proof of the Holevo–Utkin monotonicity hypothesis for $d=3$

> **Summary.** In their paper on a tight norm inequality for zero-sum vectors [HU], Holevo and Utkin work in $\mathbb R^3$ with a function $M_\alpha(\varphi)$ of an angle. They state, on numerical evidence only, that $-M_\alpha'(\varphi)/\sin 6\varphi \ge C(\alpha) > 0$ on $[0,\pi/6]$ for $\alpha>2$. We prove this, and we find the sharp constant $C(\alpha)$ in closed form. The proof rests on one identity: $-M_\alpha'(\varphi)/\sin 6\varphi$ is, up to the factor $\alpha/18$, a second-order **divided difference** of $t\mapsto t^{\alpha-1}$ at the three numbers $x_j(\varphi)^2$. Its positivity then follows from the Hermite–Genocchi formula. The same argument shows that $\sum_j g(x_j^2)$ is monotone on $[0,\pi/6]$ for every $g$ with $g'''\ge 0$. That gives a short, unified proof of the $d=3$ extremal problem for every $\alpha>0$.

---

## 1. Background

Let $L=\{x\in\mathbb R^d:\ x_1+\dots+x_d=0\}$. Holevo and Utkin [HU] conjectured sharp constants in $\|x\|_{2\alpha}\le M(d,\alpha)^{1/(2\alpha)}\|x\|_2$ for $\alpha\ge 1$ (and the reverse inequality for $0<\alpha<1$), with $x\in L$. They proved the case $d=3$. Zhang [Z] then proved the remaining cases $d\ge 4$.

For $d=3$, the unit vectors of $L$ are parametrized as

$$
x_j(\varphi)=\sqrt{\tfrac23}\,\cos\!\Big(\varphi+\tfrac{2\pi(j-1)}{3}\Big),\qquad j=1,2,3,
$$

and one studies

$$
M_\alpha(\varphi)=\sum_{j=1}^{3}|x_j(\varphi)|^{2\alpha}.
$$

$M_\alpha$ has period $\pi/3$ and is even about $\varphi=0$ and about $\varphi=\pi/6$. So it is enough to look at $\varphi\in[0,\pi/6]$. The point $\varphi=0$ is the vector $\big(\sqrt{2/3},-1/\sqrt6,-1/\sqrt6\big)$, and $\varphi=\pi/6$ is $\big(1/\sqrt2,-1/\sqrt2,0\big)$.

For $1<\alpha<2$ and for integer $\alpha$, [HU] get the answer from a Fourier expansion of $M_\alpha$ in $\cos 6k\varphi$. They note that this approach does not extend simply to non-integer $\alpha>2$, and they write (Section 2): *"Numerical study suggests that for $\alpha>2$"*

$$
-\frac{M_\alpha'(\varphi)}{\sin 6\varphi}\ \ge\ C(\alpha)>0,\qquad \varphi\in[0,\pi/6], \tag{H}
$$

which would make $M_\alpha$ decreasing on $[0,\pi/6]$. They then prove the $d=3$ inequality for $\alpha>2$ by a different argument, a monotonicity property of an auxiliary function $g_\alpha$, and leave (H) as a hypothesis. At $\varphi\in\{0,\pi/6\}$ the left side of (H) means its limit.

As far as we know (November 2026), (H) has not been proved. The paper [Z] covers $d\ge4$; we checked its abstract, which does not mention (H).

## 2. Results

Throughout, $y_j=y_j(\varphi):=x_j(\varphi)^2$. For a function $f$, $f[z_0,\dots,z_n]$ is the divided difference; coincident nodes are allowed, as usual [dB]. Let

$$
\Phi_\alpha(\varphi):=-\frac{M_\alpha'(\varphi)}{\sin 6\varphi}\quad(0<\varphi<\pi/6),
$$

and extend $\Phi_\alpha$ to $[0,\pi/6]$ by continuity.

**Theorem 1 (identity).** For every $\alpha>0$ and $\varphi\in(0,\pi/6)$,

$$
\Phi_\alpha(\varphi)=\frac{\alpha}{18}\,f_\alpha[y_1,y_2,y_3],\qquad f_\alpha(t)=t^{\alpha-1}.
$$

More generally, for $g\in C^1(0,\infty)$ and $S_g(\varphi):=\sum_j g\big(x_j(\varphi)^2\big)$, we have $-S_g'(\varphi)/\sin 6\varphi=\tfrac1{18}\,g'[y_1,y_2,y_3]$.

**Theorem 2 (hypothesis (H), with the sharp constant).** Let $\alpha>2$. Then $\Phi_\alpha$ is continuous and strictly positive on $[0,\pi/6]$, so (H) holds with

$$
C(\alpha)=\min_{[0,\pi/6]}\Phi_\alpha=\begin{cases}
\Phi_\alpha(0)=\dfrac{\alpha}{9}\Big[\,2\big(\tfrac23\big)^{\alpha-1}-\big(\alpha-\tfrac23\big)\,6^{\,2-\alpha}\Big], & 2<\alpha<3\ \text{ or }\ 4<\alpha<5,\\[3mm]
\Phi_\alpha(\pi/6)=\dfrac{\alpha(\alpha-2)}{18}\,2^{\,3-\alpha}, & 3<\alpha<4\ \text{ or }\ \alpha>5,
\end{cases}
$$

and this constant cannot be improved. More precisely, $\Phi_\alpha$ is strictly monotone on $[0,\pi/6]$. It is increasing when $(\alpha-3)(\alpha-4)(\alpha-5)<0$ and decreasing when $(\alpha-3)(\alpha-4)(\alpha-5)>0$. For $\alpha=3,4,5$ it is constant, equal to $\tfrac16$, $\tfrac29$, $\tfrac5{24}$ respectively. As $\alpha\to2^+$,

$$
C(\alpha)=\tfrac29\big(\tfrac83\ln 2-1\big)(\alpha-2)+O\big((\alpha-2)^2\big)\approx 0.18853\,(\alpha-2).
$$

**Theorem 3 (monotonicity for every exponent).** Let $g\in C[0,\tfrac23]\cap C^3(0,\tfrac23]$ with $g'''>0$ on $(0,\tfrac23)$. Then $\varphi\mapsto\sum_j g(x_j(\varphi)^2)$ is strictly decreasing on $[0,\pi/6]$. If $g'''<0$, it is strictly increasing.
Taking $g(t)=t^\alpha$, where $g'''(t)=\alpha(\alpha-1)(\alpha-2)t^{\alpha-3}$, gives the following.

- $M_\alpha$ is strictly decreasing on $[0,\pi/6]$ for $\alpha\in(0,1)\cup(2,\infty)$.
- $M_\alpha$ is strictly increasing on $[0,\pi/6]$ for $\alpha\in(1,2)$.
- $M_\alpha$ is constant for $\alpha\in\{1,2\}$.

So for every $\alpha>0$, the extreme values of $\|x\|_{2\alpha}^{2\alpha}$ on the unit sphere of $L\subset\mathbb R^3$ are

$$
M_\alpha(0)=3^{-\alpha}\big(2^{\alpha}+2^{1-\alpha}\big)\qquad\text{and}\qquad M_\alpha(\pi/6)=2^{1-\alpha}.
$$

For $\alpha\notin\{1,2\}$, they are attained only on the corresponding orbits (permutations and an overall sign change). This recovers the $d=3$ case of the Holevo–Utkin conjecture, in both directions, by one argument.

## 3. Proofs

### 3.1 The three squares are the roots of an explicit cubic

Using $\sum_j\cos(\theta+2\pi j/3)=0$ and $\sum_j\cos(2\theta+4\pi j/3)=0$, one checks that

$$
\sum_j y_j=1,\qquad \sum_j y_j^2=\sum_j x_j^4=\tfrac12 .
$$

Hence $e_1=1$ and $e_2=\tfrac12\big(e_1^2-\sum y_j^2\big)=\tfrac14$. Only $e:=e_3=y_1y_2y_3$ varies, and $y_1,y_2,y_3$ are the roots of

$$
P_e(t)=t^3-t^2+\tfrac14 t-e=h(t)-e,\qquad h(t):=t\,(t-\tfrac12)^2 .
$$

**Lemma 1.** $e(\varphi)=\dfrac{1+\cos 6\varphi}{108}$. In particular, $e$ decreases strictly from $\tfrac1{54}$ to $0$ on $[0,\pi/6]$, and $e'(\varphi)=-\tfrac1{18}\sin 6\varphi$.

*Proof.* We have $y_j=\tfrac13\big(1+\cos(2\varphi+4\pi(j-1)/3)\big)$. The three numbers $c_k=\cos(\psi+2\pi k/3)$ are the roots of $4c^3-3c-\cos3\psi$, because $\cos3\theta=4\cos^3\theta-3\cos\theta$. So $\prod_k(a+c_k)=a^3-\tfrac34a+\tfrac14\cos3\psi$. Take $a=1$ and $\psi=2\varphi$; then $27e=\tfrac14(1+\cos6\varphi)$. $\square$

The function $h$ has a local maximum $h(\tfrac16)=\tfrac1{54}$ and a local minimum $h(\tfrac12)=0$. Therefore, for $0<e<\tfrac1{54}$, $P_e$ has three **simple** roots

$$
0<y_{(1)}<\tfrac16<y_{(2)}<\tfrac12<y_{(3)}<\tfrac23.
$$

At $e=\tfrac1{54}$ (that is, $\varphi=0$) the roots are $\{\tfrac16,\tfrac16,\tfrac23\}$. At $e=0$ (that is, $\varphi=\pi/6$) they are $\{0,\tfrac12,\tfrac12\}$.

### 3.2 Facts about divided differences

We use the following standard facts; see e.g. [dB].

- **(D1) Lagrange form.** If $z_1,z_2,z_3$ are distinct and $Q(t)=\prod_i(t-z_i)$, then $\sum_j \dfrac{G(z_j)}{Q'(z_j)}=G[z_1,z_2,z_3]$.
- **(D2) Hermite–Genocchi.** If $G\in C^n$ on an interval containing $z_0,\dots,z_n$, then
  $G[z_0,\dots,z_n]=\displaystyle\int_{\Delta_n}G^{(n)}\Big(\sum_i s_iz_i\Big)\,ds$, where $\Delta_n$ is the standard simplex with Lebesgue measure of total mass $1/n!$. In particular, $G^{(n)}>0$ implies $G[z_0,\dots,z_n]>0$.
- **(D3) Derivatives in the nodes.** For distinct nodes and $G$ smooth near them, $\partial_{z_j}G[z_1,\dots,z_m]=G[z_1,\dots,z_m,z_j]$. Moreover, for $H(t):=G[z_1,\dots,z_m,t]$ we have $H[w_1,\dots,w_k]=G[z_1,\dots,z_m,w_1,\dots,w_k]$.
- **(D4) Continuity.** Divided differences depend continuously on the nodes, coincident nodes included, as long as $G$ is smooth enough at the coincident nodes.

### 3.3 Proof of Theorem 1

$S_g(\varphi)$ depends only on the multiset $\{y_j\}$, which is the root set of $P_{e(\varphi)}$. So $S_g(\varphi)=F(e(\varphi))$ with $F(e):=\sum_{P_e(y)=0}g(y)$.

For $0<e<\tfrac1{54}$ the roots are simple. By the implicit function theorem they are smooth in $e$, and differentiating $h(y_j(e))=e$ gives $y_j'(e)=1/h'(y_j)=1/P_e'(y_j)$. Hence, by (D1),

$$
F'(e)=\sum_j\frac{g'(y_j)}{P_e'(y_j)}=g'[y_1,y_2,y_3].
$$

For $\varphi\in(0,\pi/6)$ we have $e(\varphi)\in(0,\tfrac1{54})$. By Lemma 1,

$$
S_g'(\varphi)=F'(e)\,e'(\varphi)=-\frac{\sin6\varphi}{18}\,g'[y_1,y_2,y_3].
$$

With $g(t)=t^\alpha$ we get $g'=\alpha f_\alpha$. $\square$

### 3.4 Proof of Theorem 3

For $\varphi\in(0,\pi/6)$ all $y_j$ lie in $(0,\tfrac23)$ and are distinct. By Theorem 1 and (D2) with $n=2$,

$$
-\frac{S_g'(\varphi)}{\sin 6\varphi}=\frac1{18}\,g'[y_1,y_2,y_3]=\frac1{18}\int_{\Delta_2}g'''\Big(\sum s_iy_i\Big)ds .
$$

This has the sign of $g'''$, and $\sin6\varphi>0$ on $(0,\pi/6)$. So $S_g$ is strictly monotone on $(0,\pi/6)$. Being continuous, it is strictly monotone on $[0,\pi/6]$.

For $g(t)=t^\alpha$, the sign of $g'''$ on $(0,\infty)$ is the sign of $(\alpha-1)(\alpha-2)$ when $\alpha>0$. The values $M_\alpha(0)=(\tfrac23)^\alpha+2(\tfrac16)^\alpha$ and $M_\alpha(\pi/6)=2(\tfrac12)^\alpha$ give the stated extremes. They are global extremes on the circle by the symmetries of $M_\alpha$. $\square$

### 3.5 Proof of Theorem 2

Fix $\alpha>2$ and let $G(e):=f_\alpha[y_1,y_2,y_3]$, the divided difference at the root multiset of $P_e$. By Theorem 1, $\Phi_\alpha(\varphi)=\frac{\alpha}{18}G(e(\varphi))$ on $(0,\pi/6)$.

*Positivity on the open interval.* $f_\alpha''(t)=(\alpha-1)(\alpha-2)t^{\alpha-3}>0$ for $t>0$, so $G(e)>0$ for $0<e<\tfrac1{54}$ by (D2).

*The endpoints.*

- At $e=\tfrac1{54}$ the nodes $\{\tfrac16,\tfrac16,\tfrac23\}$ are positive and $f_\alpha$ is smooth there. By (D4), $G$ extends continuously, and
  $G(\tfrac1{54})=f_\alpha[\tfrac16,\tfrac16,\tfrac23]=2\big(f_\alpha[\tfrac16,\tfrac23]-f_\alpha'(\tfrac16)\big)$.
  Multiplying by $\alpha/18$ gives the formula for $\Phi_\alpha(0)$ in Theorem 2. It is positive by (D2).
- At $e=0$ the nodes are $\{0,\tfrac12,\tfrac12\}$. For $2<\alpha<3$, $f_\alpha''$ is not bounded at $0$, so we argue directly. Write the roots as $y_a(e)\to0$ and $y_b(e),y_c(e)\to\tfrac12$. Then
  $$
  G(e)=\frac{f_\alpha[y_b,y_c]-f_\alpha[y_a,y_b]}{y_c-y_a}\ \longrightarrow\ \frac{f_\alpha'(\tfrac12)-f_\alpha[0,\tfrac12]}{1/2}=(\alpha-2)\,2^{3-\alpha}>0,
  $$
  using that $f_\alpha$ is smooth near $\tfrac12$ and continuous on $[0,\infty)$. This gives $\Phi_\alpha(\pi/6)=\frac{\alpha(\alpha-2)}{18}2^{3-\alpha}$.

So $\Phi_\alpha$ is continuous and strictly positive on the compact interval $[0,\pi/6]$. Hence $C(\alpha):=\min\Phi_\alpha>0$, which proves (H).

*Where the minimum is.* For $0<e<\tfrac1{54}$, (D3) and (D1) give

$$
G'(e)=\sum_j \frac{f_\alpha[y_1,y_2,y_3,y_j]}{P_e'(y_j)}=H[y_1,y_2,y_3]=f_\alpha[y_1,y_1,y_2,y_2,y_3,y_3],
$$

where $H(t)=f_\alpha[y_1,y_2,y_3,t]$. By (D2) with $n=5$, this has the sign of

$$
f_\alpha^{(5)}(t)=(\alpha-1)(\alpha-2)(\alpha-3)(\alpha-4)(\alpha-5)\,t^{\alpha-6},
$$

which for $\alpha>2$ is the sign of $(\alpha-3)(\alpha-4)(\alpha-5)$. So $G$ is strictly monotone on $[0,\tfrac1{54}]$, or constant when $\alpha\in\{3,4,5\}$. Since $e$ decreases in $\varphi$, the minimum of $\Phi_\alpha$ is at $\varphi=\pi/6$ when the sign is $+$ and at $\varphi=0$ when it is $-$. This gives the case split in Theorem 2, and the constant is attained, so it is sharp.

*Constant cases.* For integer $m\ge 0$, $t^{m+2}[y_1,y_2,y_3]$ is the complete homogeneous symmetric polynomial $h_m(y)$. With $e_1=1$ and $e_2=\tfrac14$: $h_0=1$, $h_1=e_1=1$, and $h_2=\sum y_i^2+e_2=\tfrac34$. This gives $\Phi_3=\tfrac3{18}$, $\Phi_4=\tfrac4{18}$, $\Phi_5=\tfrac5{18}\cdot\tfrac34$.

*Behaviour as $\alpha\to2^+$.* Here the minimum is $\Phi_\alpha(0)$, which vanishes at $\alpha=2$. Differentiating the closed form at $\alpha=2$ gives
$\tfrac29\big[\tfrac43\ln\tfrac23-1+\tfrac43\ln6\big]=\tfrac29\big(\tfrac83\ln2-1\big)$. $\square$

## 4. Remarks

1. **Why Fourier coefficients are not the natural tool.** For $1<\alpha<2$ and integer $\alpha$, [HU] argue from the signs of the Fourier coefficients of $M_\alpha$. For non-integer $\alpha>2$ those coefficients do not have a fixed sign. The proof above avoids them. The relevant object is not the Fourier series but the cubic whose roots are $x_j^2$. Only its constant term moves, and it moves linearly in $\cos6\varphi$. Differentiating along this one-parameter family of cubics produces divided differences, which have a positive integral representation.
2. **The role of $\alpha=2$, and of $\alpha=3,4,5$.** The sign change of $M_\alpha'$ at $\alpha=2$ (and at $\alpha=1$), which [HU] call remarkable, is the sign change of $g'''$ for $g(t)=t^\alpha$. In the same way, the sharp constant $C(\alpha)$ switches endpoints exactly at the sign changes of $f_\alpha^{(5)}$, namely $\alpha=3,4,5$.
3. **Scope.** The argument is special to $d=3$: there the zero-sum unit sphere is a curve on which the power sums $p_1=1$ and $p_2=\tfrac12$ of the $y_j$ are fixed, so the cubic has a single moving coefficient. For $d\ge4$ see [Z].

## 5. Numerical check

[`verify.py`](verify.py) (needs `mpmath`) checks the statements above at 40-digit precision.

| Check | Result |
|---|---|
| Identity of Theorem 1, 9 values of $\alpha$ from 0.7 to 25.5, 12 values of $\varphi$ each | max relative error $2.4\times10^{-39}$ |
| $e_3=(1+\cos6\varphi)/108$ | max absolute error $5.7\times10^{-42}$ |
| Location and value of $\min\Phi_\alpha$ (400-point grid plus endpoints) | matches the case split of Theorem 2 for all 11 tested $\alpha$, including $\alpha=4.5$ |
| $C(2+\varepsilon)/\varepsilon$ for $\varepsilon=10^{-7}$ | $0.1885316667$ vs. predicted $0.1885316626$ |

Selected values of the sharp constant:

| $\alpha$ | 2.5 | 3 | 3.5 | 4 | 4.5 | 5 | 5.5 | 8 | 15 |
|---|---|---|---|---|---|---|---|---|---|
| $C(\alpha)$ | 0.094502 | 1/6 | 0.206239 | 2/9 | 0.220189 | 5/24 | 0.189053 | 1/12 | 0.0026449 |
| attained at $\varphi=$ | 0 | (const) | $\pi/6$ | (const) | 0 | (const) | $\pi/6$ | $\pi/6$ | $\pi/6$ |

## References

- **[HU]** A. S. Holevo, A. V. Utkin, *A conjecture on a tight norm inequality in the finite-dimensional $l_p$*, arXiv:2603.24017 (2026).
- **[Z]** H. Zhang, *Proof of the Holevo–Utkin conjecture on sharp $\ell_p$ norms for zero-sum vectors*, arXiv:2605.05243 (2026).
- **[dB]** C. de Boor, *Divided differences*, Surveys in Approximation Theory **1** (2005), 46–69.

---

