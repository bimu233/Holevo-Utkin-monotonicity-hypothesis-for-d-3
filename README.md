# The Holevo–Utkin monotonicity hypothesis for d = 3

📄 **Full proof: [paper/holevo_utkin_d3.pdf](paper/holevo_utkin_d3.pdf)** (LaTeX source alongside).

## The problem

Holevo and Utkin ([arXiv:2603.24017](https://arxiv.org/abs/2603.24017)) parametrize the unit zero-sum vectors of $`\mathbb{R}^3`$ by

```math
x_j(\varphi)=\sqrt{\tfrac{2}{3}}\,\cos\Big(\varphi+\tfrac{2\pi(j-1)}{3}\Big),\qquad j=1,2,3,
```

and study $`M_\alpha(\varphi)=\sum_{j} |x_j(\varphi)|^{2\alpha}`$. On numerical evidence only, they state that for every $`\alpha>2`$

```math
\text{(H)}\qquad -\frac{M_\alpha'(\varphi)}{\sin 6\varphi}\ \ge\ C(\alpha)>0\qquad\text{on }[0,\pi/6].
```

## Results

- **(H) is true for every $`\alpha>2`$, with the sharp constant in closed form.** The minimum of $`-M_\alpha'/\sin 6\varphi`$ is attained at $`\varphi=0`$ when $`(\alpha-3)(\alpha-4)(\alpha-5)<0`$, and at $`\varphi=\pi/6`$ when this product is positive. In the latter case $`C(\alpha)=\alpha(\alpha-2)\,2^{3-\alpha}/18`$. For $`\alpha=3,4,5`$ the quotient is constant, equal to $`\tfrac{1}{6},\tfrac{2}{9},\tfrac{5}{24}`$.
- **Monotonicity for every exponent.** $`M_\alpha`$ is strictly decreasing on $`[0,\pi/6]`$ for $`\alpha\in(0,1)\cup(2,\infty)`$ and strictly increasing for $`\alpha\in(1,2)`$. This gives a one-argument proof of the $`d=3`$ case of the Holevo–Utkin inequality for all $`\alpha>0`$.

## Key idea

The three numbers $`y_j=x_j^2`$ satisfy $`y_1+y_2+y_3=1`$ and $`y_1y_2+y_1y_3+y_2y_3=\tfrac{1}{4}`$ for every $`\varphi`$. So they are the roots of the cubic

```math
t\,\big(t-\tfrac{1}{2}\big)^2=e,\qquad e=y_1y_2y_3=\frac{1+\cos 6\varphi}{108},
```

and only $`e`$ moves with $`\varphi`$. Differentiating along this family of cubics gives the exact identity

```math
-\frac{M_\alpha'(\varphi)}{\sin 6\varphi}=\frac{\alpha}{18}\,f[y_1,y_2,y_3],\qquad f(t)=t^{\alpha-1}.
```

Here $`f[\cdot,\cdot,\cdot]`$ is a second-order **divided difference**. Its sign is that of $`f''`$, which is positive for $`\alpha>2`$. The location of the minimum is governed in the same way by the sign of $`f^{(5)}`$.

## Contents

| Path | What |
|---|---|
| [`paper/`](paper/) | Full statement and proof (LaTeX source and compiled PDF) |
| [`verify.py`](verify.py) | 40-digit numerical check of every statement (`pip install mpmath`) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization, `sorry`-free (details in [`lean/README.md`](lean/README.md)) |

## Formal verification

The core results are formalized in Lean 4 with Mathlib, with no `sorry`; the axiom check reports only `propext`, `Classical.choice` and `Quot.sound`. The formalization covers:

- the identity for $`M_\alpha`$;
- the monotonicity of $`M_\alpha`$ in all three ranges of $`\alpha`$;
- hypothesis (H);
- the endpoint limits and closed forms;
- the direction of monotonicity of $`-M_\alpha'/\sin 6\varphi`$;
- the constant cases $`\alpha=3,4,5`$;
- the sharpness of $`C(\alpha)`$ (as an `IsGLB` statement).

The general-$`g`$ versions, the symmetry argument for the full circle and the $`\alpha\to 2^+`$ asymptotics are not formalized; see [`lean/README.md`](lean/README.md).
