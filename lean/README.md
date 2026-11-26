# Lean 4 formalization

A complete, `sorry`-free Lean 4 + Mathlib formalization of the main results of
[`../paper/holevo_utkin_d3.pdf`](../paper/holevo_utkin_d3.pdf).

**Start with [`HolevoUtkin/Statements.lean`](HolevoUtkin/Statements.lean).** It restates every formalized result in terms of the definitions in [`HolevoUtkin/Defs.lean`](HolevoUtkin/Defs.lean) and ends with `#print axioms` checks. Those checks report only `propext`, `Classical.choice` and `Quot.sound`.

## Build

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

Toolchain: see `lean-toolchain` (currently `leanprover/lean4:v4.37.0-rc1`). The exact Mathlib revision is pinned in `lake-manifest.json`.

## What is formalized

| Paper | Lean (`HolevoUtkin.Main.*`) |
|---|---|
| Thm 1 for $`M_\alpha`$: $`\Phi_\alpha=\frac{\alpha}{18}\,f_\alpha[y_1,y_2,y_3]`$ | `Φ_eq_divided_difference` |
| Thm 2: $`M_\alpha`$ strictly decreasing on $`[0,\pi/6]`$ for $`\alpha>2`$ and $`0<\alpha<1`$, increasing for $`1<\alpha<2`$ | `M_strictAntiOn_of_two_lt`, `M_strictAntiOn_of_pos_of_lt_one`, `M_strictMonoOn_of_one_lt_of_lt_two` |
| Thm 2: values $`M_\alpha(0)`$ and $`M_\alpha(\pi/6)`$ | `M_zero`, `M_pi_div_six` |
| Thm 3: hypothesis (H), i.e. $`\exists\, C>0`$ with $`C\le\Phi_\alpha`$ on $`(0,\pi/6)`$ | `hypothesis_H` |
| Thm 3: limits at the endpoints, with the closed forms $`\Phi_\alpha(0)`$ and $`\Phi_\alpha(\pi/6)`$ | `tendsto_Φ_zero`, `tendsto_Φ_pi_div_six` |
| Thm 3: direction of monotonicity by the sign of $`(\alpha-3)(\alpha-4)(\alpha-5)`$ | `Φ_strictMonoOn`, `Φ_strictAntiOn` |
| Thm 3: constants $`\tfrac{1}{6},\tfrac{2}{9},\tfrac{5}{24}`$ at $`\alpha=3,4,5`$ | `Φ_three`, `Φ_four`, `Φ_five` |
| Thm 3: sharpness, $`C(\alpha)=\inf_{(0,\pi/6)}\Phi_\alpha`$, and $`C(\alpha)>0`$ | `isGLB_Φ`, `Csharp_pos` |

**Not formalized**:

- the general-$`g`$ versions of Theorems 1 and 2 (only $`g(t)=t^\alpha`$ is formalized);
- the passage from $`[0,\pi/6]`$ to the whole circle by symmetry, and the uniqueness of the extremal orbits;
- the asymptotics $`C(\alpha)\sim\tfrac{2}{9}\big(\tfrac{8}{3}\ln 2-1\big)(\alpha-2)`$ as $`\alpha\to 2^+`$.

## Files

| File | Contents |
|---|---|
| `Defs.lean` | $`x_j(\varphi)`$, $`M_\alpha`$, $`\Phi_\alpha`$, the closed forms $`\Phi_0`$, $`\Phi_1`$, and the sharp constant |
| `DividedDiff.lean` | Divided differences over a `Finset`, Lagrange interpolation, generalized Rolle theorem, mean value theorem for divided differences |
| `Cubic.lean` | $`y_j=x_j^2`$ as roots of $`t(t-\tfrac{1}{2})^2=e(\varphi)`$; Vieta relations; $`y_j'\prod_{i\ne j}(y_j-y_i)=-\tfrac{1}{18}\sin 6\varphi`$; location of the roots |
| `Identity.lean` | Theorem 1 and the monotonicity of $`M_\alpha`$ |
| `Sharp.lean` | The six-node identity, the sign of the fifth divided difference, endpoint limits, and sharpness |
| `Statements.lean` | Summary of the main results and the axiom checks |

The proof follows the paper. One detail differs. The monotonicity of $`\Phi_\alpha`$ is obtained from the identity

```math
f[Y(\varphi)]-f[Y(\psi)]=\big(e(\varphi)-e(\psi)\big)\,f[Y(\varphi)\cup Y(\psi)],
```

with six distinct nodes. The sign of the fifth-order divided difference then follows from the mean value theorem for divided differences. The endpoint limits are obtained by squeezing slopes between derivatives.
