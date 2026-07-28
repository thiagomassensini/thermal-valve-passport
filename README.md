# Thermal Valve Passport

[![Lean CI](https://github.com/thiagomassensini/thermal-valve-passport/actions/workflows/ci.yml/badge.svg)](https://github.com/thiagomassensini/thermal-valve-passport/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/thiagomassensini/thermal-valve-passport)](https://github.com/thiagomassensini/thermal-valve-passport/releases/latest)

Lean 4 formalization of a gauge-invariant discrete-curvature passport for geometrically dressed sequences.

> [!NOTE]
> The library is independent of any particular physical model, number-theoretic object, special function, or privileged use of the complex plane. Its core theorems are stated over an arbitrary field.

## Structural model

For a sequence

$$
x_k = c q^k g_k,
$$

the weighted bracket

$$
B_q x(k) = q^{-1}x_{k+2} - 2x_{k+1} + qx_k
$$

satisfies the exact dressing-removal identity

```math
B_q x(k)
= c q^{k+1}\bigl(g_{k+2} - 2g_{k+1} + g_k\bigr).
```

The passport stores the boundary trace and the normalized weighted curvature:

```math
\tau_q(x) = \frac{x_1}{q x_0},
\qquad
\kappa_q(x;k) = \frac{B_q x(k)}{q^{k+1}x_0}.
```

Whenever $c \neq 0$, $q \neq 0$, and $g_0 \neq 0$,

```math
\tau_q(x) = \frac{g_1}{g_0},
\qquad
\kappa_q(x;k) = \frac{\Delta^2 g(k)}{g_0}.
```

Thus the geometric factor $q^k$ and the global scale $c$ disappear from the passport.

## Completeness

The normalized structural sequence is reconstructed from trace and curvature by

```math
\operatorname{reconstruct}(\mathcal P_q(x),n)
= \frac{g_n}{g_0}.
```

Consequently, equal passports force equal normalized structures:

```math
\mathcal P_{q_1}\!\left(c_1 q_1^{\bullet}g\right)
=
\mathcal P_{q_2}\!\left(c_2 q_2^{\bullet}h\right)
\quad\Longrightarrow\quad
\frac{g_n}{g_0} = \frac{h_n}{h_0}
\quad\text{for every }n.
```

> [!IMPORTANT]
> The passport is not merely a heuristic fingerprint. Inside the dressed class $x_k=cq^kg_k$, it is a complete invariant of the normalized structural sequence.

## Scalar TFVD / Green reconstruction

The finite scalar Teorema Fundamental da Válvula Discreta is

```math
x_n
=
q^n\left(x_0+n\,d_qx(0)\right)
+
\sum_{j<n}(n-1-j)q^{n-1-j}B_qx(j),
```

where

$$
d_qx(k)=q^{-1}x_{k+1}-x_k.
$$

It separates the state into a trace-return channel and a causal Green reconstruction of the weighted curvature.

## Exact moving-cutoff provenance

For the prefix cutoff $Q_M$, the commutator $[B_q,Q_M]$ is supported on exactly two consecutive output coordinates:

```math
[B_q,Q_M]x(M-1)=-q^{-1}x_M,
\qquad
[B_q,Q_M]x(M)=qx_{M-1}.
```

Therefore the final interior bracket coordinate has the exact correction

```math
B_qx(M-1)
=
B_q(Q_Mx)(M-1)+q^{-1}x_M.
```

## Connected Richardson filter

Under the common affine scale law

$$
a_h(\varepsilon)=1-h\varepsilon,
$$

the connected cumulant obeys

```math
2K_{1/2}-K_1
=
\frac12\varepsilon_A\varepsilon_B.
```

A scale-independent readout instead satisfies

$$
2D-D=D,
$$

so Richardson does not manufacture connected information when no scale law is present.

## Certified modules

- [`ThermalValvePassport.Core`](ThermalValvePassport/Core.lean): dressing, trace, curvature, and passport invariance;
- [`ThermalValvePassport.TFVD`](ThermalValvePassport/TFVD.lean): finite Green/TFVD reconstruction and completeness;
- [`ThermalValvePassport.Cutoff`](ThermalValvePassport/Cutoff.lean): exact two-coordinate moving-cutoff commutator;
- [`ThermalValvePassport.Richardson`](ThermalValvePassport/Richardson.lean): connected Richardson cancellation and its scale-independent guardrail.

A theorem-by-theorem map is available in [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md).

## Build

```bash
lake exe cache get
lake build --wfail
```

The GitHub Actions workflow also rejects proof placeholders and recompiles the public root module.

## Release and citation

Releases are tagged automatically after a green build on `main`. GitHub/Zenodo metadata and citation metadata are provided in [`.zenodo.json`](.zenodo.json) and [`CITATION.cff`](CITATION.cff).

## Scope

This repository formalizes an algebraic method. Physical interpretations, numerical thresholds, and empirical applications belong in separate downstream projects.

## License

Apache-2.0.
