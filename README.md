# Thermal Valve Passport

[![Lean CI](https://github.com/thiagomassensini/thermal-valve-passport/actions/workflows/ci.yml/badge.svg)](https://github.com/thiagomassensini/thermal-valve-passport/actions/workflows/ci.yml)

Lean 4 formalization of a gauge-invariant discrete-curvature passport for geometrically dressed sequences.

The library is intentionally independent of any particular physical model, number-theoretic object, or privileged use of the complex plane. Its core theorems are stated over an arbitrary commutative field.

## Structural model

For a sequence

\[
x_k=cq^kg_k,
\]

the weighted bracket

\[
B_qx(k)=q^{-1}x_{k+2}-2x_{k+1}+qx_k
\]

satisfies

\[
B_qx(k)=cq^{k+1}\bigl(g_{k+2}-2g_{k+1}+g_k\bigr).
\]

The passport stores

\[
\tau_q(x)=\frac{x_1}{qx_0},
\qquad
\kappa_q(x;k)=\frac{B_qx(k)}{q^{k+1}x_0}.
\]

When `c`, `q`, and `g 0` are nonzero,

\[
\tau_q(x)=\frac{g_1}{g_0},
\qquad
\kappa_q(x;k)=\frac{\Delta^2g_k}{g_0}.
\]

Thus the passport is invariant under geometric dressing and reconstructs the complete normalized structure `g k / g 0`.

## Certified modules

- `ThermalValvePassport.Core`: dressing, trace, curvature, and passport invariance;
- `ThermalValvePassport.TFVD`: finite Green/TFVD reconstruction and completeness;
- `ThermalValvePassport.Cutoff`: exact two-coordinate moving-cutoff commutator;
- `ThermalValvePassport.Richardson`: connected Richardson cancellation and its scale-independent guardrail.

## Build

```bash
lake exe cache get
lake build --wfail
```

The GitHub Actions workflow also runs independent kernel checks and rejects proof placeholders.

## Release and citation

Releases are tagged automatically after a green build on `main`. Metadata for GitHub/Zenodo and citation software is provided in `.zenodo.json` and `CITATION.cff`.

## Scope

This repository formalizes an algebraic method. Physical interpretations, numerical thresholds, and empirical applications belong in separate downstream projects.

## License

Apache-2.0.
