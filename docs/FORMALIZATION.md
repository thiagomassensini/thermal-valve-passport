# Formalization map

## Scope

The library studies arbitrary sequences over a commutative field. No physical model, number-theoretic object, prime base, special function, or privileged complex-plane representation appears in the theorem statements.

Fix

\[
x_k=cq^kg_k,
\qquad c\ne0,
\qquad q\ne0,
\qquad g_0\ne0.
\]

## 1. Weighted curvature

Definitions:

```lean
secondDifference
weightedFirstDifference
weightedBracket
dressed
```

Theorem:

```lean
weightedBracket_dressed
```

Mathematical statement:

\[
B_q(cq^{\bullet}g)(k)
=
cq^{k+1}\Delta^2g(k).
\]

## 2. Passport invariance

Definitions:

```lean
thermalTraceRatio
thermalCurvature
Passport
Passport.ofObservation
Passport.normalized
```

Theorems:

```lean
thermalTraceRatio_dressed
thermalCurvature_dressed
Passport.ofObservation_dressed
Passport.invariant_under_dressing
```

They establish

\[
\tau_q(x)=\frac{g_1}{g_0},
\qquad
\kappa_q(x;k)=\frac{\Delta^2g(k)}{g_0}.
\]

Thus the passport is invariant under changes of both global scale `c` and geometric gauge `q`.

## 3. Scalar TFVD

Definitions:

```lean
weightedSecondDifference
weightedGreenSum
```

Theorems:

```lean
weightedSecondDifference_eq_weightedBracket
weightedSecondDifference_telescope
weightedGreenSum_succ
weightedScalarReconstruction
```

The reconstruction identity is

\[
x_n
=
q^n\left(x_0+n\,d_qx(0)\right)
+
\sum_{j<n}(n-1-j)q^{n-1-j}\,B_qx(j).
\]

This is the scalar Teorema Fundamental da Válvula Discreta.

## 4. Completeness

Definition:

```lean
Passport.reconstruct
```

Theorems:

```lean
secondDifferenceReconstruction
Passport.reconstruct_normalized
Passport.reconstruct_observation
Passport.normalized_eq_of_passport_eq
Passport.dressed_structures_eq_of_passport_eq
```

The passport reconstructs the entire normalized structure:

\[
\operatorname{reconstruct}(\mathcal P_q(x),n)
=
\frac{g_n}{g_0}.
\]

Therefore equal passports imply equal normalized structural sequences.

## 5. Exact cutoff provenance

Definitions:

```lean
truncate
weightedBracketOutput
cutoffCommutator
```

Theorems:

```lean
cutoffCommutator_interior
cutoffCommutator_leftBoundary
cutoffCommutator_rightBoundary
cutoffCommutator_exterior
exact_leftBoundary_correction
cutoffCommutator_two_boundary_values
```

For cutoff `M = k + 2`, the commutator is supported on exactly two output coordinates:

\[
[B_q,Q_M]x(M-1)=-q^{-1}x_M,
\qquad
[B_q,Q_M]x(M)=qx_{M-1}.
\]

## 6. Connected Richardson filter

Definitions:

```lean
affineObservation
connectedCumulant
```

Theorems:

```lean
connectedCumulant_eq_linear_sub_quadratic
connectedRichardson
scaleIndependentRichardson
richardson_eq_self_of_scale_independent
```

If the same affine scale law holds on the two marginals and the joint channel,

\[
2K_{1/2}-K_1=\frac12\varepsilon_A\varepsilon_B.
\]

If a readout is scale independent, Richardson returns it unchanged. The filter does not manufacture connected information.

## Status

The GitHub CI builds with `--wfail`, rejects proof placeholders, and runs independent kernel checking. A release is created only after the build on `main` succeeds.
