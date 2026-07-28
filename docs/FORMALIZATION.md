# Formalization map

## Scope

The library studies arbitrary sequences over a field. No physical model, number-theoretic object, prime base, special function, or privileged complex-plane representation appears in the theorem statements.

Fix a geometrically dressed sequence

```math
x_k = c q^k g_k,
\qquad
c \neq 0,
\qquad
q \neq 0,
\qquad
g_0 \neq 0.
```

The formalization extracts from $x$ the normalized structure $g/g_0$, independently of the global scale $c$ and geometric gauge $q$.

> [!NOTE]
> All theorem names below are declarations exported by the public root module `ThermalValvePassport.lean`.

## 1. Weighted curvature

### Definitions

```lean
secondDifference
weightedFirstDifference
weightedBracket
dressed
```

The weighted bracket is

$$
B_qx(k)=q^{-1}x_{k+2}-2x_{k+1}+qx_k.
$$

### Dressing-removal theorem

```lean
weightedBracket_dressed
```

It proves

```math
\boxed{
B_q\!\left(cq^{\bullet}g\right)(k)
=
cq^{k+1}\Delta^2g(k)
}
```

with

$$
\Delta^2g(k)=g_{k+2}-2g_{k+1}+g_k.
$$

The bracket therefore transfers the geometric dressing into the explicit scalar factor $cq^{k+1}$ and preserves the ordinary structural curvature.

## 2. Passport invariance

### Definitions

```lean
thermalTraceRatio
thermalCurvature
Passport
Passport.ofObservation
Passport.normalized
```

The two passport channels are

```math
\tau_q(x)=\frac{x_1}{qx_0},
\qquad
\kappa_q(x;k)=\frac{B_qx(k)}{q^{k+1}x_0}.
```

### Theorems

```lean
thermalTraceRatio_dressed
thermalCurvature_dressed
Passport.ofObservation_dressed
Passport.invariant_under_dressing
```

They establish

```math
\boxed{
\tau_q\!\left(cq^{\bullet}g\right)=\frac{g_1}{g_0}
}
```

and

```math
\boxed{
\kappa_q\!\left(cq^{\bullet}g;k\right)=\frac{\Delta^2g(k)}{g_0}.
}
```

Consequently,

```math
\mathcal P_{q_1}\!\left(c_1q_1^{\bullet}g\right)
=
\mathcal P_{q_2}\!\left(c_2q_2^{\bullet}g\right).
```

The passport is invariant under simultaneous changes of global scale and geometric gauge.

## 3. Scalar TFVD

### Definitions

```lean
weightedSecondDifference
weightedGreenSum
```

The first-difference form of the bracket is

$$
B_qx(k)=d_qx(k+1)-q\,d_qx(k),
$$

where

$$
d_qx(k)=q^{-1}x_{k+1}-x_k.
$$

### Theorems

```lean
weightedSecondDifference_eq_weightedBracket
weightedSecondDifference_telescope
weightedGreenSum_succ
weightedScalarReconstruction
```

The weighted second differences telescope as

```math
\sum_{j<n}q^{n-1-j}B_qx(j)
=
d_qx(n)-q^nd_qx(0).
```

The scalar reconstruction identity is

```math
\boxed{
x_n
=
q^n\left(x_0+n\,d_qx(0)\right)
+
\sum_{j<n}(n-1-j)q^{n-1-j}B_qx(j).
}
```

This is the finite scalar Teorema Fundamental da Válvula Discreta: the state is the sum of a trace-return term and a causal Green reconstruction of the weighted curvature.

## 4. Completeness of the passport

### Definition

```lean
Passport.reconstruct
```

For a passport $P$, the reconstruction is

```math
\operatorname{reconstruct}(P,n)
=
1+n(P.\mathrm{trace}-1)
+
\sum_{j<n}(n-1-j)P.\mathrm{curvature}(j).
```

### Theorems

```lean
secondDifferenceReconstruction
Passport.reconstruct_normalized
Passport.reconstruct_observation
Passport.normalized_eq_of_passport_eq
Passport.dressed_structures_eq_of_passport_eq
```

The normalized passport reconstructs every structural coordinate:

```math
\boxed{
\operatorname{reconstruct}(\mathcal P_{\mathrm{norm}}(g),n)
=
\frac{g_n}{g_0}.
}
```

For an observed dressed sequence,

```math
\boxed{
\operatorname{reconstruct}\!\left(
\mathcal P_q(cq^{\bullet}g),n
\right)
=
\frac{g_n}{g_0}.
}
```

Therefore equal passports imply equality of normalized structural sequences:

```math
\mathcal P_{q_1}\!\left(c_1q_1^{\bullet}g\right)
=
\mathcal P_{q_2}\!\left(c_2q_2^{\bullet}h\right)
\quad\Longrightarrow\quad
\frac{g_n}{g_0}=\frac{h_n}{h_0}
\quad\forall n.
```

> [!IMPORTANT]
> Completeness is stronger than numerical similarity: within the geometrically dressed class, passport equality determines the full normalized structure.

## 5. Exact cutoff provenance

### Definitions

```lean
truncate
weightedBracketOutput
cutoffCommutator
```

The prefix cutoff is

```math
(Q_Mx)_n=
\begin{cases}
x_n,&n<M,\\
0,&n\ge M.
\end{cases}
```

The moving-cutoff commutator is

$$
[B_q,Q_M]=B_qQ_M-Q_MB_q.
$$

### Theorems

```lean
cutoffCommutator_interior
cutoffCommutator_leftBoundary
cutoffCommutator_rightBoundary
cutoffCommutator_exterior
exact_leftBoundary_correction
cutoffCommutator_two_boundary_values
```

For $M=k+2$, the commutator vanishes in the strict interior and beyond the two boundary outputs. Its complete nonzero data are

```math
\boxed{
[B_q,Q_M]x(M-1)=-q^{-1}x_M,
\qquad
[B_q,Q_M]x(M)=qx_{M-1}.
}
```

The final interior bracket coordinate is corrected exactly by

```math
\boxed{
B_qx(M-1)
=
B_q(Q_Mx)(M-1)+q^{-1}x_M.
}
```

Thus the cutoff defect has explicit provenance rather than being represented by an unspecified approximation error.

## 6. Connected Richardson filter

### Definitions

```lean
affineObservation
connectedCumulant
```

The common affine observation law is

$$
a_h(\varepsilon)=1-h\varepsilon.
$$

For marginal defects $\varepsilon_A$, $\varepsilon_B$ and a joint defect $\varepsilon_{AB}$, the connected cumulant is

```math
K_h
=
a_h(\varepsilon_{AB})
-
a_h(\varepsilon_A)a_h(\varepsilon_B).
```

### Theorems

```lean
connectedCumulant_eq_linear_sub_quadratic
connectedRichardson
scaleIndependentRichardson
richardson_eq_self_of_scale_independent
```

The cumulant expands as

```math
K_h
=
h(\varepsilon_A+\varepsilon_B-\varepsilon_{AB})
-h^2\varepsilon_A\varepsilon_B.
```

The exact connected Richardson identity is

```math
\boxed{
2K_{1/2}-K_1
=
\frac12\varepsilon_A\varepsilon_B.
}
```

For a scale-independent readout $D$,

$$
\boxed{2D-D=D.}
$$

Hence Richardson cancellation isolates connected information only after the required common scale law has been established; it cannot manufacture connected structure from a scale-independent detector.

## Certified dependency chain

```math
\boxed{
\text{dressing}
\longrightarrow
\text{weighted bracket}
\longrightarrow
\text{passport invariance}
\longrightarrow
\text{TFVD reconstruction}
\longrightarrow
\text{completeness}
}
```

with two independent guardrail layers:

```math
\boxed{
\text{cutoff provenance}
\qquad\text{and}\qquad
\text{Richardson admissibility}.
}
```

## Status

The GitHub CI:

1. builds the project with `lake build --wfail`;
2. rejects `sorry`, `admit`, and user declarations of `axiom`;
3. recompiles the public root module `ThermalValvePassport.lean`;
4. publishes a versioned release only after a green build on `main`.
