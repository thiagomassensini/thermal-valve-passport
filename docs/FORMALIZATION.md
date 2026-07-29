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

## 7. Carrier-covariant passport

### Definitions

```lean
carrierDressed
carrierUndress
carrierBracket
carrierTrace
carrierCurvature
Passport.ofCarrierObservation
```

For an arbitrary nonzero carrier $w$, the bracket is

```math
B_wx(k)
=
\frac{w_{k+1}}{w_{k+2}}x_{k+2}
-2x_{k+1}
+\frac{w_{k+1}}{w_k}x_k.
```

### Theorems

```lean
carrierBracket_div_eq_secondDifference_undress
carrierBracket_dressed
carrierTrace_dressed
carrierCurvature_dressed
Passport.ofCarrierObservation_dressed
Passport.invariant_under_carrier
Passport.reconstruct_carrierObservation
```

The bracket is the ordinary curvature of the undressed observation, redressed
at the middle stencil coordinate:

```math
\frac{B_wx(k)}{w_{k+1}}
=
\Delta^2\!\left(\frac{x}{w}\right)(k).
```

For $x_k=cw_kg_k$,

```math
\boxed{
B_wx(k)=c\,w_{k+1}\Delta^2g(k)
}
```

and

```math
\boxed{
\tau_w(x)=\frac{g_1}{g_0},
\qquad
\kappa_w(x;k)=\frac{\Delta^2g(k)}{g_0}.
}
```

Therefore arbitrary-carrier passport extraction equals the same canonical
normalized passport already reconstructed by `Passport.reconstruct`.

## 8. Carrier misspecification

### Definition

```lean
relativeCarrierStructure
```

The residual structure produced by a supplied carrier $\widetilde w$ and an
actual carrier $w$ is

$$
g_k^{\mathrm{res}}
=
\frac{w_k}{\widetilde w_k}g_k.
$$

### Theorems

```lean
carrierDressed_factor_through_relative
Passport.ofCarrierObservation_misspecified
```

They prove the exact factorization

```math
c\,w_{\bullet}g
=
c\,\widetilde w_{\bullet}
\left(\frac{w_{\bullet}}{\widetilde w_{\bullet}}g\right)
```

and the passport identity

```math
\boxed{
\mathcal P_{\widetilde w}(c\,w_{\bullet}g)
=
\mathcal P_{\mathrm{norm}}\!\left(
\frac{w_{\bullet}}{\widetilde w_{\bullet}}g
\right).
}
```

This is a falsification guardrail: carrier error is transferred into the
reported structure rather than being silently removed.

## 9. Carrier TFVD and geometric specialization

### Definitions

```lean
carrierReturn
carrierGreen
geometricCarrier
```

### Theorems

```lean
carrierScalarReconstruction
geometricCarrier_ratio_succ
geometricCarrier_ratio_next
carrierBracket_geometric
carrierTrace_geometric
carrierCurvature_geometric
```

The arbitrary-carrier scalar reconstruction is

```math
\boxed{
x_n
=
w_n\left[
\frac{x_0}{w_0}
+n\left(\frac{x_1}{w_1}-\frac{x_0}{w_0}\right)
+\sum_{j<n}(n-1-j)\frac{B_wx(j)}{w_{j+1}}
\right].
}
```

For $w_k=q^k$, the new bracket, trace, and curvature agree with
`weightedBracket`, `thermalTraceRatio`, and `thermalCurvature`. Thus the
arbitrary-carrier development is a strict generalization of the original
geometric library.

## 10. Natural carrier cutoff and tail provenance

### Definition

```lean
carrierCutoffCommutator
```

This module uses the natural, unshifted stencil index:

$$
[B_w,Q_M]x(k)=B_w(Q_Mx)(k)-Q_M(B_wx)(k).
$$

### Theorems

```lean
carrierCutoffCommutator_interior
carrierCutoffCommutator_firstBoundary
carrierCutoffCommutator_secondBoundary
carrierCutoffCommutator_exterior
carrierCutoffCommutator_support_subset
carrierBracket_firstBoundary_correction
carrierBracket_secondBoundary_correction
carrierBracket_difference_of_same_prefix
carrierCutoffCommutator_geometric
```

For $M=k+2$, the two possible boundary values are

```math
\boxed{
[B_w,Q_{k+2}]x(k)
=
-\frac{w_{k+1}}{w_{k+2}}x_{k+2}
}
```

and

```math
\boxed{
[B_w,Q_{k+2}]x(k+1)
=
2x_{k+2}
-\frac{w_{k+2}}{w_{k+3}}x_{k+3}.
}
```

Hence

$$
\operatorname{supp}[B_w,Q_{k+2}]x
\subseteq\{k,k+1\}.
$$

The inclusion is intentionally not stated as equality: either boundary value
may vanish.

The original `Cutoff` module reserves output coordinate zero, so its two
stencil positions are shifted to $\{M-1,M\}$. The natural carrier convention
reports the same positions as $\{M-2,M-1\}$.

Finally, if $Q_{k+2}x=Q_{k+2}y$, then

```math
\boxed{
B_wx(k)-B_wy(k)
=
\frac{w_{k+1}}{w_{k+2}}
\left(x_{k+2}-y_{k+2}\right).
}
```

The visible prefix therefore does not determine the missing tail value. An
exact boundary correction that consumes that value is a ledger with explicit
provenance, not a tail predictor.

## 11. Nonuniform-mesh passport

### Definitions

```lean
dividedSlope
dividedCurvature
affineOnMesh
addAffineGauge
additiveObservation
NonuniformPassport
NonuniformPassport.ofObservation
NonuniformPassport.reconstructedSlope
NonuniformPassport.reconstruct
```

For arbitrary mesh coordinates \(m_k\),

```math
s_k=\frac{x_{k+1}-x_k}{m_{k+1}-m_k},
\qquad
\kappa_k
=
\frac{2}{m_{k+2}-m_k}(s_{k+1}-s_k).
```

### Theorems

```lean
dividedSlope_affine
dividedCurvature_affine
dividedSlope_addAffineGauge
dividedCurvature_addAffineGauge
additiveObservation_difference
dividedCurvature_crossGaugeDifference
dividedCurvature_to_slopeIncrement
NonuniformPassport.initialSlope_add_curvature_sum
NonuniformPassport.reconstructedSlope_ofObservation
NonuniformPassport.reconstruct_ofObservation
NonuniformPassport.ofObservation_injective
NonuniformPassport.eq_affineOnMesh_of_dividedCurvature_eq_zero
```

The passport \((x_0,s_0,\kappa)\) reconstructs every sampled coordinate
exactly. Hence passport equality implies observation equality, and zero
curvature forces the unique affine mesh profile fixed by the first value and
first divided slope.

## 12. Richardson scale-law admissibility

### Definitions

```lean
prefixFromTail
firstRichardson
affineScaleReadout
secondRichardson
quadraticScaleReadout
```

### Theorems

```lean
firstRichardson_prefix_identity
firstRichardson_prefix_eq_one_iff
firstRichardson_prefix_eq_one_iff_half
firstRichardson_eq_target_iff
firstRichardson_affineScale
secondRichardson_eq_target_iff
secondRichardson_quadraticScale
```

For \(C_M=1-T_M\),

```math
2C_{2M}-C_M=1+T_M-2T_{2M},
```

so exact recovery of one is equivalent to the required tail relation. The
first- and second-order cancellation theorems are consequences of explicit
affine and quadratic scale laws.

## 13. Reflected reciprocal-root recurrence

### Definitions

```lean
reflectedLambda
reflectedBracket
reflectedReturn
reflectedThermalKernel
affineProfile
```

### Theorems

```lean
reflectedBracket_change_lambda
reflectedBracket_geometric
reflectedBracket_inverseGeometric
reflectedBracket_reflectedReturn
reflectedBracket_reflectedThermalKernel
reflectedBracket_kernel_mismatch
secondDifference_affineProfile
secondDifference_sub_profile_eq_zero
```

The coefficient \(q+q^{-1}\) annihilates both reciprocal roots and their
finite reflected kernel. A coefficient mismatch appears as an exact local
residual rather than being erased.

## Certified dependency chain

```math
\boxed{
\text{arbitrary carrier dressing}
\longrightarrow
\text{carrier bracket}
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
\qquad
\text{carrier misspecification}
\qquad
\text{Richardson admissibility}.
}
```

## Status

The GitHub CI:

1. builds the project with `lake build --wfail`;
2. rejects `sorry`, `admit`, and user declarations of `axiom`;
3. recompiles the public root module `ThermalValvePassport.lean`;
4. publishes a versioned release only after a green build on `main`.
