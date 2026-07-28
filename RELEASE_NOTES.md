# Thermal Valve Passport v0.2.0

Carrier-covariant extension and falsification guardrails for the independent
Lean 4 formalization of the Thermal Valve Passport.

## Arbitrary carriers

The geometric carrier $q^k$ is generalized to any nonzero sequence $w_k$.
For

$$
x_k=c\,w_k g_k,
$$

the new bracket

```math
B_wx(k)
=
\frac{w_{k+1}}{w_{k+2}}x_{k+2}
-2x_{k+1}
+\frac{w_{k+1}}{w_k}x_k
```

obeys

```math
B_wx(k)=c\,w_{k+1}\Delta^2g(k).
```

The carrier trace and normalized curvature recover $g_1/g_0$ and
$\Delta^2g(k)/g_0$. The existing passport reconstruction therefore remains
complete for non-geometric carriers.

## Carrier-misspecification guardrail

If an observation uses the actual carrier $w$ but is analyzed with a supplied
carrier $\widetilde w$, Lean proves

```math
\mathcal P_{\widetilde w}(c\,w_{\bullet}g)
=
\mathcal P_{\mathrm{norm}}\!\left(
\frac{w_{\bullet}}{\widetilde w_{\bullet}}g
\right).
```

An incorrect carrier is not silently removed. Its exact ratio to the actual
carrier becomes part of the recovered structure.

## Carrier-covariant TFVD

The finite reconstruction is generalized to

```math
x_n
=
w_n\left[
\frac{x_0}{w_0}
+n\left(\frac{x_1}{w_1}-\frac{x_0}{w_0}\right)
+\sum_{j<n}(n-1-j)\frac{B_wx(j)}{w_{j+1}}
\right].
```

Specialization to $w_k=q^k$ agrees with the original geometric bracket, trace,
and curvature.

## Natural cutoff provenance

For the unshifted arbitrary-carrier stencil, the cutoff commutator has support
contained in the final two stencil positions:

$$
\operatorname{supp}[B_w,Q_M]x\subseteq\{M-2,M-1\}.
$$

Both boundary values and both exact corrections are certified. The release
also proves that two sequences with the same visible prefix can have boundary
brackets differing by

```math
\frac{w_{k+1}}{w_{k+2}}
\left(x_{k+2}-y_{k+2}\right).
```

This separates an exact correction ledger from a prediction of the unseen
tail.

## New certified modules

- `ThermalValvePassport.Carrier`
- `ThermalValvePassport.CarrierCutoff`

## Validation

The release remains gated by:

```bash
lake build --wfail
lake env lean ThermalValvePassport.lean
```

The CI also rejects proof placeholders. No physical model, numerical threshold,
prime base, special function, or privileged complex-plane representation is
introduced into the theorem statements.
