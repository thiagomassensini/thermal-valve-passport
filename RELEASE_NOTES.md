# Thermal Valve Passport v0.4.0

Bilateral integer-indexed carrier invariance, paired reflection channels,
exact reconstruction, and symmetric cutoff provenance for the independent
Lean 4 formalization of the Thermal Valve Passport.

## Bilateral carrier removal

For

```math
x_n=cq^ng_n,\qquad n\in\mathbb Z,
```

the normalized paired product obeys

```math
\frac{x_nx_{-n}}{x_0^2}
=
\frac{g_ng_{-n}}{g_0^2}.
```

Thus normalization and the bilateral geometric carrier cancel exactly without
introducing a square root or logarithm. The theorem is valid even when
\(g_0=0\), using the field's total division convention; nonzero \(c\) and
\(q\) remain necessary.

## Complementary ratio channel

Under the explicit denominator condition \(g_{-n}\ne0\),

```math
\frac{x_n}{x_{-n}}
=
q^{2n}\frac{g_n}{g_{-n}}.
```

If the structural sequence is reflection symmetric at the pair,
\(g_n=g_{-n}\), the ratio recovers \(q^{2n}\). A second redressing preserves
the paired product and multiplies the ratio by its own doubled carrier.

## Reflection and completeness

The release separates an arbitrary integer-indexed observation into additive
reflection-even and reflection-odd channels, with exact reconstruction when
\(2\ne0\).

On the nonnegative half-axis, the paired-product sequence is reconstructed
exactly from its first two coordinates and its complete second-difference
channel. The paired curvature is therefore a complete finite Green ledger,
not merely a numerical fingerprint.

## Symmetric cutoff provenance

The symmetric cutoff keeps precisely the indices satisfying \(|n|\le M\).
Lean proves:

- reflection commutes with the cutoff;
- the prefix and omitted tail sum pointwise to the full observation;
- truncation is idempotent and its support lies in the declared window;
- a reflected pair is either kept together or removed together;
- after pairing, the symmetric cutoff becomes the ordinary prefix cutoff at
  \(M+1\);
- finite paired windows split exactly into observed prefix and explicitly
  indexed tail;
- the paired-curvature cutoff commutator is confined to the final two stencil
  positions, with both boundary values explicit.

The cutoff identities record provenance. They do not infer unseen values from
the visible prefix.

## New certified module

- `ThermalValvePassport.Bilateral`

The module adds 31 theorems and 15 definitions.

## Validation

The release remains gated by:

```bash
lake build --wfail
lake env lean ThermalValvePassport.lean
```

The CI also rejects proof placeholders and user axioms. No empirical
threshold, physical transition claim, special function, probability model, or
privileged complex-plane representation is introduced into the theorem
statements.
