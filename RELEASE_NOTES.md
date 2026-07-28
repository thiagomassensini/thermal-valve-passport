# Thermal Valve Passport v0.1.2

Targeted Markdown-rendering patch for the independent Lean 4 formalization of the Thermal Valve Passport.

## Multiline mathematics

- keeps short display equations in the existing `$$...$$` form;
- converts only multiline display equations to GitHub's fenced `math` syntax;
- fixes the formulas that were being split into headings and raw LaTeX on narrow web layouts;
- preserves every theorem statement, formula, link, and explanatory paragraph.

The corrected multiline displays include the completeness theorem,

```math
\operatorname{reconstruct}\!\left(\mathcal P_q(cq^{\bullet}g),n\right)
=
\frac{g_n}{g_0},
```

the scalar TFVD reconstruction,

```math
x_n
=
q^n\left(x_0+n\,d_qx(0)\right)
+
\sum_{j<n}(n-1-j)q^{n-1-j}B_qx(j),
```

and the connected Richardson identity,

```math
2K_{1/2}-K_1
=
\frac12\varepsilon_A\varepsilon_B.
```

## Certified core

The Lean theorem surface is unchanged from `v0.1.1`:

- weighted geometric dressing and weighted second-difference bracket;
- exact invariance of trace and curvature under `x k = c * q^k * g k`;
- finite scalar TFVD / Green reconstruction;
- completeness of the passport for the normalized structure `g / g 0`;
- exact two-coordinate moving-cutoff commutator;
- connected Richardson identity and the scale-independent guardrail.

## Validation

The release remains gated by:

```bash
lake build --wfail
lake env lean ThermalValvePassport.lean
```

The CI also rejects proof placeholders. This release changes documentation and metadata only; no mathematical theorem or proof term is weakened.
