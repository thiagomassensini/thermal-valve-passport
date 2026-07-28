# Thermal Valve Passport v0.1.1

Documentation-rendering release for the independent Lean 4 formalization of the Thermal Valve Passport.

## GitHub Markdown rendering

- converts display mathematics from `\[`…`\]` to GitHub-supported `$$` delimiters;
- uses `$...$` for inline mathematics;
- restructures `README.md` into a rendered overview of invariance, completeness, TFVD, cutoff provenance, and Richardson cancellation;
- expands `docs/FORMALIZATION.md` into a theorem-by-theorem map with GitHub-rendered equations;
- adds direct links from the README to the certified Lean modules and formalization map.

The central rendered identity is

$$
B_q\!\left(cq^{\bullet}g\right)(k)
=
cq^{k+1}\Delta^2g(k),
$$

and the completeness theorem is displayed as

$$
\operatorname{reconstruct}\!\left(\mathcal P_q(cq^{\bullet}g),n\right)
=
\frac{g_n}{g_0}.
$$

## Certified core

The Lean theorem surface is unchanged from `v0.1.0`:

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
