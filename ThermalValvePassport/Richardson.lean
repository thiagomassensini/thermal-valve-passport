import Mathlib

/-!
# Connected Richardson filter

Richardson cancellation is meaningful only after a common affine scale law has
been established on two marginal channels and their joint channel.  This file
formalizes the exact connected identity and the scale-independent guardrail.
-/

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [CommField K]

/-- Affine observation law at scale `h`. -/
def affineObservation (h ε : K) : K :=
  1 - h * ε

/-- Connected cumulant of two marginals and one joint channel. -/
def connectedCumulant
    (h εA εB εAB : K) : K :=
  affineObservation h εAB -
    affineObservation h εA * affineObservation h εB

/-- Expansion into a linear background and a connected quadratic term. -/
theorem connectedCumulant_eq_linear_sub_quadratic
    (h εA εB εAB : K) :
    connectedCumulant h εA εB εAB =
      h * (εA + εB - εAB) - h ^ 2 * εA * εB := by
  unfold connectedCumulant affineObservation
  ring

/-- Exact connected Richardson identity. -/
theorem connectedRichardson
    (εA εB εAB : K) (h2 : (2 : K) ≠ 0) :
    2 * connectedCumulant ((1 : K) / 2) εA εB εAB -
        connectedCumulant 1 εA εB εAB =
      ((1 : K) / 2) * εA * εB := by
  unfold connectedCumulant affineObservation
  field_simp [h2]
  ring

/-- A scale-independent defect is returned unchanged; Richardson creates no
connected information by itself. -/
theorem scaleIndependentRichardson (D : K) :
    2 * D - D = D := by
  ring

/-- If two readouts coincide across the two scales, the Richardson output is
exactly that same readout. -/
theorem richardson_eq_self_of_scale_independent
    (D₁ D₂ : K) (h : D₂ = D₁) :
    2 * D₂ - D₁ = D₁ := by
  rw [h]
  exact scaleIndependentRichardson D₁

end

end ThermalValvePassport
