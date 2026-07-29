import ThermalValvePassport.Richardson

/-!
# Scale-law guardrails for Richardson filters

Richardson combinations are exact only when the readouts obey the required
relation across resolutions.  This module records that relation as an
if-and-only-if theorem, then derives the familiar first- and second-order
cancellations from explicit scale laws.
-/

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Observed prefix after removing an omitted tail from a normalized total. -/
def prefixFromTail (tail : K) : K :=
  1 - tail

/-- First Richardson combination of a coarse and a fine readout. -/
def firstRichardson (coarse fine : K) : K :=
  2 * fine - coarse

/-- Exact tail ledger for the first Richardson combination. -/
theorem firstRichardson_prefix_identity
    (coarseTail fineTail : K) :
    firstRichardson (prefixFromTail coarseTail)
        (prefixFromTail fineTail) =
      1 + coarseTail - 2 * fineTail := by
  unfold firstRichardson prefixFromTail
  ring

/-- A normalized prefix extrapolates exactly to one if and only if the fine
tail is related to the coarse tail by the required factor of two. -/
theorem firstRichardson_prefix_eq_one_iff
    (coarseTail fineTail : K) :
    firstRichardson (prefixFromTail coarseTail)
        (prefixFromTail fineTail) = 1 ↔
      2 * fineTail = coarseTail := by
  unfold firstRichardson prefixFromTail
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

/-- Division form of the exact tail scaling law when two is invertible. -/
theorem firstRichardson_prefix_eq_one_iff_half
    (coarseTail fineTail : K) (h2 : (2 : K) ≠ 0) :
    firstRichardson (prefixFromTail coarseTail)
        (prefixFromTail fineTail) = 1 ↔
      fineTail = coarseTail / 2 := by
  rw [firstRichardson_prefix_eq_one_iff]
  constructor
  · intro h
    apply (eq_div_iff h2).2
    simpa [mul_comm] using h
  · intro h
    have hmul := (eq_div_iff h2).1 h
    simpa [mul_comm] using hmul

/-- Exact admissibility condition for a first Richardson extrapolation to hit
a supplied target. -/
theorem firstRichardson_eq_target_iff
    (target coarse fine : K) :
    firstRichardson coarse fine = target ↔
      2 * (fine - target) = coarse - target := by
  unfold firstRichardson
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- Readout with a first-order error at resolution `h`. -/
def affineScaleReadout
    (target error h : K) : K :=
  target + h * error

/-- First Richardson cancellation is exact under the stated affine scale law. -/
theorem firstRichardson_affineScale
    (target error h : K) (h2 : (2 : K) ≠ 0) :
    firstRichardson
        (affineScaleReadout target error h)
        (affineScaleReadout target error (h / 2)) =
      target := by
  unfold firstRichardson affineScaleReadout
  field_simp [h2]
  ring

/-- Second Richardson combination for a quadratic leading error. -/
def secondRichardson (coarse fine : K) : K :=
  (4 * fine - coarse) / 3

/-- Exact admissibility condition for a second-order Richardson extrapolation. -/
theorem secondRichardson_eq_target_iff
    (target coarse fine : K) (h3 : (3 : K) ≠ 0) :
    secondRichardson coarse fine = target ↔
      4 * (fine - target) = coarse - target := by
  unfold secondRichardson
  constructor
  · intro h
    have hmul := (div_eq_iff h3).1 h
    linear_combination hmul
  · intro h
    apply (div_eq_iff h3).2
    linear_combination h

/-- Readout with a quadratic leading error at resolution `h`. -/
def quadraticScaleReadout
    (target error h : K) : K :=
  target + h ^ 2 * error

/-- The second-order Richardson combination cancels an exact quadratic scale
law and returns the target. -/
theorem secondRichardson_quadraticScale
    (target error h : K)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    secondRichardson
        (quadraticScaleReadout target error h)
        (quadraticScaleReadout target error (h / 2)) =
      target := by
  unfold secondRichardson quadraticScaleReadout
  field_simp [h2, h3]
  ring

end

end ThermalValvePassport
