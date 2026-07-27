import Mathlib

/-!
# Core algebra of the Thermal Valve Passport

The declarations in this file are independent of any physical model.  They are
stated over an arbitrary field and describe sequences of the form

`x k = c * q^k * g k`.

The weighted bracket removes the geometric dressing `q^k`; the trace and the
normalized weighted bracket form the thermal-valve passport.
-/

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Ordinary forward second difference. -/
def secondDifference (g : ℕ → K) (k : ℕ) : K :=
  g (k + 2) - 2 * g (k + 1) + g k

/-- First difference in coordinates dressed by a geometric ratio `q`. -/
def weightedFirstDifference (q : K) (x : ℕ → K) (k : ℕ) : K :=
  q⁻¹ * x (k + 1) - x k

/-- Weighted second difference used by the valve. -/
def weightedBracket (q : K) (x : ℕ → K) (k : ℕ) : K :=
  q⁻¹ * x (k + 2) - 2 * x (k + 1) + q * x k

/-- Geometric dressing of a structural sequence. -/
def dressed (c q : K) (g : ℕ → K) (k : ℕ) : K :=
  c * q ^ k * g k

/-- The weighted bracket removes the geometric dressing exactly. -/
theorem weightedBracket_dressed
    (c q : K) (g : ℕ → K) (k : ℕ) (hq : q ≠ 0) :
    weightedBracket q (dressed c q g) k =
      c * q ^ (k + 1) * secondDifference g k := by
  simp only [weightedBracket, dressed, secondDifference]
  simp only [pow_succ]
  field_simp [hq]

/-- Boundary trace ratio of an observed dressed sequence. -/
def thermalTraceRatio (q : K) (x : ℕ → K) : K :=
  x 1 / (q * x 0)

/-- Normalized structural curvature read by the weighted bracket. -/
def thermalCurvature (q : K) (x : ℕ → K) (k : ℕ) : K :=
  weightedBracket q x k / (q ^ (k + 1) * x 0)

/-- The trace ratio of a dressed sequence is independent of its scale and ratio. -/
theorem thermalTraceRatio_dressed
    (c q : K) (g : ℕ → K)
    (hq : q ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    thermalTraceRatio q (dressed c q g) = g 1 / g 0 := by
  unfold thermalTraceRatio dressed
  simp only [pow_zero, pow_one, mul_one]
  field_simp [hq, hc, hg0]

/-- The normalized weighted curvature is the normalized ordinary curvature. -/
theorem thermalCurvature_dressed
    (c q : K) (g : ℕ → K) (k : ℕ)
    (hq : q ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    thermalCurvature q (dressed c q g) k =
      secondDifference g k / g 0 := by
  unfold thermalCurvature
  rw [weightedBracket_dressed c q g k hq]
  unfold dressed
  simp only [pow_zero, mul_one]
  have hpow : q ^ (k + 1) ≠ 0 := pow_ne_zero _ hq
  field_simp [hpow, hc, hg0]

/-- The two-channel passport: initial trace and all normalized curvatures. -/
@[ext]
structure Passport (K : Type*) where
  trace : K
  curvature : ℕ → K

namespace Passport

variable (K)

/-- Passport extracted from an observation using a supplied geometric ratio. -/
def ofObservation (q : K) (x : ℕ → K) : Passport K where
  trace := thermalTraceRatio q x
  curvature := thermalCurvature q x

/-- Canonical passport of a structural sequence, normalized by its ground value. -/
def normalized (g : ℕ → K) : Passport K where
  trace := g 1 / g 0
  curvature := fun k => secondDifference g k / g 0

variable {K}

/-- A dressed observation has exactly the normalized passport of its structure. -/
theorem ofObservation_dressed
    (c q : K) (g : ℕ → K)
    (hq : q ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    ofObservation K q (dressed c q g) = normalized K g := by
  apply Passport.ext
  · exact thermalTraceRatio_dressed c q g hq hc hg0
  · funext k
    exact thermalCurvature_dressed c q g k hq hc hg0

/-- Changing only the geometric gauge and global scale preserves the passport. -/
theorem invariant_under_dressing
    (c₁ q₁ c₂ q₂ : K) (g : ℕ → K)
    (hq₁ : q₁ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hq₂ : q₂ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hg0 : g 0 ≠ 0) :
    ofObservation K q₁ (dressed c₁ q₁ g) =
      ofObservation K q₂ (dressed c₂ q₂ g) := by
  calc
    ofObservation K q₁ (dressed c₁ q₁ g) = normalized K g :=
      ofObservation_dressed c₁ q₁ g hq₁ hc₁ hg0
    _ = ofObservation K q₂ (dressed c₂ q₂ g) :=
      (ofObservation_dressed c₂ q₂ g hq₂ hc₂ hg0).symm

end Passport

end

end ThermalValvePassport
