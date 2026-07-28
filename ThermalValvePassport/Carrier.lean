import ThermalValvePassport.TFVD

/-!
# Carrier-covariant passport

This module replaces the geometric carrier `q ^ k` by an arbitrary nonzero
sequence `w k`. It also records what a misspecified carrier does: the passport
sees the relative carrier as part of the recovered structure.
-/

open scoped BigOperators

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Dress a structural sequence by an arbitrary carrier. -/
def carrierDressed (c : K) (w g : ℕ → K) (k : ℕ) : K :=
  c * w k * g k

/-- Divide an observation by a supplied carrier. -/
def carrierUndress (w x : ℕ → K) (k : ℕ) : K :=
  x k / w k

/-- Second-difference bracket covariant under an arbitrary carrier. -/
def carrierBracket (w x : ℕ → K) (k : ℕ) : K :=
  (w (k + 1) / w (k + 2)) * x (k + 2) -
    2 * x (k + 1) +
    (w (k + 1) / w k) * x k

/-- Boundary trace after removal of the supplied carrier. -/
def carrierTrace (w x : ℕ → K) : K :=
  w 0 * x 1 / (w 1 * x 0)

/-- Normalized carrier-covariant curvature. -/
def carrierCurvature (w x : ℕ → K) (k : ℕ) : K :=
  w 0 * carrierBracket w x k / (w (k + 1) * x 0)

/-- The carrier bracket is the ordinary curvature of the undressed sequence,
redressed at the middle stencil coordinate. -/
theorem carrierBracket_div_eq_secondDifference_undress
    (w x : ℕ → K) (k : ℕ) (hw : ∀ n, w n ≠ 0) :
    carrierBracket w x k / w (k + 1) =
      secondDifference (carrierUndress w x) k := by
  unfold carrierBracket carrierUndress secondDifference
  field_simp [hw k, hw (k + 1), hw (k + 2)]
  ring

/-- The carrier bracket removes an arbitrary nonzero dressing exactly. -/
theorem carrierBracket_dressed
    (c : K) (w g : ℕ → K) (k : ℕ) (hw : ∀ n, w n ≠ 0) :
    carrierBracket w (carrierDressed c w g) k =
      c * w (k + 1) * secondDifference g k := by
  unfold carrierBracket carrierDressed secondDifference
  field_simp [hw k, hw (k + 1), hw (k + 2)]
  ring

/-- The carrier trace removes the carrier and global scale. -/
theorem carrierTrace_dressed
    (c : K) (w g : ℕ → K)
    (hw : ∀ n, w n ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    carrierTrace w (carrierDressed c w g) = g 1 / g 0 := by
  unfold carrierTrace carrierDressed
  field_simp [hw 0, hw 1, hc, hg0]
  ring

/-- The normalized carrier curvature is the normalized structural curvature. -/
theorem carrierCurvature_dressed
    (c : K) (w g : ℕ → K) (k : ℕ)
    (hw : ∀ n, w n ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    carrierCurvature w (carrierDressed c w g) k =
      secondDifference g k / g 0 := by
  unfold carrierCurvature
  rw [carrierBracket_dressed c w g k hw]
  unfold carrierDressed
  field_simp [hw 0, hw (k + 1), hc, hg0]
  ring

namespace Passport

variable (K)

/-- Passport extracted with an arbitrary carrier. -/
def ofCarrierObservation (w x : ℕ → K) : Passport K where
  trace := carrierTrace w x
  curvature := carrierCurvature w x

variable {K}

/-- Correct carrier removal recovers the canonical normalized passport. -/
theorem ofCarrierObservation_dressed
    (c : K) (w g : ℕ → K)
    (hw : ∀ n, w n ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    ofCarrierObservation K w (carrierDressed c w g) =
      normalized K g := by
  apply Passport.ext
  · exact carrierTrace_dressed c w g hw hc hg0
  · funext k
    exact carrierCurvature_dressed c w g k hw hc hg0

/-- Global scale and arbitrary nonzero carrier are both gauge data. -/
theorem invariant_under_carrier
    (c₁ c₂ : K) (w₁ w₂ g : ℕ → K)
    (hw₁ : ∀ n, w₁ n ≠ 0) (hw₂ : ∀ n, w₂ n ≠ 0)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hg0 : g 0 ≠ 0) :
    ofCarrierObservation K w₁ (carrierDressed c₁ w₁ g) =
      ofCarrierObservation K w₂ (carrierDressed c₂ w₂ g) := by
  calc
    ofCarrierObservation K w₁ (carrierDressed c₁ w₁ g) =
        normalized K g :=
      ofCarrierObservation_dressed c₁ w₁ g hw₁ hc₁ hg0
    _ = ofCarrierObservation K w₂ (carrierDressed c₂ w₂ g) :=
      (ofCarrierObservation_dressed c₂ w₂ g hw₂ hc₂ hg0).symm

/-- The arbitrary-carrier passport reconstructs the normalized structure. -/
theorem reconstruct_carrierObservation
    (c : K) (w g : ℕ → K)
    (hw : ∀ n, w n ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0)
    (n : ℕ) :
    reconstruct (ofCarrierObservation K w (carrierDressed c w g)) n =
      g n / g 0 := by
  rw [ofCarrierObservation_dressed c w g hw hc hg0]
  exact reconstruct_normalized g hg0 n

end Passport

/-- Structural sequence left after dividing an actual carrier by a supplied
carrier. -/
def relativeCarrierStructure
    (supplied actual g : ℕ → K) (k : ℕ) : K :=
  (actual k / supplied k) * g k

/-- Any observation can be refactored through a nonzero supplied carrier, with
the carrier mismatch transferred exactly into the structure. -/
theorem carrierDressed_factor_through_relative
    (c : K) (supplied actual g : ℕ → K)
    (hsupplied : ∀ n, supplied n ≠ 0) :
    carrierDressed c actual g =
      carrierDressed c supplied
        (relativeCarrierStructure supplied actual g) := by
  funext n
  unfold carrierDressed relativeCarrierStructure
  field_simp [hsupplied n]
  ring

namespace Passport

/-- Carrier misspecification is not erased: the recovered structure is
multiplied by the actual-to-supplied carrier ratio. -/
theorem ofCarrierObservation_misspecified
    (c : K) (supplied actual g : ℕ → K)
    (hsupplied : ∀ n, supplied n ≠ 0)
    (hactual : ∀ n, actual n ≠ 0)
    (hc : c ≠ 0) (hg0 : g 0 ≠ 0) :
    ofCarrierObservation K supplied (carrierDressed c actual g) =
      normalized K (relativeCarrierStructure supplied actual g) := by
  rw [carrierDressed_factor_through_relative c supplied actual g
    hsupplied]
  apply ofCarrierObservation_dressed
  · exact hsupplied
  · exact hc
  · exact mul_ne_zero (div_ne_zero (hactual 0) (hsupplied 0)) hg0

end Passport

/-- Carrier-return channel determined by the first two undressed values. -/
def carrierReturn (w x : ℕ → K) (n : ℕ) : K :=
  w n *
    (carrierUndress w x 0 +
      (n : K) * (carrierUndress w x 1 - carrierUndress w x 0))

/-- Causal Green channel reconstructed from carrier-covariant curvature. -/
def carrierGreen (w x : ℕ → K) (n : ℕ) : K :=
  w n *
    ∑ j ∈ Finset.range n,
      ((n - 1 - j : ℕ) : K) *
        (carrierBracket w x j / w (j + 1))

/-- Carrier-covariant scalar TFVD for an arbitrary observation. -/
theorem carrierScalarReconstruction
    (w x : ℕ → K) (hw : ∀ n, w n ≠ 0) (n : ℕ) :
    x n = carrierReturn w x n + carrierGreen w x n := by
  have hformula :=
    secondDifferenceReconstruction (carrierUndress w x) n
  have hsum :
      (∑ j ∈ Finset.range n,
        ((n - 1 - j : ℕ) : K) *
          secondDifference (carrierUndress w x) j) =
      (∑ j ∈ Finset.range n,
        ((n - 1 - j : ℕ) : K) *
          (carrierBracket w x j / w (j + 1))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [carrierBracket_div_eq_secondDifference_undress w x j hw]
  calc
    x n = w n * carrierUndress w x n := by
      unfold carrierUndress
      field_simp [hw n] <;> ring
    _ = w n *
        (carrierUndress w x 0 +
          (n : K) *
            (carrierUndress w x 1 - carrierUndress w x 0) +
          ∑ j ∈ Finset.range n,
            ((n - 1 - j : ℕ) : K) *
              secondDifference (carrierUndress w x) j) := by
      rw [hformula]
    _ = carrierReturn w x n + carrierGreen w x n := by
      rw [hsum]
      unfold carrierReturn carrierGreen
      ring

/-- Geometric carrier used by the original passport. -/
def geometricCarrier (q : K) (n : ℕ) : K :=
  q ^ n

theorem geometricCarrier_ratio_succ
    (q : K) (k : ℕ) (hq : q ≠ 0) :
    geometricCarrier q (k + 1) / geometricCarrier q k = q := by
  have hstep :
      geometricCarrier q (k + 1) = geometricCarrier q k * q := by
    unfold geometricCarrier
    rw [pow_succ]
  rw [hstep]
  have hk : geometricCarrier q k ≠ 0 := by
    simpa [geometricCarrier] using pow_ne_zero k hq
  field_simp [hk] <;> ring

theorem geometricCarrier_ratio_next
    (q : K) (k : ℕ) (hq : q ≠ 0) :
    geometricCarrier q (k + 1) / geometricCarrier q (k + 2) = q⁻¹ := by
  have hstep :
      geometricCarrier q (k + 2) =
        geometricCarrier q (k + 1) * q := by
    unfold geometricCarrier
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  rw [hstep]
  have hk1 : geometricCarrier q (k + 1) ≠ 0 := by
    simpa [geometricCarrier] using pow_ne_zero (k + 1) hq
  field_simp [hq, hk1] <;> ring

/-- The carrier bracket specializes to the existing geometric bracket. -/
theorem carrierBracket_geometric
    (q : K) (x : ℕ → K) (k : ℕ) (hq : q ≠ 0) :
    carrierBracket (geometricCarrier q) x k =
      weightedBracket q x k := by
  unfold carrierBracket weightedBracket
  rw [geometricCarrier_ratio_next q k hq,
    geometricCarrier_ratio_succ q k hq]

/-- The carrier trace specializes to the existing geometric trace. -/
theorem carrierTrace_geometric
    (q : K) (x : ℕ → K) :
    carrierTrace (geometricCarrier q) x =
      thermalTraceRatio q x := by
  simp [carrierTrace, thermalTraceRatio, geometricCarrier]

/-- Carrier curvature specializes to the existing geometric curvature. -/
theorem carrierCurvature_geometric
    (q : K) (x : ℕ → K) (k : ℕ) (hq : q ≠ 0) :
    carrierCurvature (geometricCarrier q) x k =
      thermalCurvature q x k := by
  unfold carrierCurvature thermalCurvature
  rw [carrierBracket_geometric q x k hq]
  simp [geometricCarrier]

end

end ThermalValvePassport
