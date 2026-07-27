import ThermalValvePassport.Core

/-!
# Scalar TFVD and completeness of the passport

This file proves a finite Green reconstruction identity.  It then uses the
identity at `q = 1` to show that trace plus normalized curvature reconstructs
the complete structural sequence up to its unavoidable global scale.
-/

open scoped BigOperators

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Weighted second difference written as a difference of first differences. -/
def weightedSecondDifference (q : K) (x : ℕ → K) (n : ℕ) : K :=
  weightedFirstDifference q x (n + 1) - q * weightedFirstDifference q x n

/-- The first-difference definition agrees with the expanded bracket. -/
theorem weightedSecondDifference_eq_weightedBracket
    (q : K) (x : ℕ → K) (n : ℕ) (hq : q ≠ 0) :
    weightedSecondDifference q x n = weightedBracket q x n := by
  unfold weightedSecondDifference weightedFirstDifference weightedBracket
  field_simp [hq]
  ring

/-- Finite triangular Green sum of the weighted second difference. -/
def weightedGreenSum (q : K) (x : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ Finset.range n,
    ((n - 1 - j : ℕ) : K) * q ^ (n - 1 - j) *
      weightedSecondDifference q x j

/-- Weighted second differences telescope to the endpoints of the first difference. -/
theorem weightedSecondDifference_telescope
    (q : K) (x : ℕ → K) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      q ^ (n - 1 - j) * weightedSecondDifference q x j) =
        weightedFirstDifference q x n -
          q ^ n * weightedFirstDifference q x 0 := by
  induction n with
  | zero =>
      simp [weightedFirstDifference]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
      have hprefix :
          (∑ j ∈ Finset.range n,
            q ^ (n - j) * weightedSecondDifference q x j) =
            q * (∑ j ∈ Finset.range n,
              q ^ (n - 1 - j) * weightedSecondDifference q x j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n := Finset.mem_range.mp hj
        have hsub : n - j = (n - 1 - j) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [hprefix, ih]
      unfold weightedSecondDifference
      rw [pow_succ]
      ring

/-- Causal recurrence for the finite Green sum. -/
theorem weightedGreenSum_succ
    (q : K) (x : ℕ → K) (n : ℕ) :
    weightedGreenSum q x (n + 1) =
      q * weightedGreenSum q x n +
        q * (weightedFirstDifference q x n -
          q ^ n * weightedFirstDifference q x 0) := by
  rw [← weightedSecondDifference_telescope q x n]
  unfold weightedGreenSum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero,
    zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - j = (n - 1 - j) + 1 := by omega
  rw [hsub, pow_succ]
  push_cast
  ring

/-- Scalar Teorema Fundamental da Válvula Discreta. -/
theorem weightedScalarReconstruction
    {q : K} (hq : q ≠ 0) (x : ℕ → K) (n : ℕ) :
    x n =
      q ^ n *
          (x 0 + (n : K) * weightedFirstDifference q x 0) +
        weightedGreenSum q x n := by
  induction n with
  | zero =>
      simp [weightedGreenSum]
  | succ n ih =>
      calc
        x (n + 1) =
            q * x n + q * weightedFirstDifference q x n := by
              unfold weightedFirstDifference
              field_simp [hq]
              ring
        _ = q *
              (q ^ n *
                  (x 0 + (n : K) * weightedFirstDifference q x 0) +
                weightedGreenSum q x n) +
              q * weightedFirstDifference q x n := by
                rw [ih]
        _ = q ^ (n + 1) *
              (x 0 + ((n + 1 : ℕ) : K) *
                weightedFirstDifference q x 0) +
              weightedGreenSum q x (n + 1) := by
                rw [weightedGreenSum_succ]
                rw [pow_succ]
                push_cast
                ring

@[simp] theorem weightedSecondDifference_one
    (g : ℕ → K) (n : ℕ) :
    weightedSecondDifference (1 : K) g n = secondDifference g n := by
  unfold weightedSecondDifference weightedFirstDifference secondDifference
  ring

/-- At `q = 1`, the scalar TFVD is the standard second-difference reconstruction. -/
theorem secondDifferenceReconstruction
    (g : ℕ → K) (n : ℕ) :
    g n =
      g 0 + (n : K) * (g 1 - g 0) +
        ∑ j ∈ Finset.range n,
          ((n - 1 - j : ℕ) : K) * secondDifference g j := by
  simpa [weightedFirstDifference, weightedGreenSum] using
    (weightedScalarReconstruction (q := (1 : K)) one_ne_zero g n)

namespace Passport

/-- Reconstruct a normalized structural sequence from its passport. -/
def reconstruct (P : Passport K) (n : ℕ) : K :=
  1 + (n : K) * (P.trace - 1) +
    ∑ j ∈ Finset.range n,
      ((n - 1 - j : ℕ) : K) * P.curvature j

/-- The normalized passport reconstructs every coordinate of the structure. -/
theorem reconstruct_normalized
    (g : ℕ → K) (hg0 : g 0 ≠ 0) (n : ℕ) :
    reconstruct (normalized K g) n = g n / g 0 := by
  have hformula := secondDifferenceReconstruction g n
  have hsum :
      (∑ j ∈ Finset.range n,
        ((n - 1 - j : ℕ) : K) *
          (secondDifference g j / g 0)) =
      (∑ j ∈ Finset.range n,
        ((n - 1 - j : ℕ) : K) * secondDifference g j) / g 0 := by
    calc
      (∑ j ∈ Finset.range n,
        ((n - 1 - j : ℕ) : K) *
          (secondDifference g j / g 0)) =
          ∑ j ∈ Finset.range n,
            (((n - 1 - j : ℕ) : K) * secondDifference g j) / g 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = (∑ j ∈ Finset.range n,
            ((n - 1 - j : ℕ) : K) * secondDifference g j) / g 0 := by
              rw [← Finset.sum_div]
  simp only [reconstruct, normalized]
  rw [hsum]
  calc
    1 + (n : K) * (g 1 / g 0 - 1) +
        (∑ j ∈ Finset.range n,
          ((n - 1 - j : ℕ) : K) * secondDifference g j) / g 0 =
      (g 0 + (n : K) * (g 1 - g 0) +
        ∑ j ∈ Finset.range n,
          ((n - 1 - j : ℕ) : K) * secondDifference g j) / g 0 := by
            field_simp [hg0]
    _ = g n / g 0 := by rw [hformula]

/-- The observed passport reconstructs the underlying structure up to scale. -/
theorem reconstruct_observation
    (c q : K) (g : ℕ → K)
    (hq : q ≠ 0) (hc : c ≠ 0) (hg0 : g 0 ≠ 0) (n : ℕ) :
    reconstruct (ofObservation K q (dressed c q g)) n = g n / g 0 := by
  rw [ofObservation_dressed c q g hq hc hg0]
  exact reconstruct_normalized g hg0 n

/-- Equality of passports forces equality of normalized structures. -/
theorem normalized_eq_of_passport_eq
    (g h : ℕ → K) (hg0 : g 0 ≠ 0) (hh0 : h 0 ≠ 0)
    (hpass : normalized K g = normalized K h) (n : ℕ) :
    g n / g 0 = h n / h 0 := by
  rw [← reconstruct_normalized g hg0 n,
      ← reconstruct_normalized h hh0 n,
      hpass]

/-- Two dressed observations with equal passports have the same normalized structure. -/
theorem dressed_structures_eq_of_passport_eq
    (c₁ q₁ c₂ q₂ : K) (g h : ℕ → K)
    (hq₁ : q₁ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hq₂ : q₂ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hg0 : g 0 ≠ 0) (hh0 : h 0 ≠ 0)
    (hpass :
      ofObservation K q₁ (dressed c₁ q₁ g) =
        ofObservation K q₂ (dressed c₂ q₂ h))
    (n : ℕ) :
    g n / g 0 = h n / h 0 := by
  have hnormalized : normalized K g = normalized K h := by
    calc
      normalized K g = ofObservation K q₁ (dressed c₁ q₁ g) :=
        (ofObservation_dressed c₁ q₁ g hq₁ hc₁ hg0).symm
      _ = ofObservation K q₂ (dressed c₂ q₂ h) := hpass
      _ = normalized K h :=
        ofObservation_dressed c₂ q₂ h hq₂ hc₂ hh0
  exact normalized_eq_of_passport_eq g h hg0 hh0 hnormalized n

end Passport

end

end ThermalValvePassport
