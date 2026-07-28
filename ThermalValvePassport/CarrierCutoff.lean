import ThermalValvePassport.Carrier
import ThermalValvePassport.Cutoff

/-!
# Exact cutoff provenance for arbitrary carriers

The natural, unshifted carrier bracket has a cutoff commutator supported on
the last two stencil positions. The two boundary values are recorded
explicitly. A final theorem separates an exact boundary ledger from prediction:
two sequences with the same visible prefix can still have different boundary
brackets because their first omitted values differ.
-/

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Natural commutator between the carrier bracket and a prefix cutoff. -/
def carrierCutoffCommutator
    (w : ℕ → K) (M : ℕ) (x : ℕ → K) (k : ℕ) : K :=
  carrierBracket w (truncate M x) k -
    truncate M (carrierBracket w x) k

/-- Strictly inside the cutoff, carrier bracket and truncation commute. -/
theorem carrierCutoffCommutator_interior
    (w x : ℕ → K) (M k : ℕ) (h : k + 2 < M) :
    carrierCutoffCommutator w M x k = 0 := by
  have hk : k < M := by omega
  have hk1 : k + 1 < M := by omega
  have hk2 : k + 2 < M := h
  simp [carrierCutoffCommutator, carrierBracket, truncate,
    hk, hk1, hk2]

/-- At the first boundary stencil, only the first omitted value is missing. -/
theorem carrierCutoffCommutator_firstBoundary
    (w x : ℕ → K) (k : ℕ) :
    carrierCutoffCommutator w (k + 2) x k =
      -(w (k + 1) / w (k + 2)) * x (k + 2) := by
  have hk : k < k + 2 := by omega
  have hk1 : k + 1 < k + 2 := by omega
  have hk2 : ¬ k + 2 < k + 2 := by omega
  simp [carrierCutoffCommutator, carrierBracket, truncate,
    hk, hk1, hk2]
  ring

/-- At the second boundary stencil, the two future values are missing. -/
theorem carrierCutoffCommutator_secondBoundary
    (w x : ℕ → K) (k : ℕ) :
    carrierCutoffCommutator w (k + 2) x (k + 1) =
      2 * x (k + 2) -
        (w (k + 2) / w (k + 3)) * x (k + 3) := by
  have hk1 : k + 1 < k + 2 := by omega
  have hk2 : ¬ k + 2 < k + 2 := by omega
  have hk3 : ¬ k + 3 < k + 2 := by omega
  simp [carrierCutoffCommutator, carrierBracket, truncate,
    hk1, hk2, hk3]
  ring

/-- At and after the cutoff, both bracketed cutoff and cutoff bracket vanish. -/
theorem carrierCutoffCommutator_exterior
    (w x : ℕ → K) (M k : ℕ) (h : M ≤ k) :
    carrierCutoffCommutator w M x k = 0 := by
  have hk : ¬ k < M := Nat.not_lt.mpr h
  have hk1 : ¬ k + 1 < M := by omega
  have hk2 : ¬ k + 2 < M := by omega
  simp [carrierCutoffCommutator, carrierBracket, truncate,
    hk, hk1, hk2]

/-- The commutator support is contained in the last two stencil positions
before the cutoff. -/
theorem carrierCutoffCommutator_support_subset
    (w x : ℕ → K) (k : ℕ) :
    Function.support (carrierCutoffCommutator w (k + 2) x) ⊆
      ({k, k + 1} : Set ℕ) := by
  intro n hn
  change carrierCutoffCommutator w (k + 2) x n ≠ 0 at hn
  by_cases hnk : n = k
  · simp [hnk]
  by_cases hnk1 : n = k + 1
  · simp [hnk1]
  have hzero : carrierCutoffCommutator w (k + 2) x n = 0 := by
    by_cases hinside : n + 2 < k + 2
    · exact carrierCutoffCommutator_interior w x (k + 2) n hinside
    · have houtside : k + 2 ≤ n := by omega
      exact carrierCutoffCommutator_exterior w x (k + 2) n houtside
  exact (hn hzero).elim

/-- Exact correction of the first boundary bracket. -/
theorem carrierBracket_firstBoundary_correction
    (w x : ℕ → K) (k : ℕ) :
    carrierBracket w x k =
      carrierBracket w (truncate (k + 2) x) k +
        (w (k + 1) / w (k + 2)) * x (k + 2) := by
  have hcomm := carrierCutoffCommutator_firstBoundary w x k
  unfold carrierCutoffCommutator at hcomm
  have hk : k < k + 2 := by omega
  simp [truncate, hk] at hcomm
  linear_combination -hcomm

/-- Exact correction of the second boundary bracket. -/
theorem carrierBracket_secondBoundary_correction
    (w x : ℕ → K) (k : ℕ) :
    carrierBracket w x (k + 1) =
      carrierBracket w (truncate (k + 2) x) (k + 1) -
        2 * x (k + 2) +
        (w (k + 2) / w (k + 3)) * x (k + 3) := by
  have hcomm := carrierCutoffCommutator_secondBoundary w x k
  unfold carrierCutoffCommutator at hcomm
  have hk1 : k + 1 < k + 2 := by omega
  simp [truncate, hk1] at hcomm
  linear_combination -hcomm

/-- Equal visible prefixes leave the boundary-bracket difference determined by
the first omitted values. This is the formal distinction between an exact
cutoff ledger and a prediction of the unseen tail. -/
theorem carrierBracket_difference_of_same_prefix
    (w x y : ℕ → K) (k : ℕ)
    (hprefix : truncate (k + 2) x = truncate (k + 2) y) :
    carrierBracket w x k - carrierBracket w y k =
      (w (k + 1) / w (k + 2)) * (x (k + 2) - y (k + 2)) := by
  have hk : k < k + 2 := by omega
  have hk1 : k + 1 < k + 2 := by omega
  have hxyk := congrFun hprefix k
  have hxyk1 := congrFun hprefix (k + 1)
  simp [truncate, hk] at hxyk
  simp [truncate, hk1] at hxyk1
  unfold carrierBracket
  rw [hxyk, hxyk1]
  ring

/-- For geometric carriers, the arbitrary-carrier cutoff formula reduces to
the existing weighted bracket. -/
theorem carrierCutoffCommutator_geometric
    (q : K) (M : ℕ) (x : ℕ → K) (k : ℕ) (hq : q ≠ 0) :
    carrierCutoffCommutator (geometricCarrier q) M x k =
      weightedBracket q (truncate M x) k -
        truncate M (weightedBracket q x) k := by
  unfold carrierCutoffCommutator
  rw [carrierBracket_geometric q (truncate M x) k hq,
    carrierBracket_geometric q x k hq]

end

end ThermalValvePassport
