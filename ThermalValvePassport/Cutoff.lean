import ThermalValvePassport.Core

/-!
# Exact moving-cutoff commutator

The weighted bracket is a second-order local stencil.  Truncating an input and
then applying the bracket differs from truncating the bracket only in two
boundary coordinates.  This file identifies those coordinates exactly.
-/

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- Prefix cutoff: preserve coordinates below `M` and zero the rest. -/
def truncate (M : ℕ) (x : ℕ → K) (n : ℕ) : K :=
  if n < M then x n else 0

@[simp] theorem truncate_of_lt
    (M : ℕ) (x : ℕ → K) {n : ℕ} (h : n < M) :
    truncate M x n = x n := by
  simp [truncate, h]

@[simp] theorem truncate_of_ge
    (M : ℕ) (x : ℕ → K) {n : ℕ} (h : M ≤ n) :
    truncate M x n = 0 := by
  simp [truncate, Nat.not_lt.mpr h]

/-- Output-indexed bracket, with coordinate zero reserved for the boundary. -/
def weightedBracketOutput (q : K) (x : ℕ → K) : ℕ → K
  | 0 => 0
  | n + 1 => weightedBracket q x n

/-- Commutator `[B_q,Q_M] = B_q Q_M - Q_M B_q`. -/
def cutoffCommutator (q : K) (M : ℕ) (x : ℕ → K) (n : ℕ) : K :=
  weightedBracketOutput q (truncate M x) n -
    truncate M (weightedBracketOutput q x) n

/-- Strictly inside the cutoff, truncation commutes with the bracket. -/
theorem cutoffCommutator_interior
    (q : K) (M : ℕ) (x : ℕ → K) (k : ℕ)
    (h : k + 2 < M) :
    cutoffCommutator q M x (k + 1) = 0 := by
  have hk : k < M := by omega
  have hk1 : k + 1 < M := by omega
  have hk2 : k + 2 < M := h
  simp [cutoffCommutator, weightedBracketOutput, weightedBracket,
    truncate, hk, hk1, hk2]

/-- First boundary coordinate: the missing future value enters with `-q⁻¹`. -/
theorem cutoffCommutator_leftBoundary
    (q : K) (x : ℕ → K) (k : ℕ) :
    cutoffCommutator q (k + 2) x (k + 1) =
      -q⁻¹ * x (k + 2) := by
  have hk : k < k + 2 := by omega
  have hk1 : k + 1 < k + 2 := by omega
  simp [cutoffCommutator, weightedBracketOutput, weightedBracket,
    truncate, hk, hk1]
  ring

/-- Second boundary coordinate: the last visible value enters with `q`. -/
theorem cutoffCommutator_rightBoundary
    (q : K) (x : ℕ → K) (k : ℕ) :
    cutoffCommutator q (k + 2) x (k + 2) =
      q * x (k + 1) := by
  have hk1 : k + 1 < k + 2 := by omega
  have hk3 : ¬ k + 3 < k + 2 := by omega
  simp [cutoffCommutator, weightedBracketOutput, weightedBracket,
    truncate, hk1, hk3]

/-- After the two boundary coordinates, the commutator vanishes again. -/
theorem cutoffCommutator_exterior
    (q : K) (M : ℕ) (x : ℕ → K) (r : ℕ) :
    cutoffCommutator q M x (M + r + 1) = 0 := by
  have h0 : M ≤ M + r := by omega
  have h1 : M ≤ M + r + 1 := by omega
  have h2 : M ≤ M + r + 2 := by omega
  simp [cutoffCommutator, weightedBracketOutput, weightedBracket,
    truncate, Nat.not_lt.mpr h0, Nat.not_lt.mpr h1,
    Nat.not_lt.mpr h2]

/-- Exact correction of the last interior bracket coordinate. -/
theorem exact_leftBoundary_correction
    (q : K) (x : ℕ → K) (k : ℕ) :
    weightedBracketOutput q x (k + 1) =
      weightedBracketOutput q (truncate (k + 2) x) (k + 1) +
        q⁻¹ * x (k + 2) := by
  have hcomm := cutoffCommutator_leftBoundary q x k
  unfold cutoffCommutator at hcomm
  have hk1 : k + 1 < k + 2 := by omega
  simp [truncate, hk1] at hcomm
  linear_combination -hcomm

/-- The moving-cutoff defect is exactly supported on two consecutive outputs. -/
theorem cutoffCommutator_two_boundary_values
    (q : K) (x : ℕ → K) (k : ℕ) :
    (cutoffCommutator q (k + 2) x (k + 1),
      cutoffCommutator q (k + 2) x (k + 2)) =
      (-q⁻¹ * x (k + 2), q * x (k + 1)) := by
  rw [cutoffCommutator_leftBoundary, cutoffCommutator_rightBoundary]

end

end ThermalValvePassport
