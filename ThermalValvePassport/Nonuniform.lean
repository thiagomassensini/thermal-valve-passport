import Mathlib

/-!
# Nonuniform-mesh passport

This module replaces an equally spaced coordinate by an arbitrary
nondegenerate mesh.  The divided curvature annihilates affine functions of the
mesh coordinate, is invariant under additive affine gauges, and reconstructs
the complete sampled observation from its initial value, initial divided
slope, and curvature sequence.
-/

open scoped BigOperators

namespace ThermalValvePassport

noncomputable section

variable {K : Type*} [Field K]

/-- First divided difference on an arbitrary mesh. -/
def dividedSlope (mesh x : ℕ → K) (k : ℕ) : K :=
  (x (k + 1) - x k) / (mesh (k + 1) - mesh k)

/-- Symmetric second divided difference on an arbitrary mesh. -/
def dividedCurvature (mesh x : ℕ → K) (k : ℕ) : K :=
  (2 / (mesh (k + 2) - mesh k)) *
    (dividedSlope mesh x (k + 1) - dividedSlope mesh x k)

/-- An affine function of the mesh coordinate. -/
def affineOnMesh (a b : K) (mesh : ℕ → K) (k : ℕ) : K :=
  a + b * mesh k

/-- An affine mesh profile has constant divided slope. -/
theorem dividedSlope_affine
    (mesh : ℕ → K) (a b : K) (k : ℕ)
    (hgap : mesh (k + 1) - mesh k ≠ 0) :
    dividedSlope mesh (affineOnMesh a b mesh) k = b := by
  unfold dividedSlope affineOnMesh
  field_simp [hgap]
  ring

/-- Divided curvature annihilates every affine function of the mesh. -/
theorem dividedCurvature_affine
    (mesh : ℕ → K) (a b : K) (k : ℕ)
    (hgap₀ : mesh (k + 1) - mesh k ≠ 0)
    (hgap₁ : mesh (k + 2) - mesh (k + 1) ≠ 0) :
    dividedCurvature mesh (affineOnMesh a b mesh) k = 0 := by
  unfold dividedCurvature
  rw [dividedSlope_affine mesh a b (k + 1) hgap₁,
    dividedSlope_affine mesh a b k hgap₀]
  ring

/-- Add an arbitrary affine gauge to an observation. -/
def addAffineGauge
    (mesh x : ℕ → K) (a b : K) (k : ℕ) : K :=
  x k + affineOnMesh a b mesh k

/-- Adding an affine gauge shifts every divided slope by the same constant. -/
theorem dividedSlope_addAffineGauge
    (mesh x : ℕ → K) (a b : K) (k : ℕ)
    (hgap : mesh (k + 1) - mesh k ≠ 0) :
    dividedSlope mesh (addAffineGauge mesh x a b) k =
      dividedSlope mesh x k + b := by
  unfold dividedSlope addAffineGauge affineOnMesh
  field_simp [hgap]
  ring

/-- Divided curvature is invariant under additive affine gauges. -/
theorem dividedCurvature_addAffineGauge
    (mesh x : ℕ → K) (a b : K) (k : ℕ)
    (hgap₀ : mesh (k + 1) - mesh k ≠ 0)
    (hgap₁ : mesh (k + 2) - mesh (k + 1) ≠ 0) :
    dividedCurvature mesh (addAffineGauge mesh x a b) k =
      dividedCurvature mesh x k := by
  unfold dividedCurvature
  rw [dividedSlope_addAffineGauge mesh x a b (k + 1) hgap₁,
    dividedSlope_addAffineGauge mesh x a b k hgap₀]
  ring

/-- Additive observation with an affine gauge and a shared structural channel. -/
def additiveObservation
    (alpha beta : K) (mesh shared : ℕ → K) (k : ℕ) : K :=
  alpha - beta * mesh k + shared k

/-- Subtracting two observations with the same structure leaves an affine
cross-gauge quotient. -/
theorem additiveObservation_difference
    (alpha₁ beta₁ alpha₂ beta₂ : K)
    (mesh shared : ℕ → K) (k : ℕ) :
    additiveObservation alpha₁ beta₁ mesh shared k -
        additiveObservation alpha₂ beta₂ mesh shared k =
      (alpha₁ - alpha₂) + (beta₂ - beta₁) * mesh k := by
  unfold additiveObservation
  ring

/-- The cross-gauge quotient of two observations sharing one structural
channel has zero nonuniform divided curvature. -/
theorem dividedCurvature_crossGaugeDifference
    (alpha₁ beta₁ alpha₂ beta₂ : K)
    (mesh shared : ℕ → K) (k : ℕ)
    (hgap₀ : mesh (k + 1) - mesh k ≠ 0)
    (hgap₁ : mesh (k + 2) - mesh (k + 1) ≠ 0) :
    dividedCurvature mesh
        (fun n =>
          additiveObservation alpha₁ beta₁ mesh shared n -
            additiveObservation alpha₂ beta₂ mesh shared n) k = 0 := by
  have hfun :
      (fun n =>
        additiveObservation alpha₁ beta₁ mesh shared n -
          additiveObservation alpha₂ beta₂ mesh shared n) =
        affineOnMesh (alpha₁ - alpha₂) (beta₂ - beta₁) mesh := by
    funext n
    exact additiveObservation_difference
      alpha₁ beta₁ alpha₂ beta₂ mesh shared n
  rw [hfun]
  exact dividedCurvature_affine mesh
    (alpha₁ - alpha₂) (beta₂ - beta₁) k hgap₀ hgap₁

/-- Multiplying divided curvature by its mesh span recovers the exact slope
increment stored by the recurrence. -/
theorem dividedCurvature_to_slopeIncrement
    (mesh x : ℕ → K) (k : ℕ)
    (h2 : (2 : K) ≠ 0)
    (hspan : mesh (k + 2) - mesh k ≠ 0) :
    ((mesh (k + 2) - mesh k) / 2) *
        dividedCurvature mesh x k =
      dividedSlope mesh x (k + 1) - dividedSlope mesh x k := by
  unfold dividedCurvature
  field_simp [h2, hspan]

/-- Value, initial divided slope, and all divided curvatures on a mesh. -/
@[ext]
structure NonuniformPassport (K : Type*) where
  value0 : K
  initialSlope : K
  curvature : ℕ → K

namespace NonuniformPassport

variable (K)

/-- Encode an observation on a supplied mesh. -/
def ofObservation
    (mesh x : ℕ → K) : NonuniformPassport K where
  value0 := x 0
  initialSlope := dividedSlope mesh x 0
  curvature := dividedCurvature mesh x

variable {K}

/-- Reconstruct the divided slope at coordinate `n`. -/
def reconstructedSlope
    (mesh : ℕ → K) (p : NonuniformPassport K) (n : ℕ) : K :=
  p.initialSlope +
    ∑ j ∈ Finset.range n,
      ((mesh (j + 2) - mesh j) / 2) * p.curvature j

/-- Reconstruct the sampled observation recursively from its passport. -/
def reconstruct
    (mesh : ℕ → K) (p : NonuniformPassport K) : ℕ → K
  | 0 => p.value0
  | n + 1 =>
      reconstruct mesh p n +
        (mesh (n + 1) - mesh n) * reconstructedSlope mesh p n

/-- The curvature ledger telescopes to the actual divided slope. -/
theorem initialSlope_add_curvature_sum
    (mesh x : ℕ → K)
    (h2 : (2 : K) ≠ 0)
    (hspan : ∀ k, mesh (k + 2) - mesh k ≠ 0)
    (n : ℕ) :
    dividedSlope mesh x 0 +
        ∑ j ∈ Finset.range n,
          ((mesh (j + 2) - mesh j) / 2) *
            dividedCurvature mesh x j =
      dividedSlope mesh x n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih,
        dividedCurvature_to_slopeIncrement mesh x n h2 (hspan n)]
      ring

/-- Encoding followed by slope reconstruction recovers the exact divided
slope. -/
theorem reconstructedSlope_ofObservation
    (mesh x : ℕ → K)
    (h2 : (2 : K) ≠ 0)
    (hspan : ∀ k, mesh (k + 2) - mesh k ≠ 0)
    (n : ℕ) :
    reconstructedSlope mesh (ofObservation K mesh x) n =
      dividedSlope mesh x n := by
  unfold reconstructedSlope ofObservation
  exact initialSlope_add_curvature_sum mesh x h2 hspan n

/-- The nonuniform passport reconstructs every sampled coordinate exactly. -/
theorem reconstruct_ofObservation
    (mesh x : ℕ → K)
    (hgap : ∀ k, mesh (k + 1) - mesh k ≠ 0)
    (hspan : ∀ k, mesh (k + 2) - mesh k ≠ 0)
    (h2 : (2 : K) ≠ 0)
    (n : ℕ) :
    reconstruct mesh (ofObservation K mesh x) n = x n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [reconstruct, ih,
        reconstructedSlope_ofObservation mesh x h2 hspan n]
      unfold dividedSlope
      field_simp [hgap n]
      ring

/-- On a nondegenerate mesh, the nonuniform passport is a complete invariant
of the sampled observation. -/
theorem ofObservation_injective
    (mesh : ℕ → K)
    (hgap : ∀ k, mesh (k + 1) - mesh k ≠ 0)
    (hspan : ∀ k, mesh (k + 2) - mesh k ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    Function.Injective (ofObservation K mesh) := by
  intro x y hxy
  funext n
  calc
    x n = reconstruct mesh (ofObservation K mesh x) n :=
      (reconstruct_ofObservation mesh x hgap hspan h2 n).symm
    _ = reconstruct mesh (ofObservation K mesh y) n := by
      rw [hxy]
    _ = y n :=
      reconstruct_ofObservation mesh y hgap hspan h2 n

/-- Zero divided curvature is equivalent to belonging to the affine return
channel determined by the first value and first divided slope. -/
theorem eq_affineOnMesh_of_dividedCurvature_eq_zero
    (mesh x : ℕ → K)
    (hgap : ∀ k, mesh (k + 1) - mesh k ≠ 0)
    (hspan : ∀ k, mesh (k + 2) - mesh k ≠ 0)
    (h2 : (2 : K) ≠ 0)
    (hcurvature : ∀ k, dividedCurvature mesh x k = 0) :
    x =
      affineOnMesh
        (x 0 - dividedSlope mesh x 0 * mesh 0)
        (dividedSlope mesh x 0) mesh := by
  apply ofObservation_injective mesh hgap hspan h2
  apply NonuniformPassport.ext
  · dsimp [ofObservation, affineOnMesh]
    ring
  · dsimp [ofObservation]
    symm
    exact dividedSlope_affine mesh
      (x 0 - dividedSlope mesh x 0 * mesh 0)
      (dividedSlope mesh x 0) 0 (hgap 0)
  · funext k
    dsimp [ofObservation]
    rw [hcurvature k,
      dividedCurvature_affine mesh
        (x 0 - dividedSlope mesh x 0 * mesh 0)
        (dividedSlope mesh x 0) k (hgap k) (hgap (k + 1))]

end NonuniformPassport

end

end ThermalValvePassport
