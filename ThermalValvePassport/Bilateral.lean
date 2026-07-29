import ThermalValvePassport.CarrierCutoff

/-!
# Bilateral carrier passport

This module extends the carrier passport from natural indices to observations
on `ℤ`.  For

`x n = c * q ^ n * g n`,

the paired product removes both the global normalization and the bilateral
geometric carrier.  The paired ratio records the complementary tilt channel.
The development also supplies an additive reflection decomposition, exact
reconstruction of the natural paired channel, and a symmetric cutoff ledger.

No logarithm, square root, probability model, or physical interpretation is
used in the theorem statements.
-/

open scoped BigOperators

namespace ThermalValvePassport

noncomputable section

variable {K : Type*}

/-- Reflection of an integer-indexed sequence. -/
def reflectedSequence (x : ℤ → K) (n : ℤ) : K :=
  x (-n)

/-- Reflection is an involution. -/
@[simp] theorem reflectedSequence_reflectedSequence (x : ℤ → K) :
    reflectedSequence (reflectedSequence x) = x := by
  funext n
  simp [reflectedSequence]

variable [Field K]

/-- Bilateral geometric dressing on integer indices. -/
def bilateralDressed (c q : K) (g : ℤ → K) (n : ℤ) : K :=
  c * q ^ n * g n

/-- Multiplicative reflection-even channel, normalized at the origin. -/
def pairedProduct (x : ℤ → K) (n : ℤ) : K :=
  x n * x (-n) / (x 0) ^ 2

/-- Multiplicative reflection-ratio channel. -/
def pairedRatio (x : ℤ → K) (n : ℤ) : K :=
  x n / x (-n)

/-- Additive reflection-even component. -/
def evenChannel (x : ℤ → K) (n : ℤ) : K :=
  (x n + x (-n)) / 2

/-- Additive reflection-odd component. -/
def oddChannel (x : ℤ → K) (n : ℤ) : K :=
  (x n - x (-n)) / 2

/-- The additive even channel is reflection invariant. -/
@[simp] theorem evenChannel_neg (x : ℤ → K) (n : ℤ) :
    evenChannel x (-n) = evenChannel x n := by
  simp [evenChannel, add_comm]

/-- The additive odd channel changes sign under reflection. -/
@[simp] theorem oddChannel_neg (x : ℤ → K) (n : ℤ) :
    oddChannel x (-n) = -oddChannel x n := by
  simp [oddChannel]
  ring

/-- The even and odd channels reconstruct the observation when `2` is
invertible. -/
theorem evenChannel_add_oddChannel
    (x : ℤ → K) (n : ℤ) (h2 : (2 : K) ≠ 0) :
    evenChannel x n + oddChannel x n = x n := by
  unfold evenChannel oddChannel
  rw [← add_div]
  apply (div_eq_iff h2).2
  ring

/-- The paired product is reflection invariant. -/
@[simp] theorem pairedProduct_neg (x : ℤ → K) (n : ℤ) :
    pairedProduct x (-n) = pairedProduct x n := by
  unfold pairedProduct
  simp only [neg_neg]
  ring

/-- The paired product is normalized to one at the origin whenever the origin
is nonzero. -/
@[simp] theorem pairedProduct_zero (x : ℤ → K) (hx0 : x 0 ≠ 0) :
    pairedProduct x 0 = 1 := by
  unfold pairedProduct
  simp only [neg_zero]
  field_simp [hx0]

/-- Reciprocal integer powers cancel exactly. -/
theorem zpow_mul_reflection
    (q : K) (n : ℤ) (hq : q ≠ 0) :
    q ^ n * q ^ (-n) = 1 := by
  rw [← zpow_add₀ hq]
  simp

/-- A doubled power followed by its reflected power returns the original
power. -/
theorem zpow_double_mul_reflection
    (q : K) (n : ℤ) (hq : q ≠ 0) :
    q ^ (2 * n) * q ^ (-n) = q ^ n := by
  rw [← zpow_add₀ hq]
  congr 1
  ring

/-- The paired product removes the bilateral carrier and global scale. -/
theorem pairedProduct_bilateralDressed
    (c q : K) (g : ℤ → K) (n : ℤ)
    (hc : c ≠ 0) (hq : q ≠ 0) :
    pairedProduct (bilateralDressed c q g) n =
      g n * g (-n) / (g 0) ^ 2 := by
  by_cases hg0 : g 0 = 0
  · simp [pairedProduct, bilateralDressed, hg0]
  · unfold pairedProduct bilateralDressed
    simp only [zpow_zero, mul_one]
    have hpair : q ^ n * q ^ (-n) = (1 : K) :=
      zpow_mul_reflection q n hq
    have hnum :
        (c * q ^ n * g n) * (c * q ^ (-n) * g (-n)) =
          c ^ 2 * (g n * g (-n)) := by
      calc
        (c * q ^ n * g n) * (c * q ^ (-n) * g (-n)) =
            c ^ 2 * (q ^ n * q ^ (-n)) * (g n * g (-n)) := by
              ring
        _ = c ^ 2 * (g n * g (-n)) := by
              rw [hpair]
              ring
    rw [hnum]
    have hden : (c * g 0) ^ 2 = c ^ 2 * (g 0) ^ 2 := by
      ring
    rw [hden]
    field_simp [hc, hg0]

/-- Redressing by any second nonzero scale and fugacity preserves the paired
product. -/
theorem pairedProduct_invariant_under_redressing
    (d r : K) (x : ℤ → K) (n : ℤ)
    (hd : d ≠ 0) (hr : r ≠ 0) :
    pairedProduct (bilateralDressed d r x) n = pairedProduct x n := by
  simpa [pairedProduct] using
    (pairedProduct_bilateralDressed d r x n hd hr)

/-- The general paired-ratio law separates the bilateral carrier from the
structural reflection ratio. -/
theorem pairedRatio_bilateralDressed
    (c q : K) (g : ℤ → K) (n : ℤ)
    (hc : c ≠ 0) (hq : q ≠ 0) (hgneg : g (-n) ≠ 0) :
    pairedRatio (bilateralDressed c q g) n =
      q ^ (2 * n) * (g n / g (-n)) := by
  unfold pairedRatio bilateralDressed
  have hqneg : q ^ (-n) ≠ 0 := zpow_ne_zero _ hq
  have hden : c * q ^ (-n) * g (-n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc hqneg) hgneg
  apply (div_eq_iff hden).2
  have hpow : q ^ (2 * n) * q ^ (-n) = q ^ n :=
    zpow_double_mul_reflection q n hq
  calc
    c * q ^ n * g n =
        c * (q ^ (2 * n) * q ^ (-n)) * g n := by
          rw [hpow]
    _ = (q ^ (2 * n) * (g n / g (-n))) *
          (c * q ^ (-n) * g (-n)) := by
            field_simp [hgneg]

/-- Under reflection symmetry of the structural channel, the ratio recovers
the doubled bilateral carrier exactly. -/
theorem pairedRatio_bilateralDressed_of_symmetric
    (c q : K) (g : ℤ → K) (n : ℤ)
    (hc : c ≠ 0) (hq : q ≠ 0)
    (hgneg : g (-n) ≠ 0) (hsymm : g n = g (-n)) :
    pairedRatio (bilateralDressed c q g) n = q ^ (2 * n) := by
  rw [pairedRatio_bilateralDressed c q g n hc hq hgneg, hsymm]
  simp [hgneg]

/-- Redressing multiplies the ratio channel by the exact doubled carrier. -/
theorem pairedRatio_under_redressing
    (d r : K) (x : ℤ → K) (n : ℤ)
    (hd : d ≠ 0) (hr : r ≠ 0) (hxneg : x (-n) ≠ 0) :
    pairedRatio (bilateralDressed d r x) n =
      r ^ (2 * n) * pairedRatio x n := by
  simpa [pairedRatio] using
    (pairedRatio_bilateralDressed d r x n hd hr hxneg)

/-- Paired product restricted to nonnegative indices. -/
def pairedProductNat (x : ℤ → K) (k : ℕ) : K :=
  pairedProduct x (k : ℤ)

/-- Canonical structural paired product restricted to nonnegative indices. -/
def pairedStructuralProduct (g : ℤ → K) (k : ℕ) : K :=
  g (k : ℤ) * g (-(k : ℤ)) / (g 0) ^ 2

/-- Paired curvature on the natural half-axis. -/
def pairedCurvature (x : ℤ → K) (k : ℕ) : K :=
  secondDifference (pairedProductNat x) k

/-- The full natural paired-product channel is carrier invariant. -/
theorem pairedProductNat_bilateralDressed
    (c q : K) (g : ℤ → K)
    (hc : c ≠ 0) (hq : q ≠ 0) :
    pairedProductNat (bilateralDressed c q g) =
      pairedStructuralProduct g := by
  funext k
  exact pairedProduct_bilateralDressed c q g (k : ℤ) hc hq

/-- Paired curvature is exactly the curvature of the carrier-free structural
product. -/
theorem pairedCurvature_bilateralDressed
    (c q : K) (g : ℤ → K)
    (hc : c ≠ 0) (hq : q ≠ 0) :
    pairedCurvature (bilateralDressed c q g) =
      secondDifference (pairedStructuralProduct g) := by
  unfold pairedCurvature
  rw [pairedProductNat_bilateralDressed c q g hc hq]

/-- Exact Green reconstruction of the natural paired-product sequence. -/
def pairedReconstruction (x : ℤ → K) (n : ℕ) : K :=
  pairedProductNat x 0 +
    (n : K) * (pairedProductNat x 1 - pairedProductNat x 0) +
    ∑ j ∈ Finset.range n,
      ((n - 1 - j : ℕ) : K) * pairedCurvature x j

/-- Initial paired values and all paired curvatures reconstruct every paired
coordinate. -/
theorem pairedReconstruction_exact (x : ℤ → K) (n : ℕ) :
    pairedReconstruction x n = pairedProductNat x n := by
  unfold pairedReconstruction pairedCurvature
  exact (secondDifferenceReconstruction (pairedProductNat x) n).symm

/-- Symmetric cutoff on integer indices. -/
def symmetricTruncate (M : ℕ) (x : ℤ → K) (n : ℤ) : K :=
  if n.natAbs ≤ M then x n else 0

/-- Tail complementary to the symmetric cutoff. -/
def symmetricTail (M : ℕ) (x : ℤ → K) (n : ℤ) : K :=
  if M < n.natAbs then x n else 0

/-- Inside the symmetric window, truncation is the identity. -/
theorem symmetricTruncate_inside
    (M : ℕ) (x : ℤ → K) (n : ℤ) (h : n.natAbs ≤ M) :
    symmetricTruncate M x n = x n := by
  simp [symmetricTruncate, h]

/-- Outside the symmetric window, truncation vanishes. -/
theorem symmetricTruncate_outside
    (M : ℕ) (x : ℤ → K) (n : ℤ) (h : M < n.natAbs) :
    symmetricTruncate M x n = 0 := by
  simp [symmetricTruncate, Nat.not_le.mpr h]

/-- Symmetric truncation commutes with reflection. -/
theorem symmetricTruncate_reflection
    (M : ℕ) (x : ℤ → K) (n : ℤ) :
    symmetricTruncate M x (-n) =
      symmetricTruncate M (reflectedSequence x) n := by
  simp [symmetricTruncate, reflectedSequence, Int.natAbs_neg]

/-- Prefix and omitted tail form an exact pointwise ledger. -/
theorem symmetricTruncate_add_tail
    (M : ℕ) (x : ℤ → K) (n : ℤ) :
    symmetricTruncate M x n + symmetricTail M x n = x n := by
  by_cases h : n.natAbs ≤ M
  · have hnot : ¬ M < n.natAbs := Nat.not_lt.mpr h
    simp [symmetricTruncate, symmetricTail, h, hnot]
  · have hlt : M < n.natAbs := Nat.lt_of_not_ge h
    simp [symmetricTruncate, symmetricTail, h, hlt]

/-- Functional form of the symmetric prefix-tail ledger. -/
theorem symmetricDecomposition (M : ℕ) (x : ℤ → K) :
    (fun n => symmetricTruncate M x n + symmetricTail M x n) = x := by
  funext n
  exact symmetricTruncate_add_tail M x n

/-- Symmetric truncation is idempotent. -/
theorem symmetricTruncate_idempotent (M : ℕ) (x : ℤ → K) :
    symmetricTruncate M (symmetricTruncate M x) =
      symmetricTruncate M x := by
  funext n
  by_cases h : n.natAbs ≤ M
  · simp [symmetricTruncate, h]
  · simp [symmetricTruncate, h]

/-- The support of a symmetrically truncated sequence lies inside the declared
integer window. -/
theorem symmetricTruncate_support_subset
    (M : ℕ) (x : ℤ → K) :
    Function.support (symmetricTruncate M x) ⊆
      {n : ℤ | n.natAbs ≤ M} := by
  intro n hn
  change symmetricTruncate M x n ≠ 0 at hn
  by_contra hout
  have hlt : M < n.natAbs := Nat.lt_of_not_ge hout
  exact hn (symmetricTruncate_outside M x n hlt)

/-- A symmetric cutoff either preserves an entire reflected pair or removes
that pair entirely. -/
theorem pairedProduct_symmetricTruncate
    (M : ℕ) (x : ℤ → K) (n : ℤ) :
    pairedProduct (symmetricTruncate M x) n =
      if n.natAbs ≤ M then pairedProduct x n else 0 := by
  by_cases h : n.natAbs ≤ M
  · simp [pairedProduct, symmetricTruncate, h, Int.natAbs_neg]
  · simp [pairedProduct, symmetricTruncate, h, Int.natAbs_neg]

/-- On the natural paired channel, a radius-`M` symmetric integer cutoff is
the ordinary prefix cutoff at `M + 1`. -/
theorem pairedProductNat_symmetricTruncate
    (M : ℕ) (x : ℤ → K) :
    pairedProductNat (symmetricTruncate M x) =
      truncate (M + 1) (pairedProductNat x) := by
  funext k
  unfold pairedProductNat truncate
  by_cases hk : k ≤ M
  · have hlt : k < M + 1 := by omega
    simp [pairedProduct_symmetricTruncate, hk, hlt]
  · have hnlt : ¬ k < M + 1 := by omega
    simp [pairedProduct_symmetricTruncate, hk, hnlt]

/-- Finite observed mass in the nonnegative paired channel. -/
def pairedPrefixSum (x : ℤ → K) (M : ℕ) : K :=
  ∑ k ∈ Finset.range (M + 1), pairedProductNat x k

/-- Finite omitted paired tail between radii `M` and `L`. -/
def pairedTailSum (x : ℤ → K) (M L : ℕ) : K :=
  ∑ k ∈ Finset.Ico (M + 1) (L + 1), pairedProductNat x k

/-- Exact finite ledger: a larger paired window is the observed prefix plus
the explicitly indexed omitted tail. -/
theorem pairedPrefixSum_add_pairedTailSum
    (x : ℤ → K) (M L : ℕ) (hML : M ≤ L) :
    pairedPrefixSum x M + pairedTailSum x M L =
      pairedPrefixSum x L := by
  unfold pairedPrefixSum pairedTailSum
  exact Finset.sum_range_add_sum_Ico
    (f := pairedProductNat x) (by omega)

/-- Curvature/cutoff commutator of the natural paired-product channel. -/
def pairedCurvatureCutoffCommutator
    (M : ℕ) (x : ℤ → K) (k : ℕ) : K :=
  carrierCutoffCommutator (fun _ => 1) M (pairedProductNat x) k

/-- The unit carrier bracket is the ordinary second difference, as an
equality of operators. -/
theorem carrierBracket_one (x : ℕ → K) :
    carrierBracket (fun _ => (1 : K)) x = secondDifference x := by
  funext k
  simp [carrierBracket, secondDifference]

/-- The paired commutator is exactly the ordinary second-difference cutoff
commutator. -/
theorem pairedCurvatureCutoffCommutator_eq
    (M : ℕ) (x : ℤ → K) (k : ℕ) :
    pairedCurvatureCutoffCommutator M x k =
      secondDifference (truncate M (pairedProductNat x)) k -
        truncate M (secondDifference (pairedProductNat x)) k := by
  unfold pairedCurvatureCutoffCommutator carrierCutoffCommutator
  rw [carrierBracket_one, carrierBracket_one]

/-- First exact boundary value of the paired-curvature cutoff defect. -/
theorem pairedCurvatureCutoffCommutator_firstBoundary
    (x : ℤ → K) (k : ℕ) :
    pairedCurvatureCutoffCommutator (k + 2) x k =
      -pairedProductNat x (k + 2) := by
  simpa [pairedCurvatureCutoffCommutator] using
    (carrierCutoffCommutator_firstBoundary
      (K := K) (fun _ => 1) (pairedProductNat x) k)

/-- Second exact boundary value of the paired-curvature cutoff defect. -/
theorem pairedCurvatureCutoffCommutator_secondBoundary
    (x : ℤ → K) (k : ℕ) :
    pairedCurvatureCutoffCommutator (k + 2) x (k + 1) =
      2 * pairedProductNat x (k + 2) -
        pairedProductNat x (k + 3) := by
  simpa [pairedCurvatureCutoffCommutator] using
    (carrierCutoffCommutator_secondBoundary
      (K := K) (fun _ => 1) (pairedProductNat x) k)

/-- The paired-curvature cutoff defect is confined to the last two stencil
positions. -/
theorem pairedCurvatureCutoffCommutator_support_subset
    (x : ℤ → K) (k : ℕ) :
    Function.support
        (pairedCurvatureCutoffCommutator (k + 2) x) ⊆
      ({k, k + 1} : Set ℕ) := by
  simpa [pairedCurvatureCutoffCommutator] using
    (carrierCutoffCommutator_support_subset
      (K := K) (fun _ => 1) (pairedProductNat x) k)

end

end ThermalValvePassport
