/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.Crowd

/-!
# Canonical contiguous schedules for the crowd lemma

This file turns `Crowd.blockCrowdDataOfNatTrajectory` into the literal
contiguous block schedule needed by the outer switching argument.  An
anchor is chosen once per block and is therefore fixed at every regular
transition.  Block boundaries are explicit and have cardinality at most
`tau / blockLength`; arbitrary anchor changes there are charged to a
separate `spread + step` budget.
-/

namespace Erdos636.Crowd

noncomputable section

variable {R : Type*} [Fintype R]

/-- Number of contiguous blocks covering the times `0, ..., tau`. -/
def canonicalBlockCount (tau blockLength : ℕ) : ℕ :=
  tau / blockLength + 1

/-- The block containing time `i`.  The `min` makes the function total;
for `i ≤ tau` it is simply `i / blockLength`. -/
def canonicalBlockIndex (tau blockLength i : ℕ) : Fin (canonicalBlockCount tau blockLength) :=
  ⟨min (i / blockLength) (tau / blockLength), by
    simp only [canonicalBlockCount]
    omega⟩

/-- Local coordinate within a block. -/
def canonicalLocalTime (blockLength i : ℕ) : ℕ := i % blockLength

/-- Convert a block and local coordinate back to global time. -/
def canonicalGlobalTime {tau : ℕ} (blockLength : ℕ)
    (q : Fin (canonicalBlockCount tau blockLength)) (t : ℕ) : ℕ :=
  (q : ℕ) * blockLength + t

/-- Last local time belonging to a block. -/
def canonicalBlockLast (tau blockLength : ℕ)
    (q : Fin (canonicalBlockCount tau blockLength)) : ℕ :=
  min (blockLength - 1) (tau - (q : ℕ) * blockLength)

/-- Transitions `i → i+1` at which a new block starts. -/
def canonicalBoundary (tau blockLength : ℕ) : Finset ℕ :=
  (Finset.range (tau / blockLength)).image fun q ↦ (q + 1) * blockLength - 1

@[simp] lemma canonicalBlockIndex_val_of_le {tau blockLength i : ℕ}
    (hi : i ≤ tau) :
    (canonicalBlockIndex tau blockLength i : ℕ) = i / blockLength := by
  simp only [canonicalBlockIndex, Fin.val_mk]
  rw [min_eq_left]
  exact Nat.div_le_div_right hi

lemma canonicalLocalTime_le_last {tau blockLength i : ℕ}
    (hblock : 0 < blockLength) (hi : i ≤ tau) :
    canonicalLocalTime blockLength i ≤
      canonicalBlockLast tau blockLength (canonicalBlockIndex tau blockLength i) := by
  have hmod : i % blockLength < blockLength := Nat.mod_lt _ hblock
  have hmul : i / blockLength * blockLength ≤ i := Nat.div_mul_le_self i blockLength
  have hdecomp := Nat.div_add_mod i blockLength
  have hdecomp' : i / blockLength * blockLength + i % blockLength = i := by
    simpa [Nat.mul_comm] using hdecomp
  rw [canonicalBlockLast, canonicalBlockIndex_val_of_le hi, canonicalLocalTime]
  apply le_min
  · omega
  · omega

lemma canonicalGlobalTime_index_local {tau blockLength i : ℕ}
    (hi : i ≤ tau) :
    canonicalGlobalTime blockLength (canonicalBlockIndex tau blockLength i)
      (canonicalLocalTime blockLength i) = i := by
  rw [canonicalGlobalTime, canonicalBlockIndex_val_of_le hi, canonicalLocalTime]
  simpa [Nat.mul_comm] using Nat.div_add_mod i blockLength

lemma canonicalBoundary_card_le (tau blockLength : ℕ) :
    (canonicalBoundary tau blockLength).card ≤ tau / blockLength := by
  rw [canonicalBoundary]
  exact Finset.card_image_le.trans_eq (Finset.card_range _)

lemma canonicalBoundary_subset_range {tau blockLength : ℕ}
    (hblock : 0 < blockLength) :
    canonicalBoundary tau blockLength ⊆ Finset.range tau := by
  intro i hi
  rw [canonicalBoundary, Finset.mem_image] at hi
  rcases hi with ⟨q, hq, rfl⟩
  rw [Finset.mem_range] at hq ⊢
  have hqle : q + 1 ≤ tau / blockLength := by omega
  have hmul : (q + 1) * blockLength ≤ tau :=
    (Nat.le_div_iff_mul_le hblock).mp hqle
  have hprod : 0 < (q + 1) * blockLength := Nat.mul_pos (by omega) hblock
  omega

lemma canonicalBoundary_of_dvd {tau blockLength i : ℕ}
    (hblock : 0 < blockLength) (hi : i < tau)
    (hdvd : blockLength ∣ i + 1) :
    i ∈ canonicalBoundary tau blockLength := by
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    simp at hk
  have hkle : k ≤ tau / blockLength := by
    apply (Nat.le_div_iff_mul_le hblock).mpr
    rw [Nat.mul_comm, ← hk]
    omega
  rw [canonicalBoundary, Finset.mem_image]
  refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
  have hpred : k - 1 + 1 = k := by omega
  rw [hpred, Nat.mul_comm, ← hk]
  omega

/-- Off the explicit boundary set, the quotient block index is unchanged. -/
lemma div_succ_eq_of_not_mem_boundary {tau blockLength i : ℕ}
    (hblock : 0 < blockLength) (hi : i < tau)
    (hiBoundary : i ∉ canonicalBoundary tau blockLength) :
    (i + 1) / blockLength = i / blockLength := by
  have hnvd : ¬ blockLength ∣ i + 1 := fun hdvd ↦
    hiBoundary (canonicalBoundary_of_dvd hblock hi hdvd)
  exact Nat.succ_div_of_not_dvd hnvd

lemma canonicalBlockIndex_succ_eq_of_not_mem_boundary
    {tau blockLength i : ℕ} (hblock : 0 < blockLength) (hi : i < tau)
    (hiBoundary : i ∉ canonicalBoundary tau blockLength) :
    canonicalBlockIndex tau blockLength (i + 1) =
      canonicalBlockIndex tau blockLength i := by
  apply Fin.ext
  rw [canonicalBlockIndex_val_of_le (by omega), canonicalBlockIndex_val_of_le hi.le]
  exact div_succ_eq_of_not_mem_boundary hblock hi hiBoundary

/-- The complete output of the finite crowd schedule.  `anchorAt` is fixed
on each block.  `crowdAt i` is the retained crowd at global time `i`.
Regular and boundary motion estimates are recorded separately. -/
structure CanonicalNatCrowdSchedule
    (tau blockLength threshold window step spread : ℕ)
    (value : ℕ → R → ℕ) where
  blockLength_pos : 0 < blockLength
  anchorBlock : Fin (canonicalBlockCount tau blockLength) → R
  crowdBlock : Fin (canonicalBlockCount tau blockLength) → ℕ → Finset R
  anchorAt : ℕ → R := fun i ↦ anchorBlock (canonicalBlockIndex tau blockLength i)
  crowdAt : ℕ → Finset R := fun i ↦
    crowdBlock (canonicalBlockIndex tau blockLength i) (canonicalLocalTime blockLength i)
  anchorAt_eq : anchorAt = fun i ↦
    anchorBlock (canonicalBlockIndex tau blockLength i)
  crowdAt_eq : crowdAt = fun i ↦
    crowdBlock (canonicalBlockIndex tau blockLength i) (canonicalLocalTime blockLength i)
  crowd_large : ∀ i ≤ tau, threshold ≤ (crowdAt i).card
  crowd_near : ∀ i ≤ tau, ∀ y ∈ crowdAt i,
    Nat.dist (value i y) (value i (anchorAt i)) ≤ window
  boundary_subset : canonicalBoundary tau blockLength ⊆ Finset.range tau
  boundary_card : (canonicalBoundary tau blockLength).card ≤ tau / blockLength
  regular_motion : ∀ i < tau, i ∉ canonicalBoundary tau blockLength →
    Nat.dist (value (i + 1) (anchorAt (i + 1))) (value i (anchorAt i)) ≤ step
  boundary_motion : ∀ i ∈ canonicalBoundary tau blockLength,
    Nat.dist (value (i + 1) (anchorAt (i + 1))) (value i (anchorAt i)) ≤
      spread + step

/-- Construct a canonical contiguous crowd schedule from bounded
natural-valued trajectories.

The `controlled` and `travelBound` premises are exactly those consumed by
`blockCrowdDataOfNatTrajectory`.  The two final trajectory assumptions have
separate roles: `oneStep` controls a fixed particle at ordinary switches,
whereas `sameTimeSpread` pays for changing the block anchor at a boundary. -/
theorem exists_canonicalNatCrowdSchedule
    (tau blockLength : ℕ) (value : ℕ → R → ℕ)
    (base : Fin (canonicalBlockCount tau blockLength) → ℕ → ℕ)
    (span width threshold window stride travel step spread : ℕ)
    (hblock : 0 < blockLength) (hwidth : 0 < width) (hstride : 0 < stride)
    (controlled : ∀ q j,
      j * stride ≤ canonicalBlockLast tau blockLength q → ∀ x,
        base q j ≤ value (canonicalGlobalTime blockLength q (j * stride)) x ∧
          value (canonicalGlobalTime blockLength q (j * stride)) x < base q j + span)
    (travelBound : ∀ q t, t ≤ canonicalBlockLast tau blockLength q → ∀ x,
      Nat.dist (value (canonicalGlobalTime blockLength q t) x)
        (value (canonicalGlobalTime blockLength q ((t / stride) * stride)) x) ≤ travel)
    (hradius : width + 2 * travel ≤ window)
    (hcount : ∀ q,
      (canonicalBlockLast tau blockLength q / stride + 1) *
          natBucketCount span width * threshold < Fintype.card R)
    (oneStep : ∀ i < tau, ∀ x,
      Nat.dist (value (i + 1) x) (value i x) ≤ step)
    (sameTimeSpread : ∀ i ≤ tau, ∀ x y,
      Nat.dist (value i x) (value i y) ≤ spread) :
    Nonempty (CanonicalNatCrowdSchedule tau blockLength threshold window step spread value) := by
  classical
  let D : BlockCrowdData (Fin (canonicalBlockCount tau blockLength)) R :=
    blockCrowdDataOfNatTrajectory
      (canonicalBlockLast tau blockLength) (canonicalGlobalTime blockLength)
      value base span width threshold window stride travel hwidth hstride
      controlled travelBound hradius hcount
  obtain ⟨anchorBlock, crowdBlock, hcrowdEq, hcrowdLarge⟩ :=
    exists_block_anchors_and_crowds D
  let anchorAt : ℕ → R := fun i ↦
    anchorBlock (canonicalBlockIndex tau blockLength i)
  let crowdAt : ℕ → Finset R := fun i ↦
    crowdBlock (canonicalBlockIndex tau blockLength i) (canonicalLocalTime blockLength i)
  refine ⟨{
    blockLength_pos := hblock
    anchorBlock := anchorBlock
    crowdBlock := crowdBlock
    anchorAt := anchorAt
    crowdAt := crowdAt
    anchorAt_eq := rfl
    crowdAt_eq := rfl
    crowd_large := ?_
    crowd_near := ?_
    boundary_subset := canonicalBoundary_subset_range hblock
    boundary_card := canonicalBoundary_card_le tau blockLength
    regular_motion := ?_
    boundary_motion := ?_ }⟩
  · intro i hi
    exact hcrowdLarge (canonicalBlockIndex tau blockLength i)
      (canonicalLocalTime blockLength i) (canonicalLocalTime_le_last hblock hi)
  · intro i hi y hy
    have hy' : y ∈ D.nearby (canonicalBlockIndex tau blockLength i)
        (canonicalLocalTime blockLength i)
        (anchorBlock (canonicalBlockIndex tau blockLength i)) := by
      rw [← hcrowdEq (canonicalBlockIndex tau blockLength i)
        (canonicalLocalTime blockLength i)]
      exact hy
    change y ∈ natTrajectoryNearby (canonicalGlobalTime blockLength) value window
      (canonicalBlockIndex tau blockLength i) (canonicalLocalTime blockLength i)
      (anchorBlock (canonicalBlockIndex tau blockLength i)) at hy'
    rw [natTrajectoryNearby, Finset.mem_filter] at hy'
    simpa [anchorAt, canonicalGlobalTime_index_local hi] using hy'.2
  · intro i hi hiBoundary
    have hidx := canonicalBlockIndex_succ_eq_of_not_mem_boundary hblock hi hiBoundary
    simpa [anchorAt, hidx] using oneStep i hi (anchorBlock (canonicalBlockIndex tau blockLength i))
  · intro i hiBoundary
    have hi : i < tau := Finset.mem_range.mp
      (canonicalBoundary_subset_range hblock hiBoundary)
    calc
      Nat.dist (value (i + 1) (anchorAt (i + 1))) (value i (anchorAt i)) ≤
          Nat.dist (value (i + 1) (anchorAt (i + 1)))
              (value (i + 1) (anchorAt i)) +
            Nat.dist (value (i + 1) (anchorAt i)) (value i (anchorAt i)) :=
        Nat.dist.triangle_inequality _ _ _
      _ ≤ spread + step :=
        Nat.add_le_add (sameTimeSpread (i + 1) (by omega) _ _) (oneStep i hi _)

end

end Erdos636.Crowd
