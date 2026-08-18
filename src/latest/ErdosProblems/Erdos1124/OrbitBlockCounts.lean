/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.OrbitBlocks
import ErdosProblems.Erdos1124.TorusAction
import ErdosProblems.Erdos1124.RoomBounds

/-!
# Orbit-block counts and torus discrepancy

This file identifies every canonical lattice block from `OrbitBlocks.lean`
with a negatively oriented orbit cube from `TorusAction.lean`.  It then
packages normalized discrepancy estimates into the uniform room inequalities
needed by the bounded-flow matching argument.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Erdos1124.OrbitBlockCounts

noncomputable section

open TorusAction OrbitBlocks

/-- Coordinatewise reversal of a finite cube. -/
def reverseOffset {d M : ℕ} : (Fin d → Fin M) ≃ (Fin d → Fin M) where
  toFun q i := Fin.rev (q i)
  invFun q i := Fin.rev (q i)
  left_inv q := funext fun i ↦ Fin.rev_involutive (q i)
  right_inv q := funext fun i ↦ Fin.rev_involutive (q i)

/-- The top corner of the finite remainder cube. -/
def topOffset {d M : ℕ} [NeZero M] : Fin d → Fin M :=
  fun _ ↦ Fin.rev 0

lemma neg_cubeIndex_add_topCoordinate {d M : ℕ} [NeZero M]
    (c : OrbitBlocks.Lattice d) (q : Fin d → Fin M) :
    -Flow.cubeIndex q +
        (latticeDivMod (d := d) M).symm (c, topOffset (d := d) (M := M)) =
      (latticeDivMod (d := d) M).symm
        (c, reverseOffset (d := d) (M := M) q) := by
  funext j
  simp [Flow.cubeIndex, latticeDivMod, Int.divModEquiv, topOffset,
    reverseOffset, Fin.val_rev]
  omega

variable {d k : ℕ} (u : Fin d → Torus k)

/-- Injectivity of torus displacement is pointwise freeness of its additive
action. -/
lemma freeAction_of_free (hu : Free u) :
    letI := torusAddAction u
    FreeAction (d := d) (X := Torus k) := by
  letI := torusAddAction u
  intro x m n h
  apply hu
  exact add_right_cancel h

/-- The top corner of a canonical orbit block, used as the anchor of its
negatively oriented orbit cube. -/
def blockAnchor (M : ℕ) [NeZero M] :
    letI := torusAddAction u
    BlockIndex (d := d) (X := Torus k) → Torus k := by
  letI := torusAddAction u
  intro i
  exact blockPoint (d := d) M i (topOffset (d := d) (M := M))

lemma neg_cube_vadd_blockAnchor (M : ℕ) [NeZero M] :
    letI := torusAddAction u
    ∀ (i : BlockIndex (d := d) (X := Torus k)) (q : Fin d → Fin M),
    (-Flow.cubeIndex q) +ᵥ blockAnchor u M i =
      blockPoint (d := d) M i (reverseOffset (d := d) (M := M) q) := by
  letI := torusAddAction u
  intro i q
  rw [blockAnchor, blockPoint, ← add_vadd]
  rw [neg_cubeIndex_add_topCoordinate]
  rfl

/-- The points of `E` in a canonical block are counted by the negative orbit
cube anchored at that block's top corner. -/
lemma card_pointsInBlock_eq_cubeCount (hu : Free u) (E : Set (Torus k))
    (M : ℕ) [NeZero M] : letI := torusAddAction u
    ∀ i : BlockIndex (d := d) (X := Torus k),
    (pointsInBlock (d := d) E M i).card =
      cubeCount u E M (blockAnchor u M i) := by
  letI := torusAddAction u
  intro i
  classical
  letI : DecidableEq (Fin d → Fin M) := Fintype.decidablePiFintype
  rw [pointsInBlock, Finset.card_subtype, Finset.card_filter]
  have hblocks : blockPoints (d := d) M i =
      Finset.univ.image (blockPoint (d := d) M i) := by
    ext x
    simp [blockPoints]
  rw [hblocks]
  have hinj : Set.InjOn (blockPoint (d := d) M i)
      (Finset.univ : Finset (Fin d → Fin M)) :=
    Set.injOn_of_injective
      (blockPoint_injective (d := d) (freeAction_of_free u hu) M i)
  rw [Finset.sum_image hinj]
  unfold cubeCount
  rw [← (reverseOffset (d := d) (M := M)).sum_comp]
  apply Finset.sum_congr rfl
  intro q hq
  rw [neg_cube_vadd_blockAnchor]

/-- A normalized count estimate at the anchor of one canonical orbit block
gives the exact room inequality used by the bounded-block-flow argument. -/
theorem room_of_cubeDensity_error (hu : Free u) (E : Set (Torus k))
    (M : ℕ) [NeZero M] (i : letI := torusAddAction u
      BlockIndex (d := d) (X := Torus k))
    (mu error : ℝ) (D b : ℕ) (hd : 0 < d)
    (hdensity :
      |cubeDensity u E M (blockAnchor u M i) - mu| ≤ error)
    (herror : error ≤ mu / 2)
    (hcapacity : ((D * b : ℕ) : ℝ) ≤ (mu / 2) * M) :
    letI := torusAddAction u
    D * (b * M ^ (d - 1)) ≤
      (pointsInBlock (d := d) E M i).card := by
  letI := torusAddAction u
  rw [card_pointsInBlock_eq_cubeCount u hu E M i]
  apply RoomBounds.capacity_le_count_of_density_error hd
    (NeZero.pos M) (count := cubeCount u E M (blockAnchor u M i))
  · simpa only [cubeDensity] using hdensity
  · exact herror
  · exact hcapacity

/-- A uniform normalized density estimate supplies the room inequality in
every canonical block. -/
theorem uniform_room_of_cubeDensity_error (hu : Free u) (E : Set (Torus k))
    (M : ℕ) [NeZero M] (mu error : ℝ) (D b : ℕ) (hd : 0 < d)
    (hdensity : ∀ x : Torus k, |cubeDensity u E M x - mu| ≤ error)
    (herror : error ≤ mu / 2)
    (hcapacity : ((D * b : ℕ) : ℝ) ≤ (mu / 2) * M) :
    letI := torusAddAction u
    ∀ i : BlockIndex (d := d) (X := Torus k),
      D * (b * M ^ (d - 1)) ≤
        (pointsInBlock (d := d) E M i).card := by
  letI := torusAddAction u
  intro i
  exact room_of_cubeDensity_error u hu E M i mu error D b hd
    (hdensity _) herror hcapacity

/-- One dyadic side length works simultaneously for two sets satisfying the
same uniform normalized density estimate. -/
theorem exists_dyadic_uniform_room_pair
    (hu : Free u) (A B : Set (Torus k)) (mu C delta : ℝ) (D b : ℕ)
    (hd : 0 < d) (hmu : 0 < mu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hA : ∀ (q : ℕ) (x : Torus k),
      |cubeDensity u A (2 ^ q) x - mu| ≤
        C * (((2 ^ q : ℕ) : ℝ) ^ (-(1 + delta))))
    (hB : ∀ (q : ℕ) (x : Torus k),
      |cubeDensity u B (2 ^ q) x - mu| ≤
        C * (((2 ^ q : ℕ) : ℝ) ^ (-(1 + delta)))) :
    ∃ q : ℕ, let M : ℕ := 2 ^ q
      letI : NeZero M := inferInstance
      letI := torusAddAction u
      (∀ i : BlockIndex (d := d) (X := Torus k),
        D * (b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) A M i).card) ∧
      (∀ i : BlockIndex (d := d) (X := Torus k),
        D * (b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) B M i).card) := by
  obtain ⟨q, hroom⟩ := RoomBounds.exists_dyadic_capacity_le_count
    D b hmu hC hdelta
  refine ⟨q, ?_, ?_⟩
  · intro i
    apply hroom hd
    rw [card_pointsInBlock_eq_cubeCount u hu A (2 ^ q) i]
    simpa only [cubeDensity] using hA q (blockAnchor u (2 ^ q) i)
  · intro i
    apply hroom hd
    rw [card_pointsInBlock_eq_cubeCount u hu B (2 ^ q) i]
    simpa only [cubeDensity] using hB q (blockAnchor u (2 ^ q) i)

/-- The preceding pair theorem in the discrepancy vocabulary used by the
analytic torus-action API. -/
theorem exists_dyadic_uniform_room_pair_of_discrepancy
    (hu : Free u) (A B : Set (Torus k)) (mu C delta : ℝ) (D b : ℕ)
    (hd : 0 < d) (hmu : 0 < mu) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hA : ∀ (q : ℕ) (x : Torus k),
      discrepancy u A (2 ^ q) x ≤
        C * (((2 ^ q : ℕ) : ℝ) ^ (-(1 + delta))))
    (hB : ∀ (q : ℕ) (x : Torus k),
      discrepancy u B (2 ^ q) x ≤
        C * (((2 ^ q : ℕ) : ℝ) ^ (-(1 + delta))))
    (hmuA : (volume A).toReal = mu)
    (hmuB : (volume B).toReal = mu) :
    ∃ q : ℕ, let M : ℕ := 2 ^ q
      letI : NeZero M := inferInstance
      letI := torusAddAction u
      (∀ i : BlockIndex (d := d) (X := Torus k),
        D * (b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) A M i).card) ∧
      (∀ i : BlockIndex (d := d) (X := Torus k),
        D * (b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) B M i).card) := by
  apply exists_dyadic_uniform_room_pair u hu A B mu C delta D b hd hmu hC hdelta
  · intro q x
    rw [← hmuA]
    exact hA q x
  · intro q x
    rw [← hmuB]
    exact hB q x

end

end Erdos1124.OrbitBlockCounts
