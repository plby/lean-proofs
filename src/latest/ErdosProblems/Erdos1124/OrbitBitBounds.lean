/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.OrbitBlocks
import ErdosProblems.Erdos1124.TorusAction

/-!
# Uniform bounds for canonical orbit blocks

This file supplies the geometric estimates for the canonical side-`M`
blocks of a free `ℤ^d`-orbit.  A bit move changes every coarse coordinate by
at most one, so the block graph has degree at most `3^d`.  Moreover, a move
which leaves a block must start on a coordinate face; this gives the
boundary-order block-flow estimate.
-/

open Function Set
open scoped BigOperators

namespace Erdos1124.OrbitBitBounds

noncomputable section

open OrbitBlocks

abbrev Lattice (d : ℕ) := Flow.Lattice d

private lemma divMod_add_bit {M : ℕ} [NeZero M]
    (k : ℤ) (q : Fin M) (g : Fin 2) :
    ((Int.divModEquiv M)
      ((Int.divModEquiv M).symm (k, q) + (g : ℕ))).1 = k ∨
    ((Int.divModEquiv M)
      ((Int.divModEquiv M).symm (k, q) + (g : ℕ))).1 = k + 1 := by
  change (k * (M : ℤ) + (q : ℕ) + (g : ℕ)) / (M : ℤ) = k ∨
    (k * (M : ℤ) + (q : ℕ) + (g : ℕ)) / (M : ℤ) = k + 1
  have hdvd : (M : ℤ) ∣ k * (M : ℤ) := ⟨k, by ring⟩
  have hrw : (k * (M : ℤ) + (q : ℕ) + (g : ℕ)) / (M : ℤ) =
      k + ((((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) / (M : ℤ)) := by
    rw [show k * (M : ℤ) + (q : ℕ) + (g : ℕ) =
      k * (M : ℤ) + (((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) by ring,
      Int.add_ediv_of_dvd_left hdvd]
    have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [show k * (M : ℤ) = (M : ℤ) * k by ring,
      Int.mul_ediv_cancel_left k hM0]
  rw [hrw]
  have hM : 0 < (M : ℤ) := by exact_mod_cast NeZero.pos M
  have hlt : ((q : ℕ) : ℤ) + ((g : ℕ) : ℤ) < 2 * (M : ℤ) := by
    have hq := q.isLt
    have hg := g.isLt
    omega
  have hlo : 0 ≤ (((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) / (M : ℤ) :=
    Int.ediv_nonneg (by omega) (by omega)
  have hhi : (((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) / (M : ℤ) < 2 :=
    Int.ediv_lt_of_lt_mul hM (by simpa [mul_comm] using hlt)
  omega

private lemma divMod_sub_bit {M : ℕ} [NeZero M]
    (k : ℤ) (q : Fin M) (g : Fin 2) :
    ((Int.divModEquiv M)
      ((Int.divModEquiv M).symm (k, q) - (g : ℕ))).1 = k ∨
    ((Int.divModEquiv M)
      ((Int.divModEquiv M).symm (k, q) - (g : ℕ))).1 = k - 1 := by
  change (k * (M : ℤ) + (q : ℕ) - (g : ℕ)) / (M : ℤ) = k ∨
    (k * (M : ℤ) + (q : ℕ) - (g : ℕ)) / (M : ℤ) = k - 1
  have hdvd : (M : ℤ) ∣ k * (M : ℤ) := ⟨k, by ring⟩
  have hrw : (k * (M : ℤ) + (q : ℕ) - (g : ℕ)) / (M : ℤ) =
      k + ((((q : ℕ) : ℤ) - ((g : ℕ) : ℤ)) / (M : ℤ)) := by
    rw [show k * (M : ℤ) + (q : ℕ) - (g : ℕ) =
      k * (M : ℤ) + (((q : ℕ) : ℤ) - ((g : ℕ) : ℤ)) by ring,
      Int.add_ediv_of_dvd_left hdvd]
    have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [show k * (M : ℤ) = (M : ℤ) * k by ring,
      Int.mul_ediv_cancel_left k hM0]
  rw [hrw]
  have hM : 0 < (M : ℤ) := by exact_mod_cast NeZero.pos M
  have hlo : -1 ≤
      ((((q : ℕ) : ℤ) - ((g : ℕ) : ℤ)) / (M : ℤ)) := by
    rw [Int.le_ediv_iff_mul_le hM]
    have hq := q.isLt
    have hg := g.isLt
    omega
  have hhi :
      ((((q : ℕ) : ℤ) - ((g : ℕ) : ℤ)) / (M : ℤ)) < 1 := by
    apply Int.ediv_lt_of_lt_mul hM
    have hq := q.isLt
    have hg := g.isLt
    omega
  omega

private lemma divMod_add_bit_ne_imp_eq_last {M : ℕ} [NeZero M]
    (k : ℤ) (q : Fin M) (g : Fin 2)
    (hne : ((Int.divModEquiv M)
      ((Int.divModEquiv M).symm (k, q) + (g : ℕ))).1 ≠ k) :
    (q : ℕ) = M - 1 := by
  have hother := (divMod_add_bit k q g).resolve_left hne
  change (k * (M : ℤ) + (q : ℕ) + (g : ℕ)) / (M : ℤ) = k + 1 at hother
  have hdvd : (M : ℤ) ∣ k * (M : ℤ) := ⟨k, by ring⟩
  have hrw : (k * (M : ℤ) + (q : ℕ) + (g : ℕ)) / (M : ℤ) =
      k + ((((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) / (M : ℤ)) := by
    rw [show k * (M : ℤ) + (q : ℕ) + (g : ℕ) =
      k * (M : ℤ) + (((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) by ring,
      Int.add_ediv_of_dvd_left hdvd]
    have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [show k * (M : ℤ) = (M : ℤ) * k by ring,
      Int.mul_ediv_cancel_left k hM0]
  rw [hrw] at hother
  have hM : 0 < (M : ℤ) := by exact_mod_cast NeZero.pos M
  have hquot : 1 ≤
      ((((q : ℕ) : ℤ) + ((g : ℕ) : ℤ)) / (M : ℤ)) := by omega
  have hle : (M : ℤ) ≤ ((q : ℕ) : ℤ) + ((g : ℕ) : ℤ) := by
    have hm := (Int.le_ediv_iff_mul_le hM).mp hquot
    simpa using hm
  have hq := q.isLt
  have hg := g.isLt
  omega

section Degree

variable {d : ℕ} {X : Type*} [AddAction (Lattice d) X]

/-- The `3^d` possible blocks whose coarse coordinates differ by at most one
from a given block. -/
def ternaryBlockNeighborhood
    (i : BlockIndex (d := d) (X := X)) :
    Finset (BlockIndex (d := d) (X := X)) := by
  classical
  exact Finset.univ.image fun δ : Fin d → Fin 3 ↦
    (i.1, fun k ↦ i.2 k + (δ k : ℕ) - 1)

lemma card_ternaryBlockNeighborhood_le
    (i : BlockIndex (d := d) (X := X)) :
    (ternaryBlockNeighborhood i).card ≤ 3 ^ d := by
  classical
  calc
    (ternaryBlockNeighborhood i).card ≤
        (Finset.univ : Finset (Fin d → Fin 3)).card := by
      exact Finset.card_image_le
    _ = 3 ^ d := by simp

private lemma blockOf_bitMove_mem_ternary
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X))
    (x : X) (hx : x ∈ blockPoints (d := d) M i)
    (g : Flow.BitDirection d) :
    blockOf (d := d) M (bitMoves (d := d) g x) ∈
      ternaryBlockNeighborhood i := by
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
  let n : Lattice d :=
    (latticeDivMod (d := d) M).symm (i.2, q)
  let c : Lattice d :=
    ((latticeDivMod (d := d) M) (Flow.bitVector g + n)).1
  have hc (k : Fin d) : c k = i.2 k ∨ c k = i.2 k + 1 := by
    change ((Int.divModEquiv M)
      (((g k : ℕ) : ℤ) + (Int.divModEquiv M).symm (i.2 k, q k))).1 =
        i.2 k ∨
      ((Int.divModEquiv M)
      (((g k : ℕ) : ℤ) + (Int.divModEquiv M).symm (i.2 k, q k))).1 =
        i.2 k + 1
    simpa only [add_comm] using divMod_add_bit (i.2 k) (q k) (g k)
  let δ : Fin d → Fin 3 := fun k ↦ if c k = i.2 k then 1 else 2
  rw [ternaryBlockNeighborhood, Finset.mem_image]
  refine ⟨δ, Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · simp [blockOf, bitMoves_apply, blockPoint, orbitClass_vadd]
  · funext k
    have hcoord : orbitCoord (d := d)
        (Flow.bitVector g +ᵥ blockPoint (d := d) M i q) =
        Flow.bitVector g + n := by
      rw [orbitCoord_vadd (d := d) hfree,
        orbitCoord_blockPoint (d := d) hfree]
    simp only [blockOf, bitMoves_apply]
    rw [hcoord]
    change i.2 k + ((δ k : Fin 3) : ℕ) - 1 = c k
    rcases hc k with hk | hk
    · simp [δ, hk]
    · have hne : c k ≠ i.2 k := by omega
      simp [δ, hne]
      omega

private lemma blockOf_inverseBitMove_mem_ternary
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X))
    (x : X) (hx : x ∈ blockPoints (d := d) M i)
    (g : Flow.BitDirection d) :
    blockOf (d := d) M ((bitMoves (d := d) g).symm x) ∈
      ternaryBlockNeighborhood i := by
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
  let n : Lattice d :=
    (latticeDivMod (d := d) M).symm (i.2, q)
  let c : Lattice d :=
    ((latticeDivMod (d := d) M) (-Flow.bitVector g + n)).1
  have hc (k : Fin d) : c k = i.2 k ∨ c k = i.2 k - 1 := by
    change ((Int.divModEquiv M)
      (-((g k : ℕ) : ℤ) + (Int.divModEquiv M).symm (i.2 k, q k))).1 =
        i.2 k ∨
      ((Int.divModEquiv M)
      (-((g k : ℕ) : ℤ) + (Int.divModEquiv M).symm (i.2 k, q k))).1 =
        i.2 k - 1
    simpa only [sub_eq_add_neg, add_comm] using
      divMod_sub_bit (i.2 k) (q k) (g k)
  let δ : Fin d → Fin 3 := fun k ↦ if c k = i.2 k then 1 else 0
  rw [ternaryBlockNeighborhood, Finset.mem_image]
  refine ⟨δ, Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · simp [blockOf, bitMoves_symm_apply, blockPoint, orbitClass_vadd]
  · funext k
    simp only [blockOf, bitMoves_symm_apply]
    rw [orbitCoord_vadd (d := d) hfree,
      orbitCoord_blockPoint (d := d) hfree]
    change i.2 k + ((δ k : Fin 3) : ℕ) - 1 = c k
    rcases hc k with hk | hk
    · simp [δ, hk]
    · have hne : c k ≠ i.2 k := by omega
      simp [δ, hne, hk]

lemma orbitAdjacentBlocks_subset_ternaryBlockNeighborhood
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) :
    orbitAdjacentBlocks hfree M i ⊆ ternaryBlockNeighborhood i := by
  classical
  intro j hj
  rw [orbitAdjacentBlocks, mem_adjacentBlocks_iff] at hj
  rcases hj.2 with ⟨x, hx, g, rfl⟩ | ⟨x, hx, g, rfl⟩
  · exact blockOf_bitMove_mem_ternary hfree M i x hx g
  · exact blockOf_inverseBitMove_mem_ternary hfree M i x hx g

/-- The canonical bit-move block graph has degree at most `3^d`.
The harmless loop is erased in `orbitAdjacentBlocks`, so `3^d - 1` is also
valid; the rounder bound is more convenient downstream. -/
theorem card_orbitAdjacentBlocks_le_pow_three
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) :
    (orbitAdjacentBlocks hfree M i).card ≤ 3 ^ d := by
  classical
  apply (Finset.card_le_card ?_).trans (card_ternaryBlockNeighborhood_le i)
  exact orbitAdjacentBlocks_subset_ternaryBlockNeighborhood hfree M i

end Degree

section Capacity

variable {d : ℕ} {X : Type*} [AddAction (Lattice d) X]

private lemma card_fixed_coordinate [NeZero M]
    (p : Fin d) (c : Fin M) :
    Fintype.card {q : Fin d → Fin M // q p = c} = M ^ (d - 1) := by
  let e : {q : Fin d → Fin M // q p = c} ≃
      ({i : Fin d // i ≠ p} → Fin M) := {
    toFun := fun q i ↦ q.1 i
    invFun := fun r ↦
      ⟨fun i ↦ if h : i = p then c else r ⟨i, h⟩, by simp⟩
    left_inv := by
      intro q
      ext i
      by_cases h : i = p <;> simp [h, q.2]
    right_inv := by
      intro r
      funext i
      change (if h : (i : Fin d) = p then c else r ⟨i, h⟩) = r i
      rw [dif_neg i.property]
  }
  rw [Fintype.card_congr e, Fintype.card_fun]
  simp

private noncomputable def outgoingCrossings
    (M : ℕ) [NeZero M]
    (i j : BlockIndex (d := d) (X := X))
    (g : Flow.BitDirection d) : Finset (Fin d → Fin M) := by
  classical
  exact (Finset.univ : Finset (Fin d → Fin M)).filter fun q ↦
    blockOf (d := d) M
      (bitMoves (d := d) g (blockPoint (d := d) M i q)) = j

@[simp] private lemma mem_outgoingCrossings
    (M : ℕ) [NeZero M]
    (i j : BlockIndex (d := d) (X := X))
    (g : Flow.BitDirection d) (q : Fin d → Fin M) :
    q ∈ outgoingCrossings M i j g ↔
      blockOf (d := d) M
        (bitMoves (d := d) g (blockPoint (d := d) M i q)) = j := by
  classical
  rw [outgoingCrossings]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma card_outgoing_crossings_le
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (i j : BlockIndex (d := d) (X := X)) (hij : i ≠ j)
    (g : Flow.BitDirection d) :
    (outgoingCrossings M i j g).card ≤ M ^ (d - 1) := by
  classical
  let S := outgoingCrossings M i j g
  by_cases hS : S = ∅
  · rw [show outgoingCrossings M i j g = ∅ from hS]
    simp
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have hmove₀ : blockOf (d := d) M
      (bitMoves (d := d) g (blockPoint (d := d) M i q₀)) = j :=
    (mem_outgoingCrossings M i j g q₀).mp hq₀
  have hfirst : i.1 = j.1 := by
    rw [← hmove₀]
    simp [blockOf, bitMoves_apply, blockPoint, orbitClass_vadd]
  have hsecond : i.2 ≠ j.2 := by
    intro h
    apply hij
    exact Prod.ext hfirst h
  have hpExists : ∃ p : Fin d, i.2 p ≠ j.2 p := by
    by_contra h
    push_neg at h
    exact hsecond (funext h)
  obtain ⟨p, hp⟩ := hpExists
  let last : Fin M := ⟨M - 1, Nat.sub_lt (NeZero.pos M) (by omega)⟩
  have hsubset : S ⊆
      (Finset.univ : Finset (Fin d → Fin M)).filter (fun q ↦ q p = last) := by
    intro q hq
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hmove : blockOf (d := d) M
      (bitMoves (d := d) g (blockPoint (d := d) M i q)) = j :=
      (mem_outgoingCrossings M i j g q).mp hq
    let n : Lattice d :=
      (latticeDivMod (d := d) M).symm (i.2, q)
    have hcoord : orbitCoord (d := d)
        (Flow.bitVector g +ᵥ blockPoint (d := d) M i q) =
        Flow.bitVector g + n := by
      rw [orbitCoord_vadd (d := d) hfree,
        orbitCoord_blockPoint (d := d) hfree]
    have htarget := congrArg (fun z ↦ z.2 p) hmove
    simp only [blockOf, bitMoves_apply] at htarget
    rw [hcoord] at htarget
    have hcoarse :
        ((Int.divModEquiv M)
          ((g p : ℕ) + (Int.divModEquiv M).symm (i.2 p, q p))).1 ≠
          i.2 p := by
      intro heq
      apply hp
      change ((Int.divModEquiv M)
        (((g p : ℕ) : ℤ) + (Int.divModEquiv M).symm (i.2 p, q p))).1 =
          j.2 p at htarget
      exact heq.symm.trans htarget
    have hlast := divMod_add_bit_ne_imp_eq_last (i.2 p) (q p) (g p)
      (by simpa only [add_comm] using hcoarse)
    apply Fin.ext
    exact hlast
  calc
    S.card ≤
        ((Finset.univ : Finset (Fin d → Fin M)).filter
          (fun q ↦ q p = last)).card := Finset.card_le_card hsubset
    _ = M ^ (d - 1) := by
      rw [← Fintype.card_subtype]
      exact card_fixed_coordinate p last

private noncomputable def orbitRawBlockFlow
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (i j : BlockIndex (d := d) (X := X)) : ℤ := by
  classical
  exact rawBlockFlow (orbitBlockPartition hfree M) (bitMoves (d := d))
    (fun x g ↦ φ g x) i j

private lemma orbitRawBlockFlow_eq
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (i j : BlockIndex (d := d) (X := X)) :
    orbitRawBlockFlow hfree M φ i j =
      ∑ g : Flow.BitDirection d, ∑ q ∈ outgoingCrossings M i j g,
        φ g (blockPoint (d := d) M i q) := by
  classical
  rw [orbitRawBlockFlow, rawBlockFlow]
  change (∑ x ∈ blockPoints (d := d) M i, ∑ g : Flow.BitDirection d,
      if blockOf (d := d) M (bitMoves (d := d) g x) = j
        then φ g x else 0) = _
  rw [blockPoints, Finset.sum_image
    (blockPoint_injective (d := d) hfree M i).injOn]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← Finset.sum_filter]
  rfl

private lemma abs_rawBlockFlow_orbit_le
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (b : ℕ) (hbound : ∀ g x, |φ g x| ≤ (b : ℤ))
    (i j : BlockIndex (d := d) (X := X)) (hij : i ≠ j) :
    |orbitRawBlockFlow hfree M φ i j| ≤
      ((2 ^ d * b * M ^ (d - 1) : ℕ) : ℤ) := by
  classical
  rw [orbitRawBlockFlow_eq hfree]
  calc
    |∑ g : Flow.BitDirection d, ∑ q ∈ outgoingCrossings M i j g,
        φ g (blockPoint (d := d) M i q)| ≤
        ∑ g : Flow.BitDirection d,
          |∑ q ∈ outgoingCrossings M i j g,
            φ g (blockPoint (d := d) M i q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g : Flow.BitDirection d, ((M ^ (d - 1) * b : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro g hg
      calc
        |∑ q ∈ outgoingCrossings M i j g,
            φ g (blockPoint (d := d) M i q)| ≤
            ∑ q ∈ outgoingCrossings M i j g,
              |φ g (blockPoint (d := d) M i q)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _q ∈ outgoingCrossings M i j g, (b : ℤ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact hbound g _
        _ = (((outgoingCrossings M i j g).card * b : ℕ) : ℤ) := by
          simp
        _ ≤ ((M ^ (d - 1) * b : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right b
            (card_outgoing_crossings_le hfree M i j hij g)
    _ = ((2 ^ d * b * M ^ (d - 1) : ℕ) : ℤ) := by
      simp [mul_assoc, mul_comm, mul_left_comm]

private lemma orbitNetBlockFlow_eq_raw_sub
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (i j : BlockIndex (d := d) (X := X)) :
    orbitNetBlockFlow hfree M φ i j =
      orbitRawBlockFlow hfree M φ i j -
        orbitRawBlockFlow hfree M φ j i := by
  classical
  rfl

/-- A bounded bit-direction flow carries only boundary-order net flow between
two canonical side-`M` blocks. -/
theorem orbitNetBlockFlow_le
    (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M]
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (b : ℕ) (hbound : ∀ g x, |φ g x| ≤ (b : ℤ))
    (i j : BlockIndex (d := d) (X := X)) :
    orbitNetBlockFlow hfree M φ i j ≤
      (2 ^ (d + 1) * b * M ^ (d - 1) : ℕ) := by
  by_cases hij : i = j
  · subst j
    rw [orbitNetBlockFlow_eq_raw_sub]
    simp only [sub_self, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hi := abs_rawBlockFlow_orbit_le hfree M φ b hbound i j hij
  have hj := abs_rawBlockFlow_orbit_le hfree M φ b hbound j i (Ne.symm hij)
  rw [orbitNetBlockFlow_eq_raw_sub]
  calc
    orbitRawBlockFlow hfree M φ i j - orbitRawBlockFlow hfree M φ j i ≤
        |orbitRawBlockFlow hfree M φ i j| +
          |orbitRawBlockFlow hfree M φ j i| := by
      linarith [le_abs_self (orbitRawBlockFlow hfree M φ i j),
        neg_le_abs (orbitRawBlockFlow hfree M φ j i)]
    _ ≤ ((2 ^ d * b * M ^ (d - 1) : ℕ) : ℤ) +
        ((2 ^ d * b * M ^ (d - 1) : ℕ) : ℤ) := add_le_add hi hj
    _ = ((2 ^ (d + 1) * b * M ^ (d - 1) : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      ring

end Capacity

section Displacements

variable {d : ℕ} {X : Type*} [AddGroup X] [AddAction (Lattice d) X]

/-- The relative lattice vector between two offsets in equal or coordinatewise
adjacent side-`M` blocks. -/
def blockDisplacementVector (M : ℕ) (δ : Fin d → Fin 3)
    (q r : Fin d → Fin M) : Lattice d := fun k ↦
  (((δ k : ℕ) : ℤ) - 1) * (M : ℤ) + (r k : ℕ) - (q k : ℕ)

/-- The finite set of additive displacements between points in equal or
coordinatewise adjacent canonical blocks, for an action induced by an
additive lattice homomorphism. -/
def orbitDisplacements (shift : Lattice d →+ X) (M : ℕ) : Finset X := by
  classical
  exact Finset.univ.image fun p :
      (Fin d → Fin 3) × (Fin d → Fin M) × (Fin d → Fin M) ↦
    shift (blockDisplacementVector M p.1 p.2.1 p.2.2)

private lemma latticeDivMod_adjacent_sub
    (M : ℕ) [NeZero M]
    (k : Lattice d) (δ : Fin d → Fin 3) (q r : Fin d → Fin M) :
    (latticeDivMod (d := d) M).symm
        ((fun p ↦ k p + (δ p : ℕ) - 1), r) -
      (latticeDivMod (d := d) M).symm (k, q) =
        blockDisplacementVector M δ q r := by
  funext p
  change (k p + ((δ p : ℕ) : ℤ) - 1) * (M : ℤ) + (r p : ℕ) -
      (k p * (M : ℤ) + (q p : ℕ)) =
    (((δ p : ℕ) : ℤ) - 1) * (M : ℤ) + (r p : ℕ) - (q p : ℕ)
  ring

/-- Equal or adjacent canonical blocks give one of the explicit finite
additive displacements.  The compatibility equation is necessary: an
arbitrary permutation action on an additive group need not act by additive
translations. -/
theorem sub_mem_orbitDisplacements_of_same_or_adjacent
    (hfree : FreeAction (d := d) (X := X))
    (shift : Lattice d →+ X)
    (htranslate : ∀ (n : Lattice d) (x : X), n +ᵥ x = shift n + x)
    (M : ℕ) [NeZero M] (a b : X)
    (hab : blockOf (d := d) M b = blockOf (d := d) M a ∨
      blockOf (d := d) M b ∈
        orbitAdjacentBlocks hfree M (blockOf (d := d) M a)) :
    b - a ∈ orbitDisplacements shift M := by
  classical
  let i := blockOf (d := d) M a
  let j := blockOf (d := d) M b
  have hj : j ∈ ternaryBlockNeighborhood i := by
    rcases hab with hs | ha
    · rw [ternaryBlockNeighborhood, Finset.mem_image]
      let δ : Fin d → Fin 3 := fun _ ↦ 1
      refine ⟨δ, Finset.mem_univ _, ?_⟩
      rw [show j = i from hs]
      apply Prod.ext
      · rfl
      · funext p
        simp [δ]
    · exact orbitAdjacentBlocks_subset_ternaryBlockNeighborhood hfree M i ha
  rw [ternaryBlockNeighborhood, Finset.mem_image] at hj
  obtain ⟨δ, hδuniv, hδ⟩ := hj
  let q := blockOffset (d := d) M a
  let r := blockOffset (d := d) M b
  have ha : blockPoint (d := d) M i q = a :=
    blockPoint_blockOf_offset (d := d) M a
  have hb : blockPoint (d := d) M j r = b :=
    blockPoint_blockOf_offset (d := d) M b
  rw [orbitDisplacements, Finset.mem_image]
  refine ⟨(δ, q, r), Finset.mem_univ _, ?_⟩
  rw [← ha, ← hb]
  have hji : j =
      (i.1, fun p ↦ i.2 p + (δ p : ℕ) - 1) := hδ.symm
  rw [hji]
  simp only [blockPoint]
  rw [htranslate, htranslate]
  rw [show shift
      ((latticeDivMod (d := d) M).symm
        ((fun p ↦ i.2 p + (δ p : ℕ) - 1), r)) + orbitRep i.1 -
      (shift ((latticeDivMod (d := d) M).symm (i.2, q)) + orbitRep i.1) =
      shift ((latticeDivMod (d := d) M).symm
        ((fun p ↦ i.2 p + (δ p : ℕ) - 1), r)) -
      shift ((latticeDivMod (d := d) M).symm (i.2, q)) by
        simp [sub_eq_add_neg, neg_add_rev, add_assoc]]
  rw [← map_sub, latticeDivMod_adjacent_sub]

end Displacements

section TorusApplication

open TorusAction

/-- The additive homomorphism underlying the standard lattice action on a
torus. -/
def torusShift {d k : ℕ} (u : Fin d → Torus k) :
    Flow.Lattice d →+ Torus k where
  toFun := displacement u
  map_zero' := displacement_zero u
  map_add' := displacement_add u

@[simp] lemma torusShift_apply {d k : ℕ} (u : Fin d → Torus k)
    (n : Flow.Lattice d) : torusShift u n = displacement u n := rfl

private lemma torus_freeAction_of_free {d k : ℕ}
    (u : Fin d → Torus k) (hu : Free u) :
    letI := torusAddAction u
    FreeAction (d := d) (X := Torus k) := by
  let := torusAddAction u
  intro x m n hmn
  apply hu
  exact add_right_cancel hmn

/-- The application-facing canonical block theorem on a torus.  Degree,
boundary capacity, and finite-displacement compatibility are all discharged;
the remaining inputs are exactly freeness, the bounded point flow with its
divergence, and the two room estimates. -/
theorem exists_equidecomp_of_torusBitFlow
    {d k : ℕ} (u : Fin d → Torus k) (hu : Free u)
    (A B : Set (Torus k)) (M : ℕ) [NeZero M]
    (φ : Flow.BitDirection d → Torus k → ℤ) (b : ℕ)
    (hbound : ∀ g x, |φ g x| ≤ (b : ℤ))
    (hdiv : ∀ x,
      letI := torusAddAction u
      bitDivergence (d := d) φ x = intIndicator B x - intIndicator A x)
    (hroomA :
      letI := torusAddAction u
      ∀ i : BlockIndex (d := d) (X := Torus k),
        3 ^ d * (2 ^ (d + 1) * b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) A M i).card)
    (hroomB :
      letI := torusAddAction u
      ∀ i : BlockIndex (d := d) (X := Torus k),
        3 ^ d * (2 ^ (d + 1) * b * M ^ (d - 1)) ≤
          (pointsInBlock (d := d) B M i).card) :
    ∃ e : Equidecomp (Torus k) (Multiplicative (Torus k)),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A
          (multiplicativeDisplacements
            (orbitDisplacements (torusShift u) M)) := by
  let := torusAddAction u
  have hfree : FreeAction (d := d) (X := Torus k) :=
    torus_freeAction_of_free u hu
  apply exists_equidecomp_of_orbitBitFlow hfree A B
    (orbitDisplacements (torusShift u) M) M (3 ^ d)
    (2 ^ (d + 1) * b * M ^ (d - 1)) φ
  · exact card_orbitAdjacentBlocks_le_pow_three hfree M
  · exact orbitNetBlockFlow_le hfree M φ b hbound
  · exact hdiv
  · exact hroomA
  · exact hroomB
  · intro a b hab
    exact sub_mem_orbitDisplacements_of_same_or_adjacent hfree
      (torusShift u) (fun _ _ ↦ rfl) M a b hab

end TorusApplication

end

end Erdos1124.OrbitBitBounds
