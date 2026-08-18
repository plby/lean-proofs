/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# The subset-sum structure interface for Erdős problem 186

This file isolates the *conclusion* of the Conlon--Fox--Pham subset-sum
structure theorem in terms of the finite GAP API in `Erdos186.GAP`.

The deep existence theorem is not currently in Mathlib.  Consequently this
file deliberately does not postulate it.  Instead, `CFPWitness A s D k loss`
is the data supplied by one application of that theorem, where

* `s` bounds the number of reserved elements;
* `D` bounds the rank of the GAP;
* `k` is the (integer) dilation scale; and
* `loss` bounds the number of elements removed from the structured core.

All consequences below are proved from that data.  In particular, a proper
dilated GAP covered by subset sums has volume at most `2 ^ s`.  This is the
finite counting interface needed by the dimension-increase arguments.
-/

namespace Erdos186

open scoped BigOperators

namespace CFP

/-- A closed axis-parallel integer box in `ℤ^d`.  The box is allowed to be
empty when one of its lower endpoints exceeds the corresponding upper
endpoint. -/
structure IntegerBox (d : ℕ) where
  lower : LatticePoint d
  upper : LatticePoint d

namespace IntegerBox

variable {d : ℕ}

/-- The finite carrier of an integer box. -/
noncomputable def carrier (B : IntegerBox d) : Finset (LatticePoint d) :=
  Fintype.piFinset fun i ↦ Finset.Icc (B.lower i) (B.upper i)

@[simp]
theorem mem_carrier_iff {B : IntegerBox d} {x : LatticePoint d} :
    x ∈ B.carrier ↔ ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i := by
  simp [carrier]

/-- The cardinality of an integer box is the product of its side lengths. -/
theorem card_carrier (B : IntegerBox d) :
    B.carrier.card =
      ∏ i, (B.upper i + 1 - B.lower i).toNat := by
  simp [carrier, Int.card_Icc]

end IntegerBox

/-- Translation of a finite subset of an integer lattice. -/
def translate {d : ℕ} (x : LatticePoint d) (S : Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  S.image fun y ↦ x + y

@[simp]
theorem mem_translate_iff {d : ℕ} {x y : LatticePoint d}
    {S : Finset (LatticePoint d)} :
    y ∈ translate x S ↔ ∃ z ∈ S, x + z = y := by
  classical
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    exact ⟨z, hz, hzy⟩
  · rintro ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

/-- Translation preserves cardinality. -/
@[simp]
theorem card_translate {d : ℕ} (x : LatticePoint d)
    (S : Finset (LatticePoint d)) :
    (translate x S).card = S.card := by
  classical
  exact Finset.card_image_of_injective _ (add_right_injective x)

/-- Subset sums are monotone in the underlying finite set. -/
theorem subsetSums_mono {d : ℕ} {A B : Finset (LatticePoint d)}
    (hAB : A ⊆ B) : GAP.subsetSums A ⊆ GAP.subsetSums B := by
  intro x hx
  obtain ⟨S, hSA, hsum⟩ := GAP.mem_subsetSums_iff.mp hx
  exact GAP.mem_subsetSums_iff.mpr ⟨S, hSA.trans hAB, hsum⟩

/-- The finite data in the conclusion of one application of the
Conlon--Fox--Pham subset-sum structure theorem.

This structure packages only the conclusion.  Its fields do not assert that
a witness exists for every set satisfying the analytic size hypotheses; that
existence assertion is precisely the external theorem still to be
formalized. -/
structure CFPWitness {d : ℕ} (A : Finset (LatticePoint d))
    (s D k loss : ℕ) where
  /-- The large structured part of `A`. -/
  core : Finset (LatticePoint d)
  /-- The small reserved set whose subset sums cover a GAP. -/
  reserved : Finset (LatticePoint d)
  /-- Rank of the progression obtained from the structure theorem. -/
  rank : ℕ
  rank_le : rank ≤ D
  progression : GAP d rank
  core_subset : core ⊆ A
  reserved_subset_core : reserved ⊆ core
  /-- At most `loss` elements of `A` are discarded. -/
  core_large : A.card ≤ core.card + loss
  reserved_small : reserved.card ≤ s
  /-- The structured core and zero lie in the undilated progression. -/
  core_zero_subset : insert 0 core ⊆ progression.carrier
  homogeneous : progression.Homogeneous
  translatePoint : LatticePoint d
  /-- A translate of the dilated GAP is covered by subset sums of the
  reserved set. -/
  covered :
    translate translatePoint (progression.dilate k).carrier ⊆
      GAP.subsetSums reserved
  /-- Properness is required at the enlarged scale, exactly where counting
  the displayed coefficient box is used. -/
  dilate_proper : (progression.dilate k).Proper

namespace CFPWitness

variable {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFPWitness A s D k loss)

/-- Every reserved element is an element of the original set. -/
theorem reserved_subset : W.reserved ⊆ A :=
  W.reserved_subset_core.trans W.core_subset

/-- The covered translate is also contained in the subset sums of the
original set. -/
theorem covered_by_original_subsetSums :
    translate W.translatePoint (W.progression.dilate k).carrier ⊆
      GAP.subsetSums A :=
  W.covered.trans (subsetSums_mono W.reserved_subset)

/-- The number of discarded elements is at most the loss parameter. -/
theorem card_sdiff_core_le : (A \ W.core).card ≤ loss := by
  rw [Finset.card_sdiff_of_subset W.core_subset]
  rw [Nat.sub_le_iff_le_add]
  simpa [add_comm] using W.core_large

/-- Subtraction form of the lower bound for the structured core. -/
theorem card_sub_loss_le_core : A.card - loss ≤ W.core.card := by
  rw [Nat.sub_le_iff_le_add]
  simpa [add_comm] using W.core_large

/-- The core cardinality is at most the presented volume of its GAP.  This
does not need properness. -/
theorem core_card_le_volume : W.core.card ≤ W.progression.volume := by
  calc
    W.core.card ≤ W.progression.carrier.card := by
      apply Finset.card_le_card
      exact (Finset.subset_insert 0 W.core).trans W.core_zero_subset
    _ ≤ W.progression.volume := W.progression.card_carrier_le_volume

/-- The original set, up to the allowed loss, fits inside the displayed GAP
volume. -/
theorem card_sub_loss_le_volume : A.card - loss ≤ W.progression.volume :=
  W.card_sub_loss_le_core.trans W.core_card_le_volume

/-- Coverage and properness bound the dilated GAP volume by the number of
available subset sums. -/
theorem dilated_volume_le_card_subsetSums :
    (W.progression.dilate k).volume ≤
      (GAP.subsetSums W.reserved).card := by
  rw [← W.progression.dilate k |>.card_carrier_eq_volume W.dilate_proper,
    ← card_translate W.translatePoint (W.progression.dilate k).carrier]
  exact Finset.card_le_card W.covered

/-- A proper dilated GAP covered by subset sums of the reserved set has at
most `2 ^ #reserved` displayed points. -/
theorem dilated_volume_le_pow_card_reserved :
    (W.progression.dilate k).volume ≤ 2 ^ W.reserved.card :=
  W.dilated_volume_le_card_subsetSums.trans
    (GAP.card_subsetSums_le_pow_two W.reserved)

/-- The convenient theorem-parameter form of the preceding counting bound. -/
theorem dilated_volume_le_pow_s :
    (W.progression.dilate k).volume ≤ 2 ^ s := by
  exact W.dilated_volume_le_pow_card_reserved.trans
    (Nat.pow_le_pow_right (by omega) W.reserved_small)

/-- The core is nonempty whenever the allowed loss is smaller than the
original set. -/
theorem core_nonempty (h : loss < A.card) : W.core.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hcore
  have : W.core.card = 0 := by simp [hcore]
  have hlarge := W.core_large
  omega

/-- In particular, the progression carrier is nonempty whenever the core
survives the loss. -/
theorem progression_carrier_nonempty (h : loss < A.card) :
    W.progression.carrier.Nonempty :=
  (W.core_nonempty h).mono <|
    (Finset.subset_insert 0 W.core).trans W.core_zero_subset

end CFPWitness

/-- The proposition that the CFP conclusion is available with specified
finite parameters.  Keeping this as `Nonempty CFPWitness` makes the precise
remaining mathematical dependency explicit without postulating it. -/
def HasCFPStructure {d : ℕ} (A : Finset (LatticePoint d))
    (s D k loss : ℕ) : Prop :=
  Nonempty (CFPWitness A s D k loss)

/-- Eliminate the proposition-valued structure interface into any target
proposition. -/
theorem HasCFPStructure.elim {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)} {p : Prop}
    (h : HasCFPStructure A s D k loss)
    (hp : ∀ _W : CFPWitness A s D k loss, p) : p := by
  exact Nonempty.elim h hp

/-- Any genuine CFP witness supplies the proposition-valued interface. -/
theorem hasCFPStructure_of_witness {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFPWitness A s D k loss) :
    HasCFPStructure A s D k loss :=
  ⟨W⟩

end CFP
end Erdos186
