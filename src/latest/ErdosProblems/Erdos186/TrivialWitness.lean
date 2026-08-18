/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.StructureTheorem

/-!
# Trivial witnesses for the CFP structure interface

This file supplies `CFPWitness` values in the degenerate parameter regimes
where no deep subset-sum structure theorem is needed.

* If `A.card ≤ loss`, discard all of `A` and use the rank-zero GAP `{0}`.
* If the dilation scale is zero and `A.card ≤ D`, enumerate `A` as the
  steps of a rank-`A.card` GAP of widths two.  Its carrier contains `0` and
  `A`; its zero dilation is `{0}`, so the empty reserved set covers it.

The second construction is intentionally not asserted to be proper before
dilation: arbitrary elements of `A` may satisfy additive relations.  At
scale zero every coefficient box has a unique element, which is exactly the
properness required by `CFPWitness`.
-/

namespace Erdos186

open scoped BigOperators

namespace CFP

variable {d : ℕ}

/-- The homogeneous rank-zero GAP whose carrier is the singleton `{0}`. -/
def zeroGAP (d : ℕ) : GAP d 0 where
  offset := 0
  steps := fun i ↦ Fin.elim0 i
  widths := fun i ↦ Fin.elim0 i
  width_pos := fun i ↦ Fin.elim0 i

@[simp]
theorem zeroGAP_offset : (zeroGAP d).offset = 0 := rfl

@[simp]
theorem zeroGAP_carrier : (zeroGAP d).carrier = {0} := by
  ext x
  rw [GAP.mem_carrier_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    apply funext
    intro j
    change 0 + ∑ i : Fin 0, (n i : ℤ) * (zeroGAP d).steps i j = 0
    simp
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    apply funext
    intro j
    change 0 + ∑ i : Fin 0,
      ((fun i ↦ Fin.elim0 i) i : ℤ) * (zeroGAP d).steps i j = 0
    simp

@[simp]
theorem zeroGAP_dilate_carrier (k : ℕ) :
    ((zeroGAP d).dilate k).carrier = {0} := by
  ext x
  rw [GAP.mem_carrier_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    apply funext
    intro j
    change (k : ℤ) * 0 +
      ∑ i : Fin 0, (n i : ℤ) * (zeroGAP d).steps i j = 0
    simp
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    apply funext
    intro j
    change (k : ℤ) * 0 + ∑ i : Fin 0,
      ((fun i ↦ Fin.elim0 i) i : ℤ) * (zeroGAP d).steps i j = 0
    simp

/-- The rank-zero GAP is homogeneous. -/
theorem zeroGAP_homogeneous : (zeroGAP d).Homogeneous := by
  refine ⟨Fin.elim0, ?_⟩
  ext j
  simp [zeroGAP]

/-- Every dilation of the rank-zero GAP is proper. -/
theorem zeroGAP_dilate_proper (k : ℕ) : ((zeroGAP d).dilate k).Proper := by
  intro x y _hxy
  exact Subsingleton.elim x y

/-- The translate of the rank-zero GAP by zero is covered by the subset
sums of the empty set. -/
theorem zeroGAP_covered_by_empty (k : ℕ) :
    translate (0 : LatticePoint d) ((zeroGAP d).dilate k).carrier ⊆
      GAP.subsetSums (∅ : Finset (LatticePoint d)) := by
  intro x hx
  rw [mem_translate_iff] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz0 : z = 0 := by
    simpa only [zeroGAP_dilate_carrier, Finset.mem_singleton] using hz
  subst z
  exact GAP.zero_mem_subsetSums _

/-- A witness obtained by discarding the whole input set. -/
def discardAllWitness (A : Finset (LatticePoint d)) (s D k loss : ℕ)
    (hA : A.card ≤ loss) : CFPWitness A s D k loss where
  core := ∅
  reserved := ∅
  rank := 0
  rank_le := Nat.zero_le D
  progression := zeroGAP d
  core_subset := Finset.empty_subset A
  reserved_subset_core := Finset.Subset.rfl
  core_large := by simpa using hA
  reserved_small := Nat.zero_le s
  core_zero_subset := by simp
  homogeneous := zeroGAP_homogeneous
  translatePoint := 0
  covered := zeroGAP_covered_by_empty k
  dilate_proper := zeroGAP_dilate_proper k

/-- If the loss allowance can discard every element, the CFP conclusion is
available for arbitrary values of all other parameters. -/
theorem hasCFPStructure_of_card_le_loss (A : Finset (LatticePoint d))
    (s D k loss : ℕ) (hA : A.card ≤ loss) :
    HasCFPStructure A s D k loss :=
  ⟨discardAllWitness A s D k loss hA⟩

/-- In particular, the empty set always has a CFP witness. -/
theorem hasCFPStructure_empty (s D k loss : ℕ) :
    HasCFPStructure (∅ : Finset (LatticePoint d)) s D k loss := by
  exact hasCFPStructure_of_card_le_loss ∅ s D k loss (by simp)

/-- A bijective enumeration of the subtype associated to a finite set. -/
noncomputable def enumEquiv (A : Finset (LatticePoint d)) :
    Fin A.card ≃ ↑A :=
  Fintype.equivOfCardEq (by simp)

/-- Enumerate a finite set by `Fin A.card`. -/
noncomputable def enum (A : Finset (LatticePoint d)) :
    Fin A.card → LatticePoint d := fun i ↦ (enumEquiv A i).1

theorem enum_mem (A : Finset (LatticePoint d)) (i : Fin A.card) :
    enum A i ∈ A :=
  (enumEquiv A i).2

theorem exists_enum_eq (A : Finset (LatticePoint d))
    {x : LatticePoint d} (hx : x ∈ A) :
    ∃ i, enum A i = x := by
  let xA : ↑A := ⟨x, hx⟩
  refine ⟨(enumEquiv A).symm xA, ?_⟩
  exact congrArg Subtype.val ((enumEquiv A).apply_symm_apply xA)

/-- The width-two GAP whose steps enumerate `A`. -/
noncomputable def supportGAP (A : Finset (LatticePoint d)) : GAP d A.card where
  offset := 0
  steps := enum A
  widths := fun _ ↦ 2
  width_pos := fun _ ↦ by omega

/-- Every input element, and zero, lies in the carrier of `supportGAP`. -/
theorem insert_subset_supportGAP_carrier (A : Finset (LatticePoint d)) :
    insert 0 A ⊆ (supportGAP A).carrier := by
  classical
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact GAP.mem_carrier_iff.mpr
      ⟨fun _ ↦ ⟨0, by simp [supportGAP]⟩,
        by ext j; simp [GAP.coordPoint, supportGAP]⟩
  · obtain ⟨i, hi⟩ := exists_enum_eq A hx
    let n : (supportGAP A).Coord := fun j ↦
      if hji : j = i then ⟨1, by simp [supportGAP]⟩
      else ⟨0, by simp [supportGAP]⟩
    rw [GAP.mem_carrier_iff]
    refine ⟨n, ?_⟩
    ext q
    simp only [GAP.coordPoint, supportGAP, Pi.zero_apply, zero_add, n]
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _hj hji
      simp [hji]
    · simp

/-- `supportGAP` is homogeneous because its offset is zero. -/
theorem supportGAP_homogeneous (A : Finset (LatticePoint d)) :
    (supportGAP A).Homogeneous := by
  refine ⟨fun _ ↦ 0, ?_⟩
  ext j
  simp [supportGAP]

/-- The zero dilation of any GAP is proper: every coordinate has width one. -/
theorem dilate_zero_proper {r : ℕ} (P : GAP d r) : (P.dilate 0).Proper := by
  intro x y _hxy
  funext i
  apply Fin.ext
  have hx := (x i).isLt
  have hy := (y i).isLt
  simp only [GAP.dilate_widths, zero_mul, zero_add] at hx hy
  omega

/-- At dilation scale zero, the empty reserved set covers the zero translate
of every GAP. -/
theorem dilate_zero_covered_by_empty {r : ℕ} (P : GAP d r) :
    translate (0 : LatticePoint d) (P.dilate 0).carrier ⊆
      GAP.subsetSums (∅ : Finset (LatticePoint d)) := by
  rw [GAP.dilate_zero_carrier]
  intro x hx
  rw [mem_translate_iff] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz0 : z = 0 := by simpa using hz
  subst z
  exact GAP.zero_mem_subsetSums _

/-- A witness at dilation scale zero.  The only necessary finite resource is
one rank for each element of `A`; neither the reserved-set budget nor the
loss allowance is used. -/
noncomputable def zeroScaleWitness (A : Finset (LatticePoint d))
    (s D loss : ℕ) (hA : A.card ≤ D) : CFPWitness A s D 0 loss where
  core := A
  reserved := ∅
  rank := A.card
  rank_le := hA
  progression := supportGAP A
  core_subset := Finset.Subset.rfl
  reserved_subset_core := Finset.empty_subset A
  core_large := by omega
  reserved_small := Nat.zero_le s
  core_zero_subset := insert_subset_supportGAP_carrier A
  homogeneous := supportGAP_homogeneous A
  translatePoint := 0
  covered := dilate_zero_covered_by_empty (supportGAP A)
  dilate_proper := dilate_zero_proper (supportGAP A)

/-- The exact CFP conclusion at scale zero, under the evident rank budget. -/
theorem hasCFPStructure_zero_scale (A : Finset (LatticePoint d))
    (s D loss : ℕ) (hA : A.card ≤ D) :
    HasCFPStructure A s D 0 loss :=
  ⟨zeroScaleWitness A s D loss hA⟩

/-- A convenient parameter form: choosing `D = A.card` always suffices at
scale zero. -/
theorem hasCFPStructure_zero_scale_card (A : Finset (LatticePoint d))
    (s loss : ℕ) : HasCFPStructure A s A.card 0 loss := by
  exact hasCFPStructure_zero_scale A s A.card loss le_rfl

/-- The zero-scale witness remains available when both the reserved budget
and rank budget dominate the cardinality of `A`.  The first hypothesis is
recorded explicitly for callers whose trivial branch is stated using both
budgets; the construction in fact reserves no elements. -/
theorem hasCFPStructure_zero_scale_of_card_le (A : Finset (LatticePoint d))
    (s D loss : ℕ) (_hs : A.card ≤ s) (hD : A.card ≤ D) :
    HasCFPStructure A s D 0 loss :=
  hasCFPStructure_zero_scale A s D loss hD

end CFP
end Erdos186
