/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.LayerSelection
import ErdosProblems.Erdos874.ModularDecomposition
import ErdosProblems.Erdos874.ResidueSubgroup
import ErdosProblems.Erdos874.SubgroupGenerators
import ErdosProblems.Erdos874.AlignedBlockSum
import ErdosProblems.Erdos874.RegularSpan

/-!
# Finite modular structure for Erdős Problem 874

This file supplies the finite bookkeeping used in the modular part of the
Deshouillers--Freiman argument.  It separates four elementary operations:

* partitioning a finite integer set into residue fibres;
* discarding the fibres having fewer than `R` elements, with the sharp
  fibre-counting bound;
* combining a long `q`-progression with one complete block for a subgroup of
  order `h`, where `q = d*h`;
* turning a common residue modulo `d`, together with the ambient bound
  `[1,N]`, into a containing progression of at most `N/d+1` terms.

The lower-level packaging theorem accepts a complete integer `d`-block.  The
end-to-end theorems below derive the residue subgroup and the common regular
coset.  They also keep the quotient coordinates of the integer lifts
explicit: residue coverage alone is not silently identified with literal
integer progression coverage.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma restrictedSumset_mono_modularStructure
    {r : ℕ} {A B : Finset ℤ} (hAB : A ⊆ B) :
    restrictedSumset r A ⊆ restrictedSumset r B := by
  intro z hz
  obtain ⟨C, hCA, hCcard, hCsum⟩ := mem_restrictedSumset.mp hz
  exact mem_restrictedSumset.mpr ⟨C, hCA.trans hAB, hCcard, hCsum⟩

private lemma add_restrictedSumsets_disjoint_modularStructure
    {A B : Finset ℤ} {r s : ℕ} (hAB : Disjoint A B)
    {x y : ℤ} (hx : x ∈ restrictedSumset r A)
    (hy : y ∈ restrictedSumset s B) :
    x + y ∈ restrictedSumset (r + s) (A ∪ B) := by
  obtain ⟨R, hRA, hRcard, hRsum⟩ := mem_restrictedSumset.mp hx
  obtain ⟨S, hSB, hScard, hSsum⟩ := mem_restrictedSumset.mp hy
  have hRS : Disjoint R S := hAB.mono hRA hSB
  apply mem_restrictedSumset.mpr
  refine ⟨R ∪ S,
    Finset.union_subset (hRA.trans Finset.subset_union_left)
      (hSB.trans Finset.subset_union_right), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hRS, hRcard, hScard]
  · rw [Finset.sum_union hRS, hRsum, hSsum]

/-! ## Residue fibres and the poor part -/

/-- The residues modulo `q` represented by `D`. -/
def residueSupport (q : ℕ) (D : Finset ℤ) : Finset (ZMod q) :=
  D.image fun x ↦ (x : ZMod q)

/-- The fibre of `D` over the residue `r` modulo `q`. -/
def residueFiber (q : ℕ) (D : Finset ℤ) (r : ZMod q) : Finset ℤ :=
  D.filter fun x ↦ (x : ZMod q) = r

/-- Residues whose fibre has at least `R` elements. -/
def richResidues (q R : ℕ) (D : Finset ℤ) : Finset (ZMod q) :=
  (residueSupport q D).filter fun r ↦ R ≤ (residueFiber q D r).card

/-- Represented residue classes which are not rich. -/
def poorResidues (q R : ℕ) (D : Finset ℤ) : Finset (ZMod q) :=
  residueSupport q D \ richResidues q R D

/-- Elements in residue fibres having fewer than `R` elements. -/
def poorPart (q R : ℕ) (D : Finset ℤ) : Finset ℤ :=
  D.filter fun x ↦ (residueFiber q D (x : ZMod q)).card < R

/-- Elements in rich residue fibres. -/
def richPart (q R : ℕ) (D : Finset ℤ) : Finset ℤ :=
  D.filter fun x ↦ R ≤ (residueFiber q D (x : ZMod q)).card

@[simp] lemma mem_residueSupport {q : ℕ} {D : Finset ℤ} {r : ZMod q} :
    r ∈ residueSupport q D ↔ ∃ x ∈ D, (x : ZMod q) = r := by
  simp [residueSupport]

@[simp] lemma mem_residueFiber {q : ℕ} {D : Finset ℤ} {r : ZMod q}
    {x : ℤ} :
    x ∈ residueFiber q D r ↔ x ∈ D ∧ (x : ZMod q) = r := by
  simp [residueFiber]

@[simp] lemma mem_richResidues {q R : ℕ} {D : Finset ℤ} {r : ZMod q} :
    r ∈ richResidues q R D ↔
      r ∈ residueSupport q D ∧ R ≤ (residueFiber q D r).card := by
  simp [richResidues]

@[simp] lemma mem_poorResidues {q R : ℕ} {D : Finset ℤ} {r : ZMod q} :
    r ∈ poorResidues q R D ↔
      r ∈ residueSupport q D ∧ (residueFiber q D r).card < R := by
  simp only [poorResidues, Finset.mem_sdiff, mem_richResidues]
  constructor
  · rintro ⟨hr, hnrich⟩
    exact ⟨hr, Nat.lt_of_not_ge fun hge ↦ hnrich ⟨hr, hge⟩⟩
  · rintro ⟨hr, hlt⟩
    exact ⟨hr, fun hrich ↦ (Nat.not_lt_of_ge hrich.2) hlt⟩

lemma poorResidues_disjoint_richResidues (q R : ℕ) (D : Finset ℤ) :
    Disjoint (poorResidues q R D) (richResidues q R D) := by
  rw [Finset.disjoint_left]
  intro r hpoor hrich
  exact (Finset.mem_sdiff.mp hpoor).2 hrich

lemma poorResidues_union_richResidues (q R : ℕ) (D : Finset ℤ) :
    poorResidues q R D ∪ richResidues q R D = residueSupport q D := by
  rw [poorResidues, Finset.sdiff_union_of_subset]
  exact Finset.filter_subset _ _

lemma poorResidues_card_add_richResidues_card (q R : ℕ) (D : Finset ℤ) :
    (poorResidues q R D).card + (richResidues q R D).card =
      (residueSupport q D).card := by
  rw [← Finset.card_union_of_disjoint
    (poorResidues_disjoint_richResidues q R D),
    poorResidues_union_richResidues]

@[simp] lemma mem_poorPart {q R : ℕ} {D : Finset ℤ} {x : ℤ} :
    x ∈ poorPart q R D ↔
      x ∈ D ∧ (residueFiber q D (x : ZMod q)).card < R := by
  simp [poorPart]

@[simp] lemma mem_richPart {q R : ℕ} {D : Finset ℤ} {x : ℤ} :
    x ∈ richPart q R D ↔
      x ∈ D ∧ R ≤ (residueFiber q D (x : ZMod q)).card := by
  simp [richPart]

lemma poorPart_subset (q R : ℕ) (D : Finset ℤ) : poorPart q R D ⊆ D := by
  intro x hx
  exact (mem_poorPart.mp hx).1

lemma richPart_subset (q R : ℕ) (D : Finset ℤ) : richPart q R D ⊆ D := by
  intro x hx
  exact (mem_richPart.mp hx).1

lemma poorPart_disjoint_richPart (q R : ℕ) (D : Finset ℤ) :
    Disjoint (poorPart q R D) (richPart q R D) := by
  rw [Finset.disjoint_left]
  intro x hxpoor hxrich
  have hp := (mem_poorPart.mp hxpoor).2
  have hr := (mem_richPart.mp hxrich).2
  omega

lemma poorPart_union_richPart (q R : ℕ) (D : Finset ℤ) :
    poorPart q R D ∪ richPart q R D = D := by
  ext x
  simp only [Finset.mem_union, mem_poorPart, mem_richPart]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hpoor : (residueFiber q D (x : ZMod q)).card < R
    · exact Or.inl ⟨hx, hpoor⟩
    · exact Or.inr ⟨hx, Nat.le_of_not_gt hpoor⟩

/-- The poor fibres cost at most `R-1` elements per represented residue.
This is the exact finite counting estimate used when fewer than `R` residues
are represented. -/
theorem poorPart_card_le (q R : ℕ) (D : Finset ℤ) :
    (poorPart q R D).card ≤ (residueSupport q D).card * (R - 1) := by
  let f : ℤ → ZMod q := fun x ↦ (x : ZMod q)
  let P := poorPart q R D
  have hcard : P.card =
      ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card :=
    Finset.card_eq_sum_card_image f P
  rw [hcard]
  calc
    ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card
        ≤ ∑ _r ∈ P.image f, (R - 1) := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨x, hxP, hxr⟩ := Finset.mem_image.mp hr
          have hxpoor : (residueFiber q D (x : ZMod q)).card < R :=
            (mem_poorPart.mp hxP).2
          have hsub : P.filter (fun y ↦ f y = r) ⊆
              residueFiber q D (x : ZMod q) := by
            intro y hy
            have hy' := Finset.mem_filter.mp hy
            apply mem_residueFiber.mpr
            refine ⟨(poorPart_subset q R D) hy'.1, ?_⟩
            change f y = f x
            simpa [hxr] using hy'.2
          have hle := Finset.card_le_card hsub
          omega
    _ = (P.image f).card * (R - 1) := by simp
    _ ≤ (residueSupport q D).card * (R - 1) := by
      apply Nat.mul_le_mul_right
      apply Finset.card_le_card
      intro r hr
      obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.mp hr
      exact mem_residueSupport.mpr
        ⟨x, poorPart_subset q R D hxP, rfl⟩

lemma image_poorPart_cast (q R : ℕ) (D : Finset ℤ) :
    (poorPart q R D).image (fun x : ℤ ↦ (x : ZMod q)) =
      poorResidues q R D := by
  ext r
  constructor
  · intro hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact mem_poorResidues.mpr
      ⟨mem_residueSupport.mpr ⟨x, (mem_poorPart.mp hx).1, rfl⟩,
        (mem_poorPart.mp hx).2⟩
  · intro hr
    obtain ⟨x, hxD, hxr⟩ := mem_residueSupport.mp
      (mem_poorResidues.mp hr).1
    apply Finset.mem_image.mpr
    refine ⟨x, mem_poorPart.mpr ⟨hxD, ?_⟩, hxr⟩
    simpa [hxr] using (mem_poorResidues.mp hr).2

/-- Sharp form of `poorPart_card_le`: only the non-rich represented classes
contribute to the loss. -/
theorem poorPart_card_le_poorResidues (q R : ℕ) (D : Finset ℤ) :
    (poorPart q R D).card ≤ (poorResidues q R D).card * (R - 1) := by
  let f : ℤ → ZMod q := fun x ↦ (x : ZMod q)
  let P := poorPart q R D
  have hcard : P.card =
      ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card :=
    Finset.card_eq_sum_card_image f P
  rw [hcard]
  calc
    ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card
        ≤ ∑ _r ∈ P.image f, (R - 1) := by
          apply Finset.sum_le_sum
          intro r hr
          obtain ⟨x, hxP, hxr⟩ := Finset.mem_image.mp hr
          have hxpoor : (residueFiber q D (x : ZMod q)).card < R :=
            (mem_poorPart.mp hxP).2
          have hsub : P.filter (fun y ↦ f y = r) ⊆
              residueFiber q D (x : ZMod q) := by
            intro y hy
            have hy' := Finset.mem_filter.mp hy
            apply mem_residueFiber.mpr
            refine ⟨(poorPart_subset q R D) hy'.1, ?_⟩
            change f y = f x
            simpa [hxr] using hy'.2
          have hle := Finset.card_le_card hsub
          omega
    _ = (P.image f).card * (R - 1) := by simp
    _ = (poorResidues q R D).card * (R - 1) := by
      rw [show P.image f = poorResidues q R D by
        simpa [P, f] using image_poorPart_cast q R D]

theorem poorPart_card_lt_sq {q R : ℕ} {D : Finset ℤ}
    (hR : 0 < R) (hsupport : (residueSupport q D).card < R) :
    (poorPart q R D).card < R * R := by
  calc
    (poorPart q R D).card
        ≤ (residueSupport q D).card * (R - 1) := poorPart_card_le q R D
    _ ≤ (residueSupport q D).card * R :=
      Nat.mul_le_mul_left _ (Nat.sub_le R 1)
    _ < R * R := Nat.mul_lt_mul_of_pos_right hsupport hR

/-- Two-parameter poor-fibre estimate: fewer than `R` represented classes,
with richness threshold `F`, cost fewer than `R*F` elements. -/
theorem poorPart_card_lt_mul {q R F : ℕ} {D : Finset ℤ}
    (hF : 0 < F) (hsupport : (residueSupport q D).card < R) :
    (poorPart q F D).card < R * F := by
  calc
    (poorPart q F D).card
        ≤ (residueSupport q D).card * (F - 1) := poorPart_card_le q F D
    _ ≤ (residueSupport q D).card * F :=
      Nat.mul_le_mul_left _ (Nat.sub_le F 1)
    _ < R * F := Nat.mul_lt_mul_of_pos_right hsupport hF

lemma image_richPart_cast {q R : ℕ} {D : Finset ℤ} (hR : 0 < R) :
    (richPart q R D).image (fun x : ℤ ↦ (x : ZMod q)) =
      richResidues q R D := by
  ext r
  constructor
  · intro hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact mem_richResidues.mpr
      ⟨mem_residueSupport.mpr ⟨x, (mem_richPart.mp hx).1, rfl⟩,
        (mem_richPart.mp hx).2⟩
  · intro hr
    have hcardpos : 0 < (residueFiber q D r).card :=
      hR.trans_le (mem_richResidues.mp hr).2
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hcardpos
    apply Finset.mem_image.mpr
    refine ⟨x, mem_richPart.mpr ⟨(mem_residueFiber.mp hx).1, ?_⟩,
      (mem_residueFiber.mp hx).2⟩
    simpa [(mem_residueFiber.mp hx).2] using (mem_richResidues.mp hr).2

lemma richPart_card_le_of_fibers_lt_sq
    {q R : ℕ} {D : Finset ℤ} (hR : 0 < R)
    (hall : ∀ g ∈ richResidues q R D,
      (residueFiber q D g).card < R * R) :
    (richPart q R D).card ≤
      (richResidues q R D).card * (R * R - 1) := by
  let f : ℤ → ZMod q := fun x ↦ (x : ZMod q)
  let P := richPart q R D
  have hcard : P.card =
      ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card :=
    Finset.card_eq_sum_card_image f P
  rw [hcard]
  calc
    ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card
        ≤ ∑ _r ∈ P.image f, (R * R - 1) := by
          apply Finset.sum_le_sum
          intro r hr
          have hrG : r ∈ richResidues q R D := by
            rw [← image_richPart_cast hR]
            simpa [P, f] using hr
          obtain ⟨x, hxP, hxr⟩ := Finset.mem_image.mp hr
          have hsub : P.filter (fun y ↦ f y = r) ⊆ residueFiber q D r := by
            intro y hy
            have hy' := Finset.mem_filter.mp hy
            exact mem_residueFiber.mpr
              ⟨(richPart_subset q R D) hy'.1, hy'.2⟩
          have hle := Finset.card_le_card hsub
          have hlt := hall r hrG
          omega
    _ = (P.image f).card * (R * R - 1) := by simp
    _ = (richResidues q R D).card * (R * R - 1) := by
      rw [show P.image f = richResidues q R D by
        simpa [P, f] using image_richPart_cast (q := q) (D := D) hR]

/-- General fibrewise upper bound for the rich part. -/
lemma richPart_card_le_of_fibers_le
    {q F M : ℕ} {D : Finset ℤ} (hF : 0 < F)
    (hall : ∀ g ∈ richResidues q F D, (residueFiber q D g).card ≤ M) :
    (richPart q F D).card ≤ (richResidues q F D).card * M := by
  let f : ℤ → ZMod q := fun x ↦ (x : ZMod q)
  let P := richPart q F D
  have hcard : P.card =
      ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card :=
    Finset.card_eq_sum_card_image f P
  rw [hcard]
  calc
    ∑ r ∈ P.image f, (P.filter fun x ↦ f x = r).card
        ≤ ∑ _r ∈ P.image f, M := by
          apply Finset.sum_le_sum
          intro r hr
          have hrG : r ∈ richResidues q F D := by
            rw [← image_richPart_cast hF]
            simpa [P, f] using hr
          have hsub : P.filter (fun y ↦ f y = r) ⊆ residueFiber q D r := by
            intro y hy
            exact mem_residueFiber.mpr
              ⟨(richPart_subset q F D) (Finset.mem_filter.mp hy).1,
                (Finset.mem_filter.mp hy).2⟩
          exact (Finset.card_le_card hsub).trans (hall r hrG)
    _ = (P.image f).card * M := by simp
    _ = (richResidues q F D).card * M := by
      rw [show P.image f = richResidues q F D by
        simpa [P, f] using image_richPart_cast (q := q) (D := D) hF]

/-- Two-parameter rich-fibre pigeonhole principle.  This is the form needed
when the number of residue classes and the retained fibre threshold live at
different scales. -/
theorem exists_richResidue_with_large_fiber
    {q R F M : ℕ} {D : Finset ℤ} (hF : 0 < F) (hM : 0 < M)
    (hsupport : (residueSupport q D).card < R)
    (hD : R * F + R * M < D.card) :
    ∃ g ∈ richResidues q F D, M ≤ (residueFiber q D g).card := by
  by_contra hnot
  have hall : ∀ g ∈ richResidues q F D,
      (residueFiber q D g).card ≤ M - 1 := by
    intro g hg
    have hlt : (residueFiber q D g).card < M := by
      by_contra hnlt
      exact hnot ⟨g, hg, Nat.le_of_not_gt hnlt⟩
    omega
  have hpoor : (poorPart q F D).card < R * F :=
    poorPart_card_lt_mul hF hsupport
  have hrichBound := richPart_card_le_of_fibers_le hF hall
  have hGle : (richResidues q F D).card ≤ (residueSupport q D).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hGlt : (richResidues q F D).card < R := hGle.trans_lt hsupport
  have hrich : (richPart q F D).card < R * M := by
    calc
      (richPart q F D).card
          ≤ (richResidues q F D).card * (M - 1) := hrichBound
      _ ≤ (richResidues q F D).card * M :=
        Nat.mul_le_mul_left _ (Nat.sub_le M 1)
      _ < R * M := Nat.mul_lt_mul_of_pos_right hGlt hM
  have hpartition : (poorPart q F D).card + (richPart q F D).card = D.card := by
    rw [← Finset.card_union_of_disjoint (poorPart_disjoint_richPart q F D),
      poorPart_union_richPart]
  omega

/-- If `D` is larger than the total possible poor loss and `R³` rich
elements, some rich residue fibre contains `R²` elements. -/
theorem exists_richResidue_with_sq_fiber
    {q R : ℕ} {D : Finset ℤ} (hR : 0 < R)
    (hsupport : (residueSupport q D).card < R)
    (hD : R * R + R * R * R < D.card) :
    ∃ g ∈ richResidues q R D, R * R ≤ (residueFiber q D g).card := by
  by_contra hnot
  have hall : ∀ g ∈ richResidues q R D,
      (residueFiber q D g).card < R * R := by
    intro g hg
    by_contra hnlt
    exact hnot ⟨g, hg, Nat.le_of_not_gt hnlt⟩
  have hpoor : (poorPart q R D).card < R * R :=
    poorPart_card_lt_sq hR hsupport
  have hrichBound := richPart_card_le_of_fibers_lt_sq hR hall
  have hGle : (richResidues q R D).card ≤ (residueSupport q D).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrich : (richPart q R D).card < R * R * R := by
    have hGlt : (richResidues q R D).card < R := hGle.trans_lt hsupport
    have hRRpos : 0 < R * R := Nat.mul_pos hR hR
    calc
      (richPart q R D).card
          ≤ (richResidues q R D).card * (R * R - 1) := hrichBound
      _ ≤ (richResidues q R D).card * (R * R) :=
        Nat.mul_le_mul_left _ (Nat.sub_le (R * R) 1)
      _ < R * (R * R) := Nat.mul_lt_mul_of_pos_right hGlt hRRpos
      _ = R * R * R := by ring
  have hpartition : (poorPart q R D).card + (richPart q R D).card = D.card := by
    rw [← Finset.card_union_of_disjoint (poorPart_disjoint_richPart q R D),
      poorPart_union_richPart]
  omega

/-! ## Canonical representatives and the few-residue estimate -/

/-- Choose one element of `D` above a represented residue.  The subtype in
the domain records that the required fibre is nonempty. -/
noncomputable def residueRepresentative (q : ℕ) (D : Finset ℤ)
    (r : ↑(residueSupport q D)) : ℤ :=
  Classical.choose (mem_residueSupport.mp r.property)

lemma residueRepresentative_mem (q : ℕ) (D : Finset ℤ)
    (r : ↑(residueSupport q D)) :
    residueRepresentative q D r ∈ D :=
  (Classical.choose_spec (mem_residueSupport.mp r.property)).1

@[simp] lemma residueRepresentative_cast (q : ℕ) (D : Finset ℤ)
    (r : ↑(residueSupport q D)) :
    (residueRepresentative q D r : ZMod q) = r :=
  (Classical.choose_spec (mem_residueSupport.mp r.property)).2

/-- A transversal containing exactly one integer from every represented
residue class. -/
noncomputable def residueRepresentatives (q : ℕ) (D : Finset ℤ) : Finset ℤ :=
  (residueSupport q D).attach.image (residueRepresentative q D)

lemma residueRepresentatives_subset (q : ℕ) (D : Finset ℤ) :
    residueRepresentatives q D ⊆ D := by
  intro x hx
  obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hx
  exact residueRepresentative_mem q D r

lemma residueRepresentative_injective (q : ℕ) (D : Finset ℤ) :
    Function.Injective (residueRepresentative q D) := by
  intro r s hrs
  apply Subtype.ext
  have := congrArg (fun x : ℤ ↦ (x : ZMod q)) hrs
  simpa using this

@[simp] theorem residueRepresentatives_card (q : ℕ) (D : Finset ℤ) :
    (residueRepresentatives q D).card = (residueSupport q D).card := by
  rw [residueRepresentatives,
    Finset.card_image_of_injective _ (residueRepresentative_injective q D)]
  simp

lemma residueRepresentatives_cast_injOn (q : ℕ) (D : Finset ℤ) :
    Set.InjOn (fun x : ℤ ↦ (x : ZMod q)) (residueRepresentatives q D) := by
  intro x hx y hy hxy
  obtain ⟨r, _hr, hrx⟩ := Finset.mem_image.mp hx
  obtain ⟨s, _hs, hsy⟩ := Finset.mem_image.mp hy
  rw [← hrx, ← hsy] at hxy ⊢
  have hrs : r = s := by
    apply Subtype.ext
    simpa using hxy
  rw [hrs]

/-- General same-layer packing form of the few-residue argument.  `W` is a
fixed filler disjoint from the residue representatives `X`; consequently all
translates have the same cardinality and land in the prescribed layer `s`.
This is the form used with the small layer selected earlier in DF95. -/
theorem representative_card_mul_le_restricted_layer
    {q t s L : ℕ} {A B X W : Finset ℤ}
    (hBA : B ⊆ A) (hX : X ⊆ A \ B) (hW : W ⊆ (A \ B) \ X)
    (hres : Set.InjOn (fun x : ℤ ↦ (x : ZMod q)) X)
    (hq : 0 < q) (hlayer : t + (W.card + 1) = s)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    X.card * L ≤ (restrictedSumset s A).card := by
  obtain ⟨a, ha⟩ := hAP
  let F : (↑X × Fin L) → ℤ := fun p ↦
    a + (q : ℤ) * (p.2 : ℕ) + (p.1 : ℤ) + ∑ w ∈ W, w
  letI : NeZero q := ⟨hq.ne'⟩
  have hFmem : ∀ p : ↑X × Fin L, F p ∈ restrictedSumset s A := by
    rintro ⟨x, i⟩
    have hxD : (x : ℤ) ∈ A \ B := hX x.property
    have hxW : (x : ℤ) ∉ W := by
      intro hx
      exact (Finset.mem_sdiff.mp (hW hx)).2 x.property
    let U : Finset ℤ := insert (x : ℤ) W
    have hUsub : U ⊆ A \ B := by
      intro y hy
      simp only [U, Finset.mem_insert] at hy
      rcases hy with rfl | hyW
      · exact hxD
      · exact (Finset.mem_sdiff.mp (hW hyW)).1
    have hUcard : U.card = W.card + 1 := by
      simp [U, hxW, Nat.add_comm]
    have hz : a + (q : ℤ) * (i : ℕ) ∈ restrictedSumset t B :=
      ha (mem_arithmeticProgression.mpr ⟨i, i.isLt, rfl⟩)
    have hadd := add_sum_mem_restrictedSumset_of_subset_sdiff hBA hUsub hz
    rw [hUcard, hlayer] at hadd
    simpa [F, U, hxW, add_assoc, add_left_comm, add_comm] using hadd
  have hFinj : Function.Injective F := by
    rintro ⟨x, i⟩ ⟨y, j⟩ heq
    have hresEq : ((x : ℤ) : ZMod q) = ((y : ℤ) : ZMod q) := by
      have heq' := congrArg (fun z : ℤ ↦ (z : ZMod q)) heq
      simpa [F] using heq'
    have hxy : (x : ℤ) = (y : ℤ) := hres x.property y.property hresEq
    have hijZ : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
      have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
      have hmul : (q : ℤ) * ((i : ℕ) : ℤ) =
          (q : ℤ) * ((j : ℕ) : ℤ) := by
        dsimp [F] at heq
        rw [hxy] at heq
        omega
      exact mul_left_cancel₀ hqZ hmul
    have hij : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijZ
    exact Prod.ext (Subtype.ext hxy) (Fin.ext hij)
  let P : Finset ℤ := Finset.univ.image F
  have hPcard : P.card = X.card * L := by
    change (Finset.univ.image F).card = X.card * L
    rw [Finset.card_image_of_injective _ hFinj]
    simp
  have hPsub : P ⊆ restrictedSumset s A := by
    intro z hz
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hz
    exact hFmem p
  rw [← hPcard]
  exact Finset.card_le_card hPsub

/-- Same-layer packing when the residue representatives are fixed-cardinality
subset sums from a reserved regular block `T`.  The filler is chosen outside
the whole reserve, so every translated progression lands in the same layer.
-/
theorem fixed_sum_representatives_card_mul_le_restricted_layer
    {q t r s L : ℕ} {A B T X W : Finset ℤ}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hX : X ⊆ restrictedSumset r T)
    (hW : W ⊆ (A \ B) \ T)
    (hres : Set.InjOn (fun x : ℤ ↦ (x : ZMod q)) X)
    (hq : 0 < q) (hlayer : t + r + W.card = s)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    X.card * L ≤ (restrictedSumset s A).card := by
  obtain ⟨a, ha⟩ := hAP
  let F : (↑X × Fin L) → ℤ := fun p ↦
    a + (q : ℤ) * (p.2 : ℕ) + (p.1 : ℤ) + ∑ w ∈ W, w
  letI : NeZero q := ⟨hq.ne'⟩
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro x hxB hxT
    exact (Finset.mem_sdiff.mp (hT hxT)).2 hxB
  have hBTA : B ∪ T ⊆ A :=
    Finset.union_subset hBA (hT.trans Finset.sdiff_subset)
  have hW' : W ⊆ A \ (B ∪ T) := by
    intro x hxW
    have hx := hW hxW
    exact Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1,
        fun hxu ↦ (Finset.mem_union.mp hxu).elim
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2
          (Finset.mem_sdiff.mp hx).2⟩
  have hFmem : ∀ p : ↑X × Fin L, F p ∈ restrictedSumset s A := by
    rintro ⟨x, i⟩
    have hz : a + (q : ℤ) * (i : ℕ) ∈ restrictedSumset t B :=
      ha (mem_arithmeticProgression.mpr ⟨i, i.isLt, rfl⟩)
    have hxsum : (x : ℤ) ∈ restrictedSumset r T := hX x.property
    have hadd : a + (q : ℤ) * (i : ℕ) + (x : ℤ) ∈
        restrictedSumset (t + r) (B ∪ T) :=
      add_restrictedSumsets_disjoint_modularStructure hBT hz hxsum
    have hfill := add_sum_mem_restrictedSumset_of_subset_sdiff hBTA hW' hadd
    rw [hlayer] at hfill
    simpa [F, add_assoc, add_left_comm, add_comm] using hfill
  have hFinj : Function.Injective F := by
    rintro ⟨x, i⟩ ⟨y, j⟩ heq
    have hresEq : ((x : ℤ) : ZMod q) = ((y : ℤ) : ZMod q) := by
      have heq' := congrArg (fun z : ℤ ↦ (z : ZMod q)) heq
      simpa [F] using heq'
    have hxy : (x : ℤ) = (y : ℤ) := hres x.property y.property hresEq
    have hijZ : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
      have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
      have hmul : (q : ℤ) * ((i : ℕ) : ℤ) =
          (q : ℤ) * ((j : ℕ) : ℤ) := by
        dsimp [F] at heq
        rw [hxy] at heq
        omega
      exact mul_left_cancel₀ hqZ hmul
    have hij : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijZ
    exact Prod.ext (Subtype.ext hxy) (Fin.ext hij)
  let P : Finset ℤ := Finset.univ.image F
  have hPcard : P.card = X.card * L := by
    change (Finset.univ.image F).card = X.card * L
    rw [Finset.card_image_of_injective _ hFinj]
    simp
  have hPsub : P ⊆ restrictedSumset s A := by
    intro z hz
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hz
    exact hFmem p
  rw [← hPcard]
  exact Finset.card_le_card hPsub

/-- Same-layer packing for a complete coset of a subgroup of `ZMod q`.

The input `hcover` supplies an actual fixed-cardinality restricted sum for
every element of the subgroup.  Choosing one such sum for every subgroup
element gives distinct residues, hence distinct translates of the long
`q`-progression.  This is the capacity step which bounds the order of the
rich-difference subgroup; it does not make any integer-alignment claim. -/
theorem subgroup_coverage_card_mul_le_restricted_layer
    {q t u s L filler : ℕ} {A B T : Finset ℤ}
    {H : AddSubgroup (ZMod q)} {base : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hcover : ∀ h : H, ∃ z ∈ restrictedSumset u T,
      (z : ZMod q) = base + (h : ZMod q))
    (hq : 0 < q) (hlayer : t + u + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    Nat.card H * L ≤ (restrictedSumset s A).card := by
  letI : NeZero q := ⟨hq.ne'⟩
  choose w hwmem hwcast using hcover
  have hwinj : Function.Injective w := by
    intro i j hij
    have hcastij : base + (i : ZMod q) = base + (j : ZMod q) := by
      rw [← hwcast i, ← hwcast j, hij]
    exact Subtype.ext (add_left_cancel hcastij)
  let X : Finset ℤ := Finset.univ.image w
  have hXcard : X.card = Nat.card H := by
    rw [Finset.card_image_of_injective _ hwinj]
    simp [Nat.card_eq_fintype_card]
  have hXsub : X ⊆ restrictedSumset u T := by
    intro z hz
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hz
    exact hwmem h
  have hXinj : Set.InjOn (fun z : ℤ ↦ (z : ZMod q)) X := by
    intro x hx y hy hxy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hy
    apply congrArg w
    apply Subtype.ext
    have : base + (i : ZMod q) = base + (j : ZMod q) := by
      rw [← hwcast i, ← hwcast j]
      exact hxy
    exact add_left_cancel this
  have hdiffCard : ((A \ B) \ T).card = (A \ B).card - T.card := by
    rw [Finset.card_sdiff_of_subset hT]
  have hfiller' : filler ≤ ((A \ B) \ T).card := by
    simpa [hdiffCard] using hfiller
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hfiller'
  have hcount := fixed_sum_representatives_card_mul_le_restricted_layer
    hBA hT hXsub hW hXinj hq (by simpa [hWcard] using hlayer) hAP
  simpa [hXcard] using hcount

/-- If a complete subgroup coset has fixed-layer restricted-sum witnesses and
that layer cannot hold `R` long-progression translates, the subgroup has
fewer than `R` elements. -/
theorem subgroup_card_lt_of_coverage_and_layer_capacity
    {q t u s L filler R : ℕ} {A B T : Finset ℤ}
    {H : AddSubgroup (ZMod q)} {base : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hcover : ∀ h : H, ∃ z ∈ restrictedSumset u T,
      (z : ZMod q) = base + (h : ZMod q))
    (hq : 0 < q) (hlayer : t + u + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hcapacity : (restrictedSumset s A).card < R * L) :
    Nat.card H < R := by
  have hcount := subgroup_coverage_card_mul_le_restricted_layer
    hBA hT hcover hq hlayer hfiller hAP
  by_contra hnot
  have hR : R ≤ Nat.card H := Nat.le_of_not_gt hnot
  have : R * L ≤ (restrictedSumset s A).card :=
    (Nat.mul_le_mul_right L hR).trans hcount
  omega

/-- The capacity contradiction which forces every rich-class difference to
have additive order below `R`.  If the order were at least `R`, the mixed
`R`-term sums supplied by `exists_mixed_restrictedSums_cast_injOn` would give
`R` distinct AP translates in the selected small layer. -/
theorem richDifference_addOrderOf_lt_of_layer_capacity
    {q R t s L filler : ℕ} {A B T : Finset ℤ} {g₀ g : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) (hq : 0 < q) (hgg₀ : g ≠ g₀)
    (hbase : R ≤ (residueFiber q T g₀).card)
    (hgfiber : R ≤ (residueFiber q T g).card)
    (hlayer : t + R + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    addOrderOf (g - g₀) < R := by
  by_contra hnot
  have horder : R ≤ addOrderOf (g - g₀) := Nat.le_of_not_gt hnot
  obtain ⟨X, hX, hXcard, hXinj⟩ :=
    exists_mixed_restrictedSums_cast_injOn hgg₀
      (by simpa [residueFiber] using hbase)
      (by simpa [residueFiber] using hgfiber) horder
  have hdiffCard : ((A \ B) \ T).card = (A \ B).card - T.card := by
    rw [Finset.card_sdiff_of_subset hT]
  have hfiller' : filler ≤ ((A \ B) \ T).card := by
    simpa [hdiffCard] using hfiller
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hfiller'
  have hcount := fixed_sum_representatives_card_mul_le_restricted_layer
    hBA hT hX hW hXinj hq (by simpa [hWcard] using hlayer) hAP
  rw [hXcard] at hcount
  omega

/-- All generators of the rich-difference subgroup have order below `R`
for the standard selector. -/
theorem selected_richDifference_orders_lt_of_layer_capacity
    {q R t s L filler : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) (hq : 0 < q) (hR : 0 < R)
    (hTbase : (residueFiber q T g₀).card = R * R)
    (hTother : ∀ g ∈ richResidues q R (A \ B), g ≠ g₀ →
      (residueFiber q T g).card = R)
    (hlayer : t + R + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    ∀ g ∈ (richResidues q R (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R := by
  intro g hg
  have hg' := Finset.mem_erase.mp hg
  apply richDifference_addOrderOf_lt_of_layer_capacity
    hBA hT hq hg'.1
  · rw [hTbase]
    nlinarith
  · rw [hTother g hg'.2 hg'.1]
  · exact hlayer
  · exact hfiller
  · exact hcapacity
  · exact hAP

/-- Two-scale form of
`selected_richDifference_orders_lt_of_layer_capacity`.  The definition of
richness may use a larger fibre threshold `F`; only `R` reserved elements in
the two fibres are needed for the mixed-sum collision. -/
theorem selected_richDifference_orders_lt_of_layer_capacity_general
    {q F R t s L filler : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) (hq : 0 < q)
    (hbase : R ≤ (residueFiber q T g₀).card)
    (hother : ∀ g ∈ (richResidues q F (A \ B)).erase g₀,
      R ≤ (residueFiber q T g).card)
    (hlayer : t + R + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    ∀ g ∈ (richResidues q F (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R := by
  intro g hg
  have hg' := Finset.mem_erase.mp hg
  exact richDifference_addOrderOf_lt_of_layer_capacity
    hBA hT hq hg'.1 hbase (hother g hg) hlayer hfiller hcapacity hAP

/-- Canonical-transversal specialization of
`representative_card_mul_le_restricted_layer`.  The numerical filler
hypothesis is exactly what is needed to raise the AP layer from `t` to `s`.
-/
theorem residueSupport_card_mul_le_restricted_layer
    {q t s L filler : ℕ} {A B : Finset ℤ}
    (hBA : B ⊆ A) (hq : 0 < q) (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - (residueSupport q (A \ B)).card)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    (residueSupport q (A \ B)).card * L ≤ (restrictedSumset s A).card := by
  let X := residueRepresentatives q (A \ B)
  have hXD : X ⊆ A \ B := residueRepresentatives_subset q (A \ B)
  have hdiffCard : ((A \ B) \ X).card =
      (A \ B).card - (residueSupport q (A \ B)).card := by
    rw [Finset.card_sdiff_of_subset hXD, residueRepresentatives_card]
  have hfiller' : filler ≤ ((A \ B) \ X).card := by
    simpa [hdiffCard] using hfiller
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hfiller'
  have hcount := representative_card_mul_le_restricted_layer
    hBA hXD hWsub (residueRepresentatives_cast_injOn q (A \ B)) hq
    (by simpa [hWcard] using hlayer) hAP
  calc
    (residueSupport q (A \ B)).card * L = X.card * L := by
      simp [X]
    _ ≤ (restrictedSumset s A).card := hcount

/-- If the prescribed target layer has capacity smaller than `R*L`, the
regular part represents fewer than `R` residues modulo the long AP step. -/
theorem residueSupport_card_lt_of_restricted_layer_capacity
    {q t s L filler R : ℕ} {A B : Finset ℤ}
    (hBA : B ⊆ A) (hq : 0 < q) (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - R)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hcapacity : (restrictedSumset s A).card < R * L) :
    (residueSupport q (A \ B)).card < R := by
  by_contra hnot
  have hRle : R ≤ (residueSupport q (A \ B)).card := Nat.le_of_not_gt hnot
  let Xall := residueRepresentatives q (A \ B)
  have hRXall : R ≤ Xall.card := by simpa [Xall] using hRle
  obtain ⟨X, hXXall, hXcard⟩ := Finset.exists_subset_card_eq hRXall
  have hXD : X ⊆ A \ B :=
    hXXall.trans (residueRepresentatives_subset q (A \ B))
  have hdiffCard : ((A \ B) \ X).card = (A \ B).card - R := by
    rw [Finset.card_sdiff_of_subset hXD, hXcard]
  have hfiller' : filler ≤ ((A \ B) \ X).card := by
    simpa [hdiffCard] using hfiller
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hfiller'
  have hres : Set.InjOn (fun x : ℤ ↦ (x : ZMod q)) X :=
    (residueRepresentatives_cast_injOn q (A \ B)).mono hXXall
  have hcount := representative_card_mul_le_restricted_layer
    hBA hXD hWsub hres hq (by simpa [hWcard] using hlayer) hAP
  rw [hXcard] at hcount
  omega

/-! ## Selecting representatives from the rich fibres -/

/-- Select `R²` elements from one distinguished rich residue class and `R`
elements from every other rich class.  This is the representative block used
to generate the subgroup in the modular argument. -/
theorem exists_rich_residue_selection
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q}
    (hg₀ : g₀ ∈ richResidues q R D)
    (hbase : R * R ≤ (residueFiber q D g₀).card) :
    ∃ T : Finset ℤ,
      T ⊆ richPart q R D ∧
      (residueFiber q T g₀).card = R * R ∧
      (∀ g ∈ richResidues q R D, g ≠ g₀ →
        (residueFiber q T g).card = R) ∧
      T.card ≤ R * R + (richResidues q R D).card * R := by
  let G := richResidues q R D
  have hchoose : ∀ g ∈ G, ∃ S : Finset ℤ,
      S ⊆ residueFiber q D g ∧
        S.card = if g = g₀ then R * R else R := by
    intro g hg
    by_cases hgg₀ : g = g₀
    · subst g
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hbase
      exact ⟨S, hSsub, by simpa⟩
    · have hrich : R ≤ (residueFiber q D g).card :=
        (mem_richResidues.mp hg).2
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hrich
      exact ⟨S, hSsub, by simpa [hgg₀]⟩
  choose S hSsub hScard using hchoose
  let S' : ZMod q → Finset ℤ := fun g ↦ if hg : g ∈ G then S g hg else ∅
  have hSsub' : ∀ g ∈ G, S' g ⊆ residueFiber q D g := by
    intro g hg
    simpa [S', hg] using hSsub g hg
  have hScard' : ∀ g ∈ G,
      (S' g).card = if g = g₀ then R * R else R := by
    intro g hg
    simpa [S', hg] using hScard g hg
  let T := G.biUnion S'
  have hSTfiber : ∀ g ∈ G, residueFiber q T g = S' g := by
    intro g hg
    ext x
    simp only [mem_residueFiber]
    constructor
    · rintro ⟨hxT, hxg⟩
      obtain ⟨r, hrG, hxr⟩ := Finset.mem_biUnion.mp hxT
      have hxr' := mem_residueFiber.mp (hSsub' r hrG hxr)
      have hrg : r = g := by rw [← hxr'.2, ← hxg]
      simpa [hrg] using hxr
    · intro hxS
      have hxTf : x ∈ T := Finset.mem_biUnion.mpr ⟨g, hg, hxS⟩
      have hxg : (x : ZMod q) = g :=
        (mem_residueFiber.mp (hSsub' g hg hxS)).2
      exact ⟨hxTf, hxg⟩
  have hTrich : T ⊆ richPart q R D := by
    intro x hxT
    obtain ⟨g, hgG, hxS⟩ := Finset.mem_biUnion.mp hxT
    have hxfiber := mem_residueFiber.mp (hSsub' g hgG hxS)
    exact mem_richPart.mpr
      ⟨hxfiber.1, by simpa [hxfiber.2] using (mem_richResidues.mp hgG).2⟩
  have hg₀G : g₀ ∈ G := hg₀
  refine ⟨T, hTrich, ?_, ?_, ?_⟩
  · rw [hSTfiber g₀ hg₀, hScard' g₀ hg₀]
    simp
  · intro g hg hne
    rw [hSTfiber g hg, hScard' g hg]
    simp [hne]
  · calc
      T.card ≤ ∑ g ∈ G, (S' g).card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ G, ((if g = g₀ then R * R else 0) + R) := by
        apply Finset.sum_le_sum
        intro g hg
        rw [hScard' g hg]
        split <;> omega
      _ = R * R + G.card * R := by
        simp [Finset.sum_add_distrib, hg₀G]

/-- General two-scale selector: take `baseCount` elements in one rich fibre
and `otherCount` in every other rich fibre. -/
theorem exists_rich_residue_selection_general
    {q F baseCount otherCount : ℕ} {D : Finset ℤ} {g₀ : ZMod q}
    (hg₀ : g₀ ∈ richResidues q F D)
    (hbase : baseCount ≤ (residueFiber q D g₀).card)
    (hother : otherCount ≤ F) :
    ∃ T : Finset ℤ,
      T ⊆ richPart q F D ∧
      (residueFiber q T g₀).card = baseCount ∧
      (∀ g ∈ richResidues q F D, g ≠ g₀ →
        (residueFiber q T g).card = otherCount) ∧
      T.card ≤ baseCount + (richResidues q F D).card * otherCount := by
  let G := richResidues q F D
  have hchoose : ∀ g ∈ G, ∃ S : Finset ℤ,
      S ⊆ residueFiber q D g ∧
        S.card = if g = g₀ then baseCount else otherCount := by
    intro g hg
    by_cases hgg₀ : g = g₀
    · subst g
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hbase
      exact ⟨S, hSsub, by simpa⟩
    · have hrich : F ≤ (residueFiber q D g).card :=
        (mem_richResidues.mp hg).2
      obtain ⟨S, hSsub, hScard⟩ :=
        Finset.exists_subset_card_eq (hother.trans hrich)
      exact ⟨S, hSsub, by simpa [hgg₀]⟩
  choose S hSsub hScard using hchoose
  let S' : ZMod q → Finset ℤ := fun g ↦ if hg : g ∈ G then S g hg else ∅
  let T := G.biUnion S'
  have hSsub' : ∀ g ∈ G, S' g ⊆ residueFiber q D g := by
    intro g hg
    simpa [S', hg] using hSsub g hg
  have hScard' : ∀ g ∈ G,
      (S' g).card = if g = g₀ then baseCount else otherCount := by
    intro g hg
    simpa [S', hg] using hScard g hg
  have hSTfiber : ∀ g ∈ G, residueFiber q T g = S' g := by
    intro g hg
    ext x
    simp only [mem_residueFiber]
    constructor
    · rintro ⟨hxT, hxg⟩
      obtain ⟨r, hrG, hxr⟩ := Finset.mem_biUnion.mp hxT
      have hxr' := mem_residueFiber.mp (hSsub' r hrG hxr)
      have hrg : r = g := by rw [← hxr'.2, ← hxg]
      simpa [hrg] using hxr
    · intro hxS
      exact ⟨Finset.mem_biUnion.mpr ⟨g, hg, hxS⟩,
        (mem_residueFiber.mp (hSsub' g hg hxS)).2⟩
  have hTrich : T ⊆ richPart q F D := by
    intro x hxT
    obtain ⟨g, hgG, hxS⟩ := Finset.mem_biUnion.mp hxT
    have hxfiber := mem_residueFiber.mp (hSsub' g hgG hxS)
    exact mem_richPart.mpr
      ⟨hxfiber.1, by simpa [hxfiber.2] using (mem_richResidues.mp hgG).2⟩
  have hg₀G : g₀ ∈ G := hg₀
  refine ⟨T, hTrich, ?_, ?_, ?_⟩
  · rw [hSTfiber g₀ hg₀, hScard' g₀ hg₀]
    simp
  · intro g hg hne
    rw [hSTfiber g hg, hScard' g hg]
    simp [hne]
  · calc
      T.card ≤ ∑ g ∈ G, (S' g).card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ G,
          ((if g = g₀ then baseCount else 0) + otherCount) := by
        apply Finset.sum_le_sum
        intro g hg
        rw [hScard' g hg]
        split <;> omega
      _ = baseCount + G.card * otherCount := by
        simp [Finset.sum_add_distrib, hg₀G]

theorem exists_rich_residue_selection_card_le_two_sq
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q}
    (hg₀ : g₀ ∈ richResidues q R D)
    (hbase : R * R ≤ (residueFiber q D g₀).card)
    (hG : (richResidues q R D).card < R) :
    ∃ T : Finset ℤ,
      T ⊆ richPart q R D ∧
      (residueFiber q T g₀).card = R * R ∧
      (∀ g ∈ richResidues q R D, g ≠ g₀ →
        (residueFiber q T g).card = R) ∧
      T.card ≤ 2 * (R * R) := by
  obtain ⟨T, hTrich, hTbase, hTother, hTcard⟩ :=
    exists_rich_residue_selection hg₀ hbase
  refine ⟨T, hTrich, hTbase, hTother, hTcard.trans ?_⟩
  nlinarith

/-! ## Disjoint fibre blocks for the short generator chain -/

/-- Partition a sufficiently large base residue fibre into `k` disjoint
`F`-blocks and choose one `F`-block from each of `k` distinct non-base
fibres.  The paired supports are pairwise disjoint.

This is the finite selection step needed by `AlignedBlockSum`: no disjoint
block family remains as an external hypothesis of the modular constructor. -/
theorem exists_pairwiseDisjoint_residueBlock_pairs
    {q k F : ℕ} {D : Finset ℤ} {g₀ : ZMod q}
    (g : Fin k → ZMod q) (hF : 0 < F)
    (hg_ne : ∀ i, g i ≠ g₀) (hg_inj : Function.Injective g)
    (hbase : k * F ≤ (residueFiber q D g₀).card)
    (hfiber : ∀ i, F ≤ (residueFiber q D (g i)).card) :
    ∃ X Y : Fin k → Finset ℤ,
      (∀ i, X i ⊆ residueFiber q D g₀ ∧ (X i).card = F) ∧
      (∀ i, Y i ⊆ residueFiber q D (g i) ∧ (Y i).card = F) ∧
      (Set.univ : Set (Fin k)).PairwiseDisjoint
        (fun i ↦ X i ∪ Y i) := by
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hbase
  let e : Fin (k * F) ≃o S := S.orderIsoOfFin hScard
  let blockIndex (i : Fin k) (j : Fin F) : Fin (k * F) :=
    ⟨(i : ℕ) * F + (j : ℕ), by
      have h₁ : (i : ℕ) * F + (j : ℕ) < ((i : ℕ) + 1) * F := by
        have := Nat.add_lt_add_left j.isLt ((i : ℕ) * F)
        simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using this
      have h₂ : ((i : ℕ) + 1) * F ≤ k * F :=
        Nat.mul_le_mul_right F (Nat.succ_le_iff.mpr i.isLt)
      exact h₁.trans_le h₂⟩
  let X : Fin k → Finset ℤ := fun i ↦
    Finset.univ.image fun j : Fin F ↦ (e (blockIndex i j) : ℤ)
  have hXcard : ∀ i, (X i).card = F := by
    intro i
    change (Finset.univ.image
      (fun j : Fin F ↦ (e (blockIndex i j) : ℤ))).card = F
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have heq : e (blockIndex i a) = e (blockIndex i b) :=
        Subtype.ext hab
      have hidx := e.injective heq
      apply Fin.ext
      have hval := Fin.ext_iff.mp hidx
      dsimp [blockIndex] at hval ⊢
      omega
  have hXsub : ∀ i, X i ⊆ residueFiber q D g₀ := by
    intro i z hz
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hz
    have hzS : (e (blockIndex i j) : ℤ) ∈ S := (e (blockIndex i j)).property
    exact hSsub hzS
  have hXdis : (Set.univ : Set (Fin k)).PairwiseDisjoint X := by
    intro i _hi j _hj hij
    change Disjoint (X i) (X j)
    rw [Finset.disjoint_left]
    intro z hzi hzj
    obtain ⟨a, _ha, hza⟩ := Finset.mem_image.mp hzi
    obtain ⟨b, _hb, hzb⟩ := Finset.mem_image.mp hzj
    have heq : e (blockIndex i a) = e (blockIndex j b) := by
      apply Subtype.ext
      rw [hza, hzb]
    have hidx := e.injective heq
    have hval := Fin.ext_iff.mp hidx
    dsimp [blockIndex] at hval
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hi1j : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
      have hmul : ((i : ℕ) + 1) * F ≤ (j : ℕ) * F :=
        Nat.mul_le_mul_right F hi1j
      have ha_lt : (i : ℕ) * F + (a : ℕ) < ((i : ℕ) + 1) * F := by
        have := Nat.add_lt_add_left a.isLt ((i : ℕ) * F)
        simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using this
      have hb_ge : (j : ℕ) * F ≤ (j : ℕ) * F + (b : ℕ) :=
        Nat.le_add_right _ _
      omega
    · have hj1i : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
      have hmul : ((j : ℕ) + 1) * F ≤ (i : ℕ) * F :=
        Nat.mul_le_mul_right F hj1i
      have hb_lt : (j : ℕ) * F + (b : ℕ) < ((j : ℕ) + 1) * F := by
        have := Nat.add_lt_add_left b.isLt ((j : ℕ) * F)
        simpa [Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using this
      have ha_ge : (i : ℕ) * F ≤ (i : ℕ) * F + (a : ℕ) :=
        Nat.le_add_right _ _
      omega
  have hYchoose : ∀ i : Fin k, ∃ Yi : Finset ℤ,
      Yi ⊆ residueFiber q D (g i) ∧ Yi.card = F := by
    intro i
    exact Finset.exists_subset_card_eq (hfiber i)
  choose Y hYsub hYcard using hYchoose
  refine ⟨X, Y, fun i ↦ ⟨hXsub i, hXcard i⟩,
    fun i ↦ ⟨hYsub i, hYcard i⟩, ?_⟩
  intro i _hi j _hj hij
  change Disjoint (X i ∪ Y i) (X j ∪ Y j)
  rw [Finset.disjoint_left]
  intro z hzi hzj
  rcases Finset.mem_union.mp hzi with hziX | hziY
  · rcases Finset.mem_union.mp hzj with hzjX | hzjY
    · exact (Finset.disjoint_left.mp
        (hXdis (Set.mem_univ i) (Set.mem_univ j) hij)) hziX hzjX
    · have hres₀ := (mem_residueFiber.mp (hXsub i hziX)).2
      have hresj := (mem_residueFiber.mp (hYsub j hzjY)).2
      exact (hg_ne j) (by rw [← hresj, ← hres₀])
  · rcases Finset.mem_union.mp hzj with hzjX | hzjY
    · have hresi := (mem_residueFiber.mp (hYsub i hziY)).2
      have hres₀ := (mem_residueFiber.mp (hXsub j hzjX)).2
      exact (hg_ne i) (by rw [← hres₀, ← hresi])
    · have hresi := (mem_residueFiber.mp (hYsub i hziY)).2
      have hresj := (mem_residueFiber.mp (hYsub j hzjY)).2
      apply hij
      apply hg_inj
      rw [← hresi, ← hresj]

/-- Every translate of an ordered mixed-sum path by a long progression and
a fixed filler lands in one prescribed restricted-sum layer.  This is the
set-theoretic input to the convex capacity lemma. -/
theorem orderedMixed_translates_mem_restricted_layer
    {q t F L s : ℕ} {A B X Y W : Finset ℤ} {a : ℤ}
    (hBA : B ⊆ A) (hXY : Disjoint X Y)
    (hXcard : X.card = F) (hYcard : Y.card = F)
    (hP : X ∪ Y ⊆ A \ B) (hW : W ⊆ (A \ B) \ (X ∪ Y))
    (hlayer : t + F + W.card = s)
    (ha : arithmeticProgression a (q : ℤ) L ⊆ restrictedSumset t B) :
    ∀ j ≤ F, ∀ k < L,
      (a + ∑ w ∈ W, w) + orderedMixedSum X Y F j +
        (q : ℤ) * (k : ℤ) ∈ restrictedSumset s A := by
  have hBP : B ∪ (X ∪ Y) ⊆ A :=
    Finset.union_subset hBA (hP.trans Finset.sdiff_subset)
  have hdisj : Disjoint B (X ∪ Y) := by
    rw [Finset.disjoint_left]
    intro z hzB hzP
    exact (Finset.mem_sdiff.mp (hP hzP)).2 hzB
  have hW' : W ⊆ A \ (B ∪ (X ∪ Y)) := by
    intro z hzW
    have hz := hW hzW
    have hzD := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1
    exact Finset.mem_sdiff.mpr
      ⟨hzD.1, fun hzU ↦ (Finset.mem_union.mp hzU).elim hzD.2
        (Finset.mem_sdiff.mp hz).2⟩
  intro j hj k hk
  have hbase : a + (q : ℤ) * (k : ℤ) ∈ restrictedSumset t B :=
    ha (mem_arithmeticProgression.mpr ⟨k, hk, rfl⟩)
  have hmix : orderedMixedSum X Y F j ∈ restrictedSumset F (X ∪ Y) := by
    exact mem_restrictedSumset.mpr
      ⟨orderedMixedSubset X Y F j,
        orderedMixedSubset_subset hXcard hYcard hj,
        card_orderedMixedSubset hXY hXcard hYcard hj, rfl⟩
  have hadd : a + (q : ℤ) * (k : ℤ) + orderedMixedSum X Y F j ∈
      restrictedSumset (t + F) (B ∪ (X ∪ Y)) :=
    add_restrictedSumsets_disjoint_modularStructure hdisj hbase hmix
  have hfill := add_sum_mem_restrictedSumset_of_subset_sdiff hBP hW' hadd
  rw [hlayer] at hfill
  simpa [add_assoc, add_left_comm, add_comm] using hfill

/-! ## The subgroup generated by rich-class differences -/

/-- The subgroup of `ZMod q` generated by differences between rich residues
and a distinguished base residue. -/
def richDifferenceSubgroup (q R : ℕ) (D : Finset ℤ) (g₀ : ZMod q) :
    AddSubgroup (ZMod q) :=
  AddSubgroup.closure
    (((↑((richResidues q R D).erase g₀) : Set (ZMod q))).image
      fun g ↦ g - g₀)

/-- The rich-difference subgroup has a duplicate-free generator family of
logarithmic length, indexed by `Fin k`, whose generators retain their source
rich residues.  This is the exact interface needed to select one ordered
mixed-sum block per generator. -/
theorem exists_short_richDifference_generator_family
    {q F : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    ∃ k : ℕ, ∃ delta g : Fin k → ZMod q,
      Function.Injective delta ∧
      Function.Injective g ∧
      (∀ i, g i ∈ (richResidues q F D).erase g₀ ∧
        delta i = g i - g₀) ∧
      AddSubgroup.closure (Set.range delta) =
        richDifferenceSubgroup q F D g₀ ∧
      2 ^ k ≤ Nat.card (richDifferenceSubgroup q F D g₀) ∧
      k ≤ Nat.log 2 (Nat.card (richDifferenceSubgroup q F D g₀)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let G := richResidues q F D
  let S : Finset (ZMod q) := (G.erase g₀).image fun g ↦ g - g₀
  obtain ⟨l, hlNodup, hlmem, hlchain, hlclosure, hlpow⟩ :=
    exists_strict_addGeneratorChain S
  let Lset : Finset (ZMod q) :=
    @List.toFinset (ZMod q) (fun a b ↦ Classical.propDecidable (a = b)) l
  let k := l.length
  let delta : Fin k → ZMod q := fun i ↦ l.get i
  let g : Fin k → ZMod q := fun i ↦ delta i + g₀
  have hdeltaInj : Function.Injective delta := by
    exact hlNodup.injective_get
  have hgInj : Function.Injective g := by
    intro i j hij
    apply hdeltaInj
    exact add_right_cancel hij
  have hsource : ∀ i, g i ∈ G.erase g₀ ∧ delta i = g i - g₀ := by
    intro i
    have hmemS : delta i ∈ S := by
      apply hlmem
      exact List.get_mem l i
    obtain ⟨r, hr, hre⟩ := Finset.mem_image.mp hmemS
    have hgr : g i = r := by
      dsimp [g]
      rw [← hre]
      exact sub_add_cancel r g₀
    refine ⟨by simpa [hgr] using hr, ?_⟩
    rw [hgr]
    exact hre.symm
  have hrange : Set.range delta = (↑Lset : Set (ZMod q)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      simpa [delta, Lset] using List.get_mem l i
    · intro hx
      have hxl : x ∈ l := by simpa [Lset] using hx
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxl
      exact ⟨i, by simpa [delta] using hi⟩
  have hSclosure : AddSubgroup.closure (↑S : Set (ZMod q)) =
      richDifferenceSubgroup q F D g₀ := by
    simp only [S, G, richDifferenceSubgroup, Finset.coe_image]
  have hlclosure' : AddSubgroup.closure (↑Lset : Set (ZMod q)) =
      AddSubgroup.closure (↑S : Set (ZMod q)) := by
    simpa [Lset] using hlclosure
  have hclosure : AddSubgroup.closure (Set.range delta) =
      richDifferenceSubgroup q F D g₀ := by
    exact (congrArg AddSubgroup.closure hrange).trans
      (hlclosure'.trans hSclosure)
  have hcardEq : Nat.card (AddSubgroup.closure (↑S : Set (ZMod q))) =
      Nat.card (richDifferenceSubgroup q F D g₀) :=
    congrArg (fun K : AddSubgroup (ZMod q) ↦ Nat.card K) hSclosure
  have hklog : k ≤ Nat.log 2
      (Nat.card (richDifferenceSubgroup q F D g₀)) := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two (hlpow.trans_eq hcardEq)
  exact ⟨k, delta, g, hdeltaInj, hgInj,
    fun i ↦ ⟨by simpa [G] using (hsource i).1, (hsource i).2⟩,
    hclosure, hlpow.trans_eq hcardEq, hklog⟩

/-- The join of the cyclic subgroups generated by a finite family is the
subgroup generated by the range of that family. -/
lemma iSup_zmultiples_eq_closure_range
    {q k : ℕ} (delta : Fin k → ZMod q) :
    (⨆ i, AddSubgroup.zmultiples (delta i)) =
      AddSubgroup.closure (Set.range delta) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact (le_iSup (fun i ↦ AddSubgroup.zmultiples (delta i)) i)
      (AddSubgroup.mem_zmultiples (delta i))

lemma richResidue_sub_mem_richDifferenceSubgroup
    {q R : ℕ} {D : Finset ℤ} {g₀ g : ZMod q}
    (hg : g ∈ richResidues q R D) :
    g - g₀ ∈ richDifferenceSubgroup q R D g₀ := by
  by_cases hgg₀ : g = g₀
  · subst g
    simp [richDifferenceSubgroup]
  · apply AddSubgroup.subset_closure
    exact ⟨g, by simpa [hgg₀] using hg, rfl⟩

/-- Every element of the rich part lies in the base coset of the generated
subgroup. -/
lemma richPart_cast_sub_mem_richDifferenceSubgroup
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} {x : ℤ}
    (hx : x ∈ richPart q R D) :
    (x : ZMod q) - g₀ ∈ richDifferenceSubgroup q R D g₀ := by
  apply richResidue_sub_mem_richDifferenceSubgroup
  apply mem_richResidues.mpr
  refine ⟨mem_residueSupport.mpr ⟨x, (mem_richPart.mp hx).1, rfl⟩, ?_⟩
  exact (mem_richPart.mp hx).2

/-- The order of the rich-difference subgroup divides the ambient modulus.
This is the Lagrange-theorem justification for the integer quotient used as
the refined structural step. -/
lemma richDifferenceSubgroup_card_dvd
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    Nat.card (richDifferenceSubgroup q R D g₀) ∣ q := by
  letI : NeZero q := ⟨hq.ne'⟩
  simpa using
    (richDifferenceSubgroup q R D g₀).card_addSubgroup_dvd_card

/-- Fixed-layer capacity bounds the rich-difference subgroup itself.

The coverage theorem in `ResidueSubgroup` supplies one actual `R²`-term
restricted sum for every element of the subgroup.  Packing the corresponding
long-progression translates then rules out `R` or more subgroup elements.
This statement deliberately concludes only a cardinality bound; the later
integer-alignment argument chooses correlated witnesses separately. -/
theorem richDifferenceSubgroup_card_lt_of_layer_capacity
    {q F R t s L filler : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) (hq : 0 < q)
    (hg₀ : g₀ ∈ richResidues q F (A \ B))
    (hG : (richResidues q F (A \ B)).card < R)
    (hbase : R * R ≤ (residueFiber q T g₀).card)
    (hfiber : ∀ g ∈ (richResidues q F (A \ B)).erase g₀,
      R ≤ (residueFiber q T g).card)
    (horder : ∀ g ∈ (richResidues q F (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R)
    (hlayer : t + R * R + filler = s)
    (hfiller : filler ≤ (A \ B).card - T.card)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hAP : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    Nat.card (richDifferenceSubgroup q F (A \ B) g₀) < R := by
  let G := richResidues q F (A \ B)
  let H := richDifferenceSubgroup q F (A \ B) g₀
  have hcoverRaw : ∀ h ∈ H, ∃ z ∈ restrictedSumset (R * R) T,
      (z : ZMod q) = (R * R) • g₀ + h := by
    apply restrictedSumset_sq_covers_differenceSubgroup hq hg₀ hG
    · simpa [residueFiber] using hbase
    · intro g hg
      simpa [residueFiber] using hfiber g hg
    · exact horder
  have hcover : ∀ h : H, ∃ z ∈ restrictedSumset (R * R) T,
      (z : ZMod q) = (R * R) • g₀ + (h : ZMod q) := by
    intro h
    exact hcoverRaw h h.property
  exact subgroup_card_lt_of_coverage_and_layer_capacity
    hBA hT hcover hq hlayer hfiller hAP hcapacity

/-- The refined step attached to `H` is `q/|H|`. -/
def richDifferenceStep (q R : ℕ) (D : Finset ℤ) (g₀ : ZMod q) : ℕ :=
  q / Nat.card (richDifferenceSubgroup q R D g₀)

lemma richDifferenceStep_mul_card
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    richDifferenceStep q R D g₀ *
        Nat.card (richDifferenceSubgroup q R D g₀) = q := by
  exact Nat.div_mul_cancel (richDifferenceSubgroup_card_dvd hq)

lemma richDifferenceStep_pos
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    0 < richDifferenceStep q R D g₀ := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hcardpos : 0 < Nat.card (richDifferenceSubgroup q R D g₀) :=
    Nat.card_pos
  have hcardle : Nat.card (richDifferenceSubgroup q R D g₀) ≤ q :=
    Nat.le_of_dvd hq (richDifferenceSubgroup_card_dvd hq)
  exact Nat.div_pos hcardle hcardpos

/-- Membership in a finite additive subgroup of `ZMod q` forces divisibility
by `q/|H|` for every integral lift.  This is the cyclic subgroup
classification in exactly the arithmetic form needed below. -/
theorem richDifferenceStep_dvd_int_of_cast_mem
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) {z : ℤ}
    (hz : (z : ZMod q) ∈ richDifferenceSubgroup q R D g₀) :
    (richDifferenceStep q R D g₀ : ℤ) ∣ z := by
  letI : NeZero q := ⟨hq.ne'⟩
  let H := richDifferenceSubgroup q R D g₀
  let h := Nat.card H
  let d := richDifferenceStep q R D g₀
  have hhpos : 0 < h := Nat.card_pos
  have hsmulSubtype : h • (⟨(z : ZMod q), hz⟩ : H) = 0 := by
    exact card_nsmul_eq_zero'
  have hsmul : h • (z : ZMod q) = 0 := by
    exact congrArg Subtype.val hsmulSubtype
  have hzmod : (((h : ℤ) * z : ℤ) : ZMod q) = 0 := by
    simpa [nsmul_eq_mul] using hsmul
  have hqdiv : (q : ℤ) ∣ (h : ℤ) * z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzmod
  obtain ⟨c, hc⟩ := hqdiv
  refine ⟨c, ?_⟩
  have hdh : d * h = q := richDifferenceStep_mul_card hq
  have hhZ : (h : ℤ) ≠ 0 := by exact_mod_cast hhpos.ne'
  apply mul_left_cancel₀ hhZ
  calc
    (h : ℤ) * z = (q : ℤ) * c := hc
    _ = ((d * h : ℕ) : ℤ) * c := by rw [hdh]
    _ = (h : ℤ) * ((d : ℤ) * c) := by push_cast; ring

/-- The rich part is contained in a single residue class modulo the refined
step `q/|H|`. -/
theorem richPart_isDifferenceDivisor_richDifferenceStep
    {q R : ℕ} {D : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    IsDifferenceDivisor (richDifferenceStep q R D g₀) (richPart q R D) := by
  intro x hx y hy
  have hxH := richPart_cast_sub_mem_richDifferenceSubgroup (g₀ := g₀) hx
  have hyH := richPart_cast_sub_mem_richDifferenceSubgroup (g₀ := g₀) hy
  have hxyH : ((x - y : ℤ) : ZMod q) ∈ richDifferenceSubgroup q R D g₀ := by
    have := (richDifferenceSubgroup q R D g₀).sub_mem hxH hyH
    simpa only [Int.cast_sub, sub_sub_sub_cancel_right] using this
  exact richDifferenceStep_dvd_int_of_cast_mem hq hxyH

/-- Once `B` and every poor fibre have been made exceptional, every remaining
element belongs to the rich part, independently of the selected set `T`. -/
lemma sdiff_seed_poor_selected_subset_richPart
    (q R : ℕ) (A B T : Finset ℤ) :
    A \ (B ∪ poorPart q R (A \ B) ∪ T) ⊆ richPart q R (A \ B) := by
  intro x hx
  have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
  have hxnot : x ∉ B ∪ poorPart q R (A \ B) ∪ T :=
    (Finset.mem_sdiff.mp hx).2
  have hxB : x ∉ B := by
    intro hxB
    exact hxnot (Finset.mem_union_left _ (Finset.mem_union_left _ hxB))
  have hxD : x ∈ A \ B := Finset.mem_sdiff.mpr ⟨hxA, hxB⟩
  have hxpoor : x ∉ poorPart q R (A \ B) := by
    intro hp
    exact hxnot (Finset.mem_union_left _ (Finset.mem_union_right _ hp))
  apply mem_richPart.mpr
  refine ⟨hxD, ?_⟩
  by_contra hlt
  exact hxpoor (mem_poorPart.mpr ⟨hxD, Nat.lt_of_not_ge hlt⟩)

/-- Therefore the common-residue conclusion required by the packaged
structure theorem is a consequence of the generated subgroup, not an extra
assumption. -/
theorem modularRegular_isDifferenceDivisor_richDifferenceStep
    {q R : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q} (hq : 0 < q) :
    IsDifferenceDivisor (richDifferenceStep q R (A \ B) g₀)
      (A \ (B ∪ poorPart q R (A \ B) ∪ T)) := by
  intro x hx y hy
  exact richPart_isDifferenceDivisor_richDifferenceStep hq x
    (sdiff_seed_poor_selected_subset_richPart q R A B T hx) y
    (sdiff_seed_poor_selected_subset_richPart q R A B T hy)

/-! ## Combining the long progression with a subgroup block -/

/-- If a `t`-sum layer on `B` contains a `q=d*h` progression and a disjoint
`u`-sum layer on `T` contains one complete `d`-block of `h` terms, their
fixed-cardinality sums contain a `d`-progression with `h*L` terms. -/
theorem ContainsAP.combine_complete_block
    {B T : Finset ℤ} {t u d q h L : ℕ}
    (hBT : Disjoint B T) (hh : 0 < h) (hq : q = d * h)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T) (d : ℤ) h) :
    ContainsAP (restrictedSumset (t + u) (B ∪ T)) (d : ℤ) (h * L) := by
  obtain ⟨a, ha⟩ := hlong
  obtain ⟨b, hb⟩ := hblock
  refine ⟨a + b, ?_⟩
  intro z hz
  obtain ⟨k, hk, rfl⟩ := mem_arithmeticProgression.mp hz
  let i := k / h
  let j := k % h
  have hj : j < h := by
    exact Nat.mod_lt _ hh
  have hi : i < L := by
    dsimp [i]
    exact (Nat.div_lt_iff_lt_mul hh).mpr (by simpa [Nat.mul_comm] using hk)
  have hmemA : a + (q : ℤ) * (i : ℤ) ∈ restrictedSumset t B :=
    ha (mem_arithmeticProgression.mpr ⟨i, hi, rfl⟩)
  have hmemB : b + (d : ℤ) * (j : ℤ) ∈ restrictedSumset u T :=
    hb (mem_arithmeticProgression.mpr ⟨j, hj, rfl⟩)
  have hadd :
      (a + (q : ℤ) * (i : ℤ)) + (b + (d : ℤ) * (j : ℤ)) ∈
        restrictedSumset (t + u) (B ∪ T) := by
    exact add_restrictedSumsets_disjoint_modularStructure hBT hmemA hmemB
  have hkdecomp : j + h * i = k := by
    dsimp [i, j]
    exact Nat.mod_add_div k h
  have hkdecompZ : (j : ℤ) + (h : ℤ) * (i : ℤ) = (k : ℤ) := by
    exact_mod_cast hkdecomp
  have hvalue :
      (a + (q : ℤ) * (i : ℤ)) + (b + (d : ℤ) * (j : ℤ)) =
        a + b + (d : ℤ) * (k : ℤ) := by
    rw [hq]
    push_cast
    rw [← hkdecompZ]
    ring
  rw [← hvalue]
  exact hadd

lemma restrictedSumset_mem_nonneg_le_mul
    {N r : ℕ} {T : Finset ℤ} (hT : T ⊆ ambient N) {z : ℤ}
    (hz : z ∈ restrictedSumset r T) :
    0 ≤ z ∧ z ≤ (r : ℤ) * (N : ℤ) := by
  obtain ⟨C, hCT, hCcard, rfl⟩ := mem_restrictedSumset.mp hz
  constructor
  · apply Finset.sum_nonneg
    intro x hx
    have hxone : 1 ≤ x := (mem_ambient.mp (hT (hCT hx))).1
    omega
  · calc
      ∑ x ∈ C, x ≤ ∑ _x ∈ C, (N : ℤ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (mem_ambient.mp (hT (hCT hx))).2
      _ = (r : ℤ) * (N : ℤ) := by simp [hCcard]

/-- Turn the actual fixed-layer subgroup coverage into an integer
progression.  The only quantitative loss is the explicit quotient-span
allowance `R²*N/q+1`; no residue-coverage or progression conclusion is
assumed. -/
theorem ContainsAP.combine_richDifferenceSubgroup
    {N q R t L K : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q}
    (hA : A ⊆ ambient N) (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hq : 0 < q) (hg₀ : g₀ ∈ richResidues q R (A \ B))
    (hG : (richResidues q R (A \ B)).card < R)
    (hbase : R * R ≤ (residueFiber q T g₀).card)
    (hfiber : ∀ g ∈ (richResidues q R (A \ B)).erase g₀,
      R ≤ (residueFiber q T g).card)
    (horder : ∀ g ∈ (richResidues q R (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hfit : R * R * N / q + 1 + K ≤ L) :
    ContainsAP (restrictedSumset (t + R * R) (B ∪ T))
      (richDifferenceStep q R (A \ B) g₀ : ℤ)
      (Nat.card (richDifferenceSubgroup q R (A \ B) g₀) * K) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let H := richDifferenceSubgroup q R (A \ B) g₀
  let h := Nat.card H
  let d := richDifferenceStep q R (A \ B) g₀
  have hh : 0 < h := Nat.card_pos
  have hfactor : q = d * h := by
    simpa [H, h, d] using
      (richDifferenceStep_mul_card (R := R) (D := A \ B) (g₀ := g₀) hq).symm
  have hTambient : T ⊆ ambient N :=
    hT.trans Finset.sdiff_subset |>.trans hA
  obtain ⟨w, hw⟩ := exists_restrictedSumset_sq_residue_block
    (G := richResidues q R (A \ B)) (T := T) hq hg₀ hG
      (by simpa [residueFiber] using hbase)
      (by intro g hg; simpa [residueFiber] using hfiber g hg) horder
  have hwmem : ∀ j : Fin h, w j ∈ restrictedSumset (R * R) T := by
    intro j
    simpa [H, h, d, richDifferenceSubgroup, richDifferenceStep] using (hw j).1
  have hwcast : ∀ j : Fin h,
      (w j : ZMod q) = (R * R) • g₀ + ((d * (j : ℕ) : ℕ) : ZMod q) := by
    intro j
    simpa [H, h, d, richDifferenceSubgroup, richDifferenceStep] using (hw j).2
  obtain ⟨z, hzform⟩ :=
    exists_integer_lifts_of_residue_block hq ((R * R) • g₀) w hwcast
  let c : ℤ := ((((R * R) • g₀).val : ℕ) : ℤ)
  have hcbounds : 0 ≤ c ∧ c < q := by
    constructor
    · dsimp [c]
      positivity
    · simpa [c] using (show (((R * R) • g₀).val : ℤ) < q by exact_mod_cast
        ((R * R) • g₀).val_lt)
  have hdjlt : ∀ j : Fin h, (d : ℤ) * (j : ℕ) < q := by
    intro j
    have hj : d * (j : ℕ) < q := by
      rw [hfactor]
      exact Nat.mul_lt_mul_of_pos_left j.isLt (richDifferenceStep_pos hq)
    exact_mod_cast hj
  have hzlo : ∀ j : Fin h, (-1 : ℤ) ≤ z j := by
    intro j
    have hw0 := (restrictedSumset_mem_nonneg_le_mul hTambient (hwmem j)).1
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have := hdjlt j
    rw [hzform j] at hw0
    nlinarith
  let M : ℕ := R * R * N / q
  have hzhi : ∀ j : Fin h, z j ≤ (M : ℤ) := by
    intro j
    have hwbd := (restrictedSumset_mem_nonneg_le_mul hTambient (hwmem j)).2
    have hc0 := hcbounds.1
    have hdj0 : 0 ≤ (d : ℤ) * (j : ℕ) := by positivity
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have hqzle : (q : ℤ) * z j ≤ ((R * R * N : ℕ) : ℤ) := by
      have heq : (q : ℤ) * z j = w j - c - (d : ℤ) * (j : ℕ) := by
        rw [hzform j]
        ring
      calc
        (q : ℤ) * z j = w j - c - (d : ℤ) * (j : ℕ) := heq
        _ ≤ w j := by nlinarith
        _ ≤ (R * R : ℤ) * N := hwbd
        _ = ((R * R * N : ℕ) : ℤ) := by norm_num
    by_cases hzneg : z j < 0
    · have hM0 : (0 : ℤ) ≤ (M : ℤ) := by positivity
      exact hzneg.le.trans hM0
    · have hz0 : 0 ≤ z j := le_of_not_gt hzneg
      have hzcast : ((z j).toNat : ℤ) = z j := Int.toNat_of_nonneg hz0
      have hqzle' : (q : ℤ) * ((z j).toNat : ℤ) ≤
          ((R * R * N : ℕ) : ℤ) := by simpa [hzcast] using hqzle
      have hmulNat : (z j).toNat * q ≤ R * R * N := by
        have : q * (z j).toNat ≤ R * R * N := by exact_mod_cast hqzle'
        simpa [Nat.mul_comm] using this
      have hdivNat : (z j).toNat ≤ R * R * N / q :=
        (Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hmulNat)
      rw [← hzcast]
      exact_mod_cast (show (z j).toNat ≤ M by simpa [M] using hdivNat)
  have hfit' : (((M : ℤ) - (-1)).toNat) + K ≤ L := by
    have heq : (M : ℤ) - (-1) = ((M + 1 : ℕ) : ℤ) := by push_cast; ring
    have hspan : ((M : ℤ) - (-1)).toNat = M + 1 := by rw [heq]; simp
    rw [hspan]
    simpa [M] using hfit
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro x hxB hxT'
    exact (Finset.mem_sdiff.mp (hT hxT')).2 hxB
  simpa [H, h, d] using
    ContainsAP.combine_residue_witnesses hBT hh hfactor hlong w z hwmem hzform
      hzlo hzhi hfit'

/-- A regular part lying in one residue modulo the AP difference has at most
`d` elements once the exceptional restricted layer contains a `d`-AP longer
than the ambient interval.  Otherwise a subset of size equal to the additive
order of the common residue has sum divisible by `d`, and the modular
collision obstruction applies. -/
theorem regular_card_le_step_of_long_progression
    {N d t L : ℕ} {A C : Finset ℤ}
    (hA : IsBoundedAdmissible N A) (hCA : C ⊆ A)
    (hd : 0 < d) (ht : 0 < t) (hNL : N < L)
    (hAP : ContainsAP (restrictedSumset t C) (d : ℤ) L)
    (hregular : IsDifferenceDivisor d (A \ C)) :
    (A \ C).card ≤ d := by
  letI : NeZero d := ⟨hd.ne'⟩
  by_contra hnot
  have hdcard : d < (A \ C).card := Nat.lt_of_not_ge hnot
  have hregne : (A \ C).Nonempty := Finset.card_pos.mp (hd.trans hdcard)
  obtain ⟨a, ha⟩ := hregne
  let r : ZMod d := (a : ZMod d)
  let e : ℕ := addOrderOf r
  have hepos : 0 < e := addOrderOf_pos r
  have hediv : e ∣ d := by
    simpa [e] using addOrderOf_dvd_natCard r
  have heled : e ≤ d := Nat.le_of_dvd hd hediv
  have hecard : e ≤ (A \ C).card := heled.trans hdcard.le
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hecard
  have hcast : ∀ x ∈ S, (x : ZMod d) = r := by
    intro x hx
    obtain ⟨c, hc⟩ := hregular x (hSsub hx) a ha
    have hz : (((x - a : ℤ) : ℤ) : ZMod d) = 0 := by
      rw [hc]
      push_cast
      simp
    simpa [r, Int.cast_sub, sub_eq_zero] using hz
  have hsumcast : (((∑ x ∈ S, x : ℤ) : ℤ) : ZMod d) = 0 := by
    calc
      (((∑ x ∈ S, x : ℤ) : ℤ) : ZMod d) =
          ∑ x ∈ S, (x : ZMod d) := by push_cast; rfl
      _ = ∑ _x ∈ S, r := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hcast x hx
      _ = S.card • r := by simp
      _ = 0 := by
        rw [hScard]
        dsimp [e]
        exact addOrderOf_nsmul_eq_zero r
  have hsumdiv : (d : ℤ) ∣ ∑ x ∈ S, x :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hsumcast
  obtain ⟨z, hsumz⟩ := hsumdiv
  have hposA : ∀ x ∈ A, 0 < x := by
    intro x hx
    exact (mem_ambient.mp (hA.1 hx)).1.trans_lt' (by omega)
  have hSne : S.Nonempty := Finset.card_pos.mp (hScard.trans_gt hepos)
  have hsumpos : 0 < ∑ x ∈ S, x :=
    sum_pos_of_subset hposA (hSsub.trans Finset.sdiff_subset) hSne
  have hsumle : ∑ x ∈ S, x ≤ (e : ℤ) * (N : ℤ) := by
    calc
      ∑ x ∈ S, x ≤ ∑ _x ∈ S, (N : ℤ) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (mem_ambient.mp (hA.1 (Finset.sdiff_subset (hSsub hx)))).2
      _ = (e : ℤ) * (N : ℤ) := by simp [hScard]
  have hznonneg : 0 ≤ z := by
    have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
    nlinarith
  have hzle : z ≤ (N : ℤ) := by
    have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
    have heledZ : (e : ℤ) ≤ (d : ℤ) := by exact_mod_cast heled
    have hNnonneg : 0 ≤ (N : ℤ) := by positivity
    nlinarith
  have hzabs : z.natAbs < L := by
    have habsZ : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hznonneg
    have hzabsleZ : (z.natAbs : ℤ) ≤ (N : ℤ) := by simpa [habsZ] using hzle
    have : z.natAbs ≤ N := by exact_mod_cast hzabsleZ
    exact this.trans_lt hNL
  exact no_short_zero_residue_outside_subset_sum hA.2 hCA ht hAP hSsub hSne
    hsumz hzabs

/-! ## A common residue in a bounded interval is a short progression -/

/-- A bounded set all of whose pairwise differences are divisible by `d`
is contained in a `N/d+1` term progression of difference `d`. -/
theorem containedInAP_of_bounded_of_isDifferenceDivisor
    {N d : ℕ} {S : Finset ℤ} (hd : 0 < d)
    (hS : S ⊆ ambient N) (hdiv : IsDifferenceDivisor d S) :
    ∃ start : ℤ, ContainedInAP S start d (N / d + 1) := by
  by_cases hSne : S.Nonempty
  · let start : ℤ := S.min' hSne
    refine ⟨start, hd, ?_⟩
    intro x hx
    have hstart : start ∈ S := Finset.min'_mem S hSne
    have hsx : start ≤ x := Finset.min'_le S x hx
    obtain ⟨z, hz⟩ := hdiv x hx start hstart
    have hznonneg : 0 ≤ z := by
      have hdZ : 0 < (d : ℤ) := by exact_mod_cast hd
      nlinarith
    let i : ℕ := z.toNat
    have hiz : (i : ℤ) = z := by
      exact Int.toNat_of_nonneg hznonneg
    have hxN : x ≤ (N : ℤ) := (mem_ambient.mp (hS hx)).2
    have hstartpos : 1 ≤ start := (mem_ambient.mp (hS hstart)).1
    have himulZ : (i : ℤ) * (d : ℤ) ≤ (N : ℤ) := by
      rw [hiz]
      nlinarith
    have himul : i * d ≤ N := by exact_mod_cast himulZ
    have hi : i < N / d + 1 := by
      have : i ≤ N / d := (Nat.le_div_iff_mul_le hd).2 himul
      omega
    refine ⟨i, hi, ?_⟩
    rw [hiz]
    nlinarith
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    exact ⟨0, by simp [ContainedInAP, hd]⟩

/-! ## Packaged finite exceptional-set construction -/

/-- The explicit exceptional set obtained from a seed `B`, all poor residue
fibres of `D=A\B`, and a selected representative set `T` from the rich part.
-/
def modularExceptional (q R : ℕ) (A B T : Finset ℤ) : Finset ℤ :=
  B ∪ poorPart q R (A \ B) ∪ T

lemma modularExceptional_subset
    {q R : ℕ} {A B T : Finset ℤ}
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) :
    modularExceptional q R A B T ⊆ A := by
  apply Finset.union_subset
  · exact Finset.union_subset hBA
      ((poorPart_subset q R (A \ B)).trans Finset.sdiff_subset)
  · exact hT.trans Finset.sdiff_subset

lemma modularExceptional_card_le
    {q R : ℕ} {A B T : Finset ℤ} :
    (modularExceptional q R A B T).card ≤
      B.card + (residueSupport q (A \ B)).card * (R - 1) + T.card := by
  calc
    (modularExceptional q R A B T).card
        ≤ (B ∪ poorPart q R (A \ B)).card + T.card := by
          simpa [modularExceptional] using
            Finset.card_union_le (B ∪ poorPart q R (A \ B)) T
    _ ≤ (B.card + (poorPart q R (A \ B)).card) + T.card :=
      Nat.add_le_add_right (Finset.card_union_le B (poorPart q R (A \ B))) _
    _ ≤ B.card + (residueSupport q (A \ B)).card * (R - 1) + T.card :=
      Nat.add_le_add_right
        (Nat.add_le_add_left (poorPart_card_le q R (A \ B)) B.card) T.card

lemma modularExceptional_card_le_by_poorResidues
    {q R : ℕ} {A B T : Finset ℤ} :
    (modularExceptional q R A B T).card ≤
      B.card + (poorResidues q R (A \ B)).card * (R - 1) + T.card := by
  calc
    (modularExceptional q R A B T).card
        ≤ (B ∪ poorPart q R (A \ B)).card + T.card := by
          simpa [modularExceptional] using
            Finset.card_union_le (B ∪ poorPart q R (A \ B)) T
    _ ≤ (B.card + (poorPart q R (A \ B)).card) + T.card :=
      Nat.add_le_add_right (Finset.card_union_le B (poorPart q R (A \ B))) _
    _ ≤ B.card + (poorResidues q R (A \ B)).card * (R - 1) + T.card :=
      Nat.add_le_add_right
        (Nat.add_le_add_left
          (poorPart_card_le_poorResidues q R (A \ B)) B.card) T.card

/-- With fewer than `R` represented classes, the poor fibres together with
the standard rich-fibre selection cost at most `2R²` elements.  This is the
DF95 exceptional-set accounting; it uses the partition of the support into
poor and rich classes rather than charging every class twice. -/
lemma modularExceptional_card_le_two_sq
    {q R : ℕ} {A B T : Finset ℤ}
    (hsupport : (residueSupport q (A \ B)).card < R)
    (hTcard : T.card ≤ R * R + (richResidues q R (A \ B)).card * R) :
    (modularExceptional q R A B T).card ≤ B.card + 2 * (R * R) := by
  let p := (poorResidues q R (A \ B)).card
  let g := (richResidues q R (A \ B)).card
  let v := (residueSupport q (A \ B)).card
  have hpg : p + g = v := by
    simpa [p, g, v] using poorResidues_card_add_richResidues_card q R (A \ B)
  have hpR : p * (R - 1) ≤ p * R :=
    Nat.mul_le_mul_left p (Nat.sub_le R 1)
  have hvR : v * R + R * R ≤ 2 * (R * R) := by
    have hvle : v ≤ R := hsupport.le
    nlinarith
  calc
    (modularExceptional q R A B T).card
        ≤ B.card + p * (R - 1) + T.card := by
          simpa [p] using modularExceptional_card_le_by_poorResidues
    _ ≤ B.card + p * R + (R * R + g * R) :=
      Nat.add_le_add (Nat.add_le_add_left hpR B.card) hTcard
    _ = B.card + ((p + g) * R + R * R) := by
      rw [Nat.add_mul]
      omega
    _ = B.card + (v * R + R * R) := by rw [hpg]
    _ ≤ B.card + 2 * (R * R) := Nat.add_le_add_left hvR B.card

lemma modularExceptional_card_le_sq
    {q R : ℕ} {A B T : Finset ℤ}
    (hsupport : (residueSupport q (A \ B)).card < R) :
    (modularExceptional q R A B T).card ≤ B.card + R * R + T.card := by
  calc
    (modularExceptional q R A B T).card
        ≤ B.card + (residueSupport q (A \ B)).card * (R - 1) + T.card :=
      modularExceptional_card_le
    _ ≤ B.card + R * R + T.card := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      exact Nat.mul_le_mul hsupport.le (Nat.sub_le R 1)

/-- Two-parameter exceptional-set bound for support count `R` and fibre
threshold `F`. -/
lemma modularExceptional_card_le_mul
    {q R F : ℕ} {A B T : Finset ℤ}
    (hsupport : (residueSupport q (A \ B)).card < R) :
    (modularExceptional q F A B T).card ≤ B.card + R * F + T.card := by
  calc
    (modularExceptional q F A B T).card
        ≤ B.card + (residueSupport q (A \ B)).card * (F - 1) + T.card :=
      modularExceptional_card_le
    _ ≤ B.card + R * F + T.card := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      calc
        (residueSupport q (A \ B)).card * (F - 1)
            ≤ (residueSupport q (A \ B)).card * F :=
          Nat.mul_le_mul_left _ (Nat.sub_le F 1)
        _ ≤ R * F := Nat.mul_le_mul_right F hsupport.le

/-- **Finite modular structure theorem.**

Starting with the exceptional seed `B`, discard all poor `q`-residue fibres
and add a selected set `T` from the rich fibres.  A complete subgroup block
in one fixed restricted layer of `T` refines the long difference from `q` to
`d`; a common `d`-residue for the unselected part gives the required short
containing progression.  All supports, layers, progression lengths, and
cardinality losses are explicit.
-/
theorem finite_modular_structure
    {N q d h R t u L : ℕ} {A B T : Finset ℤ}
    (hA : IsBoundedAdmissible N A)
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hd : 0 < d) (hh : 0 < h) (hq : q = d * h)
    (hsupport : (residueSupport q (A \ B)).card < R)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T) (d : ℤ) h)
    (hregular : IsDifferenceDivisor d (A \ modularExceptional q R A B T)) :
    ∃ C' start,
      C' = modularExceptional q R A B T ∧
      C' ⊆ A ∧
      C'.card ≤ B.card + R * R + T.card ∧
      ContainsAP (restrictedSumset (t + u) C') (d : ℤ) (h * L) ∧
      ContainedInAP (A \ C') start d (N / d + 1) := by
  let C' := modularExceptional q R A B T
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro x hxB hxT
    exact (Finset.mem_sdiff.mp (hT hxT)).2 hxB
  have hcombine := hlong.combine_complete_block hBT hh hq hblock
  have hBTsub : B ∪ T ⊆ C' := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxT'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxB)
    · exact Finset.mem_union_right _ hxT'
  have hlongC : ContainsAP (restrictedSumset (t + u) C') (d : ℤ) (h * L) :=
    hcombine.mono (restrictedSumset_mono_modularStructure hBTsub)
  have hCsub : C' ⊆ A := modularExceptional_subset hBA hT
  have hregBound : A \ C' ⊆ ambient N :=
    Finset.sdiff_subset.trans hA.1
  obtain ⟨start, hshort⟩ :=
    containedInAP_of_bounded_of_isDifferenceDivisor hd hregBound hregular
  refine ⟨C', start, rfl, hCsub, ?_, hlongC, hshort⟩
  exact modularExceptional_card_le_sq hsupport

/-- Same-layer-capacity version of `finite_modular_structure`.  Here the
few-residue hypothesis is not assumed: it is derived by packing the AP
translates, with a fixed filler, into the explicitly prescribed small layer
`sˆA`. -/
theorem finite_modular_structure_of_layer_capacity
    {N q d h R t u L s filler : ℕ} {A B T : Finset ℤ}
    (hA : IsBoundedAdmissible N A)
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hd : 0 < d) (hh : 0 < h) (hq : q = d * h)
    (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - R)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T) (d : ℤ) h)
    (hregular : IsDifferenceDivisor d (A \ modularExceptional q R A B T)) :
    ∃ C' start,
      C' = modularExceptional q R A B T ∧
      C' ⊆ A ∧
      C'.card ≤ B.card + R * R + T.card ∧
      ContainsAP (restrictedSumset (t + u) C') (d : ℤ) (h * L) ∧
      ContainedInAP (A \ C') start d (N / d + 1) := by
  have hqpos : 0 < q := by
    rw [hq]
    exact Nat.mul_pos hd hh
  have hsupport : (residueSupport q (A \ B)).card < R :=
    residueSupport_card_lt_of_restricted_layer_capacity
      hBA hqpos hlayer hfiller hlong hcapacity
  exact finite_modular_structure hA hBA hT hd hh hq hsupport
    hlong hblock hregular

/-- Sharp exceptional-cardinality version of the same-layer-capacity
theorem.  The standard rich-fibre selector satisfies `hTcard`, and the poor
and rich residue-class costs then total at most `2R²`. -/
theorem finite_modular_structure_of_layer_capacity_two_sq
    {N q d h R t u L s filler : ℕ} {A B T : Finset ℤ}
    (hA : IsBoundedAdmissible N A)
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hTcard : T.card ≤ R * R + (richResidues q R (A \ B)).card * R)
    (hd : 0 < d) (hh : 0 < h) (hq : q = d * h)
    (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - R)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T) (d : ℤ) h)
    (hregular : IsDifferenceDivisor d (A \ modularExceptional q R A B T)) :
    ∃ C' start,
      C' = modularExceptional q R A B T ∧
      C' ⊆ A ∧
      C'.card ≤ B.card + 2 * (R * R) ∧
      ContainsAP (restrictedSumset (t + u) C') (d : ℤ) (h * L) ∧
      ContainedInAP (A \ C') start d (N / d + 1) := by
  have hqpos : 0 < q := by
    rw [hq]
    exact Nat.mul_pos hd hh
  have hsupport : (residueSupport q (A \ B)).card < R :=
    residueSupport_card_lt_of_restricted_layer_capacity
      hBA hqpos hlayer hfiller hlong hcapacity
  obtain ⟨C', start, rfl, hCsub, _hCcard, hlongC, hshort⟩ :=
    finite_modular_structure hA hBA hT hd hh hq hsupport hlong hblock hregular
  exact ⟨modularExceptional q R A B T, start, rfl, hCsub,
    modularExceptional_card_le_two_sq hsupport hTcard, hlongC, hshort⟩

/-- Exact residue-level certificate, with no unjustified conversion of a
complete residue block into an integer arithmetic progression.  The witness
shifts `z` expose precisely the remaining alignment data. -/
theorem finite_DF95_modular_residue_certificate
    {q R t L s supportFiller orderFiller : ℕ} {A B : Finset ℤ}
    (hBA : B ⊆ A) (hq : 0 < q) (hR : 0 < R)
    (hlargeD : R * R + R * R * R < (A \ B).card)
    (hsupportLayer : t + (supportFiller + 1) = s)
    (hsupportFiller : supportFiller ≤ (A \ B).card - R)
    (horderLayer : t + R + orderFiller = s)
    (horderFiller : orderFiller + 2 * (R * R) ≤ (A \ B).card)
    (hsmall : (restrictedSumset s A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L) :
    ∃ C T d h c, ∃ w z : Fin h → ℤ,
      T ⊆ C ∧ C ⊆ A ∧
      C.card ≤ B.card + 2 * (R * R) ∧
      0 < d ∧ q = d * h ∧
      IsDifferenceDivisor d (A \ C) ∧
      (∀ j, w j ∈ restrictedSumset (R * R) T) ∧
      (∀ j, w j = c + (d : ℤ) * (j : ℕ) + (q : ℤ) * z j) := by
  have hsupport : (residueSupport q (A \ B)).card < R :=
    residueSupport_card_lt_of_restricted_layer_capacity hBA hq hsupportLayer
      hsupportFiller hlong hsmall
  obtain ⟨g₀, hg₀, hbase⟩ :=
    exists_richResidue_with_sq_fiber hR hsupport hlargeD
  have hG : (richResidues q R (A \ B)).card < R :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hsupport
  obtain ⟨T, hTrich, hTbase, hTother, hTcard⟩ :=
    exists_rich_residue_selection hg₀ hbase
  have hTD : T ⊆ A \ B :=
    hTrich.trans (richPart_subset q R (A \ B))
  have hTtwo : T.card ≤ 2 * (R * R) := by
    calc
      T.card ≤ R * R + (richResidues q R (A \ B)).card * R := hTcard
      _ ≤ 2 * (R * R) := by nlinarith [hG.le]
  have horderFill : orderFiller ≤ (A \ B).card - T.card := by omega
  have horders : ∀ g ∈ (richResidues q R (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R :=
    selected_richDifference_orders_lt_of_layer_capacity hBA hTD hq hR hTbase
      hTother horderLayer horderFill hsmall hlong
  let H := richDifferenceSubgroup q R (A \ B) g₀
  let h := Nat.card H
  let d := richDifferenceStep q R (A \ B) g₀
  letI : NeZero q := ⟨hq.ne'⟩
  have hd : 0 < d := richDifferenceStep_pos hq
  have hfactor : q = d * h := by
    simpa [H, h, d] using
      (richDifferenceStep_mul_card (R := R) (D := A \ B) (g₀ := g₀) hq).symm
  obtain ⟨w, hw⟩ := exists_restrictedSumset_sq_residue_block
    (G := richResidues q R (A \ B)) (T := T) hq hg₀ hG
      (by simpa [residueFiber] using hTbase.ge)
      (by intro g hg; simpa [residueFiber] using
        (show R ≤ (residueFiber q T g).card by
          rw [hTother g (Finset.mem_erase.mp hg).2 (Finset.mem_erase.mp hg).1]))
      horders
  have hwcast : ∀ j : Fin h,
      (w j : ZMod q) = (R * R) • g₀ + ((d * (j : ℕ) : ℕ) : ZMod q) := by
    intro j
    simpa [H, h, d, richDifferenceSubgroup, richDifferenceStep] using (hw j).2
  obtain ⟨z, hz⟩ :=
    exists_integer_lifts_of_residue_block hq ((R * R) • g₀) w hwcast
  let c : ℤ := (((R * R) • g₀).val : ℕ)
  let C := modularExceptional q R A B T
  have hTC : T ⊆ C := fun _ hx ↦ Finset.mem_union_right _ hx
  have hCA : C ⊆ A := modularExceptional_subset hBA hTD
  have hCcard : C.card ≤ B.card + 2 * (R * R) :=
    modularExceptional_card_le_two_sq hsupport hTcard
  have hregular : IsDifferenceDivisor d (A \ C) := by
    simpa [C, d, modularExceptional] using
      (modularRegular_isDifferenceDivisor_richDifferenceStep
        (A := A) (B := B) (T := T) (g₀ := g₀) hq)
  refine ⟨C, T, d, h, c, w, z, hTC, hCA, hCcard, hd, hfactor, hregular,
    ?_, ?_⟩
  · intro j
    simpa [H, h, d, richDifferenceSubgroup, richDifferenceStep] using (hw j).1
  · intro j
    simpa [c] using hz j

/-- **End-to-end finite DF95 modular decomposition (with explicit alignment
budget).**

This theorem derives, rather than assumes, the few residue classes, a rich
base fibre, the representative selector, the generator-order bounds, the
subgroup residue block, the refined difference, and the common residue of the
regular part.  `hquotientFit` is the honest integer-alignment cost omitted in
the printed residue-level argument.  Finally the endpoint-absorption theorem
turns the common residue into a genuinely short `U`-term progression.
-/
theorem finite_DF95_modular_structure_of_crude_alignment_fit
    {N q R t L K sFew supportFiller orderFiller
      endpointT U sEnd endpointFiller : ℕ}
    {A B : Finset ℤ}
    (hA : IsBoundedAdmissible N A) (hBA : B ⊆ A)
    (hq : 0 < q) (hR : 0 < R)
    (hlargeD : R * R + R * R * R < (A \ B).card)
    (hsupportLayer : t + (supportFiller + 1) = sFew)
    (hsupportFiller : supportFiller ≤ (A \ B).card - R)
    (horderLayer : t + R + orderFiller = sFew)
    (horderFiller : orderFiller + 2 * (R * R) ≤ (A \ B).card)
    (hsmallFew : (restrictedSumset sFew A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hquotientFit : R * R * N / q + 1 + K ≤ L)
    (hendpointT : 0 < endpointT)
    (hendpointLayer : (t + R * R) + (endpointFiller + endpointT) = sEnd)
    (hendpointRoom : endpointFiller + (B.card + 2 * (R * R)) +
      2 * endpointT ≤ A.card)
    (hsmallEnd : (restrictedSumset sEnd A).card < endpointT * min U K) :
    ∃ C' start d h,
      C' ⊆ A ∧
      C'.card ≤ B.card + 2 * (R * R) + 2 * endpointT ∧
      0 < d ∧ q = d * h ∧
      ContainsAP (restrictedSumset (t + R * R) C') (d : ℤ) (h * K) ∧
      ContainedInAP (A \ C') start d U := by
  have hsupport : (residueSupport q (A \ B)).card < R :=
    residueSupport_card_lt_of_restricted_layer_capacity hBA hq hsupportLayer
      hsupportFiller hlong hsmallFew
  obtain ⟨g₀, hg₀, hbase⟩ :=
    exists_richResidue_with_sq_fiber hR hsupport hlargeD
  have hG : (richResidues q R (A \ B)).card < R := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hsupport
  obtain ⟨T, hTrich, hTbase, hTother, hTcard⟩ :=
    exists_rich_residue_selection hg₀ hbase
  have hTD : T ⊆ A \ B :=
    hTrich.trans (richPart_subset q R (A \ B))
  have hTtwo : T.card ≤ 2 * (R * R) := by
    have hGle : (richResidues q R (A \ B)).card ≤ R := hG.le
    calc
      T.card ≤ R * R + (richResidues q R (A \ B)).card * R := hTcard
      _ ≤ 2 * (R * R) := by nlinarith
  have horderFill : orderFiller ≤ (A \ B).card - T.card := by omega
  have horders : ∀ g ∈ (richResidues q R (A \ B)).erase g₀,
      addOrderOf (g - g₀) < R :=
    selected_richDifference_orders_lt_of_layer_capacity hBA hTD hq hR hTbase
      hTother horderLayer horderFill hsmallFew hlong
  letI : NeZero q := ⟨hq.ne'⟩
  let H := richDifferenceSubgroup q R (A \ B) g₀
  let h := Nat.card H
  let d := richDifferenceStep q R (A \ B) g₀
  have hh : 0 < h := Nat.card_pos
  have hd : 0 < d := richDifferenceStep_pos hq
  have hfactor : q = d * h := by
    simpa [H, h, d] using
      (richDifferenceStep_mul_card (R := R) (D := A \ B) (g₀ := g₀) hq).symm
  have hlongBT : ContainsAP (restrictedSumset (t + R * R) (B ∪ T))
      (d : ℤ) (h * K) := by
    simpa [H, h, d] using
      ContainsAP.combine_richDifferenceSubgroup hA.1 hBA hTD hq hg₀ hG
        (by rw [hTbase])
        (by intro g hg; rw [hTother g (Finset.mem_erase.mp hg).2
          (Finset.mem_erase.mp hg).1]) horders hlong hquotientFit
  let C₀ := modularExceptional q R A B T
  have hC₀A : C₀ ⊆ A := modularExceptional_subset hBA hTD
  have hC₀card : C₀.card ≤ B.card + 2 * (R * R) :=
    modularExceptional_card_le_two_sq hsupport hTcard
  have hBTC₀ : B ∪ T ⊆ C₀ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxT'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxB)
    · exact Finset.mem_union_right _ hxT'
  have hlongC₀ : ContainsAP (restrictedSumset (t + R * R) C₀)
      (d : ℤ) (h * K) :=
    hlongBT.mono (restrictedSumset_mono_modularStructure hBTC₀)
  have hregular : IsDifferenceDivisor d (A \ C₀) := by
    simpa [C₀, d, modularExceptional] using
      (modularRegular_isDifferenceDivisor_richDifferenceStep
        (A := A) (B := B) (T := T) (g₀ := g₀) hq)
  have hregcard : (A \ C₀).card + C₀.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hC₀A
  have hendpointFill : endpointFiller ≤ (A \ C₀).card - 2 * endpointT := by
    omega
  have hsmallEnd' : (restrictedSumset sEnd A).card <
      endpointT * min U (h * K) := by
    have hKle : K ≤ h * K := by nlinarith
    have hmin : min U K ≤ min U (h * K) := by omega
    exact hsmallEnd.trans_le
      (Nat.mul_le_mul_left endpointT hmin)
  obtain ⟨C', start, _hC₀C', hC'A, hC'card, hlongC', hshort⟩ :=
    exists_regular_span_after_absorbing_extremes hC₀A hd hendpointT
      hendpointLayer hendpointFill hsmallEnd' hlongC₀ hregular
  refine ⟨C', start, d, h, hC'A, ?_, hd, hfactor, hlongC', hshort⟩
  omega

/-- Strengthened finite endpoint exposing the lower bound on the structural
step supplied by admissibility: the regular part has at most `d` elements.
-/
theorem finite_modular_structure_of_layer_capacity_with_step_bound
    {N q d h R t u L s filler : ℕ} {A B T : Finset ℤ}
    (hA : IsBoundedAdmissible N A)
    (hBA : B ⊆ A) (hT : T ⊆ A \ B)
    (hd : 0 < d) (hh : 0 < h) (hq : q = d * h)
    (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - R)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T) (d : ℤ) h)
    (hregular : IsDifferenceDivisor d (A \ modularExceptional q R A B T))
    (htotal : 0 < t + u) (hNL : N < h * L) :
    ∃ C' start,
      C' = modularExceptional q R A B T ∧
      C' ⊆ A ∧
      C'.card ≤ B.card + R * R + T.card ∧
      0 < d ∧
      ContainsAP (restrictedSumset (t + u) C') (d : ℤ) (h * L) ∧
      (A \ C').card ≤ d ∧
      ContainedInAP (A \ C') start d (N / d + 1) := by
  obtain ⟨C', start, rfl, hCsub, hCcard, hlongC, hshort⟩ :=
    finite_modular_structure_of_layer_capacity hA hBA hT hd hh hq
      hlayer hfiller hcapacity hlong hblock hregular
  have hregcard : (A \ modularExceptional q R A B T).card ≤ d :=
    regular_card_le_step_of_long_progression hA hCsub hd htotal hNL hlongC hregular
  exact ⟨modularExceptional q R A B T, start, rfl, hCsub, hCcard, hd,
    hlongC, hregcard, hshort⟩

/-- Subgroup-specialized endpoint.  The common-residue conclusion and the
identity `q=d*|H|` are derived internally from the rich-difference subgroup;
the only remaining group-combinatorial input is the complete fixed-layer
subgroup block furnished by the selected representatives. -/
theorem finite_modular_structure_of_richSubgroupBlock
    {N q R t u L s filler : ℕ} {A B T : Finset ℤ} {g₀ : ZMod q}
    (hA : IsBoundedAdmissible N A)
    (hBA : B ⊆ A) (hT : T ⊆ A \ B) (hq : 0 < q)
    (hlayer : t + (filler + 1) = s)
    (hfiller : filler ≤ (A \ B).card - R)
    (hcapacity : (restrictedSumset s A).card < R * L)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) L)
    (hblock : ContainsAP (restrictedSumset u T)
      (richDifferenceStep q R (A \ B) g₀ : ℤ)
      (Nat.card (richDifferenceSubgroup q R (A \ B) g₀)))
    (htotal : 0 < t + u)
    (hNL : N < Nat.card (richDifferenceSubgroup q R (A \ B) g₀) * L) :
    ∃ C' start,
      C' = modularExceptional q R A B T ∧
      C' ⊆ A ∧
      C'.card ≤ B.card + R * R + T.card ∧
      0 < richDifferenceStep q R (A \ B) g₀ ∧
      ContainsAP (restrictedSumset (t + u) C')
        (richDifferenceStep q R (A \ B) g₀ : ℤ)
        (Nat.card (richDifferenceSubgroup q R (A \ B) g₀) * L) ∧
      (A \ C').card ≤ richDifferenceStep q R (A \ B) g₀ ∧
      ContainedInAP (A \ C') start
        (richDifferenceStep q R (A \ B) g₀)
        (N / richDifferenceStep q R (A \ B) g₀ + 1) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hd : 0 < richDifferenceStep q R (A \ B) g₀ := richDifferenceStep_pos hq
  have hh : 0 < Nat.card (richDifferenceSubgroup q R (A \ B) g₀) := Nat.card_pos
  have hfactor : q = richDifferenceStep q R (A \ B) g₀ *
      Nat.card (richDifferenceSubgroup q R (A \ B) g₀) :=
    (richDifferenceStep_mul_card hq).symm
  have hregular : IsDifferenceDivisor (richDifferenceStep q R (A \ B) g₀)
      (A \ modularExceptional q R A B T) := by
    simpa [modularExceptional] using
      (modularRegular_isDifferenceDivisor_richDifferenceStep
        (A := A) (B := B) (T := T) (g₀ := g₀) hq)
  exact finite_modular_structure_of_layer_capacity_with_step_bound
    hA hBA hT hd hh hfactor hlayer hfiller hcapacity hlong hblock hregular
      htotal hNL

/-! ## Repaired two-scale modular constructor -/

/-- End-to-end finite modular decomposition with correlated integer lifts.

The support scale is `R`, while fibres retained for alignment have size `F`.
An irredundant generator family of length `k ≤ J` is selected internally.
For each generator, a convex ordered mixed-sum path and the capacity of the
selected layer produce a bounded complete cyclic-coset block.  The disjoint
blocks are then summed and aligned before being combined with the original
long `q`-progression.  Thus no residue-coverage-to-integer-progression step is
assumed.

All filler hypotheses are expressed as subtraction-free room bounds for the
single target layer `s`. -/
theorem finite_DF95_modular_structure_aligned
    {q R F J t ell K s : ℕ} {A B : Finset ℤ}
    (hBA : B ⊆ A) (hq : 0 < q) (hR : 0 < R)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) ell)
    (hsupportLayer : t + 1 ≤ s)
    (hsupportRoom : s - (t + 1) + R ≤ (A \ B).card)
    (hcapacity : (restrictedSumset s A).card < R * ell)
    (hrichMass : R * F + R * (R * R + J * F) < (A \ B).card)
    (hRF : R ≤ F)
    (horderLayer : t + R ≤ s)
    (horderRoom : s - (t + R) + 2 * (R * R) ≤ (A \ B).card)
    (hsubgroupLayer : t + R * R ≤ s)
    (hsubgroupRoom : s - (t + R * R) + 2 * (R * R) ≤ (A \ B).card)
    (halignLayer : t + F ≤ s)
    (halignRoom : s - (t + F) + 2 * F ≤ (A \ B).card)
    (hdouble : 2 * R ≤ F)
    (halignMargin : 2 * (restrictedSumset s A).card <
      (F - 2 * R + 2) * ell)
    (hlog : Nat.log 2 R ≤ J)
    (hfit : 2 * J * (restrictedSumset s A).card +
      (F - 2 * R + 2) * K ≤ (F - 2 * R + 2) * ell) :
    ∃ (k : ℕ) (C : Finset ℤ) (d : ℕ),
      k ≤ J ∧
      C ⊆ A ∧
      C.card ≤ B.card + R * F + 2 * k * F ∧
      0 < d ∧
      ContainsAP (restrictedSumset (t + k * F) C) (d : ℤ) K ∧
      IsDifferenceDivisor d (A \ C) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let D := A \ B
  have hF : 0 < F := hR.trans_le hRF
  have hsupportEq : t + (s - (t + 1) + 1) = s := by omega
  have hsupportFill : s - (t + 1) ≤ D.card - R := by
    dsimp [D]
    omega
  have hsupport : (residueSupport q D).card < R := by
    apply residueSupport_card_lt_of_restricted_layer_capacity
      hBA hq hsupportEq hsupportFill hlong
    simpa [D] using hcapacity
  let M := R * R + J * F
  have hM : 0 < M := by
    dsimp [M]
    nlinarith
  obtain ⟨g₀, hg₀, hg₀fiber⟩ :=
    exists_richResidue_with_large_fiber hF hM hsupport (by
      simpa [D, M] using hrichMass)
  have hG : (richResidues q F D).card < R := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt hsupport
  have hbaseSq : R * R ≤ (residueFiber q D g₀).card := by
    exact (Nat.le_add_right (R * R) (J * F)).trans hg₀fiber
  obtain ⟨T₀, hT₀rich, hT₀base, hT₀other, hT₀card⟩ :=
    exists_rich_residue_selection_general hg₀ hbaseSq hRF
  have hT₀D : T₀ ⊆ D := hT₀rich.trans (richPart_subset q F D)
  have hT₀card' : T₀.card ≤ 2 * (R * R) := by
    calc
      T₀.card ≤ R * R + (richResidues q F D).card * R := hT₀card
      _ ≤ R * R + R * R := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right R hG.le) (R * R)
      _ = 2 * (R * R) := by omega
  have hT₀baseR : R ≤ (residueFiber q T₀ g₀).card := by
    rw [hT₀base]
    nlinarith
  have hT₀otherR : ∀ g ∈ (richResidues q F D).erase g₀,
      R ≤ (residueFiber q T₀ g).card := by
    intro g hg
    have hg' := Finset.mem_erase.mp hg
    rw [hT₀other g hg'.2 hg'.1]
  have horderEq : t + R + (s - (t + R)) = s := by omega
  have horderFill : s - (t + R) ≤ D.card - T₀.card := by
    dsimp [D] at horderRoom ⊢
    omega
  have horders : ∀ g ∈ (richResidues q F D).erase g₀,
      addOrderOf (g - g₀) < R := by
    apply selected_richDifference_orders_lt_of_layer_capacity_general
      hBA hT₀D hq hT₀baseR hT₀otherR horderEq horderFill
    · simpa [D] using hcapacity
    · exact hlong
  have hsubgroupEq : t + R * R + (s - (t + R * R)) = s := by omega
  have hsubgroupFill : s - (t + R * R) ≤ D.card - T₀.card := by
    dsimp [D] at hsubgroupRoom ⊢
    omega
  have hHcard : Nat.card (richDifferenceSubgroup q F D g₀) < R := by
    apply richDifferenceSubgroup_card_lt_of_layer_capacity
      hBA hT₀D hq hg₀ hG
    · simpa [hT₀base]
    · exact hT₀otherR
    · exact horders
    · exact hsubgroupEq
    · exact hsubgroupFill
    · simpa [D] using hcapacity
    · exact hlong
  obtain ⟨k, delta, g, hdeltaInj, hgInj, hgsource,
      hdeltaClosure, _hkpow, hklogH⟩ :=
    exists_short_richDifference_generator_family (D := D) (g₀ := g₀) hq
  have hkJ : k ≤ J := by
    exact hklogH.trans ((Nat.log_mono_right hHcard.le).trans hlog)
  have hg_ne : ∀ i, g i ≠ g₀ := fun i ↦
    (Finset.mem_erase.mp (hgsource i).1).1
  have hbaseBlocks : k * F ≤ (residueFiber q D g₀).card := by
    calc
      k * F ≤ J * F := Nat.mul_le_mul_right F hkJ
      _ ≤ M := by simp [M]
      _ ≤ (residueFiber q D g₀).card := hg₀fiber
  have hgenFibers : ∀ i, F ≤ (residueFiber q D (g i)).card := by
    intro i
    exact (mem_richResidues.mp (Finset.mem_erase.mp (hgsource i).1).2).2
  obtain ⟨X, Y, hX, hY, hpairwise⟩ :=
    exists_pairwiseDisjoint_residueBlock_pairs g hF hg_ne hgInj
      hbaseBlocks hgenFibers
  have hXY : ∀ i, Disjoint (X i) (Y i) := by
    intro i
    rw [Finset.disjoint_left]
    intro z hzX hzY
    have hz₀ := (mem_residueFiber.mp ((hX i).1 hzX)).2
    have hzg := (mem_residueFiber.mp ((hY i).1 hzY)).2
    exact (hg_ne i) (by rw [← hzg, ← hz₀])
  let P : Fin k → Finset ℤ := fun i ↦ X i ∪ Y i
  let T := (Finset.univ : Finset (Fin k)).biUnion P
  have hPD : ∀ i, P i ⊆ D := by
    intro i
    apply Finset.union_subset
    · intro z hz
      exact (mem_residueFiber.mp ((hX i).1 hz)).1
    · intro z hz
      exact (mem_residueFiber.mp ((hY i).1 hz)).1
  have hTD : T ⊆ D := by
    apply Finset.biUnion_subset.2
    intro i _hi
    exact hPD i
  have hPcard : ∀ i, (P i).card = 2 * F := by
    intro i
    dsimp [P]
    rw [Finset.card_union_of_disjoint (hXY i), (hX i).2, (hY i).2]
    omega
  have hTcard : T.card = 2 * k * F := by
    calc
      T.card = ∑ i : Fin k, (P i).card := by
        dsimp [T]
        rw [Finset.card_biUnion]
        simpa [P] using hpairwise
      _ = ∑ _i : Fin k, 2 * F := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hPcard i
      _ = 2 * k * F := by simp; ring
  have hTrich : T ⊆ richPart q F D := by
    intro z hzT
    obtain ⟨i, _hi, hzP⟩ := Finset.mem_biUnion.mp hzT
    rcases Finset.mem_union.mp hzP with hzX | hzY
    · have hz := mem_residueFiber.mp ((hX i).1 hzX)
      exact mem_richPart.mpr ⟨hz.1, by simpa [hz.2] using
        (mem_richResidues.mp hg₀).2⟩
    · have hz := mem_residueFiber.mp ((hY i).1 hzY)
      have hgrich := (Finset.mem_erase.mp (hgsource i).1).2
      exact mem_richPart.mpr ⟨hz.1, by simpa [hz.2] using
        (mem_richResidues.mp hgrich).2⟩
  obtain ⟨a, ha⟩ := hlong
  have halignOne : ∀ i : Fin k, ∃ Z : ℕ,
      Z < ell ∧
      (F - 2 * addOrderOf (g i - g₀) + 2) * Z ≤
        2 * (restrictedSumset s A).card ∧
      ∃ W : BoundedCosetWitnesses q F (P i)
          (AddSubgroup.zmultiples (g i - g₀)),
        W.upper - W.lower ≤ (q : ℤ) * (Z : ℤ) := by
    intro i
    have hPsub : P i ⊆ D := hPD i
    have hfillRoom : s - (t + F) ≤ D.card - (P i).card := by
      dsimp [D] at halignRoom ⊢
      rw [hPcard i]
      omega
    have hdiffCard : (D \ P i).card = D.card - (P i).card := by
      rw [Finset.card_sdiff_of_subset hPsub]
    have hfillRoom' : s - (t + F) ≤ (D \ P i).card := by
      simpa [hdiffCard] using hfillRoom
    obtain ⟨Wfill, hWfill, hWfillcard⟩ :=
      Finset.exists_subset_card_eq hfillRoom'
    have hlayer : t + F + Wfill.card = s := by
      rw [hWfillcard]
      omega
    have hU : ∀ j ≤ F, ∀ n < ell,
        (a + ∑ w ∈ Wfill, w) + orderedMixedSum (X i) (Y i) F j +
          (q : ℤ) * (n : ℤ) ∈ restrictedSumset s A := by
      apply orderedMixed_translates_mem_restricted_layer hBA (hXY i)
        (hX i).2 (hY i).2 hPsub hWfill hlayer ha
    have horderi : addOrderOf (g i - g₀) < R :=
      horders (g i) (hgsource i).1
    have hroomi : 2 * addOrderOf (g i - g₀) ≤ F := by
      have := Nat.mul_le_mul_left 2 horderi.le
      omega
    have hGi : F - 2 * R + 2 ≤
        F - 2 * addOrderOf (g i - g₀) + 2 := by omega
    have hmargini : 2 * (restrictedSumset s A).card <
        (F - 2 * addOrderOf (g i - g₀) + 2) * ell := by
      exact halignMargin.trans_le (Nat.mul_le_mul_right ell hGi)
    simpa [P] using
      exists_boundedCosetWitnesses_of_orderedMixed_capacity
        (a + ∑ w ∈ Wfill, w) hq (hXY i) (hX i).2 (hY i).2
        (fun z hz ↦ (mem_residueFiber.mp ((hX i).1 hz)).2)
        (fun z hz ↦ (mem_residueFiber.mp ((hY i).1 hz)).2)
        hroomi hU hmargini
  choose Z hZlt hZcost W hWdiam using halignOne
  let Hgen : Fin k → AddSubgroup (ZMod q) :=
    fun i ↦ AddSubgroup.zmultiples (g i - g₀)
  let Block : ∀ i, BoundedCosetBlock q (P i) F (Z i) (Hgen i) :=
    fun i ↦ BoundedCosetBlock.ofBoundedCosetWitnesses (W i) (hWdiam i)
  let Sgroup := blockSumSubgroup Hgen
  have hSgroup : Sgroup = richDifferenceSubgroup q F D g₀ := by
    calc
      Sgroup = ⨆ i, Hgen i := blockSumSubgroup_eq_iSup Hgen
      _ = AddSubgroup.closure (Set.range delta) := by
        simp only [Hgen, ← (hgsource _).2]
        exact iSup_zmultiples_eq_closure_range delta
      _ = richDifferenceSubgroup q F D g₀ := hdeltaClosure
  obtain ⟨Aligned⟩ :=
    nonempty_alignedResidueWitnesses_of_boundedCosetBlocks hq Block (by
      simpa [P] using hpairwise)
  have hAligned : AlignedResidueWitnesses q (k * F)
      (Nat.card (richDifferenceSubgroup q F D g₀))
      (q / Nat.card (richDifferenceSubgroup q F D g₀))
      (∑ i, Z i) T := by
    simpa [Block, Sgroup, hSgroup, T, P, Nat.mul_comm] using Aligned
  let Gcap := F - 2 * R + 2
  have hGcap : 0 < Gcap := by omega
  have hZfixed : ∀ i, Gcap * Z i ≤ 2 * (restrictedSumset s A).card := by
    intro i
    have horderi : addOrderOf (g i - g₀) < R :=
      horders (g i) (hgsource i).1
    have hGi : Gcap ≤ F - 2 * addOrderOf (g i - g₀) + 2 := by
      dsimp [Gcap]
      omega
    exact (Nat.mul_le_mul_right (Z i) hGi).trans (hZcost i)
  have hZsum : Gcap * (∑ i, Z i) ≤
      2 * k * (restrictedSumset s A).card := by
    calc
      Gcap * (∑ i, Z i) = ∑ i, Gcap * Z i := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin k, 2 * (restrictedSumset s A).card :=
        Finset.sum_le_sum fun i _hi ↦ hZfixed i
      _ = 2 * k * (restrictedSumset s A).card := by simp; ring
  have hlossFit : (∑ i, Z i) + K ≤ ell := by
    apply Nat.le_of_mul_le_mul_left _ hGcap
    calc
      Gcap * ((∑ i, Z i) + K) =
          Gcap * (∑ i, Z i) + Gcap * K := by rw [Nat.mul_add]
      _ ≤ 2 * k * (restrictedSumset s A).card + Gcap * K :=
        Nat.add_le_add_right hZsum _
      _ ≤ 2 * J * (restrictedSumset s A).card + Gcap * K := by
        have hk := Nat.mul_le_mul_right (2 * (restrictedSumset s A).card) hkJ
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          Nat.add_le_add_right hk (Gcap * K)
      _ ≤ Gcap * ell := by simpa [Gcap] using hfit
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro z hzB hzT
    exact (Finset.mem_sdiff.mp (hTD hzT)).2 hzB
  have hcombined := ContainsAP.combine_alignedResidueWitnesses
    hBT (⟨a, ha⟩ : ContainsAP (restrictedSumset t B) (q : ℤ) ell)
      hAligned hlossFit
  have hKle : K ≤ Nat.card (richDifferenceSubgroup q F D g₀) * K := by
    have hh : 1 ≤ Nat.card (richDifferenceSubgroup q F D g₀) := Nat.card_pos
    simpa using Nat.mul_le_mul_right K hh
  have hcombinedK := hcombined.of_length_le hKle
  let C := modularExceptional q F A B T
  let d := richDifferenceStep q F D g₀
  have hBTC : B ∪ T ⊆ C := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzB | hzT
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzB)
    · exact Finset.mem_union_right _ hzT
  have hlongC : ContainsAP (restrictedSumset (t + k * F) C) (d : ℤ) K := by
    have hm := ContainsAP.mono hcombinedK
      (restrictedSumset_mono_modularStructure hBTC)
    have hdEq : d =
        q / Nat.card (richDifferenceSubgroup q F D g₀) := rfl
    rw [hdEq]
    exact hm
  have hCsub : C ⊆ A := modularExceptional_subset hBA hTD
  have hCcard : C.card ≤ B.card + R * F + 2 * k * F := by
    calc
      C.card ≤ B.card + R * F + T.card := by
        simpa [C, D] using modularExceptional_card_le_mul
          (A := A) (B := B) (T := T) (F := F) hsupport
      _ = B.card + R * F + 2 * k * F := by rw [hTcard]
  have hd : 0 < d := by
    exact richDifferenceStep_pos (D := D) (R := F) (g₀ := g₀) hq
  have hregular : IsDifferenceDivisor d (A \ C) := by
    change IsDifferenceDivisor (richDifferenceStep q F D g₀)
      (A \ modularExceptional q F A B T)
    exact modularRegular_isDifferenceDivisor_richDifferenceStep
      (A := A) (B := B) (T := T) (R := F) (g₀ := g₀) hq
  exact ⟨k, C, d, hkJ, hCsub, hCcard, hd, hlongC, hregular⟩

/-- The complete finite DF95 modular-structure step.

This packages `finite_DF95_modular_structure_aligned` with the endpoint
absorption theorem.  The aligned construction may use fewer than `J`
generator blocks.  Before absorbing endpoints, we promote its progression to
the fixed layer `t + J * F` by adjoining an arbitrary disjoint set of
`(J-k)*F` regular elements.  Consequently the endpoint filler and room
hypotheses are independent of the existentially chosen `k`. -/
theorem finite_DF95_modular_structure
    {q R F J t ell K s T U : ℕ} {A B : Finset ℤ}
    (hBA : B ⊆ A) (hq : 0 < q) (hR : 0 < R) (ht : 0 < t)
    (hlong : ContainsAP (restrictedSumset t B) (q : ℤ) ell)
    (hsupportLayer : t + 1 ≤ s)
    (hsupportRoom : s - (t + 1) + R ≤ (A \ B).card)
    (hcapacity : (restrictedSumset s A).card < R * ell)
    (hrichMass : R * F + R * (R * R + J * F) < (A \ B).card)
    (hRF : R ≤ F)
    (horderLayer : t + R ≤ s)
    (horderRoom : s - (t + R) + 2 * (R * R) ≤ (A \ B).card)
    (hsubgroupLayer : t + R * R ≤ s)
    (hsubgroupRoom : s - (t + R * R) + 2 * (R * R) ≤ (A \ B).card)
    (halignLayer : t + F ≤ s)
    (halignRoom : s - (t + F) + 2 * F ≤ (A \ B).card)
    (hdouble : 2 * R ≤ F)
    (halignMargin : 2 * (restrictedSumset s A).card <
      (F - 2 * R + 2) * ell)
    (hlog : Nat.log 2 R ≤ J)
    (hfit : 2 * J * (restrictedSumset s A).card +
      (F - 2 * R + 2) * K ≤ (F - 2 * R + 2) * ell)
    (hT : 0 < T)
    (hendpointLayer : t + J * F + T ≤ s)
    (hendpointRoom :
      s - (t + J * F + T) + (B.card + R * F + 2 * J * F) + 2 * T ≤
        A.card)
    (hendpointCapacity : (restrictedSumset s A).card < T * min U K) :
    ∃ (C : Finset ℤ) (start : ℤ) (d : ℕ),
      C ⊆ A ∧
      C.card ≤ B.card + R * F + 2 * J * F + 2 * T ∧
      0 < d ∧
      0 < t + J * F ∧
      ContainsAP (restrictedSumset (t + J * F) C) (d : ℤ) K ∧
      ContainedInAP (A \ C) start d U := by
  obtain ⟨k, C₀, d, hkJ, hC₀A, hC₀card, hd, hlong₀, hregular₀⟩ :=
    finite_DF95_modular_structure_aligned hBA hq hR hlong
      hsupportLayer hsupportRoom hcapacity hrichMass hRF
      horderLayer horderRoom hsubgroupLayer hsubgroupRoom
      halignLayer halignRoom hdouble halignMargin hlog hfit
  let u := (J - k) * F
  have hku : k * F + u = J * F := by
    dsimp [u]
    rw [← Nat.add_mul]
    rw [Nat.add_sub_of_le hkJ]
  have hC₀u : C₀.card + u ≤ B.card + R * F + 2 * J * F := by
    have hkF : k * F ≤ J * F := Nat.mul_le_mul_right F hkJ
    calc
      C₀.card + u ≤ (B.card + R * F + 2 * k * F) + u :=
        Nat.add_le_add_right hC₀card u
      _ = B.card + R * F + (k * F + (k * F + u)) := by ring
      _ = B.card + R * F + (k * F + J * F) := by rw [hku]
      _ ≤ B.card + R * F + (J * F + J * F) :=
        Nat.add_le_add_left (Nat.add_le_add_right hkF (J * F)) _
      _ = B.card + R * F + 2 * J * F := by ring
  have huRoom : u ≤ (A \ C₀).card := by
    rw [Finset.card_sdiff_of_subset hC₀A]
    omega
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq huRoom
  have hEsub' : E ⊆ A \ C₀ := hEsub
  have hC₀E : Disjoint C₀ E := by
    rw [Finset.disjoint_left]
    intro x hxC hxE
    exact (Finset.mem_sdiff.mp (hEsub' hxE)).2 hxC
  have hEA : E ⊆ A := hEsub'.trans Finset.sdiff_subset
  have hEsum : ∑ x ∈ E, x ∈ restrictedSumset E.card E := by
    exact mem_restrictedSumset.mpr ⟨E, Finset.Subset.rfl, rfl, rfl⟩
  have hlongCE : ContainsAP
      (restrictedSumset ((t + k * F) + E.card) (C₀ ∪ E)) (d : ℤ) K :=
    ContainsAP.add_fixed_restrictedSum hC₀E hlong₀ hEsum
  let C₁ := C₀ ∪ E
  have hC₁A : C₁ ⊆ A := Finset.union_subset hC₀A hEA
  have hC₁cardEq : C₁.card = C₀.card + u := by
    dsimp [C₁]
    rw [Finset.card_union_of_disjoint hC₀E, hEcard]
  have hC₁card : C₁.card ≤ B.card + R * F + 2 * J * F := by
    rw [hC₁cardEq]
    exact hC₀u
  have hlong₁ : ContainsAP
      (restrictedSumset (t + J * F) C₁) (d : ℤ) K := by
    have hlayerEq : (t + k * F) + E.card = t + J * F := by
      rw [hEcard]
      omega
    simpa [C₁, hlayerEq] using hlongCE
  have hregular₁ : IsDifferenceDivisor d (A \ C₁) := by
    intro x hx y hy
    have hx' := Finset.mem_sdiff.mp hx
    have hy' := Finset.mem_sdiff.mp hy
    exact hregular₀ x
      (Finset.mem_sdiff.mpr ⟨hx'.1, fun hxC ↦ hx'.2
        (Finset.mem_union_left E hxC)⟩) y
      (Finset.mem_sdiff.mpr ⟨hy'.1, fun hyC ↦ hy'.2
        (Finset.mem_union_left E hyC)⟩)
  let filler := s - (t + J * F + T)
  have hfillLayer : (t + J * F) + (filler + T) = s := by
    dsimp [filler]
    omega
  have hfillRoom : filler ≤ (A \ C₁).card - 2 * T := by
    rw [Finset.card_sdiff_of_subset hC₁A]
    dsimp [filler]
    omega
  obtain ⟨C, start, _hC₁C, hCA, hCcard, hlongC, hshort⟩ :=
    exists_regular_span_after_absorbing_extremes hC₁A hd hT
      hfillLayer hfillRoom hendpointCapacity hlong₁ hregular₁
  refine ⟨C, start, d, hCA, ?_, hd, ?_, hlongC, hshort⟩
  · exact hCcard.trans (Nat.add_le_add_right hC₁card (2 * T))
  · exact ht.trans_le (Nat.le_add_right t (J * F))

end

end Erdos874
