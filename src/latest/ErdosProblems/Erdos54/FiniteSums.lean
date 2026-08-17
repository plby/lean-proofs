/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos54.Core
import Mathlib.Combinatorics.Additive.SubsetSum

/-!
# Finite distinct subset sums for Erdős Problem 54

This file contains the elementary subset-sum tools used in the
Conlon--Fox--Pham construction.  All sums are sums of subsets of a `Finset`,
so every summand is used at most once.  The two principal results are
Graham's interval-extension lemma and CFP Lemma 2.5, which says that adjoining
a modulus creates at least one new integer subset sum for every residue class
already represented modulo that modulus.
-/

open scoped BigOperators

namespace Erdos54

/-! ## Finite and set-level subset-sum values -/

/-- The finite set of all sums of subsets of `s`. -/
abbrev subsetSumValues (s : Finset ℕ) : Finset ℕ := s.subsetSum

@[simp]
theorem mem_subsetSumValues {s : Finset ℕ} {n : ℕ} :
    n ∈ subsetSumValues s ↔
      ∃ t : Finset ℕ, t ⊆ s ∧ (∑ x ∈ t, x) = n :=
  Finset.mem_subsetSum_iff

@[simp]
theorem subsetSumValues_empty : subsetSumValues ∅ = {0} := by
  simp [Finset.subsetSum]

@[simp]
theorem zero_mem_subsetSumValues (s : Finset ℕ) : 0 ∈ subsetSumValues s :=
  Finset.zero_mem_subsetSum

theorem sum_mem_subsetSumValues (s : Finset ℕ) :
    (∑ x ∈ s, x) ∈ subsetSumValues s := by
  exact Finset.mem_subsetSum_iff.mpr ⟨s, Finset.Subset.rfl, rfl⟩

/-- Enlarging a finite set can only enlarge its set of subset sums. -/
theorem subsetSumValues_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    subsetSumValues s ⊆ subsetSumValues t :=
  Finset.subsetSum_mono hst

/-- The set-level set of finite distinct subset sums, tied definitionally to
the public predicate in `Core`. -/
def finiteSubsetSumValues (A : Set ℕ) : Set ℕ :=
  {n | FiniteDistinctSubsetSum A n}

@[simp]
theorem mem_finiteSubsetSumValues {A : Set ℕ} {n : ℕ} :
    n ∈ finiteSubsetSumValues A ↔ FiniteDistinctSubsetSum A n :=
  Iff.rfl

/-- Set-level monotonicity of finite distinct subset sums. -/
theorem finiteSubsetSumValues_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    finiteSubsetSumValues A ⊆ finiteSubsetSumValues B := by
  intro n hn
  exact hn.mono hAB

/-- A subset sum remains available after adjoining one element. -/
theorem subsetSumValues_subset_insert (a : ℕ) (s : Finset ℕ) :
    subsetSumValues s ⊆ subsetSumValues (insert a s) :=
  subsetSumValues_mono (Finset.subset_insert a s)

/-- Adding a fresh element gives exactly the old subset sums and their
translate by the new element. -/
theorem subsetSumValues_insert {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) :
    subsetSumValues (insert a s) =
      subsetSumValues s ∪ (subsetSumValues s).image (fun n ↦ n + a) := by
  ext n
  constructor
  · intro hn
    rw [mem_subsetSumValues] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    by_cases hau : a ∈ u
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨∑ x ∈ u.erase a, x, ?_, ?_⟩
      · rw [mem_subsetSumValues]
        refine ⟨u.erase a, ?_, rfl⟩
        intro x hx
        have hxu : x ∈ u := Finset.mem_of_mem_erase hx
        have hxas : x = a ∨ x ∈ s := by
          simpa only [Finset.mem_insert] using hu hxu
        exact hxas.resolve_left (fun hxa ↦ (Finset.ne_of_mem_erase hx) hxa)
      · rw [← Finset.sum_erase_add _ _ hau]
    · apply Finset.mem_union_left
      rw [mem_subsetSumValues]
      refine ⟨u, ?_, rfl⟩
      intro x hx
      have hxas : x = a ∨ x ∈ s := by
        simpa only [Finset.mem_insert] using hu hx
      exact hxas.resolve_left (fun hxa ↦ hau (hxa ▸ hx))
  · intro hn
    rw [Finset.mem_union] at hn
    rcases hn with hn | hn
    · exact subsetSumValues_subset_insert a s hn
    · rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [mem_subsetSumValues] at hm ⊢
      obtain ⟨u, hus, rfl⟩ := hm
      refine ⟨insert a u, ?_, ?_⟩
      · exact Finset.insert_subset_insert a hus
      · have hau : a ∉ u := fun hau ↦ ha (hus hau)
        simp [hau, add_comm]

theorem add_mem_subsetSumValues_insert {a m : ℕ} {s : Finset ℕ}
    (ha : a ∉ s) (hm : m ∈ subsetSumValues s) :
    m + a ∈ subsetSumValues (insert a s) := by
  rw [subsetSumValues_insert ha]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)

/-- For disjoint finite sets, subset sums of the union are exactly pairwise
sums of subset sums of the two parts. -/
theorem subsetSumValues_union {s t : Finset ℕ} (hdisj : Disjoint s t) :
    subsetSumValues (s ∪ t) =
      Finset.image₂ (fun m n : ℕ ↦ m + n) (subsetSumValues s) (subsetSumValues t) := by
  ext n
  constructor
  · intro hn
    rw [mem_subsetSumValues] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    let us := u ∩ s
    let ut := u ∩ t
    have hus : us ⊆ s := Finset.inter_subset_right
    have hut : ut ⊆ t := Finset.inter_subset_right
    have hust : Disjoint us ut := hdisj.mono hus hut
    have hu_eq : u = us ∪ ut := by
      ext x
      simp only [us, ut, Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hu hx) with hxs | hxt
        · exact Or.inl ⟨hx, hxs⟩
        · exact Or.inr ⟨hx, hxt⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    rw [hu_eq, Finset.sum_union hust]
    apply Finset.mem_image₂.mpr
    refine ⟨∑ x ∈ us, x, ?_, ∑ x ∈ ut, x, ?_, rfl⟩
    · exact mem_subsetSumValues.mpr ⟨us, hus, rfl⟩
    · exact mem_subsetSumValues.mpr ⟨ut, hut, rfl⟩
  · intro hn
    rw [Finset.mem_image₂] at hn
    obtain ⟨m, hm, k, hk, rfl⟩ := hn
    rw [mem_subsetSumValues] at hm hk ⊢
    obtain ⟨us, hus, rfl⟩ := hm
    obtain ⟨ut, hut, rfl⟩ := hk
    have hust : Disjoint us ut := hdisj.mono hus hut
    refine ⟨us ∪ ut, Finset.union_subset_union hus hut, ?_⟩
    rw [Finset.sum_union hust]

theorem add_mem_subsetSumValues_union {s t : Finset ℕ} (hdisj : Disjoint s t)
    {m n : ℕ} (hm : m ∈ subsetSumValues s) (hn : n ∈ subsetSumValues t) :
    m + n ∈ subsetSumValues (s ∪ t) := by
  rw [subsetSumValues_union hdisj]
  exact Finset.mem_image₂.mpr ⟨m, hm, n, hn, rfl⟩

/-! ## Graham's interval-extension lemma -/

/-- All natural numbers in the closed interval `[L,U]` occur as distinct
subset sums of `s`. -/
def CoversInterval (s : Finset ℕ) (L U : ℕ) : Prop :=
  Finset.Icc L U ⊆ subsetSumValues s

theorem CoversInterval.mono {s t : Finset ℕ} {L U : ℕ}
    (h : CoversInterval s L U) (hst : s ⊆ t) : CoversInterval t L U :=
  fun _ hn ↦ subsetSumValues_mono hst (h hn)

/-- Graham interval extension, one step.  A fresh integer no larger than the
length of the covered interval extends the upper endpoint by that integer. -/
theorem coversInterval_insert {s : Finset ℕ} {a L U : ℕ}
    (hLU : L ≤ U) (ha : a ∉ s) (ha_small : a ≤ U - L + 1)
    (hcover : CoversInterval s L U) :
    CoversInterval (insert a s) L (U + a) := by
  intro n hn
  have hn_bounds : L ≤ n ∧ n ≤ U + a := Finset.mem_Icc.mp hn
  by_cases hnU : n ≤ U
  · apply subsetSumValues_subset_insert a s
    exact hcover (Finset.mem_Icc.mpr ⟨hn_bounds.1, hnU⟩)
  · have ha_le_n : a ≤ n := by omega
    have hL : L ≤ n - a := by omega
    have hU : n - a ≤ U := by omega
    have hdiff : n - a ∈ subsetSumValues s :=
      hcover (Finset.mem_Icc.mpr ⟨hL, hU⟩)
    have hadd := add_mem_subsetSumValues_insert ha hdiff
    simpa [Nat.sub_add_cancel ha_le_n] using hadd

/-- Iterated Graham extension.  The `i`th new element is at most the original
interval length plus the sum of the preceding new elements. -/
theorem coversInterval_add_list {s : Finset ℕ} {L U : ℕ} (l : List ℕ)
    (hLU : L ≤ U) (hnodup : l.Nodup) (hdisj : Disjoint l.toFinset s)
    (hsmall : ∀ (i : ℕ) (hi : i < l.length),
      l[i] ≤ U - L + 1 + (l.take i).sum)
    (hcover : CoversInterval s L U) :
    CoversInterval (s ∪ l.toFinset) L (U + l.sum) := by
  induction l generalizing s U with
  | nil => simpa using hcover
  | cons a l ih =>
      have ha_s : a ∉ s := by
        have hdisj' : Disjoint (insert a l.toFinset) s := by
          simpa [List.toFinset_cons] using hdisj
        exact (Finset.disjoint_insert_left.mp hdisj').1
      have ha_small : a ≤ U - L + 1 := by
        have h := hsmall 0 (by simp)
        simpa using h
      have hfirst : CoversInterval (insert a s) L (U + a) :=
        coversInterval_insert hLU ha_s ha_small hcover
      have hnodup_l : l.Nodup := hnodup.tail
      have ha_l : a ∉ l := (List.nodup_cons.mp hnodup).1
      have hdisj_l : Disjoint l.toFinset (insert a s) := by
        rw [Finset.disjoint_insert_right]
        refine ⟨?_, ?_⟩
        · simpa using ha_l
        · exact hdisj.mono_left (by simp)
      have hsmall_l : ∀ (i : ℕ) (hi : i < l.length),
          l[i] ≤ (U + a) - L + 1 + (l.take i).sum := by
        intro i hi
        have h := hsmall (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.sum_cons] at h
        omega
      have htail := ih (U := U + a) (s := insert a s) (by omega)
        hnodup_l hdisj_l hsmall_l hfirst
      simpa [List.toFinset_cons, Finset.union_assoc, Finset.union_left_comm,
        Finset.union_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-! ## CFP Lemma 2.5: adjoining a modulus -/

/-- Residue classes modulo `m` represented by distinct subset sums of `s`. -/
def subsetSumResidues (m : ℕ) (s : Finset ℕ) : Finset (ZMod m) :=
  (subsetSumValues s).image fun n : ℕ ↦ (n : ZMod m)

@[simp]
theorem mem_subsetSumResidues {m : ℕ} {s : Finset ℕ} {r : ZMod m} :
    r ∈ subsetSumResidues m s ↔
      ∃ n ∈ subsetSumValues s, (n : ZMod m) = r := by
  simp [subsetSumResidues]

/-- A finite set and its translate by a positive modulus contain at least one
new integer for every residue class represented by the original set. -/
private theorem card_add_residues_le_card_union_translate (S : Finset ℕ)
    {m : ℕ} (hm : 0 < m) :
    S.card + (S.image fun n : ℕ ↦ (n : ZMod m)).card ≤
      (S ∪ S.image fun n : ℕ ↦ n + m).card := by
  let residues : Finset (ZMod m) := S.image fun n : ℕ ↦ (n : ZMod m)
  let R := residues.attach
  let fiber (r : ↑residues) : Finset ℕ :=
    S.filter fun n : ℕ ↦ (n : ZMod m) = r.1
  have hfiber (r : ↑residues) : (fiber r).Nonempty := by
    rcases Finset.mem_image.mp r.2 with ⟨n, hn, hnr⟩
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hnr⟩⟩
  let top (r : ↑residues) : ℕ := (fiber r).max' (hfiber r)
  have htop_mem (r : ↑residues) : top r ∈ S := by
    exact (Finset.mem_filter.mp ((fiber r).max'_mem (hfiber r))).1
  have htop_residue (r : ↑residues) : (top r : ZMod m) = r.1 := by
    exact (Finset.mem_filter.mp ((fiber r).max'_mem (hfiber r))).2
  have htop_add_not_mem (r : ↑residues) : top r + m ∉ S := by
    intro hmem
    have hcast : ((top r + m : ℕ) : ZMod m) = r.1 := by
      simpa [Nat.cast_add, ZMod.natCast_self] using htop_residue r
    have hfmem : top r + m ∈ fiber r :=
      Finset.mem_filter.mpr ⟨hmem, hcast⟩
    have hle : top r + m ≤ top r := (fiber r).le_max' _ hfmem
    omega
  have htop_injective : Function.Injective (fun r : ↑residues ↦ top r + m) := by
    intro r q heq
    have ht : top r = top q := Nat.add_right_cancel heq
    apply Subtype.ext
    rw [← htop_residue r, ← htop_residue q, ht]
  let newReps : Finset ℕ := R.image fun r ↦ top r + m
  have hnew_card : newReps.card = residues.card := by
    calc
      newReps.card = R.card := Finset.card_image_iff.mpr htop_injective.injOn
      _ = residues.card := by simp [R]
  have hdisj : Disjoint S newReps := by
    rw [Finset.disjoint_left]
    intro n hnS hnnew
    rcases Finset.mem_image.mp hnnew with ⟨r, -, rfl⟩
    exact htop_add_not_mem r hnS
  have hnew_subset : newReps ⊆ S.image (fun n ↦ n + m) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨r, -, rfl⟩
    exact Finset.mem_image.mpr ⟨top r, htop_mem r, rfl⟩
  calc
    S.card + (S.image fun n : ℕ ↦ (n : ZMod m)).card =
        S.card + residues.card := by rfl
    _ = S.card + newReps.card := by rw [hnew_card]
    _ = (S ∪ newReps).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (S ∪ S.image fun n : ℕ ↦ n + m).card := by
      exact Finset.card_le_card (Finset.union_subset_union_right hnew_subset)

/-- CFP Lemma 2.5, sharp cardinal form.  Adjoining the positive modulus `m`
creates at least as many new integer subset sums as there are represented
subset-sum residues modulo `m`. -/
theorem card_subsetSumValues_add_modulus {B : Finset ℕ} {m : ℕ}
    (hm : 0 < m) (hmB : m ∉ B) :
    (subsetSumValues B).card + (subsetSumResidues m B).card ≤
      (subsetSumValues (insert m B)).card := by
  rw [subsetSumValues_insert hmB]
  exact card_add_residues_le_card_union_translate (subsetSumValues B) hm

/-- CFP Lemma 2.5 in its customary lower-bound form. -/
theorem adjoin_modulus_card_growth {B : Finset ℕ} {m h : ℕ}
    (hm : 0 < m) (hmB : m ∉ B)
    (hh : h ≤ (subsetSumResidues m B).card) :
    (subsetSumValues B).card + h ≤
      (subsetSumValues (insert m B)).card := by
  exact (Nat.add_le_add_left hh _).trans
    (card_subsetSumValues_add_modulus hm hmB)

end Erdos54
