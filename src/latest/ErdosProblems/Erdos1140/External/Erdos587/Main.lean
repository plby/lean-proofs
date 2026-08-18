/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import Mathlib
import HasseWeil.HasseBound
import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import Waring.Analytic.FourierCoefficientSum
import ErdosProblems.Erdos1140.External.Scratch.HalberstamComplete448
import ErdosProblems.Erdos1140.External.Scratch.MeanValueSpecial448

/-!
# Erdős Problem 587

For `A ⊆ {1, ..., N}`, write `A` as admissible when no nonempty subset of
`A` has square sum.  Nguyen and Vu proved that the largest admissible set has
cardinality at most `N^(1/3)` times a fixed power of `log N`.

The definition and final theorem below reproduce the statement in
`google-deepmind/formal-conjectures`.
-/

open Filter
open scoped Pointwise

/- `Real.nthRoot` is the exact compatibility definition used by the upstream
formal-conjectures statement.  It is scheduled for inclusion in Mathlib, but is
not yet present in the v4.33.0 release targeted by this repository. -/
namespace Real

noncomputable def nthRoot (n : ℕ) (r : ℝ) : ℝ :=
  if Even n then r ^ (n⁻¹ : ℝ) else SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ)

theorem nthRoot_of_even {n : ℕ} (hn : Even n) (r : ℝ) : nthRoot n r = r ^ (n⁻¹ : ℝ) :=
  if_pos hn

theorem nthRoot_of_odd {n : ℕ} (hn : Odd n) (r : ℝ) :
    nthRoot n r = SignType.sign r ^ n * abs r ^ (n⁻¹ : ℝ) :=
  if_neg <| Nat.not_even_iff_odd.mpr hn

theorem nthRoot_of_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    nthRoot n r = r ^ (n⁻¹ : ℝ) := by
  cases Nat.even_or_odd n with
  | inl he => rw [nthRoot_of_even he]
  | inr ho =>
    have hn0 : n ≠ 0 := Nat.ne_of_odd_add ho
    rw [nthRoot_of_odd ho, abs_of_nonneg hr]
    obtain rfl | hr := hr.eq_or_lt
    · simp [hn0]
    rw [_root_.sign_pos hr]
    simp

end Real

namespace Erdos587

/-! ## Additive-combinatorial library interfaces -/

/-- Natural-number specialization of Mathlib's Ruzsa covering lemma for
finite integer sets. -/
lemma ruzsa_covering_int {A B : Finset ℤ} {K : ℕ} (hB : B.Nonempty)
    (hsmall : (A + B).card ≤ K * B.card) :
    ∃ F ⊆ A, F.card ≤ K ∧ A ⊆ F + (B - B) := by
  have hsmall' : ((A + B).card : ℝ) ≤ (K : ℝ) * (B.card : ℝ) := by
    exact_mod_cast hsmall
  obtain ⟨F, hFA, hFK, hcover⟩ := Finset.ruzsa_covering_add hB hsmall'
  refine ⟨F, hFA, ?_, hcover⟩
  exact_mod_cast hFK

/-- Natural-number consequence of Mathlib's Plünnecke--Ruzsa inequality. -/
lemma pluennecke_ruzsa_int {A B : Finset ℤ} {K m n : ℕ} (hA : A.Nonempty)
    (hsmall : (A + B).card ≤ K * A.card) :
    (m • B - n • B).card ≤ K ^ (m + n) * A.card := by
  have hratio :
      ((A + B).card : ℚ≥0) / (A.card : ℚ≥0) ≤ (K : ℚ≥0) := by
    rw [div_le_iff₀]
    · exact_mod_cast hsmall
    · exact_mod_cast hA.card_pos
  have hbound := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B m n
  have hbound' :
      ((m • B - n • B).card : ℚ≥0) ≤
        (K : ℚ≥0) ^ (m + n) * (A.card : ℚ≥0) := by
    refine hbound.trans ?_
    gcongr
  exact_mod_cast hbound'

/-! ## Modular subset-sum growth

The common-divisor branch can be obtained without a quadratic exponential
sum.  Starting from `{0}` in a finite additive group, adjoining a term either
strictly enlarges the set of reachable subset sums or translates that set to
itself.  There are at most `|G| - 1` strict enlargements.  Every term of the
second kind stabilizes the final reachable set; if that set is proper, these
terms therefore lie in a proper additive subgroup. -/

section ModularSubsetSumGrowth

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Translate a finset in an additive group.  Keeping this operation explicit
avoids any ambiguity between pointwise addition and scalar actions. -/
def addTranslate (a : G) (S : Finset G) : Finset G :=
  S.image fun x => a + x

@[simp] lemma mem_addTranslate {a x : G} {S : Finset G} :
    x ∈ addTranslate a S ↔ -a + x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    have : y = -a + x := by
      rw [← hxy]
      abel
    simpa [this] using hy
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨-a + x, hx, ?_⟩
    abel

lemma card_addTranslate (a : G) (S : Finset G) :
    (addTranslate a S).card = S.card := by
  rw [addTranslate, Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

@[simp] lemma addTranslate_zero (S : Finset G) : addTranslate 0 S = S := by
  ext x
  simp [mem_addTranslate]

lemma addTranslate_add (a b : G) (S : Finset G) :
    addTranslate a (addTranslate b S) = addTranslate (a + b) S := by
  ext x
  simp only [mem_addTranslate]
  constructor <;> intro hx
  · convert hx using 1 <;> abel
  · convert hx using 1 <;> abel

lemma addTranslate_union (a : G) (S T : Finset G) :
    addTranslate a (S ∪ T) = addTranslate a S ∪ addTranslate a T := by
  ext x
  simp [mem_addTranslate]

/-- All subset sums of a list, with occurrences distinguished by the list
positions. -/
def listSubsetSums : List G → Finset G
  | [] => {0}
  | a :: A =>
      let S := listSubsetSums A
      S ∪ addTranslate a S

@[simp] lemma listSubsetSums_nil : listSubsetSums ([] : List G) = {0} := rfl

@[simp] lemma listSubsetSums_cons (a : G) (A : List G) :
    listSubsetSums (a :: A) =
      listSubsetSums A ∪ addTranslate a (listSubsetSums A) := rfl

lemma zero_mem_listSubsetSums (A : List G) : 0 ∈ listSubsetSums A := by
  induction A with
  | nil => simp
  | cons a A ih => simp [listSubsetSums, ih]

/-- Witness characterization of `listSubsetSums`. -/
lemma mem_listSubsetSums_iff {A : List G} {x : G} :
    x ∈ listSubsetSums A ↔ ∃ T : List G, T.Sublist A ∧ T.sum = x := by
  induction A generalizing x with
  | nil =>
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa [listSubsetSums] using hx
        subst x
        exact ⟨[], List.nil_sublist _, by simp⟩
      · rintro ⟨T, hT, rfl⟩
        have hTnil : T = [] := List.sublist_nil.mp hT
        subst T
        simp [listSubsetSums]
  | cons a A ih =>
      constructor
      · intro hx
        rw [listSubsetSums_cons, Finset.mem_union] at hx
        rcases hx with hx | hx
        · obtain ⟨T, hTA, rfl⟩ := ih.mp hx
          exact ⟨T, hTA.cons a, rfl⟩
        · rw [mem_addTranslate] at hx
          obtain ⟨T, hTA, hsum⟩ := ih.mp hx
          refine ⟨a :: T, hTA.cons_cons a, ?_⟩
          simp only [List.sum_cons]
          rw [hsum]
          abel
      · rintro ⟨T, hT, rfl⟩
        rw [listSubsetSums_cons, Finset.mem_union]
        rcases List.sublist_cons_iff.mp hT with hTA | ⟨U, rfl, hUA⟩
        · exact Or.inl (ih.mpr ⟨T, hTA, rfl⟩)
        · apply Or.inr
          rw [mem_addTranslate]
          apply ih.mpr
          refine ⟨U, hUA, ?_⟩
          simp

/-- Terms which do not enlarge the subset-sum set of the suffix. -/
def subsetSumStableTerms : List G → List G
  | [] => []
  | a :: A =>
      if addTranslate a (listSubsetSums A) = listSubsetSums A then
        a :: subsetSumStableTerms A
      else
        subsetSumStableTerms A

/-- Terms which strictly enlarge the subset-sum set of the suffix. -/
def subsetSumGrowthTerms : List G → List G
  | [] => []
  | a :: A =>
      if addTranslate a (listSubsetSums A) = listSubsetSums A then
        subsetSumGrowthTerms A
      else
        a :: subsetSumGrowthTerms A

lemma length_stable_add_length_growth (A : List G) :
    (subsetSumStableTerms A).length + (subsetSumGrowthTerms A).length = A.length := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      by_cases h : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simp only [subsetSumStableTerms, subsetSumGrowthTerms, h, if_pos,
          ite_true, List.length_cons]
        omega
      · simp only [subsetSumStableTerms, subsetSumGrowthTerms, h, if_neg,
          ite_false, List.length_cons]
        omega

lemma subsetSumStableTerms_sublist (A : List G) :
    (subsetSumStableTerms A).Sublist A := by
  induction A with
  | nil => exact List.nil_sublist []
  | cons a A ih =>
      by_cases h : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumStableTerms, h] using ih.cons_cons a
      · simpa [subsetSumStableTerms, h] using ih.cons a

lemma subsetSumGrowthTerms_sublist (A : List G) :
    (subsetSumGrowthTerms A).Sublist A := by
  induction A with
  | nil => exact List.nil_sublist []
  | cons a A ih =>
      by_cases h : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumGrowthTerms, h] using ih.cons a
      · simpa [subsetSumGrowthTerms, h] using ih.cons_cons a

/-- Stable and growth occurrences partition the original list, up to
permutation. -/
lemma stable_append_growth_perm (A : List G) :
    (subsetSumStableTerms A ++ subsetSumGrowthTerms A).Perm A := by
  induction A with
  | nil => exact List.Perm.nil
  | cons a A ih =>
      by_cases h : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumStableTerms, subsetSumGrowthTerms, h] using ih.cons a
      · have hmove :
            (subsetSumStableTerms A ++ a :: subsetSumGrowthTerms A).Perm
              (a :: subsetSumStableTerms A ++ subsetSumGrowthTerms A) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm (l₁ := subsetSumStableTerms A)
              (l₂ := [a])).append_right (subsetSumGrowthTerms A)
        simpa [subsetSumStableTerms, subsetSumGrowthTerms, h] using
          hmove.trans (ih.cons a)

/-- Once a term stabilizes the subset sums of a suffix, it also stabilizes
the subset sums after any earlier terms have been adjoined. -/
lemma mem_stable_stabilizes_listSubsetSums {A : List G} {b : G}
    (hb : b ∈ subsetSumStableTerms A) :
    addTranslate b (listSubsetSums A) = listSubsetSums A := by
  induction A with
  | nil => simp [subsetSumStableTerms] at hb
  | cons a A ih =>
      by_cases ha : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simp only [subsetSumStableTerms, ha, if_pos, List.mem_cons] at hb
        rcases hb with rfl | hb
        · simpa [listSubsetSums_cons, ha]
        · have hbstab := ih hb
          simpa [listSubsetSums_cons, ha] using hbstab
      · simp only [subsetSumStableTerms, ha, if_neg] at hb
        have hbstab := ih hb
        rw [listSubsetSums_cons, addTranslate_union, hbstab,
          addTranslate_add, add_comm b a, ← addTranslate_add, hbstab]

/-- The number of strict growth terms is bounded by the number of reachable
residues minus one. -/
lemma growth_length_add_one_le_card_listSubsetSums (A : List G) :
    (subsetSumGrowthTerms A).length + 1 ≤ (listSubsetSums A).card := by
  induction A with
  | nil => simp [subsetSumGrowthTerms, listSubsetSums]
  | cons a A ih =>
      by_cases ha : addTranslate a (listSubsetSums A) = listSubsetSums A
      · simpa [subsetSumGrowthTerms, listSubsetSums_cons, ha] using ih
      · have hproper : listSubsetSums A ⊂
            listSubsetSums A ∪ addTranslate a (listSubsetSums A) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
          intro heq
          have hsub : addTranslate a (listSubsetSums A) ⊆ listSubsetSums A := by
            intro x hx
            have : x ∈ listSubsetSums A ∪ addTranslate a (listSubsetSums A) :=
              Finset.mem_union_right _ hx
            rwa [← heq] at this
          exact ha (Finset.eq_of_subset_of_card_le hsub (by
            rw [card_addTranslate]))
        have hcard : (listSubsetSums A).card + 1 ≤
            (listSubsetSums (a :: A)).card := by
          have hlt := Finset.card_lt_card hproper
          simp only [listSubsetSums_cons]
          omega
        simp only [subsetSumGrowthTerms, ha, if_neg, ite_false, List.length_cons]
        omega

/-- In a finite group, all but at most `|G|-1` list occurrences stabilize
the final subset-sum set. -/
lemma length_le_card_add_stable [Fintype G] (A : List G) :
    A.length + 1 ≤ Fintype.card G + (subsetSumStableTerms A).length := by
  have hgrowth := growth_length_add_one_le_card_listSubsetSums A
  have hcard : (listSubsetSums A).card ≤ Fintype.card G := Finset.card_le_univ _
  have hparts := length_stable_add_length_growth A
  omega

/-- If the reachable subset sums are not the whole finite group, the stable
terms all translate one fixed proper finset to itself. -/
lemma stable_terms_in_proper_additive_stabilizer [Fintype G] (A : List G)
    (hproper : listSubsetSums A ≠ Finset.univ) :
    ∃ S : Finset G, S ≠ Finset.univ ∧ 0 ∈ S ∧
      ∀ a ∈ subsetSumStableTerms A, addTranslate a S = S := by
  exact ⟨listSubsetSums A, hproper, zero_mem_listSubsetSums A,
    fun _ ha => mem_stable_stabilizes_listSubsetSums ha⟩

/-- The subgroup of translations preserving a finite set. -/
def finsetAddStabilizer (S : Finset G) : AddSubgroup G where
  carrier := {a | addTranslate a S = S}
  zero_mem' := addTranslate_zero S
  add_mem' {a b} ha hb := by
    change addTranslate (a + b) S = S
    change addTranslate a S = S at ha
    change addTranslate b S = S at hb
    rw [← addTranslate_add, hb, ha]
  neg_mem' {a} ha := by
    change addTranslate (-a) S = S
    change addTranslate a S = S at ha
    calc
      addTranslate (-a) S = addTranslate (-a) (addTranslate a S) := by rw [ha]
      _ = addTranslate (-a + a) S := addTranslate_add _ _ _
      _ = S := by simp

@[simp] lemma mem_finsetAddStabilizer {S : Finset G} {a : G} :
    a ∈ finsetAddStabilizer S ↔ addTranslate a S = S := Iff.rfl

/-- A proper nonempty finset has a proper translation stabilizer. -/
lemma finsetAddStabilizer_ne_top [Fintype G] {S : Finset G}
    (hS0 : 0 ∈ S) (hSproper : S ≠ Finset.univ) :
    finsetAddStabilizer S ≠ ⊤ := by
  intro htop
  apply hSproper
  apply Finset.eq_univ_of_forall
  intro x
  have hxstab : x ∈ finsetAddStabilizer S := by rw [htop]; simp
  have hxmem : x + 0 ∈ addTranslate x S := by
    exact Finset.mem_image.mpr ⟨0, hS0, rfl⟩
  rw [mem_finsetAddStabilizer.mp hxstab] at hxmem
  simpa using hxmem

/-- The additive group of a prime residue field has no nontrivial proper
additive subgroup. -/
lemma addSubgroup_eq_bot_of_zmod_prime {p : ℕ} (hp : p.Prime)
    (H : AddSubgroup (ZMod p)) (hH : H ≠ ⊤) : H = ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  apply eq_bot_iff.mpr
  intro x hx
  by_contra hx0
  have hxne : x ≠ 0 := by simpa using hx0
  apply hH
  apply top_unique
  intro y _
  let H' : Submodule (ZMod p) (ZMod p) := AddSubgroup.toZModSubmodule p H
  have hx' : x ∈ H' := hx
  have hmul : (y * x⁻¹) • x ∈ H' := H'.smul_mem (y * x⁻¹) hx'
  have hyx : (y * x⁻¹) • x = y := by
    change (y * x⁻¹) * x = y
    field_simp [hxne]
  exact hyx ▸ hmul

/-- For a prime modulus, failure to reach every residue forces every stable
occurrence to be zero modulo that prime. -/
lemma stable_term_eq_zero_of_zmod_prime {p : ℕ} [NeZero p] (hp : p.Prime)
    (A : List (ZMod p)) (hproper : listSubsetSums A ≠ Finset.univ)
    {a : ZMod p} (ha : a ∈ subsetSumStableTerms A) : a = 0 := by
  let H := finsetAddStabilizer (listSubsetSums A)
  have hHproper : H ≠ ⊤ := finsetAddStabilizer_ne_top
    (zero_mem_listSubsetSums A) hproper
  have hHbot : H = ⊥ := addSubgroup_eq_bot_of_zmod_prime hp H hHproper
  have haH : a ∈ H := mem_stable_stabilizes_listSubsetSums ha
  rw [hHbot] at haH
  simpa using haH

/-- In a prime cyclic group, a non-complete sequence has fewer than `p`
nonzero occurrences. -/
lemma length_filter_ne_zero_lt_prime_of_not_complete {p : ℕ} [NeZero p]
    (hp : p.Prime)
    (A : List (ZMod p)) (hproper : listSubsetSums A ≠ Finset.univ) :
    (A.filter fun a => a ≠ 0).length < p := by
  have hstable :
      (subsetSumStableTerms A).filter (fun a => a ≠ 0) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    simp [stable_term_eq_zero_of_zmod_prime hp A hproper ha]
  have hperm := (stable_append_growth_perm A).filter (fun a => a ≠ 0)
  have hlen :
      (A.filter fun a => a ≠ 0).length ≤ (subsetSumGrowthTerms A).length := by
    rw [← hperm.length_eq, List.filter_append, hstable]
    exact List.length_filter_le _ _
  have hcardlt : (listSubsetSums A).card < p := by
    have hss : listSubsetSums A ⊂ (Finset.univ : Finset (ZMod p)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hproper⟩
    have := Finset.card_lt_card hss
    simpa using this
  have hgrowth := growth_length_add_one_le_card_listSubsetSums A
  omega

/-- Contrapositive completeness criterion for sequences modulo a prime. -/
lemma listSubsetSums_eq_univ_of_prime_le_nonzero_length {p : ℕ} [NeZero p]
    (hp : p.Prime)
    (A : List (ZMod p))
    (hlarge : p ≤ (A.filter fun a => a ≠ 0).length) :
    listSubsetSums A = Finset.univ := by
  by_contra hproper
  have := length_filter_ne_zero_lt_prime_of_not_complete hp A hproper
  omega

/-- Every reachable residue of a mapped natural-number list has an actual
sublist witness with the same sum modulo the modulus. -/
lemma exists_sublist_sum_mod_eq_of_mem {q : ℕ} (hq : 0 < q) (A : List ℕ)
    (r : ZMod q)
    (hr : r ∈ listSubsetSums (A.map fun a : ℕ => (a : ZMod q))) :
    ∃ T : List ℕ, T.Sublist A ∧ (T.sum : ZMod q) = r := by
  letI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨U, hU, hUsum⟩ := mem_listSubsetSums_iff.mp hr
  have hpreimage : ∃ T : List ℕ, T.Sublist A ∧
      U = T.map (fun a : ℕ => (a : ZMod q)) := by
    exact (List.sublist_map_iff (l₂ := A)
      (f := fun a : ℕ => (a : ZMod q))).mp hU
  obtain ⟨T, hTA, hUT⟩ := hpreimage
  refine ⟨T, hTA, ?_⟩
  have hcastsum : (T.sum : ZMod q) =
      (T.map fun a : ℕ => (a : ZMod q)).sum := by
    induction T with
    | nil => simp
    | cons a T ih => simp [ih]
  rw [hcastsum, ← hUT]
  exact hUsum

/-- Full modular subset sums give a sublist representing any prescribed
residue. -/
lemma exists_sublist_sum_mod_eq_of_complete {q : ℕ} [NeZero q]
    (hq : 0 < q) (A : List ℕ)
    (hall : listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) = Finset.univ)
    (r : ZMod q) :
    ∃ T : List ℕ, T.Sublist A ∧ (T.sum : ZMod q) = r := by
  apply exists_sublist_sum_mod_eq_of_mem hq A r
  rw [hall]
  simp

/-- Iterating translation by `a` is translation by the natural multiple of
`a`. -/
lemma iterate_addTranslate (a : G) (n : ℕ) (S : Finset G) :
    (addTranslate a)^[n] S = addTranslate (n • a) S := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, addTranslate_add]
      congr 1
      rw [succ_nsmul]
      exact add_comm _ _

/-- Composite-modulus form of the residue-growth dichotomy.  If the subset
sums of a natural-number list do not cover `ZMod q`, then, apart from fewer
than `q` occurrences, all terms share a divisor `d > 1` of `q`. -/
lemma exists_large_sublist_with_common_divisor_of_not_complete
    {q : ℕ} [NeZero q] (hq : 0 < q) (A : List ℕ)
    (hproper : listSubsetSums (A.map fun a : ℕ => (a : ZMod q)) ≠ Finset.univ) :
    ∃ d : ℕ, ∃ B : List ℕ, B.Sublist A ∧ 1 < d ∧ d ∣ q ∧
      A.length + 1 ≤ q + B.length ∧ ∀ b ∈ B, d ∣ b := by
  let M : List (ZMod q) := A.map fun a : ℕ => (a : ZMod q)
  let S : Finset (ZMod q) := listSubsetSums M
  let f : Finset (ZMod q) → Finset (ZMod q) := addTranslate 1
  let d : ℕ := Function.minimalPeriod f S
  have hperiodq : Function.IsPeriodicPt f q S := by
    change f^[q] S = S
    rw [show f^[q] S = addTranslate (q • (1 : ZMod q)) S by
      simpa [f] using iterate_addTranslate (1 : ZMod q) q S]
    simp
  have hdpos : 0 < d := by
    exact hperiodq.minimalPeriod_pos hq
  have hdq : d ∣ q := hperiodq.minimalPeriod_dvd
  have hSproper : S ≠ Finset.univ := by simpa [S, M] using hproper
  have hHproper : finsetAddStabilizer S ≠ ⊤ :=
    finsetAddStabilizer_ne_top (by simpa [S] using zero_mem_listSubsetSums M)
      hSproper
  have hdne : d ≠ 1 := by
    intro hd1
    have hfixed : Function.IsFixedPt f S :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp hd1
    have hone : (1 : ZMod q) ∈ finsetAddStabilizer S := by
      exact hfixed
    apply hHproper
    apply top_unique
    intro x _
    have hx := (finsetAddStabilizer S).nsmul_mem hone x.val
    have hval : x.val • (1 : ZMod q) = x := by
      simpa using ZMod.natCast_zmod_val x
    rwa [hval] at hx
  have hdgt : 1 < d := by omega
  have hsub := subsetSumStableTerms_sublist M
  have hpreimage : ∃ B : List ℕ, B.Sublist A ∧
      subsetSumStableTerms M = B.map (fun a : ℕ => (a : ZMod q)) := by
    change (subsetSumStableTerms M).Sublist
      (A.map (fun a : ℕ => (a : ZMod q))) at hsub
    exact (List.sublist_map_iff (l₂ := A)
      (f := fun a : ℕ => (a : ZMod q))).mp hsub
  obtain ⟨B, hBA, hstable⟩ := hpreimage
  refine ⟨d, B, hBA, hdgt, hdq, ?_, ?_⟩
  · have hlen := length_le_card_add_stable M
    simpa [M, hstable, ZMod.card] using hlen
  · intro b hb
    have hbStable : (b : ZMod q) ∈ subsetSumStableTerms M := by
      rw [hstable]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    have hbstab : addTranslate (b : ZMod q) S = S := by
      simpa [S] using mem_stable_stabilizes_listSubsetSums hbStable
    have hperiodb : Function.IsPeriodicPt f b S := by
      change f^[b] S = S
      rw [show f^[b] S = addTranslate (b • (1 : ZMod q)) S by
        simpa [f] using iterate_addTranslate (1 : ZMod q) b S]
      simpa using hbstab
    exact hperiodb.minimalPeriod_dvd

end ModularSubsetSumGrowth

/-! ## First analytic estimate -/

/-- The standard phase `e(x) = exp(2πix)`. -/
noncomputable def phase (x : ℝ) : ℂ :=
  Real.fourierChar x

@[simp] lemma phase_zero : phase 0 = 1 := by
  simp [phase, AddChar.map_zero_eq_one]

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  change ((Real.fourierChar (x + y) : Circle) : ℂ) =
    ((Real.fourierChar x : Circle) : ℂ) * Real.fourierChar y
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

lemma phase_neg (x : ℝ) : phase (-x) = starRingEnd ℂ (phase x) := by
  change ((Real.fourierChar (-x) : Circle) : ℂ) =
    starRingEnd ℂ ((Real.fourierChar x : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

@[simp] lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Circle.norm_coe _

lemma phase_sub (x y : ℝ) :
    phase (x - y) = phase x * starRingEnd ℂ (phase y) := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase (n * x) = phase x ^ n := by
  change ((Real.fourierChar (n * x) : Circle) : ℂ) =
    ((Real.fourierChar x : Circle) : ℂ) ^ n
  rw [show (n : ℝ) * x = n • x by simp, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

/-- Differencing a quadratic phase produces a linear phase. -/
lemma quadratic_phase_correlation (α β : ℝ) (z h : ℕ) :
    phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
        starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z)) =
      phase (2 * α * h * z + α * h ^ 2 + β * h) := by
  rw [← phase_sub]
  congr 1
  push_cast
  ring

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

lemma nearestIntDist_nonneg (x : ℝ) : 0 ≤ nearestIntDist x :=
  abs_nonneg _

lemma nearestIntDist_le_half (x : ℝ) : nearestIntDist x ≤ 1 / 2 := by
  exact abs_sub_round x

lemma fourierChar_intCast (n : ℤ) :
    ((Real.fourierChar (n : ℝ) : Circle) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- The Fourier character only depends on a real number modulo `ℤ`. -/
lemma fourierChar_sub_round (x : ℝ) :
    ((Real.fourierChar (x - (round x : ℝ)) : Circle) : ℂ) =
      Real.fourierChar x := by
  rw [AddChar.map_sub_eq_div, Circle.coe_div, fourierChar_intCast, div_one]

/-- The chord cut out by the Fourier character controls distance to the
nearest integer. -/
lemma four_mul_nearestIntDist_le_norm_fourierChar_sub_one (x : ℝ) :
    4 * nearestIntDist x ≤
      ‖((Real.fourierChar x : Circle) : ℂ) - 1‖ := by
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1 / 2 := by
    simpa [y] using (abs_sub_round x)
  have harg : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hscale : 2 / Real.pi * |Real.pi * y| = 2 * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  have hreal : 4 * |y| ≤ 2 * |Real.sin (Real.pi * y)| := by
    rw [hscale] at hsin
    nlinarith
  have hnorm :
      ‖((Real.fourierChar y : Circle) : ℂ) - 1‖ =
        2 * |Real.sin (Real.pi * y)| := by
    rw [Real.fourierChar_apply]
    rw [show (↑(2 * Real.pi * y) : ℂ) * Complex.I =
        Complex.I * (2 * Real.pi * y : ℝ) by push_cast; ring]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num [abs_mul]
    congr 2
    ring
  rw [← fourierChar_sub_round x]
  change 4 * |y| ≤ ‖((Real.fourierChar y : Circle) : ℂ) - 1‖
  rwa [hnorm]

/-- The geometric-sum estimate used after Weyl differencing.  This is the
normed-field form of the familiar `min(N, ‖ω‖⁻¹)` bound. -/
lemma norm_geom_sum_le_min (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, ζ ^ k‖ ≤
      min (N : ℝ) (2 / ‖ζ - 1‖) := by
  apply le_min
  · calc
      ‖∑ k ∈ Finset.range N, ζ ^ k‖
          ≤ ∑ k ∈ Finset.range N, ‖ζ ^ k‖ := norm_sum_le _ _
      _ = N := by simp [norm_pow, hζ]
  · rw [geom_sum_eq hζ1, norm_div]
    have hden : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
    rw [div_le_div_iff_of_pos_right hden]
    calc
      ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hζ]

/-- Geometric exponential sum bounded by the inverse distance of its
frequency to the nearest integer. -/
lemma norm_fourier_geom_sum_le_min (x : ℝ) (hx : nearestIntDist x ≠ 0) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (((Real.fourierChar x : Circle) : ℂ) ^ k)‖ ≤
      min (N : ℝ) (1 / (2 * nearestIntDist x)) := by
  let ζ : ℂ := Real.fourierChar x
  have hζnorm : ‖ζ‖ = 1 := Circle.norm_coe _
  have hdistpos : 0 < nearestIntDist x :=
    (nearestIntDist_nonneg x).lt_of_ne' hx
  have hchord : 4 * nearestIntDist x ≤ ‖ζ - 1‖ := by
    exact four_mul_nearestIntDist_le_norm_fourierChar_sub_one x
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hchord
    nlinarith
  have hchordpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
  refine (norm_geom_sum_le_min ζ hζnorm hζ1 N).trans ?_
  apply min_le_min le_rfl
  rw [div_le_div_iff₀ hchordpos (by positivity : 0 < 2 * nearestIntDist x)]
  nlinarith

/-- A finite quadratic exponential sum on `[0,N)`. -/
noncomputable def quadraticSum (α β : ℝ) (N : ℕ) : ℂ :=
  ∑ z ∈ Finset.range N, phase (α * (z : ℝ) ^ 2 + β * z)

lemma norm_quadraticSum_le (α β : ℝ) (N : ℕ) :
    ‖quadraticSum α β N‖ ≤ N := by
  calc
    ‖quadraticSum α β N‖ ≤
        ∑ z ∈ Finset.range N, ‖phase (α * (z : ℝ) ^ 2 + β * z)‖ := by
      exact norm_sum_le _ _
    _ = N := by simp

/-- Exact autocorrelation formula for a quadratic phase over a truncated
range. -/
lemma quadratic_correlation_sum (α β : ℝ) (N h : ℕ) :
    (∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))) =
      phase (α * h ^ 2 + β * h) *
        ∑ z ∈ Finset.range (N - h), phase (2 * α * h) ^ z := by
  calc
    (∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))) =
        ∑ z ∈ Finset.range (N - h),
          phase (2 * α * h * z + α * h ^ 2 + β * h) := by
      apply Finset.sum_congr rfl
      intro z _
      exact quadratic_phase_correlation α β z h
    _ = ∑ z ∈ Finset.range (N - h),
          phase (α * h ^ 2 + β * h) * phase ((z : ℝ) * (2 * α * h)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← phase_add]
      congr 1
      ring
    _ = phase (α * h ^ 2 + β * h) *
          ∑ z ∈ Finset.range (N - h), phase ((z : ℝ) * (2 * α * h)) := by
      rw [Finset.mul_sum]
    _ = phase (α * h ^ 2 + β * h) *
          ∑ z ∈ Finset.range (N - h), phase (2 * α * h) ^ z := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      exact phase_nat_mul (2 * α * h) z

/-- The autocorrelation is controlled by a geometric sum. -/
lemma norm_quadratic_correlation_sum_le (α β : ℝ) (N h : ℕ)
    (hfreq : nearestIntDist (2 * α * h) ≠ 0) :
    ‖∑ z ∈ Finset.range (N - h),
        phase (α * (z + h : ℕ) ^ 2 + β * (z + h : ℕ)) *
          starRingEnd ℂ (phase (α * (z : ℕ) ^ 2 + β * z))‖ ≤
      min ((N - h : ℕ) : ℝ) (1 / (2 * nearestIntDist (2 * α * h))) := by
  rw [quadratic_correlation_sum, norm_mul, norm_phase, one_mul]
  exact norm_fourier_geom_sum_le_min (2 * α * h) hfreq (N - h)

/-- The harmonic-sum estimate used after grouping correlation frequencies by
their residue modulo the denominator. -/
lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

/-- Scaled harmonic estimate in the exact form of the nonzero-residue term in
the quadratic Weyl bound. -/
lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

/-- Number of pairs `(m,u)` in the positive box whose product `2*m*u` has a
specified residue.  These are the finite multiplicities in the Weyl estimate. -/
def residuePairCount (q r M N : ℕ) : ℕ :=
  (((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    (2 * x.1 * x.2) % q = r).card

lemma residuePairCount_le (q r M N : ℕ) :
    residuePairCount q r M N ≤ M * N := by
  calc
    residuePairCount q r M N ≤
        ((Finset.Icc 1 M).product (Finset.Icc 1 N)).card :=
      Finset.card_filter_le _ _
    _ = M * N := by simp

/-- The residue multiplicities partition the entire `(m,u)` box. -/
lemma sum_residuePairCount (q M N : ℕ) (hq : 0 < q) :
    ∑ r ∈ Finset.range q, residuePairCount q r M N = M * N := by
  let s := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let f : ℕ × ℕ → ℕ := fun x => (2 * x.1 * x.2) % q
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo f (Finset.range q) := by
    intro x _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
  calc
    ∑ r ∈ Finset.range q, residuePairCount q r M N =
        ∑ r ∈ Finset.range q, (s.filter fun x => f x = r).card := by
      rfl
    _ = s.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
    _ = M * N := by simp [s]

/-- A uniform bound for nonzero residue multiplicities combines with the
harmonic estimate to bound their weighted contribution. -/
lemma weighted_residue_sum_le {c : ℕ → ℕ} {B q n : ℕ}
    (hc : ∀ r ∈ Finset.Icc 1 n, (c r : ℝ) ≤ B) :
    (∑ r ∈ Finset.Icc 1 n, (c r : ℝ) * ((q : ℝ) / r)) ≤
      B * (q * (1 + Real.log n)) := by
  calc
    (∑ r ∈ Finset.Icc 1 n, (c r : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ Finset.Icc 1 n, (B : ℝ) * ((q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right (hc r hr) (by positivity)
    _ = (B : ℝ) * ∑ r ∈ Finset.Icc 1 n, ((q : ℝ) / r) := by
      rw [Finset.mul_sum]
    _ ≤ (B : ℝ) * (q * (1 + Real.log n)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le q n)
        (Nat.cast_nonneg B)

/-- A set contained in `[1,X]` and lying in one residue class modulo `h`
has at most `X / h + 1` elements.  Mapping to the quotient by `h` gives a
short proof which remains useful when the residue class is specified only
implicitly. -/
lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

/-- Count integers up to `X` which are divisible by `d` and have residue
`r` modulo `q`. -/
def divisorResidueCount (d q r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun v ↦ d ∣ v ∧ v % q = r).card

/-- Divisibility and a congruence specify at most one residue class modulo
`lcm d q`. -/
lemma divisorResidueCount_le_lcm {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (r X : ℕ) : divisorResidueCount d q r X ≤ X / d.lcm q + 1 := by
  let s := (Finset.Icc 1 X).filter fun v ↦ d ∣ v ∧ v % q = r
  apply card_le_div_add_one_of_pairwise_modEq (s := s)
    (fun v hv ↦ Finset.filter_subset _ _ hv) (Nat.lcm_pos hd hq)
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  apply Nat.mod_lcm
  · exact (ha'.1.modEq_zero_nat).trans hb'.1.zero_modEq_nat
  · exact ha'.2.trans hb'.2.symm

lemma gcd_dvd_residue_of_divisorResidueCount_pos {d q r X : ℕ}
    (hpos : 0 < divisorResidueCount d q r X) : d.gcd q ∣ r := by
  rw [divisorResidueCount, Finset.card_pos] at hpos
  obtain ⟨v, hv⟩ := hpos
  have hv' := (Finset.mem_filter.mp hv).2
  apply Nat.dvd_of_mod_eq_zero
  have hmod := Nat.mod_mod_of_dvd v (Nat.gcd_dvd_right d q)
  rw [hv'.2,
    Nat.mod_eq_zero_of_dvd ((Nat.gcd_dvd_left d q).trans hv'.1)] at hmod
  exact hmod

/-- The gcd obstruction cancels against the harmonic residue weight.  This
is the precise replacement for the superficially plausible, but false,
uniform residue-count estimate when `d` and `q` are not coprime. -/
lemma divisorResidueCount_mul_weight_le {d q r X : ℕ}
    (hd : 0 < d) (hq : 0 < q) (hr : 0 < r) :
    (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r) ≤
      (X : ℝ) / d + q := by
  by_cases hc : divisorResidueCount d q r X = 0
  · simp [hc]
    positivity
  have hcpos : 0 < divisorResidueCount d q r X := Nat.pos_of_ne_zero hc
  let l := d.lcm q
  let g := d.gcd q
  have hl : 0 < l := Nat.lcm_pos hd hq
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hd
  have hgrDvd : g ∣ r := gcd_dvd_residue_of_divisorResidueCount_pos hcpos
  have hgr : g ≤ r := Nat.le_of_dvd hr hgrDvd
  have hlg : (l : ℝ) * (g : ℝ) = (d : ℝ) * (q : ℝ) := by
    exact_mod_cast Nat.lcm_mul_gcd d q
  have hcountNat := divisorResidueCount_le_lcm hd hq r X
  have hcount : (divisorResidueCount d q r X : ℝ) ≤
      (X : ℝ) / l + 1 := by
    calc
      (divisorResidueCount d q r X : ℝ) ≤ (X / l + 1 : ℕ) := by
        exact_mod_cast hcountNat
      _ = (X / l : ℕ) + 1 := by norm_num
      _ ≤ (X : ℝ) / l + 1 := by
        gcongr
        exact Nat.cast_div_le
  have heq : ((X : ℝ) / l) * ((q : ℝ) / r) =
      ((X : ℝ) / d) * ((g : ℝ) / r) := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have hmain : ((X : ℝ) / l) * ((q : ℝ) / r) ≤ (X : ℝ) / d := by
    rw [heq]
    have hratio : (g : ℝ) / r ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      exact_mod_cast hgr
    simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (X : ℝ) / d)
  have hone : (q : ℝ) / r ≤ q := by
    exact div_le_self (by positivity) (by exact_mod_cast hr)
  calc
    (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r) ≤
        ((X : ℝ) / l + 1) * ((q : ℝ) / r) := by
      gcongr
    _ = ((X : ℝ) / l) * ((q : ℝ) / r) + (q : ℝ) / r := by ring
    _ ≤ (X : ℝ) / d + q := add_le_add hmain hone

/-- The sharper pointwise form retains the factor `gcd(d,q)/r`; summing this
factor over compatible residues produces only a harmonic loss. -/
lemma divisorResidueCount_mul_weight_le_scaled {d q r X : ℕ}
    (hd : 0 < d) (hq : 0 < q) (hr : 0 < r) :
    (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r) ≤
      ((X : ℝ) / d + q) * ((d.gcd q : ℝ) / r) := by
  by_cases hc : divisorResidueCount d q r X = 0
  · simp [hc]
    positivity
  have hcpos : 0 < divisorResidueCount d q r X := Nat.pos_of_ne_zero hc
  let l := d.lcm q
  let g := d.gcd q
  have hl : 0 < l := Nat.lcm_pos hd hq
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hd
  have hlg : (l : ℝ) * (g : ℝ) = (d : ℝ) * (q : ℝ) := by
    exact_mod_cast Nat.lcm_mul_gcd d q
  have hcountNat := divisorResidueCount_le_lcm hd hq r X
  have hcount : (divisorResidueCount d q r X : ℝ) ≤
      (X : ℝ) / l + 1 := by
    calc
      (divisorResidueCount d q r X : ℝ) ≤ (X / l + 1 : ℕ) := by
        exact_mod_cast hcountNat
      _ = (X / l : ℕ) + 1 := by norm_num
      _ ≤ (X : ℝ) / l + 1 := by
        gcongr
        exact Nat.cast_div_le
  have heq : ((X : ℝ) / l) * ((q : ℝ) / r) =
      ((X : ℝ) / d) * ((g : ℝ) / r) := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have hone : (q : ℝ) / r ≤ (q : ℝ) * ((g : ℝ) / r) := by
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    gcongr
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
    simpa using mul_le_mul_of_nonneg_right hg1 (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ r))
  change _ ≤ ((X : ℝ) / d + q) * ((g : ℝ) / r)
  calc
    (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r) ≤
        ((X : ℝ) / l + 1) * ((q : ℝ) / r) := by gcongr
    _ = ((X : ℝ) / l) * ((q : ℝ) / r) + (q : ℝ) / r := by ring
    _ ≤ ((X : ℝ) / d) * ((g : ℝ) / r) +
        (q : ℝ) * ((g : ℝ) / r) := add_le_add heq.le hone
    _ = ((X : ℝ) / d + q) * ((g : ℝ) / r) := by ring

/-- Compatible residues become distinct positive quotients after division by
`gcd(d,q)`, so their scaled reciprocal sum is harmonic. -/
lemma sum_gcd_div_residue_nonzero_le_harmonic {d q X n : ℕ}
    (hd : 0 < d) :
    (∑ r ∈ (Finset.Icc 1 n).filter
        (fun r ↦ divisorResidueCount d q r X ≠ 0),
        (d.gcd q : ℝ) / r) ≤ 1 + Real.log n := by
  let g := d.gcd q
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hd
  let R := (Finset.Icc 1 n).filter fun r ↦ divisorResidueCount d q r X ≠ 0
  let f : ℕ → ℕ := fun r ↦ r / g
  have hdvd : ∀ r ∈ R, g ∣ r := by
    intro r hr
    have hc : divisorResidueCount d q r X ≠ 0 := (Finset.mem_filter.mp hr).2
    exact gcd_dvd_residue_of_divisorResidueCount_pos (Nat.pos_of_ne_zero hc)
  have hinj : Set.InjOn f R := by
    intro a ha b hb hab
    have haD := Nat.mul_div_cancel' (hdvd a ha)
    have hbD := Nat.mul_div_cancel' (hdvd b hb)
    dsimp [f] at hab
    calc
      a = g * (a / g) := haD.symm
      _ = g * (b / g) := by rw [hab]
      _ = b := hbD
  have himage : R.image f ⊆ Finset.Icc 1 n := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    have hrI : r ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hr).1
    have hrpos : 0 < r := (Finset.mem_Icc.mp hrI).1
    have hdivpos : 0 < r / g :=
      Nat.div_pos (Nat.le_of_dvd hrpos (hdvd r hr)) hg
    exact Finset.mem_Icc.mpr
      ⟨hdivpos, (Nat.div_le_self r g).trans (Finset.mem_Icc.mp hrI).2⟩
  have hterm : ∀ r ∈ R, (g : ℝ) / r = ((r / g : ℕ) : ℝ)⁻¹ := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    have hg0 : (g : ℝ) ≠ 0 := by positivity
    have hq0 : ((r / g : ℕ) : ℝ) ≠ 0 := by
      have hkpos := Nat.div_pos (Nat.le_of_dvd hrpos (hdvd r hr)) hg
      exact_mod_cast hkpos.ne'
    have heq : g * (r / g) = r := Nat.mul_div_cancel' (hdvd r hr)
    calc
      (g : ℝ) / r = (g : ℝ) / ((g : ℝ) * (r / g : ℕ)) := by
        congr 1
        exact_mod_cast heq.symm
      _ = ((r / g : ℕ) : ℝ)⁻¹ := by field_simp
  change (∑ r ∈ R, (g : ℝ) / r) ≤ _
  calc
    (∑ r ∈ R, (g : ℝ) / r) =
        ∑ r ∈ R, ((f r : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hterm r hr
    _ = ∑ k ∈ R.image f, (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by intros; positivity)
    _ ≤ 1 + Real.log n := sum_Icc_inv_natCast_le_one_add_log n

/-- Aggregate weighted count for all nonzero residues in an initial range. -/
lemma sum_divisorResidueCount_weight_le {d q X n : ℕ}
    (hd : 0 < d) (hq : 0 < q) :
    (∑ r ∈ Finset.Icc 1 n,
        (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r)) ≤
      ((X : ℝ) / d + q) * (1 + Real.log n) := by
  let R := (Finset.Icc 1 n).filter fun r ↦ divisorResidueCount d q r X ≠ 0
  have hrestrict :
      (∑ r ∈ Finset.Icc 1 n,
          (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r)) =
        ∑ r ∈ R,
          (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r) := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    intro r hrI hrR
    simp only [R, Finset.mem_filter, hrI, true_and, not_not] at hrR
    simp [hrR]
  rw [hrestrict]
  calc
    (∑ r ∈ R, (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ R, ((X : ℝ) / d + q) * ((d.gcd q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact divisorResidueCount_mul_weight_le_scaled hd hq
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    _ = ((X : ℝ) / d + q) *
        ∑ r ∈ R, ((d.gcd q : ℝ) / r) := by
      rw [Finset.mul_sum]
    _ ≤ ((X : ℝ) / d + q) * (1 + Real.log n) := by
      gcongr
      exact sum_gcd_div_residue_nonzero_le_harmonic hd

/-- Interchange the integer variable and the selected divisor.  The inner
cardinality after the interchange is exactly `divisorResidueCount`. -/
lemma sum_v_sum_d_dvd_eq (f : ℕ → ℝ) (q r X D : ℕ) :
    (∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v), f d) =
      ∑ d ∈ Finset.Icc 1 D, f d * divisorResidueCount d q r X := by
  classical
  calc
    (∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v), f d) =
        ∑ v ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 D,
          if v % q = r ∧ d ∣ v then f d else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvr : v % q = r
      · simp only [hvr, if_true, true_and]
        rw [Finset.sum_filter]
      · simp [hvr]
    _ = ∑ d ∈ Finset.Icc 1 D, ∑ v ∈ Finset.Icc 1 X,
          if v % q = r ∧ d ∣ v then f d else 0 := by rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 D, f d * divisorResidueCount d q r X := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ v ∈ Finset.Icc 1 X,
            if v % q = r ∧ d ∣ v then f d else 0) =
            ∑ _v ∈ (Finset.Icc 1 X).filter
              (fun v ↦ v % q = r ∧ d ∣ v), f d := by
          rw [Finset.sum_filter]
        _ = f d * divisorResidueCount d q r X := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hset : (Finset.Icc 1 X).filter (fun v ↦ v % q = r ∧ d ∣ v) =
              (Finset.Icc 1 X).filter (fun v ↦ d ∣ v ∧ v % q = r) := by
            ext v
            simp [and_comm]
          rw [hset, divisorResidueCount]
          ring

/-- Bounded positive factorizations of `v`. -/
def factorPairCount (v M N : ℕ) : ℕ :=
  (((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    x.1 * x.2 = v).card

/-- The elementary divisor bound behind the residue-pair estimates: a bounded
factorization is determined by its first (divisor) coordinate. -/
lemma factorPairCount_le_card_divisors {v M N : ℕ} (hv : v ≠ 0) :
    factorPairCount v M N ≤ v.divisors.card := by
  let s := ((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    x.1 * x.2 = v
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1) s := by
    intro x hx y hy hxy
    have hxmem := Finset.mem_filter.mp hx
    have hymem := Finset.mem_filter.mp hy
    have hxfirst := (Finset.mem_product.mp hxmem.1).1
    have hxpos : 0 < x.1 := by
      exact (Finset.mem_Icc.mp hxfirst).1
    apply Prod.ext hxy
    apply mul_left_cancel₀ hxpos.ne'
    calc
      x.1 * x.2 = v := hxmem.2
      _ = y.1 * y.2 := hymem.2.symm
      _ = x.1 * y.2 := congrArg (fun a => a * y.2) hxy.symm
  have hsubset : s.image (fun x : ℕ × ℕ => x.1) ⊆ v.divisors := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, hxs, rfl⟩ := hm
    have hxeq := (Finset.mem_filter.mp hxs).2
    exact Nat.mem_divisors.mpr ⟨⟨x.2, hxeq.symm⟩, hv⟩
  calc
    factorPairCount v M N = s.card := by rfl
    _ = (s.image (fun x : ℕ × ℕ => x.1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ v.divisors.card := Finset.card_le_card hsubset

/-- Bounded factorizations with a fixed positive coefficient. -/
def scaledFactorPairCount (c v M N : ℕ) : ℕ :=
  (((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    c * x.1 * x.2 = v).card

lemma scaledFactorPairCount_le_card_divisors {c v M N : ℕ}
    (hc : 0 < c) (hv : v ≠ 0) :
    scaledFactorPairCount c v M N ≤ v.divisors.card := by
  let s := ((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x =>
    c * x.1 * x.2 = v
  let f : ℕ × ℕ → ℕ := fun x => c * x.1
  have hinj : Set.InjOn f s := by
    intro x hx y hy hxy
    have hxmem := Finset.mem_filter.mp hx
    have hymem := Finset.mem_filter.mp hy
    have hxfirst := (Finset.mem_product.mp hxmem.1).1
    have hxpos : 0 < x.1 := (Finset.mem_Icc.mp hxfirst).1
    have hfirst : x.1 = y.1 := by
      exact mul_left_cancel₀ hc.ne' hxy
    apply Prod.ext hfirst
    apply mul_left_cancel₀ (mul_pos hc hxpos).ne'
    calc
      (c * x.1) * x.2 = v := hxmem.2
      _ = (c * y.1) * y.2 := hymem.2.symm
      _ = (c * x.1) * y.2 := by rw [hfirst]
  have hsubset : s.image f ⊆ v.divisors := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, hxs, rfl⟩ := hm
    have hxeq := (Finset.mem_filter.mp hxs).2
    exact Nat.mem_divisors.mpr ⟨⟨x.2, hxeq.symm⟩, hv⟩
  calc
    scaledFactorPairCount c v M N = s.card := by rfl
    _ = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ v.divisors.card := Finset.card_le_card hsubset

/-- Each modular residue count is bounded by the divisor sum over the exact
integer products in that residue class. -/
lemma residuePairCount_le_sum_card_divisors (q r M N : ℕ) :
    residuePairCount q r M N ≤
      ∑ v ∈ (Finset.Icc 1 (2 * M * N)).filter (fun v => v % q = r),
        v.divisors.card := by
  let box := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let s := box.filter fun x => (2 * x.1 * x.2) % q = r
  let f : ℕ × ℕ → ℕ := fun x => 2 * x.1 * x.2
  let t := (Finset.Icc 1 (2 * M * N)).filter fun v => v % q = r
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo f t := by
    intro x hx
    have hxmem := Finset.mem_filter.mp hx
    have hxm := (Finset.mem_product.mp hxmem.1).1
    have hxu := (Finset.mem_product.mp hxmem.1).2
    have hm := Finset.mem_Icc.mp hxm
    have hu := Finset.mem_Icc.mp hxu
    have hm0 : x.1 ≠ 0 := by omega
    have hu0 : x.2 ≠ 0 := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hxmem.2⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hm0) hu0)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm.2) hu.2
  calc
    residuePairCount q r M N = s.card := by rfl
    _ = ∑ v ∈ t, (s.filter fun x => f x = v).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ v ∈ t, scaledFactorPairCount 2 v M N := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.card_le_card
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hxS := Finset.mem_filter.mp hx'.1
      exact Finset.mem_filter.mpr ⟨hxS.1, hx'.2⟩
    _ ≤ ∑ v ∈ t, v.divisors.card := by
      apply Finset.sum_le_sum
      intro v hv
      have hvpos : 0 < v := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
      exact scaledFactorPairCount_le_card_divisors (by norm_num) hvpos.ne'

/-- Dirichlet's elementary double-counting identity for the summatory divisor
function, specialized to natural cardinalities. -/
lemma sum_card_divisors_eq_sum_div (X : ℕ) :
    ∑ v ∈ Finset.Icc 1 X, v.divisors.card =
      ∑ d ∈ Finset.Icc 1 X, X / d := by
  have hinterval : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n
    simp
    omega
  rw [← hinterval]
  simpa [ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div X

/-- Elementary first-moment divisor estimate.  The sharper residue-uniform
high-moment form is the remaining number-theoretic input in Nguyen--Vu. -/
lemma sum_card_divisors_le (X : ℕ) :
    (∑ v ∈ Finset.Icc 1 X, (v.divisors.card : ℝ)) ≤
      X * (1 + Real.log X) := by
  calc
    (∑ v ∈ Finset.Icc 1 X, (v.divisors.card : ℝ)) =
        ((∑ v ∈ Finset.Icc 1 X, v.divisors.card : ℕ) : ℝ) := by
      norm_cast
    _ = ((∑ d ∈ Finset.Icc 1 X, X / d : ℕ) : ℝ) := by
      rw [sum_card_divisors_eq_sum_div]
    _ = ∑ d ∈ Finset.Icc 1 X, ((X / d : ℕ) : ℝ) := by norm_cast
    _ ≤ ∑ d ∈ Finset.Icc 1 X, (X : ℝ) / d := by
      apply Finset.sum_le_sum
      intro d _
      exact Nat.cast_div_le
    _ ≤ X * (1 + Real.log X) := sum_Icc_natCast_div_le X X

/-- A global first-moment consequence for every residue count.  Nguyen--Vu's
Weyl theorem improves this by a factor of the modulus, using divisor moments. -/
lemma residuePairCount_le_firstMoment (q r M N : ℕ) :
    (residuePairCount q r M N : ℝ) ≤
      (2 * M * N : ℕ) * (1 + Real.log (2 * M * N : ℕ)) := by
  let X := 2 * M * N
  calc
    (residuePairCount q r M N : ℝ) ≤
        ((∑ v ∈ (Finset.Icc 1 X).filter (fun v => v % q = r),
          v.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast residuePairCount_le_sum_card_divisors q r M N
    _ = ∑ v ∈ (Finset.Icc 1 X).filter (fun v => v % q = r),
        (v.divisors.card : ℝ) := by norm_cast
    _ ≤ ∑ v ∈ Finset.Icc 1 X, (v.divisors.card : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intros; positivity)
    _ ≤ X * (1 + Real.log X) := sum_card_divisors_le X

/-- A polynomial in a prime-power exponent is globally dominated by a fixed
geometric sequence of ratio `3/2`.  This supplies the prime-power hypothesis
for the Halberstam--Richert divisor-moment estimate. -/
lemma exists_primePower_poly_bound (b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      ((j + 2 : ℕ) : ℝ) ^ b ≤ C * ((3 : ℝ) / 2) ^ j := by
  have htend :
      Tendsto (fun n : ℕ => (n : ℝ) ^ b / ((3 : ℝ) / 2) ^ n)
        atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt b (by norm_num)
  obtain ⟨C₀, hC₀⟩ := htend.bddAbove_range
  let C₁ : ℝ := max 1 C₀
  have hC₁ : 0 < C₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C₁ * ((3 : ℝ) / 2) ^ 2, mul_pos hC₁ (by positivity), ?_⟩
  intro j
  have hratio :
      (((j + 2 : ℕ) : ℝ) ^ b / ((3 : ℝ) / 2) ^ (j + 2)) ≤ C₁ := by
    exact (hC₀ ⟨j + 2, rfl⟩).trans (le_max_right _ _)
  have hden : 0 < ((3 : ℝ) / 2) ^ (j + 2) := by positivity
  have hpoly :
      (((j + 2 : ℕ) : ℝ) ^ b) ≤
        C₁ * ((3 : ℝ) / 2) ^ (j + 2) :=
    (div_le_iff₀ hden).mp hratio
  calc
    (((j + 2 : ℕ) : ℝ) ^ b) ≤
        C₁ * ((3 : ℝ) / 2) ^ (j + 2) := hpoly
    _ = (C₁ * ((3 : ℝ) / 2) ^ 2) * ((3 : ℝ) / 2) ^ j := by
      rw [pow_add]
      ring

/-- The `b`-th power of the divisor function, normalized to vanish at zero as
required by the Halberstam--Richert interface. -/
noncomputable def divisorPower (b n : ℕ) : ℝ :=
  if n = 0 then 0 else (n.divisors.card : ℝ) ^ b

@[simp] lemma divisorPower_zero (b : ℕ) : divisorPower b 0 = 0 := by
  simp [divisorPower]

@[simp] lemma divisorPower_one (b : ℕ) : divisorPower b 1 = 1 := by
  simp [divisorPower]

lemma divisorPower_nonneg (b n : ℕ) : 0 ≤ divisorPower b n := by
  simp only [divisorPower]
  split_ifs <;> positivity

lemma divisorPower_mul_of_coprime (b : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    divisorPower b (m * n) = divisorPower b m * divisorPower b n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  simp only [divisorPower, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]
  rw [hmn.card_divisors_mul, Nat.cast_mul, mul_pow]

lemma divisorPower_prime_pow (b j : ℕ) {p : ℕ} (hp : p.Prime) :
    divisorPower b (p ^ (j + 1)) = ((j + 2 : ℕ) : ℝ) ^ b := by
  have hp0 : p ^ (j + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hcard : (p ^ (j + 1)).divisors.card = j + 2 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    simpa [Nat.add_assoc] using
      ArithmeticFunction.sigma_zero_apply_prime_pow (i := j + 1) hp
  rw [divisorPower, if_neg hp0, hcard]

/-- The already formalized Halberstam--Richert theorem applied to a fixed
power of the divisor function. -/
theorem exists_divisorPower_halberstam_bound (b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      HalberstamScratch.partialSum (divisorPower b) N ≤
        (HalberstamScratch.explicitMassConstant C ((3 : ℝ) / 2) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            ∏ p ∈ (N + 1).primesBelow,
              ∑' j : ℕ, divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  obtain ⟨C, hC, hpow⟩ := exists_primePower_poly_bound b
  refine ⟨C, hC, ?_⟩
  intro N hN
  apply HalberstamComplete448.halberstam_richert_explicit
      (divisorPower b)
      (divisorPower_zero b)
      (divisorPower_one b)
      (divisorPower_mul_of_coprime b)
      (divisorPower_nonneg b)
      C ((3 : ℝ) / 2) hC.le (by positivity) (by norm_num) ?_ N hN
  intro p hp j
  rw [divisorPower_prime_pow b j hp]
  exact hpow j

lemma divisorPower_local_tsum_le {b : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hpow : ∀ j : ℕ, ((j + 2 : ℕ) : ℝ) ^ b ≤ C * ((3 : ℝ) / 2) ^ j)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)) ∧
      (∑' j : ℕ, divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        1 + C / ((p : ℝ) - (3 : ℝ) / 2) := by
  have hlocal := HalberstamScratch.prime_power_local_mass
    (divisorPower b) p C ((3 : ℝ) / 2) hp
    (divisorPower_nonneg b) (divisorPower_one b) hC (by positivity)
    (by norm_num) (fun j => by rw [divisorPower_prime_pow b j hp]; exact hpow j)
  change
    (Summable fun j : ℕ =>
      ‖divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ∧
      (∑' j : ℕ, ‖divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)‖) ≤
        1 + C / ((p : ℝ) - (3 : ℝ) / 2) at hlocal
  have hnorm : ∀ j : ℕ,
      ‖divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)‖ =
        divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (divisorPower_nonneg b _) (by positivity)
  simpa only [hnorm] using hlocal

/-- Mertens' estimate turns the local divisor-power factors into a fixed real
power of `log N`. -/
lemma divisorPower_eulerProduct_le {b : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hpow : ∀ j : ℕ, ((j + 2 : ℕ) : ℝ) ^ b ≤ C * ((3 : ℝ) / 2) ^ j)
    (N : ℕ) (hN : 3 ≤ N) :
    (∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
      Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) := by
  let P := (Finset.Icc 1 N).filter Nat.Prime
  have hP : (N + 1).primesBelow = P := by
    ext p
    simp only [Nat.mem_primesBelow, P, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, Nat.le_of_lt_succ hpN⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hpN, hp⟩
  rw [hP]
  calc
    (∏ p ∈ P,
      ∑' j : ℕ, divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
        ∏ p ∈ P, Real.exp (4 * C / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hpP
        exact tsum_nonneg fun j =>
          div_nonneg (divisorPower_nonneg b _) (by positivity)
      · intro p hpP
        have hp : p.Prime := (Finset.mem_filter.mp hpP).2
        have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hden : 0 < (p : ℝ) - (3 : ℝ) / 2 := by linarith
        have hfrac :
            C / ((p : ℝ) - (3 : ℝ) / 2) ≤ 4 * C / (p : ℝ) := by
          rw [div_le_div_iff₀ hden hpPos]
          have hpineq : (p : ℝ) ≤ 4 * ((p : ℝ) - (3 : ℝ) / 2) := by
            linarith
          calc
            C * (p : ℝ) ≤ C * (4 * ((p : ℝ) - (3 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hpineq hC
            _ = 4 * C * ((p : ℝ) - (3 : ℝ) / 2) := by ring
        calc
          (∑' j : ℕ, divisorPower b (p ^ j) / ((p ^ j : ℕ) : ℝ)) ≤
              1 + C / ((p : ℝ) - (3 : ℝ) / 2) :=
            (divisorPower_local_tsum_le hC hpow hp).2
          _ ≤ 1 + 4 * C / (p : ℝ) := by linarith
          _ ≤ Real.exp (4 * C / (p : ℝ)) := by
            simpa [add_comm] using Real.add_one_le_exp (4 * C / (p : ℝ))
    _ = Real.exp (∑ p ∈ P, 4 * C / (p : ℝ)) := by
      rw [Real.exp_sum]
    _ = Real.exp (4 * C * ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left
        (by simpa [P] using Erdos448Scratch.reciprocal_prime_sum_le_log_three_log N hN)
        (mul_nonneg (by norm_num) hC)

/-- Explicit high-moment divisor bound before converting the real exponent
into a natural power of `log N`. -/
theorem exists_divisorPower_mean_exp_bound (b : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      HalberstamScratch.partialSum (divisorPower b) N ≤
        (HalberstamScratch.explicitMassConstant C ((3 : ℝ) / 2) + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hpow⟩ := exists_primePower_poly_bound b
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hraw := HalberstamComplete448.halberstam_richert_explicit
      (divisorPower b)
      (divisorPower_zero b)
      (divisorPower_one b)
      (divisorPower_mul_of_coprime b)
      (divisorPower_nonneg b)
      C ((3 : ℝ) / 2) hC.le (by positivity) (by norm_num)
      (fun p hp j => by rw [divisorPower_prime_pow b j hp]; exact hpow j)
      N (by omega)
  refine hraw.trans (mul_le_mul_of_nonneg_left
    (divisorPower_eulerProduct_le hC.le hpow N hN) ?_)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hN))
  exact div_nonneg
    (mul_nonneg
      (add_nonneg (HalberstamScratch.explicitMassConstant_nonneg hC.le (by positivity))
        (by norm_num))
      (Nat.cast_nonneg N))
    hlog.le

/-- Normalize the real logarithmic exponent produced by the Euler product to
a natural exponent, as required by the formal-conjectures statement. -/
lemma exp_mul_log_log_le_natPow {C : ℝ} (_hC : 0 ≤ C)
    (N : ℕ) (hN : 3 ≤ N) :
    Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) ≤
      (3 : ℝ) ^ ⌈4 * C⌉₊ * Real.log (N : ℝ) ^ ⌈4 * C⌉₊ := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hthreeN : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogmono : Real.log 3 ≤ Real.log (N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr (by positivity)) hthreeN
  have hlogN : (1 : ℝ) ≤ Real.log (N : ℝ) := hlog3.trans hlogmono
  let x : ℝ := 3 * Real.log (N : ℝ)
  have hxone : 1 ≤ x := by dsimp [x]; nlinarith
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hexp : 4 * C ≤ ((⌈4 * C⌉₊ : ℕ) : ℝ) := Nat.le_ceil (4 * C)
  calc
    Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) = x ^ (4 * C) := by
      rw [Real.rpow_def_of_pos hxpos]
      dsimp [x]
      congr 1
      ring
    _ ≤ x ^ (((⌈4 * C⌉₊ : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hxone hexp
    _ = x ^ (⌈4 * C⌉₊ : ℕ) := by rw [Real.rpow_natCast]
    _ = (3 : ℝ) ^ ⌈4 * C⌉₊ * Real.log (N : ℝ) ^ ⌈4 * C⌉₊ := by
      simp only [x, mul_pow]

lemma one_le_log_nat_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (1 : ℝ) ≤ Real.log (N : ℝ) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hthreeN : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact hlog3.trans <| Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (by norm_num)) (Set.mem_Ioi.mpr (by positivity)) hthreeN

/-- Fixed powers of the divisor function have polylogarithmic mean. -/
theorem exists_divisorPower_mean_log_bound (b : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧ ∀ N : ℕ, 3 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ b) ≤
        K * (N : ℝ) * Real.log (N : ℝ) ^ O := by
  obtain ⟨C, hC, hmean⟩ := exists_divisorPower_mean_exp_bound b
  let O : ℕ := ⌈4 * C⌉₊
  let A : ℝ := HalberstamScratch.explicitMassConstant C ((3 : ℝ) / 2) + 1
  let K : ℝ := A * (3 : ℝ) ^ O
  have hO : 0 < O := by
    dsimp [O]
    exact Nat.ceil_pos.mpr (mul_pos (by norm_num) hC)
  have hA : 0 < A := by
    dsimp [A]
    have hm := HalberstamScratch.explicitMassConstant_nonneg
      (lambda1 := C) (lambda2 := (3 : ℝ) / 2) hC.le (by positivity)
    linarith
  have hK : 0 < K := mul_pos hA (by positivity)
  refine ⟨K, hK, O, hO, ?_⟩
  intro N hN
  have hlog : (1 : ℝ) ≤ Real.log (N : ℝ) := one_le_log_nat_of_three_le hN
  have hcoeff : 0 ≤ A * (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (mul_nonneg hA.le (Nat.cast_nonneg N)) (zero_le_one.trans hlog)
  have hpowNonneg :
      0 ≤ (3 : ℝ) ^ O * Real.log (N : ℝ) ^ O := by positivity
  calc
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ b) =
        HalberstamScratch.partialSum (divisorPower b) N := by
      unfold HalberstamScratch.partialSum
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hn).1
        omega
      rw [divisorPower, if_neg hn0]
    _ ≤ A * (N : ℝ) / Real.log (N : ℝ) *
          Real.exp (4 * C * Real.log (3 * Real.log (N : ℝ))) := by
      simpa [A] using hmean N hN
    _ ≤ A * (N : ℝ) / Real.log (N : ℝ) *
          ((3 : ℝ) ^ O * Real.log (N : ℝ) ^ O) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      simpa [O] using exp_mul_log_log_le_natPow hC.le N hN
    _ ≤ (A * (N : ℝ)) *
          ((3 : ℝ) ^ O * Real.log (N : ℝ) ^ O) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_self (mul_nonneg hA.le (Nat.cast_nonneg N)) hlog) hpowNonneg
    _ = K * (N : ℝ) * Real.log (N : ℝ) ^ O := by
      dsimp [K]
      ring

/-- Discrete Abel summation for nonnegative-indexed sequences whose zeroth
term vanishes.  The form with closed natural intervals is convenient for
arithmetic functions. -/
lemma weighted_sum_eq_partial_sums (a : ℕ → ℝ) (ha0 : a 0 = 0)
    {N : ℕ} (hN : 0 < N) :
    ∑ i ∈ Finset.Icc 1 N, a i / (i : ℝ) =
      (∑ i ∈ Finset.Icc 1 N, a i) / (N : ℝ) +
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, a j) / ((i : ℝ) * (i + 1)) := by
  have hbp := Finset.sum_Ioc_by_parts
    (fun i : ℕ ↦ ((i : ℝ)⁻¹)) a (m := 0) (n := N) hN
  simp only [smul_eq_mul] at hbp
  rw [show Finset.Ioc 0 N = Finset.Icc 1 N by ext i; simp; omega] at hbp
  have hrangeN : ∑ i ∈ Finset.range (N + 1), a i =
      ∑ i ∈ Finset.Icc 1 N, a i := by
    calc
      ∑ i ∈ Finset.range (N + 1), a i =
          (∑ i ∈ (Finset.range (N + 1)).erase 0, a i) + a 0 :=
        (Finset.sum_erase_add _ _ (by simp)).symm
      _ = ∑ i ∈ (Finset.range (N + 1)).erase 0, a i := by rw [ha0, add_zero]
      _ = ∑ i ∈ Finset.Icc 1 N, a i := by
        congr 1
        ext i
        simp
        omega
  have hrange0 : ∑ i ∈ Finset.range (0 + 1), a i = 0 := by simp [ha0]
  rw [hrangeN, hrange0] at hbp
  simp only [inv_one, mul_zero, sub_zero] at hbp
  rw [show Finset.Ioc 0 (N - 1) = Finset.Icc 1 (N - 1) by ext i; simp; omega] at hbp
  calc
    ∑ i ∈ Finset.Icc 1 N, a i / (i : ℝ) =
        ∑ i ∈ Finset.Icc 1 N, ((i : ℝ)⁻¹) * a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv, mul_comm]
    _ = (N : ℝ)⁻¹ * (∑ i ∈ Finset.Icc 1 N, a i) -
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (((i + 1 : ℕ) : ℝ)⁻¹ - (i : ℝ)⁻¹) *
            (∑ j ∈ Finset.range (i + 1), a j) := hbp
    _ = (∑ i ∈ Finset.Icc 1 N, a i) / (N : ℝ) +
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, a j) / ((i : ℝ) * (i + 1)) := by
      rw [sub_eq_add_neg, div_eq_mul_inv,
        mul_comm (∑ i ∈ Finset.Icc 1 N, a i)]
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hirange : ∑ j ∈ Finset.range (i + 1), a j =
          ∑ j ∈ Finset.Icc 1 i, a j := by
        calc
          ∑ j ∈ Finset.range (i + 1), a j =
              (∑ j ∈ (Finset.range (i + 1)).erase 0, a j) + a 0 :=
            (Finset.sum_erase_add _ _ (by simp)).symm
          _ = ∑ j ∈ (Finset.range (i + 1)).erase 0, a j := by rw [ha0, add_zero]
          _ = ∑ j ∈ Finset.Icc 1 i, a j := by
            congr 1
            ext j
            simp
            omega
      rw [hirange]
      have hi0 : (i : ℝ) ≠ 0 := by positivity
      have his0 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num [Nat.cast_add, Nat.cast_one] at his0 ⊢
      field_simp
      ring

lemma small_divisorPower_partial_sum_le (b : ℕ) {i : ℕ}
    (hi : 1 ≤ i) (hi3 : i < 3) :
    (∑ n ∈ Finset.Icc 1 i, (n.divisors.card : ℝ) ^ b) ≤
      (3 : ℝ) ^ (b + 1) := by
  interval_cases i
  · simp only [Finset.Icc_self, Finset.sum_singleton, Nat.divisors_one,
      Finset.card_singleton, Nat.cast_one, one_pow]
    exact one_le_pow₀ (by norm_num)
  · have hcard (n : ℕ) : (n.divisors.card : ℝ) ≤ n := by
      exact_mod_cast Nat.card_divisors_le_self n
    calc
      (∑ n ∈ Finset.Icc 1 2, (n.divisors.card : ℝ) ^ b) ≤
          ∑ _n ∈ Finset.Icc 1 2, (2 : ℝ) ^ b := by
        gcongr with n hn
        have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        exact (hcard n).trans hn2
      _ = 2 * (2 : ℝ) ^ b := by norm_num
      _ ≤ 3 * (3 : ℝ) ^ b := by gcongr <;> norm_num
      _ = (3 : ℝ) ^ (b + 1) := by rw [pow_succ]; ring

/-- The harmonic-weighted form of the fixed divisor-moment estimate.  This is
the partial-summation input used after the small-divisor selection. -/
theorem exists_weighted_divisorPower_log_bound (b : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧ ∀ N : ℕ, 3 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ b / (n : ℝ)) ≤
        K * Real.log (N : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hmean⟩ := exists_divisorPower_mean_log_bound b
  let K₀ : ℝ := K + (3 : ℝ) ^ (b + 1)
  refine ⟨3 * K₀, mul_pos (by norm_num) ?_, O + 1, by omega, ?_⟩
  · dsimp [K₀]
    positivity
  intro N hN
  have hNpos : 0 < N := by omega
  have hlog : (1 : ℝ) ≤ Real.log (N : ℝ) := one_le_log_nat_of_three_le hN
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  let L : ℝ := Real.log (N : ℝ) ^ O
  have hL : 1 ≤ L := by
    dsimp [L]
    exact one_le_pow₀ hlog
  have hpartial : ∀ i ∈ Finset.Icc 1 N,
      (∑ n ∈ Finset.Icc 1 i, divisorPower b n) ≤ K₀ * (i : ℝ) * L := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2
    have hsumEq : (∑ n ∈ Finset.Icc 1 i, divisorPower b n) =
        ∑ n ∈ Finset.Icc 1 i, (n.divisors.card : ℝ) ^ b := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
      simp [divisorPower, hn0]
    rw [hsumEq]
    by_cases hi3 : 3 ≤ i
    · have hlogi : 0 ≤ Real.log (i : ℝ) :=
        (one_le_log_nat_of_three_le hi3).trans' zero_le_one
      have hlogmono : Real.log (i : ℝ) ≤ Real.log (N : ℝ) := by
        apply Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hi1)))
          (Set.mem_Ioi.mpr (by positivity))
        exact_mod_cast hiN
      have hpow : Real.log (i : ℝ) ^ O ≤ L := by
        dsimp [L]
        exact pow_le_pow_left₀ hlogi hlogmono O
      calc
        (∑ n ∈ Finset.Icc 1 i, (n.divisors.card : ℝ) ^ b) ≤
            K * (i : ℝ) * Real.log (i : ℝ) ^ O := hmean i hi3
        _ ≤ K * (i : ℝ) * L := by gcongr
        _ ≤ K₀ * (i : ℝ) * L := by
          gcongr
          dsimp [K₀]
          exact le_add_of_nonneg_right (by positivity)
    · have hsmall := small_divisorPower_partial_sum_le b hi1 (by omega)
      calc
        (∑ n ∈ Finset.Icc 1 i, (n.divisors.card : ℝ) ^ b) ≤
            (3 : ℝ) ^ (b + 1) := hsmall
        _ ≤ K₀ := by dsimp [K₀]; linarith
        _ ≤ K₀ * (i : ℝ) * L := by
          have hiReal : (1 : ℝ) ≤ i := by exact_mod_cast hi1
          have hKi : K₀ ≤ K₀ * (i : ℝ) := by
            nlinarith [mul_nonneg hK₀.le (sub_nonneg.mpr (sub_le_sub_right hiReal 1))]
          have hKi0 : 0 ≤ K₀ * (i : ℝ) := mul_nonneg hK₀.le (by positivity)
          exact hKi.trans (by nlinarith [mul_nonneg hKi0 (sub_nonneg.mpr (sub_le_sub_right hL 1))])
  have hweighted := weighted_sum_eq_partial_sums
    (divisorPower b) (divisorPower_zero b) hNpos
  have hleft :
      (∑ n ∈ Finset.Icc 1 N, divisorPower b n / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ b / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    simp [divisorPower, hn0]
  rw [hleft] at hweighted
  rw [hweighted]
  have hmain :
      (∑ i ∈ Finset.Icc 1 N, divisorPower b i) / (N : ℝ) ≤ K₀ * L := by
    have hpartN := hpartial N (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hterms :
      (∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, divisorPower b j) /
            ((i : ℝ) * (i + 1))) ≤
        K₀ * L * ∑ i ∈ Finset.Icc 1 (N - 1), (i : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2.trans (Nat.sub_le N 1)
    have hpart := hpartial i (Finset.mem_Icc.mpr ⟨hi1, hiN⟩)
    have hiPos : (0 : ℝ) < i := by positivity
    have hisPos : (0 : ℝ) < i + 1 := by positivity
    calc
      (∑ j ∈ Finset.Icc 1 i, divisorPower b j) /
          ((i : ℝ) * (i + 1)) ≤
          (K₀ * (i : ℝ) * L) / ((i : ℝ) * (i + 1)) := by
        exact div_le_div_of_nonneg_right hpart (mul_nonneg hiPos.le hisPos.le)
      _ = K₀ * L / ((i : ℝ) + 1) := by field_simp
      _ ≤ K₀ * L / (i : ℝ) := by
        exact div_le_div_of_nonneg_left (mul_nonneg hK₀.le (zero_le_one.trans hL))
          hiPos (by linarith)
      _ = K₀ * L * (i : ℝ)⁻¹ := by rw [div_eq_mul_inv]
  have hharmonic :
      (∑ i ∈ Finset.Icc 1 (N - 1), (i : ℝ)⁻¹) ≤
        1 + Real.log (N : ℝ) := by
    calc
      (∑ i ∈ Finset.Icc 1 (N - 1), (i : ℝ)⁻¹) =
          (harmonic (N - 1) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 1 + Real.log (N - 1 : ℕ) := harmonic_le_one_add_log (N - 1)
      _ ≤ 1 + Real.log (N : ℝ) := by
        have hmono : Real.log (N - 1 : ℕ) ≤ Real.log (N : ℝ) := by
          apply Real.strictMonoOn_log.monotoneOn
            (Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < N - 1)))
            (Set.mem_Ioi.mpr (by positivity))
          exact_mod_cast (Nat.sub_le N 1)
        linarith
  calc
    (∑ i ∈ Finset.Icc 1 N, divisorPower b i) / (N : ℝ) +
        ∑ i ∈ Finset.Icc 1 (N - 1),
          (∑ j ∈ Finset.Icc 1 i, divisorPower b j) /
            ((i : ℝ) * (i + 1)) ≤
        K₀ * L + K₀ * L * (1 + Real.log (N : ℝ)) := by
      gcongr
      exact hterms.trans (mul_le_mul_of_nonneg_left hharmonic
        (mul_nonneg hK₀.le (zero_le_one.trans hL)))
    _ ≤ 3 * K₀ * Real.log (N : ℝ) ^ (O + 1) := by
      dsimp [L]
      rw [pow_succ]
      have hKL : 0 ≤ K₀ * Real.log (N : ℝ) ^ O :=
        mul_nonneg hK₀.le (zero_le_one.trans (one_le_pow₀ hlog))
      calc
        K₀ * Real.log (N : ℝ) ^ O +
            K₀ * Real.log (N : ℝ) ^ O * (1 + Real.log (N : ℝ)) =
            (K₀ * Real.log (N : ℝ) ^ O) * (2 + Real.log (N : ℝ)) := by ring
        _ ≤ (K₀ * Real.log (N : ℝ) ^ O) *
            (3 * Real.log (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hKL
        _ = 3 * K₀ * (Real.log (N : ℝ) ^ O * Real.log (N : ℝ)) := by ring

/-! ## The small-divisor selection in Nguyen--Vu's Weyl estimate -/

/-- Select the first entry from every consecutive block of four entries.
Applied to the increasing list of low-exponent prime factors, this is the
deterministic divisor used in Nguyen--Vu Lemma 6.1 (with `k = 4`). -/
def quarterHeads : List ℕ → List ℕ
  | a :: _b :: _c :: _d :: l => a :: quarterHeads l
  | _ => []

lemma quarterHeads_sublist : ∀ l : List ℕ, List.Sublist (quarterHeads l) l
  | [] => by simp [quarterHeads]
  | [_a] => by simp [quarterHeads]
  | [_a, _b] => by simp [quarterHeads]
  | [_a, _b, _c] => by simp [quarterHeads]
  | a :: b :: c :: d :: l => by
      simp only [quarterHeads]
      exact ((((quarterHeads_sublist l).cons d).cons c).cons b).cons_cons a

lemma four_mul_length_quarterHeads_le : ∀ l : List ℕ,
    4 * (quarterHeads l).length ≤ l.length
  | [] => by simp [quarterHeads]
  | [_a] => by simp [quarterHeads]
  | [_a, _b] => by simp [quarterHeads]
  | [_a, _b, _c] => by simp [quarterHeads]
  | _a :: _b :: _c :: _d :: l => by
      have ih := four_mul_length_quarterHeads_le l
      simp only [quarterHeads, List.length_cons]
      omega

lemma length_le_four_mul_length_quarterHeads_add_three : ∀ l : List ℕ,
    l.length ≤ 4 * (quarterHeads l).length + 3
  | [] => by simp [quarterHeads]
  | [_a] => by simp [quarterHeads]
  | [_a, _b] => by simp [quarterHeads]
  | [_a, _b, _c] => by simp [quarterHeads]
  | _a :: _b :: _c :: _d :: l => by
      have ih := length_le_four_mul_length_quarterHeads_add_three l
      simp only [quarterHeads, List.length_cons]
      omega

/-- The fourth power of the selected product is bounded by the product of
the full increasing list. -/
lemma quarterHeads_prod_pow_four_le_prod : ∀ {l : List ℕ}, l.SortedLE →
    (∀ x ∈ l, 1 ≤ x) → (quarterHeads l).prod ^ 4 ≤ l.prod
  | [], _hsort, _hone => by simp [quarterHeads]
  | [a], _hsort, hone => by simpa [quarterHeads] using hone a (by simp)
  | [a, b], _hsort, hone => by
      simp only [quarterHeads, List.prod_cons, List.prod_nil, mul_one, one_pow]
      exact one_le_mul (hone a (by simp)) (hone b (by simp))
  | [a, b, c], _hsort, hone => by
      simp only [quarterHeads, List.prod_cons, List.prod_nil, mul_one, one_pow]
      exact one_le_mul (hone a (by simp))
        (one_le_mul (hone b (by simp)) (hone c (by simp)))
  | a :: b :: c :: d :: l, hsort, hone => by
      have hpw : (a :: b :: c :: d :: l).Pairwise (· ≤ ·) := hsort.pairwise
      have ha : ∀ x ∈ b :: c :: d :: l, a ≤ x :=
        (List.pairwise_cons.mp hpw).1
      have hab : a ≤ b := ha b (by simp)
      have hac : a ≤ c := ha c (by simp)
      have had : a ≤ d := ha d (by simp)
      have hrest : l.SortedLE := by
        exact ((List.pairwise_cons.mp
          (List.pairwise_cons.mp
            (List.pairwise_cons.mp
              (List.pairwise_cons.mp hpw).2).2).2).2).sortedLE
      have hrestOne : ∀ x ∈ l, 1 ≤ x := by
        intro x hx
        exact hone x (by simp [hx])
      have hih := quarterHeads_prod_pow_four_le_prod hrest hrestOne
      simp only [quarterHeads, List.prod_cons]
      calc
        (a * (quarterHeads l).prod) ^ 4 =
            a * a * a * a * ((quarterHeads l).prod ^ 4) := by ring
        _ ≤ a * b * c * d * l.prod := by gcongr
        _ = a * (b * (c * (d * l.prod))) := by ring

lemma quarterHeads_nodup {l : List ℕ} (hl : l.Nodup) :
    (quarterHeads l).Nodup :=
  (quarterHeads_sublist l).nodup hl

/-- Prime factors occurring to exponent less than four. -/
def lowPrimes (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => n.factorization p < 4

def highPrimes (n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => ¬n.factorization p < 4

def lowPrimePart (n : ℕ) : ℕ :=
  ∏ p ∈ lowPrimes n, p ^ n.factorization p

def highPrimePart (n : ℕ) : ℕ :=
  ∏ p ∈ highPrimes n, p ^ n.factorization p

/-- Increasing list of the low-exponent prime factors. -/
def lowPrimeList (n : ℕ) : List ℕ := (lowPrimes n).sort (· ≤ ·)

/-- Product of the first prime in every block of four low-exponent primes. -/
def lowPrimeQuarterProduct (n : ℕ) : ℕ :=
  (quarterHeads (lowPrimeList n)).prod

def selectedLowPrimes (n : ℕ) : Finset ℕ :=
  (quarterHeads (lowPrimeList n)).toFinset

/-- Nguyen--Vu's small divisor for `k = 4`: take fourth-root exponents and
adjoin the first low prime in every block of four. -/
def nvSmallDivisor (n : ℕ) : ℕ :=
  Nat.floorRoot 4 n * lowPrimeQuarterProduct n

lemma lowPrimeList_sorted (n : ℕ) : (lowPrimeList n).SortedLE :=
  (Finset.sortedLT_sort (lowPrimes n)).sortedLE

lemma lowPrimeList_nodup (n : ℕ) : (lowPrimeList n).Nodup := by
  exact Finset.sort_nodup _ _

lemma mem_lowPrimeList_iff {n p : ℕ} :
    p ∈ lowPrimeList n ↔ p ∈ lowPrimes n := by
  simp [lowPrimeList]

lemma one_le_of_mem_lowPrimeList {n p : ℕ} (hp : p ∈ lowPrimeList n) :
    1 ≤ p := by
  have hp' : p ∈ n.primeFactors :=
    (Finset.mem_filter.mp (mem_lowPrimeList_iff.mp hp)).1
  exact (Nat.prime_of_mem_primeFactors hp').one_le

lemma selectedLowPrimes_subset_lowPrimes (n : ℕ) :
    selectedLowPrimes n ⊆ lowPrimes n := by
  intro p hp
  have hpList : p ∈ quarterHeads (lowPrimeList n) := by
    simpa [selectedLowPrimes] using hp
  exact mem_lowPrimeList_iff.mp ((quarterHeads_sublist _).mem hpList)

lemma prime_of_mem_selectedLowPrimes {n p : ℕ}
    (hp : p ∈ selectedLowPrimes n) : p.Prime := by
  have hpLow := selectedLowPrimes_subset_lowPrimes n hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpLow).1

lemma lowPrimeQuarterProduct_eq_prod_selected (n : ℕ) :
    lowPrimeQuarterProduct n = ∏ p ∈ selectedLowPrimes n, p := by
  unfold lowPrimeQuarterProduct selectedLowPrimes
  rw [List.prod_toFinset (fun p : ℕ => p)
    (quarterHeads_nodup (lowPrimeList_nodup n))]
  simp

lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      rw [hp.coprime_iff_not_dvd]
      intro hpdvd
      obtain ⟨q, hqs, hpq⟩ :=
        (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hpdvd
      have hqp := hs' q hqs
      have hqpEq : q = p := (hqp.dvd_iff_eq hp.ne_one).mp hpq
      exact hps (hqpEq ▸ hqs)
    rw [Finset.prod_insert hps]
    exact (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, ih hs'⟩

lemma card_divisors_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
  have hne : (∏ p ∈ s, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hs p hp).ne_zero
  have hsq : Squarefree (∏ p ∈ s, p) := squarefree_prod_primes s hs
  rw [Nat.card_divisors hne, Nat.primeFactors_prod hs]
  calc
    (∏ p ∈ s, ((∏ q ∈ s, q).factorization p + 1)) =
        ∏ _p ∈ s, 2 := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.factorization_eq_one_of_squarefree hsq (hs p hp)
        (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp)]
    _ = 2 ^ s.card := by simp

lemma card_divisors_lowPrimeQuarterProduct (n : ℕ) :
    (lowPrimeQuarterProduct n).divisors.card =
      2 ^ (quarterHeads (lowPrimeList n)).length := by
  rw [lowPrimeQuarterProduct_eq_prod_selected]
  rw [card_divisors_prod_primes (selectedLowPrimes n)
    (fun p hp => prime_of_mem_selectedLowPrimes hp)]
  congr 1
  simpa [selectedLowPrimes] using
    (List.toFinset_card_of_nodup
      (quarterHeads_nodup (lowPrimeList_nodup n)))

lemma lowPrimeQuarterProduct_pow_four_le_prod (n : ℕ) :
    lowPrimeQuarterProduct n ^ 4 ≤
      ∏ p ∈ lowPrimes n, p := by
  have hsel := quarterHeads_prod_pow_four_le_prod (lowPrimeList_sorted n)
    (fun p hp => one_le_of_mem_lowPrimeList hp)
  calc
    lowPrimeQuarterProduct n ^ 4 ≤ (lowPrimeList n).prod := hsel
    _ = ∏ p ∈ lowPrimes n, p := by
      rw [← Multiset.prod_coe]
      change (↑((lowPrimes n).sort (· ≤ ·)) : Multiset ℕ).prod = _
      rw [Finset.sort_eq]
      symm
      simpa only [Multiset.map_id', id_eq] using
        (Finset.prod_eq_multiset_prod (lowPrimes n) (fun p => p))

lemma primeFactorization_pos {n p : ℕ} (hp : p ∈ n.primeFactors) :
    0 < n.factorization p := by
  change p ∈ n.factorization.support at hp
  exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)

lemma lowPrimeProduct_le_lowPrimePart (n : ℕ) :
    (∏ p ∈ lowPrimes n, p) ≤ lowPrimePart n := by
  unfold lowPrimePart
  apply Finset.prod_le_prod' 
  intro p hp
  have hpSupport : p ∈ n.primeFactors := (Finset.mem_filter.mp hp).1
  exact Nat.le_pow (primeFactorization_pos hpSupport)

lemma lowPrimeQuarterProduct_pow_four_le_lowPrimePart (n : ℕ) :
    lowPrimeQuarterProduct n ^ 4 ≤ lowPrimePart n :=
  (lowPrimeQuarterProduct_pow_four_le_prod n).trans
    (lowPrimeProduct_le_lowPrimePart n)

lemma floorRoot_four_eq_highPrimeRootProduct {n : ℕ} (hn : n ≠ 0) :
    Nat.floorRoot 4 n =
      ∏ p ∈ highPrimes n, p ^ (n.factorization p / 4) := by
  rw [Nat.floorRoot]
  simp only [hn, OfNat.ofNat_ne_zero, false_or, ↓reduceIte]
  change (∏ p ∈ n.primeFactors, p ^ (n.factorization p / 4)) = _
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors
    (fun p => n.factorization p < 4) (fun p => p ^ (n.factorization p / 4))]
  have hlow : (∏ p ∈ lowPrimes n, p ^ (n.factorization p / 4)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hlt := (Finset.mem_filter.mp hp).2
    simp [Nat.div_eq_of_lt hlt]
  have hlow' :
      (∏ p ∈ n.primeFactors with n.factorization p < 4,
        p ^ (n.factorization p / 4)) = 1 := by
    simpa [lowPrimes] using hlow
  rw [hlow', one_mul]
  rfl

lemma floorRoot_four_pow_four_le_highPrimePart {n : ℕ} (hn : n ≠ 0) :
    Nat.floorRoot 4 n ^ 4 ≤ highPrimePart n := by
  rw [floorRoot_four_eq_highPrimeRootProduct hn]
  unfold highPrimePart
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod'
  intro p hp
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hp).1).pos
  simpa [Nat.mul_comm] using Nat.mul_div_le (n.factorization p) 4

lemma highPrimePart_mul_lowPrimePart {n : ℕ} (hn : n ≠ 0) :
    highPrimePart n * lowPrimePart n = n := by
  rw [mul_comm]
  unfold lowPrimePart highPrimePart lowPrimes highPrimes
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

lemma nvSmallDivisor_pow_four_le {n : ℕ} (hn : n ≠ 0) :
    nvSmallDivisor n ^ 4 ≤ n := by
  rw [nvSmallDivisor, mul_pow]
  calc
    Nat.floorRoot 4 n ^ 4 * lowPrimeQuarterProduct n ^ 4 ≤
        highPrimePart n * lowPrimePart n :=
      Nat.mul_le_mul (floorRoot_four_pow_four_le_highPrimePart hn)
        (lowPrimeQuarterProduct_pow_four_le_lowPrimePart n)
    _ = n := highPrimePart_mul_lowPrimePart hn

lemma primeFactors_floorRoot_four {n : ℕ} (hn : n ≠ 0) :
    (Nat.floorRoot 4 n).primeFactors = highPrimes n := by
  have hroot : Nat.floorRoot 4 n ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  ext p
  constructor
  · intro hpRoot
    have hpData := Nat.mem_primeFactors.mp hpRoot
    have hpPow : p ^ 4 ∣ n :=
      Nat.pow_dvd_iff_dvd_floorRoot.mpr hpData.2.1
    have hfour : 4 ≤ n.factorization p :=
      (hpData.1.pow_dvd_iff_le_factorization hn).mp hpPow
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr
        ⟨hpData.1, (dvd_pow_self p (by norm_num : 4 ≠ 0)).trans hpPow, hn⟩,
        by omega⟩
  · intro hpHigh
    have hpData := Finset.mem_filter.mp hpHigh
    have hpN := Nat.mem_primeFactors.mp hpData.1
    have hfour : 4 ≤ n.factorization p := by omega
    have hpPow : p ^ 4 ∣ n :=
      (hpN.1.pow_dvd_iff_le_factorization hn).mpr hfour
    exact Nat.mem_primeFactors.mpr
      ⟨hpN.1, Nat.pow_dvd_iff_dvd_floorRoot.mp hpPow, hroot⟩

lemma card_divisors_floorRoot_four {n : ℕ} (hn : n ≠ 0) :
    (Nat.floorRoot 4 n).divisors.card =
      ∏ p ∈ highPrimes n, (n.factorization p / 4 + 1) := by
  have hroot : Nat.floorRoot 4 n ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  rw [Nat.card_divisors hroot, primeFactors_floorRoot_four hn,
    Nat.factorization_floorRoot]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [Finsupp.floorDiv_apply, Nat.floorDiv_eq_div]

lemma floorRoot_four_coprime_lowPrimeQuarterProduct {n : ℕ} (hn : n ≠ 0) :
    (Nat.floorRoot 4 n).Coprime (lowPrimeQuarterProduct n) := by
  apply Nat.coprime_of_dvd
  intro p hp hproot
  intro hpquarter
  rw [lowPrimeQuarterProduct_eq_prod_selected] at hpquarter
  obtain ⟨q, hqsel, hpq⟩ :=
    (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp hpquarter
  have hqprime : q.Prime := prime_of_mem_selectedLowPrimes hqsel
  have hqp : q = p := (hqprime.dvd_iff_eq hp.ne_one).mp hpq
  have hpLow : p ∈ lowPrimes n := by
    rw [← hqp]
    exact selectedLowPrimes_subset_lowPrimes n hqsel
  have hlt : n.factorization p < 4 := (Finset.mem_filter.mp hpLow).2
  have hroot : Nat.floorRoot 4 n ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨by norm_num, hn⟩
  have hpRootFactors : p ∈ (Nat.floorRoot 4 n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hproot, hroot⟩
  have hpos := primeFactorization_pos hpRootFactors
  rw [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.floorDiv_eq_div] at hpos
  omega

lemma card_divisors_nvSmallDivisor {n : ℕ} (hn : n ≠ 0) :
    (nvSmallDivisor n).divisors.card =
      (Nat.floorRoot 4 n).divisors.card *
        2 ^ (quarterHeads (lowPrimeList n)).length := by
  rw [nvSmallDivisor,
    (floorRoot_four_coprime_lowPrimeQuarterProduct hn).card_divisors_mul,
    card_divisors_lowPrimeQuarterProduct]

lemma succ_le_div_four_succ_pow_twelve {a : ℕ} (ha : 4 ≤ a) :
    a + 1 ≤ (a / 4 + 1) ^ 12 := by
  let x := a / 4 + 1
  have hx : 2 ≤ x := by dsimp [x]; omega
  have ha' : a + 1 ≤ 4 * x := by dsimp [x]; omega
  have hxpow : 4 * x ≤ x ^ 3 := by
    have hsq : 2 ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    calc
      4 * x = 2 ^ 2 * x := by norm_num
      _ ≤ x ^ 2 * x := Nat.mul_le_mul_right x hsq
      _ = x ^ 3 := by ring
  have hmono : x ^ 3 ≤ x ^ 12 :=
    pow_le_pow_right₀ (by omega : 1 ≤ x) (by omega)
  exact ha'.trans (hxpow.trans hmono)

lemma card_divisors_le_low_pow_mul_floorRoot {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤
      4 ^ (lowPrimes n).card * (Nat.floorRoot 4 n).divisors.card ^ 12 := by
  have hsplit :
      n.divisors.card =
        (∏ p ∈ lowPrimes n, (n.factorization p + 1)) *
          ∏ p ∈ highPrimes n, (n.factorization p + 1) := by
    rw [Nat.card_divisors hn]
    unfold lowPrimes highPrimes
    exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => n.factorization p < 4)
      (fun p => n.factorization p + 1)).symm
  rw [hsplit]
  apply Nat.mul_le_mul
  · calc
      (∏ p ∈ lowPrimes n, (n.factorization p + 1)) ≤
          ∏ _p ∈ lowPrimes n, 4 := by
        apply Finset.prod_le_prod'
        intro p hp
        exact (Finset.mem_filter.mp hp).2
      _ = 4 ^ (lowPrimes n).card := by simp
  · rw [card_divisors_floorRoot_four hn, ← Finset.prod_pow]
    apply Finset.prod_le_prod'
    intro p hp
    exact succ_le_div_four_succ_pow_twelve
      (by have := (Finset.mem_filter.mp hp).2; omega)

lemma four_pow_low_card_le_selected_pow (n : ℕ) :
    4 ^ (lowPrimes n).card ≤
      64 * (2 ^ (quarterHeads (lowPrimeList n)).length) ^ 12 := by
  let t := (quarterHeads (lowPrimeList n)).length
  have hcard : (lowPrimes n).card ≤ 4 * t + 3 := by
    simpa [lowPrimeList, t] using
      length_le_four_mul_length_quarterHeads_add_three (lowPrimeList n)
  calc
    4 ^ (lowPrimes n).card ≤ 4 ^ (4 * t + 3) :=
      Nat.pow_le_pow_right (by norm_num) hcard
    _ = 64 * (256 ^ t) := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    _ ≤ 64 * (4096 ^ t) := by
      gcongr
      norm_num
    _ = 64 * (2 ^ t) ^ 12 := by
      congr 1
      calc
        4096 ^ t = (2 ^ 12) ^ t := by norm_num
        _ = 2 ^ (12 * t) := by rw [pow_mul]
        _ = 2 ^ (t * 12) := by rw [Nat.mul_comm]
        _ = (2 ^ t) ^ 12 := by rw [pow_mul]

/-- Nguyen--Vu Lemma 6.1 at the fixed value `k = 4`.  The divisor selected
above has fourth power at most `n`, and its twelfth divisor moment dominates
the full divisor count up to the absolute factor `64`. -/
theorem card_divisors_le_smallDivisor {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 64 * (nvSmallDivisor n).divisors.card ^ 12 := by
  have hbase := card_divisors_le_low_pow_mul_floorRoot hn
  have hlow := four_pow_low_card_le_selected_pow n
  rw [card_divisors_nvSmallDivisor hn, mul_pow]
  calc
    n.divisors.card ≤
        4 ^ (lowPrimes n).card * (Nat.floorRoot 4 n).divisors.card ^ 12 := hbase
    _ ≤ (64 * (2 ^ (quarterHeads (lowPrimeList n)).length) ^ 12) *
          (Nat.floorRoot 4 n).divisors.card ^ 12 := by gcongr
    _ = 64 *
        ((Nat.floorRoot 4 n).divisors.card ^ 12 *
          (2 ^ (quarterHeads (lowPrimeList n)).length) ^ 12) := by ring

lemma lowPrimeQuarterProduct_dvd (n : ℕ) : lowPrimeQuarterProduct n ∣ n := by
  rw [lowPrimeQuarterProduct_eq_prod_selected]
  apply (Finset.prod_dvd_prod_of_subset (selectedLowPrimes n) n.primeFactors
    (fun p : ℕ => p) ?_).trans (Nat.prod_primeFactors_dvd n)
  exact fun p hp => (Finset.filter_subset _ _)
    (selectedLowPrimes_subset_lowPrimes n hp)

lemma nvSmallDivisor_dvd {n : ℕ} (hn : n ≠ 0) : nvSmallDivisor n ∣ n := by
  rw [nvSmallDivisor]
  apply (floorRoot_four_coprime_lowPrimeQuarterProduct hn).mul_dvd_of_dvd_of_dvd
  · exact (dvd_pow_self (Nat.floorRoot 4 n) (by norm_num : 4 ≠ 0)).trans
      Nat.floorRoot_pow_dvd
  · exact lowPrimeQuarterProduct_dvd n

lemma nvSmallDivisor_ne_zero {n : ℕ} (hn : n ≠ 0) : nvSmallDivisor n ≠ 0 := by
  intro hd
  have hdiv := nvSmallDivisor_dvd hn
  rw [hd] at hdiv
  exact hn (zero_dvd_iff.mp hdiv)

/-- Finite-sum form of the small-divisor lemma. -/
theorem card_divisors_le_sum_smallDivisors {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤
      64 * ∑ d ∈ (n.divisors.filter fun d => d ^ 4 ≤ n),
        d.divisors.card ^ 12 := by
  let d := nvSmallDivisor n
  have hdDvd : d ∣ n := nvSmallDivisor_dvd hn
  have hd0 : d ≠ 0 := nvSmallDivisor_ne_zero hn
  have hdmem : d ∈ n.divisors.filter (fun e => e ^ 4 ≤ n) := by
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨hdDvd, hn⟩, nvSmallDivisor_pow_four_le hn⟩
  have hterm : d.divisors.card ^ 12 ≤
      ∑ e ∈ (n.divisors.filter fun e => e ^ 4 ≤ n), e.divisors.card ^ 12 := by
    exact Finset.single_le_sum
      (f := fun e => e.divisors.card ^ 12) (fun e he => Nat.zero_le _) hdmem
  exact (card_divisors_le_smallDivisor hn).trans
    (Nat.mul_le_mul_left 64 hterm)

lemma le_sqrt_sqrt_of_pow_four_le {d X : ℕ} (h : d ^ 4 ≤ X) :
    d ≤ Nat.sqrt (Nat.sqrt X) := by
  rw [Nat.le_sqrt]
  rw [Nat.le_sqrt]
  calc
    d * d * (d * d) = d ^ 4 := by ring
    _ ≤ X := h

/-- Put every selected divisor into one ambient interval depending only on
`X`.  This is the form needed to interchange divisors with residue classes. -/
lemma card_divisors_le_globalSmallDivisorSum {v X : ℕ}
    (hv : v ≠ 0) (hvX : v ≤ X) :
    (v.divisors.card : ℝ) ≤
      64 * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt X))).filter (fun d ↦ d ∣ v),
        (d.divisors.card : ℝ) ^ 12 := by
  have hsmall := card_divisors_le_sum_smallDivisors hv
  have hsubset :
      v.divisors.filter (fun d ↦ d ^ 4 ≤ v) ⊆
        (Finset.Icc 1 (Nat.sqrt (Nat.sqrt X))).filter (fun d ↦ d ∣ v) := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    have hdDiv := Nat.mem_divisors.mp hd'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hdDiv.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr fun hd0 ↦ hv (by simpa [hd0] using hdDiv.1)
    · exact le_sqrt_sqrt_of_pow_four_le (hd'.2.trans hvX)
  calc
    (v.divisors.card : ℝ) ≤
        (64 * ∑ d ∈ (v.divisors.filter fun d ↦ d ^ 4 ≤ v),
          d.divisors.card ^ 12 : ℕ) := by exact_mod_cast hsmall
    _ = 64 * ∑ d ∈ (v.divisors.filter fun d ↦ d ^ 4 ≤ v),
          (d.divisors.card : ℝ) ^ 12 := by norm_cast
    _ ≤ 64 * ∑ d ∈
          (Finset.Icc 1 (Nat.sqrt (Nat.sqrt X))).filter (fun d ↦ d ∣ v),
          (d.divisors.card : ℝ) ^ 12 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)) (by norm_num)

/-- A single residue-pair multiplicity is controlled by the twelfth moments
of the global small divisors, with their exact progression multiplicities. -/
lemma residuePairCount_le_globalSmallDivisorMoments (q r M N : ℕ) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (residuePairCount q r M N : ℝ) ≤
      64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 * divisorResidueCount d q r X := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  have hfirst : (residuePairCount q r M N : ℝ) ≤
      ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
        (v.divisors.card : ℝ) := by
    exact_mod_cast residuePairCount_le_sum_card_divisors q r M N
  calc
    (residuePairCount q r M N : ℝ) ≤
        ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
          (v.divisors.card : ℝ) := hfirst
    _ ≤ ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
          64 * ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v),
            (d.divisors.card : ℝ) ^ 12 := by
      apply Finset.sum_le_sum
      intro v hv
      have hvI := (Finset.mem_filter.mp hv).1
      exact card_divisors_le_globalSmallDivisorSum
        (Nat.ne_of_gt (Finset.mem_Icc.mp hvI).1) (Finset.mem_Icc.mp hvI).2
    _ = 64 * ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ v % q = r),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v),
            (d.divisors.card : ℝ) ^ 12 := by
      rw [Finset.mul_sum]
    _ = 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 * divisorResidueCount d q r X := by
      rw [sum_v_sum_d_dvd_eq]

/-- Fully finite nonzero-residue estimate.  All arithmetic losses are visible:
the small-divisor moment, progression density `X/d`, endpoint error `q`, and
one harmonic factor. -/
lemma weighted_residuePairCount_le_smallDivisorMoments
    (q M N n : ℕ) (hq : 0 < q) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (∑ r ∈ Finset.Icc 1 n,
        (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
      64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 *
          (((X : ℝ) / d + q) * (1 + Real.log n)) := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  calc
    (∑ r ∈ Finset.Icc 1 n,
        (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ Finset.Icc 1 n,
          (64 * ∑ d ∈ Finset.Icc 1 D,
            (d.divisors.card : ℝ) ^ 12 * divisorResidueCount d q r X) *
              ((q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (residuePairCount_le_globalSmallDivisorMoments q r M N) (by positivity)
    _ = 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 *
            (∑ r ∈ Finset.Icc 1 n,
              (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r)) := by
      calc
        (∑ r ∈ Finset.Icc 1 n,
            (64 * ∑ d ∈ Finset.Icc 1 D,
              (d.divisors.card : ℝ) ^ 12 * divisorResidueCount d q r X) *
                ((q : ℝ) / r)) =
            ∑ r ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 D,
              64 * ((d.divisors.card : ℝ) ^ 12 *
                divisorResidueCount d q r X) * ((q : ℝ) / r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ d ∈ Finset.Icc 1 D, ∑ r ∈ Finset.Icc 1 n,
              64 * ((d.divisors.card : ℝ) ^ 12 *
                divisorResidueCount d q r X) * ((q : ℝ) / r) := by
          rw [Finset.sum_comm]
        _ = 64 * ∑ d ∈ Finset.Icc 1 D,
              (d.divisors.card : ℝ) ^ 12 *
                (∑ r ∈ Finset.Icc 1 n,
                  (divisorResidueCount d q r X : ℝ) * ((q : ℝ) / r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ ≤ 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 *
            (((X : ℝ) / d + q) * (1 + Real.log n)) := by
      gcongr with d hd
      exact sum_divisorResidueCount_weight_le (Finset.mem_Icc.mp hd).1 hq

/-- The same estimate with the two moment sums factored out. -/
lemma weighted_residuePairCount_le_factoredMoments
    (q M N n : ℕ) (hq : 0 < q) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (∑ r ∈ Finset.Icc 1 n,
        (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
      64 * (1 + Real.log n) *
        ((X : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d) +
          (q : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12)) := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  refine (weighted_residuePairCount_le_smallDivisorMoments q M N n hq).trans_eq ?_
  calc
    64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 *
          (((X : ℝ) / d + q) * (1 + Real.log n)) =
        64 * (1 + Real.log n) *
          ∑ d ∈ Finset.Icc 1 D,
            ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
              (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by
      calc
        64 * ∑ d ∈ Finset.Icc 1 D,
            (d.divisors.card : ℝ) ^ 12 *
              (((X : ℝ) / d + q) * (1 + Real.log n)) =
            64 * ∑ d ∈ Finset.Icc 1 D,
              (1 + Real.log n) *
                ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                  (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by
          congr 1
          apply Finset.sum_congr rfl
          intro d hd
          have hd0 : (d : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Finset.mem_Icc.mp hd).1
          field_simp
        _ = 64 * ((1 + Real.log n) *
            ∑ d ∈ Finset.Icc 1 D,
              ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                (q : ℝ) * (d.divisors.card : ℝ) ^ 12)) := by
          congr 1
          exact (Finset.mul_sum (Finset.Icc 1 D)
            (fun d ↦ (X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
              (q : ℝ) * (d.divisors.card : ℝ) ^ 12) (1 + Real.log n)).symm
        _ = 64 * (1 + Real.log n) *
            ∑ d ∈ Finset.Icc 1 D,
              ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by ring
    _ = 64 * (1 + Real.log n) *
        ((X : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d) +
          (q : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Polylogarithmic form of the nonzero-residue estimate under the Weyl-range
condition `q * X^(1/4) ≤ X`.  This is the quantitative number-theoretic
input used after Cauchy--Schwarz. -/
theorem exists_weighted_residuePairCount_polylog_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ q M N n : ℕ,
        let X := 2 * M * N
        let D := Nat.sqrt (Nat.sqrt X)
        0 < q → 3 ≤ D → n ≤ X → q * D ≤ X →
        (∑ r ∈ Finset.Icc 1 n,
          (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
          K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
  obtain ⟨Kₓ, hKₓ, Oₓ, hOₓ, hweighted⟩ := exists_weighted_divisorPower_log_bound 12
  obtain ⟨Kₘ, hKₘ, Oₘ, hOₘ, hmean⟩ := exists_divisorPower_mean_log_bound 12
  let P : ℕ := Oₓ + Oₘ + 1
  let O : ℕ := P + 1
  let K : ℝ := 128 * (Kₓ + Kₘ)
  refine ⟨K, by dsimp [K]; positivity, O, by dsimp [O, P]; omega, ?_⟩
  intro q M N n
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  intro hq hD hnX hqD
  by_cases hn0 : n = 0
  · subst n
    simp
    have hDleX₀ : D ≤ X := by
      dsimp [D]
      exact (Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X)
    have hX3₀ : 3 ≤ X := hD.trans hDleX₀
    have hlogX₀ : 0 ≤ Real.log (X : ℝ) :=
      zero_le_one.trans (one_le_log_nat_of_three_le hX3₀)
    dsimp [X, K] at hlogX₀ ⊢
    push_cast at hlogX₀
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
      (pow_nonneg hlogX₀ O)
  have hDleX : D ≤ X := by
    dsimp [D]
    exact (Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X)
  have hX3 : 3 ≤ X := hD.trans hDleX
  have hlogX : (1 : ℝ) ≤ Real.log (X : ℝ) := one_le_log_nat_of_three_le hX3
  have hlogD : (1 : ℝ) ≤ Real.log (D : ℝ) := one_le_log_nat_of_three_le hD
  have hlogDX : Real.log (D : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    exact_mod_cast hDleX
  have hlognX : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0))
      (Set.mem_Ioi.mpr (by positivity))
    exact_mod_cast hnX
  have hH : 1 + Real.log (n : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    linarith
  have hOₓP : Oₓ ≤ P := by dsimp [P]; omega
  have hOₘP : Oₘ ≤ P := by dsimp [P]; omega
  have hpowW : Real.log (D : ℝ) ^ Oₓ ≤ Real.log (X : ℝ) ^ P := by
    calc
      Real.log (D : ℝ) ^ Oₓ ≤ Real.log (X : ℝ) ^ Oₓ :=
        pow_le_pow_left₀ (zero_le_one.trans hlogD) hlogDX Oₓ
      _ ≤ Real.log (X : ℝ) ^ P :=
        pow_le_pow_right₀ hlogX hOₓP
  have hpowM : Real.log (D : ℝ) ^ Oₘ ≤ Real.log (X : ℝ) ^ P := by
    calc
      Real.log (D : ℝ) ^ Oₘ ≤ Real.log (X : ℝ) ^ Oₘ :=
        pow_le_pow_left₀ (zero_le_one.trans hlogD) hlogDX Oₘ
      _ ≤ Real.log (X : ℝ) ^ P :=
        pow_le_pow_right₀ hlogX hOₘP
  let W : ℝ := ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d
  let U : ℝ := ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12
  have hW : W ≤ Kₓ * Real.log (X : ℝ) ^ P := by
    calc
      W ≤ Kₓ * Real.log (D : ℝ) ^ Oₓ := hweighted D hD
      _ ≤ Kₓ * Real.log (X : ℝ) ^ P :=
        mul_le_mul_of_nonneg_left hpowW hKₓ.le
  have hU : U ≤ Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      U ≤ Kₘ * (D : ℝ) * Real.log (D : ℝ) ^ Oₘ := hmean D hD
      _ ≤ Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P := by
        exact mul_le_mul_of_nonneg_left hpowM
          (mul_nonneg hKₘ.le (Nat.cast_nonneg D))
  have hXW : (X : ℝ) * W ≤
      Kₓ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      (X : ℝ) * W ≤ (X : ℝ) *
          (Kₓ * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg X)
      _ = Kₓ * (X : ℝ) * Real.log (X : ℝ) ^ P := by ring
  have hqU : (q : ℝ) * U ≤
      Kₘ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      (q : ℝ) * U ≤ (q : ℝ) *
          (Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg q)
      _ = Kₘ * ((q * D : ℕ) : ℝ) * Real.log (X : ℝ) ^ P := by
        push_cast
        ring
      _ ≤ Kₘ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
        gcongr
  have hraw := weighted_residuePairCount_le_factoredMoments q M N n hq
  change
    (∑ r ∈ Finset.Icc 1 n,
      (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
      K * (X : ℝ) * Real.log (X : ℝ) ^ O
  calc
    (∑ r ∈ Finset.Icc 1 n,
      (residuePairCount q r M N : ℝ) * ((q : ℝ) / r)) ≤
        64 * (1 + Real.log n) * ((X : ℝ) * W + (q : ℝ) * U) := hraw
    _ ≤ 64 * (2 * Real.log (X : ℝ)) *
        ((Kₓ + Kₘ) * (X : ℝ) * Real.log (X : ℝ) ^ P) := by
      gcongr
      nlinarith [add_le_add hXW hqU]
    _ = K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
      dsimp [K, O]
      rw [pow_succ]
      ring

/-! ## Coprime twists of the residue estimate

The quadratic Weyl sum has numerator `a`, with `a` coprime to the modulus.
Multiplication by `a` permutes residue classes, but it does not preserve their
least positive representatives and hence does not preserve the harmonic
weight `q / r`.  The following version repeats the progression-counting
argument with the congruence `a * v = r (mod q)`.  Coprimality is used only
to cancel `a` when showing that two solutions lie in one class modulo `q`;
the gcd obstruction still cancels against the harmonic weight exactly as in
the untwisted estimate above. -/

/-- Count integers up to `X` which are divisible by `d` and whose `a`-multiple
has residue `r` modulo `q`. -/
def twistedDivisorResidueCount (a d q r X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun v ↦ d ∣ v ∧ (a * v) % q = r).card

/-- Under the coprimality hypothesis, divisibility and a twisted congruence
specify at most one residue class modulo `lcm d q`. -/
lemma twistedDivisorResidueCount_le_lcm {a d q : ℕ} (haq : a.Coprime q)
    (hd : 0 < d) (hq : 0 < q) (r X : ℕ) :
    twistedDivisorResidueCount a d q r X ≤ X / d.lcm q + 1 := by
  let s := (Finset.Icc 1 X).filter fun v ↦ d ∣ v ∧ (a * v) % q = r
  apply card_le_div_add_one_of_pairwise_modEq (s := s)
    (fun v hv ↦ Finset.filter_subset _ _ hv) (Nat.lcm_pos hd hq)
  intro v hv w hw
  have hv' := (Finset.mem_filter.mp hv).2
  have hw' := (Finset.mem_filter.mp hw).2
  apply Nat.mod_lcm
  · exact (hv'.1.modEq_zero_nat).trans hw'.1.zero_modEq_nat
  · exact Nat.ModEq.cancel_left_of_coprime (m := q) (c := a)
      (by simpa [Nat.gcd_comm] using haq.gcd_eq_one)
      (hv'.2.trans hw'.2.symm)

/-- A nonempty twisted residue class has the same gcd compatibility as the
untwisted class.  No coprimality assumption on `a` is needed for this part. -/
lemma gcd_dvd_residue_of_twistedDivisorResidueCount_pos {a d q r X : ℕ}
    (hpos : 0 < twistedDivisorResidueCount a d q r X) : d.gcd q ∣ r := by
  rw [twistedDivisorResidueCount, Finset.card_pos] at hpos
  obtain ⟨v, hv⟩ := hpos
  have hv' := (Finset.mem_filter.mp hv).2
  apply Nat.dvd_of_mod_eq_zero
  have hmod := Nat.mod_mod_of_dvd (a * v) (Nat.gcd_dvd_right d q)
  have hgdv : d.gcd q ∣ a * v :=
    dvd_mul_of_dvd_right ((Nat.gcd_dvd_left d q).trans hv'.1) a
  rw [hv'.2, Nat.mod_eq_zero_of_dvd hgdv] at hmod
  exact hmod

/-- Pointwise twisted progression estimate, retaining the factor
`gcd(d,q)/r` which is needed before summing over residues. -/
lemma twistedDivisorResidueCount_mul_weight_le_scaled {a d q r X : ℕ}
    (haq : a.Coprime q) (hd : 0 < d) (hq : 0 < q) (hr : 0 < r) :
    (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r) ≤
      ((X : ℝ) / d + q) * ((d.gcd q : ℝ) / r) := by
  by_cases hc : twistedDivisorResidueCount a d q r X = 0
  · simp [hc]
    positivity
  have hcpos : 0 < twistedDivisorResidueCount a d q r X := Nat.pos_of_ne_zero hc
  let l := d.lcm q
  let g := d.gcd q
  have hl : 0 < l := Nat.lcm_pos hd hq
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hd
  have hgr : g ∣ r := gcd_dvd_residue_of_twistedDivisorResidueCount_pos hcpos
  have hlg : (l : ℝ) * (g : ℝ) = (d : ℝ) * (q : ℝ) := by
    exact_mod_cast Nat.lcm_mul_gcd d q
  have hcount := twistedDivisorResidueCount_le_lcm haq hd hq r X
  have hcountR : (twistedDivisorResidueCount a d q r X : ℝ) ≤
      (X : ℝ) / l + 1 := by
    calc
      (twistedDivisorResidueCount a d q r X : ℝ) ≤
          (X / l + 1 : ℕ) := by exact_mod_cast hcount
      _ ≤ (X : ℝ) / l + 1 := by
        push_cast
        gcongr
        exact Nat.cast_div_le
  have heq : ((X : ℝ) / l) * ((q : ℝ) / r) =
      ((X : ℝ) / d) * ((g : ℝ) / r) := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have hone : (q : ℝ) / r ≤ (q : ℝ) * ((g : ℝ) / r) := by
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    gcongr
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
    simpa using mul_le_mul_of_nonneg_right hg1
      (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ r))
  change _ ≤ ((X : ℝ) / d + q) * ((g : ℝ) / r)
  calc
    (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r) ≤
        ((X : ℝ) / l + 1) * ((q : ℝ) / r) :=
      mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ = ((X : ℝ) / l) * ((q : ℝ) / r) + (q : ℝ) / r := by ring
    _ ≤ ((X : ℝ) / d) * ((g : ℝ) / r) +
        (q : ℝ) * ((g : ℝ) / r) := add_le_add heq.le hone
    _ = ((X : ℝ) / d + q) * ((g : ℝ) / r) := by ring

/-- Compatible twisted residues become distinct positive quotients after
division by `gcd(d,q)`. -/
lemma sum_gcd_div_twisted_residue_nonzero_le_harmonic {a d q X n : ℕ}
    (hd : 0 < d) :
    (∑ r ∈ (Finset.Icc 1 n).filter
        (fun r ↦ twistedDivisorResidueCount a d q r X ≠ 0),
        (d.gcd q : ℝ) / r) ≤ 1 + Real.log n := by
  let g := d.gcd q
  have hg : 0 < g := Nat.gcd_pos_of_pos_left q hd
  let R := (Finset.Icc 1 n).filter fun r ↦
    twistedDivisorResidueCount a d q r X ≠ 0
  let f : ℕ → ℕ := fun r ↦ r / g
  have hdvd : ∀ r ∈ R, g ∣ r := by
    intro r hr
    have hc : twistedDivisorResidueCount a d q r X ≠ 0 :=
      (Finset.mem_filter.mp hr).2
    exact gcd_dvd_residue_of_twistedDivisorResidueCount_pos
      (Nat.pos_of_ne_zero hc)
  have hinj : Set.InjOn f R := by
    intro u hu v hv huv
    have huD := Nat.mul_div_cancel' (hdvd u hu)
    have hvD := Nat.mul_div_cancel' (hdvd v hv)
    dsimp [f] at huv
    calc
      u = g * (u / g) := huD.symm
      _ = g * (v / g) := by rw [huv]
      _ = v := hvD
  have himage : R.image f ⊆ Finset.Icc 1 n := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨r, hr, rfl⟩ := hk
    have hrI : r ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hr).1
    have hrpos : 0 < r := (Finset.mem_Icc.mp hrI).1
    have hdivpos : 0 < r / g :=
      Nat.div_pos (Nat.le_of_dvd hrpos (hdvd r hr)) hg
    exact Finset.mem_Icc.mpr
      ⟨hdivpos, (Nat.div_le_self r g).trans (Finset.mem_Icc.mp hrI).2⟩
  have hterm : ∀ r ∈ R, (g : ℝ) / r = ((r / g : ℕ) : ℝ)⁻¹ := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    have hg0 : (g : ℝ) ≠ 0 := by positivity
    have hq0 : ((r / g : ℕ) : ℝ) ≠ 0 := by
      have hkpos := Nat.div_pos (Nat.le_of_dvd hrpos (hdvd r hr)) hg
      exact_mod_cast hkpos.ne'
    have heq : g * (r / g) = r := Nat.mul_div_cancel' (hdvd r hr)
    calc
      (g : ℝ) / r = (g : ℝ) / ((g : ℝ) * (r / g : ℕ)) := by
        congr 1
        exact_mod_cast heq.symm
      _ = ((r / g : ℕ) : ℝ)⁻¹ := by field_simp
  change (∑ r ∈ R, (g : ℝ) / r) ≤ _
  calc
    (∑ r ∈ R, (g : ℝ) / r) =
        ∑ r ∈ R, ((f r : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hterm r hr
    _ = ∑ k ∈ R.image f, (k : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      intro u hu v hv huv
      exact hinj hu hv huv
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by intros; positivity)
    _ ≤ 1 + Real.log n := sum_Icc_inv_natCast_le_one_add_log n

/-- The twisted gcd-weighted residue aggregate is bounded by a harmonic sum.
The injective quotient map is unchanged because multiplication by the
coprime numerator does not affect the divisibility obstruction. -/
lemma sum_twistedDivisorResidueCount_weight_le {a d q X n : ℕ}
    (haq : a.Coprime q) (hd : 0 < d) (hq : 0 < q) :
    (∑ r ∈ Finset.Icc 1 n,
        (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r)) ≤
      (((X : ℝ) / d + q) * (1 + Real.log n)) := by
  let R := (Finset.Icc 1 n).filter fun r ↦
    twistedDivisorResidueCount a d q r X ≠ 0
  have hrestrict :
      (∑ r ∈ Finset.Icc 1 n,
          (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r)) =
        ∑ r ∈ R,
          (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r) := by
    rw [Finset.sum_subset (Finset.filter_subset _ _)]
    intro r hrI hrR
    simp only [R, Finset.mem_filter, hrI, true_and, not_not] at hrR
    simp [hrR]
  rw [hrestrict]
  calc
    (∑ r ∈ R,
        (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ R,
          ((X : ℝ) / d + q) * ((d.gcd q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact twistedDivisorResidueCount_mul_weight_le_scaled haq hd hq
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    _ = ((X : ℝ) / d + q) *
        ∑ r ∈ R, ((d.gcd q : ℝ) / r) := by
      rw [Finset.mul_sum]
    _ ≤ ((X : ℝ) / d + q) * (1 + Real.log n) := by
      gcongr
      exact sum_gcd_div_twisted_residue_nonzero_le_harmonic hd

/-- Residue-pair multiplicity with the coprime numerator occurring in the
quadratic phase retained explicitly. -/
def twistedResiduePairCount (a q r M N : ℕ) : ℕ :=
  (((Finset.Icc 1 M).product (Finset.Icc 1 N)).filter fun x ↦
    (a * (2 * x.1 * x.2)) % q = r).card

/-- Cancelling the part of a coefficient shared with the modulus. -/
lemma div_gcd_dvd_of_dvd_mul {q c u : ℕ} (hq : 0 < q) (h : q ∣ c * u) :
    q / q.gcd c ∣ u := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q c)
    (Nat.gcd_pos_of_pos_left c hq)]
  exact Nat.dvd_gcd_mul_iff_dvd_mul.mpr h

/-- Correct zero-residue estimate.  For a fixed first coordinate `m`, the
second coordinate must be a multiple of `q / gcd(q, 2*m)`.  Unlike the false
polylogarithmic estimate in Nguyen--Vu Lemma 4.2, this formula retains the
potentially large dependence on the prime factors of the composite modulus. -/
lemma twistedResiduePairCount_zero_le_gcd_sum
    {a q M N : ℕ} (haq : a.Coprime q) (hq : 0 < q) :
    twistedResiduePairCount a q 0 M N ≤
      ∑ m ∈ Finset.Icc 1 M, N / (q / q.gcd (2 * m)) := by
  let box := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let s := box.filter fun x ↦ (a * (2 * x.1 * x.2)) % q = 0
  let f : ℕ × ℕ → ℕ := Prod.fst
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo f (Finset.Icc 1 M) := by
    intro x hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  calc
    twistedResiduePairCount a q 0 M N = s.card := by rfl
    _ = ∑ m ∈ Finset.Icc 1 M, (s.filter fun x ↦ f x = m).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ m ∈ Finset.Icc 1 M, N / (q / q.gcd (2 * m)) := by
      apply Finset.sum_le_sum
      intro m hm
      let sm := s.filter fun x ↦ f x = m
      let d := q / q.gcd (2 * m)
      let U := (Finset.Icc 1 N).filter fun u ↦ d ∣ u
      have hdpos : 0 < d := by
        dsimp [d]
        exact Nat.div_pos (Nat.gcd_le_left (2 * m) hq)
          (Nat.gcd_pos_of_pos_left (2 * m) hq)
      have hinj : Set.InjOn (Prod.snd : ℕ × ℕ → ℕ) (sm : Set (ℕ × ℕ)) := by
        intro x hx y hy hxy
        apply Prod.ext
        · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
        · exact hxy
      have himage : sm.image Prod.snd ⊆ U := by
        intro u hu
        rw [Finset.mem_image] at hu
        obtain ⟨x, hx, rfl⟩ := hu
        have hxsm := Finset.mem_filter.mp hx
        have hxs := Finset.mem_filter.mp hxsm.1
        have hbox := Finset.mem_product.mp hxs.1
        have hqm : q ∣ 2 * m * x.2 := by
          have hqa : q ∣ a * (2 * x.1 * x.2) :=
            Nat.dvd_of_mod_eq_zero hxs.2
          have hqprod : q ∣ 2 * x.1 * x.2 :=
            haq.symm.dvd_of_dvd_mul_left hqa
          simpa [f, hxsm.2, Nat.mul_assoc] using hqprod
        exact Finset.mem_filter.mpr
          ⟨hbox.2, div_gcd_dvd_of_dvd_mul hq hqm⟩
      calc
        (s.filter fun x ↦ f x = m).card = sm.card := by rfl
        _ = (sm.image Prod.snd).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ U.card := Finset.card_le_card himage
        _ ≤ N / d := Erdos202.card_Icc_filter_dvd_le_div N d hdpos
        _ = N / (q / q.gcd (2 * m)) := by rfl

/-- A twisted residue-pair multiplicity is bounded by the divisor sum over
the exact integer products in its residue class. -/
lemma twistedResiduePairCount_le_sum_card_divisors (a q r M N : ℕ) :
    twistedResiduePairCount a q r M N ≤
      ∑ v ∈ (Finset.Icc 1 (2 * M * N)).filter
        (fun v ↦ (a * v) % q = r), v.divisors.card := by
  let box := (Finset.Icc 1 M).product (Finset.Icc 1 N)
  let s := box.filter fun x ↦ (a * (2 * x.1 * x.2)) % q = r
  let f : ℕ × ℕ → ℕ := fun x ↦ 2 * x.1 * x.2
  let t := (Finset.Icc 1 (2 * M * N)).filter fun v ↦ (a * v) % q = r
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo f t := by
    intro x hx
    have hxmem := Finset.mem_filter.mp hx
    have hxm := (Finset.mem_product.mp hxmem.1).1
    have hxu := (Finset.mem_product.mp hxmem.1).2
    have hm := Finset.mem_Icc.mp hxm
    have hu := Finset.mem_Icc.mp hxu
    have hm0 : x.1 ≠ 0 := by omega
    have hu0 : x.2 ≠ 0 := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hxmem.2⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero two_ne_zero hm0) hu0)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm.2) hu.2
  calc
    twistedResiduePairCount a q r M N = s.card := by rfl
    _ = ∑ v ∈ t, (s.filter fun x ↦ f x = v).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ v ∈ t, scaledFactorPairCount 2 v M N := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.card_le_card
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      have hxS := Finset.mem_filter.mp hx'.1
      exact Finset.mem_filter.mpr ⟨hxS.1, hx'.2⟩
    _ ≤ ∑ v ∈ t, v.divisors.card := by
      apply Finset.sum_le_sum
      intro v hv
      have hvpos : 0 < v :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
      exact scaledFactorPairCount_le_card_divisors (by norm_num) hvpos.ne'

/-- Interchange the integer variable and selected divisor in a twisted
residue class. -/
lemma sum_v_sum_d_dvd_twisted_eq (f : ℕ → ℝ) (a q r X D : ℕ) :
    (∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v), f d) =
      ∑ d ∈ Finset.Icc 1 D,
        f d * twistedDivisorResidueCount a d q r X := by
  classical
  calc
    (∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
        ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v), f d) =
        ∑ v ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 D,
          if (a * v) % q = r ∧ d ∣ v then f d else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hvr : (a * v) % q = r
      · simp only [hvr, if_true, true_and]
        rw [Finset.sum_filter]
      · simp [hvr]
    _ = ∑ d ∈ Finset.Icc 1 D, ∑ v ∈ Finset.Icc 1 X,
          if (a * v) % q = r ∧ d ∣ v then f d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 D,
        f d * twistedDivisorResidueCount a d q r X := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ v ∈ Finset.Icc 1 X,
            if (a * v) % q = r ∧ d ∣ v then f d else 0) =
            ∑ _v ∈ (Finset.Icc 1 X).filter
              (fun v ↦ (a * v) % q = r ∧ d ∣ v), f d := by
          rw [Finset.sum_filter]
        _ = f d * twistedDivisorResidueCount a d q r X := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hset :
              (Finset.Icc 1 X).filter
                  (fun v ↦ (a * v) % q = r ∧ d ∣ v) =
                (Finset.Icc 1 X).filter
                  (fun v ↦ d ∣ v ∧ (a * v) % q = r) := by
            ext v
            simp [and_comm]
          rw [hset, twistedDivisorResidueCount]
          ring

/-- A single twisted residue-pair multiplicity is controlled by the global
small-divisor moments. -/
lemma twistedResiduePairCount_le_globalSmallDivisorMoments
    (a q r M N : ℕ) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (twistedResiduePairCount a q r M N : ℝ) ≤
      64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 *
          twistedDivisorResidueCount a d q r X := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  have hfirst : (twistedResiduePairCount a q r M N : ℝ) ≤
      ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
        (v.divisors.card : ℝ) := by
    exact_mod_cast twistedResiduePairCount_le_sum_card_divisors a q r M N
  calc
    (twistedResiduePairCount a q r M N : ℝ) ≤
        ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
          (v.divisors.card : ℝ) := hfirst
    _ ≤ ∑ v ∈ (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
          64 * ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v),
            (d.divisors.card : ℝ) ^ 12 := by
      apply Finset.sum_le_sum
      intro v hv
      have hvI := (Finset.mem_filter.mp hv).1
      exact card_divisors_le_globalSmallDivisorSum
        (Nat.ne_of_gt (Finset.mem_Icc.mp hvI).1)
        (Finset.mem_Icc.mp hvI).2
    _ = 64 * ∑ v ∈
          (Finset.Icc 1 X).filter (fun v ↦ (a * v) % q = r),
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v),
            (d.divisors.card : ℝ) ^ 12 := by
      rw [Finset.mul_sum]
    _ = 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 *
            twistedDivisorResidueCount a d q r X := by
      rw [sum_v_sum_d_dvd_twisted_eq]

/-- Fully finite weighted estimate for the twisted residue multiplicities. -/
lemma weighted_twistedResiduePairCount_le_smallDivisorMoments
    (a q M N n : ℕ) (haq : a.Coprime q) (hq : 0 < q) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (∑ r ∈ Finset.Icc 1 n,
        (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
      64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 *
          (((X : ℝ) / d + q) * (1 + Real.log n)) := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  calc
    (∑ r ∈ Finset.Icc 1 n,
        (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
        ∑ r ∈ Finset.Icc 1 n,
          (64 * ∑ d ∈ Finset.Icc 1 D,
            (d.divisors.card : ℝ) ^ 12 *
              twistedDivisorResidueCount a d q r X) *
                ((q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (twistedResiduePairCount_le_globalSmallDivisorMoments a q r M N)
        (by positivity)
    _ = 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 *
            (∑ r ∈ Finset.Icc 1 n,
              (twistedDivisorResidueCount a d q r X : ℝ) *
                ((q : ℝ) / r)) := by
      calc
        (∑ r ∈ Finset.Icc 1 n,
            (64 * ∑ d ∈ Finset.Icc 1 D,
              (d.divisors.card : ℝ) ^ 12 *
                twistedDivisorResidueCount a d q r X) *
                  ((q : ℝ) / r)) =
            ∑ r ∈ Finset.Icc 1 n, ∑ d ∈ Finset.Icc 1 D,
              64 * ((d.divisors.card : ℝ) ^ 12 *
                twistedDivisorResidueCount a d q r X) *
                  ((q : ℝ) / r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ d ∈ Finset.Icc 1 D, ∑ r ∈ Finset.Icc 1 n,
              64 * ((d.divisors.card : ℝ) ^ 12 *
                twistedDivisorResidueCount a d q r X) *
                  ((q : ℝ) / r) := by
          rw [Finset.sum_comm]
        _ = 64 * ∑ d ∈ Finset.Icc 1 D,
              (d.divisors.card : ℝ) ^ 12 *
                (∑ r ∈ Finset.Icc 1 n,
                  (twistedDivisorResidueCount a d q r X : ℝ) *
                    ((q : ℝ) / r)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ ≤ 64 * ∑ d ∈ Finset.Icc 1 D,
          (d.divisors.card : ℝ) ^ 12 *
            (((X : ℝ) / d + q) * (1 + Real.log n)) := by
      gcongr with d hd
      exact sum_twistedDivisorResidueCount_weight_le haq
        (Finset.mem_Icc.mp hd).1 hq

/-- The twisted estimate with the two divisor moments factored out. -/
lemma weighted_twistedResiduePairCount_le_factoredMoments
    (a q M N n : ℕ) (haq : a.Coprime q) (hq : 0 < q) :
    let X := 2 * M * N
    let D := Nat.sqrt (Nat.sqrt X)
    (∑ r ∈ Finset.Icc 1 n,
        (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
      64 * (1 + Real.log n) *
        ((X : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d) +
          (q : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12)) := by
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  refine (weighted_twistedResiduePairCount_le_smallDivisorMoments
    a q M N n haq hq).trans_eq ?_
  calc
    64 * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ 12 *
          (((X : ℝ) / d + q) * (1 + Real.log n)) =
        64 * (1 + Real.log n) *
          ∑ d ∈ Finset.Icc 1 D,
            ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
              (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by
      calc
        64 * ∑ d ∈ Finset.Icc 1 D,
            (d.divisors.card : ℝ) ^ 12 *
              (((X : ℝ) / d + q) * (1 + Real.log n)) =
            64 * ∑ d ∈ Finset.Icc 1 D,
              (1 + Real.log n) *
                ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                  (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by
          congr 1
          apply Finset.sum_congr rfl
          intro d hd
          have hd0 : (d : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt (Finset.mem_Icc.mp hd).1
          field_simp
        _ = 64 * ((1 + Real.log n) *
            ∑ d ∈ Finset.Icc 1 D,
              ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                (q : ℝ) * (d.divisors.card : ℝ) ^ 12)) := by
          congr 1
          exact (Finset.mul_sum (Finset.Icc 1 D)
            (fun d ↦ (X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
              (q : ℝ) * (d.divisors.card : ℝ) ^ 12)
            (1 + Real.log n)).symm
        _ = 64 * (1 + Real.log n) *
            ∑ d ∈ Finset.Icc 1 D,
              ((X : ℝ) * ((d.divisors.card : ℝ) ^ 12 / d) +
                (q : ℝ) * (d.divisors.card : ℝ) ^ 12) := by ring
    _ = 64 * (1 + Real.log n) *
        ((X : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d) +
          (q : ℝ) *
            (∑ d ∈ Finset.Icc 1 D,
              (d.divisors.card : ℝ) ^ 12)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Uniform polylogarithmic weighted bound for the coprime-twisted Weyl
residue multiplicities. -/
theorem exists_weighted_twistedResiduePairCount_polylog_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ a q M N n : ℕ,
        let X := 2 * M * N
        let D := Nat.sqrt (Nat.sqrt X)
        a.Coprime q → 0 < q → 3 ≤ D → n ≤ X → q * D ≤ X →
        (∑ r ∈ Finset.Icc 1 n,
          (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
          K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
  obtain ⟨Kₓ, hKₓ, Oₓ, hOₓ, hweighted⟩ :=
    exists_weighted_divisorPower_log_bound 12
  obtain ⟨Kₘ, hKₘ, Oₘ, hOₘ, hmean⟩ :=
    exists_divisorPower_mean_log_bound 12
  let P : ℕ := Oₓ + Oₘ + 1
  let O : ℕ := P + 1
  let K : ℝ := 128 * (Kₓ + Kₘ)
  refine ⟨K, by dsimp [K]; positivity, O, by dsimp [O, P]; omega, ?_⟩
  intro a q M N n
  dsimp only
  let X := 2 * M * N
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hD hnX hqD
  by_cases hn0 : n = 0
  · subst n
    simp
    have hDleX₀ : D ≤ X := by
      dsimp [D]
      exact (Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X)
    have hX3₀ : 3 ≤ X := hD.trans hDleX₀
    have hlogX₀ : 0 ≤ Real.log (X : ℝ) :=
      zero_le_one.trans (one_le_log_nat_of_three_le hX3₀)
    dsimp [X, K] at hlogX₀ ⊢
    push_cast at hlogX₀
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
      (pow_nonneg hlogX₀ O)
  have hDleX : D ≤ X := by
    dsimp [D]
    exact (Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X)
  have hX3 : 3 ≤ X := hD.trans hDleX
  have hlogX : (1 : ℝ) ≤ Real.log (X : ℝ) :=
    one_le_log_nat_of_three_le hX3
  have hlogD : (1 : ℝ) ≤ Real.log (D : ℝ) :=
    one_le_log_nat_of_three_le hD
  have hlogDX : Real.log (D : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    exact_mod_cast hDleX
  have hlognX : Real.log (n : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0))
      (Set.mem_Ioi.mpr (by positivity))
    exact_mod_cast hnX
  have hH : 1 + Real.log (n : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    linarith
  have hOₓP : Oₓ ≤ P := by dsimp [P]; omega
  have hOₘP : Oₘ ≤ P := by dsimp [P]; omega
  have hpowW : Real.log (D : ℝ) ^ Oₓ ≤ Real.log (X : ℝ) ^ P := by
    calc
      Real.log (D : ℝ) ^ Oₓ ≤ Real.log (X : ℝ) ^ Oₓ :=
        pow_le_pow_left₀ (zero_le_one.trans hlogD) hlogDX Oₓ
      _ ≤ Real.log (X : ℝ) ^ P := pow_le_pow_right₀ hlogX hOₓP
  have hpowM : Real.log (D : ℝ) ^ Oₘ ≤ Real.log (X : ℝ) ^ P := by
    calc
      Real.log (D : ℝ) ^ Oₘ ≤ Real.log (X : ℝ) ^ Oₘ :=
        pow_le_pow_left₀ (zero_le_one.trans hlogD) hlogDX Oₘ
      _ ≤ Real.log (X : ℝ) ^ P := pow_le_pow_right₀ hlogX hOₘP
  let W : ℝ :=
    ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12 / d
  let U : ℝ :=
    ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ 12
  have hW : W ≤ Kₓ * Real.log (X : ℝ) ^ P := by
    calc
      W ≤ Kₓ * Real.log (D : ℝ) ^ Oₓ := hweighted D hD
      _ ≤ Kₓ * Real.log (X : ℝ) ^ P :=
        mul_le_mul_of_nonneg_left hpowW hKₓ.le
  have hU : U ≤ Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      U ≤ Kₘ * (D : ℝ) * Real.log (D : ℝ) ^ Oₘ := hmean D hD
      _ ≤ Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P := by
        exact mul_le_mul_of_nonneg_left hpowM
          (mul_nonneg hKₘ.le (Nat.cast_nonneg D))
  have hXW : (X : ℝ) * W ≤
      Kₓ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      (X : ℝ) * W ≤ (X : ℝ) *
          (Kₓ * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg X)
      _ = Kₓ * (X : ℝ) * Real.log (X : ℝ) ^ P := by ring
  have hqU : (q : ℝ) * U ≤
      Kₘ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
    calc
      (q : ℝ) * U ≤ (q : ℝ) *
          (Kₘ * (D : ℝ) * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg q)
      _ = Kₘ * ((q * D : ℕ) : ℝ) * Real.log (X : ℝ) ^ P := by
        push_cast
        ring
      _ ≤ Kₘ * (X : ℝ) * Real.log (X : ℝ) ^ P := by
        gcongr
  have hraw := weighted_twistedResiduePairCount_le_factoredMoments
    a q M N n haq hq
  change
    (∑ r ∈ Finset.Icc 1 n,
      (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
      K * (X : ℝ) * Real.log (X : ℝ) ^ O
  calc
    (∑ r ∈ Finset.Icc 1 n,
      (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
        64 * (1 + Real.log n) * ((X : ℝ) * W + (q : ℝ) * U) :=
      hraw
    _ ≤ 64 * (2 * Real.log (X : ℝ)) *
        ((Kₓ + Kₘ) * (X : ℝ) * Real.log (X : ℝ) ^ P) := by
      gcongr
      nlinarith [add_le_add hXW hqU]
    _ = K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
      dsimp [K, O]
      rw [pow_succ]
      ring

lemma four_mul_length_selected_low_le (n : ℕ) :
    4 * (quarterHeads (lowPrimeList n)).length ≤ (lowPrimes n).card := by
  simpa [lowPrimeList] using four_mul_length_quarterHeads_le (lowPrimeList n)

lemma low_card_le_four_mul_selected_length_add_three (n : ℕ) :
    (lowPrimes n).card ≤
      4 * (quarterHeads (lowPrimeList n)).length + 3 := by
  simpa [lowPrimeList] using
    length_le_four_mul_length_quarterHeads_add_three (lowPrimeList n)

/-- Finite Cauchy--Schwarz in the exact form used before Weyl differencing. -/
lemma norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (∑ _i ∈ s, (1 : ℝ) ^ 2) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by simp

/-- Weighted Hölder in the fourth-power form used by Burgess.  Writing the
weight twice as `sqrt ν * sqrt ν` and applying Cauchy--Schwarz twice avoids
fractional powers in all subsequent estimates. -/
lemma sum_mul_pow_four_le_sum_sq_mul_sum_pow_four
    {ι : Type*} (s : Finset ι) (ν f : ι → ℝ)
    (hν : ∀ i ∈ s, 0 ≤ ν i) :
    (∑ i ∈ s, ν i * f i) ^ 4 ≤
      (∑ i ∈ s, ν i) ^ 2 * (∑ i ∈ s, ν i ^ 2) *
        ∑ i ∈ s, f i ^ 4 := by
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i ↦ Real.sqrt (ν i)) (fun i ↦ Real.sqrt (ν i) * f i)
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq s ν (fun i ↦ f i ^ 2)
  have hsqrt (i : ι) (hi : i ∈ s) : Real.sqrt (ν i) ^ 2 = ν i :=
    Real.sq_sqrt (hν i hi)
  have hsum₁ :
      (∑ i ∈ s, Real.sqrt (ν i) * (Real.sqrt (ν i) * f i)) =
        ∑ i ∈ s, ν i * f i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      Real.sqrt (ν i) * (Real.sqrt (ν i) * f i) =
          Real.sqrt (ν i) ^ 2 * f i := by ring
      _ = ν i * f i := by rw [hsqrt i hi]
  have hsumν : (∑ i ∈ s, Real.sqrt (ν i) ^ 2) = ∑ i ∈ s, ν i := by
    apply Finset.sum_congr rfl
    exact fun i hi ↦ hsqrt i hi
  have hsum₂ :
      (∑ i ∈ s, (Real.sqrt (ν i) * f i) ^ 2) =
        ∑ i ∈ s, ν i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, hsqrt i hi]
  have h₁' :
      (∑ i ∈ s, ν i * f i) ^ 2 ≤
        (∑ i ∈ s, ν i) * ∑ i ∈ s, ν i * f i ^ 2 := by
    simpa only [hsum₁, hsumν, hsum₂] using h₁
  have h₂' :
      (∑ i ∈ s, ν i * f i ^ 2) ^ 2 ≤
        (∑ i ∈ s, ν i ^ 2) * ∑ i ∈ s, f i ^ 4 := by
    have hsum₄ : (∑ i ∈ s, (f i ^ 2) ^ 2) = ∑ i ∈ s, f i ^ 4 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum₄] at h₂
    exact h₂
  calc
    (∑ i ∈ s, ν i * f i) ^ 4 =
        ((∑ i ∈ s, ν i * f i) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i ∈ s, ν i) * ∑ i ∈ s, ν i * f i ^ 2) ^ 2 := by
      exact pow_le_pow_left₀ (sq_nonneg _) h₁' 2
    _ = (∑ i ∈ s, ν i) ^ 2 *
        (∑ i ∈ s, ν i * f i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i ∈ s, ν i) ^ 2 *
        ((∑ i ∈ s, ν i ^ 2) * ∑ i ∈ s, f i ^ 4) := by
      exact mul_le_mul_of_nonneg_left h₂' (sq_nonneg _)
    _ = (∑ i ∈ s, ν i) ^ 2 * (∑ i ∈ s, ν i ^ 2) *
        ∑ i ∈ s, f i ^ 4 := by ring

/-! ## Fixed prime-factor losses are subpower

The CRT stage of a Burgess fourth-moment argument loses a fixed constant for
each prime factor of the conductor.  The following elementary factorial
argument records, without any analytic number theory, that every such loss is
eventually smaller than an arbitrarily prescribed fixed positive power.
-/

/-- If all members of a finite set of naturals are positive, their product
dominates the factorial of the cardinality. -/
lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  classical
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by
          simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ := by
          exact f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    refine Finset.prod_le_prod' ?_
    intro i _
    exact hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) =
          ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ => x))
      _ = ∏ x ∈ s, x := by
        rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  calc
    Nat.factorial s.card = ∏ i : Fin s.card, (i.1 + 1) := hleft.symm
    _ ≤ ∏ i : Fin s.card, f i := hprod
    _ = ∏ x ∈ s, x := hright

/-- The factorial of the number of distinct prime factors of a nonzero
natural is bounded by the natural itself. -/
lemma factorial_card_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    Nat.factorial n.primeFactors.card ≤ n := by
  have hprod : Nat.factorial n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_le_prod_of_one_le _ (by
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).one_le)
  exact hprod.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))

/-- For fixed `b` and positive `m`, the loss `b ^ ω(n)` is eventually at
most `n ^ (1 / m)`.  This is the exact subpower input needed to absorb the
`3 ^ ω(q)` CRT loss in the quadratic Burgess fourth moment. -/
theorem const_pow_primeFactors_card_le_rpow_eventually
    (b m : ℕ) (hb : 1 ≤ b) (hm : 0 < m) :
    ∃ Nω : ℕ, ∀ {n : ℕ}, Nω ≤ n →
      (b : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) ^ ((1 : ℝ) / m) := by
  have hfact : ∀ᶠ k : ℕ in atTop, (b ^ m) ^ k < Nat.factorial (k - 1) := by
    simpa using (Nat.eventually_pow_lt_factorial_sub (b ^ m) 1)
  rcases eventually_atTop.mp hfact with ⟨k₀, hk₀⟩
  refine ⟨max 3 ((b ^ k₀) ^ m), ?_⟩
  intro n hn
  let k := n.primeFactors.card
  have hn3 : 3 ≤ n := (Nat.le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  by_cases hk_small : k < k₀
  · have hk_le : k ≤ k₀ := hk_small.le
    have hpow_nat : (b ^ k : ℕ) ≤ b ^ k₀ :=
      Nat.pow_le_pow_right (by omega : 0 < b) hk_le
    have hpow_real : (b : ℝ) ^ k ≤ (b : ℝ) ^ k₀ := by
      exact_mod_cast hpow_nat
    have hconst_nat : ((b ^ k₀ : ℕ) ^ m) ≤ n :=
      (Nat.le_max_right _ _).trans hn
    have hconst_real : (((b : ℝ) ^ k₀) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hconst_nat
    have hroot_le :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hconst_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k₀) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k₀ := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k₀ by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hpow_real.trans hroot_le
  · have hk_ge : k₀ ≤ k := Nat.le_of_not_gt hk_small
    have hmain_nat : (b ^ m) ^ k < Nat.factorial k := by
      exact (hk₀ k hk_ge).trans_le (Nat.factorial_le (Nat.sub_le _ _))
    have hk_fact_le_n : Nat.factorial k ≤ n := by
      simpa [k] using factorial_card_primeFactors_le n (Nat.ne_of_gt hnpos)
    have hpowm_nat' : (b ^ m) ^ k ≤ n :=
      (Nat.le_of_lt hmain_nat).trans hk_fact_le_n
    have hpowm_nat : (b ^ k : ℕ) ^ m ≤ n := by
      calc
        (b ^ k : ℕ) ^ m = b ^ (k * m) := by rw [pow_mul]
        _ = b ^ (m * k) := by rw [Nat.mul_comm]
        _ = (b ^ m) ^ k := by rw [pow_mul]
        _ ≤ n := hpowm_nat'
    have hpowm_real : (((b : ℝ) ^ k) ^ m) ≤ (n : ℝ) := by
      exact_mod_cast hpowm_nat
    have hroot_le :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) ≤
          (n : ℝ) ^ ((1 : ℝ) / m) := by
      exact Real.rpow_le_rpow (by positivity) hpowm_real (by positivity)
    have hroot :
        (((b : ℝ) ^ k) ^ m) ^ ((1 : ℝ) / m) = (b : ℝ) ^ k := by
      simpa [one_div] using
        Real.pow_rpow_inv_natCast (show 0 ≤ (b : ℝ) ^ k by positivity)
          (Nat.ne_of_gt hm)
    rw [hroot] at hroot_le
    exact hroot_le

/-! ## Quadratic-character correlations for Burgess differencing -/

/-- The complete correlation of two distinct translates of the quadratic
character of an odd finite field is exactly `-1`.  This is the diagonal
calculation in the fourth moment.  The proof identifies the transformed sum
with a quadratic Jacobi sum. -/
lemma quadraticChar_pair_correlation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) :
    (∑ x : F, quadraticChar F ((x - a) * (x - b))) = -1 := by
  let χ : MulChar F ℤ := quadraticChar F
  have hχ : χ ≠ 1 := quadraticChar_ne_one hF
  have hχinv : χ⁻¹ = χ := (quadraticChar_isQuadratic F).inv
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : F ≃ F := (Equiv.mulLeft₀ (b - a) hd).trans (Equiv.addLeft a)
  rw [← e.sum_comp]
  have hsq : χ (b - a) ^ 2 = 1 := quadraticChar_sq_one hd
  have hj : jacobiSum χ χ = -χ (-1) := by
    simpa [hχinv] using (jacobiSum_nontrivial_inv hχ)
  change (∑ x : F, χ ((e x - a) * (e x - b))) = -1
  have heval (x : F) : e x = a + (b - a) * x := rfl
  calc
    (∑ x : F, χ ((e x - a) * (e x - b))) =
        χ (-1) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [heval]
      simp only [add_sub_cancel_left]
      have h₁ : a + (b - a) * x - b = (b - a) * (x - 1) := by ring
      rw [h₁]
      rw [show ((b - a) * x) * ((b - a) * (x - 1)) =
          (-1) * ((b - a) ^ 2) * (x * (1 - x)) by ring]
      rw [map_mul, map_mul, map_mul, map_pow, hsq]
      ring
    _ = -1 := by
      rw [hj]
      have hneg : χ (-1) ^ 2 = 1 :=
        quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
      nlinarith

/-- The quadratic character, coerced to a real-valued function. -/
noncomputable def quadraticCharReal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) : ℝ :=
  quadraticChar F x

lemma quadraticCharReal_neg_one_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    -1 ≤ quadraticCharReal x := by
  rcases quadraticChar_isQuadratic F x with hx | hx | hx <;>
    simp [quadraticCharReal, hx]

lemma quadraticCharReal_pair_correlation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) :
    (∑ x : F, quadraticCharReal ((x - a) * (x - b))) = -1 := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (quadraticChar_pair_correlation hF a b hab)
  simpa [quadraticCharReal] using h

/-- Removing a square factor from a quadratic character changes the pointwise
upper bound only at the zero of that factor. -/
lemma quadraticCharReal_square_mul_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (u w : F) :
    quadraticCharReal (u ^ 2 * w) ≤
      quadraticCharReal w + if u = 0 then 1 else 0 := by
  by_cases hu : u = 0
  · have hleft : quadraticCharReal (u ^ 2 * w) = 0 := by
      rw [hu]
      simp [quadraticCharReal]
    have hw := quadraticCharReal_neg_one_le w
    calc
      quadraticCharReal (u ^ 2 * w) = 0 := hleft
      _ ≤ quadraticCharReal w + 1 := by linarith
      _ = quadraticCharReal w + if u = 0 then 1 else 0 := by simp [hu]
  · have hsq : quadraticChar F (u ^ 2) = 1 := quadraticChar_sq_one' hu
    simp [quadraticCharReal, map_mul, hsq, hu]

/-- A quartic correlation with a repeated linear factor and two distinct
remaining factors is nonpositive.  This handles every singular
off-diagonal tuple in the fourth moment. -/
lemma quadraticChar_four_correlation_le_zero_of_repeated
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b c : F) (hbc : b ≠ c) :
    (∑ x : F, quadraticCharReal
      ((x + a) ^ 2 * (x + b) * (x + c))) ≤ 0 := by
  have hpoint (x : F) :
      quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) ≤
        quadraticCharReal ((x + b) * (x + c)) +
          if x + a = 0 then 1 else 0 := by
    convert quadraticCharReal_square_mul_le
      (x + a) ((x + b) * (x + c)) using 1 <;> ring
  have hpair :
      (∑ x : F, quadraticCharReal ((x + b) * (x + c))) = -1 := by
    simpa only [sub_neg_eq_add] using
      quadraticCharReal_pair_correlation hF (-b) (-c) (by simpa using hbc)
  calc
    (∑ x : F, quadraticCharReal
      ((x + a) ^ 2 * (x + b) * (x + c))) ≤
        ∑ x : F, (quadraticCharReal ((x + b) * (x + c)) +
          if x + a = 0 then 1 else 0) :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x : F, quadraticCharReal ((x + b) * (x + c))) +
        ∑ x : F, if x + a = 0 then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = 0 := by
      rw [hpair]
      simp [add_eq_zero_iff_eq_neg]

/-- A short translated sum of the real-valued quadratic character. -/
noncomputable def quadraticShiftSum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (V : Finset F) (x : F) : ℝ :=
  ∑ v ∈ V, quadraticCharReal (x + v)

lemma quadraticCharReal_prod
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] (f : ι → F) :
    quadraticCharReal (∏ i, f i) = ∏ i, quadraticCharReal (f i) := by
  simp [quadraticCharReal, map_prod]

/-- Exact expansion of the fourth moment of translated quadratic-character
sums.  This is the algebraic starting point of Burgess's `r = 2` argument. -/
lemma quadraticShiftSum_fourth_moment_expansion
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (V : Finset F) :
    (∑ x : F, quadraticShiftSum V x ^ 4) =
      ∑ v : Fin 4 → V, ∑ x : F,
        quadraticCharReal (∏ i : Fin 4, (x + (v i : F))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [quadraticShiftSum, ← Finset.sum_attach, Finset.attach_eq_univ,
    Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v _
  exact (quadraticCharReal_prod (fun i : Fin 4 => x + (v i : F))).symm

/-- A four-tuple is diagonal when its entries can be paired into two equal
pairs.  Exactly these tuples make the product of the four linear factors a
square polynomial. -/
def burgessDiagonal {α : Type*} (v : Fin 4 → α) : Prop :=
  (v 0 = v 1 ∧ v 2 = v 3) ∨
  (v 0 = v 2 ∧ v 1 = v 3) ∨
  (v 0 = v 3 ∧ v 1 = v 2)

/-- All six pairwise inequalities for a four-tuple. -/
def burgessDistinct {α : Type*} (v : Fin 4 → α) : Prop :=
  v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 0 ≠ v 3 ∧
    v 1 ≠ v 2 ∧ v 1 ≠ v 3 ∧ v 2 ≠ v 3

instance {α : Type*} [DecidableEq α] :
    DecidablePred (@burgessDiagonal α) := fun _ => by
  unfold burgessDiagonal
  infer_instance

def burgessPairing01_23 {α : Type*} (a b : α) : Fin 4 → α :=
  ![a, a, b, b]

def burgessPairing02_13 {α : Type*} (a b : α) : Fin 4 → α :=
  ![a, b, a, b]

def burgessPairing03_12 {α : Type*} (a b : α) : Fin 4 → α :=
  ![a, b, b, a]

lemma burgessDiagonal_iff_exists_pairing {α : Type*} (v : Fin 4 → α) :
    burgessDiagonal v ↔
      (∃ a b, v = burgessPairing01_23 a b) ∨
      (∃ a b, v = burgessPairing02_13 a b) ∨
      (∃ a b, v = burgessPairing03_12 a b) := by
  simp only [burgessDiagonal]
  constructor
  · rintro (h | h | h)
    · left
      refine ⟨v 0, v 2, ?_⟩
      funext i
      fin_cases i <;> simp [burgessPairing01_23, h.1, h.2]
    · right; left
      refine ⟨v 0, v 1, ?_⟩
      funext i
      fin_cases i <;> simp [burgessPairing02_13, h.1, h.2]
    · right; right
      refine ⟨v 0, v 1, ?_⟩
      funext i
      fin_cases i <;> simp [burgessPairing03_12, h.1, h.2]
  · rintro (⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩) <;>
      simp [burgessPairing01_23, burgessPairing02_13,
        burgessPairing03_12]

/-- At most `3 * |α|²` four-tuples are diagonal. -/
lemma card_burgessDiagonal_le (α : Type*) [Fintype α] [DecidableEq α] :
    (Finset.univ.filter (burgessDiagonal : (Fin 4 → α) → Prop)).card ≤
      3 * Fintype.card α ^ 2 := by
  classical
  let P₁ : Finset (Fin 4 → α) :=
    (Finset.univ : Finset (α × α)).image fun ab =>
      burgessPairing01_23 ab.1 ab.2
  let P₂ : Finset (Fin 4 → α) :=
    (Finset.univ : Finset (α × α)).image fun ab =>
      burgessPairing02_13 ab.1 ab.2
  let P₃ : Finset (Fin 4 → α) :=
    (Finset.univ : Finset (α × α)).image fun ab =>
      burgessPairing03_12 ab.1 ab.2
  have hsub : Finset.univ.filter
      (burgessDiagonal : (Fin 4 → α) → Prop) ⊆ P₁ ∪ P₂ ∪ P₃ := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [burgessDiagonal_iff_exists_pairing] at hv
    rcases hv with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
  calc
    (Finset.univ.filter (burgessDiagonal : (Fin 4 → α) → Prop)).card ≤
        (P₁ ∪ P₂ ∪ P₃).card := Finset.card_le_card hsub
    _ ≤ P₁.card + P₂.card + P₃.card := by
      exact (Finset.card_union_le (P₁ ∪ P₂) P₃).trans
        (Nat.add_le_add_right (Finset.card_union_le P₁ P₂) P₃.card)
    _ ≤ Fintype.card (α × α) + Fintype.card (α × α) +
        Fintype.card (α × α) := by
      gcongr <;> exact Finset.card_image_le
    _ = 3 * Fintype.card α ^ 2 := by simp [pow_two]; ring

lemma quadraticCharReal_le_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    quadraticCharReal x ≤ 1 := by
  rcases quadraticChar_isQuadratic F x with hx | hx | hx <;>
    simp [quadraticCharReal, hx]

/-- Every complete four-shift correlation has the trivial upper bound given
by the size of the field. -/
lemma quadraticChar_four_correlation_le_card
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin 4 → F) :
    (∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) ≤
      Fintype.card F := by
  calc
    (∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) ≤
        ∑ _x : F, (1 : ℝ) := by
      exact Finset.sum_le_sum fun _ _ => quadraticCharReal_le_one _
    _ = Fintype.card F := by simp

/-- The fourth-moment estimate reduced exactly to an off-diagonal complete
quartic-correlation bound.  Instantiating `B` by `3 * sqrt |F|` is the local
Weil--Hasse input in the Burgess argument. -/
lemma quadraticShiftSum_fourth_moment_le_of_offDiagonal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (V : Finset F) (B : ℝ) (hB : 0 ≤ B)
    (hoff : ∀ v : Fin 4 → V, ¬burgessDiagonal v →
      (∑ x : F, quadraticCharReal
        (∏ i : Fin 4, (x + (v i : F)))) ≤ B) :
    (∑ x : F, quadraticShiftSum V x ^ 4) ≤
      3 * (V.card : ℝ) ^ 2 * Fintype.card F +
        (V.card : ℝ) ^ 4 * B := by
  classical
  let D : Finset (Fin 4 → V) := Finset.univ.filter burgessDiagonal
  have hpoint (v : Fin 4 → V) :
      (∑ x : F, quadraticCharReal
          (∏ i : Fin 4, (x + (v i : F)))) ≤
        (if burgessDiagonal v then (Fintype.card F : ℝ) else 0) + B := by
    by_cases hv : burgessDiagonal v
    · have htriv := quadraticChar_four_correlation_le_card
          (F := F) (fun i => (v i : F))
      simp only [hv, if_true]
      exact htriv.trans (le_add_of_nonneg_right hB)
    · simpa [hv] using hoff v hv
  rw [quadraticShiftSum_fourth_moment_expansion]
  calc
    (∑ v : Fin 4 → V, ∑ x : F,
        quadraticCharReal (∏ i : Fin 4, (x + (v i : F)))) ≤
        ∑ v : Fin 4 → V,
          ((if burgessDiagonal v then (Fintype.card F : ℝ) else 0) + B) := by
      exact Finset.sum_le_sum fun v _ => hpoint v
    _ = (D.card : ℝ) * Fintype.card F +
        Fintype.card (Fin 4 → V) * B := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      change (∑ v : Fin 4 → V,
          if burgessDiagonal v then (Fintype.card F : ℝ) else 0) +
          Fintype.card (Fin 4 → V) * B = _
      rw [← Finset.sum_filter]
      simp [D]
    _ ≤ (3 * V.card ^ 2 : ℕ) * Fintype.card F +
        Fintype.card (Fin 4 → V) * B := by
      gcongr
      simpa [D] using card_burgessDiagonal_le V
    _ = 3 * (V.card : ℝ) ^ 2 * Fintype.card F +
        (V.card : ℝ) ^ 4 * B := by
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
        Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- If a four-tuple is neither diagonal nor pairwise distinct, its quartic
correlation is nonpositive.  After choosing a repeated pair, removal of its
square factor leaves the exact two-shift correlation `-1`, with at most one
exceptional root. -/
lemma quadraticChar_four_correlation_le_zero_of_singular_offDiagonal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F)
    (hdiag : ¬burgessDiagonal v) (hdist : ¬burgessDistinct v) :
    (∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) ≤ 0 := by
  let a := v 0
  let b := v 1
  let c := v 2
  let d := v 3
  have hform (x : F) :
      (∏ i : Fin 4, (x + v i)) =
        (x + a) * (x + b) * (x + c) * (x + d) := by
    simp [a, b, c, d, Fin.prod_univ_four]
  simp_rw [hform]
  by_cases hab : a = b
  · have hcd : c ≠ d := by
      intro h
      apply hdiag
      exact Or.inl ⟨by simpa [a, b] using hab, by simpa [c, d] using h⟩
    subst b
    have hrep := quadraticChar_four_correlation_le_zero_of_repeated
      hF a c d hcd
    simpa only [← hab, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h
      apply hdiag
      exact Or.inr <| Or.inl
        ⟨by simpa [a, c] using hac, by simpa [b, d] using h⟩
    subst c
    have hrep := quadraticChar_four_correlation_le_zero_of_repeated
      hF a b d hbd
    simpa only [← hac, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases had : a = d
  · have hbc : b ≠ c := by
      intro h
      apply hdiag
      exact Or.inr <| Or.inr
        ⟨by simpa [a, d] using had, by simpa [b, c] using h⟩
    subst d
    have hrep := quadraticChar_four_correlation_le_zero_of_repeated
      hF a b c hbc
    simpa only [← had, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hbc : b = c
  · have had' : a ≠ d := by
      intro h
      exact had h
    subst c
    have hrep := quadraticChar_four_correlation_le_zero_of_repeated
      hF b a d had'
    simpa only [← hbc, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hbd : b = d
  · have hac' : a ≠ c := by
      intro h
      exact hac h
    subst d
    have hrep := quadraticChar_four_correlation_le_zero_of_repeated
      hF b a c hac'
    simpa only [← hbd, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  have hcd : c = d := by
    by_contra hcd
    apply hdist
    exact ⟨by simpa [a, b] using hab, by simpa [a, c] using hac,
      by simpa [a, d] using had, by simpa [b, c] using hbc,
      by simpa [b, d] using hbd, by simpa [c, d] using hcd⟩
  have hab' : a ≠ b := hab
  subst d
  have hrep := quadraticChar_four_correlation_le_zero_of_repeated
    hF c a b hab'
  simpa only [← hcd, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep

/-- Number of affine points on the quartic curve
`y² = ∏ i, (x + v i)`.  Defining the count fiberwise makes its relation to
the quadratic character exact and avoids any quotient representation of the
projective completion. -/
def quarticAffinePointCount
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin 4 → F) : ℕ :=
  ∑ x : F, ({y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card

/-- The affine point-count error of the quartic curve is exactly its complete
quadratic-character correlation. -/
lemma quarticAffinePointCount_eq_card_add_correlation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F) :
    (quarticAffinePointCount v : ℝ) = Fintype.card F +
      ∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i)) := by
  have hroot (x : F) :
      (({y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card : ℝ) =
        quadraticCharReal (∏ i : Fin 4, (x + v i)) + 1 := by
    have hx := quadraticChar_card_sqrts hF (∏ i : Fin 4, (x + v i))
    change (({y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card : ℤ) =
      quadraticChar F (∏ i : Fin 4, (x + v i)) + 1 at hx
    calc
      (({y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card : ℝ) =
          ((((
            {y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card : ℕ) : ℤ) : ℝ) := by
            norm_num
      _ = ((quadraticChar F (∏ i : Fin 4, (x + v i)) + 1 : ℤ) : ℝ) := by
        rw [hx]
      _ = quadraticCharReal (∏ i : Fin 4, (x + v i)) + 1 := by
        simp [quadraticCharReal]
  rw [quarticAffinePointCount, Nat.cast_sum]
  simp_rw [hroot, Finset.sum_add_distrib]
  simp [quadraticCharReal, add_comm]

/-! ### The Hasse bound for the quartic completion

For four distinct shifts, the affine quartic has a rational root.  Moving
that root to zero and putting `d = A * B * C`, the birational substitution

`u = d / t`, `z = d * y / t²`

identifies its nonexceptional points with the Weierstrass cubic below.  The
quartic has one exceptional affine point, while the cubic has two, and the
elliptic curve has one point at infinity.  Thus its total point count is the
quartic affine count plus two. -/

open WeierstrassCurve

noncomputable instance quarticAffinePointFintype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : Fintype W.Point := by
  classical
  letI : Fintype {xy : F × F // W.Nonsingular xy.1 xy.2} := by infer_instance
  letI : Fintype (WithZero {xy : F × F // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Fintype (Option {xy : F × F // W.Nonsingular xy.1 xy.2}))
  exact Fintype.ofEquiv _ W.nonsingularPointEquiv.symm

def quarticWeierstrassCurve {F : Type*} [Field F] (A B C : F) :
    WeierstrassCurve F where
  a₁ := 0
  a₂ := A * B + A * C + B * C
  a₃ := 0
  a₄ := A * B * C * (A + B + C)
  a₆ := (A * B * C) ^ 2

lemma quarticWeierstrassCurve_discriminant
    {F : Type*} [Field F] (A B C : F) :
    (quarticWeierstrassCurve A B C).toAffine.Δ =
      16 * (A * B * C) ^ 2 * (A - B) ^ 2 * (A - C) ^ 2 * (B - C) ^ 2 := by
  simp [quarticWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma quarticWeierstrassCurve_isElliptic
    {F : Type*} [Field F] (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    (quarticWeierstrassCurve A B C).toAffine.IsElliptic := by
  constructor
  rw [quarticWeierstrassCurve_discriminant]
  apply isUnit_iff_ne_zero.mpr
  have h16 : (16 : F) ≠ 0 := by
    convert pow_ne_zero 4 (Ring.two_ne_zero h2) using 1 <;> norm_num
  exact
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero h16 (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hA hB) hC)))
          (pow_ne_zero 2 (sub_ne_zero.mpr hAB)))
        (pow_ne_zero 2 (sub_ne_zero.mpr hAC)))
      (pow_ne_zero 2 (sub_ne_zero.mpr hBC))

def normalizedQuarticPoints {F : Type*} [Field F] (A B C : F) : Type _ :=
  {xy : F × F // xy.2 ^ 2 = xy.1 * (xy.1 + A) * (xy.1 + B) * (xy.1 + C)}

def normalizedCubicPoints {F : Type*} [Field F] (A B C : F) : Type _ :=
  {uz : F × F // uz.2 ^ 2 = uz.1 ^ 3 +
    (A * B + A * C + B * C) * uz.1 ^ 2 +
    (A * B * C * (A + B + C)) * uz.1 + (A * B * C) ^ 2}

noncomputable instance normalizedQuarticPointsFintype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (A B C : F) :
    Fintype (normalizedQuarticPoints A B C) := by
  unfold normalizedQuarticPoints
  infer_instance

noncomputable instance normalizedCubicPointsFintype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (A B C : F) :
    Fintype (normalizedCubicPoints A B C) := by
  unfold normalizedCubicPoints
  infer_instance

def normalizedQuarticCubicNonzeroEquiv
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {A B C : F} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    {q : normalizedQuarticPoints A B C // q.1.1 ≠ 0} ≃
      {c : normalizedCubicPoints A B C // c.1.1 ≠ 0} where
  toFun q := by
    let d := A * B * C
    let t : F := q.val.val.1
    let y : F := q.val.val.2
    have ht : t ≠ 0 := by simpa [t] using q.property
    have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) hC
    refine ⟨⟨⟨d / t, d * y / t ^ 2⟩, ?_⟩, div_ne_zero hd ht⟩
    dsimp only [d, t, y]
    field_simp [q.property]
    rw [q.val.property]
    ring
  invFun c := by
    let d := A * B * C
    let u : F := c.val.val.1
    let z : F := c.val.val.2
    have hu : u ≠ 0 := by simpa [u] using c.property
    have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero hA hB) hC
    refine ⟨⟨⟨d / u, d * z / u ^ 2⟩, ?_⟩, div_ne_zero hd hu⟩
    dsimp only [d, u, z]
    field_simp [c.property]
    rw [c.val.property]
    ring
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · field_simp [q.property]
    · field_simp [q.property]
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · field_simp [c.property]
    · field_simp [c.property]

lemma quarticWeierstrassCurve_equation_iff
    {F : Type*} [Field F] {A B C u z : F} :
    (quarticWeierstrassCurve A B C).toAffine.Equation u z ↔
      z ^ 2 = u ^ 3 + (A * B + A * C + B * C) * u ^ 2 +
        (A * B * C * (A + B + C)) * u + (A * B * C) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [quarticWeierstrassCurve]

def normalizedCubicPointsEquivEquation {F : Type*} [Field F] (A B C : F) :
    normalizedCubicPoints A B C ≃
      {uz : F × F //
        (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2} where
  toFun uz := ⟨uz.1, quarticWeierstrassCurve_equation_iff.mpr uz.2⟩
  invFun uz := ⟨uz.1, quarticWeierstrassCurve_equation_iff.mp uz.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_normalizedQuarticPoints_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (A B C : F) :
    Fintype.card {q : normalizedQuarticPoints A B C // q.val.1 = 0} = 1 := by
  rw [Fintype.card_eq_one_iff]
  let q0 : {q : normalizedQuarticPoints A B C // q.val.1 = 0} :=
    ⟨⟨(0, 0), by simp⟩, rfl⟩
  refine ⟨q0, fun q ↦ ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact q.property
  · have hy : q.val.val.2 ^ 2 = 0 := by
      simpa [q.property] using q.val.property
    exact sq_eq_zero_iff.mp hy

def normalizedCubicPointsZeroEquivRoots
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (A B C : F) :
    {c : normalizedCubicPoints A B C // c.val.1 = 0} ≃
      {z : F // z ^ 2 = (A * B * C) ^ 2} where
  toFun c := ⟨c.val.val.2, by simpa [c.property] using c.val.property⟩
  invFun z := ⟨⟨(0, z), by simpa [normalizedCubicPoints] using z.property⟩, rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact c.property.symm
    · rfl
  right_inv _ := rfl

lemma card_square_roots_square
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    Fintype.card {z : F // z ^ 2 = d ^ 2} = 2 := by
  have h := quadraticChar_card_sqrts h2 (d ^ 2)
  have hchar : quadraticChar F (d ^ 2) = 1 := quadraticChar_sq_one' hd
  rw [hchar] at h
  have hnat : ({z : F | z ^ 2 = d ^ 2} : Set F).toFinset.card = 2 := by
    exact_mod_cast h
  simpa [Fintype.card_subtype] using hnat

lemma card_normalizedCubicPoints_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    Fintype.card {c : normalizedCubicPoints A B C // c.val.1 = 0} = 2 := by
  rw [Fintype.card_congr (normalizedCubicPointsZeroEquivRoots A B C)]
  exact card_square_roots_square h2 (mul_ne_zero (mul_ne_zero hA hB) hC)

lemma card_normalizedQuarticPoints_eq_nonzero_add_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (A B C : F) :
    Fintype.card (normalizedQuarticPoints A B C) =
      Fintype.card {q : normalizedQuarticPoints A B C // q.val.1 ≠ 0} + 1 := by
  have hs := Fintype.card_congr
    (Equiv.sumCompl (fun q : normalizedQuarticPoints A B C ↦ q.val.1 = 0))
  calc
    Fintype.card (normalizedQuarticPoints A B C) =
        Fintype.card {q : normalizedQuarticPoints A B C // q.val.1 = 0} +
          Fintype.card {q : normalizedQuarticPoints A B C // ¬q.val.1 = 0} := by
      simpa only [Fintype.card_sum] using hs.symm
    _ = 1 + Fintype.card
        {q : normalizedQuarticPoints A B C // q.val.1 ≠ 0} := by
      rw [card_normalizedQuarticPoints_zero]
    _ = _ := Nat.add_comm _ _

lemma card_normalizedCubicPoints_eq_nonzero_add_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    Fintype.card (normalizedCubicPoints A B C) =
      Fintype.card {c : normalizedCubicPoints A B C // c.val.1 ≠ 0} + 2 := by
  have hs := Fintype.card_congr
    (Equiv.sumCompl (fun c : normalizedCubicPoints A B C ↦ c.val.1 = 0))
  calc
    Fintype.card (normalizedCubicPoints A B C) =
        Fintype.card {c : normalizedCubicPoints A B C // c.val.1 = 0} +
          Fintype.card {c : normalizedCubicPoints A B C // ¬c.val.1 = 0} := by
      simpa only [Fintype.card_sum] using hs.symm
    _ = 2 + Fintype.card
        {c : normalizedCubicPoints A B C // c.val.1 ≠ 0} := by
      rw [card_normalizedCubicPoints_zero h2 hA hB hC]
    _ = _ := Nat.add_comm _ _

lemma card_normalizedCubicPoints_eq_normalizedQuarticPoints_add_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    Fintype.card (normalizedCubicPoints A B C) =
      Fintype.card (normalizedQuarticPoints A B C) + 1 := by
  rw [card_normalizedCubicPoints_eq_nonzero_add_two h2 hA hB hC,
    card_normalizedQuarticPoints_eq_nonzero_add_one]
  have hnz := Fintype.card_congr (normalizedQuarticCubicNonzeroEquiv hA hB hC)
  omega

lemma pointCount_quarticWeierstrassCurve_eq_add_two
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    HasseWeil.pointCount (quarticWeierstrassCurve A B C).toAffine =
      Fintype.card (normalizedQuarticPoints A B C) + 2 := by
  letI : (quarticWeierstrassCurve A B C).toAffine.IsElliptic :=
    quarticWeierstrassCurve_isElliptic h2 hA hB hC hAB hAC hBC
  letI : Fintype {uz : F × F //
      (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2} := by
    classical
    infer_instance
  letI : Fintype (WithZero {uz : F × F //
      (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2}) :=
    inferInstanceAs (Fintype (Option {uz : F × F //
      (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2}))
  have hp := Fintype.card_congr
    (WeierstrassCurve.Affine.pointEquiv
      (quarticWeierstrassCurve A B C).toAffine)
  have hc := Fintype.card_congr (normalizedCubicPointsEquivEquation A B C)
  rw [HasseWeil.pointCount]
  calc
    Fintype.card (quarticWeierstrassCurve A B C).toAffine.Point =
        Fintype.card (WithZero {uz : F × F //
          (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2}) := hp
    _ = Fintype.card {uz : F × F //
          (quarticWeierstrassCurve A B C).toAffine.Equation uz.1 uz.2} + 1 := by
      exact Fintype.card_option
    _ = Fintype.card (normalizedCubicPoints A B C) + 1 := by rw [hc]
    _ = Fintype.card (normalizedQuarticPoints A B C) + 2 := by
      rw [card_normalizedCubicPoints_eq_normalizedQuarticPoints_add_one h2 hA hB hC]

lemma hasse_normalizedQuartic
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {A B C : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    |((Fintype.card (normalizedQuarticPoints A B C) : ℝ) + 2) -
        (Fintype.card F : ℝ) - 1| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  letI : (quarticWeierstrassCurve A B C).toAffine.IsElliptic :=
    quarticWeierstrassCurve_isElliptic h2 hA hB hC hAB hAC hBC
  have hh := HasseWeil.WeilPairing.hasse_bound
    (quarticWeierstrassCurve A B C)
  rw [pointCount_quarticWeierstrassCurve_eq_add_two
    h2 hA hB hC hAB hAC hBC] at hh
  simpa using hh

def quarticPointSubtype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin 4 → F) : Type _ :=
  {xy : F × F // xy.2 ^ 2 = ∏ i : Fin 4, (xy.1 + v i)}

noncomputable instance quarticPointSubtypeFintype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (v : Fin 4 → F) :
    Fintype (quarticPointSubtype v) := by
  unfold quarticPointSubtype
  infer_instance

lemma quarticAffinePointCount_eq_card_subtype
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin 4 → F) :
    quarticAffinePointCount v = Fintype.card (quarticPointSubtype v) := by
  let e := Equiv.subtypeProdEquivSigmaSubtype
    (fun x y : F ↦ y ^ 2 = ∏ i : Fin 4, (x + v i))
  have he := Fintype.card_congr e
  rw [quarticAffinePointCount]
  calc
    (∑ x : F, ({y : F | y ^ 2 = ∏ i : Fin 4, (x + v i)} : Set F).toFinset.card) =
        ∑ x : F, Fintype.card {y : F // y ^ 2 = ∏ i : Fin 4, (x + v i)} := by
      apply Finset.sum_congr rfl
      intro x _
      exact Set.toFinset_card _
    _ = Fintype.card (Σ x : F,
        {y : F // y ^ 2 = ∏ i : Fin 4, (x + v i)}) :=
      Fintype.card_sigma.symm
    _ = Fintype.card (quarticPointSubtype v) := he.symm

def shiftQuarticPointEquiv
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (v : Fin 4 → F) :
    quarticPointSubtype v ≃
      normalizedQuarticPoints (v 1 - v 0) (v 2 - v 0) (v 3 - v 0) where
  toFun q := ⟨(q.val.1 + v 0, q.val.2), by
    rw [q.property]
    simp only [Fin.prod_univ_four]
    ring⟩
  invFun q := ⟨(q.val.1 - v 0, q.val.2), by
    simpa only [quarticPointSubtype, Fin.prod_univ_four] using (show
      q.val.2 ^ 2 =
        (q.val.1 - v 0 + v 0) *
          (q.val.1 - v 0 + v 1) *
          (q.val.1 - v 0 + v 2) *
          (q.val.1 - v 0 + v 3) by
      rw [q.property]
      ring)⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · ring
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    · ring

/-- Hasse's estimate for every squarefree four-shift quartic.  This is the
axiom-clean elliptic-curve input needed by the `r = 2` Burgess moment. -/
lemma quarticAffinePointCount_hasse
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) (v : Fin 4 → F) (hv : burgessDistinct v) :
    |(quarticAffinePointCount v : ℝ) + 2 -
        ((Fintype.card F : ℝ) + 1)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  rcases hv with ⟨h01, h02, h03, h12, h13, h23⟩
  have hA : v 1 - v 0 ≠ 0 := sub_ne_zero.mpr h01.symm
  have hB : v 2 - v 0 ≠ 0 := sub_ne_zero.mpr h02.symm
  have hC : v 3 - v 0 ≠ 0 := sub_ne_zero.mpr h03.symm
  have hAB : v 1 - v 0 ≠ v 2 - v 0 := sub_left_injective.ne h12
  have hAC : v 1 - v 0 ≠ v 3 - v 0 := sub_left_injective.ne h13
  have hBC : v 2 - v 0 ≠ v 3 - v 0 := sub_left_injective.ne h23
  have hh := hasse_normalizedQuartic h2 hA hB hC hAB hAC hBC
  have he := Fintype.card_congr (shiftQuarticPointEquiv v)
  rw [quarticAffinePointCount_eq_card_subtype, he]
  convert hh using 1 <;> ring

/-- Arithmetic consequence of Hasse's bound for the smooth projective
completion of a squarefree monic quartic.  Such a completion has two points
at infinity, so the displayed hypothesis is the standard genus-one estimate.
This lemma performs all normalization needed by the Burgess moment. -/
lemma quadraticChar_four_correlation_le_three_sqrt_of_hasse
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F)
    (hhasse : |(quarticAffinePointCount v : ℝ) + 2 -
        ((Fintype.card F : ℝ) + 1)| ≤ 2 * Real.sqrt (Fintype.card F)) :
    (∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) ≤
      3 * Real.sqrt (Fintype.card F) := by
  rw [quarticAffinePointCount_eq_card_add_correlation hF v] at hhasse
  have hhasse' :
      |(∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) + 1| ≤
        2 * Real.sqrt (Fintype.card F) := by
    convert hhasse using 1 <;> ring
  have hsqrt : 1 ≤ Real.sqrt (Fintype.card F) := by
    have hcard : (1 : ℝ) ≤ Fintype.card F := by
      exact_mod_cast Fintype.card_pos
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
    have hsqrt_sq : Real.sqrt (Fintype.card F) ^ 2 = Fintype.card F :=
      Real.sq_sqrt (by positivity)
    nlinarith
  have hupper := (le_abs_self
    ((∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) + 1)).trans hhasse'
  nlinarith

/-- Every off-diagonal quartic correlation has the Burgess bound once Hasse's
estimate is supplied in the pairwise-distinct case.  The complementary
singular case is elementary and in fact nonpositive. -/
lemma quadraticChar_four_correlation_le_three_sqrt_of_hasse_of_offDiagonal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F)
    (hdiag : ¬burgessDiagonal v)
    (hhasse : burgessDistinct v →
      |(quarticAffinePointCount v : ℝ) + 2 -
          ((Fintype.card F : ℝ) + 1)| ≤
        2 * Real.sqrt (Fintype.card F)) :
    (∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) ≤
      3 * Real.sqrt (Fintype.card F) := by
  by_cases hdist : burgessDistinct v
  · exact quadraticChar_four_correlation_le_three_sqrt_of_hasse
      hF v (hhasse hdist)
  · exact (quadraticChar_four_correlation_le_zero_of_singular_offDiagonal
      hF v hdiag hdist).trans (by positivity)

/-- The complete `r = 2` Burgess fourth-moment estimate, reduced only to
Hasse's bound for the smooth quartics arising from pairwise-distinct shifts. -/
lemma quadraticShiftSum_fourth_moment_le_of_quartic_hasse
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (V : Finset F)
    (hhasse : ∀ v : Fin 4 → V,
      burgessDistinct (fun i ↦ (v i : F)) →
        |(quarticAffinePointCount (fun i ↦ (v i : F)) : ℝ) + 2 -
            ((Fintype.card F : ℝ) + 1)| ≤
          2 * Real.sqrt (Fintype.card F)) :
    (∑ x : F, quadraticShiftSum V x ^ 4) ≤
      3 * (V.card : ℝ) ^ 2 * Fintype.card F +
        (V.card : ℝ) ^ 4 *
          (3 * Real.sqrt (Fintype.card F)) := by
  apply quadraticShiftSum_fourth_moment_le_of_offDiagonal V
      (3 * Real.sqrt (Fintype.card F)) (by positivity)
  intro v hdiag
  have hdiag' : ¬burgessDiagonal (fun i ↦ (v i : F)) := by
    simpa [burgessDiagonal] using hdiag
  exact quadraticChar_four_correlation_le_three_sqrt_of_hasse_of_offDiagonal
    hF (fun i ↦ (v i : F)) hdiag' (hhasse v)

/-- The unconditional complete fourth-moment estimate: the quartic Hasse
input is discharged by the explicit birational Weierstrass model above. -/
lemma quadraticShiftSum_fourth_moment_le
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (V : Finset F) :
    (∑ x : F, quadraticShiftSum V x ^ 4) ≤
      3 * (V.card : ℝ) ^ 2 * Fintype.card F +
        (V.card : ℝ) ^ 4 *
          (3 * Real.sqrt (Fintype.card F)) := by
  apply quadraticShiftSum_fourth_moment_le_of_quartic_hasse hF V
  intro v hv
  exact quarticAffinePointCount_hasse hF (fun i ↦ (v i : F)) hv

/-! ## The finite Burgess amplifier

The next definitions isolate the incidence energy in Burgess's argument.  If
`n` ranges over an interval and `u` over a short initial segment, the weight at
`x` counts the representations `x = u⁻¹ n`.  The analytic fourth moment proved
above can then be inserted into weighted Hölder without any asymptotic
notation. -/

/-- Multiplicity of a ratio `u⁻¹ n` with `n ∈ I` and `u ∈ U`. -/
def burgessRatioWeight {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (I U : Finset F) (x : F) : ℕ :=
  ((I ×ˢ U).filter fun nu ↦ nu.2⁻¹ * nu.1 = x).card

/-- The real square energy of the Burgess ratio multiplicities. -/
def burgessRatioEnergy {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (I U : Finset F) : ℝ :=
  ∑ x : F, (burgessRatioWeight I U x : ℝ) ^ 2

/-- Ratio multiplicities partition the full incidence box. -/
lemma sum_burgessRatioWeight {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (I U : Finset F) :
    ∑ x : F, burgessRatioWeight I U x = I.card * U.card := by
  rw [← Finset.card_product]
  simpa only [burgessRatioWeight] using (Finset.card_eq_sum_card_fiberwise
    (s := I ×ˢ U) (t := Finset.univ)
    (f := fun nu : F × F ↦ nu.2⁻¹ * nu.1) (by simp)).symm

lemma burgessRatioEnergy_nonneg {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (I U : Finset F) :
    0 ≤ burgessRatioEnergy I U := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The sum of the squares of all fiber sizes of a finite map is the number
of ordered pairs in the domain with the same image. -/
lemma sum_card_fiber_sq_eq_card_collision
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (s : Finset A) (f : A → B) :
    (∑ y : B, ((s.filter fun a ↦ f a = y).card) ^ 2) =
      (((s ×ˢ s).filter fun ab ↦ f ab.1 = f ab.2).card) := by
  let c := (s ×ˢ s).filter fun ab ↦ f ab.1 = f ab.2
  have hmap : (c : Set (A × A)).MapsTo (fun ab ↦ f ab.1)
      (Finset.univ : Finset B) := by
    intro ab _
    exact Finset.mem_univ _
  change (∑ y : B, ((s.filter fun a ↦ f a = y).card) ^ 2) = c.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro y _
  rw [pow_two, ← Finset.card_product]
  congr 1
  ext ab
  simp only [c, Finset.mem_product, Finset.mem_filter]
  aesop

/-- `burgessRatioEnergy` is the cardinality of the corresponding quotient
collision set, coerced to the reals. -/
lemma burgessRatioEnergy_eq_card_collision
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (I U : Finset F) :
    burgessRatioEnergy I U =
      ((((I ×ˢ U) ×ˢ (I ×ˢ U)).filter fun ab ↦
        ab.1.2⁻¹ * ab.1.1 = ab.2.2⁻¹ * ab.2.1).card : ℕ) := by
  have h := sum_card_fiber_sq_eq_card_collision (I ×ˢ U)
    (fun nu ↦ nu.2⁻¹ * nu.1)
  rw [burgessRatioEnergy]
  change (∑ x : F,
      (((((I ×ˢ U).filter fun nu ↦ nu.2⁻¹ * nu.1 = x).card) : ℕ) : ℝ) ^ 2) = _
  simp_rw [← Nat.cast_pow]
  rw [← Nat.cast_sum]
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) h

/-- Fiberwise summation formula for the ratio multiplicities. -/
lemma sum_burgessRatioWeight_mul
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (I U : Finset F) (f : F → ℝ) :
    (∑ x : F, (burgessRatioWeight I U x : ℝ) * f x) =
      ∑ nu ∈ I ×ˢ U, f (nu.2⁻¹ * nu.1) := by
  rw [← Finset.sum_fiberwise' (I ×ˢ U)
    (fun nu : F × F ↦ nu.2⁻¹ * nu.1) f]
  apply Finset.sum_congr rfl
  intro x _
  simp [burgessRatioWeight, nsmul_eq_mul]

/-- A multiplicatively dilated short quadratic-character sum. -/
noncomputable def quadraticDilatedShiftSum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (V : Finset F) (n u : F) : ℝ :=
  ∑ v ∈ V, quadraticCharReal (n + u * v)

lemma abs_quadraticCharReal_of_ne_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {u : F} (hu : u ≠ 0) :
    |quadraticCharReal u| = 1 := by
  rcases quadraticChar_dichotomy hu with huχ | huχ <;>
    simp [quadraticCharReal, huχ]

/-- Multiplicativity converts a dilated sum into a translated sum at the
ratio `u⁻¹ n`; taking absolute values removes the unit character. -/
lemma abs_quadraticDilatedShiftSum_eq
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (V : Finset F) (n : F) {u : F} (hu : u ≠ 0) :
    |quadraticDilatedShiftSum V n u| =
      |quadraticShiftSum V (u⁻¹ * n)| := by
  have hterm (v : F) :
      quadraticCharReal (n + u * v) =
        quadraticCharReal u * quadraticCharReal (u⁻¹ * n + v) := by
    have halg : n + u * v = u * (u⁻¹ * n + v) := by
      field_simp
    rw [halg]
    simp [quadraticCharReal, map_mul]
  rw [quadraticDilatedShiftSum, quadraticShiftSum]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [abs_mul, abs_quadraticCharReal_of_ne_zero hu, one_mul]

/-- The weighted Burgess numerator is exactly the sum of the corresponding
dilated character sums over the incidence box. -/
lemma sum_abs_quadraticDilatedShiftSum_eq_weighted
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (I U V : Finset F) (hU : ∀ u ∈ U, u ≠ 0) :
    (∑ nu ∈ I ×ˢ U, |quadraticDilatedShiftSum V nu.1 nu.2|) =
      ∑ x : F, (burgessRatioWeight I U x : ℝ) *
        |quadraticShiftSum V x| := by
  rw [sum_burgessRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro nu hnu
  rw [abs_quadraticDilatedShiftSum_eq V nu.1
    (hU nu.2 (Finset.mem_product.mp hnu).2)]

/-- Two equal-length interval sums whose starting points differ by `h` differ
by at most `2h` when every summand has absolute value at most one.  This is the
boundary-error estimate used in Burgess averaging. -/
lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H, f (M + i)) -
      ∑ i ∈ Finset.range H, f (M + h + i)| ≤ 2 * h := by
  have hH₁ : h + (H - h) = H := Nat.add_sub_of_le hh
  have hH₂ : (H - h) + h = H := Nat.sub_add_cancel hh
  have hdecomp :
      (∑ i ∈ Finset.range H, f (M + i)) -
          ∑ i ∈ Finset.range H, f (M + h + i) =
        (∑ i ∈ Finset.range h, f (M + i)) -
          ∑ i ∈ Finset.range h, f (M + H + i) := by
    have hleft := Finset.sum_range_add (fun i ↦ f (M + i)) h (H - h)
    have hright := Finset.sum_range_add
      (fun i ↦ f (M + h + i)) (H - h) h
    rw [hH₁] at hleft
    rw [hH₂] at hright
    rw [hleft, hright]
    have hmiddle :
        (∑ x ∈ Finset.range (H - h), f (M + (h + x))) =
          ∑ x ∈ Finset.range (H - h), f (M + h + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hsuffix :
        (∑ x ∈ Finset.range h, f (M + h + ((H - h) + x))) =
          ∑ x ∈ Finset.range h, f (M + H + x) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [hmiddle, hsuffix]
    ring
  rw [hdecomp]
  calc
    |(∑ i ∈ Finset.range h, f (M + i)) -
        ∑ i ∈ Finset.range h, f (M + H + i)| ≤
        |∑ i ∈ Finset.range h, f (M + i)| +
          |∑ i ∈ Finset.range h, f (M + H + i)| := abs_sub _ _
    _ ≤ (∑ i ∈ Finset.range h, |f (M + i)|) +
        ∑ i ∈ Finset.range h, |f (M + H + i)| := by
      gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range h, (1 : ℝ)) +
        ∑ _i ∈ Finset.range h, (1 : ℝ) := by
      gcongr <;> exact hf _
    _ = 2 * h := by simp; ring

lemma abs_quadraticCharReal_le_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    |quadraticCharReal x| ≤ 1 := by
  rcases quadraticChar_isQuadratic F x with hx | hx | hx <;>
    simp [quadraticCharReal, hx]

/-- Natural interval form of the boundary estimate for a quadratic character
modulo a prime. -/
lemma abs_quadraticChar_sum_range_shift_sub_le
    {p : ℕ} [Fact p.Prime] (M H h : ℕ) (hh : h ≤ H) :
    |(∑ i ∈ Finset.range H,
        quadraticCharReal ((M + i : ℕ) : ZMod p)) -
      ∑ i ∈ Finset.range H,
        quadraticCharReal ((M + h + i : ℕ) : ZMod p)| ≤ 2 * h := by
  exact abs_sum_range_shift_sub_le
    (fun n ↦ quadraticCharReal (n : ZMod p))
    (fun n ↦ abs_quadraticCharReal_le_one (n : ZMod p)) M H h hh

/-- Averaging an interval sum over a finite family of forward shifts incurs
only the sum of the corresponding boundary errors.  Burgess amplification
uses this with `g u v = u * v`. -/
lemma abs_burgess_shift_average_sub_le
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (M H : ℕ) (U V : Finset ℕ) (g : ℕ → ℕ → ℕ)
    (hg : ∀ u ∈ U, ∀ v ∈ V, g u v ≤ H) :
    |((U.card * V.card : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, f (M + i)) -
      ∑ u ∈ U, ∑ v ∈ V,
        ∑ i ∈ Finset.range H, f (M + g u v + i)| ≤
      ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
  let S : ℕ → ℝ := fun h ↦ ∑ i ∈ Finset.range H, f (M + h + i)
  have hS0 : S 0 = ∑ i ∈ Finset.range H, f (M + i) := by
    simp [S]
  have heq :
      ((U.card * V.card : ℕ) : ℝ) * S 0 -
          ∑ u ∈ U, ∑ v ∈ V, S (g u v) =
        ∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v)) := by
    simp only [Finset.sum_sub_distrib]
    simp
    ring
  rw [← hS0, heq]
  calc
    |∑ u ∈ U, ∑ v ∈ V, (S 0 - S (g u v))| ≤
        ∑ u ∈ U, |∑ v ∈ V, (S 0 - S (g u v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, |S 0 - S (g u v)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ((2 * g u v : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa [S] using
        abs_sum_range_shift_sub_le f hf M H (g u v) (hg u hu v hv)

/-- If the first-coordinate projection of a finite family of pairs is
injective and all first coordinates lie in one residue class modulo `a`, the
family has at most `H / a + 1` elements. -/
lemma card_le_div_add_one_of_fst_pairwise_modEq
    {s : Finset (ℕ × ℕ)} {H a : ℕ}
    (hsH : ∀ z ∈ s, z.1 < H) (ha : 0 < a)
    (hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) s)
    (hmod : ∀ z ∈ s, ∀ w ∈ s, z.1 ≡ w.1 [MOD a]) :
    s.card ≤ H / a + 1 := by
  let f : ℕ × ℕ → ℕ := fun z ↦ z.1 + 1
  have hfinj : Set.InjOn f s := by
    intro z hz w hw hzw
    apply hinj hz hw
    change z.1 + 1 = w.1 + 1 at hzw
    exact Nat.add_right_cancel hzw
  have hcard : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hfinj).symm
  rw [hcard]
  apply card_le_div_add_one_of_pairwise_modEq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr (hsH z hz)⟩
  · exact ha
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (hmod z hz w hw).add_right 1

/-- Pairs of interval positions which give the same quotient after the two
fixed Burgess denominators are cross-multiplied modulo `p`. -/
def burgessIntervalCollision (p M H u₁ u₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range H) ×ˢ (Finset.range H)).filter fun ij ↦
    (M + ij.1) * u₂ ≡ (M + ij.2) * u₁ [MOD p]

/-- The collision count for fixed positive denominators is controlled by the
reduced denominator `u₁ / gcd u₁ u₂`.  The condition `2UH < p` makes the
difference of two congruences an honest integer equality. -/
lemma burgessIntervalCollision_card_le
    {p M H U u₁ u₂ : ℕ} (hp : p.Prime)
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hsmall : 2 * (U * H) < p) :
    (burgessIntervalCollision p M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    have hu₁p : u₁ < p := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hUle : U ≤ U * H := Nat.le_mul_of_pos_right U hH
      have : U < p := by omega
      exact lt_of_le_of_lt hu₁U this
    have hcop : p.Coprime u₁ := (hp.coprime_iff_not_dvd).2
      (Nat.not_dvd_of_pos_of_lt hu₁pos hu₁p)
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD p] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD p] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHp : H < p := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHp)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHp)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD p] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

/-- Residues of a translated interval of natural numbers modulo `p`. -/
def zmodNatInterval (p M H : ℕ) : Finset (ZMod p) :=
  (Finset.range H).image fun i ↦ (M + i : ℕ)

/-- The positive initial interval, viewed modulo `p`. -/
def zmodPositiveInterval (p U : ℕ) : Finset (ZMod p) :=
  (Finset.Icc 1 U).image fun u : ℕ ↦ (u : ZMod p)

/-- All four-variable interval collisions in the Burgess ratio energy. -/
def burgessIntervalAllCollisions (p M H U : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((((Finset.range H) ×ˢ (Finset.Icc 1 U)) ×ˢ
      ((Finset.range H) ×ˢ (Finset.Icc 1 U))).filter fun ab ↦
    (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD p])

lemma inv_mul_eq_inv_mul_iff {F : Type*} [Field F]
    {n₁ n₂ u₁ u₂ : F} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) :
    u₁⁻¹ * n₁ = u₂⁻¹ * n₂ ↔ n₁ * u₂ = n₂ * u₁ := by
  field_simp

lemma natCast_zmod_ne_zero_of_pos_of_lt {p u : ℕ}
    (hu : 0 < u) (hup : u < p) : (u : ZMod p) ≠ 0 := by
  intro h
  exact (Nat.not_dvd_of_pos_of_lt hu hup)
    ((ZMod.natCast_eq_zero_iff u p).mp h)

lemma eq_of_zmod_interval_cast_eq {p M H i j : ℕ}
    (hi : i < H) (hj : j < H) (hH : H ≤ p)
    (hcast : ((M + i : ℕ) : ZMod p) = (M + j : ℕ)) : i = j := by
  have hmodM : M + i ≡ M + j [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hmod : i ≡ j [MOD p] := Nat.ModEq.add_left_cancel' M hmodM
  exact hmod.eq_of_lt_of_lt (lt_of_lt_of_le hi hH) (lt_of_lt_of_le hj hH)

lemma eq_of_zmod_positive_cast_eq {p U u v : ℕ}
    (hu : u ∈ Finset.Icc 1 U) (hv : v ∈ Finset.Icc 1 U) (hU : U < p)
    (hcast : (u : ZMod p) = v) : u = v := by
  have hmod : u ≡ v [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact hmod.eq_of_lt_of_lt
    (lt_of_le_of_lt (Finset.mem_Icc.mp hu).2 hU)
    (lt_of_le_of_lt (Finset.mem_Icc.mp hv).2 hU)

def burgessCollisionCast (p M : ℕ)
    (ab : (ℕ × ℕ) × (ℕ × ℕ)) :
    ((ZMod p × ZMod p) × (ZMod p × ZMod p)) :=
  ((((M + ab.1.1 : ℕ) : ZMod p), (ab.1.2 : ZMod p)),
    (((M + ab.2.1 : ℕ) : ZMod p), (ab.2.2 : ZMod p)))

/-- Casting all four interval variables modulo a prime gives a bijection
between natural cross-multiplication collisions and finite-field ratio
collisions. -/
lemma ratioCollision_card_eq_intervalAllCollisions
    {p M H U : ℕ} (hp : p.Prime) (hH : H ≤ p) (hU : U < p) :
    (((zmodNatInterval p M H ×ˢ zmodPositiveInterval p U) ×ˢ
        (zmodNatInterval p M H ×ˢ zmodPositiveInterval p U)).filter
      fun ab ↦ ab.1.2⁻¹ * ab.1.1 = ab.2.2⁻¹ * ab.2.1).card =
      (burgessIntervalAllCollisions p M H U).card := by
  letI : Fact p.Prime := ⟨hp⟩
  symm
  apply Finset.card_bij (fun ab _ ↦ burgessCollisionCast p M ab)
  · intro ab hab
    rw [burgessIntervalAllCollisions, Finset.mem_filter] at hab
    rw [Finset.mem_filter]
    rcases hab with ⟨habbox, habcong⟩
    rcases Finset.mem_product.mp habbox with ⟨hab₁, hab₂⟩
    rcases Finset.mem_product.mp hab₁ with ⟨hi₁, hu₁⟩
    rcases Finset.mem_product.mp hab₂ with ⟨hi₂, hu₂⟩
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_product.mpr
      · exact ⟨Finset.mem_image.mpr ⟨ab.1.1, hi₁, rfl⟩,
          Finset.mem_image.mpr ⟨ab.1.2, hu₁, rfl⟩⟩
      · exact ⟨Finset.mem_image.mpr ⟨ab.2.1, hi₂, rfl⟩,
          Finset.mem_image.mpr ⟨ab.2.2, hu₂, rfl⟩⟩
    · apply (inv_mul_eq_inv_mul_iff
        (natCast_zmod_ne_zero_of_pos_of_lt
          (Finset.mem_Icc.mp hu₁).1
          (lt_of_le_of_lt (Finset.mem_Icc.mp hu₁).2 hU))
        (natCast_zmod_ne_zero_of_pos_of_lt
          (Finset.mem_Icc.mp hu₂).1
          (lt_of_le_of_lt (Finset.mem_Icc.mp hu₂).2 hU))).2
      simpa only [burgessCollisionCast, Nat.cast_mul] using
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr habcong
  · intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨habox, _⟩
    rcases Finset.mem_filter.mp hb with ⟨hbbox, _⟩
    rcases Finset.mem_product.mp habox with ⟨ha₁, ha₂⟩
    rcases Finset.mem_product.mp hbbox with ⟨hb₁, hb₂⟩
    rcases Finset.mem_product.mp ha₁ with ⟨hai₁, hau₁⟩
    rcases Finset.mem_product.mp ha₂ with ⟨hai₂, hau₂⟩
    rcases Finset.mem_product.mp hb₁ with ⟨hbi₁, hbu₁⟩
    rcases Finset.mem_product.mp hb₂ with ⟨hbi₂, hbu₂⟩
    apply Prod.ext
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₁) (Finset.mem_range.mp hbi₁) hH
          (congrArg (fun z ↦ z.1.1) hab)
      · exact eq_of_zmod_positive_cast_eq hau₁ hbu₁ hU
          (congrArg (fun z ↦ z.1.2) hab)
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₂) (Finset.mem_range.mp hbi₂) hH
          (congrArg (fun z ↦ z.2.1) hab)
      · exact eq_of_zmod_positive_cast_eq hau₂ hbu₂ hU
          (congrArg (fun z ↦ z.2.2) hab)
  · intro z hz
    rw [Finset.mem_filter] at hz
    rcases hz with ⟨hzbox, hzratio⟩
    rcases Finset.mem_product.mp hzbox with ⟨hz₁, hz₂⟩
    rcases Finset.mem_product.mp hz₁ with ⟨hzn₁, hzu₁⟩
    rcases Finset.mem_product.mp hz₂ with ⟨hzn₂, hzu₂⟩
    rw [zmodNatInterval, Finset.mem_image] at hzn₁ hzn₂
    rw [zmodPositiveInterval, Finset.mem_image] at hzu₁ hzu₂
    rcases hzn₁ with ⟨i₁, hi₁, hi₁z⟩
    rcases hzu₁ with ⟨u₁, hu₁, hu₁z⟩
    rcases hzn₂ with ⟨i₂, hi₂, hi₂z⟩
    rcases hzu₂ with ⟨u₂, hu₂, hu₂z⟩
    refine ⟨((i₁, u₁), (i₂, u₂)), ?_, ?_⟩
    · rw [burgessIntervalAllCollisions, Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hi₁, hu₁⟩,
            Finset.mem_product.mpr ⟨hi₂, hu₂⟩⟩
      · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        rw [Nat.cast_mul, Nat.cast_mul]
        apply (inv_mul_eq_inv_mul_iff
          (natCast_zmod_ne_zero_of_pos_of_lt
            (Finset.mem_Icc.mp hu₁).1
            (lt_of_le_of_lt (Finset.mem_Icc.mp hu₁).2 hU))
          (natCast_zmod_ne_zero_of_pos_of_lt
            (Finset.mem_Icc.mp hu₂).1
            (lt_of_le_of_lt (Finset.mem_Icc.mp hu₂).2 hU))).mp
        simpa only [hi₁z, hi₂z, hu₁z, hu₂z] using hzratio
    · simp [burgessCollisionCast, hi₁z, hi₂z, hu₁z, hu₂z]

lemma burgessIntervalAllCollisions_card_eq_sum (p M H U : ℕ) :
    (burgessIntervalAllCollisions p M H U).card =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (burgessIntervalCollision p M H u₁ u₂).card := by
  simp only [burgessIntervalAllCollisions, burgessIntervalCollision,
    Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u₁ hu₁
  calc
    (∑ i₁ ∈ Finset.range H,
        ∑ i₂ ∈ Finset.range H, ∑ u₂ ∈ Finset.Icc 1 U,
          if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD p] then 1 else 0) =
        ∑ i₁ ∈ Finset.range H,
          ∑ u₂ ∈ Finset.Icc 1 U, ∑ i₂ ∈ Finset.range H,
            if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD p] then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i₁ hi₁
      rw [Finset.sum_comm]
    _ = ∑ u₂ ∈ Finset.Icc 1 U,
          ∑ i₁ ∈ Finset.range H, ∑ i₂ ∈ Finset.range H,
            if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD p] then 1 else 0 := by
      rw [Finset.sum_comm]

lemma burgessRatioEnergy_zmodIntervals_eq_sum
    {p M H U : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hH : H ≤ p) (hU : U < p) :
    burgessRatioEnergy (zmodNatInterval p M H)
        (zmodPositiveInterval p U) =
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (burgessIntervalCollision p M H u₁ u₂).card : ℕ) : ℝ) := by
  rw [burgessRatioEnergy_eq_card_collision]
  rw [ratioCollision_card_eq_intervalAllCollisions hp hH hU]
  rw [burgessIntervalAllCollisions_card_eq_sum]

lemma burgessRatioEnergy_zmodIntervals_le_reduced_sum
    {p M H U : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hH : 0 < H) (hU : 0 < U)
    (hHp : H ≤ p) (hUp : U < p) (hsmall : 2 * (U * H) < p) :
    burgessRatioEnergy (zmodNatInterval p M H)
        (zmodPositiveInterval p U) ≤
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) := by
  rw [burgessRatioEnergy_zmodIntervals_eq_sum hp hHp hUp]
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      burgessIntervalCollision_card_le hp hH hU hu₁ hu₂ hsmall

/-- Positive multiples of `d` not exceeding `U`. -/
def positiveMultiplesUpTo (d U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ d ∣ u

lemma positiveMultiplesUpTo_card (d U : ℕ) :
    (positiveMultiplesUpTo d U).card = U / d := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 U := by
    ext x
    simp
    omega
  rw [positiveMultiplesUpTo, hset]
  exact Nat.Ioc_filter_dvd_card_eq_div U d

/-- Division by `d` bijects its positive multiples up to `U` with the
positive integers up to `U / d`. -/
lemma sum_positiveMultiplesUpTo_quotient
    {R : Type*} [AddCommMonoid R] (d U : ℕ) (hd : 0 < d)
    (f : ℕ → R) :
    (∑ u ∈ positiveMultiplesUpTo d U, f (u / d)) =
      ∑ a ∈ Finset.Icc 1 (U / d), f a := by
  apply Finset.sum_bij (fun u _ ↦ u / d)
  · intro u hu
    change u ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hu.1).1 hu.2) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hu.1).2⟩
  · intro u₁ hu₁ u₂ hu₂ h
    change u₁ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₁
    change u₂ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₂
    have hd₁ := (Finset.mem_filter.mp hu₁).2
    have hd₂ := (Finset.mem_filter.mp hu₂).2
    calc
      u₁ = d * (u₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (u₂ / d) := by rw [h]
      _ = u₂ := Nat.mul_div_cancel' hd₂
  · intro a ha
    refine ⟨d * a, ?_, ?_⟩
    · change d * a ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.mul_pos hd ha.1,
          by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp ha.2⟩
      · exact dvd_mul_right d a
    · rw [Nat.mul_div_cancel_left]
      exact hd
  · intro u hu
    rfl

lemma sum_Icc_natDiv_add_one_cast_le (H n : ℕ) :
    (((∑ a ∈ Finset.Icc 1 n, (H / a + 1)) : ℕ) : ℝ) ≤
      H * (1 + Real.log n) + n := by
  rw [Nat.cast_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n, (((H / a + 1) : ℕ) : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 n, ((H : ℝ) / a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) le_rfl
    _ = (∑ a ∈ Finset.Icc 1 n, (H : ℝ) / a) + n := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ H * (1 + Real.log n) + n := by
      gcongr
      exact sum_Icc_natCast_div_le H n

/-- The gcd itself is one of the common divisors, so the reduced-denominator
term is bounded by the sum over all common divisors. -/
lemma reduced_term_le_common_divisor_sum
    {H U u₁ u₂ : ℕ} (hu₁ : u₁ ∈ Finset.Icc 1 U) :
    H / (u₁ / u₁.gcd u₂) + 1 ≤
      ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
  let d := u₁.gcd u₂
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hdmem : d ∈ Finset.Icc 1 U := by
    rw [Finset.mem_Icc]
    exact ⟨hdpos, (Nat.gcd_le_left u₂ hu₁pos).trans
      (Finset.mem_Icc.mp hu₁).2⟩
  calc
    H / (u₁ / u₁.gcd u₂) + 1 =
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      simp [d, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      exact Finset.single_le_sum
        (s := Finset.Icc 1 U)
        (f := fun d ↦ if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hdmem

def burgessDivisorOvercount (H U : ℕ) : ℕ :=
  ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
    ∑ d ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0

lemma burgessDivisorSlice_eq (H U d : ℕ) (hd : 0 < d) :
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  classical
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  change (∑ u₁ ∈ positiveMultiplesUpTo d U,
      ∑ u₂ ∈ Finset.Icc 1 U,
        if d ∣ u₂ then H / (u₁ / d) + 1 else 0) = _
  calc
    (∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ _u₂ ∈ positiveMultiplesUpTo d U,
          (H / (u₁ / d) + 1) := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [← Finset.sum_filter]
      rfl
    _ = (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
      simp_rw [Finset.sum_const]
      rw [positiveMultiplesUpTo_card]
      simp_rw [Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact sum_positiveMultiplesUpTo_quotient d U hd
        (fun a ↦ H / a + 1)

lemma burgessDivisorOvercount_eq (H U : ℕ) :
    burgessDivisorOvercount H U =
      ∑ d ∈ Finset.Icc 1 U, (U / d) *
        ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  rw [burgessDivisorOvercount]
  calc
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        ∑ d ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 U, ∑ u₁ ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact burgessDivisorSlice_eq H U d (Finset.mem_Icc.mp hdmem).1

lemma burgessDivisorOvercount_cast_le (H U : ℕ) (hU : 0 < U) :
    (burgessDivisorOvercount H U : ℝ) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  rw [burgessDivisorOvercount_eq, Nat.cast_sum]
  have hlogU : 0 ≤ 1 + Real.log U := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg this]
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ((((U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 U,
        ((U : ℝ) / d) * ((H : ℝ) * (1 + Real.log U) + U) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdU : d ≤ U := (Finset.mem_Icc.mp hdmem).2
      have hnpos : 0 < U / d := Nat.div_pos hdU hdpos
      have hnU : U / d ≤ U := Nat.div_le_self U d
      have hlog : Real.log (((U / d : ℕ) : ℝ)) ≤ Real.log U := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnU
      rw [Nat.cast_mul]
      apply mul_le_mul
      · exact Nat.cast_div_le
      · calc
          (((∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ) ≤
              (H : ℝ) * (1 + Real.log (((U / d : ℕ) : ℝ))) +
                (U / d : ℕ) :=
            sum_Icc_natDiv_add_one_cast_le H (U / d)
          _ ≤ (H : ℝ) * (1 + Real.log U) + U := by
            gcongr
      · positivity
      · positivity
    _ = ((H : ℝ) * (1 + Real.log U) + U) *
        ∑ d ∈ Finset.Icc 1 U, ((U : ℝ) / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le U U)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg H) hlogU) (Nat.cast_nonneg U))

lemma reduced_denominator_sum_cast_le
    (H U : ℕ) :
    ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) ≤
      (burgessDivisorOvercount H U : ℝ) := by
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      reduced_term_le_common_divisor_sum hu₁

/-- Elementary energy estimate for the translated interval and the positive
amplifier interval. -/
lemma burgessRatioEnergy_zmodIntervals_le
    {p M H U : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hH : 0 < H) (hU : 0 < U)
    (hHp : H ≤ p) (hUp : U < p) (hsmall : 2 * (U * H) < p) :
    burgessRatioEnergy (zmodNatInterval p M H)
        (zmodPositiveInterval p U) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  calc
    burgessRatioEnergy (zmodNatInterval p M H)
        (zmodPositiveInterval p U) ≤
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) :=
      burgessRatioEnergy_zmodIntervals_le_reduced_sum
        hp hH hU hHp hUp hsmall
    _ ≤ (burgessDivisorOvercount H U : ℝ) :=
      reduced_denominator_sum_cast_le H U
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) :=
      burgessDivisorOvercount_cast_le H U hU

/-- Weighted fourth-moment inequality at the heart of the `r = 2` Burgess
argument.  The only remaining arithmetic input is an upper bound for
`burgessRatioEnergy` when `I` and `U` are short integer intervals. -/
lemma burgess_weighted_shift_fourth_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (I U V : Finset F) :
    (∑ x : F, (burgessRatioWeight I U x : ℝ) *
        |quadraticShiftSum V x|) ^ 4 ≤
      ((I.card * U.card : ℕ) : ℝ) ^ 2 * burgessRatioEnergy I U *
        (3 * (V.card : ℝ) ^ 2 * Fintype.card F +
          (V.card : ℝ) ^ 4 *
            (3 * Real.sqrt (Fintype.card F))) := by
  have hholder := sum_mul_pow_four_le_sum_sq_mul_sum_pow_four
    (Finset.univ : Finset F)
    (fun x ↦ (burgessRatioWeight I U x : ℝ))
    (fun x ↦ |quadraticShiftSum V x|)
    (fun _ _ ↦ Nat.cast_nonneg _)
  have hsum :
      (∑ x : F, (burgessRatioWeight I U x : ℝ)) =
        ((I.card * U.card : ℕ) : ℝ) := by
    exact_mod_cast sum_burgessRatioWeight I U
  have habs4 :
      (∑ x : F, |quadraticShiftSum V x| ^ 4) =
        ∑ x : F, quadraticShiftSum V x ^ 4 := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      |quadraticShiftSum V x| ^ 4 =
          (|quadraticShiftSum V x| ^ 2) ^ 2 := by ring
      _ = (quadraticShiftSum V x ^ 2) ^ 2 := by rw [sq_abs]
      _ = quadraticShiftSum V x ^ 4 := by ring
  rw [hsum, show (∑ x : F, ((burgessRatioWeight I U x : ℝ)) ^ 2) =
      burgessRatioEnergy I U by rfl, habs4] at hholder
  exact hholder.trans (mul_le_mul_of_nonneg_left
    (quadraticShiftSum_fourth_moment_le hF V)
    (mul_nonneg (sq_nonneg _) (burgessRatioEnergy_nonneg I U)))

lemma zmodNatInterval_card {p M H : ℕ} (hH : H ≤ p) :
    (zmodNatInterval p M H).card = H := by
  have hinj : Set.InjOn (fun i : ℕ ↦ ((M + i : ℕ) : ZMod p))
      (Finset.range H) := by
    intro i hi j hj hij
    exact eq_of_zmod_interval_cast_eq
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hH hij
  calc
    (zmodNatInterval p M H).card = (Finset.range H).card := by
      rw [zmodNatInterval]
      exact Finset.card_image_of_injOn hinj
    _ = H := Finset.card_range H

lemma zmodPositiveInterval_card {p U : ℕ} (hU : U < p) :
    (zmodPositiveInterval p U).card = U := by
  have hinj : Set.InjOn (fun u : ℕ ↦ (u : ZMod p))
      (Finset.Icc 1 U) := by
    intro u hu v hv huv
    exact eq_of_zmod_positive_cast_eq hu hv hU huv
  calc
    (zmodPositiveInterval p U).card = (Finset.Icc 1 U).card := by
      rw [zmodPositiveInterval]
      exact Finset.card_image_of_injOn hinj
    _ = U := by simp

lemma quadraticDilatedShiftSum_zmodPositive
    {p M i u V : ℕ} [Fact p.Prime] (hV : V < p) :
    quadraticDilatedShiftSum (zmodPositiveInterval p V)
        ((M + i : ℕ) : ZMod p) (u : ZMod p) =
      ∑ v ∈ Finset.Icc 1 V,
        quadraticCharReal (((M + i + u * v : ℕ) : ZMod p)) := by
  have hinj : Set.InjOn (fun v : ℕ ↦ (v : ZMod p))
      (Finset.Icc 1 V) := by
    intro v hv w hw hvw
    exact eq_of_zmod_positive_cast_eq hv hw hV hvw
  rw [quadraticDilatedShiftSum, zmodPositiveInterval]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    congr 1
    push_cast
    ring
  · exact hinj

lemma sum_abs_quadraticDilatedShiftSum_zmodIntervals
    {p M H U V : ℕ} [Fact p.Prime]
    (hH : H ≤ p) (hU : U < p) (hV : V < p) :
    (∑ nu ∈ zmodNatInterval p M H ×ˢ zmodPositiveInterval p U,
      |quadraticDilatedShiftSum (zmodPositiveInterval p V) nu.1 nu.2|) =
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| := by
  have hinjI : Set.InjOn (fun i : ℕ ↦ ((M + i : ℕ) : ZMod p))
      (Finset.range H) := by
    intro i hi j hj hij
    exact eq_of_zmod_interval_cast_eq
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hH hij
  have hinjU : Set.InjOn (fun u : ℕ ↦ (u : ZMod p))
      (Finset.Icc 1 U) := by
    intro u hu w hw huw
    exact eq_of_zmod_positive_cast_eq hu hw hU huw
  rw [Finset.sum_product]
  rw [zmodNatInterval, Finset.sum_image hinjI]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zmodPositiveInterval, Finset.sum_image hinjU]
  apply Finset.sum_congr rfl
  intro u hu
  rw [quadraticDilatedShiftSum_zmodPositive hV]

lemma abs_burgess_shifted_triple_sum_le
    {p M H U V : ℕ} [Fact p.Prime] :
    |∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H,
          quadraticCharReal (((M + u * v + i : ℕ) : ZMod p))| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| := by
  have hreorder :
      (∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          ∑ i ∈ Finset.range H,
            quadraticCharReal (((M + u * v + i : ℕ) : ZMod p))) =
        ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          ∑ v ∈ Finset.Icc 1 V,
            quadraticCharReal (((M + i + u * v : ℕ) : ZMod p)) := by
    calc
      (∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          ∑ i ∈ Finset.range H,
            quadraticCharReal (((M + u * v + i : ℕ) : ZMod p))) =
        ∑ u ∈ Finset.Icc 1 U, ∑ i ∈ Finset.range H,
          ∑ v ∈ Finset.Icc 1 V,
            quadraticCharReal (((M + u * v + i : ℕ) : ZMod p)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          ∑ v ∈ Finset.Icc 1 V,
            quadraticCharReal (((M + u * v + i : ℕ) : ZMod p)) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 2
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        ∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

lemma abs_quadraticChar_amplified_sub_shifted_le
    {p M H U V : ℕ} [Fact p.Prime] (hUV : U * V ≤ H) :
    |(((U * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H,
          quadraticCharReal (((M + i : ℕ) : ZMod p))) -
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H,
          quadraticCharReal (((M + u * v + i : ℕ) : ZMod p)))| ≤
      (2 : ℝ) * (U * V) ^ 2 := by
  have havg := abs_burgess_shift_average_sub_le
    (fun n ↦ quadraticCharReal (n : ZMod p))
    (fun n ↦ abs_quadraticCharReal_le_one (n : ZMod p))
    M H (Finset.Icc 1 U) (Finset.Icc 1 V) (fun u v ↦ u * v)
    (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp hu).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have hcards :
      ((((Finset.Icc 1 U).card * (Finset.Icc 1 V).card : ℕ) : ℝ)) =
        (U * V : ℕ) := by simp
  rw [hcards] at havg
  calc
    |(((U * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H,
          quadraticCharReal (((M + i : ℕ) : ZMod p))) -
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H,
          quadraticCharReal (((M + u * v + i : ℕ) : ZMod p)))| ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ((2 * (u * v) : ℕ) : ℝ) := havg
    _ ≤ ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ((2 * (U * V) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      norm_cast
      exact Nat.mul_le_mul_left 2
        (Nat.mul_le_mul (Finset.mem_Icc.mp hu).2
          (Finset.mem_Icc.mp hv).2)
    _ = (2 : ℝ) * (U * V) ^ 2 := by
      simp
      ring

lemma burgess_natural_numerator_eq_weighted
    {p M H U V : ℕ} [Fact p.Prime]
    (hH : H ≤ p) (hU : U < p) (hV : V < p) :
    (∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))|) =
      ∑ x : ZMod p,
        (burgessRatioWeight (zmodNatInterval p M H)
          (zmodPositiveInterval p U) x : ℝ) *
          |quadraticShiftSum (zmodPositiveInterval p V) x| := by
  have hUnz : ∀ u ∈ zmodPositiveInterval p U, u ≠ 0 := by
    intro u hu
    rw [zmodPositiveInterval, Finset.mem_image] at hu
    obtain ⟨n, hn, rfl⟩ := hu
    exact natCast_zmod_ne_zero_of_pos_of_lt
      (Finset.mem_Icc.mp hn).1 (lt_of_le_of_lt (Finset.mem_Icc.mp hn).2 hU)
  rw [← sum_abs_quadraticDilatedShiftSum_eq_weighted
    (zmodNatInterval p M H) (zmodPositiveInterval p U)
    (zmodPositiveInterval p V) hUnz]
  exact (sum_abs_quadraticDilatedShiftSum_zmodIntervals hH hU hV).symm

lemma burgess_amplified_abs_le_weighted_add_error
    {p M H U V : ℕ} [Fact p.Prime]
    (hH : H ≤ p) (hU : U < p) (hV : V < p) (hUV : U * V ≤ H) :
    ((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticCharReal (((M + i : ℕ) : ZMod p))| ≤
      (∑ x : ZMod p,
        (burgessRatioWeight (zmodNatInterval p M H)
          (zmodPositiveInterval p U) x : ℝ) *
          |quadraticShiftSum (zmodPositiveInterval p V) x|) +
        (2 : ℝ) * (U * V) ^ 2 := by
  let S : ℝ := ∑ i ∈ Finset.range H,
    quadraticCharReal (((M + i : ℕ) : ZMod p))
  let T : ℝ := ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H,
      quadraticCharReal (((M + u * v + i : ℕ) : ZMod p))
  have havg : |(((U * V : ℕ) : ℝ) * S) - T| ≤
      (2 : ℝ) * (U * V) ^ 2 := by
    exact abs_quadraticChar_amplified_sub_shifted_le hUV
  have hT : |T| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| := by
    exact abs_burgess_shifted_triple_sum_le
  have htri : |(((U * V : ℕ) : ℝ) * S)| ≤
      |(((U * V : ℕ) : ℝ) * S) - T| + |T| := by
    calc
      |(((U * V : ℕ) : ℝ) * S)| =
          |((((U * V : ℕ) : ℝ) * S) - T) + T| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (U * V))] at htri
  change ((U * V : ℕ) : ℝ) * |S| ≤ _
  calc
    ((U * V : ℕ) : ℝ) * |S| ≤
        |(((U * V : ℕ) : ℝ) * S) - T| + |T| := htri
    _ ≤ (2 : ℝ) * (U * V) ^ 2 +
        ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticCharReal (((M + i + u * v : ℕ) : ZMod p))| :=
      add_le_add havg hT
    _ = (∑ x : ZMod p,
        (burgessRatioWeight (zmodNatInterval p M H)
          (zmodPositiveInterval p U) x : ℝ) *
          |quadraticShiftSum (zmodPositiveInterval p V) x|) +
        (2 : ℝ) * (U * V) ^ 2 := by
      rw [burgess_natural_numerator_eq_weighted hH hU hV]
      ring

lemma add_pow_four_le_eight (a b : ℝ) :
    (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h₁ : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have h₂ : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
  have hs₁ : 0 ≤ (a + b) ^ 2 := sq_nonneg _
  have hs₂ : 0 ≤ 2 * (a ^ 2 + b ^ 2) := by positivity
  have hsquare : ((a + b) ^ 2) ^ 2 ≤
      (2 * (a ^ 2 + b ^ 2)) ^ 2 := by nlinarith
  nlinarith

/-- Explicit `r = 2` Burgess amplification bound.  This is the complete
finite inequality: the only hypotheses are the elementary size conditions
on the two amplifier lengths. -/
lemma burgess_amplified_fourth_bound
    {p M H U V : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp₂ : p ≠ 2)
    (hH : 0 < H) (hU₀ : 0 < U)
    (hHp : H ≤ p) (hUp : U < p) (hVp : V < p)
    (hUV : U * V ≤ H) (hsmall : 2 * (U * H) < p) :
    ((((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticCharReal (((M + i : ℕ) : ZMod p))|) ^ 4) ≤
      8 *
        (((((H * U : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (3 * (V : ℝ) ^ 2 * p +
            (V : ℝ) ^ 4 * (3 * Real.sqrt p))) +
          ((2 : ℝ) * (U * V) ^ 2) ^ 4) := by
  let B : ℝ := ∑ x : ZMod p,
    (burgessRatioWeight (zmodNatInterval p M H)
      (zmodPositiveInterval p U) x : ℝ) *
      |quadraticShiftSum (zmodPositiveInterval p V) x|
  let E : ℝ := (2 : ℝ) * (U * V) ^ 2
  let X : ℝ := ((U * V : ℕ) : ℝ) *
    |∑ i ∈ Finset.range H,
      quadraticCharReal (((M + i : ℕ) : ZMod p))|
  have hXB : X ≤ B + E := by
    exact burgess_amplified_abs_le_weighted_add_error hHp hUp hVp hUV
  have hX₀ : 0 ≤ X := by positivity
  have hB₀ : 0 ≤ B := by
    dsimp [B]
    positivity
  have hE₀ : 0 ≤ E := by positivity
  have hpow : X ^ 4 ≤ (B + E) ^ 4 :=
    pow_le_pow_left₀ hX₀ hXB 4
  have hadd := add_pow_four_le_eight B E
  have hchar : ringChar (ZMod p) ≠ 2 :=
    (ZMod.ringChar_zmod_n p).substr hp₂
  have hweighted := burgess_weighted_shift_fourth_bound hchar
    (zmodNatInterval p M H) (zmodPositiveInterval p U)
    (zmodPositiveInterval p V)
  rw [zmodNatInterval_card hHp, zmodPositiveInterval_card hUp,
    zmodPositiveInterval_card hVp, ZMod.card] at hweighted
  have henergy := burgessRatioEnergy_zmodIntervals_le (M := M)
    hp hH hU₀ hHp hUp hsmall
  have hmoment₀ : 0 ≤
      3 * (V : ℝ) ^ 2 * p +
        (V : ℝ) ^ 4 * (3 * Real.sqrt p) := by positivity
  have hweighted' : B ^ 4 ≤
      ((H * U : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) *
        (3 * (V : ℝ) ^ 2 * p +
          (V : ℝ) ^ 4 * (3 * Real.sqrt p)) := by
    calc
      B ^ 4 ≤ ((H * U : ℕ) : ℝ) ^ 2 *
          burgessRatioEnergy (zmodNatInterval p M H)
            (zmodPositiveInterval p U) *
          (3 * (V : ℝ) ^ 2 * p +
            (V : ℝ) ^ 4 * (3 * Real.sqrt p)) := hweighted
      _ ≤ ((H * U : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) *
          (3 * (V : ℝ) ^ 2 * p +
            (V : ℝ) ^ 4 * (3 * Real.sqrt p)) := by
        gcongr
  calc
    X ^ 4 ≤ (B + E) ^ 4 := hpow
    _ ≤ 8 * (B ^ 4 + E ^ 4) := hadd
    _ ≤ 8 *
        (((((H * U : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (3 * (V : ℝ) ^ 2 * p +
            (V : ℝ) ^ 4 * (3 * Real.sqrt p))) + E ^ 4) := by
      gcongr
    _ = _ := by rfl

/-- A finite square-hitting consequence of the explicit Burgess inequality.
If the fourth-moment upper bound is strictly smaller than the fourth power
forced by an interval containing no quadratic residue, the interval contains
a square modulo `p`. -/
lemma exists_isSquare_zmod_in_interval_of_burgess_bound
    {p M H U V : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp₂ : p ≠ 2)
    (hH : 0 < H) (hU₀ : 0 < U)
    (hHp : H ≤ p) (hUp : U < p) (hVp : V < p)
    (hUV : U * V ≤ H) (hsmall : 2 * (U * H) < p)
    (hstrict :
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * p +
              (V : ℝ) ^ 4 * (3 * Real.sqrt p))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * H) ^ 4) :
    ∃ i ∈ Finset.range H,
      IsSquare (((M + i : ℕ) : ZMod p)) := by
  by_contra hnone
  push_neg at hnone
  have hchar : ∀ i ∈ Finset.range H,
      quadraticCharReal (((M + i : ℕ) : ZMod p)) = -1 := by
    intro i hi
    have hneg : quadraticChar (ZMod p) (((M + i : ℕ) : ZMod p)) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr (hnone i hi)
    have hneg' := congrArg (fun z : ℤ ↦ (z : ℝ)) hneg
    simpa only [quadraticCharReal, Int.cast_neg, Int.cast_one] using hneg'
  have hsum :
      (∑ i ∈ Finset.range H,
        quadraticCharReal (((M + i : ℕ) : ZMod p))) = -(H : ℝ) := by
    calc
      (∑ i ∈ Finset.range H,
          quadraticCharReal (((M + i : ℕ) : ZMod p))) =
          ∑ _i ∈ Finset.range H, (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hchar i hi
      _ = -(H : ℝ) := by simp
  have hbound := burgess_amplified_fourth_bound
    hp hp₂ hH hU₀ hHp hUp hVp hUV hsmall (M := M)
  rw [hsum, abs_neg, abs_of_nonneg (Nat.cast_nonneg H)] at hbound
  exact (not_lt_of_ge hbound) hstrict

/-! ### The squarefree CRT expansion

Nguyen--Vu's normalized modulus is assembled from coprime prime-power
factors.  The squarefree analytic core is governed by the following local
quadratic characters and their exact powerset expansion. -/

/-- The real quadratic character modulo `p`, defined to be zero when `p` is
not prime so that it can be used uniformly inside products over finsets. -/
noncomputable def primeQuadraticCharReal (p n : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    quadraticCharReal (n : ZMod p)
  else 0

lemma primeQuadraticCharReal_of_prime {p n : ℕ} [Fact p.Prime]
    (hp : p.Prime) :
    primeQuadraticCharReal p n = quadraticCharReal (n : ZMod p) := by
  simp only [primeQuadraticCharReal, dif_pos hp]

lemma primeQuadraticCharReal_eq_one_iff_isSquare
    {p n : ℕ} [Fact p.Prime] (hp : p.Prime)
    (hn : (n : ZMod p) ≠ 0) :
    primeQuadraticCharReal p n = 1 ↔ IsSquare (n : ZMod p) := by
  rw [primeQuadraticCharReal_of_prime hp]
  have hiff := quadraticChar_one_iff_isSquare (F := ZMod p) hn
  constructor
  · intro h
    apply hiff.mp
    change (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℝ) = 1 at h
    exact_mod_cast h
  · intro h
    have hone := hiff.mpr h
    change (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℝ) = 1
    exact_mod_cast hone

lemma primeQuadraticCharReal_eq_neg_one_iff_not_isSquare
    {p n : ℕ} [Fact p.Prime] (hp : p.Prime) :
    primeQuadraticCharReal p n = -1 ↔ ¬IsSquare (n : ZMod p) := by
  rw [primeQuadraticCharReal_of_prime hp]
  have hiff := quadraticChar_neg_one_iff_not_isSquare
    (F := ZMod p) (a := (n : ZMod p))
  constructor
  · intro h
    apply hiff.mp
    change (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℝ) = -1 at h
    exact_mod_cast h
  · intro h
    have hneg := hiff.mpr h
    change (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℝ) = -1
    exact_mod_cast hneg

lemma natCast_zmod_prime_ne_zero_of_coprime
    {p q n : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hnq : n.Coprime q) :
    (n : ZMod p) ≠ 0 := by
  intro hnzero
  have hpdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hnzero
  exact (hp.coprime_iff_not_dvd.mp ((hnq.of_dvd_right hpq).symm)) hpdvd

/-- Product of the local quadratic characters indexed by a set of primes. -/
noncomputable def quadraticPrimeFactorProduct (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ s, primeQuadraticCharReal p n

/-- Exact expansion of the product of the local square-class factors. -/
lemma sum_quadraticPrimeFactorProduct_powerset (s : Finset ℕ) (n : ℕ) :
    (∑ t ∈ s.powerset, quadraticPrimeFactorProduct t n) =
      ∏ p ∈ s, (1 + primeQuadraticCharReal p n) := by
  simpa only [quadraticPrimeFactorProduct] using
    (Finset.prod_one_add (s := s) (f := fun p ↦ primeQuadraticCharReal p n)).symm

lemma sum_quadraticPrimeFactorProduct_powerset_eq_pow
    {s : Finset ℕ} {n : ℕ}
    (h : ∀ p ∈ s, primeQuadraticCharReal p n = 1) :
    (∑ t ∈ s.powerset, quadraticPrimeFactorProduct t n) = (2 : ℝ) ^ s.card := by
  rw [sum_quadraticPrimeFactorProduct_powerset]
  calc
    (∏ p ∈ s, (1 + primeQuadraticCharReal p n)) =
        ∏ _p ∈ s, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [h p hp]
      norm_num
    _ = (2 : ℝ) ^ s.card := by simp

lemma sum_quadraticPrimeFactorProduct_powerset_eq_zero
    {s : Finset ℕ} {n p : ℕ} (hp : p ∈ s)
    (h : primeQuadraticCharReal p n = -1) :
    (∑ t ∈ s.powerset, quadraticPrimeFactorProduct t n) = 0 := by
  rw [sum_quadraticPrimeFactorProduct_powerset]
  exact Finset.prod_eq_zero hp (by rw [h]; norm_num)

/-- For a unit modulo `q`, the powerset character expansion is the square
indicator on all prime factors of `q`. -/
lemma sum_quadraticPrimeFactorProduct_powerset_eq_pow_iff
    {q n : ℕ} (hnq : n.Coprime q) :
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) =
        (2 : ℝ) ^ q.primeFactors.card ↔
      ∀ p ∈ q.primeFactors, IsSquare (n : ZMod p) := by
  constructor
  · intro hsum p hpq
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    letI : Fact p.Prime := ⟨hp⟩
    by_contra hsq
    have hneg : primeQuadraticCharReal p n = -1 :=
      (primeQuadraticCharReal_eq_neg_one_iff_not_isSquare hp).mpr hsq
    have hzero := sum_quadraticPrimeFactorProduct_powerset_eq_zero hpq hneg
    rw [hsum] at hzero
    have hpowpos : 0 < (2 : ℝ) ^ q.primeFactors.card := by positivity
    linarith
  · intro hsquares
    apply sum_quadraticPrimeFactorProduct_powerset_eq_pow
    intro p hpq
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    letI : Fact p.Prime := ⟨hp⟩
    have hnonzero := natCast_zmod_prime_ne_zero_of_coprime hp
      (Nat.dvd_of_mem_primeFactors hpq) hnq
    exact (primeQuadraticCharReal_eq_one_iff_isSquare hp hnonzero).mpr
      (hsquares p hpq)

lemma primeFactors_pairwise_coprime (q : ℕ) :
    Pairwise (fun p r : q.primeFactors ↦ Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  have hr : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.property
  exact hp.coprime_iff_not_dvd.mpr fun hdvd ↦
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd))

/-- A residue modulo a squarefree number is a square exactly when all of its
prime-modulus projections are squares. -/
lemma isSquare_zmod_iff_local_of_squarefree
    {q n : ℕ} (hq : Squarefree q) :
    IsSquare (n : ZMod q) ↔
      ∀ p ∈ q.primeFactors, IsSquare (n : ZMod p) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hprod : q = ∏ p : q.primeFactors, (p : ℕ) := by
    calc
      q = ∏ p ∈ q.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hq).symm
      _ = ∏ p : q.primeFactors, (p : ℕ) := by
        exact (Finset.prod_attach q.primeFactors (fun p : ℕ ↦ p)).symm
  let e0 : ZMod q ≃+* ZMod (∏ p : q.primeFactors, (p : ℕ)) :=
    ZMod.ringEquivCongr hprod
  let e1 : ZMod (∏ p : q.primeFactors, (p : ℕ)) ≃+*
      (∀ p : q.primeFactors, ZMod (p : ℕ)) :=
    ZMod.prodEquivPi (fun p : q.primeFactors ↦ (p : ℕ))
      (primeFactors_pairwise_coprime q)
  let e := e0.trans e1
  have heval (p : q.primeFactors) : e (n : ZMod q) p = (n : ZMod (p : ℕ)) := by
    simp [e, e0, e1]
  constructor
  · intro hs p hpq
    let ps : q.primeFactors := ⟨p, hpq⟩
    have himage : IsSquare (e (n : ZMod q)) := hs.map e.toMonoidHom
    obtain ⟨r, hr⟩ := himage
    refine ⟨r ps, ?_⟩
    have happ := congrFun hr ps
    simpa only [Pi.mul_apply, heval ps] using happ
  · intro hs
    have himage : IsSquare (e (n : ZMod q)) := by
      refine ⟨fun p ↦ (hs p p.property).choose, ?_⟩
      funext p
      have hpw := (hs p p.property).choose_spec
      simpa only [Pi.mul_apply, heval p] using hpw
    obtain ⟨r, hr⟩ := himage
    refine ⟨e.symm r, ?_⟩
    rw [← e.symm_apply_apply (n : ZMod q), hr, map_mul]

/-- The powerset character expansion is exactly `2 ^ ω(q)` on unit square
classes modulo a squarefree modulus. -/
lemma sum_quadraticPrimeFactorProduct_eq_pow_iff_isSquare
    {q n : ℕ} (hq : Squarefree q) (hnq : n.Coprime q) :
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) =
        (2 : ℝ) ^ q.primeFactors.card ↔
      IsSquare (n : ZMod q) := by
  rw [sum_quadraticPrimeFactorProduct_powerset_eq_pow_iff hnq,
    isSquare_zmod_iff_local_of_squarefree hq]

/-- The value of the squarefree local-character expansion at one residue. -/
noncomputable def squarefreeSquareIndicator (q n : ℕ) : ℝ := by
  classical
  exact if IsSquare (n : ZMod q) then (2 : ℝ) ^ q.primeFactors.card else 0

lemma sum_quadraticPrimeFactorProduct_eq_squarefreeSquareIndicator
    {q n : ℕ} (hq : Squarefree q) (hnq : n.Coprime q) :
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) =
      squarefreeSquareIndicator q n := by
  classical
  rw [squarefreeSquareIndicator]
  by_cases hsquare : IsSquare (n : ZMod q)
  · rw [if_pos hsquare]
    exact (sum_quadraticPrimeFactorProduct_powerset_eq_pow_iff hnq).mpr
      ((isSquare_zmod_iff_local_of_squarefree hq).mp hsquare)
  · rw [if_neg hsquare]
    have hnotlocal : ¬∀ p ∈ q.primeFactors, IsSquare (n : ZMod p) := by
      rwa [← isSquare_zmod_iff_local_of_squarefree hq]
    push_neg at hnotlocal
    obtain ⟨p, hpq, hpnot⟩ := hnotlocal
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
    letI : Fact p.Prime := ⟨hp⟩
    apply sum_quadraticPrimeFactorProduct_powerset_eq_zero hpq
    exact (primeQuadraticCharReal_eq_neg_one_iff_not_isSquare hp).mpr hpnot

/-- The character product restricted to units modulo `q`. -/
noncomputable def restrictedQuadraticPrimeFactorProduct
    (q : ℕ) (s : Finset ℕ) (n : ℕ) : ℝ :=
  if n.Coprime q then quadraticPrimeFactorProduct s n else 0

/-- The value of the unit-square indicator after the CRT expansion. -/
noncomputable def unitSquareExpansionValue (q n : ℕ) : ℝ := by
  classical
  exact if n.Coprime q ∧ IsSquare (n : ZMod q) then
    (2 : ℝ) ^ q.primeFactors.card else 0

lemma sum_restrictedQuadraticPrimeFactorProduct_powerset
    {q n : ℕ} (hq : Squarefree q) :
    (∑ t ∈ q.primeFactors.powerset,
        restrictedQuadraticPrimeFactorProduct q t n) =
      unitSquareExpansionValue q n := by
  classical
  rw [unitSquareExpansionValue]
  by_cases hnq : n.Coprime q
  · simp only [restrictedQuadraticPrimeFactorProduct, if_pos hnq, hnq, true_and]
    rw [sum_quadraticPrimeFactorProduct_eq_squarefreeSquareIndicator hq hnq]
    rw [squarefreeSquareIndicator]
    by_cases hs : IsSquare (n : ZMod q)
    · rw [if_pos hs, if_pos ⟨hnq, hs⟩]
    · rw [if_neg hs, if_neg (fun h ↦ hs h.2)]
  · simp [restrictedQuadraticPrimeFactorProduct, hnq]

/-- If the principal term in the squarefree CRT character expansion dominates
the total absolute contribution of every nonempty character product, a unit
square occurs in the interval. -/
lemma exists_coprime_isSquare_zmod_in_interval_of_character_domination
    {q M H : ℕ} (hq : Squarefree q)
    (hdom :
      (∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct q ∅ (M + i)) >
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
          |∑ i ∈ Finset.range H,
            restrictedQuadraticPrimeFactorProduct q t (M + i)|) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime q ∧ IsSquare ((M + i : ℕ) : ZMod q) := by
  classical
  by_contra hnone
  push_neg at hnone
  let F : Finset ℕ → ℝ := fun t ↦
    ∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct q t (M + i)
  have htotal : (∑ t ∈ q.primeFactors.powerset, F t) = 0 := by
    calc
      (∑ t ∈ q.primeFactors.powerset, F t) =
          ∑ i ∈ Finset.range H,
            ∑ t ∈ q.primeFactors.powerset,
              restrictedQuadraticPrimeFactorProduct q t (M + i) := by
        simp only [F]
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [sum_restrictedQuadraticPrimeFactorProduct_powerset hq]
        rw [unitSquareExpansionValue,
          if_neg (fun h ↦ (hnone i hi h.1) h.2)]
  have herase :
      q.primeFactors.powerset.erase ∅ =
        q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hempty : (∅ : Finset ℕ) ∈ q.primeFactors.powerset := by simp
  have hsplit :
      F ∅ + ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t = 0 := by
    rw [← herase]
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ hempty).trans htotal
  have hFnonneg : 0 ≤ F ∅ := by
    dsimp only [F]
    apply Finset.sum_nonneg
    intro i hi
    by_cases hcop : (M + i).Coprime q
    · simp only [restrictedQuadraticPrimeFactorProduct, if_pos hcop,
        quadraticPrimeFactorProduct, Finset.prod_empty]
      norm_num
    · simp only [restrictedQuadraticPrimeFactorProduct, if_neg hcop]
      norm_num
  have hFabs :
      F ∅ ≤ |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| := by
    rw [show F ∅ = -(∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t) by
      linarith]
    exact neg_le_abs _
  have habs :
      |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| ≤
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle :
      F ∅ ≤ ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    hFabs.trans habs
  exact (not_lt_of_ge hle) hdom

/-- Uniform version of the squarefree character-domination criterion. -/
lemma exists_coprime_isSquare_zmod_in_interval_of_uniform_character_bound
    {q M H : ℕ} (hq : Squarefree q) {B : ℝ}
    (hprincipal :
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B <
        ∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct q ∅ (M + i))
    (hbound : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct q t (M + i)| ≤ B) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime q ∧ IsSquare ((M + i : ℕ) : ZMod q) := by
  apply exists_coprime_isSquare_zmod_in_interval_of_character_domination hq
  calc
    (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
        |∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct q t (M + i)|) ≤
        ∑ _t ∈ q.primeFactors.powerset.filter Finset.Nonempty, B := by
      apply Finset.sum_le_sum
      intro t ht
      exact hbound t ht
    _ = ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B := by
      simp
    _ < _ := hprincipal

/-- If a residue is not a square modulo a squarefree modulus, one local
quadratic character equals `-1`, so the entire CRT expansion vanishes. -/
lemma sum_quadraticPrimeFactorProduct_eq_zero_of_not_isSquare
    {q n : ℕ} (hq : Squarefree q) (hn : ¬IsSquare (n : ZMod q)) :
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) = 0 := by
  have hnotlocal : ¬∀ p ∈ q.primeFactors, IsSquare (n : ZMod p) := by
    rwa [← isSquare_zmod_iff_local_of_squarefree hq]
  push_neg at hnotlocal
  obtain ⟨p, hpq, hpnot⟩ := hnotlocal
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpq
  letI : Fact p.Prime := ⟨hp⟩
  apply sum_quadraticPrimeFactorProduct_powerset_eq_zero hpq
  exact (primeQuadraticCharReal_eq_neg_one_iff_not_isSquare hp).mpr hpnot

/-- Unrestricted squarefree character-domination criterion.  Unlike the unit
version, its principal term is exactly the interval length. -/
lemma exists_isSquare_zmod_in_interval_of_character_domination
    {q M H : ℕ} (hq : Squarefree q)
    (hdom :
      (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct t (M + i)|) < H) :
    ∃ i ∈ Finset.range H, IsSquare ((M + i : ℕ) : ZMod q) := by
  classical
  by_contra hnone
  push_neg at hnone
  let F : Finset ℕ → ℝ := fun t ↦
    ∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (M + i)
  have htotal : (∑ t ∈ q.primeFactors.powerset, F t) = 0 := by
    calc
      (∑ t ∈ q.primeFactors.powerset, F t) =
          ∑ i ∈ Finset.range H,
            ∑ t ∈ q.primeFactors.powerset,
              quadraticPrimeFactorProduct t (M + i) := by
        simp only [F]
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact sum_quadraticPrimeFactorProduct_eq_zero_of_not_isSquare
          hq (hnone i hi)
  have herase :
      q.primeFactors.powerset.erase ∅ =
        q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hempty : (∅ : Finset ℕ) ∈ q.primeFactors.powerset := by simp
  have hsplit :
      F ∅ + ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t = 0 := by
    rw [← herase, add_comm]
    exact (Finset.sum_erase_add _ _ hempty).trans htotal
  have hFempty : F ∅ = (H : ℝ) := by
    simp [F, quadraticPrimeFactorProduct]
  have hFabs :
      (H : ℝ) ≤ |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| := by
    rw [← hFempty]
    rw [show F ∅ = -(∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t) by
      linarith]
    exact neg_le_abs _
  have habs :
      |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| ≤
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle :
      (H : ℝ) ≤ ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    hFabs.trans habs
  exact (not_lt_of_ge hle) hdom

/-- Uniform nontrivial-character version of the unrestricted square-hitting
criterion. -/
lemma exists_isSquare_zmod_in_interval_of_uniform_character_bound
    {q M H : ℕ} (hq : Squarefree q) {B : ℝ}
    (hsmall :
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hbound : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (M + i)| ≤ B) :
    ∃ i ∈ Finset.range H, IsSquare ((M + i : ℕ) : ZMod q) := by
  apply exists_isSquare_zmod_in_interval_of_character_domination hq
  calc
    (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
        |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (M + i)|) ≤
        ∑ _t ∈ q.primeFactors.powerset.filter Finset.Nonempty, B := by
      apply Finset.sum_le_sum
      intro t ht
      exact hbound t ht
    _ = ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B := by
      simp
    _ < _ := hsmall

/-- Conductor attached to a set of local quadratic characters. -/
def primeSetModulus (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

lemma dvd_primeSetModulus {s : Finset ℕ} {p : ℕ} (hp : p ∈ s) :
    p ∣ primeSetModulus s := by
  exact Finset.dvd_prod_of_mem id hp

lemma primeQuadraticCharReal_mul {p a b : ℕ} [Fact p.Prime]
    (hp : p.Prime) :
    primeQuadraticCharReal p (a * b) =
      primeQuadraticCharReal p a * primeQuadraticCharReal p b := by
  rw [primeQuadraticCharReal_of_prime hp,
    primeQuadraticCharReal_of_prime hp,
    primeQuadraticCharReal_of_prime hp]
  simp [quadraticCharReal, map_mul]

/-- The subset character is completely multiplicative. -/
lemma quadraticPrimeFactorProduct_mul
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (a b : ℕ) :
    quadraticPrimeFactorProduct s (a * b) =
      quadraticPrimeFactorProduct s a * quadraticPrimeFactorProduct s b := by
  simp only [quadraticPrimeFactorProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact p.Prime := ⟨hs p hp⟩
  exact primeQuadraticCharReal_mul (hs p hp)

lemma abs_primeQuadraticCharReal_le_one
    {p n : ℕ} [Fact p.Prime] (hp : p.Prime) :
    |primeQuadraticCharReal p n| ≤ 1 := by
  rw [primeQuadraticCharReal_of_prime hp]
  exact abs_quadraticCharReal_le_one _

/-- Every value of a subset quadratic character has absolute value at most
one. -/
lemma abs_quadraticPrimeFactorProduct_le_one
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    |quadraticPrimeFactorProduct s n| ≤ 1 := by
  rw [quadraticPrimeFactorProduct, Finset.abs_prod]
  calc
    (∏ p ∈ s, |primeQuadraticCharReal p n|) ≤ ∏ _p ∈ s, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        letI : Fact p.Prime := ⟨hs p hp⟩
        exact abs_primeQuadraticCharReal_le_one (hs p hp)
    _ = 1 := by simp

lemma primeQuadraticCharReal_eq_of_modEq
    {p a b : ℕ} [Fact p.Prime] (hp : p.Prime) (hab : a ≡ b [MOD p]) :
    primeQuadraticCharReal p a = primeQuadraticCharReal p b := by
  rw [primeQuadraticCharReal_of_prime hp,
    primeQuadraticCharReal_of_prime hp]
  congr 1
  exact (ZMod.natCast_eq_natCast_iff a b p).mpr hab

/-- A subset character is periodic modulo the product of its primes. -/
lemma quadraticPrimeFactorProduct_eq_of_modEq
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {a b : ℕ}
    (hab : a ≡ b [MOD primeSetModulus s]) :
    quadraticPrimeFactorProduct s a = quadraticPrimeFactorProduct s b := by
  rw [quadraticPrimeFactorProduct, quadraticPrimeFactorProduct]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact p.Prime := ⟨hs p hp⟩
  apply primeQuadraticCharReal_eq_of_modEq (hs p hp)
  exact hab.of_dvd (dvd_primeSetModulus hp)

lemma primeSet_pairwise_coprime (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    Pairwise (fun p r : s ↦ Nat.Coprime (p : ℕ) (r : ℕ)) := by
  intro p r hpr
  have hp : (p : ℕ).Prime := hs p p.property
  have hr : (r : ℕ).Prime := hs r r.property
  exact hp.coprime_iff_not_dvd.mpr fun hdvd ↦
    hpr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd))

/-- The conductor of a product of distinct prime characters is squarefree. -/
lemma primeSetModulus_squarefree (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (primeSetModulus s) := by
  rw [primeSetModulus]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp
      ((hs p hp).coprime_iff_not_dvd.mpr fun hdvd ↦
        hpr ((Nat.prime_dvd_prime_iff_eq (hs p hp) (hs r hr)).mp hdvd))
  · intro p hp
    exact (hs p hp).squarefree

lemma primeFactors_primeSetModulus (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (primeSetModulus s).primeFactors = s := by
  exact Nat.primeFactors_prod hs

lemma primeSetModulus_pos (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : 0 < primeSetModulus s := by
  rw [primeSetModulus]
  exact Finset.prod_pos fun p hp ↦ (hs p hp).pos

/-- The Chinese-remainder equivalence for the conductor of a finite set of
distinct prime characters. -/
noncomputable def primeSetCRTEqv (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ZMod (primeSetModulus s) ≃+* (∀ p : s, ZMod (p : ℕ)) := by
  let hprod : primeSetModulus s = ∏ p : s, (p : ℕ) := by
    exact (Finset.prod_attach s (fun p : ℕ ↦ p)).symm
  exact (ZMod.ringEquivCongr hprod).trans
    (ZMod.prodEquivPi (fun p : s ↦ (p : ℕ))
      (primeSet_pairwise_coprime s hs))

lemma primeSetCRTEqv_natCast_apply (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (n : ℕ) (p : s) :
    primeSetCRTEqv s hs (n : ZMod (primeSetModulus s)) p =
      (n : ZMod (p : ℕ)) := by
  simp [primeSetCRTEqv]

/-- A local quadratic character whose primality proof is explicit, avoiding
a global family of typeclass instances indexed by a prime set. -/
noncomputable def localQuadraticCharReal (p : ℕ) (hp : p.Prime)
    (x : ZMod p) : ℝ := by
  letI : Fact p.Prime := ⟨hp⟩
  exact quadraticCharReal x

/-- The squarefree quadratic character on its natural CRT conductor. -/
noncomputable def quadraticPrimeSetCharReal (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (x : ZMod (primeSetModulus s)) : ℝ :=
  ∏ p : s, localQuadraticCharReal p (hs p p.property)
    (primeSetCRTEqv s hs x p)

lemma quadraticPrimeSetCharReal_natCast (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    quadraticPrimeSetCharReal s hs (n : ZMod (primeSetModulus s)) =
      quadraticPrimeFactorProduct s n := by
  rw [quadraticPrimeSetCharReal, quadraticPrimeFactorProduct]
  rw [← Finset.prod_attach s (fun p ↦ primeQuadraticCharReal p n)]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
  rw [localQuadraticCharReal, primeQuadraticCharReal_of_prime (hs p p.property),
    primeSetCRTEqv_natCast_apply]

lemma quadraticPrimeSetCharReal_prod (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) {ι : Type*} [Fintype ι]
    (f : ι → ZMod (primeSetModulus s)) :
    quadraticPrimeSetCharReal s hs (∏ i, f i) =
      ∏ i, quadraticPrimeSetCharReal s hs (f i) := by
  simp only [quadraticPrimeSetCharReal, map_prod]
  rw [Finset.prod_comm]
  apply Fintype.prod_congr
  intro p
  letI : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
  simpa [localQuadraticCharReal] using
    (quadraticCharReal_prod
      (F := ZMod (p : ℕ)) (ι := ι)
      (fun i ↦ primeSetCRTEqv s hs (f i) p))

/-! ### Fourier completion for squarefree quadratic characters -/

/-- An additive character turns a finite sum into a finite product. -/
lemma addChar_map_sum_eq_prod
    {A M ι : Type*} [AddCommMonoid A] [CommMonoid M] [Fintype ι]
    (ψ : AddChar A M) (f : ι → A) :
    ψ (∑ i, f i) = ∏ i, ψ (f i) := by
  classical
  let T : Finset ι := Finset.univ
  change ψ (∑ i ∈ T, f i) = ∏ i ∈ T, ψ (f i)
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]

/-- A nonempty product of odd local quadratic characters has mean zero over
its complete squarefree conductor. -/
lemma sum_quadraticPrimeSetCharReal_eq_zero
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (hodd : ∀ p ∈ s, p ≠ 2) (hne : s.Nonempty) :
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs x) = 0 := by
  let e := primeSetCRTEqv s hs
  calc
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs x) =
        ∑ y : (∀ p : s, ZMod (p : ℕ)),
          ∏ p : s, localQuadraticCharReal p (hs p p.property) (y p) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [quadraticPrimeSetCharReal]
      apply Fintype.prod_congr
      intro p
      congr 1
    _ = ∏ p : s, ∑ y : ZMod (p : ℕ),
        localQuadraticCharReal p (hs p p.property) y := by
      rw [Fintype.prod_sum]
    _ = 0 := by
      obtain ⟨p, hp⟩ := hne
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : s))
      let ps : s := ⟨p, hp⟩
      letI : Fact p.Prime := ⟨hs p hp⟩
      have hchar : ringChar (ZMod p) ≠ 2 :=
        (ZMod.ringChar_zmod_n p).substr (hodd p hp)
      have hz := quadraticChar_sum_zero (F := ZMod p) hchar
      have hz' := congrArg (fun z : ℤ ↦ (z : ℝ)) hz
      simpa [ps, localQuadraticCharReal, quadraticCharReal] using hz'

/-- Every local quadratic Gauss sum, including the zero-frequency sum, has
norm at most the square root of the prime modulus.  For a nontrivial additive
character this is the exact Gauss-sum identity; for the trivial character the
sum vanishes. -/
lemma norm_localQuadraticGaussSum_le_sqrt
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp₂ : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) :
    ‖∑ x : ZMod p, (localQuadraticCharReal p hp x : ℂ) * ψ x‖ ≤
      Real.sqrt p := by
  letI : Fact p.Prime := ⟨hp⟩
  let χ : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 :=
    (ZMod.ringChar_zmod_n p).substr hp₂
  have hχne : χ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
      (quadraticChar_ne_one hchar)
  have hχquad : χ.IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod p)).comp _
  have hsum :
      (∑ x : ZMod p, (localQuadraticCharReal p hp x : ℂ) * ψ x) =
        gaussSum χ ψ := by
    simp [localQuadraticCharReal, quadraticCharReal, gaussSum, χ]
  rw [hsum]
  by_cases hψ : ψ = 1
  · rw [hψ, gaussSum_one_right hχne]
    simpa using Real.sqrt_nonneg (p : ℝ)
  · have hψprim : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
    have hg := gaussSum_sq hχne hχquad hψprim
    have hχnorm : ‖χ (-1)‖ = 1 := by
      rcases quadraticChar_dichotomy (F := ZMod p)
          (neg_ne_zero.mpr one_ne_zero) with hpos | hneg
      · simp [χ, hpos]
      · simp [χ, hneg]
    have hnormsq : ‖gaussSum χ ψ‖ ^ 2 = (p : ℝ) := by
      have hnorm := congrArg norm hg
      simpa [norm_pow, norm_mul, hχnorm, ZMod.card] using hnorm
    have hsqrtsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
      Real.sq_sqrt (by positivity)
    nlinarith [norm_nonneg (gaussSum χ ψ), Real.sqrt_nonneg (p : ℝ)]

/-- Restriction of a global additive character to one CRT coordinate. -/
noncomputable def primeSetLocalAddChar
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (h : ZMod (primeSetModulus s)) (p : s) : AddChar (ZMod (p : ℕ)) ℂ :=
  (ZMod.stdAddChar.mulShift h).compAddMonoidHom
    ((primeSetCRTEqv s hs).symm.toAddEquiv.toAddMonoidHom.comp
      (AddMonoidHom.single (fun p : s ↦ ZMod (p : ℕ)) p))

/-- Under CRT, a global additive character is the product of its restrictions
to the prime coordinates. -/
lemma primeSet_addChar_eq_prod_local
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (h : ZMod (primeSetModulus s))
    (y : ∀ p : s, ZMod (p : ℕ)) :
    ZMod.stdAddChar (h * (primeSetCRTEqv s hs).symm y) =
      ∏ p : s, primeSetLocalAddChar s hs h p (y p) := by
  have hy : (∑ p : s, Pi.single p (y p)) = y := by
    funext p
    simp
  rw [← hy]
  simp [primeSetLocalAddChar, map_sum]
  rw [Finset.mul_sum]
  exact addChar_map_sum_eq_prod ZMod.stdAddChar
    (fun p : s ↦ h * (primeSetCRTEqv s hs).symm (Pi.single p (y p)))

/-- The complete Fourier twist of a squarefree quadratic character. -/
noncomputable def quadraticPrimeSetTwistedSum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)]
    (h : ZMod (primeSetModulus s)) : ℂ :=
  ∑ x : ZMod (primeSetModulus s),
    (quadraticPrimeSetCharReal s hs x : ℂ) * ZMod.stdAddChar (h * x)

/-- The complete squarefree twist factors as a product of local quadratic
Gauss sums. -/
lemma quadraticPrimeSetTwistedSum_eq_prod
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (h : ZMod (primeSetModulus s)) :
    quadraticPrimeSetTwistedSum s hs h =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        (localQuadraticCharReal p (hs p p.property) y : ℂ) *
          primeSetLocalAddChar s hs h p y := by
  let e := primeSetCRTEqv s hs
  calc
    quadraticPrimeSetTwistedSum s hs h =
        ∑ y : (∀ p : s, ZMod (p : ℕ)),
          ∏ p : s,
            ((localQuadraticCharReal p (hs p p.property) (y p) : ℂ) *
              primeSetLocalAddChar s hs h p (y p)) := by
      rw [quadraticPrimeSetTwistedSum, ← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro y hy
      have hadd := primeSet_addChar_eq_prod_local s hs h (e y)
      have hadd' : ZMod.stdAddChar (h * y) =
          ∏ p : s, primeSetLocalAddChar s hs h p (e y p) := by
        simpa [e] using hadd
      rw [hadd']
      have hchar : (quadraticPrimeSetCharReal s hs y : ℂ) =
          ∏ p : s,
            (localQuadraticCharReal p (hs p p.property) (e y p) : ℂ) := by
        simp [quadraticPrimeSetCharReal, e]
      rw [hchar]
      rw [← Finset.prod_mul_distrib]
      apply Fintype.prod_congr
      intro p
      simp [e]
    _ = _ := by rw [Fintype.prod_sum]

/-- Uniform square-root bound for every complete Fourier twist of a
squarefree quadratic character. -/
lemma norm_quadraticPrimeSetTwistedSum_le_sqrt
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (hodd : ∀ p ∈ s, p ≠ 2)
    (h : ZMod (primeSetModulus s)) :
    ‖quadraticPrimeSetTwistedSum s hs h‖ ≤
      Real.sqrt (primeSetModulus s) := by
  rw [quadraticPrimeSetTwistedSum_eq_prod]
  rw [norm_prod]
  calc
    (∏ p : s, ‖∑ y : ZMod (p : ℕ),
        (localQuadraticCharReal p (hs p p.property) y : ℂ) *
          primeSetLocalAddChar s hs h p y‖) ≤
        ∏ p : s, Real.sqrt (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact norm_localQuadraticGaussSum_le_sqrt
          (hs p p.property) (hodd p p.property)
          (primeSetLocalAddChar s hs h p)
    _ = Real.sqrt (primeSetModulus s) := by
      rw [← Real.sqrt_prod Finset.univ (by intro p hp; positivity)]
      congr 1
      simpa [primeSetModulus] using
        (Finset.prod_attach s (fun p : ℕ ↦ (p : ℝ)))

/-- A squarefree quadratic-character sum over the integer interval
`M < x ≤ M + m`. -/
noncomputable def quadraticPrimeSetShortCharSum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] (M : ℤ) (m : ℕ) : ℂ :=
  ∑ x ∈ Finset.Ioc M (M + m),
    (quadraticPrimeSetCharReal s hs (x : ZMod (primeSetModulus s)) : ℂ)

/-- Exact finite Fourier completion of a squarefree quadratic-character sum. -/
lemma quadraticPrimeSetShortCharSum_eq_complete
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] (M : ℤ) (m : ℕ) :
    quadraticPrimeSetShortCharSum s hs M m =
      (primeSetModulus s : ℂ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          Waring.Analytic.intervalFourierCoefficient M m h *
            quadraticPrimeSetTwistedSum s hs h := by
  unfold quadraticPrimeSetShortCharSum
    Waring.Analytic.intervalFourierCoefficient
  symm
  calc
    (primeSetModulus s : ℂ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          (∑ x ∈ Finset.Ioc M (M + m),
            ZMod.stdAddChar (-(h * (x : ZMod (primeSetModulus s))))) *
              quadraticPrimeSetTwistedSum s hs h =
      (primeSetModulus s : ℂ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          ∑ x ∈ Finset.Ioc M (M + m),
            ZMod.stdAddChar (-(h * (x : ZMod (primeSetModulus s)))) *
              quadraticPrimeSetTwistedSum s hs h := by
        simp_rw [Finset.sum_mul]
    _ = (primeSetModulus s : ℂ)⁻¹ *
        ∑ x ∈ Finset.Ioc M (M + m),
          ∑ h : ZMod (primeSetModulus s),
            ZMod.stdAddChar (-(h * (x : ZMod (primeSetModulus s)))) *
              quadraticPrimeSetTwistedSum s hs h := by
        congr 1
        rw [Finset.sum_comm]
    _ = (primeSetModulus s : ℂ)⁻¹ *
        ∑ x ∈ Finset.Ioc M (M + m),
          (primeSetModulus s : ℂ) *
            (quadraticPrimeSetCharReal s hs
              (x : ZMod (primeSetModulus s)) : ℂ) := by
        apply congrArg ((primeSetModulus s : ℂ)⁻¹ * ·)
        apply Finset.sum_congr rfl
        intro x hx
        exact Erdos387.AdditiveOrthogonality.sum_stdAddChar_neg_mul_fourierSum
          (fun y : ZMod (primeSetModulus s) ↦
            (quadraticPrimeSetCharReal s hs y : ℂ))
          (x : ZMod (primeSetModulus s))
    _ = ∑ x ∈ Finset.Ioc M (M + m),
        (quadraticPrimeSetCharReal s hs
          (x : ZMod (primeSetModulus s)) : ℂ) := by
        rw [← Finset.mul_sum]
        have hq : (primeSetModulus s : ℂ) ≠ 0 := by
          exact_mod_cast NeZero.ne (primeSetModulus s)
        rw [← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- Pólya--Vinogradov completion bound for one squarefree quadratic
character, with the explicit Fourier `L¹` loss used elsewhere in this
repository. -/
lemma norm_quadraticPrimeSetShortCharSum_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (hodd : ∀ p ∈ s, p ≠ 2) (M : ℤ) (m : ℕ)
    (hm : m ≤ primeSetModulus s) :
    ‖quadraticPrimeSetShortCharSum s hs M m‖ ≤
      (Real.log (primeSetModulus s) + 1) *
        Real.sqrt (primeSetModulus s) := by
  rw [quadraticPrimeSetShortCharSum_eq_complete]
  have hqReal : (primeSetModulus s : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne (primeSetModulus s)
  calc
    ‖(primeSetModulus s : ℂ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          Waring.Analytic.intervalFourierCoefficient M m h *
            quadraticPrimeSetTwistedSum s hs h‖ =
      (primeSetModulus s : ℝ)⁻¹ *
        ‖∑ h : ZMod (primeSetModulus s),
          Waring.Analytic.intervalFourierCoefficient M m h *
            quadraticPrimeSetTwistedSum s hs h‖ := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (primeSetModulus s : ℝ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          ‖Waring.Analytic.intervalFourierCoefficient M m h *
            quadraticPrimeSetTwistedSum s hs h‖ := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (primeSetModulus s : ℝ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
            ‖quadraticPrimeSetTwistedSum s hs h‖ := by
        simp only [norm_mul]
    _ ≤ (primeSetModulus s : ℝ)⁻¹ *
        ∑ h : ZMod (primeSetModulus s),
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
            Real.sqrt (primeSetModulus s) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_left
          (norm_quadraticPrimeSetTwistedSum_le_sqrt s hs hodd h)
          (norm_nonneg _)
    _ = (primeSetModulus s : ℝ)⁻¹ *
        (∑ h : ZMod (primeSetModulus s),
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖) *
            Real.sqrt (primeSetModulus s) := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ (primeSetModulus s : ℝ)⁻¹ *
        ((primeSetModulus s : ℝ) *
          (Real.log (primeSetModulus s) + 1)) *
            Real.sqrt (primeSetModulus s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (Waring.Analytic.sum_norm_intervalFourierCoefficient_le
            (primeSetModulus s) M m hm)
          (by positivity)
    _ = (Real.log (primeSetModulus s) + 1) *
        Real.sqrt (primeSetModulus s) := by
        field_simp

/-- The zero-based natural interval is the integer interval beginning at
`M - 1` used by the Fourier-coefficient API. -/
lemma sum_range_quadraticPrimeFactorProduct_eq_short
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] (M H : ℕ) :
    (∑ i ∈ Finset.range H, (quadraticPrimeFactorProduct s (M + i) : ℂ)) =
      quadraticPrimeSetShortCharSum s hs ((M : ℤ) - 1) H := by
  unfold quadraticPrimeSetShortCharSum
  apply Finset.sum_bij (fun (i : ℕ) _hi ↦ ((M + i : ℕ) : ℤ))
  · intro i hi
    rw [Finset.mem_Ioc]
    have hiH : i < H := Finset.mem_range.mp hi
    constructor <;> omega
  · intro i hi j hj hij
    exact Nat.add_left_cancel (Int.ofNat_inj.mp hij)
  · intro x hx
    rw [Finset.mem_Ioc] at hx
    have hMx : (M : ℤ) ≤ x := by omega
    let i : ℕ := (x - M).toNat
    have hdiff : (x - M).toNat = x.toNat - M := by omega
    have hiH : i < H := by
      dsimp only [i]
      omega
    refine ⟨i, Finset.mem_range.mpr hiH, ?_⟩
    dsimp only [i]
    omega
  · intro i hi
    simpa only [Int.cast_natCast] using
      congrArg (fun r : ℝ ↦ (r : ℂ))
        (quadraticPrimeSetCharReal_natCast s hs (M + i)).symm

/-- Explicit completion estimate for the natural interval form of a
squarefree quadratic-character sum. -/
lemma abs_sum_quadraticPrimeFactorProduct_le_completion
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) (M H : ℕ)
    (hH : H ≤ primeSetModulus s) :
    |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)| ≤
      (Real.log (primeSetModulus s) + 1) *
        Real.sqrt (primeSetModulus s) := by
  letI : NeZero (primeSetModulus s) :=
    ⟨(primeSetModulus_pos s hs).ne'⟩
  letI : (p : s) → NeZero (p : ℕ) := fun p ↦
    ⟨(hs p p.property).ne_zero⟩
  have hbound := norm_quadraticPrimeSetShortCharSum_le
    s hs hodd ((M : ℤ) - 1) H hH
  rw [← sum_range_quadraticPrimeFactorProduct_eq_short] at hbound
  have hcast :
      (∑ i ∈ Finset.range H,
        (quadraticPrimeFactorProduct s (M + i) : ℂ)) =
      ((∑ i ∈ Finset.range H,
        quadraticPrimeFactorProduct s (M + i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast] at hbound
  rw [Complex.norm_real] at hbound
  exact hbound

/-- The nonzero Fourier mass of an interval is bounded independently of its
length.  This is the long-interval form of the standard geometric-series
estimate. -/
lemma sum_norm_intervalFourierCoefficient_erase_zero_le
    (q : ℕ) [NeZero q] (M : ℤ) (m : ℕ) :
    (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖) ≤
      (q : ℝ) * Real.log q := by
  calc
    (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        ‖Waring.Analytic.intervalFourierCoefficient M m h‖) ≤
      ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        Waring.Analytic.leastResidueWeight q h := by
          apply Finset.sum_le_sum
          intro h hh
          exact Waring.Analytic.norm_intervalFourierCoefficient_le_leastResidue
            M m (Finset.mem_erase.mp hh).1
    _ ≤ ∑ h : ZMod q, Waring.Analytic.leastResidueWeight q h := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _)
          intro h hh hnot
          unfold Waring.Analytic.leastResidueWeight
          positivity
    _ ≤ (q : ℝ) * Real.log q :=
      Waring.Analytic.sum_leastResidueWeight_le_log q

/-- The zero Fourier twist vanishes for a nonempty squarefree quadratic
character. -/
lemma quadraticPrimeSetTwistedSum_zero
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (hodd : ∀ p ∈ s, p ≠ 2) (hne : s.Nonempty) :
    quadraticPrimeSetTwistedSum s hs 0 = 0 := by
  have hz := sum_quadraticPrimeSetCharReal_eq_zero s hs hodd hne
  have hz' := congrArg (fun r : ℝ ↦ (r : ℂ)) hz
  simp [quadraticPrimeSetTwistedSum]
  simpa using hz'

/-- Long-interval Pólya--Vinogradov completion.  Complete periods disappear
because the zero Fourier mode vanishes, so the bound is independent of the
interval length. -/
lemma norm_quadraticPrimeSetShortCharSum_le_long
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (hodd : ∀ p ∈ s, p ≠ 2) (hne : s.Nonempty)
    (M : ℤ) (m : ℕ) :
    ‖quadraticPrimeSetShortCharSum s hs M m‖ ≤
      Real.log (primeSetModulus s) * Real.sqrt (primeSetModulus s) := by
  rw [quadraticPrimeSetShortCharSum_eq_complete]
  let q := primeSetModulus s
  let F : ZMod q → ℂ := fun h ↦
    Waring.Analytic.intervalFourierCoefficient M m h *
      quadraticPrimeSetTwistedSum s hs h
  have hzero : F 0 = 0 := by
    simp [F, quadraticPrimeSetTwistedSum_zero s hs hodd hne]
  have hmem : (0 : ZMod q) ∈ (Finset.univ : Finset (ZMod q)) := by simp
  have hsplit : (∑ h : ZMod q, F h) =
      ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, F h := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (ZMod q)) F hmem,
      hzero, add_zero]
  rw [show (∑ h : ZMod q,
      Waring.Analytic.intervalFourierCoefficient M m h *
        quadraticPrimeSetTwistedSum s hs h) = ∑ h : ZMod q, F h by rfl]
  rw [hsplit]
  calc
    ‖(q : ℂ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, F h‖ =
      (q : ℝ)⁻¹ *
        ‖∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, F h‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (q : ℝ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, ‖F h‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (q : ℝ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
            ‖quadraticPrimeSetTwistedSum s hs h‖ := by
          simp only [F, norm_mul]
    _ ≤ (q : ℝ)⁻¹ *
        ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖ *
            Real.sqrt q := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro h hh
          exact mul_le_mul_of_nonneg_left
            (norm_quadraticPrimeSetTwistedSum_le_sqrt s hs hodd h)
            (norm_nonneg _)
    _ = (q : ℝ)⁻¹ *
        (∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖) *
            Real.sqrt q := by
          rw [← Finset.sum_mul]
          ring
    _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * Real.log q) * Real.sqrt q := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (sum_norm_intervalFourierCoefficient_erase_zero_le q M m)
            (by positivity)
    _ = Real.log q * Real.sqrt q := by
          have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
          field_simp

/-- Arbitrary-length natural-interval completion estimate for a nonempty
squarefree quadratic character. -/
lemma abs_sum_quadraticPrimeFactorProduct_le_completion_long
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) (hne : s.Nonempty) (M H : ℕ) :
    |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)| ≤
      Real.log (primeSetModulus s) * Real.sqrt (primeSetModulus s) := by
  letI : NeZero (primeSetModulus s) :=
    ⟨(primeSetModulus_pos s hs).ne'⟩
  letI : (p : s) → NeZero (p : ℕ) := fun p ↦
    ⟨(hs p p.property).ne_zero⟩
  have hbound := norm_quadraticPrimeSetShortCharSum_le_long
    s hs hodd hne ((M : ℤ) - 1) H
  rw [← sum_range_quadraticPrimeFactorProduct_eq_short] at hbound
  have hcast :
      (∑ i ∈ Finset.range H,
        (quadraticPrimeFactorProduct s (M + i) : ℂ)) =
      ((∑ i ∈ Finset.range H,
        quadraticPrimeFactorProduct s (M + i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real] at hbound
  exact hbound

/-- A complete four-shift correlation of a squarefree quadratic character is
the product of its local prime correlations. -/
lemma quadraticPrimeSet_complete_correlation_eq_prod
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (v : Fin 4 → ZMod (primeSetModulus s)) :
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs
          (∏ i : Fin 4, (x + v i))) =
      ∏ p : s, ∑ y : ZMod (p : ℕ),
        localQuadraticCharReal p (hs p p.property)
          (∏ i : Fin 4,
            (y + primeSetCRTEqv s hs (v i) p)) := by
  let e := primeSetCRTEqv s hs
  calc
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs
          (∏ i : Fin 4, (x + v i))) =
        ∑ y : (∀ p : s, ZMod (p : ℕ)),
          ∏ p : s, localQuadraticCharReal p (hs p p.property)
            (∏ i : Fin 4,
              (y p + primeSetCRTEqv s hs (v i) p)) := by
      rw [← e.toEquiv.sum_comp]
      apply Finset.sum_congr rfl
      intro x hx
      rw [quadraticPrimeSetCharReal]
      apply Fintype.prod_congr
      intro p
      congr 1
      simp [e]
    _ = ∏ p : s, ∑ y : ZMod (p : ℕ),
        localQuadraticCharReal p (hs p p.property)
          (∏ i : Fin 4,
            (y + primeSetCRTEqv s hs (v i) p)) := by
      rw [Fintype.prod_sum]

/-- Absolute-value form of the quartic Hasse estimate. -/
lemma abs_quadraticChar_four_correlation_le_three_sqrt_of_hasse
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F)
    (hhasse : |(quarticAffinePointCount v : ℝ) + 2 -
        ((Fintype.card F : ℝ) + 1)| ≤ 2 * Real.sqrt (Fintype.card F)) :
    |∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))| ≤
      3 * Real.sqrt (Fintype.card F) := by
  rw [quarticAffinePointCount_eq_card_add_correlation hF v] at hhasse
  have hhasse' :
      |(∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) + 1| ≤
        2 * Real.sqrt (Fintype.card F) := by
    convert hhasse using 1 <;> ring
  have hsqrt : 1 ≤ Real.sqrt (Fintype.card F) := by
    have hcard : (1 : ℝ) ≤ Fintype.card F := by
      exact_mod_cast Fintype.card_pos
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
    have hsqrt_sq : Real.sqrt (Fintype.card F) ^ 2 = Fintype.card F :=
      Real.sq_sqrt (by positivity)
    nlinarith
  calc
    |∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))| =
        |((∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) + 1) - 1| := by
      congr 1
      ring
    _ ≤ |(∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))) + 1| + |(1 : ℝ)| :=
      abs_sub _ _
    _ ≤ 2 * Real.sqrt (Fintype.card F) + 1 := by
      exact add_le_add hhasse' (by norm_num)
    _ ≤ 3 * Real.sqrt (Fintype.card F) := by linarith

/-- A singular off-diagonal quartic correlation is uniformly bounded.  After
removing its repeated square factor it differs from the exact two-shift
correlation `-1` at at most the single root of that factor. -/
lemma abs_quadraticChar_four_correlation_le_two_of_repeated
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b c : F) (hbc : b ≠ c) :
    |∑ x : F, quadraticCharReal
      ((x + a) ^ 2 * (x + b) * (x + c))| ≤ 2 := by
  let C : ℝ := ∑ x : F, quadraticCharReal
    ((x + a) ^ 2 * (x + b) * (x + c))
  let P : ℝ := ∑ x : F, quadraticCharReal ((x + b) * (x + c))
  have hpair : P = -1 := by
    simpa only [P, sub_neg_eq_add] using
      quadraticCharReal_pair_correlation hF (-b) (-c) (by simpa using hbc)
  have hpoint (x : F) :
      |quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) -
        quadraticCharReal ((x + b) * (x + c))| ≤
          if x + a = 0 then 1 else 0 := by
    by_cases hx : x + a = 0
    · rw [if_pos hx]
      have hleft :
          quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) = 0 := by
        rw [hx]
        simp [quadraticCharReal]
      rw [hleft, zero_sub, abs_neg]
      exact abs_quadraticCharReal_le_one _
    · rw [if_neg hx]
      have hsq : quadraticChar F ((x + a) ^ 2) = 1 :=
        quadraticChar_sq_one' hx
      have heq :
          quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) =
            quadraticCharReal ((x + b) * (x + c)) := by
        simp [quadraticCharReal, map_mul, hsq]
      rw [heq, sub_self, abs_zero]
  have hdiff : |C - P| ≤ 1 := by
    dsimp only [C, P]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ x : F,
          (quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) -
            quadraticCharReal ((x + b) * (x + c)))| ≤
          ∑ x : F,
            |quadraticCharReal ((x + a) ^ 2 * (x + b) * (x + c)) -
              quadraticCharReal ((x + b) * (x + c))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : F, if x + a = 0 then 1 else 0 := by
        exact Finset.sum_le_sum fun x hx ↦ hpoint x
      _ = 1 := by simp [add_eq_zero_iff_eq_neg]
  have hdecomp : C = (C - P) + P := by ring
  change |C| ≤ 2
  calc
    |C| = |(C - P) + P| := congrArg abs hdecomp
    _ ≤ |C - P| + |P| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add hdiff (by rw [hpair]; norm_num)
    _ = 2 := by norm_num

lemma abs_quadraticChar_four_correlation_le_two_of_singular_offDiagonal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : Fin 4 → F)
    (hdiag : ¬burgessDiagonal v) (hdist : ¬burgessDistinct v) :
    |∑ x : F, quadraticCharReal (∏ i : Fin 4, (x + v i))| ≤ 2 := by
  let a := v 0
  let b := v 1
  let c := v 2
  let d := v 3
  have hform (x : F) :
      (∏ i : Fin 4, (x + v i)) =
        (x + a) * (x + b) * (x + c) * (x + d) := by
    simp [a, b, c, d, Fin.prod_univ_four]
  simp_rw [hform]
  by_cases hab : a = b
  · have hcd : c ≠ d := by
      intro h
      apply hdiag
      exact Or.inl ⟨by simpa [a, b] using hab, by simpa [c, d] using h⟩
    subst b
    have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
      hF a c d hcd
    simpa only [← hab, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h
      apply hdiag
      exact Or.inr <| Or.inl
        ⟨by simpa [a, c] using hac, by simpa [b, d] using h⟩
    subst c
    have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
      hF a b d hbd
    simpa only [← hac, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases had : a = d
  · have hbc : b ≠ c := by
      intro h
      apply hdiag
      exact Or.inr <| Or.inr
        ⟨by simpa [a, d] using had, by simpa [b, c] using h⟩
    subst d
    have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
      hF a b c hbc
    simpa only [← had, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hbc : b = c
  · have had' : a ≠ d := had
    subst c
    have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
      hF b a d had'
    simpa only [← hbc, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  by_cases hbd : b = d
  · have hac' : a ≠ c := hac
    subst d
    have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
      hF b a c hac'
    simpa only [← hbd, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep
  have hcd : c = d := by
    by_contra hcd
    apply hdist
    exact ⟨by simpa [a, b] using hab, by simpa [a, c] using hac,
      by simpa [a, d] using had, by simpa [b, c] using hbc,
      by simpa [b, d] using hbd, by simpa [c, d] using hcd⟩
  have hab' : a ≠ b := hab
  subst d
  have hrep := abs_quadraticChar_four_correlation_le_two_of_repeated
    hF c a b hab'
  simpa only [← hcd, pow_two, mul_comm, mul_left_comm, mul_assoc] using hrep

/-- A local quartic correlation bound.  Only the genuinely diagonal tuples
need the trivial bound; Hasse or the repeated-factor estimate gives a square
root saving for every off-diagonal tuple. -/
noncomputable def localQuadraticQuarticBound
    (p : ℕ) (v : Fin 4 → ZMod p) : ℝ := by
  classical
  exact if p = 2 then p else
    if burgessDiagonal v then p else 3 * Real.sqrt p

lemma abs_localQuadraticChar_four_correlation_le
    {p : ℕ} [NeZero p] (hp : p.Prime) (v : Fin 4 → ZMod p) :
    |∑ x : ZMod p, localQuadraticCharReal p hp
        (∏ i : Fin 4, (x + v i))| ≤
      localQuadraticQuarticBound p v := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rw [localQuadraticQuarticBound]
  have htrivial :
      |∑ x : ZMod p, localQuadraticCharReal p hp
          (∏ i : Fin 4, (x + v i))| ≤ p := by
    calc
      |∑ x : ZMod p, localQuadraticCharReal p hp
          (∏ i : Fin 4, (x + v i))| ≤
          ∑ x : ZMod p, |localQuadraticCharReal p hp
            (∏ i : Fin 4, (x + v i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : ZMod p, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [localQuadraticCharReal] using
          (abs_quadraticCharReal_le_one
            (∏ i : Fin 4, (x + v i)))
      _ = p := by simp [ZMod.card]
  by_cases hp₂ : p = 2
  · rw [if_pos hp₂]
    exact htrivial
  rw [if_neg hp₂]
  have hchar : ringChar (ZMod p) ≠ 2 :=
    (ZMod.ringChar_zmod_n p).substr hp₂
  by_cases hdiag : burgessDiagonal v
  · rw [if_pos hdiag]
    exact htrivial
  rw [if_neg hdiag]
  by_cases hv : burgessDistinct v
  · simpa [localQuadraticCharReal, ZMod.card] using
      abs_quadraticChar_four_correlation_le_three_sqrt_of_hasse
        (F := ZMod p) hchar v
        (quarticAffinePointCount_hasse
          (F := ZMod p) hchar v hv)
  · have hsing :=
      abs_quadraticChar_four_correlation_le_two_of_singular_offDiagonal
        (F := ZMod p) hchar v hdiag hv
    have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      have hsqrt_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
      have hsqrt_sq : Real.sqrt p ^ 2 = (p : ℝ) :=
        Real.sq_sqrt (by positivity)
      nlinarith
    simpa [localQuadraticCharReal, ZMod.card] using
      hsing.trans (by nlinarith : (2 : ℝ) ≤ 3 * Real.sqrt p)

/-- Product of the local quartic bounds for a squarefree character. -/
noncomputable def quadraticPrimeSetQuarticBound
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (v : Fin 4 → ZMod (primeSetModulus s)) : ℝ :=
  ∏ p : s, localQuadraticQuarticBound p
    (fun i ↦ primeSetCRTEqv s hs (v i) p)

lemma abs_quadraticPrimeSet_complete_correlation_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (v : Fin 4 → ZMod (primeSetModulus s)) :
    |∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs
          (∏ i : Fin 4, (x + v i))| ≤
      quadraticPrimeSetQuarticBound s hs v := by
  rw [quadraticPrimeSet_complete_correlation_eq_prod s hs v,
    Finset.abs_prod, quadraticPrimeSetQuarticBound]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    exact abs_localQuadraticChar_four_correlation_le
      (hs p p.property) (fun i ↦ primeSetCRTEqv s hs (v i) p)

/-- A translated sum of the squarefree product character. -/
noncomputable def quadraticPrimeSetShiftSum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (V : Finset (ZMod (primeSetModulus s)))
    (x : ZMod (primeSetModulus s)) : ℝ :=
  ∑ v ∈ V, quadraticPrimeSetCharReal s hs (x + v)

lemma quadraticPrimeSetShiftSum_fourth_moment_expansion
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)]
    (V : Finset (ZMod (primeSetModulus s))) :
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetShiftSum s hs V x ^ 4) =
      ∑ v : Fin 4 → V, ∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetCharReal s hs
          (∏ i : Fin 4, (x + (v i : ZMod (primeSetModulus s)))) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [quadraticPrimeSetShiftSum, ← Finset.sum_attach,
    Finset.attach_eq_univ, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro v hv
  exact (quadraticPrimeSetCharReal_prod s hs
    (fun i : Fin 4 ↦ x + (v i : ZMod (primeSetModulus s)))).symm

/-- Exact squarefree-conductor fourth-moment bound.  The remaining right-hand
side records precisely which shift tuples collide at which prime factors. -/
lemma quadraticPrimeSetShiftSum_fourth_moment_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)] [(p : s) → NeZero (p : ℕ)]
    (V : Finset (ZMod (primeSetModulus s))) :
    (∑ x : ZMod (primeSetModulus s),
        quadraticPrimeSetShiftSum s hs V x ^ 4) ≤
      ∑ v : Fin 4 → V,
        quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s))) := by
  rw [quadraticPrimeSetShiftSum_fourth_moment_expansion]
  apply Finset.sum_le_sum
  intro v hv
  exact (le_abs_self _).trans
    (abs_quadraticPrimeSet_complete_correlation_le s hs
      (fun i ↦ (v i : ZMod (primeSetModulus s))))

/-- Reduction modulo one prime factor is injective on a positive interval
shorter than that prime. -/
lemma primeSetCRTEqv_apply_injective_on_zmodPositive
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (p : s)
    {V : ℕ} (hVp : V < p) :
    Set.InjOn (fun x : ZMod (primeSetModulus s) ↦
      primeSetCRTEqv s hs x p)
      (zmodPositiveInterval (primeSetModulus s) V) := by
  intro x hx y hy hxy
  change x ∈ zmodPositiveInterval (primeSetModulus s) V at hx
  change y ∈ zmodPositiveInterval (primeSetModulus s) V at hy
  rw [zmodPositiveInterval, Finset.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  change primeSetCRTEqv s hs
      (a : ZMod (primeSetModulus s)) p =
    primeSetCRTEqv s hs (b : ZMod (primeSetModulus s)) p at hxy
  rw [primeSetCRTEqv_natCast_apply,
    primeSetCRTEqv_natCast_apply] at hxy
  have hab : a = b := eq_of_zmod_positive_cast_eq ha hb hVp hxy
  rw [hab]

/-- On a sufficiently short interval, diagonal collision is preserved and
reflected by every CRT projection. -/
lemma burgessDiagonal_primeSetCRTEqv_iff
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (p : s)
    {V : ℕ} (hVp : V < p)
    (v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V)) :
    burgessDiagonal
        (fun i ↦ primeSetCRTEqv s hs
          (v i : ZMod (primeSetModulus s)) p) ↔
      burgessDiagonal v := by
  let f : ↥(zmodPositiveInterval (primeSetModulus s) V) → ZMod (p : ℕ) :=
    fun x ↦ primeSetCRTEqv s hs (x : ZMod (primeSetModulus s)) p
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext
      (primeSetCRTEqv_apply_injective_on_zmodPositive s hs p hVp
        x.property y.property hxy)
  change burgessDiagonal (fun i ↦ f (v i)) ↔ burgessDiagonal v
  simp only [burgessDiagonal, hf.eq_iff]

lemma prod_sqrt_nat_eq_sqrt_prod (s : Finset ℕ) :
    (∏ n ∈ s, Real.sqrt n) = Real.sqrt (∏ n ∈ s, n) := by
  rw [← Real.sqrt_prod s (fun n hn ↦ Nat.cast_nonneg n)]

/-- If every prime factor is odd and exceeds the shift length, the CRT
product bound has just one global diagonal case. -/
lemma quadraticPrimeSetQuarticBound_eq_ite_of_small_shifts
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) {V : ℕ}
    (hVp : ∀ p ∈ s, V < p)
    (v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V)) :
    quadraticPrimeSetQuarticBound s hs
        (fun i ↦ (v i : ZMod (primeSetModulus s))) =
      if burgessDiagonal v then (primeSetModulus s : ℝ) else
        (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) := by
  classical
  rw [quadraticPrimeSetQuarticBound]
  by_cases hdiag : burgessDiagonal v
  · rw [if_pos hdiag]
    have hlocal (p : s) :
        localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p) = (p : ℝ) := by
      rw [localQuadraticQuarticBound, if_neg (hodd p p.property),
        if_pos ((burgessDiagonal_primeSetCRTEqv_iff
          s hs p (hVp p p.property) v).mpr hdiag)]
    calc
      (∏ p : s, localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p)) =
          ∏ p : s, ((p : ℕ) : ℝ) := by
        apply Fintype.prod_congr
        exact hlocal
      _ = (primeSetModulus s : ℝ) := by
        rw [primeSetModulus, Nat.cast_prod]
        exact Finset.prod_attach s (fun p : ℕ ↦ (p : ℝ))
  · rw [if_neg hdiag]
    have hlocal (p : s) :
        localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p) =
          3 * Real.sqrt (p : ℕ) := by
      rw [localQuadraticQuarticBound, if_neg (hodd p p.property),
        if_neg (fun hp ↦ hdiag ((burgessDiagonal_primeSetCRTEqv_iff
          s hs p (hVp p p.property) v).mp hp))]
    calc
      (∏ p : s, localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p)) =
          ∏ p : s, (3 * Real.sqrt (p : ℕ)) := by
        apply Fintype.prod_congr
        exact hlocal
      _ = (∏ _p : s, (3 : ℝ)) *
          ∏ p : s, Real.sqrt (p : ℕ) := by
        rw [← Finset.prod_mul_distrib]
      _ = (3 : ℝ) ^ s.card *
          Real.sqrt (primeSetModulus s) := by
        rw [show (∏ _p : s, (3 : ℝ)) = (3 : ℝ) ^ s.card by simp]
        rw [show (∏ p : s, Real.sqrt (p : ℕ)) =
            ∏ p ∈ s, Real.sqrt p by
          exact Finset.prod_attach s (fun p : ℕ ↦ Real.sqrt p)]
        rw [prod_sqrt_nat_eq_sqrt_prod, primeSetModulus, Nat.cast_prod]

/-- Counting the three possible pairings bounds the contribution of all
global diagonal four-tuples. -/
lemma sum_ite_burgessDiagonal_le
    {W : Type*} [Fintype W] [DecidableEq W]
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑ v : Fin 4 → W, if burgessDiagonal v then A else B) ≤
      3 * (Fintype.card W : ℝ) ^ 2 * A +
        (Fintype.card W : ℝ) ^ 4 * B := by
  classical
  let D : Finset (Fin 4 → W) := Finset.univ.filter burgessDiagonal
  have hpoint (v : Fin 4 → W) :
      (if burgessDiagonal v then A else B) ≤
        (if burgessDiagonal v then A else 0) + B := by
    by_cases hv : burgessDiagonal v
    · simp only [hv, if_true]
      exact le_add_of_nonneg_right hB
    · simp [hv]
  calc
    (∑ v : Fin 4 → W, if burgessDiagonal v then A else B) ≤
        ∑ v : Fin 4 → W,
          ((if burgessDiagonal v then A else 0) + B) := by
      exact Finset.sum_le_sum fun v _ ↦ hpoint v
    _ = (D.card : ℝ) * A + Fintype.card (Fin 4 → W) * B := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      change (∑ v : Fin 4 → W,
          if burgessDiagonal v then A else 0) +
          Fintype.card (Fin 4 → W) * B = _
      rw [← Finset.sum_filter]
      simp [D]
    _ ≤ (3 * Fintype.card W ^ 2 : ℕ) * A +
        Fintype.card (Fin 4 → W) * B := by
      gcongr
      simpa [D] using card_burgessDiagonal_le W
    _ = 3 * (Fintype.card W : ℝ) ^ 2 * A +
        (Fintype.card W : ℝ) ^ 4 * B := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]

/-- Explicit composite quartic moment cost for shifts shorter than every
prime factor. -/
lemma quadraticPrimeSetQuarticBound_sum_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) {V : ℕ}
    (hVp : ∀ p ∈ s, V < p)
    (hVq : V < primeSetModulus s) :
    (∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
        quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s)))) ≤
      3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
        (V : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s)) := by
  classical
  calc
    (∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
        quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s)))) =
        ∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
          if burgessDiagonal v then (primeSetModulus s : ℝ) else
            (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact quadraticPrimeSetQuarticBound_eq_ite_of_small_shifts
        s hs hodd hVp v
    _ ≤ 3 *
          (Fintype.card
            ↥(zmodPositiveInterval (primeSetModulus s) V) : ℝ) ^ 2 *
            (primeSetModulus s : ℝ) +
        (Fintype.card
            ↥(zmodPositiveInterval (primeSetModulus s) V) : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s)) := by
      apply sum_ite_burgessDiagonal_le
      · positivity
      · positivity
    _ = 3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
        (V : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s)) := by
      rw [Fintype.card_coe, zmodPositiveInterval_card hVq]

/-! ### General composite Burgess fourth moment

The printed short-shift estimate in Nguyen--Vu is too strong for arbitrary
squarefree composite conductors.  Their Remark 7.3 permits Burgess's method.
The following lemmas implement that repair: primes at which a globally
non-diagonal quadruple becomes locally diagonal are partitioned among the
three pairings, and the product belonging to each pairing is at most the
shift length. -/

def generalBurgessPairingMod (j : Fin 3) (p : ℕ) (n : Fin 4 → ℕ) : Prop :=
  match j with
  | 0 => n 0 ≡ n 1 [MOD p] ∧ n 2 ≡ n 3 [MOD p]
  | 1 => n 0 ≡ n 2 [MOD p] ∧ n 1 ≡ n 3 [MOD p]
  | 2 => n 0 ≡ n 3 [MOD p] ∧ n 1 ≡ n 2 [MOD p]

lemma general_burgessDiagonal_natCast_iff_exists_pairing
    (p : ℕ) (n : Fin 4 → ℕ) :
    burgessDiagonal (fun i ↦ (n i : ZMod p)) ↔
      ∃ j : Fin 3, generalBurgessPairingMod j p n := by
  simp only [burgessDiagonal, generalBurgessPairingMod,
    ZMod.natCast_eq_natCast_iff]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨j, hj⟩
    fin_cases j <;> simp_all

noncomputable def generalBurgessPairingChoice
    (p : ℕ) (n : Fin 4 → ℕ) : Fin 3 := by
  classical
  exact if h : ∃ j : Fin 3, generalBurgessPairingMod j p n then
    Classical.choose h else 0

lemma general_pairingChoice_spec
    {p : ℕ} {n : Fin 4 → ℕ}
    (hdiag : burgessDiagonal (fun i ↦ (n i : ZMod p))) :
    generalBurgessPairingMod (generalBurgessPairingChoice p n) p n := by
  rw [general_burgessDiagonal_natCast_iff_exists_pairing] at hdiag
  rw [generalBurgessPairingChoice, dif_pos hdiag]
  exact Classical.choose_spec hdiag

lemma general_prod_dvd_iff_all_prime_dvd
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℕ) :
    (∏ p ∈ t, p) ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        have hp : p.Prime := ht p (Finset.mem_insert_self p t)
        have hcop : p.Coprime (∏ r ∈ t, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hp (ht r (Finset.mem_insert_of_mem hr))).mpr
            (Ne.symm (ne_of_mem_of_not_mem hr hpt))
        exact hcop.mul_dvd_of_dvd_of_dvd
          (h p (Finset.mem_insert_self p t))
          (ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
            (fun r hr ↦ h r (Finset.mem_insert_of_mem hr)))

lemma general_prime_product_le_of_modEq_of_ne
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime)
    {a b V : ℕ} (ha : a ∈ Finset.Icc 1 V) (hb : b ∈ Finset.Icc 1 V)
    (hne : a ≠ b) (hmod : ∀ p ∈ t, a ≡ b [MOD p]) :
    ∏ p ∈ t, p ≤ V := by
  have hdiv : (∏ p ∈ t, p) ∣ Nat.dist a b := by
    rw [general_prod_dvd_iff_all_prime_dvd t ht]
    intro p hp
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.modEq_iff_dvd' hab).mp (hmod p hp)
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.modEq_iff_dvd' hba).mp (hmod p hp).symm
  have hdistpos : 0 < Nat.dist a b := by
    exact Nat.dist_pos_of_ne hne
  have hdist : Nat.dist a b < V := by
    have ha1 := (Finset.mem_Icc.mp ha).1
    have haV := (Finset.mem_Icc.mp ha).2
    have hb1 := (Finset.mem_Icc.mp hb).1
    have hbV := (Finset.mem_Icc.mp hb).2
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]
      omega
  exact (Nat.le_of_dvd hdistpos hdiv).trans hdist.le

lemma general_localDiagonal_prime_product_le_cube
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime)
    {V : ℕ} (hV : 0 < V) (n : Fin 4 → ℕ)
    (hn : ∀ i, n i ∈ Finset.Icc 1 V)
    (hnotdiag : ¬burgessDiagonal n)
    (hdiag : ∀ p ∈ t,
      burgessDiagonal (fun i ↦ (n i : ZMod p))) :
    ∏ p ∈ t, p ≤ V ^ 3 := by
  classical
  let c : ℕ → Fin 3 := fun p ↦ generalBurgessPairingChoice p n
  let t0 := t.filter fun p ↦ c p = 0
  let t1 := t.filter fun p ↦ c p = 1
  let t2 := t.filter fun p ↦ c p = 2
  have hpart (j : Fin 3) : (t.filter fun p ↦ c p = j).prod id ≤ V := by
    have hmods : ∀ p ∈ (t.filter fun p ↦ c p = j),
        generalBurgessPairingMod j p n := by
      intro p hp
      have hpt := (Finset.mem_filter.mp hp).1
      have hc := (Finset.mem_filter.mp hp).2
      have hspec := general_pairingChoice_spec (hdiag p hpt)
      simpa [c, hc] using hspec
    fin_cases j
    · simp only [generalBurgessPairingMod] at hmods
      by_cases h01 : n 0 = n 1
      · have h23 : n 2 ≠ n 3 := by
          intro h
          exact hnotdiag (Or.inl ⟨h01, h⟩)
        exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 2) (hn 3) h23 (fun p hp ↦ (hmods p hp).2)
      · exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 0) (hn 1) h01 (fun p hp ↦ (hmods p hp).1)
    · simp only [generalBurgessPairingMod] at hmods
      by_cases h02 : n 0 = n 2
      · have h13 : n 1 ≠ n 3 := by
          intro h
          exact hnotdiag (Or.inr (Or.inl ⟨h02, h⟩))
        exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 1) (hn 3) h13 (fun p hp ↦ (hmods p hp).2)
      · exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 0) (hn 2) h02 (fun p hp ↦ (hmods p hp).1)
    · simp only [generalBurgessPairingMod] at hmods
      by_cases h03 : n 0 = n 3
      · have h12 : n 1 ≠ n 2 := by
          intro h
          exact hnotdiag (Or.inr (Or.inr ⟨h03, h⟩))
        exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 1) (hn 2) h12 (fun p hp ↦ (hmods p hp).2)
      · exact general_prime_product_le_of_modEq_of_ne _
          (fun p hp ↦ ht p (Finset.mem_filter.mp hp).1)
          (hn 0) (hn 3) h03 (fun p hp ↦ (hmods p hp).1)
  have ht0 : t0.prod id ≤ V := by simpa [t0] using hpart 0
  have ht1 : t1.prod id ≤ V := by simpa [t1] using hpart 1
  have ht2 : t2.prod id ≤ V := by simpa [t2] using hpart 2
  have h01 : Disjoint t0 t1 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp1
    simp only [t0, t1, Finset.mem_filter] at hp0 hp1
    omega
  have h02 : Disjoint t0 t2 := by
    rw [Finset.disjoint_left]
    intro p hp0 hp2
    simp only [t0, t2, Finset.mem_filter] at hp0 hp2
    omega
  have h12 : Disjoint t1 t2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [t1, t2, Finset.mem_filter] at hp1 hp2
    omega
  have hunion : t0 ∪ t1 ∪ t2 = t := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, t0, t1, t2]
    constructor
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
    · intro hp
      have hc : c p = 0 ∨ c p = 1 ∨ c p = 2 := by
        have hv : (c p).val = 0 ∨ (c p).val = 1 ∨ (c p).val = 2 := by
          omega
        rcases hv with hv | hv | hv
        · left
          exact Fin.eq_of_val_eq (by simpa using hv)
        · right; left
          exact Fin.eq_of_val_eq (by simpa using hv)
        · right; right
          exact Fin.eq_of_val_eq (by simpa using hv)
      rcases hc with hc | hc | hc
      · exact Or.inl (Or.inl ⟨hp, hc⟩)
      · exact Or.inl (Or.inr ⟨hp, hc⟩)
      · exact Or.inr ⟨hp, hc⟩
  have hprod : (∏ p ∈ t, p) = t0.prod id * t1.prod id * t2.prod id := by
    rw [← hunion, Finset.prod_union]
    · rw [Finset.prod_union h01]
      rfl
    · exact Finset.disjoint_union_left.mpr ⟨h02, h12⟩
  rw [hprod]
  calc
    t0.prod id * t1.prod id * t2.prod id ≤ V * V * V :=
      Nat.mul_le_mul (Nat.mul_le_mul ht0 ht1) ht2
    _ = V ^ 3 := by ring

noncomputable def generalPositiveIntervalRep
    (q V : ℕ) (x : ↥(zmodPositiveInterval q V)) : ℕ := by
  classical
  exact Classical.choose (Finset.mem_image.mp x.property)

lemma generalPositiveIntervalRep_mem
    (q V : ℕ) (x : ↥(zmodPositiveInterval q V)) :
    generalPositiveIntervalRep q V x ∈ Finset.Icc 1 V := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp x.property)).1

lemma generalPositiveIntervalRep_cast
    (q V : ℕ) (x : ↥(zmodPositiveInterval q V)) :
    ((generalPositiveIntervalRep q V x : ℕ) : ZMod q) = x := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp x.property)).2

lemma general_localQuadraticQuarticBound_le_three_mul
    {p : ℕ} (hp : 1 ≤ p) (v : Fin 4 → ZMod p) :
    localQuadraticQuarticBound p v ≤ 3 * p := by
  classical
  rw [localQuadraticQuarticBound]
  split_ifs
  · have hp0 : (0 : ℝ) ≤ p := by positivity
    nlinarith
  · have hp0 : (0 : ℝ) ≤ p := by positivity
    nlinarith
  · have hsqrt_nonneg : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
    have hsqrt_sq : Real.sqrt p ^ 2 = (p : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith

lemma general_quarticBound_le_trivial
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (v : Fin 4 → ZMod (primeSetModulus s)) :
    quadraticPrimeSetQuarticBound s hs v ≤
      (3 : ℝ) ^ s.card * (primeSetModulus s : ℝ) := by
  rw [quadraticPrimeSetQuarticBound]
  calc
    (∏ p : s, localQuadraticQuarticBound p
        (fun i ↦ primeSetCRTEqv s hs (v i) p)) ≤
        ∏ p : s, (3 * (p : ℕ) : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        rw [localQuadraticQuarticBound]
        split_ifs <;> positivity
      · intro p hp
        exact general_localQuadraticQuarticBound_le_three_mul
          (hs p p.property).one_le _
    _ = (3 : ℝ) ^ s.card * (primeSetModulus s : ℝ) := by
      rw [show (∏ p : s, (3 * (p : ℕ) : ℝ)) =
          (∏ _p : s, (3 : ℝ)) * ∏ p : s, ((p : ℕ) : ℝ) by
        rw [← Finset.prod_mul_distrib]]
      rw [show (∏ _p : s, (3 : ℝ)) = (3 : ℝ) ^ s.card by simp]
      rw [show (∏ p : s, ((p : ℕ) : ℝ)) =
          ∏ p ∈ s, (p : ℝ) by
        exact Finset.prod_attach s (fun p : ℕ ↦ (p : ℝ))]
      rw [primeSetModulus, Nat.cast_prod]

lemma general_quarticBound_le_offDiagonal_general
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) {V : ℕ} (hV : 0 < V)
    (hVq : V < primeSetModulus s)
    (v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V))
    (hv : ¬burgessDiagonal v) :
    quadraticPrimeSetQuarticBound s hs
        (fun i ↦ (v i : ZMod (primeSetModulus s))) ≤
      (3 : ℝ) ^ s.card * V ^ 2 * Real.sqrt (primeSetModulus s) := by
  classical
  let n : Fin 4 → ℕ := fun i ↦ generalPositiveIntervalRep (primeSetModulus s) V (v i)
  let t : Finset ℕ := s.filter fun p ↦ ∃ hp : p ∈ s,
    burgessDiagonal (fun i ↦ primeSetCRTEqv s hs
      (v i : ZMod (primeSetModulus s)) ⟨p, hp⟩)
  have hn : ∀ i, n i ∈ Finset.Icc 1 V := fun i ↦
    generalPositiveIntervalRep_mem _ _ _
  have hndiag : ¬burgessDiagonal n := by
    intro h
    apply hv
    have heq {i j : Fin 4} (hij : n i = n j) : v i = v j := by
      apply Subtype.ext
      calc
        (v i : ZMod (primeSetModulus s)) = (n i : ℕ) := by
          symm
          exact generalPositiveIntervalRep_cast _ _ _
        _ = (n j : ℕ) := by rw [hij]
        _ = (v j : ZMod (primeSetModulus s)) :=
          generalPositiveIntervalRep_cast _ _ _
    rcases h with h | h | h
    · exact Or.inl ⟨heq h.1, heq h.2⟩
    · exact Or.inr (Or.inl ⟨heq h.1, heq h.2⟩)
    · exact Or.inr (Or.inr ⟨heq h.1, heq h.2⟩)
  have htprime : ∀ p ∈ t, p.Prime := by
    intro p hp
    exact hs p (Finset.mem_filter.mp hp).1
  have htdiag : ∀ p ∈ t,
      burgessDiagonal (fun i ↦ (n i : ZMod p)) := by
    intro p hp
    obtain ⟨hpS, hpdiag⟩ := (Finset.mem_filter.mp hp).2
    have heq (i : Fin 4) :
        primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) ⟨p, hpS⟩ =
          (n i : ZMod p) := by
      calc
        primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) ⟨p, hpS⟩ =
            primeSetCRTEqv s hs
              ((n i : ℕ) : ZMod (primeSetModulus s)) ⟨p, hpS⟩ := by
                rw [generalPositiveIntervalRep_cast]
        _ = (n i : ZMod p) := primeSetCRTEqv_natCast_apply s hs _ _
    simp only [burgessDiagonal] at hpdiag ⊢
    simpa only [heq] using hpdiag
  have htprod : (∏ p ∈ t, p) ≤ V ^ 3 :=
    general_localDiagonal_prime_product_le_cube t htprime hV n hn hndiag htdiag
  have hpoint (p : ℕ) (hp : p ∈ s) :
      localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) ⟨p, hp⟩) ≤
        (3 * Real.sqrt p) *
          (if p ∈ t then Real.sqrt p else 1) := by
    rw [localQuadraticQuarticBound, if_neg (hodd p hp)]
    by_cases hd : burgessDiagonal (fun i ↦ primeSetCRTEqv s hs
        (v i : ZMod (primeSetModulus s)) ⟨p, hp⟩)
    · rw [if_pos hd, if_pos]
      · have hsqrt_sq : Real.sqrt p ^ 2 = (p : ℝ) :=
          Real.sq_sqrt (by positivity)
        nlinarith [Real.sqrt_nonneg (p : ℝ)]
      · exact Finset.mem_filter.mpr ⟨hp, ⟨hp, hd⟩⟩
    · have hpt : p ∉ t := by
        intro hpt
        obtain ⟨_hpS, hd'⟩ := (Finset.mem_filter.mp hpt).2
        exact hd hd'
      rw [if_neg hd, if_neg hpt, mul_one]
  have hprod :
      quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s))) ≤
        (∏ p ∈ s, (3 * Real.sqrt p) *
          (if p ∈ t then Real.sqrt p else 1)) := by
    rw [quadraticPrimeSetQuarticBound]
    calc
      (∏ p : s, localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p)) ≤
          ∏ p : s, (3 * Real.sqrt (p : ℕ)) *
            (if (p : ℕ) ∈ t then Real.sqrt (p : ℕ) else 1) := by
        apply Finset.prod_le_prod
        · intro p hp
          rw [localQuadraticQuarticBound]
          split_ifs <;> positivity
        · intro p hp
          exact hpoint p p.property
      _ = ∏ p ∈ s, (3 * Real.sqrt p) *
            (if p ∈ t then Real.sqrt p else 1) :=
        Finset.prod_coe_sort s (fun p : ℕ ↦
          (3 : ℝ) * Real.sqrt p *
            (if p ∈ t then Real.sqrt p else 1))
  have htss : t ⊆ s := Finset.filter_subset _ _
  have hprodform :
      (∏ p ∈ s, (3 * Real.sqrt p) *
          (if p ∈ t then Real.sqrt p else 1)) =
        (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
          Real.sqrt (∏ p ∈ t, p) := by
    calc
      (∏ p ∈ s, (3 * Real.sqrt p) *
          (if p ∈ t then Real.sqrt p else 1)) =
          (∏ p ∈ s, (3 : ℝ)) * (∏ p ∈ s, Real.sqrt p) *
            ∏ p ∈ s, (if p ∈ t then Real.sqrt p else 1) := by
        simp_rw [Finset.prod_mul_distrib]
      _ = (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
            ∏ p ∈ t, Real.sqrt p := by
        rw [show (∏ p ∈ s, (3 : ℝ)) = (3 : ℝ) ^ s.card by simp]
        rw [prod_sqrt_nat_eq_sqrt_prod]
        rw [primeSetModulus]
        rw [Nat.cast_prod]
        rw [Finset.prod_ite_mem]
        rw [Finset.inter_eq_right.mpr htss]
      _ = _ := by
        rw [prod_sqrt_nat_eq_sqrt_prod]
  rw [hprodform] at hprod
  have htprodR : ((∏ p ∈ t, p : ℕ) : ℝ) ≤ (V : ℝ) ^ 3 := by
    exact_mod_cast htprod
  have htprodC : (∏ p ∈ t, (p : ℝ)) ≤ (V : ℝ) ^ 3 := by
    simpa only [Nat.cast_prod] using htprodR
  calc
    quadraticPrimeSetQuarticBound s hs
        (fun i ↦ (v i : ZMod (primeSetModulus s))) ≤
        (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
          Real.sqrt (∏ p ∈ t, p) := hprod
    _ ≤ (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
          Real.sqrt ((V : ℝ) ^ 3) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.sqrt_le_sqrt htprodC
      · positivity
    _ ≤ (3 : ℝ) ^ s.card * V ^ 2 *
          Real.sqrt (primeSetModulus s) := by
      have hsqrtV : Real.sqrt ((V : ℝ) ^ 3) ≤ (V : ℝ) ^ 2 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt ((V : ℝ) ^ 3) := Real.sqrt_nonneg _
        have hsqrt_sq : Real.sqrt ((V : ℝ) ^ 3) ^ 2 = (V : ℝ) ^ 3 :=
          Real.sq_sqrt (by positivity)
        have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
        nlinarith [sq_nonneg ((V : ℝ) ^ 2 - Real.sqrt ((V : ℝ) ^ 3))]
      calc
        (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
            Real.sqrt ((V : ℝ) ^ 3) ≤
            (3 : ℝ) ^ s.card * Real.sqrt (primeSetModulus s) *
              (V : ℝ) ^ 2 := by
                gcongr
        _ = (3 : ℝ) ^ s.card * V ^ 2 *
            Real.sqrt (primeSetModulus s) := by ring

lemma general_quadraticPrimeSetQuarticBound_eq_of_diagonal
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) {V : ℕ}
    (v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V))
    (hv : burgessDiagonal v) :
    quadraticPrimeSetQuarticBound s hs
        (fun i ↦ (v i : ZMod (primeSetModulus s))) =
      (primeSetModulus s : ℝ) := by
  classical
  rw [quadraticPrimeSetQuarticBound]
  have hlocal (p : s) :
      localQuadraticQuarticBound p
          (fun i ↦ primeSetCRTEqv s hs
            (v i : ZMod (primeSetModulus s)) p) = (p : ℝ) := by
    rw [localQuadraticQuarticBound, if_neg (hodd p p.property), if_pos]
    simp only [burgessDiagonal] at hv ⊢
    let f : ↥(zmodPositiveInterval (primeSetModulus s) V) → ZMod p :=
      fun x ↦ primeSetCRTEqv s hs
        (x : ZMod (primeSetModulus s)) p
    rcases hv with h | h | h
    · exact Or.inl ⟨congrArg f h.1, congrArg f h.2⟩
    · exact Or.inr (Or.inl ⟨congrArg f h.1, congrArg f h.2⟩)
    · exact Or.inr (Or.inr ⟨congrArg f h.1, congrArg f h.2⟩)
  calc
    (∏ p : s, localQuadraticQuarticBound p
        (fun i ↦ primeSetCRTEqv s hs
          (v i : ZMod (primeSetModulus s)) p)) =
        ∏ p : s, ((p : ℕ) : ℝ) := by
      apply Fintype.prod_congr
      exact hlocal
    _ = (primeSetModulus s : ℝ) := by
      rw [primeSetModulus, Nat.cast_prod]
      exact Finset.prod_coe_sort s (fun p : ℕ ↦ (p : ℝ))

lemma general_quadraticPrimeSetQuarticBound_sum_le_general
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) {V : ℕ}
    (hV : 0 < V) (hVq : V < primeSetModulus s) :
    (∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
        quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s)))) ≤
      3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
        (V : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * V ^ 2 *
            Real.sqrt (primeSetModulus s)) := by
  classical
  calc
    (∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
        quadraticPrimeSetQuarticBound s hs
          (fun i ↦ (v i : ZMod (primeSetModulus s)))) ≤
        ∑ v : Fin 4 → ↥(zmodPositiveInterval (primeSetModulus s) V),
          if burgessDiagonal v then (primeSetModulus s : ℝ) else
            (3 : ℝ) ^ s.card * V ^ 2 *
              Real.sqrt (primeSetModulus s) := by
      apply Finset.sum_le_sum
      intro v _hv
      by_cases hv : burgessDiagonal v
      · rw [if_pos hv, general_quadraticPrimeSetQuarticBound_eq_of_diagonal
          s hs hodd v hv]
      · rw [if_neg hv]
        exact general_quarticBound_le_offDiagonal_general
          s hs hodd hV hVq v hv
    _ ≤ 3 *
          (Fintype.card
            ↥(zmodPositiveInterval (primeSetModulus s) V) : ℝ) ^ 2 *
            (primeSetModulus s : ℝ) +
        (Fintype.card
            ↥(zmodPositiveInterval (primeSetModulus s) V) : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * V ^ 2 *
            Real.sqrt (primeSetModulus s)) := by
      apply sum_ite_burgessDiagonal_le
      · positivity
      · positivity
    _ = 3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
        (V : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * V ^ 2 *
            Real.sqrt (primeSetModulus s)) := by
      rw [Fintype.card_coe, zmodPositiveInterval_card hVq]

/-! ### Burgess ratios with unit denominators

For a composite squarefree conductor a denominator must be represented by a
unit.  These definitions are the composite-ring analogues of the prime-field
ratio weights used above. -/

def burgessUnitRatioWeight
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) (x : R) : ℕ :=
  ((I ×ˢ U).filter fun nu ↦ ((nu.2⁻¹ : Rˣ) : R) * nu.1 = x).card

def burgessUnitRatioEnergy
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) : ℝ :=
  ∑ x : R, (burgessUnitRatioWeight I U x : ℝ) ^ 2

lemma sum_burgessUnitRatioWeight
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) :
    ∑ x : R, burgessUnitRatioWeight I U x = I.card * U.card := by
  rw [← Finset.card_product]
  simpa only [burgessUnitRatioWeight] using
    (Finset.card_eq_sum_card_fiberwise
      (s := I ×ˢ U) (t := Finset.univ)
      (f := fun nu : R × Rˣ ↦ ((nu.2⁻¹ : Rˣ) : R) * nu.1)
      (by simp)).symm

lemma burgessUnitRatioEnergy_nonneg
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) :
    0 ≤ burgessUnitRatioEnergy I U := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma burgessUnitRatioEnergy_eq_card_collision
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) :
    burgessUnitRatioEnergy I U =
      (((((I ×ˢ U) ×ˢ (I ×ˢ U)).filter fun ab ↦
        (((ab.1.2⁻¹ : Rˣ) : R) * ab.1.1 =
          ((ab.2.2⁻¹ : Rˣ) : R) * ab.2.1)).card : ℕ) : ℝ) := by
  have h := sum_card_fiber_sq_eq_card_collision (I ×ˢ U)
    (fun nu : R × Rˣ ↦ ((nu.2⁻¹ : Rˣ) : R) * nu.1)
  rw [burgessUnitRatioEnergy]
  change (∑ x : R,
      (((((I ×ˢ U).filter fun nu ↦
        ((nu.2⁻¹ : Rˣ) : R) * nu.1 = x).card) : ℕ) : ℝ) ^ 2) = _
  simp_rw [← Nat.cast_pow]
  rw [← Nat.cast_sum]
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) h

lemma sum_burgessUnitRatioWeight_mul
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) (f : R → ℝ) :
    (∑ x : R, (burgessUnitRatioWeight I U x : ℝ) * f x) =
      ∑ nu ∈ I ×ˢ U, f (((nu.2⁻¹ : Rˣ) : R) * nu.1) := by
  rw [← Finset.sum_fiberwise' (I ×ˢ U)
    (fun nu : R × Rˣ ↦ ((nu.2⁻¹ : Rˣ) : R) * nu.1) f]
  apply Finset.sum_congr rfl
  intro x hx
  simp [burgessUnitRatioWeight, nsmul_eq_mul]

/-- Hölder's inequality in the form needed for a Burgess amplifier over an
arbitrary finite commutative ring. -/
lemma burgessUnit_weighted_fourth_bound
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (I : Finset R) (U : Finset Rˣ) (T : R → ℝ) :
    (∑ x : R, (burgessUnitRatioWeight I U x : ℝ) * |T x|) ^ 4 ≤
      ((I.card * U.card : ℕ) : ℝ) ^ 2 * burgessUnitRatioEnergy I U *
        (∑ x : R, T x ^ 4) := by
  have hholder := sum_mul_pow_four_le_sum_sq_mul_sum_pow_four
    (Finset.univ : Finset R)
    (fun x ↦ (burgessUnitRatioWeight I U x : ℝ))
    (fun x ↦ |T x|)
    (fun _ _ ↦ Nat.cast_nonneg _)
  have hsum :
      (∑ x : R, (burgessUnitRatioWeight I U x : ℝ)) =
        ((I.card * U.card : ℕ) : ℝ) := by
    exact_mod_cast sum_burgessUnitRatioWeight I U
  have habs4 :
      (∑ x : R, |T x| ^ 4) = ∑ x : R, T x ^ 4 := by
    apply Finset.sum_congr rfl
    intro x hx
    calc
      |T x| ^ 4 = (|T x| ^ 2) ^ 2 := by ring
      _ = (T x ^ 2) ^ 2 := by rw [sq_abs]
      _ = T x ^ 4 := by ring
  rw [hsum, show (∑ x : R,
      ((burgessUnitRatioWeight I U x : ℝ)) ^ 2) =
        burgessUnitRatioEnergy I U by rfl, habs4] at hholder
  exact hholder

lemma quadraticPrimeSetCharReal_mul
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (a b : ZMod (primeSetModulus s)) :
    quadraticPrimeSetCharReal s hs (a * b) =
      quadraticPrimeSetCharReal s hs a *
        quadraticPrimeSetCharReal s hs b := by
  rw [quadraticPrimeSetCharReal, quadraticPrimeSetCharReal,
    quadraticPrimeSetCharReal, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  letI : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
  simp [localQuadraticCharReal, quadraticCharReal, map_mul]

lemma primeSetCRTEqv_unit_ne_zero
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : (ZMod (primeSetModulus s))ˣ) (p : s) :
    primeSetCRTEqv s hs (u : ZMod (primeSetModulus s)) p ≠ 0 := by
  letI : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  letI : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
  have hu : IsUnit
      (primeSetCRTEqv s hs (u : ZMod (primeSetModulus s))) :=
    u.isUnit.map (primeSetCRTEqv s hs).toMonoidHom
  exact (hu.map (Pi.evalMonoidHom (fun p : s ↦ ZMod (p : ℕ)) p)).ne_zero

lemma abs_quadraticPrimeSetCharReal_unit
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (u : (ZMod (primeSetModulus s))ˣ) :
    |quadraticPrimeSetCharReal s hs (u : ZMod (primeSetModulus s))| = 1 := by
  rw [quadraticPrimeSetCharReal, Finset.abs_prod]
  calc
    (∏ p : s, |localQuadraticCharReal p (hs p p.property)
      (primeSetCRTEqv s hs (u : ZMod (primeSetModulus s)) p)|) =
        ∏ _p : s, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro p
      letI : Fact (p : ℕ).Prime := ⟨hs p p.property⟩
      simpa [localQuadraticCharReal] using
        abs_quadraticCharReal_of_ne_zero
          (primeSetCRTEqv_unit_ne_zero s hs u p)
    _ = 1 := by simp

/-- A multiplicatively dilated squarefree-character sum. -/
noncomputable def quadraticPrimeSetDilatedShiftSum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (V : Finset (ZMod (primeSetModulus s)))
    (n : ZMod (primeSetModulus s))
    (u : (ZMod (primeSetModulus s))ˣ) : ℝ :=
  ∑ v ∈ V, quadraticPrimeSetCharReal s hs
    (n + (u : ZMod (primeSetModulus s)) * v)

/-- Multiplicativity converts a unit-dilated sum into a translated sum at the
unit ratio. -/
lemma abs_quadraticPrimeSetDilatedShiftSum_eq
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (V : Finset (ZMod (primeSetModulus s)))
    (n : ZMod (primeSetModulus s))
    (u : (ZMod (primeSetModulus s))ˣ) :
    |quadraticPrimeSetDilatedShiftSum s hs V n u| =
      |quadraticPrimeSetShiftSum s hs V
        (((u⁻¹ : (ZMod (primeSetModulus s))ˣ) :
          ZMod (primeSetModulus s)) * n)| := by
  have hterm (v : ZMod (primeSetModulus s)) :
      quadraticPrimeSetCharReal s hs
          (n + (u : ZMod (primeSetModulus s)) * v) =
        quadraticPrimeSetCharReal s hs
            (u : ZMod (primeSetModulus s)) *
          quadraticPrimeSetCharReal s hs
            (((u⁻¹ : (ZMod (primeSetModulus s))ˣ) :
              ZMod (primeSetModulus s)) * n + v) := by
    rw [← quadraticPrimeSetCharReal_mul]
    congr 1
    rw [mul_add, ← mul_assoc, ← Units.val_mul]
    simp
  rw [quadraticPrimeSetDilatedShiftSum, quadraticPrimeSetShiftSum]
  simp_rw [hterm]
  rw [← Finset.mul_sum, abs_mul,
    abs_quadraticPrimeSetCharReal_unit, one_mul]

lemma sum_abs_quadraticPrimeSetDilatedShiftSum_eq_weighted
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    [NeZero (primeSetModulus s)]
    (I : Finset (ZMod (primeSetModulus s)))
    (U : Finset (ZMod (primeSetModulus s))ˣ)
    (V : Finset (ZMod (primeSetModulus s))) :
    (∑ nu ∈ I ×ˢ U,
        |quadraticPrimeSetDilatedShiftSum s hs V nu.1 nu.2|) =
      ∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight I U x : ℝ) *
          |quadraticPrimeSetShiftSum s hs V x| := by
  rw [sum_burgessUnitRatioWeight_mul]
  apply Finset.sum_congr rfl
  intro nu hnu
  rw [abs_quadraticPrimeSetDilatedShiftSum_eq]

lemma coprime_primeSetModulus_of_lt_primes
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {u U : ℕ} (hu : 0 < u) (huU : u ≤ U)
    (hlarge : ∀ p ∈ s, U < p) :
    u.Coprime (primeSetModulus s) := by
  rw [primeSetModulus]
  apply Nat.Coprime.prod_right
  intro p hp
  exact ((hs p hp).coprime_iff_not_dvd.mpr fun hdiv ↦
    (Nat.not_dvd_of_pos_of_lt hu
      (lt_of_le_of_lt huU (hlarge p hp))) hdiv).symm

/-- A positive integer below every prime in `s`, regarded as a unit modulo
the product conductor. -/
def primeSetPositiveUnit
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p)
    (u : ↥(Finset.Icc 1 U)) :
    (ZMod (primeSetModulus s))ˣ :=
  ZMod.unitOfCoprime u
    (coprime_primeSetModulus_of_lt_primes s hs
      (Finset.mem_Icc.mp u.property).1
      (Finset.mem_Icc.mp u.property).2 hlarge)

/-- The first `U` positive integers, embedded as distinct conductor units
when all conductor primes exceed `U`. -/
noncomputable def primeSetPositiveUnits
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) :
    Finset (ZMod (primeSetModulus s))ˣ :=
  (Finset.univ : Finset ↥(Finset.Icc 1 U)).image
    (primeSetPositiveUnit s hs U hlarge)

lemma primeSetPositiveUnit_coe
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p)
    (u : ↥(Finset.Icc 1 U)) :
    ((primeSetPositiveUnit s hs U hlarge u :
      (ZMod (primeSetModulus s))ˣ) : ZMod (primeSetModulus s)) =
      (u : ℕ) := by
  exact ZMod.coe_unitOfCoprime _ _

lemma primeSetPositiveUnits_card
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p) :
    (primeSetPositiveUnits s hs U hlarge).card = U := by
  have hUq : U < primeSetModulus s := by
    obtain ⟨p, hp⟩ := hsne
    exact (hlarge p hp).trans_le
      (Nat.le_of_dvd (primeSetModulus_pos s hs)
        (dvd_primeSetModulus hp))
  rw [primeSetPositiveUnits, Finset.card_image_of_injective]
  · simp
  · intro u v huv
    apply Subtype.ext
    apply eq_of_zmod_positive_cast_eq u.property v.property hUq
    have hcoe := congrArg Units.val huv
    simpa [primeSetPositiveUnit_coe] using hcoe

/-- Cross multiplication for ratios whose denominators are units; unlike the
field version above this is valid in rings with zero divisors. -/
lemma unit_inv_mul_eq_unit_inv_mul_iff
    {R : Type*} [CommRing R]
    (u₁ u₂ : Rˣ) (n₁ n₂ : R) :
    ((u₁⁻¹ : Rˣ) : R) * n₁ = ((u₂⁻¹ : Rˣ) : R) * n₂ ↔
      n₁ * (u₂ : R) = n₂ * (u₁ : R) := by
  constructor
  · intro h
    have h' : n₁ = (u₁ : R) * (((u₂⁻¹ : Rˣ) : R) * n₂) :=
      (Units.inv_mul_eq_iff_eq_mul u₁).mp h
    rw [h']
    calc
      ((u₁ : R) * (((u₂⁻¹ : Rˣ) : R) * n₂)) * (u₂ : R) =
          n₂ * (u₁ : R) * (((u₂⁻¹ : Rˣ) : R) * (u₂ : R)) := by
            ac_rfl
      _ = n₂ * (u₁ : R) := by rw [Units.inv_mul]; simp
  · intro h
    apply (Units.inv_mul_eq_iff_eq_mul u₁).mpr
    have h' : n₁ = (n₂ * (u₁ : R)) * ((u₂⁻¹ : Rˣ) : R) :=
      (Units.eq_mul_inv_iff_mul_eq u₂).mpr h
    calc
      n₁ = (n₂ * (u₁ : R)) * ((u₂⁻¹ : Rˣ) : R) := h'
      _ = (u₁ : R) * (((u₂⁻¹ : Rˣ) : R) * n₂) := by ac_rfl

/-- The interval collision estimate only needs the first denominator to be
coprime to the modulus; primality of the modulus is unnecessary. -/
lemma burgessIntervalCollision_card_le_of_coprime
    {q M H U u₁ u₂ : ℕ}
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hcop₁ : q.Coprime u₁)
    (hsmall : 2 * (U * H) < q) :
    (burgessIntervalCollision q M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD q] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop₁.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD q] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHq : H < q := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHq)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHq)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD q] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

noncomputable def primeSetPositiveUnitNat
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) (u : ℕ) :
    (ZMod (primeSetModulus s))ˣ := by
  classical
  exact if hu : u ∈ Finset.Icc 1 U then
    primeSetPositiveUnit s hs U hlarge ⟨u, hu⟩ else 1

lemma primeSetPositiveUnitNat_of_mem
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) {u : ℕ}
    (hu : u ∈ Finset.Icc 1 U) :
    primeSetPositiveUnitNat s hs U hlarge u =
      primeSetPositiveUnit s hs U hlarge ⟨u, hu⟩ := by
  simp [primeSetPositiveUnitNat, hu]

lemma primeSetPositiveUnitNat_coe_of_mem
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) {u : ℕ}
    (hu : u ∈ Finset.Icc 1 U) :
    ((primeSetPositiveUnitNat s hs U hlarge u :
      (ZMod (primeSetModulus s))ˣ) : ZMod (primeSetModulus s)) = u := by
  rw [primeSetPositiveUnitNat_of_mem s hs U hlarge hu,
    primeSetPositiveUnit_coe]

lemma primeSetPositiveUnitNat_mem
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) {u : ℕ}
    (hu : u ∈ Finset.Icc 1 U) :
    primeSetPositiveUnitNat s hs U hlarge u ∈
      primeSetPositiveUnits s hs U hlarge := by
  rw [primeSetPositiveUnitNat_of_mem s hs U hlarge hu]
  rw [primeSetPositiveUnits, Finset.mem_image]
  exact ⟨⟨u, hu⟩, by simp, rfl⟩

lemma primeSetPositiveUnitNat_injective_on
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    {u v : ℕ} (hu : u ∈ Finset.Icc 1 U) (hv : v ∈ Finset.Icc 1 U)
    (huv : primeSetPositiveUnitNat s hs U hlarge u =
      primeSetPositiveUnitNat s hs U hlarge v) : u = v := by
  have hUq : U < primeSetModulus s := by
    obtain ⟨p, hp⟩ := hsne
    exact (hlarge p hp).trans_le
      (Nat.le_of_dvd (primeSetModulus_pos s hs)
        (dvd_primeSetModulus hp))
  apply eq_of_zmod_positive_cast_eq hu hv hUq
  have hcoe := congrArg Units.val huv
  simpa [primeSetPositiveUnitNat_coe_of_mem s hs U hlarge hu,
    primeSetPositiveUnitNat_coe_of_mem s hs U hlarge hv] using hcoe

noncomputable def burgessUnitCollisionCast
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) (M : ℕ)
    (ab : (ℕ × ℕ) × (ℕ × ℕ)) :
    ((ZMod (primeSetModulus s) × (ZMod (primeSetModulus s))ˣ) ×
      (ZMod (primeSetModulus s) × (ZMod (primeSetModulus s))ˣ)) :=
  (((M + ab.1.1 : ℕ),
      primeSetPositiveUnitNat s hs U hlarge ab.1.2),
    ((M + ab.2.1 : ℕ),
      primeSetPositiveUnitNat s hs U hlarge ab.2.2))

/-- The collision finset for the composite-ring unit ratio map. -/
noncomputable def burgessPrimeSetRatioCollisions
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hlarge : ∀ p ∈ s, U < p) (M H : ℕ) :=
  (((zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetPositiveUnits s hs U hlarge) ×ˢ
      (zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetPositiveUnits s hs U hlarge)).filter fun ab ↦
    (((ab.1.2⁻¹ : (ZMod (primeSetModulus s))ˣ) :
        ZMod (primeSetModulus s)) * ab.1.1 =
      ((ab.2.2⁻¹ : (ZMod (primeSetModulus s))ˣ) :
        ZMod (primeSetModulus s)) * ab.2.1))

/-- Unit-ratio collisions modulo a squarefree conductor are in bijection
with the same natural cross-multiplication collisions as in prime Burgess. -/
lemma unitRatioCollision_card_eq_intervalAllCollisions
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    {M H : ℕ} (hH : H ≤ primeSetModulus s) :
    (burgessPrimeSetRatioCollisions s hs U hlarge M H).card =
      (burgessIntervalAllCollisions (primeSetModulus s) M H U).card := by
  rw [burgessPrimeSetRatioCollisions]
  symm
  apply Finset.card_bij
      (fun ab _ ↦ burgessUnitCollisionCast s hs U hlarge M ab)
  · intro ab hab
    rw [burgessIntervalAllCollisions, Finset.mem_filter] at hab
    rw [Finset.mem_filter]
    rcases hab with ⟨habbox, habcong⟩
    rcases Finset.mem_product.mp habbox with ⟨hab₁, hab₂⟩
    rcases Finset.mem_product.mp hab₁ with ⟨hi₁, hu₁⟩
    rcases Finset.mem_product.mp hab₂ with ⟨hi₂, hu₂⟩
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_product.mpr
      · exact ⟨Finset.mem_image.mpr ⟨ab.1.1, hi₁, rfl⟩,
          primeSetPositiveUnitNat_mem s hs U hlarge hu₁⟩
      · exact ⟨Finset.mem_image.mpr ⟨ab.2.1, hi₂, rfl⟩,
          primeSetPositiveUnitNat_mem s hs U hlarge hu₂⟩
    · apply (unit_inv_mul_eq_unit_inv_mul_iff
        (primeSetPositiveUnitNat s hs U hlarge ab.1.2)
        (primeSetPositiveUnitNat s hs U hlarge ab.2.2)
        ((M + ab.1.1 : ℕ) : ZMod (primeSetModulus s))
        ((M + ab.2.1 : ℕ) : ZMod (primeSetModulus s))).2
      rw [primeSetPositiveUnitNat_coe_of_mem s hs U hlarge hu₁,
        primeSetPositiveUnitNat_coe_of_mem s hs U hlarge hu₂]
      simpa only [burgessUnitCollisionCast, Nat.cast_mul] using
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr habcong
  · intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨habox, _⟩
    rcases Finset.mem_filter.mp hb with ⟨hbbox, _⟩
    rcases Finset.mem_product.mp habox with ⟨ha₁, ha₂⟩
    rcases Finset.mem_product.mp hbbox with ⟨hb₁, hb₂⟩
    rcases Finset.mem_product.mp ha₁ with ⟨hai₁, hau₁⟩
    rcases Finset.mem_product.mp ha₂ with ⟨hai₂, hau₂⟩
    rcases Finset.mem_product.mp hb₁ with ⟨hbi₁, hbu₁⟩
    rcases Finset.mem_product.mp hb₂ with ⟨hbi₂, hbu₂⟩
    apply Prod.ext
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₁) (Finset.mem_range.mp hbi₁) hH
          (congrArg (fun z ↦ z.1.1) hab)
      · exact primeSetPositiveUnitNat_injective_on s hs U hsne hlarge
          hau₁ hbu₁ (congrArg (fun z ↦ z.1.2) hab)
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₂) (Finset.mem_range.mp hbi₂) hH
          (congrArg (fun z ↦ z.2.1) hab)
      · exact primeSetPositiveUnitNat_injective_on s hs U hsne hlarge
          hau₂ hbu₂ (congrArg (fun z ↦ z.2.2) hab)
  · intro z hz
    rw [Finset.mem_filter] at hz
    rcases hz with ⟨hzbox, hzratio⟩
    rcases Finset.mem_product.mp hzbox with ⟨hz₁, hz₂⟩
    rcases Finset.mem_product.mp hz₁ with ⟨hzn₁, hzu₁⟩
    rcases Finset.mem_product.mp hz₂ with ⟨hzn₂, hzu₂⟩
    rw [zmodNatInterval, Finset.mem_image] at hzn₁ hzn₂
    rw [primeSetPositiveUnits, Finset.mem_image] at hzu₁ hzu₂
    rcases hzn₁ with ⟨i₁, hi₁, hi₁z⟩
    rcases hzu₁ with ⟨u₁, hu₁, hu₁z⟩
    rcases hzn₂ with ⟨i₂, hi₂, hi₂z⟩
    rcases hzu₂ with ⟨u₂, hu₂, hu₂z⟩
    refine ⟨((i₁, u₁), (i₂, u₂)), ?_, ?_⟩
    · rw [burgessIntervalAllCollisions, Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hi₁, u₁.property⟩,
            Finset.mem_product.mpr ⟨hi₂, u₂.property⟩⟩
      · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        rw [Nat.cast_mul, Nat.cast_mul]
        change ((M + i₁ : ℕ) : ZMod (primeSetModulus s)) *
            (u₂ : ℕ) =
          ((M + i₂ : ℕ) : ZMod (primeSetModulus s)) * (u₁ : ℕ)
        have hcross := (unit_inv_mul_eq_unit_inv_mul_iff
          (primeSetPositiveUnitNat s hs U hlarge u₁)
          (primeSetPositiveUnitNat s hs U hlarge u₂)
          ((M + i₁ : ℕ) : ZMod (primeSetModulus s))
          ((M + i₂ : ℕ) : ZMod (primeSetModulus s))).mp (by
            simpa only [hi₁z, hi₂z,
              primeSetPositiveUnitNat_of_mem s hs U hlarge u₁.property,
              primeSetPositiveUnitNat_of_mem s hs U hlarge u₂.property,
              hu₁z, hu₂z] using hzratio)
        simpa only [primeSetPositiveUnitNat_coe_of_mem s hs U hlarge u₁.property,
          primeSetPositiveUnitNat_coe_of_mem s hs U hlarge u₂.property] using hcross
    · simp [burgessUnitCollisionCast, hi₁z, hi₂z,
        primeSetPositiveUnitNat_of_mem s hs U hlarge u₁.property,
        primeSetPositiveUnitNat_of_mem s hs U hlarge u₂.property,
        hu₁z, hu₂z]

lemma burgessUnitRatioEnergy_primeSetIntervals_eq_sum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : H ≤ primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetPositiveUnits s hs U hlarge) =
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (burgessIntervalCollision (primeSetModulus s) M H u₁ u₂).card : ℕ) : ℝ) := by
  rw [burgessUnitRatioEnergy_eq_card_collision]
  change ((burgessPrimeSetRatioCollisions s hs U hlarge M H).card : ℝ) = _
  rw [unitRatioCollision_card_eq_intervalAllCollisions s hs U hsne hlarge hH]
  rw [burgessIntervalAllCollisions_card_eq_sum]

lemma burgessUnitRatioEnergy_primeSetIntervals_le_reduced_sum
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : 0 < H) (hU : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetPositiveUnits s hs U hlarge) ≤
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) := by
  rw [burgessUnitRatioEnergy_primeSetIntervals_eq_sum
    s hs U hsne hlarge hHq]
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      burgessIntervalCollision_card_le_of_coprime hH hU hu₁ hu₂
        (coprime_primeSetModulus_of_lt_primes s hs
          (Finset.mem_Icc.mp hu₁).1 (Finset.mem_Icc.mp hu₁).2 hlarge).symm
        hsmall

/-- The prime Burgess harmonic energy estimate remains valid verbatim for a
squarefree conductor when every chosen denominator is a unit. -/
lemma burgessUnitRatioEnergy_primeSetIntervals_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : 0 < H) (hU : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetPositiveUnits s hs U hlarge) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  calc
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetPositiveUnits s hs U hlarge) ≤
      ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) :=
      burgessUnitRatioEnergy_primeSetIntervals_le_reduced_sum
        s hs U hsne hlarge hH hU hHq hsmall
    _ ≤ (burgessDivisorOvercount H U : ℝ) :=
      reduced_denominator_sum_cast_le H U
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) :=
      burgessDivisorOvercount_cast_le H U hU

lemma primeSetPositiveUnit_injective
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p) :
    Function.Injective (primeSetPositiveUnit s hs U hlarge) := by
  intro u v huv
  apply Subtype.ext
  exact primeSetPositiveUnitNat_injective_on s hs U hsne hlarge
    u.property v.property (by
      simpa only [primeSetPositiveUnitNat_of_mem s hs U hlarge u.property,
        primeSetPositiveUnitNat_of_mem s hs U hlarge v.property] using huv)

lemma quadraticPrimeSetDilatedShiftSum_zmodPositive
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hlarge : ∀ p ∈ s, U < p)
    {M i u V : ℕ} (hu : u ∈ Finset.Icc 1 U)
    (hV : V < primeSetModulus s) :
    quadraticPrimeSetDilatedShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V)
        ((M + i : ℕ) : ZMod (primeSetModulus s))
        (primeSetPositiveUnit s hs U hlarge ⟨u, hu⟩) =
      ∑ v ∈ Finset.Icc 1 V,
        quadraticPrimeFactorProduct s (M + i + u * v) := by
  have hinj : Set.InjOn
      (fun v : ℕ ↦ (v : ZMod (primeSetModulus s)))
      (Finset.Icc 1 V) := by
    intro v hv w hw hvw
    exact eq_of_zmod_positive_cast_eq hv hw hV hvw
  rw [quadraticPrimeSetDilatedShiftSum, zmodPositiveInterval]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← quadraticPrimeSetCharReal_natCast s hs (M + i + u * v)]
  congr 1
  rw [primeSetPositiveUnit_coe]
  push_cast
  ring

lemma sum_abs_quadraticPrimeSetDilatedShiftSum_zmodIntervals
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    {M H V : ℕ} (hH : H ≤ primeSetModulus s)
    (hV : V < primeSetModulus s) :
    (∑ nu ∈ zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetPositiveUnits s hs U hlarge,
      |quadraticPrimeSetDilatedShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V) nu.1 nu.2|) =
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticPrimeFactorProduct s (M + i + u * v)| := by
  have hinjI : Set.InjOn
      (fun i : ℕ ↦ ((M + i : ℕ) : ZMod (primeSetModulus s)))
      (Finset.range H) := by
    intro i hi j hj hij
    exact eq_of_zmod_interval_cast_eq
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hH hij
  rw [Finset.sum_product]
  rw [zmodNatInterval, Finset.sum_image hinjI]
  apply Finset.sum_congr rfl
  intro i hi
  have hinjU : Set.InjOn (primeSetPositiveUnit s hs U hlarge)
      (Finset.univ : Finset ↥(Finset.Icc 1 U)) :=
    (primeSetPositiveUnit_injective s hs U hsne hlarge).injOn
  rw [primeSetPositiveUnits, Finset.sum_image hinjU]
  rw [Finset.sum_subtype (Finset.Icc 1 U) (fun _ ↦ Iff.rfl)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [quadraticPrimeSetDilatedShiftSum_zmodPositive
    s hs U hlarge u.property hV]

/-- Purely combinatorial rearrangement and triangle inequality for the
three sums in a Burgess average. -/
lemma abs_burgess_shifted_triple_sum_le_generic
    (f : ℕ → ℝ) (M H U V : ℕ) :
    |∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H, f (M + u * v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v)| := by
  have hreorder :
      (∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          ∑ i ∈ Finset.range H, f (M + u * v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          ∑ v ∈ Finset.Icc 1 V, f (M + i + u * v) := by
    calc
      (∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          ∑ i ∈ Finset.range H, f (M + u * v + i)) =
        ∑ u ∈ Finset.Icc 1 U, ∑ i ∈ Finset.range H,
          ∑ v ∈ Finset.Icc 1 V, f (M + u * v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          ∑ v ∈ Finset.Icc 1 V, f (M + u * v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        ∑ v ∈ Finset.Icc 1 V, f (M + i + u * v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
          f (M + i + u * v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V, f (M + i + u * v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

lemma abs_quadraticPrimeFactorProduct_amplified_sub_shifted_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ} (hUV : U * V ≤ H) :
    |(((U * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)) -
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + u * v + i))| ≤
      (2 : ℝ) * (U * V) ^ 2 := by
  have havg := abs_burgess_shift_average_sub_le
    (quadraticPrimeFactorProduct s)
    (abs_quadraticPrimeFactorProduct_le_one hs)
    M H (Finset.Icc 1 U) (Finset.Icc 1 V) (fun u v ↦ u * v)
    (by
      intro u hu v hv
      exact (Nat.mul_le_mul (Finset.mem_Icc.mp hu).2
        (Finset.mem_Icc.mp hv).2).trans hUV)
  have hcards :
      ((((Finset.Icc 1 U).card * (Finset.Icc 1 V).card : ℕ) : ℝ)) =
        (U * V : ℕ) := by simp
  rw [hcards] at havg
  calc
    |(((U * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)) -
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + u * v + i))| ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ((2 * (u * v) : ℕ) : ℝ) := havg
    _ ≤ ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
        ((2 * (U * V) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      norm_cast
      exact Nat.mul_le_mul_left 2
        (Nat.mul_le_mul (Finset.mem_Icc.mp hu).2
          (Finset.mem_Icc.mp hv).2)
    _ = (2 : ℝ) * (U * V) ^ 2 := by
      simp
      ring

lemma burgessPrimeSet_natural_numerator_eq_weighted
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    [NeZero (primeSetModulus s)]
    {M H V : ℕ} (hH : H ≤ primeSetModulus s)
    (hV : V < primeSetModulus s) :
    (∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticPrimeFactorProduct s (M + i + u * v)|) =
      ∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetPositiveUnits s hs U hlarge) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x| := by
  rw [← sum_abs_quadraticPrimeSetDilatedShiftSum_eq_weighted]
  exact (sum_abs_quadraticPrimeSetDilatedShiftSum_zmodIntervals
    s hs U hsne hlarge hH hV).symm

/-- Finite amplification inequality for a product of prime quadratic
characters, before Hölder and the complete fourth moment are inserted. -/
lemma burgessPrimeSet_amplified_abs_le_weighted_add_error
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (U : ℕ) (hsne : s.Nonempty) (hlarge : ∀ p ∈ s, U < p)
    [NeZero (primeSetModulus s)]
    {M H V : ℕ} (hH : H ≤ primeSetModulus s)
    (hV : V < primeSetModulus s) (hUV : U * V ≤ H) :
    ((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)| ≤
      (∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetPositiveUnits s hs U hlarge) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x|) +
        (2 : ℝ) * (U * V) ^ 2 := by
  let S : ℝ := ∑ i ∈ Finset.range H,
    quadraticPrimeFactorProduct s (M + i)
  let T : ℝ := ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 V,
    ∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + u * v + i)
  have havg : |(((U * V : ℕ) : ℝ) * S) - T| ≤
      (2 : ℝ) * (U * V) ^ 2 :=
    abs_quadraticPrimeFactorProduct_amplified_sub_shifted_le s hs hUV
  have hT : |T| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
        |∑ v ∈ Finset.Icc 1 V,
          quadraticPrimeFactorProduct s (M + i + u * v)| :=
    abs_burgess_shifted_triple_sum_le_generic
      (quadraticPrimeFactorProduct s) M H U V
  have htri : |(((U * V : ℕ) : ℝ) * S)| ≤
      |(((U * V : ℕ) : ℝ) * S) - T| + |T| := by
    calc
      |(((U * V : ℕ) : ℝ) * S)| =
          |((((U * V : ℕ) : ℝ) * S) - T) + T| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (U * V))] at htri
  change ((U * V : ℕ) : ℝ) * |S| ≤ _
  calc
    ((U * V : ℕ) : ℝ) * |S| ≤
        |(((U * V : ℕ) : ℝ) * S) - T| + |T| := htri
    _ ≤ (2 : ℝ) * (U * V) ^ 2 +
        ∑ i ∈ Finset.range H, ∑ u ∈ Finset.Icc 1 U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticPrimeFactorProduct s (M + i + u * v)| :=
      add_le_add havg hT
    _ = (∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetPositiveUnits s hs U hlarge) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x|) +
        (2 : ℝ) * (U * V) ^ 2 := by
      rw [burgessPrimeSet_natural_numerator_eq_weighted
        s hs U hsne hlarge hH hV]
      ring

lemma localQuadraticQuarticBound_nonneg
    (p : ℕ) (v : Fin 4 → ZMod p) :
    0 ≤ localQuadraticQuarticBound p v := by
  classical
  rw [localQuadraticQuarticBound]
  split_ifs <;> positivity

lemma quadraticPrimeSetQuarticBound_nonneg
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (v : Fin 4 → ZMod (primeSetModulus s)) :
    0 ≤ quadraticPrimeSetQuarticBound s hs v := by
  rw [quadraticPrimeSetQuarticBound]
  exact Finset.prod_nonneg fun p hp ↦ localQuadraticQuarticBound_nonneg _ _

/-- Complete finite `r = 2` Burgess amplification bound for the quadratic
character of a squarefree product of primes.  The exact local-collision sum
is left visible for the subsequent divisor estimate. -/
lemma burgessPrimeSet_amplified_fourth_bound
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hsne : s.Nonempty) {M H U V : ℕ}
    (hH : 0 < H) (hU₀ : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hlarge : ∀ p ∈ s, U < p)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    ((((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
      8 *
        (((((H * U : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (∑ v : Fin 4 →
              ↥(zmodPositiveInterval (primeSetModulus s) V),
            quadraticPrimeSetQuarticBound s hs
              (fun i ↦ (v i : ZMod (primeSetModulus s))))) +
          ((2 : ℝ) * (U * V) ^ 2) ^ 4) := by
  letI : NeZero (primeSetModulus s) :=
    ⟨(primeSetModulus_pos s hs).ne'⟩
  letI (p : s) : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  let B : ℝ := ∑ x : ZMod (primeSetModulus s),
    (burgessUnitRatioWeight
      (zmodNatInterval (primeSetModulus s) M H)
      (primeSetPositiveUnits s hs U hlarge) x : ℝ) *
      |quadraticPrimeSetShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V) x|
  let E : ℝ := (2 : ℝ) * (U * V) ^ 2
  let X : ℝ := ((U * V : ℕ) : ℝ) *
    |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)|
  let Q : ℝ := ∑ v : Fin 4 →
      ↥(zmodPositiveInterval (primeSetModulus s) V),
    quadraticPrimeSetQuarticBound s hs
      (fun i ↦ (v i : ZMod (primeSetModulus s)))
  have hXB : X ≤ B + E := by
    exact burgessPrimeSet_amplified_abs_le_weighted_add_error
      s hs U hsne hlarge hHq hVq hUV
  have hX₀ : 0 ≤ X := by positivity
  have hpow : X ^ 4 ≤ (B + E) ^ 4 :=
    pow_le_pow_left₀ hX₀ hXB 4
  have hadd := add_pow_four_le_eight B E
  have hweighted₀ := burgessUnit_weighted_fourth_bound
    (zmodNatInterval (primeSetModulus s) M H)
    (primeSetPositiveUnits s hs U hlarge)
    (quadraticPrimeSetShiftSum s hs
      (zmodPositiveInterval (primeSetModulus s) V))
  rw [zmodNatInterval_card hHq,
    primeSetPositiveUnits_card s hs U hsne hlarge] at hweighted₀
  have hmoment := quadraticPrimeSetShiftSum_fourth_moment_le
    s hs (zmodPositiveInterval (primeSetModulus s) V)
  have hleftnonneg : 0 ≤ ((H * U : ℕ) : ℝ) ^ 2 *
      burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetPositiveUnits s hs U hlarge) := by
    exact mul_nonneg (sq_nonneg _)
      (burgessUnitRatioEnergy_nonneg _ _)
  have hweighted : B ^ 4 ≤
      ((H * U : ℕ) : ℝ) ^ 2 *
        burgessUnitRatioEnergy
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetPositiveUnits s hs U hlarge) * Q := by
    exact hweighted₀.trans
      (mul_le_mul_of_nonneg_left hmoment hleftnonneg)
  have henergy := burgessUnitRatioEnergy_primeSetIntervals_le
    s hs U hsne hlarge hH hU₀ hHq hsmall (M := M)
  have hQ₀ : 0 ≤ Q := by
    dsimp only [Q]
    exact Finset.sum_nonneg fun v hv ↦
      quadraticPrimeSetQuarticBound_nonneg s hs _
  have hweighted' : B ^ 4 ≤
      ((H * U : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) * Q := by
    calc
      B ^ 4 ≤ ((H * U : ℕ) : ℝ) ^ 2 *
          burgessUnitRatioEnergy
            (zmodNatInterval (primeSetModulus s) M H)
            (primeSetPositiveUnits s hs U hlarge) * Q := hweighted
      _ ≤ ((H * U : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) * Q := by
        gcongr
  calc
    X ^ 4 ≤ (B + E) ^ 4 := hpow
    _ ≤ 8 * (B ^ 4 + E ^ 4) := hadd
    _ ≤ 8 *
        (((((H * U : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) * Q) + E ^ 4) := by
      gcongr
    _ = _ := by rfl

/-- The composite Burgess bound with all CRT correlation costs evaluated.
The hypotheses `hlarge` and `hshift` ensure that both amplifier denominators
and shifts are shorter than every prime factor. -/
lemma burgessPrimeSet_amplified_fourth_bound_explicit
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hsne : s.Nonempty) {M H U V : ℕ}
    (hH : 0 < H) (hU₀ : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hlarge : ∀ p ∈ s, U < p)
    (hshift : ∀ p ∈ s, V < p)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    ((((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
      8 *
        (((((H * U : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
              ((3 : ℝ) ^ s.card *
                Real.sqrt (primeSetModulus s)))) +
          ((2 : ℝ) * (U * V) ^ 2) ^ 4) := by
  calc
    ((((U * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
        8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (∑ v : Fin 4 →
                ↥(zmodPositiveInterval (primeSetModulus s) V),
              quadraticPrimeSetQuarticBound s hs
                (fun i ↦ (v i : ZMod (primeSetModulus s))))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) :=
      burgessPrimeSet_amplified_fourth_bound s hs hsne hH hU₀
        hHq hVq hlarge hUV hsmall
    _ ≤ _ := by
      gcongr
      exact quadraticPrimeSetQuarticBound_sum_le
        s hs hodd hshift hVq

/-- A directly usable strict character-sum consequence of the explicit
composite Burgess inequality. -/
lemma abs_quadraticPrimeFactorProduct_sum_lt_of_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hsne : s.Nonempty) {M H U V : ℕ} {B : ℝ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hB : 0 ≤ B)
    (hHq : H ≤ primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hlarge : ∀ p ∈ s, U < p)
    (hshift : ∀ p ∈ s, V < p)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hstrict :
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * B) ^ 4) :
    |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + i)| < B := by
  have hbound := burgessPrimeSet_amplified_fourth_bound_explicit
    s hs hsne hH hU₀ hHq hVq hlarge hshift hodd hUV hsmall (M := M)
  have hpow :
      ((((U * V : ℕ) : ℝ) *
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct s (M + i)|) ^ 4) <
        (((U * V : ℕ) : ℝ) * B) ^ 4 := hbound.trans_lt hstrict
  have hlt :
      ((U * V : ℕ) : ℝ) *
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct s (M + i)| <
        ((U * V : ℕ) : ℝ) * B := by
    exact lt_of_pow_lt_pow_left₀ 4 (mul_nonneg (by positivity) hB) hpow
  have hUVpos : (0 : ℝ) < ((U * V : ℕ) : ℝ) := by
    positivity
  nlinarith

noncomputable section

/-- Positive integers at most `U` which are units modulo the prime-set
conductor. -/
def primeSetCoprimeDenominators (s : Finset ℕ) (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ u.Coprime (primeSetModulus s)

/-- Multiples of `p` in the finite interval used to count admissible
Burgess denominators. -/
def primeSetMultiplesInIcc (U p : ℕ) : Finset ↥(Finset.Icc 1 U) :=
  Finset.univ.filter fun u ↦ p ∣ (u : ℕ)

lemma prod_dvd_iff_all_prime_dvd
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (n : ℕ) :
    (∏ p ∈ t, p) ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        have hp : p.Prime := ht p (Finset.mem_insert_self p t)
        have hcop : p.Coprime (∏ r ∈ t, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hp
            (ht r (Finset.mem_insert_of_mem hr))).mpr
            (Ne.symm (ne_of_mem_of_not_mem hr hpt))
        exact hcop.mul_dvd_of_dvd_of_dvd
          (h p (Finset.mem_insert_self p t))
          (ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
            (fun r hr ↦ h r (Finset.mem_insert_of_mem hr)))

lemma card_inf_primeSetMultiplesInIcc
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (U : ℕ) :
    (t.inf (primeSetMultiplesInIcc U)).card =
      U / (∏ p ∈ t, p) := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_bij
    (s := t.inf (primeSetMultiplesInIcc U))
    (t := (Finset.Ioc 0 U).filter fun n ↦ (∏ p ∈ t, p) ∣ n)
    (fun (u : ↥(Finset.Icc 1 U)) _hu ↦ (u : ℕ)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp u.property)
    · rw [prod_dvd_iff_all_prime_dvd t ht]
      intro p hp
      have hu' : ∀ p ∈ t, u ∈ primeSetMultiplesInIcc U p := by
        simpa only [Finset.mem_inf] using hu
      have hup : u ∈ primeSetMultiplesInIcc U p := hu' p hp
      simpa [primeSetMultiplesInIcc] using hup
  · intro u₁ h₁ u₂ h₂ huv
    exact Subtype.ext huv
  · intro n hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    let u : ↥(Finset.Icc 1 U) :=
      ⟨n, Finset.mem_Icc.mpr (Finset.mem_Ioc.mp hnIoc)⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_inf]
    intro p hp
    simp only [primeSetMultiplesInIcc, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (prod_dvd_iff_all_prime_dvd t ht n).mp
      (Finset.mem_filter.mp hn).2 p hp

lemma inf_compl_primeSetMultiples_eq_coprime
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    s.inf (fun p ↦ (primeSetMultiplesInIcc U p)ᶜ) =
      (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
        (fun (u : ↥(Finset.Icc 1 U)) ↦
          (u : ℕ).Coprime (primeSetModulus s)) := by
  ext u
  simp only [Finset.mem_inf, Finset.mem_compl,
    primeSetMultiplesInIcc, Finset.mem_filter, Finset.mem_univ,
    true_and, primeSetModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd]
    exact h p hp
  · intro h p hp hdiv
    have hpco := h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd] at hpco
    exact hpco hdiv

/-- Inclusion--exclusion formula for the positive denominators coprime to a
squarefree prime-set conductor. -/
lemma card_primeSetCoprimeDenominators_eq_alternating
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    ((primeSetCoprimeDenominators s U).card : ℤ) =
      ∑ t ∈ s.powerset,
        (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
  have hIE := Finset.inclusion_exclusion_card_inf_compl s
    (primeSetMultiplesInIcc U)
  calc
    ((primeSetCoprimeDenominators s U).card : ℤ) =
        (((Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeSetModulus s))).card : ℤ) := by
      apply congrArg (fun n : ℕ ↦ (n : ℤ))
      refine Finset.card_bij
        (s := primeSetCoprimeDenominators s U)
        (t := (Finset.univ : Finset ↥(Finset.Icc 1 U)).filter
          (fun (u : ↥(Finset.Icc 1 U)) ↦
            (u : ℕ).Coprime (primeSetModulus s)))
        (fun n hn ↦ ⟨n, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_filter.mp hn).1
      · intro n hn
        simpa [primeSetCoprimeDenominators] using
          (Finset.mem_filter.mp hn).2
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro u hu
        refine ⟨u, ?_, Subtype.ext rfl⟩
        simpa [primeSetCoprimeDenominators] using
          (Finset.mem_filter.mp hu).2
    _ = ((s.inf fun p ↦ (primeSetMultiplesInIcc U p)ᶜ).card : ℤ) := by
      rw [inf_compl_primeSetMultiples_eq_coprime s hs U]
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card *
            ((t.inf (primeSetMultiplesInIcc U)).card : ℤ) := hIE
    _ = ∑ t ∈ s.powerset,
          (-1 : ℤ) ^ t.card * (U / (∏ p ∈ t, p) : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_inf_primeSetMultiplesInIcc t
        (fun p hp ↦ hs p (Finset.mem_powerset.mp ht hp)) U]

lemma alternating_prime_reciprocal_eq
    (s : Finset ℕ) (U : ℕ) :
    (∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))) =
      (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_inv_distrib]
  simp only [Nat.cast_prod]
  ring

lemma half_le_one_sub_prime_inv {p : ℕ} (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hp2
  norm_num at hinv ⊢
  linarith

lemma prod_one_sub_prime_inv_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / 2 : ℝ) ^ s.card ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun p hp ↦ by positivity)
    (fun p hp ↦ half_le_one_sub_prime_inv (hs p hp))

lemma abs_natCast_div_sub_div_lt_one (U d : ℕ) :
    |((U / d : ℕ) : ℝ) - (U : ℝ) / (d : ℝ)| < 1 := by
  have hle : ((U / d : ℕ) : ℝ) ≤ (U : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hlt : (U : ℝ) / (d : ℝ) < ((U / d : ℕ) : ℝ) + 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.lt_floor_add_one ((U : ℝ) / (d : ℝ)))
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

lemma alternating_prime_floor_sum_error
    (s : Finset ℕ) (U : ℕ) :
    |(∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)) -
      ∑ t ∈ s.powerset,
        (-1 : ℝ) ^ t.card *
          ((U : ℝ) / (∏ p ∈ t, p : ℕ))| ≤
        (2 : ℝ) ^ s.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
          (-1 : ℝ) ^ t.card *
            ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| ≤
        ∑ t ∈ s.powerset,
          |((-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ) -
            (-1 : ℝ) ^ t.card *
              ((U : ℝ) / (∏ p ∈ t, p : ℕ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul, abs_neg_one_pow]
      simpa only [one_mul] using
        (abs_natCast_div_sub_div_lt_one U (∏ p ∈ t, p)).le
    _ = (2 : ℝ) ^ s.card := by simp

/-- Crude uniform lower bound for the number of Burgess denominators.  The
main term loses at most one half per conductor prime; the
inclusion--exclusion floor errors cost at most the number of subsets. -/
lemma card_primeSetCoprimeDenominators_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ) :
    (U : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
      (primeSetCoprimeDenominators s U).card := by
  let F : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U / (∏ p ∈ t, p) : ℕ) : ℝ)
  let R : ℝ := ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * ((U : ℝ) / (∏ p ∈ t, p : ℕ))
  have hcount : ((primeSetCoprimeDenominators s U).card : ℝ) = F := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (card_primeSetCoprimeDenominators_eq_alternating s hs U)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have herror : |F - R| ≤ (2 : ℝ) ^ s.card :=
    alternating_prime_floor_sum_error s U
  have hR : (U : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) = R :=
    (alternating_prime_reciprocal_eq s U).symm
  have hprod : (U : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ R := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left
      (prod_one_sub_prime_inv_lower s hs) (by positivity)
  have hRF : R - F ≤ (2 : ℝ) ^ s.card := by
    calc
      R - F ≤ |R - F| := le_abs_self _
      _ = |F - R| := abs_sub_comm _ _
      _ ≤ (2 : ℝ) ^ s.card := herror
  rw [hcount]
  linarith

/-- Multiples of `p` among the indices of the translated interval
`M, ..., M + H - 1`. -/
def primeSetMultiplesInRange (M H p : ℕ) : Finset ↑(Finset.range H) :=
  Finset.univ.filter fun i ↦ p ∣ M + (i : ℕ)

/-- Indices for which the translated interval value is a unit modulo the
prime-set conductor. -/
def shiftedPrimeSetCoprimeIndices (s : Finset ℕ) (M H : ℕ) : Finset ℕ :=
  (Finset.range H).filter fun i ↦ (M + i).Coprime (primeSetModulus s)

lemma card_filter_range_modEq_bounds (H d v : ℕ) (hd : 0 < d) :
    H / d ≤ ((Finset.range H).filter fun i ↦ i ≡ v [MOD d]).card ∧
      ((Finset.range H).filter fun i ↦ i ≡ v [MOD d]).card ≤ H / d + 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card H hd v]
  split_ifs <;> omega

lemma card_filter_range_dvd_add_bounds (M H d : ℕ) (hd : 0 < d) :
    H / d ≤ ((Finset.range H).filter fun i ↦ d ∣ M + i).card ∧
      ((Finset.range H).filter fun i ↦ d ∣ M + i).card ≤ H / d + 1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  let v : ℕ := (-(M : ZMod d)).val
  have hv : (v : ZMod d) = -(M : ZMod d) := ZMod.natCast_zmod_val _
  have hequiv (i : ℕ) : d ∣ M + i ↔ i ≡ v [MOD d] := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [← ZMod.natCast_eq_natCast_iff]
    constructor
    · intro hz
      calc
        (i : ZMod d) = (i : ZMod d) + ((M : ZMod d) + -(M : ZMod d)) := by ring
        _ = ((M + i : ℕ) : ZMod d) + -(M : ZMod d) := by push_cast; ring
        _ = -(M : ZMod d) := by rw [hz]; simp
        _ = (v : ZMod d) := hv.symm
    · intro hiv
      calc
        ((M + i : ℕ) : ZMod d) = (M : ZMod d) + (i : ZMod d) := by
          push_cast
          ring
        _ = (M : ZMod d) + (v : ZMod d) := by rw [hiv]
        _ = 0 := by rw [hv]; ring
  have heq :
      ((Finset.range H).filter fun i ↦ d ∣ M + i) =
        ((Finset.range H).filter fun i ↦ i ≡ v [MOD d]) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hequiv]
  rw [heq]
  exact card_filter_range_modEq_bounds H d v hd

/-- Number of members of the residue class `a mod d` lying in `[0,H)`,
under the canonical assumption `a < d`. -/
def residueClassLength (H d a : ℕ) : ℕ :=
  if a < H then (H + d - 1 - a) / d else 0

lemma lt_residueClassLength_iff
    {H d a j : ℕ} (hd : 0 < d) (ha : a < H) :
    j < residueClassLength H d a ↔ a + d * j < H := by
  rw [residueClassLength, if_pos ha, Nat.lt_div_iff_mul_lt hd]
  have heq : H + d - 1 - a - (d - 1) = H - a := by omega
  rw [heq, Nat.mul_comm j d]
  omega

lemma residueClassLength_eq_zero_of_le
    {H d a : ℕ} (ha : H ≤ a) : residueClassLength H d a = 0 := by
  simp [residueClassLength, Nat.not_lt.mpr ha]

/-- Explicit enumeration of the indices in a fixed divisibility class. -/
lemma filter_range_dvd_add_eq_image_residueClass
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (Finset.range H).filter (fun i ↦ d ∣ M + i) =
      (Finset.range (residueClassLength H d a)).image (fun j ↦ a + d * j) := by
  ext i
  constructor
  · intro hi
    have hiH := (Finset.mem_filter.mp hi).1
    have hMi := (Finset.mem_filter.mp hi).2
    have hmod : i ≡ a [MOD d] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have hMiz : ((M + i : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + i) d).mpr hMi
      have hMaz : ((M + a : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + a) d).mpr hMa
      calc
        (i : ZMod d) = ((M + i : ℕ) : ZMod d) - (M : ZMod d) := by
          push_cast
          ring
        _ = -(M : ZMod d) := by rw [hMiz]; ring
        _ = ((M + a : ℕ) : ZMod d) - (M : ZMod d) := by rw [hMaz]; ring
        _ = (a : ZMod d) := by push_cast; ring
    have himod : i % d = a := Nat.mod_eq_of_modEq hmod ha
    let j := i / d
    have hij : i = a + d * j := by
      dsimp [j]
      calc
        i = d * (i / d) + i % d := (Nat.div_add_mod i d).symm
        _ = d * (i / d) + a := by rw [himod]
        _ = a + d * (i / d) := by omega
    have hai : a ≤ i := by rw [hij]; exact Nat.le_add_right _ _
    have haH : a < H := hai.trans_lt (Finset.mem_range.mp hiH)
    have hj : j < residueClassLength H d a :=
      (lt_residueClassLength_iff hd haH).mpr (by
        rw [← hij]
        exact Finset.mem_range.mp hiH)
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, hij.symm⟩
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have haH : a < H := by
      by_contra h
      have hz := residueClassLength_eq_zero_of_le
        (d := d) (Nat.le_of_not_gt h)
      rw [Finset.mem_range, hz] at hj
      omega
    have hlt : a + d * j < H :=
      (lt_residueClassLength_iff hd haH).mp (Finset.mem_range.mp hj)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hlt
    · obtain ⟨c, hc⟩ := hMa
      refine ⟨c + j, ?_⟩
      calc
        M + (a + d * j) = (M + a) + d * j := by omega
        _ = d * c + d * j := by rw [hc]
        _ = d * (c + j) := by ring

lemma sum_ite_dvd_eq_residueClass
    (f : ℕ → ℝ) {M H d a : ℕ}
    (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (∑ i ∈ Finset.range H, if d ∣ M + i then f (M + i) else 0) =
      ∑ j ∈ Finset.range (residueClassLength H d a),
        f (M + (a + d * j)) := by
  rw [← Finset.sum_filter]
  rw [filter_range_dvd_add_eq_image_residueClass hd ha hMa]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)

lemma residueClassLength_le_div_add_one
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    residueClassLength H d a ≤ H / d + 1 := by
  have heq := filter_range_dvd_add_eq_image_residueClass
    (M := M) (H := H) hd ha hMa
  have hinj : Function.Injective (fun j : ℕ ↦ a + d * j) := by
    intro x y hxy
    exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)
  have hcard :
      residueClassLength H d a =
        ((Finset.range H).filter (fun i ↦ d ∣ M + i)).card := by
    rw [heq, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  exact (card_filter_range_dvd_add_bounds M H d hd).2

lemma residueClassLength_le
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    residueClassLength H d a ≤ H := by
  have heq := filter_range_dvd_add_eq_image_residueClass
    (M := M) (H := H) hd ha hMa
  have hinj : Function.Injective (fun j : ℕ ↦ a + d * j) := by
    intro x y hxy
    exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)
  have hcard :
      residueClassLength H d a =
        ((Finset.range H).filter (fun i ↦ d ∣ M + i)).card := by
    rw [heq, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- A divisibility-restricted sum of a completely multiplicative real
function is, up to the constant factor at `d`, an ordinary consecutive sum
of length at most `H / d + 1`. -/
lemma exists_divisible_sum_factorization
    (f : ℕ → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H d : ℕ) (hd : 0 < d) :
    ∃ K L : ℕ, L ≤ H ∧ L ≤ H / d + 1 ∧
      (∑ i ∈ Finset.range H,
        if d ∣ M + i then f (M + i) else 0) =
        f d * ∑ j ∈ Finset.range L, f (K + j) := by
  letI : NeZero d := ⟨hd.ne'⟩
  let a : ℕ := (-(M : ZMod d)).val
  let K : ℕ := (M + a) / d
  let L : ℕ := residueClassLength H d a
  have ha : a < d := ZMod.val_lt _
  have hMa : d ∣ M + a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    change (M : ZMod d) + (a : ZMod d) = 0
    rw [show (a : ZMod d) = -(M : ZMod d) by
      exact ZMod.natCast_zmod_val _]
    ring
  have hK : d * K = M + a := Nat.mul_div_cancel' hMa
  refine ⟨K, L, residueClassLength_le hd ha hMa,
    residueClassLength_le_div_add_one hd ha hMa, ?_⟩
  rw [sum_ite_dvd_eq_residueClass f hd ha hMa]
  calc
    (∑ j ∈ Finset.range L, f (M + (a + d * j))) =
        ∑ j ∈ Finset.range L, f (d * (K + j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          calc
            M + (a + d * j) = (M + a) + d * j := by omega
            _ = d * K + d * j := by rw [hK]
            _ = d * (K + j) := by ring
    _ = ∑ j ∈ Finset.range L, f d * f (K + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hmul d (K + j)
    _ = f d * ∑ j ∈ Finset.range L, f (K + j) := by
      rw [Finset.mul_sum]

/-- Bounding a divisibility-restricted quadratic character sum reduces to a
uniform bound for shorter consecutive sums of the same character. -/
lemma abs_divisible_quadraticPrimeFactorProduct_sum_le
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime)
    (M H d : ℕ) (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B)
    (hinterval : ∀ K L : ℕ, L ≤ H → L ≤ H / d + 1 →
      |∑ j ∈ Finset.range L,
        quadraticPrimeFactorProduct t (K + j)| ≤ B) :
    |∑ i ∈ Finset.range H,
      if d ∣ M + i then quadraticPrimeFactorProduct t (M + i) else 0| ≤ B := by
  obtain ⟨K, L, hLH, hL, heq⟩ := exists_divisible_sum_factorization
    (quadraticPrimeFactorProduct t) (quadraticPrimeFactorProduct_mul ht)
    M H d hd
  rw [heq, abs_mul]
  calc
    |quadraticPrimeFactorProduct t d| *
        |∑ j ∈ Finset.range L,
          quadraticPrimeFactorProduct t (K + j)| ≤
      1 * B := mul_le_mul
        (abs_quadraticPrimeFactorProduct_le_one ht d)
        (hinterval K L hLH hL) (abs_nonneg _) zero_le_one
    _ = B := by ring

lemma card_inf_primeSetMultiplesInRange
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (M H : ℕ) :
    (t.inf (primeSetMultiplesInRange M H)).card =
      ((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card := by
  refine Finset.card_bij
    (s := t.inf (primeSetMultiplesInRange M H))
    (t := (Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i)
    (fun (u : ↑(Finset.range H)) _hu ↦ (u : ℕ)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter]
    constructor
    · exact u.property
    · rw [prod_dvd_iff_all_prime_dvd t ht]
      intro p hp
      have hu' : ∀ p ∈ t, u ∈ primeSetMultiplesInRange M H p := by
        simpa only [Finset.mem_inf] using hu
      have hup := hu' p hp
      simpa [primeSetMultiplesInRange] using hup
  · intro u₁ h₁ u₂ h₂ huv
    exact Subtype.ext huv
  · intro i hi
    let u : ↑(Finset.range H) := ⟨i, (Finset.mem_filter.mp hi).1⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_inf]
    intro p hp
    simp only [primeSetMultiplesInRange, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (prod_dvd_iff_all_prime_dvd t ht (M + i)).mp
      (Finset.mem_filter.mp hi).2 p hp

lemma inf_compl_primeSetMultiplesInRange_eq_coprime
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ) :
    s.inf (fun p ↦ (primeSetMultiplesInRange M H p)ᶜ) =
      (Finset.univ : Finset ↑(Finset.range H)).filter
        (fun i : ↑(Finset.range H) ↦
          (M + (i : ℕ)).Coprime (primeSetModulus s)) := by
  ext i
  simp only [Finset.mem_inf, Finset.mem_compl,
    primeSetMultiplesInRange, Finset.mem_filter, Finset.mem_univ,
    true_and, primeSetModulus, Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd]
    exact h p hp
  · intro h p hp hdiv
    have hpco := h p hp
    rw [Nat.coprime_comm, (hs p hp).coprime_iff_not_dvd] at hpco
    exact hpco hdiv

/-- Inclusion--exclusion for units in an arbitrary translated interval. -/
lemma card_shiftedPrimeSetCoprimeIndices_eq_alternating
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ) :
    ((shiftedPrimeSetCoprimeIndices s M H).card : ℤ) =
      ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card *
        (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℤ) := by
  have hIE := Finset.inclusion_exclusion_card_inf_compl s
    (primeSetMultiplesInRange M H)
  calc
    ((shiftedPrimeSetCoprimeIndices s M H).card : ℤ) =
        (((Finset.univ : Finset ↑(Finset.range H)).filter
          (fun i : ↑(Finset.range H) ↦
            (M + (i : ℕ)).Coprime (primeSetModulus s))).card : ℤ) := by
      apply congrArg (fun n : ℕ ↦ (n : ℤ))
      refine Finset.card_bij
        (s := shiftedPrimeSetCoprimeIndices s M H)
        (t := (Finset.univ : Finset ↑(Finset.range H)).filter
          (fun i : ↑(Finset.range H) ↦
            (M + (i : ℕ)).Coprime (primeSetModulus s)))
        (fun n hn ↦ ⟨n, ?_⟩) ?_ ?_ ?_
      · exact (Finset.mem_filter.mp hn).1
      · intro n hn
        simpa [shiftedPrimeSetCoprimeIndices] using (Finset.mem_filter.mp hn).2
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro i hi
        refine ⟨i, ?_, Subtype.ext rfl⟩
        simpa [shiftedPrimeSetCoprimeIndices] using (Finset.mem_filter.mp hi).2
    _ = ((s.inf fun p ↦ (primeSetMultiplesInRange M H p)ᶜ).card : ℤ) := by
      rw [inf_compl_primeSetMultiplesInRange_eq_coprime s hs M H]
    _ = ∑ t ∈ s.powerset, (-1 : ℤ) ^ t.card *
          ((t.inf (primeSetMultiplesInRange M H)).card : ℤ) := hIE
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [card_inf_primeSetMultiplesInRange t
        (fun p hp ↦ hs p (Finset.mem_powerset.mp ht hp)) M H]

lemma shifted_prime_floor_sum_error
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ) :
    |(∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
        (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ)) -
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
        ((H : ℝ) / (∏ p ∈ t, p : ℕ))| ≤ (2 : ℝ) ^ s.card := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card *
            (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ) -
          (-1 : ℝ) ^ t.card * ((H : ℝ) / (∏ p ∈ t, p : ℕ)))| ≤
      ∑ t ∈ s.powerset,
        |((-1 : ℝ) ^ t.card *
            (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ) -
          (-1 : ℝ) ^ t.card * ((H : ℝ) / (∏ p ∈ t, p : ℕ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← mul_sub, abs_mul, abs_neg_one_pow, one_mul]
      have htp : 0 < ∏ p ∈ t, p := Finset.prod_pos
        (fun p hp ↦ (hs p (Finset.mem_powerset.mp ht hp)).pos)
      have hb := card_filter_range_dvd_add_bounds M H (∏ p ∈ t, p) htp
      have hfloor : (((H / (∏ p ∈ t, p) : ℕ) : ℝ)) ≤
          (H : ℝ) / (∏ p ∈ t, p : ℕ) := Nat.cast_div_le
      have hfloor' : (H : ℝ) / (∏ p ∈ t, p : ℕ) <
          ((H / (∏ p ∈ t, p) : ℕ) : ℝ) + 1 := by
        simpa only [Nat.floor_div_eq_div] using
          (Nat.lt_floor_add_one ((H : ℝ) / (∏ p ∈ t, p : ℕ)))
      have hbR₁ : ((H / (∏ p ∈ t, p) : ℕ) : ℝ) ≤
          (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ) := by
        exact_mod_cast hb.1
      have hbR₂ :
          (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ) ≤
            ((H / (∏ p ∈ t, p) : ℕ) : ℝ) + 1 := by
        exact_mod_cast hb.2
      rw [abs_le]
      constructor <;> linarith
    _ = (2 : ℝ) ^ s.card := by simp

/-- The unit count in any translated interval has the expected elementary
sieve main term, with at most one endpoint error per squarefree divisor. -/
lemma card_shiftedPrimeSetCoprimeIndices_lower
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ) :
    (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
      (shiftedPrimeSetCoprimeIndices s M H).card := by
  let F : ℝ := ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
    (((Finset.range H).filter fun i ↦ (∏ p ∈ t, p) ∣ M + i).card : ℝ)
  let R : ℝ := ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card *
    ((H : ℝ) / (∏ p ∈ t, p : ℕ))
  have hcount : ((shiftedPrimeSetCoprimeIndices s M H).card : ℝ) = F := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ))
      (card_shiftedPrimeSetCoprimeIndices_eq_alternating s hs M H)
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have herror : |F - R| ≤ (2 : ℝ) ^ s.card :=
    shifted_prime_floor_sum_error s hs M H
  have hR : (H : ℝ) * ∏ p ∈ s, (1 - (p : ℝ)⁻¹) = R :=
    (alternating_prime_reciprocal_eq s H).symm
  have hprod : (H : ℝ) * (1 / 2 : ℝ) ^ s.card ≤ R := by
    rw [← hR]
    exact mul_le_mul_of_nonneg_left
      (prod_one_sub_prime_inv_lower s hs) (by positivity)
  have hRF : R - F ≤ (2 : ℝ) ^ s.card := by
    calc
      R - F ≤ |R - F| := le_abs_self _
      _ = |F - R| := abs_sub_comm _ _
      _ ≤ (2 : ℝ) ^ s.card := herror
  rw [hcount]
  linarith

/-- Real-valued indicator that a prime divides an integer. -/
noncomputable def primeDivisibilityIndicator (p n : ℕ) : ℝ :=
  if p ∣ n then 1 else 0

lemma prod_primeDivisibilityIndicator
    (u : Finset ℕ) (hu : ∀ p ∈ u, p.Prime) (n : ℕ) :
    ∏ p ∈ u, primeDivisibilityIndicator p n =
      if (∏ p ∈ u, p) ∣ n then 1 else 0 := by
  by_cases h : (∏ p ∈ u, p) ∣ n
  · rw [if_pos h]
    have hall := (prod_dvd_iff_all_prime_dvd u hu n).mp h
    apply Finset.prod_eq_one
    intro p hp
    simp [primeDivisibilityIndicator, hall p hp]
  · rw [if_neg h]
    have hnall : ¬ ∀ p ∈ u, p ∣ n := by
      rwa [← prod_dvd_iff_all_prime_dvd u hu n]
    push_neg at hnall
    obtain ⟨p, hp, hpd⟩ := hnall
    apply Finset.prod_eq_zero hp
    simp [primeDivisibilityIndicator, hpd]

lemma alternating_dvd_indicator_eq_prod
    (r : Finset ℕ) (hr : ∀ p ∈ r, p.Prime) (n : ℕ) :
    (∑ u ∈ r.powerset, (-1 : ℝ) ^ u.card *
      (if (∏ p ∈ u, p) ∣ n then 1 else 0)) =
      ∏ p ∈ r, (1 - primeDivisibilityIndicator p n) := by
  calc
    (∑ u ∈ r.powerset, (-1 : ℝ) ^ u.card *
      (if (∏ p ∈ u, p) ∣ n then 1 else 0)) =
      ∑ u ∈ r.powerset, (-1 : ℝ) ^ u.card *
        ∏ p ∈ u, primeDivisibilityIndicator p n := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [prod_primeDivisibilityIndicator u
            (fun p hp ↦ hr p (Finset.mem_powerset.mp hu hp)) n]
    _ = ∏ p ∈ r, ((1 : ℝ) - primeDivisibilityIndicator p n) := by
      rw [Finset.prod_sub]
      simp only [Finset.prod_const_one, mul_one]

lemma alternating_dvd_indicator
    (r : Finset ℕ) (hr : ∀ p ∈ r, p.Prime) (n : ℕ) :
    (∑ u ∈ r.powerset, (-1 : ℝ) ^ u.card *
      (if (∏ p ∈ u, p) ∣ n then 1 else 0)) =
      if n.Coprime (primeSetModulus r) then 1 else 0 := by
  rw [alternating_dvd_indicator_eq_prod r hr n]
  by_cases hcop : n.Coprime (primeSetModulus r)
  · rw [if_pos hcop]
    apply Finset.prod_eq_one
    intro p hp
    have hnp : ¬ p ∣ n := by
      have hpco : n.Coprime p :=
        hcop.of_dvd_right (dvd_primeSetModulus hp)
      exact ((hr p hp).coprime_iff_not_dvd).mp hpco.symm
    simp [primeDivisibilityIndicator, hnp]
  · rw [if_neg hcop]
    obtain ⟨p, hpprime, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpqmem : p ∈ (primeSetModulus r).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hpprime, hpq, (primeSetModulus_pos r hr).ne'⟩
    have hpr : p ∈ r := by
      rwa [primeFactors_primeSetModulus r hr] at hpqmem
    apply Finset.prod_eq_zero hpr
    simp [primeDivisibilityIndicator, hpn]

/-- Exact inclusion--exclusion expansion of a quadratic product restricted
to units modulo a larger squarefree prime-set conductor. -/
lemma restrictedQuadraticPrimeFactorProduct_eq_alternating
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hts : t ⊆ s) (n : ℕ) :
    restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t n =
      ∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
        (if (∏ p ∈ u, p) ∣ n then quadraticPrimeFactorProduct t n else 0) := by
  have hdisj : Disjoint (s \ t) t := Finset.sdiff_disjoint
  have hprod : primeSetModulus s =
      primeSetModulus (s \ t) * primeSetModulus t := by
    rw [primeSetModulus, primeSetModulus, primeSetModulus]
    rw [← Finset.prod_union hdisj]
    congr 2
    exact (Finset.sdiff_union_of_subset hts).symm
  have hrt : ∀ p ∈ s \ t, p.Prime :=
    fun p hp ↦ hs p (Finset.mem_sdiff.mp hp).1
  rw [restrictedQuadraticPrimeFactorProduct]
  rw [show (∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
        (if (∏ p ∈ u, p) ∣ n then quadraticPrimeFactorProduct t n else 0)) =
      quadraticPrimeFactorProduct t n *
        (∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
          (if (∏ p ∈ u, p) ∣ n then 1 else 0)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hd : (∏ p ∈ u, p) ∣ n <;> simp [hd] <;> ring]
  rw [alternating_dvd_indicator (s \ t) hrt n]
  by_cases hcop : n.Coprime (primeSetModulus s)
  · rw [if_pos hcop]
    have hcopr : n.Coprime (primeSetModulus (s \ t)) := by
      rw [hprod] at hcop
      exact (Nat.coprime_mul_iff_right.mp hcop).1
    rw [if_pos hcopr, mul_one]
  · rw [if_neg hcop]
    by_cases hcopr : n.Coprime (primeSetModulus (s \ t))
    · rw [if_pos hcopr, mul_one]
      have hnott : ¬ n.Coprime (primeSetModulus t) := by
        intro ht
        apply hcop
        rw [hprod]
        exact (Nat.coprime_mul_iff_right).mpr ⟨hcopr, ht⟩
      have hzero : quadraticPrimeFactorProduct t n = 0 := by
        obtain ⟨p, hpprime, hpn, hpq⟩ :=
          Nat.Prime.not_coprime_iff_dvd.mp hnott
        have hpqmem : p ∈ (primeSetModulus t).primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨hpprime, hpq,
            (primeSetModulus_pos t (fun p hp ↦ hs p (hts hp))).ne'⟩
        have hpt : p ∈ t := by
          rwa [primeFactors_primeSetModulus t
            (fun p hp ↦ hs p (hts hp))] at hpqmem
        letI : Fact p.Prime := ⟨hpprime⟩
        rw [quadraticPrimeFactorProduct, Finset.prod_eq_zero hpt]
        rw [primeQuadraticCharReal_of_prime hpprime]
        change (((quadraticChar (ZMod p)) (n : ZMod p) : ℤ) : ℝ) = 0
        exact_mod_cast
          (quadraticChar_eq_zero_iff.mpr
            ((ZMod.natCast_eq_zero_iff n p).mpr hpn))
      exact hzero.symm
    · rw [if_neg hcopr, mul_zero]

/-- Triangle-inequality form of unit-sieve inclusion--exclusion.  It reduces
a restricted nonprincipal character sum to its divisor-class pieces. -/
lemma abs_sum_restrictedQuadraticPrimeFactorProduct_le_divisor_bounds
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hts : t ⊆ s)
    (M H : ℕ) (B : Finset ℕ → ℝ)
    (hbound : ∀ u ∈ (s \ t).powerset,
      |∑ i ∈ Finset.range H,
        if (∏ p ∈ u, p) ∣ M + i then
          quadraticPrimeFactorProduct t (M + i) else 0| ≤ B u) :
    |∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)| ≤
      ∑ u ∈ (s \ t).powerset, B u := by
  rw [show (∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)) =
      ∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
        (∑ i ∈ Finset.range H,
          if (∏ p ∈ u, p) ∣ M + i then
            quadraticPrimeFactorProduct t (M + i) else 0) by
    calc
      (∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)) =
        ∑ i ∈ Finset.range H,
          ∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
            (if (∏ p ∈ u, p) ∣ M + i then
              quadraticPrimeFactorProduct t (M + i) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact restrictedQuadraticPrimeFactorProduct_eq_alternating
              hs hts (M + i)
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mul_sum]]
  calc
    |∑ u ∈ (s \ t).powerset, (-1 : ℝ) ^ u.card *
        (∑ i ∈ Finset.range H,
          if (∏ p ∈ u, p) ∣ M + i then
            quadraticPrimeFactorProduct t (M + i) else 0)| ≤
      ∑ u ∈ (s \ t).powerset,
        |(-1 : ℝ) ^ u.card *
          (∑ i ∈ Finset.range H,
            if (∏ p ∈ u, p) ∣ M + i then
              quadraticPrimeFactorProduct t (M + i) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u ∈ (s \ t).powerset,
        |∑ i ∈ Finset.range H,
          if (∏ p ∈ u, p) ∣ M + i then
            quadraticPrimeFactorProduct t (M + i) else 0| := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [abs_mul, abs_neg_one_pow, one_mul]
    _ ≤ ∑ u ∈ (s \ t).powerset, B u := by
      exact Finset.sum_le_sum hbound

/-- The principal unit-restricted character sum is exactly the elementary
sieve count. -/
lemma sum_restrictedQuadraticPrimeFactorProduct_empty
    (s : Finset ℕ) (M H : ℕ) :
    (∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) ∅ (M + i)) =
      (shiftedPrimeSetCoprimeIndices s M H).card := by
  calc
    (∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) ∅ (M + i)) =
      ∑ i ∈ Finset.range H,
        if (M + i).Coprime (primeSetModulus s) then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [restrictedQuadraticPrimeFactorProduct,
            quadraticPrimeFactorProduct]
    _ = ∑ _i ∈ shiftedPrimeSetCoprimeIndices s M H, (1 : ℝ) := by
      rw [shiftedPrimeSetCoprimeIndices, ← Finset.sum_filter]
    _ = (shiftedPrimeSetCoprimeIndices s M H).card := by simp

/-- Finite unit-square criterion after both the square-class expansion and
the exact unit-sieve inclusion--exclusion have been opened. -/
lemma exists_coprime_isSquare_primeSetModulus_of_restricted_divisor_bounds
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ)
    (B : Finset ℕ → Finset ℕ → ℝ)
    (hbound : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset,
        |∑ i ∈ Finset.range H,
          if (∏ p ∈ u, p) ∣ M + i then
            quadraticPrimeFactorProduct t (M + i) else 0| ≤ B t u)
    (hbudget :
      (∑ t ∈ s.powerset.filter Finset.Nonempty,
        ∑ u ∈ (s \ t).powerset, B t u) <
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime (primeSetModulus s) ∧
        IsSquare ((M + i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_zmod_in_interval_of_character_domination
    (primeSetModulus_squarefree s hs)
  rw [primeFactors_primeSetModulus s hs]
  rw [sum_restrictedQuadraticPrimeFactorProduct_empty]
  have hprincipal := card_shiftedPrimeSetCoprimeIndices_lower s hs M H
  calc
    (∑ t ∈ s.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)|) ≤
      ∑ t ∈ s.powerset.filter Finset.Nonempty,
        ∑ u ∈ (s \ t).powerset, B t u := by
          apply Finset.sum_le_sum
          intro t ht
          exact abs_sum_restrictedQuadraticPrimeFactorProduct_le_divisor_bounds
            hs (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1)
            M H (B t) (hbound t ht)
    _ < (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card :=
      hbudget
    _ ≤ (shiftedPrimeSetCoprimeIndices s M H).card := hprincipal

/-- Unit-square hitting from ordinary interval bounds for every nonprincipal
subproduct character and every coprimality-sieve divisor. -/
lemma exists_coprime_isSquare_primeSetModulus_of_interval_bounds
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (M H : ℕ)
    (B : Finset ℕ → Finset ℕ → ℝ)
    (hB : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, 0 ≤ B t u)
    (hinterval : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H →
        L ≤ H / (∏ p ∈ u, p) + 1 →
        |∑ j ∈ Finset.range L,
          quadraticPrimeFactorProduct t (K + j)| ≤ B t u)
    (hbudget :
      (∑ t ∈ s.powerset.filter Finset.Nonempty,
        ∑ u ∈ (s \ t).powerset, B t u) <
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime (primeSetModulus s) ∧
        IsSquare ((M + i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_primeSetModulus_of_restricted_divisor_bounds
    s hs M H B
  · intro t ht u hu
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have htu : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
    have hus : u ⊆ s := fun p hp ↦
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hu hp)).1
    have hupos : 0 < ∏ p ∈ u, p := Finset.prod_pos fun p hp ↦
      (hs p (hus hp)).pos
    exact abs_divisible_quadraticPrimeFactorProduct_sum_le t htu M H
      (∏ p ∈ u, p) hupos (hB t ht u hu)
      (hinterval t ht u hu)
  · exact hbudget

lemma card_primeSetCoprimeDenominators_le (s : Finset ℕ) (U : ℕ) :
    (primeSetCoprimeDenominators s U).card ≤ U := by
  calc
    (primeSetCoprimeDenominators s U).card ≤ (Finset.Icc 1 U).card := by
      exact Finset.card_filter_le _ _
    _ = U := by simp

/-- Once the denominator range dominates the inclusion--exclusion endpoint
error, its elementary sieve lower bound retains half of the Euler-product
main term. -/
lemma primeSet_sieve_lower_ge_half (w U : ℕ)
    (hU : (2 : ℝ) * (4 : ℝ) ^ w ≤ U) :
    (U : ℝ) * (1 / 2 : ℝ) ^ w - (2 : ℝ) ^ w ≥
      (U : ℝ) * (1 / 2 : ℝ) ^ (w + 1) := by
  let a : ℝ := (2 : ℝ) ^ w
  have ha : 0 < a := by positivity
  have h4 : (4 : ℝ) ^ w = a ^ 2 := by
    calc
      (4 : ℝ) ^ w = ((2 : ℝ) ^ 2) ^ w := by norm_num
      _ = (2 : ℝ) ^ (2 * w) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (w * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ w) ^ 2 := by rw [pow_mul]
      _ = a ^ 2 := by rfl
  have hUa : 2 * a ^ 2 ≤ (U : ℝ) := by simpa [h4] using hU
  have ha_le : a ≤ (U : ℝ) / (2 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hinv : (1 / 2 : ℝ) ^ w = 1 / a := by
    simp [a, one_div, inv_pow]
  have hinv' : (1 / 2 : ℝ) ^ (w + 1) = 1 / (2 * a) := by
    rw [pow_succ, hinv]
    field_simp
  rw [hinv, hinv']
  calc
    (U : ℝ) * (1 / a) - a ≥
        (U : ℝ) * (1 / a) - (U : ℝ) / (2 * a) := by linarith
    _ = (U : ℝ) * (1 / (2 * a)) := by field_simp; ring

/-- The number of pairs `(t,u)` in the exact unit-restricted character
expansion is at most `4^|s|`.  The exact count is closer to `3^|s|`, but this
coarser bound makes the eventual error allocation especially transparent. -/
lemma squarefreeSievePairCount_le (s : Finset ℕ) :
    ∑ t ∈ s.powerset.filter Finset.Nonempty,
        (s \ t).powerset.card ≤ 4 ^ s.card := by
  calc
    ∑ t ∈ s.powerset.filter Finset.Nonempty,
        (s \ t).powerset.card ≤
      ∑ _t ∈ s.powerset.filter Finset.Nonempty, 2 ^ s.card := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.card_powerset]
        exact Nat.pow_le_pow_right (by omega)
          (Finset.card_le_card Finset.sdiff_subset)
    _ = (s.powerset.filter Finset.Nonempty).card * 2 ^ s.card := by simp
    _ ≤ 2 ^ s.card * 2 ^ s.card := by
      gcongr
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset s)
    _ = 4 ^ s.card := by rw [← mul_pow]; norm_num

/-- Uniform allowance for every pair in the exact unit-square
inclusion--exclusion expansion. -/
noncomputable def unitSquareTermBudget (w H : ℕ) : ℝ :=
  (H : ℝ) / (16 * (8 : ℝ) ^ w)

lemma unitSquareTermBudget_nonneg (w H : ℕ) :
    0 ≤ unitSquareTermBudget w H := by
  dsimp [unitSquareTermBudget]
  positivity

/-- Summing the uniform allowance over all character/divisor pairs still
uses strictly less than the elementary unit-sieve main term. -/
lemma unitSquareTermBudget_total_lt
    (s : Finset ℕ) {H : ℕ} (hH : 0 < H)
    (hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H) :
    (∑ t ∈ s.powerset.filter Finset.Nonempty,
        ∑ _u ∈ (s \ t).powerset,
          unitSquareTermBudget s.card H) <
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card := by
  have hcount :
      (∑ t ∈ s.powerset.filter Finset.Nonempty,
          ((s \ t).powerset.card : ℝ)) ≤ (4 : ℝ) ^ s.card := by
    exact_mod_cast squarefreeSievePairCount_le s
  have hB : 0 ≤ unitSquareTermBudget s.card H :=
    unitSquareTermBudget_nonneg _ _
  have hsum :
      (∑ t ∈ s.powerset.filter Finset.Nonempty,
          ∑ _u ∈ (s \ t).powerset,
            unitSquareTermBudget s.card H) ≤
        (4 : ℝ) ^ s.card * unitSquareTermBudget s.card H := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hcount hB
  have hmain := primeSet_sieve_lower_ge_half s.card H hlarge
  have hpow : (0 : ℝ) < (2 : ℝ) ^ s.card := by positivity
  have hbudget :
      (4 : ℝ) ^ s.card * unitSquareTermBudget s.card H <
        (H : ℝ) * (1 / 2 : ℝ) ^ (s.card + 1) := by
    rw [unitSquareTermBudget, pow_succ]
    rw [show (8 : ℝ) ^ s.card =
        (4 : ℝ) ^ s.card * (2 : ℝ) ^ s.card by
      rw [← mul_pow]; norm_num]
    rw [show (1 / 2 : ℝ) ^ s.card =
        1 / (2 : ℝ) ^ s.card by simp [div_eq_mul_inv]]
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    field_simp
    nlinarith
  exact hsum.trans_lt (hbudget.trans_le hmain)

/-- The trivial bound for a consecutive subset-character sum. -/
lemma abs_sum_quadraticPrimeFactorProduct_le_length
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) (K L : ℕ) :
    |∑ j ∈ Finset.range L,
        quadraticPrimeFactorProduct t (K + j)| ≤ L := by
  calc
    |∑ j ∈ Finset.range L,
        quadraticPrimeFactorProduct t (K + j)| ≤
      ∑ j ∈ Finset.range L,
        |quadraticPrimeFactorProduct t (K + j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range L, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_quadraticPrimeFactorProduct_le_one ht _
    _ = L := by simp

/-- A convenient positive lower bound for the actual number of coprime
Burgess denominators. -/
lemma card_primeSetCoprimeDenominators_ge_half
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    (hU : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ U) :
    (U : ℝ) * (1 / 2 : ℝ) ^ (s.card + 1) ≤
      (primeSetCoprimeDenominators s U).card := by
  exact (primeSet_sieve_lower_ge_half s.card U hU).trans
    (card_primeSetCoprimeDenominators_lower s hs U)

/-- A dyadic integer approximation to the eighth root of a conductor. -/
def burgessDyadicShift (q : ℕ) : ℕ :=
  2 ^ (Nat.log 2 q / 8)

lemma burgessDyadicShift_pos (q : ℕ) :
    0 < burgessDyadicShift q := by
  simp [burgessDyadicShift]

lemma burgessDyadicShift_pow_eight_le {q : ℕ} (hq : q ≠ 0) :
    burgessDyadicShift q ^ 8 ≤ q := by
  calc
    burgessDyadicShift q ^ 8 =
        2 ^ ((Nat.log 2 q / 8) * 8) := by
      rw [burgessDyadicShift, pow_mul]
    _ ≤ 2 ^ Nat.log 2 q := by
      exact Nat.pow_le_pow_right (by omega)
        (Nat.div_mul_le_self _ _)
    _ ≤ q := Nat.pow_log_le_self 2 hq

lemma burgessDyadicShift_lt {q : ℕ} (hq : 2 ≤ q) :
    burgessDyadicShift q < q := by
  have hq0 : q ≠ 0 := by omega
  have hV1 : 1 ≤ burgessDyadicShift q := burgessDyadicShift_pos q
  have hVpow : burgessDyadicShift q ≤ burgessDyadicShift q ^ 8 := by
    calc
      burgessDyadicShift q = burgessDyadicShift q ^ 1 := by simp
      _ ≤ burgessDyadicShift q ^ 8 :=
        pow_le_pow_right₀ hV1 (by omega)
  have hVq : burgessDyadicShift q ≤ q :=
    hVpow.trans (burgessDyadicShift_pow_eight_le hq0)
  by_contra hnot
  have heq : burgessDyadicShift q = q := Nat.le_antisymm hVq (by omega)
  have hstrict : q ^ 1 < q ^ 8 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hp := burgessDyadicShift_pow_eight_le hq0
  rw [heq] at hp
  exact (Nat.not_le_of_lt hstrict) (by simpa using hp)

/-- The same dyadic scale loses at most the absolute factor `256` in the
opposite direction. -/
lemma lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight
    (q : ℕ) :
    q < 256 * burgessDyadicShift q ^ 8 := by
  let e := Nat.log 2 q
  let k := e / 8
  have he : e + 1 ≤ 8 * (k + 1) := by
    have hmod : e % 8 < 8 := Nat.mod_lt _ (by omega)
    have hdecomp : e % 8 + 8 * (e / 8) = e := Nat.mod_add_div e 8
    dsimp only [k]
    omega
  calc
    q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by omega) q
    _ = 2 ^ (e + 1) := by rfl
    _ ≤ 2 ^ (8 * (k + 1)) := Nat.pow_le_pow_right (by omega) he
    _ = 256 * burgessDyadicShift q ^ 8 := by
      calc
        2 ^ (8 * (k + 1)) = 2 ^ (8 * k + 8) := by congr 1
        _ = 2 ^ (8 * k) * 2 ^ 8 := by rw [pow_add]
        _ = (2 ^ k) ^ 8 * 256 := by
          rw [show 8 * k = k * 8 by omega, pow_mul]
          norm_num
        _ = 256 * burgessDyadicShift q ^ 8 := by
          simp only [k, e, burgessDyadicShift]
          omega

lemma sqrt_lt_sixteen_mul_burgessDyadicShift_pow_four (q : ℕ) :
    Real.sqrt q < 16 * burgessDyadicShift q ^ 4 := by
  rw [Real.sqrt_lt (by positivity) (by positivity)]
  have hreal : (q : ℝ) <
      256 * (burgessDyadicShift q : ℝ) ^ 8 := by
    exact_mod_cast lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight q
  calc
    (q : ℝ) < 256 * (burgessDyadicShift q : ℝ) ^ 8 := hreal
    _ = (16 * (burgessDyadicShift q : ℝ) ^ 4) ^ 2 := by ring

/-- The elementary logarithmic energy factor in the Burgess amplifier is
bounded by the corresponding expression at the ambient interval length. -/
lemma burgessEnergyFactor_le
    {H U : ℕ} (hU : 0 < U) (hUH : U ≤ H) :
    (((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U))) ≤
      2 * H * U * (1 + Real.log H) ^ 2 := by
  have hUreal : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hHreal : (1 : ℝ) ≤ H := hUreal.trans (by exact_mod_cast hUH)
  have hlogU₀ : 0 ≤ Real.log U := Real.log_nonneg hUreal
  have hlogH₀ : 0 ≤ Real.log H := Real.log_nonneg hHreal
  have hlog : Real.log U ≤ Real.log H := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hUH)
  have hfirst :
      (H : ℝ) * (1 + Real.log U) + U ≤
        2 * H * (1 + Real.log H) := by
    have hUHR : (U : ℝ) ≤ H := by exact_mod_cast hUH
    nlinarith
  have hsecond :
      (U : ℝ) * (1 + Real.log U) ≤ U * (1 + Real.log H) := by
    gcongr
  calc
    (((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U))) ≤
        (2 * H * (1 + Real.log H)) *
          (U * (1 + Real.log H)) := by
      exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = 2 * H * U * (1 + Real.log H) ^ 2 := by ring

/-- A member of `primeSetCoprimeDenominators`, regarded as a conductor unit. -/
def primeSetCoprimePositiveUnit
    (s : Finset ℕ) (U : ℕ) (u : ↥(primeSetCoprimeDenominators s U)) :
    (ZMod (primeSetModulus s))ˣ :=
  ZMod.unitOfCoprime u (Finset.mem_filter.mp u.property).2

/-- All positive conductor units represented by an integer at most `U`. -/
def primeSetCoprimePositiveUnits (s : Finset ℕ) (U : ℕ) :
    Finset (ZMod (primeSetModulus s))ˣ :=
  (Finset.univ : Finset ↥(primeSetCoprimeDenominators s U)).image
    (primeSetCoprimePositiveUnit s U)

lemma primeSetCoprimePositiveUnit_coe
    (s : Finset ℕ) (U : ℕ) (u : ↥(primeSetCoprimeDenominators s U)) :
    ((primeSetCoprimePositiveUnit s U u :
      (ZMod (primeSetModulus s))ˣ) : ZMod (primeSetModulus s)) =
      (u : ℕ) := by
  exact ZMod.coe_unitOfCoprime _ _

lemma primeSetCoprimePositiveUnit_injective
    (s : Finset ℕ) (U : ℕ) (hUq : U < primeSetModulus s) :
    Function.Injective (primeSetCoprimePositiveUnit s U) := by
  intro u v huv
  apply Subtype.ext
  apply eq_of_zmod_positive_cast_eq
      (Finset.mem_filter.mp u.property).1
      (Finset.mem_filter.mp v.property).1 hUq
  have hcoe := congrArg Units.val huv
  simpa [primeSetCoprimePositiveUnit_coe] using hcoe

lemma primeSetCoprimePositiveUnits_card
    (s : Finset ℕ) (U : ℕ) (hUq : U < primeSetModulus s) :
    (primeSetCoprimePositiveUnits s U).card =
      (primeSetCoprimeDenominators s U).card := by
  rw [primeSetCoprimePositiveUnits,
    Finset.card_image_of_injective _
      (primeSetCoprimePositiveUnit_injective s U hUq)]
  simp

def primeSetCoprimePositiveUnitNat
    (s : Finset ℕ) (U u : ℕ) : (ZMod (primeSetModulus s))ˣ := by
  classical
  exact if hu : u ∈ primeSetCoprimeDenominators s U then
    primeSetCoprimePositiveUnit s U ⟨u, hu⟩ else 1

lemma primeSetCoprimePositiveUnitNat_of_mem
    (s : Finset ℕ) (U : ℕ) {u : ℕ}
    (hu : u ∈ primeSetCoprimeDenominators s U) :
    primeSetCoprimePositiveUnitNat s U u =
      primeSetCoprimePositiveUnit s U ⟨u, hu⟩ := by
  simp [primeSetCoprimePositiveUnitNat, hu]

lemma primeSetCoprimePositiveUnitNat_coe_of_mem
    (s : Finset ℕ) (U : ℕ) {u : ℕ}
    (hu : u ∈ primeSetCoprimeDenominators s U) :
    ((primeSetCoprimePositiveUnitNat s U u :
      (ZMod (primeSetModulus s))ˣ) : ZMod (primeSetModulus s)) = u := by
  rw [primeSetCoprimePositiveUnitNat_of_mem s U hu,
    primeSetCoprimePositiveUnit_coe]

lemma primeSetCoprimePositiveUnitNat_mem
    (s : Finset ℕ) (U : ℕ) {u : ℕ}
    (hu : u ∈ primeSetCoprimeDenominators s U) :
    primeSetCoprimePositiveUnitNat s U u ∈
      primeSetCoprimePositiveUnits s U := by
  rw [primeSetCoprimePositiveUnitNat_of_mem s U hu]
  rw [primeSetCoprimePositiveUnits, Finset.mem_image]
  exact ⟨⟨u, hu⟩, by simp, rfl⟩

lemma primeSetCoprimePositiveUnitNat_injective_on
    (s : Finset ℕ) (U : ℕ) (hUq : U < primeSetModulus s)
    {u v : ℕ} (hu : u ∈ primeSetCoprimeDenominators s U)
    (hv : v ∈ primeSetCoprimeDenominators s U)
    (huv : primeSetCoprimePositiveUnitNat s U u =
      primeSetCoprimePositiveUnitNat s U v) : u = v := by
  apply eq_of_zmod_positive_cast_eq
      (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 hUq
  have hcoe := congrArg Units.val huv
  simpa [primeSetCoprimePositiveUnitNat_coe_of_mem s U hu,
    primeSetCoprimePositiveUnitNat_coe_of_mem s U hv] using hcoe

def burgessCoprimeUnitCollisionCast
    (s : Finset ℕ) (U M : ℕ)
    (ab : (ℕ × ℕ) × (ℕ × ℕ)) :
    ((ZMod (primeSetModulus s) × (ZMod (primeSetModulus s))ˣ) ×
      (ZMod (primeSetModulus s) × (ZMod (primeSetModulus s))ˣ)) :=
  (((M + ab.1.1 : ℕ), primeSetCoprimePositiveUnitNat s U ab.1.2),
    ((M + ab.2.1 : ℕ), primeSetCoprimePositiveUnitNat s U ab.2.2))

def burgessCoprimePrimeSetRatioCollisions
    (s : Finset ℕ) (U M H : ℕ) :=
  (((zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetCoprimePositiveUnits s U) ×ˢ
      (zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetCoprimePositiveUnits s U)).filter fun ab ↦
    (((ab.1.2⁻¹ : (ZMod (primeSetModulus s))ˣ) :
        ZMod (primeSetModulus s)) * ab.1.1 =
      ((ab.2.2⁻¹ : (ZMod (primeSetModulus s))ˣ) :
        ZMod (primeSetModulus s)) * ab.2.1))

def burgessCoprimeIntervalAllCollisions
    (q M H : ℕ) (W : Finset ℕ) :=
  ((((Finset.range H) ×ˢ W) ×ˢ
      ((Finset.range H) ×ˢ W)).filter fun ab ↦
    (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q])

lemma coprimeUnitRatioCollision_card_eq_intervalAllCollisions
    (s : Finset ℕ) (U : ℕ) {M H : ℕ}
    (hH : H ≤ primeSetModulus s) (hUq : U < primeSetModulus s) :
    (burgessCoprimePrimeSetRatioCollisions s U M H).card =
      (burgessCoprimeIntervalAllCollisions (primeSetModulus s) M H
        (primeSetCoprimeDenominators s U)).card := by
  rw [burgessCoprimePrimeSetRatioCollisions]
  symm
  apply Finset.card_bij
      (fun ab _ ↦ burgessCoprimeUnitCollisionCast s U M ab)
  · intro ab hab
    rw [burgessCoprimeIntervalAllCollisions, Finset.mem_filter] at hab
    rw [Finset.mem_filter]
    rcases hab with ⟨habbox, habcong⟩
    rcases Finset.mem_product.mp habbox with ⟨hab₁, hab₂⟩
    rcases Finset.mem_product.mp hab₁ with ⟨hi₁, hu₁⟩
    rcases Finset.mem_product.mp hab₂ with ⟨hi₂, hu₂⟩
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_product.mpr
      · exact ⟨Finset.mem_image.mpr ⟨ab.1.1, hi₁, rfl⟩,
          primeSetCoprimePositiveUnitNat_mem s U hu₁⟩
      · exact ⟨Finset.mem_image.mpr ⟨ab.2.1, hi₂, rfl⟩,
          primeSetCoprimePositiveUnitNat_mem s U hu₂⟩
    · apply (unit_inv_mul_eq_unit_inv_mul_iff
        (primeSetCoprimePositiveUnitNat s U ab.1.2)
        (primeSetCoprimePositiveUnitNat s U ab.2.2)
        ((M + ab.1.1 : ℕ) : ZMod (primeSetModulus s))
        ((M + ab.2.1 : ℕ) : ZMod (primeSetModulus s))).2
      rw [primeSetCoprimePositiveUnitNat_coe_of_mem s U hu₁,
        primeSetCoprimePositiveUnitNat_coe_of_mem s U hu₂]
      simpa only [burgessCoprimeUnitCollisionCast, Nat.cast_mul] using
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr habcong
  · intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨habox, _⟩
    rcases Finset.mem_filter.mp hb with ⟨hbbox, _⟩
    rcases Finset.mem_product.mp habox with ⟨ha₁, ha₂⟩
    rcases Finset.mem_product.mp hbbox with ⟨hb₁, hb₂⟩
    rcases Finset.mem_product.mp ha₁ with ⟨hai₁, hau₁⟩
    rcases Finset.mem_product.mp ha₂ with ⟨hai₂, hau₂⟩
    rcases Finset.mem_product.mp hb₁ with ⟨hbi₁, hbu₁⟩
    rcases Finset.mem_product.mp hb₂ with ⟨hbi₂, hbu₂⟩
    apply Prod.ext
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₁) (Finset.mem_range.mp hbi₁) hH
          (congrArg (fun z ↦ z.1.1) hab)
      · exact primeSetCoprimePositiveUnitNat_injective_on s U hUq
          hau₁ hbu₁ (congrArg (fun z ↦ z.1.2) hab)
    · apply Prod.ext
      · exact eq_of_zmod_interval_cast_eq
          (Finset.mem_range.mp hai₂) (Finset.mem_range.mp hbi₂) hH
          (congrArg (fun z ↦ z.2.1) hab)
      · exact primeSetCoprimePositiveUnitNat_injective_on s U hUq
          hau₂ hbu₂ (congrArg (fun z ↦ z.2.2) hab)
  · intro z hz
    rw [Finset.mem_filter] at hz
    rcases hz with ⟨hzbox, hzratio⟩
    rcases Finset.mem_product.mp hzbox with ⟨hz₁, hz₂⟩
    rcases Finset.mem_product.mp hz₁ with ⟨hzn₁, hzu₁⟩
    rcases Finset.mem_product.mp hz₂ with ⟨hzn₂, hzu₂⟩
    rw [zmodNatInterval, Finset.mem_image] at hzn₁ hzn₂
    rw [primeSetCoprimePositiveUnits, Finset.mem_image] at hzu₁ hzu₂
    rcases hzn₁ with ⟨i₁, hi₁, hi₁z⟩
    rcases hzu₁ with ⟨u₁, hu₁, hu₁z⟩
    rcases hzn₂ with ⟨i₂, hi₂, hi₂z⟩
    rcases hzu₂ with ⟨u₂, hu₂, hu₂z⟩
    refine ⟨((i₁, u₁), (i₂, u₂)), ?_, ?_⟩
    · rw [burgessCoprimeIntervalAllCollisions, Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hi₁, u₁.property⟩,
            Finset.mem_product.mpr ⟨hi₂, u₂.property⟩⟩
      · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        rw [Nat.cast_mul, Nat.cast_mul]
        change ((M + i₁ : ℕ) : ZMod (primeSetModulus s)) *
            (u₂ : ℕ) =
          ((M + i₂ : ℕ) : ZMod (primeSetModulus s)) * (u₁ : ℕ)
        have hcross := (unit_inv_mul_eq_unit_inv_mul_iff
          (primeSetCoprimePositiveUnitNat s U u₁)
          (primeSetCoprimePositiveUnitNat s U u₂)
          ((M + i₁ : ℕ) : ZMod (primeSetModulus s))
          ((M + i₂ : ℕ) : ZMod (primeSetModulus s))).mp (by
            simpa only [hi₁z, hi₂z,
              primeSetCoprimePositiveUnitNat_of_mem s U u₁.property,
              primeSetCoprimePositiveUnitNat_of_mem s U u₂.property,
              hu₁z, hu₂z] using hzratio)
        simpa only [primeSetCoprimePositiveUnitNat_coe_of_mem s U u₁.property,
          primeSetCoprimePositiveUnitNat_coe_of_mem s U u₂.property] using hcross
    · simp [burgessCoprimeUnitCollisionCast, hi₁z, hi₂z,
        primeSetCoprimePositiveUnitNat_of_mem s U u₁.property,
        primeSetCoprimePositiveUnitNat_of_mem s U u₂.property,
        hu₁z, hu₂z]

lemma burgessCoprimeIntervalAllCollisions_card_eq_sum
    (q M H : ℕ) (W : Finset ℕ) :
    (burgessCoprimeIntervalAllCollisions q M H W).card =
      ∑ u₁ ∈ W, ∑ u₂ ∈ W,
        (burgessIntervalCollision q M H u₁ u₂).card := by
  simp only [burgessCoprimeIntervalAllCollisions,
    burgessIntervalCollision, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u₁ hu₁
  calc
    (∑ i₁ ∈ Finset.range H,
        ∑ i₂ ∈ Finset.range H, ∑ u₂ ∈ W,
          if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD q] then 1 else 0) =
        ∑ i₁ ∈ Finset.range H,
          ∑ u₂ ∈ W, ∑ i₂ ∈ Finset.range H,
            if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD q] then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i₁ hi₁
      rw [Finset.sum_comm]
    _ = ∑ u₂ ∈ W,
          ∑ i₁ ∈ Finset.range H, ∑ i₂ ∈ Finset.range H,
            if (M + i₁) * u₂ ≡ (M + i₂) * u₁ [MOD q] then 1 else 0 := by
      rw [Finset.sum_comm]

lemma burgessUnitRatioEnergy_coprimeIntervals_eq_sum
    (s : Finset ℕ) (U : ℕ) [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetCoprimePositiveUnits s U) =
      ((∑ u₁ ∈ primeSetCoprimeDenominators s U,
        ∑ u₂ ∈ primeSetCoprimeDenominators s U,
          (burgessIntervalCollision
            (primeSetModulus s) M H u₁ u₂).card : ℕ) : ℝ) := by
  rw [burgessUnitRatioEnergy_eq_card_collision]
  change ((burgessCoprimePrimeSetRatioCollisions s U M H).card : ℝ) = _
  rw [coprimeUnitRatioCollision_card_eq_intervalAllCollisions s U hH hUq]
  rw [burgessCoprimeIntervalAllCollisions_card_eq_sum]

lemma burgessUnitRatioEnergy_coprimeIntervals_le_reduced_sum
    (s : Finset ℕ) (U : ℕ) [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : 0 < H) (hU : 0 < U)
    (hHq : H ≤ primeSetModulus s) (hUq : U < primeSetModulus s)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetCoprimePositiveUnits s U) ≤
      ((∑ u₁ ∈ primeSetCoprimeDenominators s U,
        ∑ u₂ ∈ primeSetCoprimeDenominators s U,
          (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) := by
  rw [burgessUnitRatioEnergy_coprimeIntervals_eq_sum s U hHq hUq]
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      burgessIntervalCollision_card_le_of_coprime hH hU
        (Finset.mem_filter.mp hu₁).1 (Finset.mem_filter.mp hu₂).1
        (Nat.Coprime.symm (Finset.mem_filter.mp hu₁).2) hsmall

lemma burgessUnitRatioEnergy_coprimeIntervals_le
    (s : Finset ℕ) (U : ℕ) [NeZero (primeSetModulus s)]
    {M H : ℕ} (hH : 0 < H) (hU : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetCoprimePositiveUnits s U) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  calc
    burgessUnitRatioEnergy
        (zmodNatInterval (primeSetModulus s) M H)
        (primeSetCoprimePositiveUnits s U) ≤
      ((∑ u₁ ∈ primeSetCoprimeDenominators s U,
        ∑ u₂ ∈ primeSetCoprimeDenominators s U,
          (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) :=
      burgessUnitRatioEnergy_coprimeIntervals_le_reduced_sum
        s U hH hU hHq hUq hsmall
    _ ≤ ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) := by
      have hsub : primeSetCoprimeDenominators s U ⊆ Finset.Icc 1 U :=
        Finset.filter_subset _ _
      have hinner (u₁ : ℕ) :
          (∑ u₂ ∈ primeSetCoprimeDenominators s U,
              (H / (u₁ / u₁.gcd u₂) + 1)) ≤
            ∑ u₂ ∈ Finset.Icc 1 U,
              (H / (u₁ / u₁.gcd u₂) + 1) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun u₂ hu₂ _ ↦ Nat.zero_le _)
      have houter :
          (∑ u₁ ∈ primeSetCoprimeDenominators s U,
              ∑ u₂ ∈ primeSetCoprimeDenominators s U,
                (H / (u₁ / u₁.gcd u₂) + 1)) ≤
            ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
              (H / (u₁ / u₁.gcd u₂) + 1) := by
        calc
          (∑ u₁ ∈ primeSetCoprimeDenominators s U,
              ∑ u₂ ∈ primeSetCoprimeDenominators s U,
                (H / (u₁ / u₁.gcd u₂) + 1)) ≤
              ∑ u₁ ∈ primeSetCoprimeDenominators s U,
                ∑ u₂ ∈ Finset.Icc 1 U,
                  (H / (u₁ / u₁.gcd u₂) + 1) :=
            Finset.sum_le_sum fun u₁ hu₁ ↦ hinner u₁
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun u₁ hu₁ _ ↦ Nat.zero_le _)
      exact_mod_cast houter
    _ ≤ (burgessDivisorOvercount H U : ℝ) :=
      reduced_denominator_sum_cast_le H U
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) :=
      burgessDivisorOvercount_cast_le H U hU

lemma quadraticPrimeSetDilatedShiftSum_coprimePositive
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    {M i V : ℕ} (u : ↥(primeSetCoprimeDenominators s U))
    (hV : V < primeSetModulus s) :
    quadraticPrimeSetDilatedShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V)
        ((M + i : ℕ) : ZMod (primeSetModulus s))
        (primeSetCoprimePositiveUnit s U u) =
      ∑ v ∈ Finset.Icc 1 V,
        quadraticPrimeFactorProduct s (M + i + (u : ℕ) * v) := by
  have hinj : Set.InjOn
      (fun v : ℕ ↦ (v : ZMod (primeSetModulus s)))
      (Finset.Icc 1 V) := by
    intro v hv w hw hvw
    exact eq_of_zmod_positive_cast_eq hv hw hV hvw
  rw [quadraticPrimeSetDilatedShiftSum, zmodPositiveInterval]
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← quadraticPrimeSetCharReal_natCast s hs
    (M + i + (u : ℕ) * v)]
  congr 1
  rw [primeSetCoprimePositiveUnit_coe]
  push_cast
  ring

lemma sum_abs_quadraticPrimeSetDilatedShiftSum_coprimeIntervals
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    {M H V : ℕ} (hH : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s) (hV : V < primeSetModulus s) :
    (∑ nu ∈ zmodNatInterval (primeSetModulus s) M H ×ˢ
        primeSetCoprimePositiveUnits s U,
      |quadraticPrimeSetDilatedShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V) nu.1 nu.2|) =
      ∑ i ∈ Finset.range H,
        ∑ u ∈ primeSetCoprimeDenominators s U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticPrimeFactorProduct s (M + i + u * v)| := by
  have hinjI : Set.InjOn
      (fun i : ℕ ↦ ((M + i : ℕ) : ZMod (primeSetModulus s)))
      (Finset.range H) := by
    intro i hi j hj hij
    exact eq_of_zmod_interval_cast_eq
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hH hij
  rw [Finset.sum_product]
  rw [zmodNatInterval, Finset.sum_image hinjI]
  apply Finset.sum_congr rfl
  intro i hi
  have hinjU : Set.InjOn (primeSetCoprimePositiveUnit s U)
      (Finset.univ : Finset ↥(primeSetCoprimeDenominators s U)) :=
    (primeSetCoprimePositiveUnit_injective s U hUq).injOn
  rw [primeSetCoprimePositiveUnits, Finset.sum_image hinjU]
  rw [Finset.sum_subtype (primeSetCoprimeDenominators s U)
    (fun _ ↦ Iff.rfl)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [quadraticPrimeSetDilatedShiftSum_coprimePositive s hs U u hV]

lemma burgessCoprime_natural_numerator_eq_weighted
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    [NeZero (primeSetModulus s)] {M H V : ℕ}
    (hH : H ≤ primeSetModulus s) (hUq : U < primeSetModulus s)
    (hV : V < primeSetModulus s) :
    (∑ i ∈ Finset.range H,
        ∑ u ∈ primeSetCoprimeDenominators s U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticPrimeFactorProduct s (M + i + u * v)|) =
      ∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetCoprimePositiveUnits s U) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x| := by
  rw [← sum_abs_quadraticPrimeSetDilatedShiftSum_eq_weighted]
  exact (sum_abs_quadraticPrimeSetDilatedShiftSum_coprimeIntervals
    s hs U hH hUq hV).symm

lemma abs_quadraticPrimeFactorProduct_coprime_amplified_sub_shifted_le
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ} (hUV : U * V ≤ H) :
    |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)) -
      ∑ u ∈ primeSetCoprimeDenominators s U,
        ∑ v ∈ Finset.Icc 1 V, ∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + u * v + i))| ≤
      (2 : ℝ) * (primeSetCoprimeDenominators s U).card * V * (U * V) := by
  have havg := abs_burgess_shift_average_sub_le
    (quadraticPrimeFactorProduct s)
    (abs_quadraticPrimeFactorProduct_le_one hs)
    M H (primeSetCoprimeDenominators s U) (Finset.Icc 1 V)
    (fun u v ↦ u * v)
    (by
      intro u hu v hv
      have huU : u ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
      exact (Nat.mul_le_mul huU (Finset.mem_Icc.mp hv).2).trans hUV)
  have hcards :
      ((((primeSetCoprimeDenominators s U).card *
        (Finset.Icc 1 V).card : ℕ) : ℝ)) =
        ((primeSetCoprimeDenominators s U).card * V : ℕ) := by simp
  rw [hcards] at havg
  calc
    |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        (∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)) -
      ∑ u ∈ primeSetCoprimeDenominators s U,
        ∑ v ∈ Finset.Icc 1 V, ∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + u * v + i))| ≤
      ∑ u ∈ primeSetCoprimeDenominators s U,
        ∑ v ∈ Finset.Icc 1 V, ((2 * (u * v) : ℕ) : ℝ) := havg
    _ ≤ ∑ _u ∈ primeSetCoprimeDenominators s U,
        ∑ _v ∈ Finset.Icc 1 V, ((2 * (U * V) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      norm_cast
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
        (Finset.mem_Icc.mp hv).2)
    _ = (2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
        (U * V) := by
      simp
      ring

lemma abs_burgess_shifted_triple_sum_le_finset
    (f : ℕ → ℝ) (M H : ℕ) (U V : Finset ℕ) (shift : ℕ → ℕ → ℕ) :
    |∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
        f (M + shift u v + i)| ≤
      ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
  have hreorder :
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + i + shift u v) := by
    calc
      (∑ u ∈ U, ∑ v ∈ V, ∑ i ∈ Finset.range H,
          f (M + shift u v + i)) =
        ∑ u ∈ U, ∑ i ∈ Finset.range H,
          ∑ v ∈ V, f (M + shift u v + i) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
      _ = ∑ i ∈ Finset.range H, ∑ u ∈ U,
          ∑ v ∈ V, f (M + shift u v + i) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          omega
  rw [hreorder]
  calc
    |∑ i ∈ Finset.range H, ∑ u ∈ U,
        ∑ v ∈ V, f (M + i + shift u v)| ≤
      ∑ i ∈ Finset.range H,
        |∑ u ∈ U, ∑ v ∈ V, f (M + i + shift u v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range H, ∑ u ∈ U,
        |∑ v ∈ V, f (M + i + shift u v)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _

lemma burgessCoprime_amplified_abs_le_weighted_add_error
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (U : ℕ)
    [NeZero (primeSetModulus s)] {M H V : ℕ}
    (hH : H ≤ primeSetModulus s) (hUq : U < primeSetModulus s)
    (hV : V < primeSetModulus s) (hUV : U * V ≤ H) :
    (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)| ≤
      (∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetCoprimePositiveUnits s U) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x|) +
        (2 : ℝ) * (primeSetCoprimeDenominators s U).card * V * (U * V) := by
  let S : ℝ := ∑ i ∈ Finset.range H,
    quadraticPrimeFactorProduct s (M + i)
  let T : ℝ := ∑ u ∈ primeSetCoprimeDenominators s U,
    ∑ v ∈ Finset.Icc 1 V, ∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + u * v + i)
  let E : ℝ := (2 : ℝ) * (primeSetCoprimeDenominators s U).card * V * (U * V)
  have havg : |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S) - T| ≤ E :=
    abs_quadraticPrimeFactorProduct_coprime_amplified_sub_shifted_le
      s hs hUV
  have hT : |T| ≤
      ∑ i ∈ Finset.range H,
        ∑ u ∈ primeSetCoprimeDenominators s U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticPrimeFactorProduct s (M + i + u * v)| := by
    exact abs_burgess_shifted_triple_sum_le_finset
      (quadraticPrimeFactorProduct s) M H
      (primeSetCoprimeDenominators s U) (Finset.Icc 1 V)
      (fun u v ↦ u * v)
  have htri :
      |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S)| ≤
        |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S) - T| +
          |T| := by
    calc
      |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S)| =
          |(((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S) - T) + T| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at htri
  change (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * |S| ≤ _
  calc
    (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * |S| ≤
        |((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * S) - T| + |T| := htri
    _ ≤ E + ∑ i ∈ Finset.range H,
        ∑ u ∈ primeSetCoprimeDenominators s U,
          |∑ v ∈ Finset.Icc 1 V,
            quadraticPrimeFactorProduct s (M + i + u * v)| :=
      add_le_add havg hT
    _ = (∑ x : ZMod (primeSetModulus s),
        (burgessUnitRatioWeight
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetCoprimePositiveUnits s U) x : ℝ) *
        |quadraticPrimeSetShiftSum s hs
          (zmodPositiveInterval (primeSetModulus s) V) x|) + E := by
      rw [burgessCoprime_natural_numerator_eq_weighted
        s hs U hH hUq hV]
      ring

lemma primeSetCoprimeDenominators_nonempty
    (s : Finset ℕ) {U : ℕ} (hU : 0 < U) :
    (primeSetCoprimeDenominators s U).Nonempty := by
  refine ⟨1, ?_⟩
  simp [primeSetCoprimeDenominators, show 1 ≤ U by omega]

/-- Composite fourth-moment Burgess amplification with all positive
denominators coprime to the conductor retained. -/
lemma burgessCoprime_amplified_fourth_bound
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ}
    (hH : 0 < H) (hU₀ : 0 < U)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    (((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
      8 *
        (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (∑ v : Fin 4 →
              ↥(zmodPositiveInterval (primeSetModulus s) V),
            quadraticPrimeSetQuarticBound s hs
              (fun i ↦ (v i : ZMod (primeSetModulus s))))) +
          ((2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
            (U * V)) ^ 4) := by
  letI : NeZero (primeSetModulus s) :=
    ⟨(primeSetModulus_pos s hs).ne'⟩
  letI (p : s) : NeZero (p : ℕ) := ⟨(hs p p.property).ne_zero⟩
  let B : ℝ := ∑ x : ZMod (primeSetModulus s),
    (burgessUnitRatioWeight
      (zmodNatInterval (primeSetModulus s) M H)
      (primeSetCoprimePositiveUnits s U) x : ℝ) *
      |quadraticPrimeSetShiftSum s hs
        (zmodPositiveInterval (primeSetModulus s) V) x|
  let E : ℝ := (2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
    (U * V)
  let X : ℝ := (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
    |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)|
  let Q : ℝ := ∑ v : Fin 4 →
      ↥(zmodPositiveInterval (primeSetModulus s) V),
    quadraticPrimeSetQuarticBound s hs
      (fun i ↦ (v i : ZMod (primeSetModulus s)))
  have hXB : X ≤ B + E := by
    exact burgessCoprime_amplified_abs_le_weighted_add_error
      s hs U hHq hUq hVq hUV
  have hX₀ : 0 ≤ X := by positivity
  have hpow : X ^ 4 ≤ (B + E) ^ 4 :=
    pow_le_pow_left₀ hX₀ hXB 4
  have hadd := add_pow_four_le_eight B E
  have hweighted₀ := burgessUnit_weighted_fourth_bound
    (zmodNatInterval (primeSetModulus s) M H)
    (primeSetCoprimePositiveUnits s U)
    (quadraticPrimeSetShiftSum s hs
      (zmodPositiveInterval (primeSetModulus s) V))
  rw [zmodNatInterval_card hHq,
    primeSetCoprimePositiveUnits_card s U hUq] at hweighted₀
  have hmoment := quadraticPrimeSetShiftSum_fourth_moment_le
    s hs (zmodPositiveInterval (primeSetModulus s) V)
  have hleftnonneg :
      0 ≤ ((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
        burgessUnitRatioEnergy
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetCoprimePositiveUnits s U) := by
    exact mul_nonneg (sq_nonneg _)
      (burgessUnitRatioEnergy_nonneg _ _)
  have hweighted : B ^ 4 ≤
      ((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
        burgessUnitRatioEnergy
          (zmodNatInterval (primeSetModulus s) M H)
          (primeSetCoprimePositiveUnits s U) * Q := by
    exact hweighted₀.trans
      (mul_le_mul_of_nonneg_left hmoment hleftnonneg)
  have henergy := burgessUnitRatioEnergy_coprimeIntervals_le
    s U hH hU₀ hHq hUq hsmall (M := M)
  have hQ₀ : 0 ≤ Q := by
    dsimp only [Q]
    exact Finset.sum_nonneg fun v hv ↦
      quadraticPrimeSetQuarticBound_nonneg s hs _
  have hweighted' : B ^ 4 ≤
      ((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) * Q := by
    calc
      B ^ 4 ≤
          ((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            burgessUnitRatioEnergy
              (zmodNatInterval (primeSetModulus s) M H)
              (primeSetCoprimePositiveUnits s U) * Q := hweighted
      _ ≤ ((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
          (((H : ℝ) * (1 + Real.log U) + U) *
            ((U : ℝ) * (1 + Real.log U))) * Q := by
        gcongr
  calc
    X ^ 4 ≤ (B + E) ^ 4 := hpow
    _ ≤ 8 * (B ^ 4 + E ^ 4) := hadd
    _ ≤ 8 *
        (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) * Q) + E ^ 4) := by
      gcongr
    _ = _ := by rfl

lemma burgessCoprime_amplified_fourth_bound_explicit
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s) :
    (((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
      8 *
        (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
              ((3 : ℝ) ^ s.card * V ^ 2 *
                Real.sqrt (primeSetModulus s)))) +
          ((2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
            (U * V)) ^ 4) := by
  calc
    (((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
        |∑ i ∈ Finset.range H,
          quadraticPrimeFactorProduct s (M + i)|) ^ 4) ≤
      8 *
        (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (∑ v : Fin 4 →
              ↥(zmodPositiveInterval (primeSetModulus s) V),
            quadraticPrimeSetQuarticBound s hs
              (fun i ↦ (v i : ZMod (primeSetModulus s))))) +
          ((2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
            (U * V)) ^ 4) :=
      burgessCoprime_amplified_fourth_bound s hs
        hH hU₀ hHq hUq hVq hUV hsmall
    _ ≤ _ := by
      gcongr
      exact general_quadraticPrimeSetQuarticBound_sum_le_general
        s hs hodd hV₀ hVq

lemma abs_quadraticPrimeFactorProduct_sum_lt_of_coprime_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ} {B : ℝ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hB : 0 ≤ B)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hstrict :
      8 *
          (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
              (U * V)) ^ 4) <
        ((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * B) ^ 4) :
    |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + i)| < B := by
  have hbound := burgessCoprime_amplified_fourth_bound_explicit
    s hs hH hU₀ hV₀ hHq hUq hVq hodd hUV hsmall (M := M)
  have hpow :
      (((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct s (M + i)|) ^ 4) <
        ((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * B) ^ 4 :=
    hbound.trans_lt hstrict
  have hlt :
      (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) *
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct s (M + i)| <
        (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * B := by
    exact lt_of_pow_lt_pow_left₀ 4 (mul_nonneg (by positivity) hB) hpow
  have hmultpos :
      (0 : ℝ) <
        ((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ)) := by
    have hcard : 0 < (primeSetCoprimeDenominators s U).card :=
      (primeSetCoprimeDenominators_nonempty s hU₀).card_pos
    positivity
  nlinarith

end

/-- Explicit coprime-denominator Burgess data for one squarefree conductor.
The parameters are allowed to depend on the conductor; this is essential when
the square-class expansion ranges over every nonempty subproduct. -/
def CoprimeBurgessCertificate (s : Finset ℕ) (H : ℕ) (B : ℝ) : Prop :=
  ∃ U V : ℕ,
    0 < U ∧
    0 < V ∧
    H ≤ primeSetModulus s ∧
    U < primeSetModulus s ∧
    V < primeSetModulus s ∧
    U * V ≤ H ∧
    2 * (U * H) < primeSetModulus s ∧
    8 *
        (((((H * (primeSetCoprimeDenominators s U).card : ℕ) : ℝ) ^ 2 *
            (((H : ℝ) * (1 + Real.log U) + U) *
              ((U : ℝ) * (1 + Real.log U)))) *
          (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
              ((3 : ℝ) ^ s.card * V ^ 2 *
                Real.sqrt (primeSetModulus s)))) +
          ((2 : ℝ) * (primeSetCoprimeDenominators s U).card * V *
            (U * V)) ^ 4) <
      ((((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * B) ^ 4

/-- A Burgess certificate remains valid when its permitted error is
increased. -/
lemma coprimeBurgessCertificate_mono
    {s : Finset ℕ} {H : ℕ} {B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (hB : B₁ ≤ B₂)
    (hcert : CoprimeBurgessCertificate s H B₁) :
    CoprimeBurgessCertificate s H B₂ := by
  rcases hcert with
    ⟨U, V, hU, hV, hHq, hUq, hVq, hUV, hsmall, hstrict⟩
  refine ⟨U, V, hU, hV, hHq, hUq, hVq, hUV, hsmall, ?_⟩
  apply hstrict.trans_le
  apply pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      (((primeSetCoprimeDenominators s U).card * V : ℕ) : ℝ) * B₁)
  exact mul_le_mul_of_nonneg_left hB (by positivity)

/-- The global loss that makes a local Burgess bound summable over every
pair in the exact unit-square character expansion. -/
def unitSquareBurgessLoss (w : ℕ) : ℕ := 2 * 8 ^ w

lemma unitSquareBurgessLoss_pos (w : ℕ) :
    0 < unitSquareBurgessLoss w := by
  simp [unitSquareBurgessLoss]

/-- The full denominator loss used by the corrected fourth-moment amplifier
with an additional global loss `J`.  It is placed here because the uniform
scale estimates below already use it. -/
def burgessDenominatorLossExtra (w J V : ℕ) : ℕ :=
  256 * 4 ^ w * J * V

lemma burgessDenominatorLossExtra_pos
    (w : ℕ) {J V : ℕ} (hJ : 0 < J) (hV : 0 < V) :
    0 < burgessDenominatorLossExtra w J V := by
  simp [burgessDenominatorLossExtra, hJ, hV]

/-- The local error delivered with `unitSquareBurgessLoss` is no larger than
the global term budget, even for an interval whose length is one larger than
the ambient length because of residue-class rounding. -/
lemma localBurgessBudget_le_unitSquareTermBudget
    {w H L tc : ℕ} (hH : 0 < H) (hL : L ≤ H + 1) :
    (L : ℝ) /
        (16 * (2 : ℝ) ^ tc * unitSquareBurgessLoss w) ≤
      unitSquareTermBudget w H := by
  have hL2 : L ≤ 2 * H := by omega
  have hL2real : (L : ℝ) ≤ 2 * H := by exact_mod_cast hL2
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ tc := one_le_pow₀ (by norm_num)
  dsimp [unitSquareTermBudget, unitSquareBurgessLoss]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have h8 : (0 : ℝ) < (8 : ℝ) ^ w := by positivity
  rw [div_le_div_iff₀ (by positivity)
    (show (0 : ℝ) < 16 * 8 ^ w by positivity)]
  have hm := mul_le_mul_of_nonneg_right hL2real
    (show (0 : ℝ) ≤ 16 * 8 ^ w by positivity)
  calc
    (L : ℝ) * (16 * 8 ^ w) ≤ 2 * H * (16 * 8 ^ w) := hm
    _ = (H : ℝ) * (16 * 1 * (2 * 8 ^ w)) := by ring
    _ ≤ (H : ℝ) * (16 * 2 ^ tc * (2 * 8 ^ w)) := by gcongr

/-- Convert a local extra-loss certificate to the common global allowance. -/
lemma CoprimeBurgessCertificate.to_unitSquareTermBudget
    {s t : Finset ℕ} {H L : ℕ} (hH : 0 < H) (hL : L ≤ H + 1)
    (hcert : CoprimeBurgessCertificate t L
      ((L : ℝ) /
        (16 * (2 : ℝ) ^ t.card * unitSquareBurgessLoss s.card))) :
    CoprimeBurgessCertificate t L (unitSquareTermBudget s.card H) := by
  exact coprimeBurgessCertificate_mono (by positivity)
    (localBurgessBudget_le_unitSquareTermBudget hH hL) hcert

/-- One fixed integer base dominates every prime-factor loss in the local
extra-loss Burgess inequalities. -/
def unitSquareGlobalLossBase : ℕ :=
  32 * ((2 ^ 10) * 3 * (8 ^ 5))

lemma unitSquare_local_loss_le_global_base
    {s t : Finset ℕ} (hts : t ⊆ s) (htne : t.Nonempty) :
    (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 *
          (3 : ℝ) ^ t.card ≤
      (unitSquareGlobalLossBase : ℝ) ^ s.card := by
  have hcard : t.card ≤ s.card := Finset.card_le_card hts
  have hspos : 0 < s.card := (htne.mono hts).card_pos
  have h2 : (2 : ℝ) ^ (10 * t.card) ≤ (2 : ℝ) ^ (10 * s.card) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (3 : ℝ) ^ t.card ≤ (3 : ℝ) ^ s.card := by
    exact pow_le_pow_right₀ (by norm_num) hcard
  have h32 : (32 : ℝ) ≤ (32 : ℝ) ^ s.card := by
    calc
      (32 : ℝ) = 32 ^ 1 := by simp
      _ ≤ 32 ^ s.card := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num only [unitSquareBurgessLoss, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow]
  calc
    (2 : ℝ) ^ (10 * t.card) * (2 * 8 ^ s.card) ^ 5 *
          3 ^ t.card ≤
      2 ^ (10 * s.card) * (2 * 8 ^ s.card) ^ 5 *
          3 ^ s.card := by gcongr
    _ = 32 * (((2 : ℝ) ^ 10) ^ s.card *
        (3 : ℝ) ^ s.card * ((8 : ℝ) ^ 5) ^ s.card) := by
      rw [show (2 : ℝ) ^ (10 * s.card) =
          ((2 : ℝ) ^ 10) ^ s.card by rw [pow_mul]]
      rw [mul_pow]
      rw [show ((8 : ℝ) ^ s.card) ^ 5 =
          ((8 : ℝ) ^ 5) ^ s.card by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      norm_num
      ring
    _ = 32 * (((2 : ℝ) ^ 10) * 3 * (8 ^ 5)) ^ s.card := by
      rw [mul_pow, mul_pow]
    _ ≤ (32 : ℝ) ^ s.card *
        (((2 : ℝ) ^ 10) * 3 * (8 ^ 5)) ^ s.card := by gcongr
    _ = (unitSquareGlobalLossBase : ℝ) ^ s.card := by
      rw [← mul_pow]
      norm_num [unitSquareGlobalLossBase]

lemma unitSquare_local_loss_without_three_le_global_base
    {s t : Finset ℕ} (hts : t ⊆ s) (htne : t.Nonempty) :
    (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 ≤
      (unitSquareGlobalLossBase : ℝ) ^ s.card := by
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ t.card := one_le_pow₀ (by norm_num)
  calc
    (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 =
      (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 * 1 := by ring
    _ ≤ (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 *
          (3 : ℝ) ^ t.card := by gcongr
    _ ≤ _ := unitSquare_local_loss_le_global_base hts htne

/-- The combined global loss is eventually at most the 128th-root of the
full squarefree conductor. -/
theorem exists_unitSquareGlobalLossThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s →
      (unitSquareGlobalLossBase : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((128 : ℝ)⁻¹) := by
  obtain ⟨Q₀, hQ₀⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually
      unitSquareGlobalLossBase 128 (by
        norm_num [unitSquareGlobalLossBase]) (by omega)
  refine ⟨Q₀, ?_⟩
  intro s hs hq
  have h := hQ₀ (n := primeSetModulus s) hq
  rw [primeFactors_primeSetModulus s hs] at h
  simpa [one_div] using h

lemma rpow_inv_one_twenty_eight_le_inv_sixty_four_of_le_sq
    {Q q : ℕ} (hq : 0 < q) (hQ : (Q : ℝ) ≤ (q : ℝ) ^ 2) :
    (Q : ℝ) ^ ((128 : ℝ)⁻¹) ≤
      (q : ℝ) ^ ((64 : ℝ)⁻¹) := by
  let a : ℝ := (Q : ℝ) ^ ((128 : ℝ)⁻¹)
  let b : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have haPow : a ^ 128 = (Q : ℝ) := by
    dsimp [a]
    exact Real.rpow_inv_natCast_pow (n := 128) (by positivity) (by norm_num)
  have hb64 : b ^ 64 = (q : ℝ) := by
    dsimp [b]
    exact Real.rpow_inv_natCast_pow (n := 64) (by positivity) (by norm_num)
  change a ≤ b
  apply le_of_pow_le_pow_left₀ (by omega : 128 ≠ 0) hb
  rw [haPow]
  calc
    (Q : ℝ) ≤ (q : ℝ) ^ 2 := hQ
    _ = (b ^ 64) ^ 2 := by rw [hb64]
    _ = b ^ 128 := by rw [← pow_mul]

/-- If a subproduct conductor is at least the square root of the full
conductor, the global prime-factor loss fits its local `q^(1/64)` majorant. -/
lemma unitSquare_local_losses_le_subpower_of_global_le_sq
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hts : t ⊆ s) (htne : t.Nonempty)
    (hthreshold :
      (unitSquareGlobalLossBase : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((128 : ℝ)⁻¹))
    (hrel : (primeSetModulus s : ℝ) ≤
      (primeSetModulus t : ℝ) ^ 2) :
    ((2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 ≤
        (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹)) ∧
      ((2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 *
          (3 : ℝ) ^ t.card ≤
        (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹)) := by
  have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
  have hqt : 0 < primeSetModulus t := primeSetModulus_pos t htprime
  have hroot := rpow_inv_one_twenty_eight_le_inv_sixty_four_of_le_sq hqt hrel
  constructor
  · exact (unitSquare_local_loss_without_three_le_global_base hts htne).trans
      (hthreshold.trans hroot)
  · exact (unitSquare_local_loss_le_global_base hts htne).trans
      (hthreshold.trans hroot)

lemma primeSetModulus_le_of_subset
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hts : t ⊆ s) :
    primeSetModulus t ≤ primeSetModulus s := by
  have hdiv : primeSetModulus t ∣ primeSetModulus s := by
    exact Finset.prod_dvd_prod_of_subset t s id hts
  exact Nat.le_of_dvd (primeSetModulus_pos s hs) hdiv

/-- Failure of completion forces the local subproduct conductor to be large.
Under the displayed global fourth-root estimate it is already larger than the
square root of the full conductor. -/
lemma completion_failure_local_scale
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hts : t ⊆ s) (_htne : t.Nonempty)
    {H : ℕ}
    (hroot : (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2)
    (hglobal :
      (16 : ℝ) * (8 : ℝ) ^ s.card *
          Real.log (primeSetModulus s) ≤
        (primeSetModulus s : ℝ) ^ ((4 : ℝ)⁻¹))
    (hfailure :
      unitSquareTermBudget s.card H <
        Real.log (primeSetModulus t) *
          Real.sqrt (primeSetModulus t)) :
    (primeSetModulus s : ℝ) < (primeSetModulus t : ℝ) ^ 2 ∧
      H < primeSetModulus t := by
  let Q : ℝ := primeSetModulus s
  let q : ℝ := primeSetModulus t
  let a : ℝ := Q ^ ((4 : ℝ)⁻¹)
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast primeSetModulus_pos s hs
  have hqpos : 0 < q := by
    dsimp [q]
    exact_mod_cast primeSetModulus_pos t (fun p hp ↦ hs p (hts hp))
  have hqtQnat : primeSetModulus t ≤ primeSetModulus s :=
    primeSetModulus_le_of_subset hs hts
  have hqtQ : q ≤ Q := by
    dsimp [q, Q]
    exact_mod_cast hqtQnat
  have hlog : Real.log q ≤ Real.log Q :=
    Real.log_le_log hqpos hqtQ
  have hsqrtQH : Real.sqrt Q ≤ H := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (H : ℝ))]
    exact Real.sqrt_le_sqrt hroot
  have hApos : (0 : ℝ) < 16 * 8 ^ s.card := by positivity
  have hHlt : (H : ℝ) <
      (16 * 8 ^ s.card) *
        (Real.log q * Real.sqrt q) := by
    have := (div_lt_iff₀ hApos).mp hfailure
    dsimp [unitSquareTermBudget, q] at this ⊢
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  have hglobal' :
      (16 * 8 ^ s.card) * Real.log q ≤ a := by
    calc
      (16 * 8 ^ s.card) * Real.log q ≤
          (16 * 8 ^ s.card) * Real.log Q := by gcongr
      _ ≤ a := by simpa only [Q, a] using hglobal
  have hsqrtLt : Real.sqrt Q < a * Real.sqrt q := by
    calc
      Real.sqrt Q ≤ H := hsqrtQH
      _ < (16 * 8 ^ s.card) * (Real.log q * Real.sqrt q) := hHlt
      _ = ((16 * 8 ^ s.card) * Real.log q) * Real.sqrt q := by ring
      _ ≤ a * Real.sqrt q := by gcongr
  have ha : 0 < a := by dsimp [a]; positivity
  have ha4 : a ^ 4 = Q := by
    dsimp [a]
    exact Real.rpow_inv_natCast_pow (n := 4) hQpos.le (by norm_num)
  have hsqrtQa : Real.sqrt Q = a ^ 2 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    calc
      Q = a ^ 4 := ha4.symm
      _ = a ^ 2 * a ^ 2 := by ring
  have hsqrtqSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hqpos.le
  rw [hsqrtQa] at hsqrtLt
  have ha_lt : a < Real.sqrt q := by nlinarith
  have ha2_lt : a ^ 2 < (Real.sqrt q) ^ 2 := by nlinarith
  have hsqroot_lt : Real.sqrt Q < q := by
    rw [hsqrtQa, ← hsqrtqSq]
    exact ha2_lt
  have hsqrtQSq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQpos.le
  have hfull : Q < q ^ 2 := by
    calc
      Q = (Real.sqrt Q) ^ 2 := hsqrtQSq.symm
      _ < q ^ 2 := by nlinarith [hsqroot_lt]
  have hHqReal : (H : ℝ) < q := by
    calc
      (H : ℝ) < (16 * 8 ^ s.card) *
          (Real.log q * Real.sqrt q) := hHlt
      _ = ((16 * 8 ^ s.card) * Real.log q) * Real.sqrt q := by ring
      _ ≤ a * Real.sqrt q := by gcongr
      _ < Real.sqrt q * Real.sqrt q := by gcongr
      _ = q := Real.mul_self_sqrt hqpos.le
  have hHqReal' : (H : ℝ) < (primeSetModulus t : ℝ) := by
    simpa only [q] using hHqReal
  exact ⟨hfull, by exact_mod_cast hHqReal'⟩

lemma full_conductor_le_sq_local_of_completion_failure
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hts : t ⊆ s) (htne : t.Nonempty)
    {H : ℕ}
    (hroot : (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2)
    (hglobal :
      (16 : ℝ) * (8 : ℝ) ^ s.card *
          Real.log (primeSetModulus s) ≤
        (primeSetModulus s : ℝ) ^ ((4 : ℝ)⁻¹))
    (hfailure :
      unitSquareTermBudget s.card H <
        Real.log (primeSetModulus t) *
          Real.sqrt (primeSetModulus t)) :
    (primeSetModulus s : ℝ) < (primeSetModulus t : ℝ) ^ 2 :=
  (completion_failure_local_scale hs hts htne hroot hglobal hfailure).1

/-- Eventually the global unit-sieve loss times the completion logarithm is
smaller than the fourth root of the full conductor. -/
theorem exists_unitSquareCompletionScaleThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s →
      (16 : ℝ) * (8 : ℝ) ^ s.card *
          Real.log (primeSetModulus s) ≤
        (primeSetModulus s : ℝ) ^ ((4 : ℝ)⁻¹) := by
  obtain ⟨Nω, hNω⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually 128 16 (by omega) (by omega)
  have ht : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ ((16 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      (4 : ℝ) ≤ (q : ℝ) ^ ((16 : ℝ)⁻¹) :=
    tendsto_atTop.mp ht 4
  rcases eventually_atTop.mp hev with ⟨Nᵣ, hNᵣ⟩
  refine ⟨max 2 (max Nω Nᵣ), ?_⟩
  intro s hs hq
  let Q : ℕ := primeSetModulus s
  let P : ℝ := (Q : ℝ) ^ ((16 : ℝ)⁻¹)
  have hQ₂ : 2 ≤ Q := (Nat.le_max_left _ _).trans hq
  have hQNω : Nω ≤ Q :=
    (Nat.le_max_left Nω Nᵣ).trans ((Nat.le_max_right 2 _).trans hq)
  have hQNᵣ : Nᵣ ≤ Q :=
    (Nat.le_max_right Nω Nᵣ).trans ((Nat.le_max_right 2 _).trans hq)
  have hsne : s.Nonempty := by
    by_contra h
    dsimp [Q] at hQ₂
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hQ₂
    simp [primeSetModulus] at hQ₂
  have hspos : 0 < s.card := hsne.card_pos
  have hlossRaw := hNω (n := Q) hQNω
  rw [show Q.primeFactors = s by
    simpa [Q] using primeFactors_primeSetModulus s hs] at hlossRaw
  have hlossPow : (128 : ℝ) ^ s.card ≤ P := by
    simpa [P, one_div] using hlossRaw
  have h16 : (16 : ℝ) ≤ (16 : ℝ) ^ s.card := by
    calc
      (16 : ℝ) = 16 ^ 1 := by simp
      _ ≤ 16 ^ s.card := pow_le_pow_right₀ (by norm_num) (by omega)
  have hloss : (16 : ℝ) * (8 : ℝ) ^ s.card ≤ P := by
    calc
      (16 : ℝ) * 8 ^ s.card ≤ 16 ^ s.card * 8 ^ s.card := by gcongr
      _ = 128 ^ s.card := by rw [← mul_pow]; norm_num
      _ ≤ P := hlossPow
  have hlog : Real.log (Q : ℝ) ≤ 16 * P := by
    have h := Real.log_natCast_le_rpow_div Q
      (show (0 : ℝ) < (1 : ℝ) / 16 by norm_num)
    calc
      Real.log (Q : ℝ) ≤ P * 16 := by
        simpa [P, one_div, div_eq_mul_inv] using h
      _ = 16 * P := by ring
  have hP4 : (4 : ℝ) ≤ P := hNᵣ Q hQNᵣ
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hcoef : (16 : ℝ) ≤ P ^ 2 := by nlinarith
  have htarget : P ^ 4 = (Q : ℝ) ^ ((4 : ℝ)⁻¹) := by
    calc
      P ^ 4 = (Q : ℝ) ^ (((16 : ℝ)⁻¹) * (4 : ℕ)) := by
        dsimp [P]
        exact (Real.rpow_mul_natCast (by positivity) _ 4).symm
      _ = (Q : ℝ) ^ ((4 : ℝ)⁻¹) := by norm_num
  calc
    (16 : ℝ) * 8 ^ s.card * Real.log (primeSetModulus s) =
        ((16 : ℝ) * 8 ^ s.card) * Real.log (Q : ℝ) := by rfl
    _ ≤ P * (16 * P) := by gcongr
    _ ≤ P * P ^ 3 := by
      have hm := mul_le_mul_of_nonneg_left hcoef hP₀
      nlinarith
    _ = P ^ 4 := by ring
    _ = (Q : ℝ) ^ ((4 : ℝ)⁻¹) := htarget

/-- At square-root interval length, the common unit-square error allowance is
eventually at least three.  This supplies both the minimum interval length
required by the Burgess certificate and the elementary main-term domination. -/
theorem exists_unitSquareBudgetThreeThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s → ∀ {H : ℕ},
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      (3 : ℝ) ≤ unitSquareTermBudget s.card H := by
  obtain ⟨Qc, hQc⟩ := exists_unitSquareCompletionScaleThreshold
  have ht : Tendsto (fun q : ℕ ↦ Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop, (3 : ℝ) ≤ Real.log (q : ℝ) :=
    tendsto_atTop.mp ht 3
  rcases eventually_atTop.mp hev with ⟨Nlog, hNlog⟩
  refine ⟨max 1 (max Qc Nlog), ?_⟩
  intro s hs hQ H hroot
  let Q : ℕ := primeSetModulus s
  have hQ1 : 1 ≤ Q := (Nat.le_max_left _ _).trans hQ
  have hQQc : Qc ≤ Q :=
    (Nat.le_max_left Qc Nlog).trans ((Nat.le_max_right 1 _).trans hQ)
  have hQNlog : Nlog ≤ Q :=
    (Nat.le_max_right Qc Nlog).trans ((Nat.le_max_right 1 _).trans hQ)
  have hscale := hQc s hs hQQc
  have hlog : (3 : ℝ) ≤ Real.log (Q : ℝ) := hNlog Q hQNlog
  have hsqrtH : Real.sqrt (Q : ℝ) ≤ H := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (H : ℝ))]
    exact Real.sqrt_le_sqrt (by simpa only [Q] using hroot)
  dsimp [unitSquareTermBudget]
  rw [le_div_iff₀ (show (0 : ℝ) < 16 * 8 ^ s.card by positivity)]
  calc
    (3 : ℝ) * (16 * 8 ^ s.card) =
        (16 * 8 ^ s.card) * 3 := by ring
    _ ≤ (16 * 8 ^ s.card) * Real.log (Q : ℝ) := by gcongr
    _ ≤ (Q : ℝ) ^ ((4 : ℝ)⁻¹) := by
      simpa only [Q] using hscale
    _ ≤ Real.sqrt Q := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ1) (by norm_num)
    _ ≤ H := hsqrtH

/-- The fifth power of the global Burgess loss dominates the square of the
unit-sieve denominator. -/
lemma unitSquareSieveScale_sq_le_loss_pow
    {w : ℕ} (hw : 0 < w) :
    ((16 : ℝ) * (8 : ℝ) ^ w) ^ 2 ≤
      (unitSquareBurgessLoss w : ℝ) ^ 5 := by
  have h512 : (8 : ℝ) ≤ (512 : ℝ) ^ w := by
    calc
      (8 : ℝ) ≤ 512 := by norm_num
      _ = 512 ^ 1 := by simp
      _ ≤ 512 ^ w := pow_le_pow_right₀ (by norm_num) hw
  norm_num only [unitSquareBurgessLoss, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow]
  rw [mul_pow, mul_pow]
  norm_num
  rw [show ((8 : ℝ) ^ w) ^ 2 = (64 : ℝ) ^ w by
    rw [← pow_mul, show w * 2 = 2 * w by omega, pow_mul]; norm_num]
  rw [show ((8 : ℝ) ^ w) ^ 5 = (32768 : ℝ) ^ w by
    rw [← pow_mul, show w * 5 = 5 * w by omega, pow_mul]; norm_num]
  have hm := mul_le_mul_of_nonneg_right h512
    (show (0 : ℝ) ≤ 32 * (64 : ℝ) ^ w by positivity)
  calc
    256 * (64 : ℝ) ^ w = 8 * (32 * 64 ^ w) := by ring
    _ ≤ 512 ^ w * (32 * 64 ^ w) := hm
    _ = 32 * (32768 : ℝ) ^ w := by
      calc
        512 ^ w * (32 * 64 ^ w) = 32 * (512 ^ w * 64 ^ w) := by ring
        _ = 32 * (32768 : ℝ) ^ w := by rw [← mul_pow]; norm_num

/-- Once the common character budget is exceeded, the local interval lies in
the relaxed Burgess range. -/
lemma relaxed_conductor_range_of_budget_lt
    {s t : Finset ℕ} (hts : t ⊆ s) (htne : t.Nonempty)
    {H L : ℕ}
    (hroot : (primeSetModulus t : ℝ) ≤ (H : ℝ) ^ 2)
    (hloss :
      (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 ≤
        (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹))
    (hbudget : unitSquareTermBudget s.card H < L) :
    (primeSetModulus t : ℝ) ≤
      (L : ℝ) ^ 2 *
        (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹) := by
  have hspos : 0 < s.card := (htne.mono hts).card_pos
  have hscaleLoss := unitSquareSieveScale_sq_le_loss_pow hspos
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (10 * t.card) := one_le_pow₀ (by norm_num)
  have hscaleP : ((16 : ℝ) * 8 ^ s.card) ^ 2 ≤
      (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹) := by
    calc
      ((16 : ℝ) * 8 ^ s.card) ^ 2 ≤
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 := hscaleLoss
      _ = 1 * (unitSquareBurgessLoss s.card : ℝ) ^ 5 := by ring
      _ ≤ (2 : ℝ) ^ (10 * t.card) *
          (unitSquareBurgessLoss s.card : ℝ) ^ 5 := by gcongr
      _ ≤ _ := hloss
  have hApos : (0 : ℝ) < 16 * 8 ^ s.card := by positivity
  have hHL : (H : ℝ) < (16 * 8 ^ s.card) * L := by
    have := (div_lt_iff₀ hApos).mp hbudget
    simpa [unitSquareTermBudget, mul_assoc, mul_left_comm, mul_comm] using this
  have hsq : (H : ℝ) ^ 2 <
      ((16 : ℝ) * 8 ^ s.card) ^ 2 * (L : ℝ) ^ 2 := by nlinarith
  calc
    (primeSetModulus t : ℝ) ≤ (H : ℝ) ^ 2 := hroot
    _ ≤ ((16 : ℝ) * 8 ^ s.card) ^ 2 * (L : ℝ) ^ 2 := hsq.le
    _ ≤ (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹) * (L : ℝ) ^ 2 := by gcongr
    _ = (L : ℝ) ^ 2 *
        (primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹) := by ring

/-- A fixed base dominating the Burgess fit factor uniformly over every
subproduct conductor. -/
def unitSquareFitBase : ℕ := 16384 * 1024

lemma unitSquare_fit_factor_le_base
    {s t : Finset ℕ} (hts : t ⊆ s) (htne : t.Nonempty) :
    ((((2 * 4 ^ t.card) *
        burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) : ℕ) : ℝ) *
        ((16 : ℝ) * 8 ^ s.card)) ≤
      (unitSquareFitBase : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by
  have hcard : t.card ≤ s.card := Finset.card_le_card hts
  have hspos : 0 < s.card := (htne.mono hts).card_pos
  have h16 : (16 : ℝ) ^ t.card ≤ (16 : ℝ) ^ s.card :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hc : (16384 : ℝ) ≤ (16384 : ℝ) ^ s.card := by
    calc
      (16384 : ℝ) = 16384 ^ 1 := by simp
      _ ≤ 16384 ^ s.card := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num only [burgessDenominatorLossExtra, unitSquareBurgessLoss,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    ((2 : ℝ) * 4 ^ t.card *
        (256 * 4 ^ t.card * (2 * 8 ^ s.card) *
          burgessDyadicShift (primeSetModulus t))) *
          (16 * 8 ^ s.card) =
      16384 * (16 : ℝ) ^ t.card * (64 : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by
          rw [show (16 : ℝ) ^ t.card = 4 ^ t.card * 4 ^ t.card by
            rw [← mul_pow]; norm_num]
          rw [show (64 : ℝ) ^ s.card = 8 ^ s.card * 8 ^ s.card by
            rw [← mul_pow]; norm_num]
          ring
    _ ≤ 16384 * (16 : ℝ) ^ s.card * (64 : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by gcongr
    _ = 16384 * (1024 : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by
          calc
            16384 * (16 : ℝ) ^ s.card * 64 ^ s.card *
                burgessDyadicShift (primeSetModulus t) =
              16384 * ((16 : ℝ) ^ s.card * 64 ^ s.card) *
                burgessDyadicShift (primeSetModulus t) := by ring
            _ = 16384 * (1024 : ℝ) ^ s.card *
                burgessDyadicShift (primeSetModulus t) := by
                  rw [← mul_pow]
                  norm_num
    _ ≤ (16384 : ℝ) ^ s.card * (1024 : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by gcongr
    _ = (unitSquareFitBase : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) := by
          rw [← mul_pow]
          norm_num [unitSquareFitBase]

lemma rpow_eighth_sq_eq_rpow_quarter (Q : ℕ) :
    ((Q : ℝ) ^ ((8 : ℝ)⁻¹)) ^ 2 =
      (Q : ℝ) ^ ((4 : ℝ)⁻¹) := by
  calc
    ((Q : ℝ) ^ ((8 : ℝ)⁻¹)) ^ 2 =
        (Q : ℝ) ^ (((8 : ℝ)⁻¹) * (2 : ℕ)) := by
      exact (Real.rpow_mul_natCast (by positivity) _ 2).symm
    _ = (Q : ℝ) ^ ((4 : ℝ)⁻¹) := by norm_num

lemma rpow_quarter_le_sqrt (Q : ℕ) (hQ : 1 ≤ Q) :
    (Q : ℝ) ^ ((4 : ℝ)⁻¹) ≤ Real.sqrt Q := by
  rw [Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ)
  norm_num

lemma burgessDyadicShift_le_eighthRoot_of_le
    {q Q : ℕ} (hq : q ≠ 0) (hqQ : q ≤ Q) :
    (burgessDyadicShift q : ℝ) ≤ (Q : ℝ) ^ ((8 : ℝ)⁻¹) := by
  let P : ℝ := (Q : ℝ) ^ ((8 : ℝ)⁻¹)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hP8 : P ^ 8 = (Q : ℝ) := by
    dsimp [P]
    exact Real.rpow_inv_natCast_pow (n := 8) (by positivity) (by norm_num)
  apply le_of_pow_le_pow_left₀ (by omega : 8 ≠ 0) hP
  calc
    (burgessDyadicShift q : ℝ) ^ 8 ≤ q := by
      exact_mod_cast burgessDyadicShift_pow_eight_le hq
    _ ≤ Q := by exact_mod_cast hqQ
    _ = P ^ 8 := hP8.symm

lemma unitSquare_fit_scale
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (hts : t ⊆ s) (htne : t.Nonempty)
    (hfitLoss :
      (unitSquareFitBase : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((8 : ℝ)⁻¹)) :
    ((((2 * 4 ^ t.card) *
        burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) : ℕ) : ℝ) *
        ((16 : ℝ) * 8 ^ s.card)) ≤
      Real.sqrt (primeSetModulus s) := by
  have hqQ := primeSetModulus_le_of_subset hs hts
  have hqne := (primeSetModulus_pos t (fun p hp ↦ hs p (hts hp))).ne'
  have hV := burgessDyadicShift_le_eighthRoot_of_le hqne hqQ
  calc
    ((((2 * 4 ^ t.card) *
        burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) : ℕ) : ℝ) *
        ((16 : ℝ) * 8 ^ s.card)) ≤
      (unitSquareFitBase : ℝ) ^ s.card *
        burgessDyadicShift (primeSetModulus t) :=
          unitSquare_fit_factor_le_base hts htne
    _ ≤ (primeSetModulus s : ℝ) ^ ((8 : ℝ)⁻¹) *
        (primeSetModulus s : ℝ) ^ ((8 : ℝ)⁻¹) := by gcongr
    _ = (primeSetModulus s : ℝ) ^ ((4 : ℝ)⁻¹) := by
      rw [← pow_two, rpow_eighth_sq_eq_rpow_quarter]
    _ ≤ Real.sqrt (primeSetModulus s) :=
      rpow_quarter_le_sqrt _ (primeSetModulus_pos s hs)

theorem exists_unitSquareFitScaleThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s →
      (unitSquareFitBase : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((8 : ℝ)⁻¹) := by
  obtain ⟨Q₀, hQ₀⟩ := const_pow_primeFactors_card_le_rpow_eventually
    unitSquareFitBase 8 (by norm_num [unitSquareFitBase]) (by omega)
  refine ⟨Q₀, ?_⟩
  intro s hs hq
  have h := hQ₀ (n := primeSetModulus s) hq
  rw [primeFactors_primeSetModulus s hs] at h
  simpa [one_div] using h

/-- Uniformly in every nonempty prime subproduct whose square exceeds the
ambient squarefree modulus, the denominator range used by the fourth-moment
Burgess amplifier does not wrap modulo that subproduct once the ambient
modulus is large enough.  This is the second elementary scale estimate in
the Burgess replacement for Nguyen--Vu's printed composite Weyl lemma. -/
theorem exists_unitSquareWrapScaleThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s →
      ∀ t ⊆ s, t.Nonempty →
      (primeSetModulus s : ℝ) < (primeSetModulus t : ℝ) ^ 2 →
      (2 : ℝ) * ((16 : ℝ) * (8 : ℝ) ^ s.card) ^ 2 *
          Real.log (primeSetModulus s) ^ 2 <
        (burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) : ℝ) := by
  obtain ⟨Nω, hNω⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually 128 1024 (by omega) (by omega)
  let C : ℝ := 2 * 1024 ^ 2
  have ht : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ ((1024 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      max 1 (max C 65536) ≤ (q : ℝ) ^ ((1024 : ℝ)⁻¹) :=
    tendsto_atTop.mp ht (max 1 (max C 65536))
  rcases eventually_atTop.mp hev with ⟨Nᵣ, hNᵣ⟩
  refine ⟨max 2 (max Nω Nᵣ), ?_⟩
  intro s hs hQ t hts htne hrel
  let Q : ℕ := primeSetModulus s
  let q : ℕ := primeSetModulus t
  let P : ℝ := (Q : ℝ) ^ ((1024 : ℝ)⁻¹)
  let V : ℝ := burgessDyadicShift q
  have hQ₂ : 2 ≤ Q := (Nat.le_max_left _ _).trans hQ
  have hQNω : Nω ≤ Q :=
    (Nat.le_max_left Nω Nᵣ).trans ((Nat.le_max_right 2 _).trans hQ)
  have hQNᵣ : Nᵣ ≤ Q :=
    (Nat.le_max_right Nω Nᵣ).trans ((Nat.le_max_right 2 _).trans hQ)
  have hspos : 0 < s.card := (htne.mono hts).card_pos
  have hlossRaw := hNω (n := Q) hQNω
  rw [show Q.primeFactors = s by
    simpa [Q] using primeFactors_primeSetModulus s hs] at hlossRaw
  have hlossPow : (128 : ℝ) ^ s.card ≤ P := by
    simpa [P, one_div] using hlossRaw
  have h16 : (16 : ℝ) ≤ (16 : ℝ) ^ s.card := by
    calc
      (16 : ℝ) = 16 ^ 1 := by simp
      _ ≤ 16 ^ s.card := pow_le_pow_right₀ (by norm_num) (by omega)
  have hA : (16 : ℝ) * 8 ^ s.card ≤ P := by
    calc
      (16 : ℝ) * 8 ^ s.card ≤ 16 ^ s.card * 8 ^ s.card := by gcongr
      _ = 128 ^ s.card := by rw [← mul_pow]; norm_num
      _ ≤ P := hlossPow
  have hlog : Real.log (Q : ℝ) ≤ 1024 * P := by
    have h := Real.log_natCast_le_rpow_div Q
      (show (0 : ℝ) < (1 : ℝ) / 1024 by norm_num)
    calc
      Real.log (Q : ℝ) ≤ P * 1024 := by
        simpa [P, one_div, div_eq_mul_inv] using h
      _ = 1024 * P := by ring
  have hbig := hNᵣ Q hQNᵣ
  have hP₁ : (1 : ℝ) ≤ P := (le_max_left _ _).trans hbig
  have hPC : C ≤ P :=
    (le_max_left C 65536).trans ((le_max_right 1 _).trans hbig)
  have hP65536 : (65536 : ℝ) ≤ P :=
    (le_max_right C 65536).trans ((le_max_right 1 _).trans hbig)
  have hlog0 : 0 ≤ Real.log (Q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
  have hlhs :
      (2 : ℝ) * ((16 : ℝ) * 8 ^ s.card) ^ 2 *
          Real.log (Q : ℝ) ^ 2 ≤ P ^ 8 := by
    have hC4 : C ≤ P ^ 4 := by
      calc
        C ≤ P := hPC
        _ = P ^ 1 := by simp
        _ ≤ P ^ 4 := pow_le_pow_right₀ hP₁ (by omega)
    calc
      (2 : ℝ) * ((16 : ℝ) * 8 ^ s.card) ^ 2 *
          Real.log (Q : ℝ) ^ 2 ≤
        2 * P ^ 2 * (1024 * P) ^ 2 := by gcongr
      _ = C * P ^ 4 := by dsimp [C]; ring
      _ ≤ P ^ 4 * P ^ 4 := by gcongr
      _ = P ^ 8 := by ring
  have hP1024 : P ^ 1024 = (Q : ℝ) := by
    dsimp [P]
    exact Real.rpow_inv_natCast_pow (n := 1024) (by positivity) (by norm_num)
  have hP896 : (65536 : ℝ) ≤ P ^ 896 := by
    calc
      (65536 : ℝ) ≤ P := hP65536
      _ = P ^ 1 := by simp
      _ ≤ P ^ 896 := pow_le_pow_right₀ hP₁ (by omega)
  have hcoef : (65536 : ℝ) * P ^ 128 ≤ P ^ 1024 := by
    have hm := mul_le_mul_of_nonneg_right hP896
      (show (0 : ℝ) ≤ P ^ 128 by positivity)
    calc
      (65536 : ℝ) * P ^ 128 ≤ P ^ 896 * P ^ 128 := hm
      _ = P ^ 1024 := by ring
  have hqpos : 0 < q := primeSetModulus_pos t (fun p hp ↦ hs p (hts hp))
  have hqV : (q : ℝ) < 256 * V ^ 8 := by
    dsimp [V]
    exact_mod_cast lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight q
  have hqSq : (q : ℝ) ^ 2 < 65536 * V ^ 16 := by
    have hsq := (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ (q : ℝ))
      (by positivity)).mpr hqV
    nlinarith
  have hPq : P ^ 1024 < (q : ℝ) ^ 2 := by
    rw [hP1024]
    simpa only [Q, q] using hrel
  have hP128V : P ^ 128 < V ^ 16 := by
    nlinarith [hcoef, hPq, hqSq]
  have hP8V : P ^ 8 < V := by
    apply lt_of_pow_lt_pow_left₀ 16 (by positivity)
    calc
      (P ^ 8) ^ 16 = P ^ 128 := by ring
      _ < V ^ 16 := hP128V
  have hdV : V ≤
      (burgessDenominatorLossExtra t.card
        (unitSquareBurgessLoss s.card)
        (burgessDyadicShift (primeSetModulus t)) : ℝ) := by
    norm_num only [burgessDenominatorLossExtra, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow]
    dsimp only [V]
    have hcoefOne : (1 : ℝ) ≤
        256 * 4 ^ t.card * unitSquareBurgessLoss s.card := by
      norm_num only [unitSquareBurgessLoss, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_pow]
      have h4 : (1 : ℝ) ≤ 4 ^ t.card :=
        one_le_pow₀ (by norm_num)
      have h8 : (1 : ℝ) ≤ 8 ^ s.card :=
        one_le_pow₀ (by norm_num)
      calc
        (1 : ℝ) ≤ 256 * 1 * (2 * 1) := by norm_num
        _ ≤ 256 * 4 ^ t.card * (2 * 8 ^ s.card) := by gcongr
    nlinarith [show (0 : ℝ) ≤ burgessDyadicShift (primeSetModulus t) by
      positivity]
  calc
    (2 : ℝ) * ((16 : ℝ) * 8 ^ s.card) ^ 2 *
          Real.log (primeSetModulus s) ^ 2 =
        2 * ((16 : ℝ) * 8 ^ s.card) ^ 2 * Real.log (Q : ℝ) ^ 2 := by rfl
    _ ≤ P ^ 8 := hlhs
    _ < V := hP8V
    _ ≤ _ := hdV

/-- A cardinality-free sufficient condition for a coprime Burgess
certificate.  The admissible-denominator count may be replaced below by any
nonnegative real lower bound `L`, while occurrences on the upper-bound side
are enlarged to `U`. -/
lemma coprimeBurgessCertificate_of_explicit_majorant
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H U V : ℕ} {B L : ℝ}
    (hB : 0 ≤ B) (hL₀ : 0 ≤ L)
    (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hL : L ≤ (primeSetCoprimeDenominators s U).card)
    (hstrict :
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * U * V * (U * V)) ^ 4) <
        ((L * V) * B) ^ 4) :
    CoprimeBurgessCertificate s H B := by
  refine ⟨U, V, hU₀, hV₀, hHq, hUq, hVq, hUV, hsmall, ?_⟩
  let C := (primeSetCoprimeDenominators s U).card
  have hCU_nat : C ≤ U := card_primeSetCoprimeDenominators_le s U
  have hCU : (C : ℝ) ≤ U := by exact_mod_cast hCU_nat
  have hC₀ : (0 : ℝ) ≤ C := by positivity
  have hVreal : (0 : ℝ) ≤ V := by positivity
  have henergy :
      0 ≤ (((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U))) := by
    have hlog : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU₀)
    positivity
  have hmoment :
      0 ≤ 3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
        (V : ℝ) ^ 4 *
          ((3 : ℝ) ^ s.card * V ^ 2 *
            Real.sqrt (primeSetModulus s)) := by
    positivity
  have hleft :
      8 *
          (((((H * C : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * C * V * (U * V)) ^ 4) ≤
        8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * U * V * (U * V)) ^ 4) := by
    norm_num only [Nat.cast_mul]
    gcongr
  have hbase : (L * V) * B ≤ (((C * V : ℕ) : ℝ) * B) := by
    norm_num only [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hL hVreal) hB
  have hright : ((L * V) * B) ^ 4 ≤
      ((((C * V : ℕ) : ℝ) * B) ^ 4) := by
    exact pow_le_pow_left₀ (by positivity) hbase 4
  exact hleft.trans_lt hstrict |>.trans_le hright

/-- A coarser but asymptotically convenient Burgess certificate: the exact
denominator count is replaced by the elementary half-sieve lower bound, and
the ratio-energy logarithms are all evaluated at the ambient interval
length. -/
lemma coprimeBurgessCertificate_of_coarse_majorant
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H U V : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hsieve : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ U)
    (hstrict :
      8 *
          (((((H : ℝ) * U) ^ 2 *
              (2 * H * U * (1 + Real.log H) ^ 2)) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * U * V * (U * V)) ^ 4) <
        ((((U : ℝ) * (1 / 2 : ℝ) ^ (s.card + 1) * V) * B) ^ 4)) :
    CoprimeBurgessCertificate s H B := by
  have hUH : U ≤ H := by
    calc
      U = U * 1 := by omega
      _ ≤ U * V := Nat.mul_le_mul_left U (by omega)
      _ ≤ H := hUV
  have henergy := burgessEnergyFactor_le hU₀ hUH
  apply coprimeBurgessCertificate_of_explicit_majorant s hs hB
      (by positivity) hU₀ hV₀ hHq hUq hVq hUV hsmall
      (card_primeSetCoprimeDenominators_ge_half s hs U hsieve)
  refine lt_of_le_of_lt ?_ hstrict
  norm_num only [Nat.cast_mul]
  gcongr

/-- Purely algebraic parameter check for the corrected composite Burgess
fourth moment.  The two displayed main-term hypotheses are the fixed power
savings later supplied by `V ≈ q^(1/8)`; the factor `4^w` pays for the
coprime-denominator sieve and the shift error. -/
lemma burgessScaledAlgebra
    (w : ℕ) {q H U V : ℝ}
    (hH : 0 < H) (hU : 0 < U) (hV : 0 < V)
    (hscale₀ : 256 * (4 : ℝ) ^ w * U * V ≤ H)
    (hscale₁ : H ≤ 2 * (256 * (4 : ℝ) ^ w) * U * V)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2 * V)
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w * V ^ 3 *
          Real.sqrt q * (1 + Real.log H) ^ 2 ≤ H ^ 2) :
    8 *
          ((((H * U) ^ 2 *
              (2 * H * U * (1 + Real.log H) ^ 2)) *
            (3 * V ^ 2 * q +
              V ^ 4 * ((3 : ℝ) ^ w * V ^ 2 * Real.sqrt q))) +
            (2 * U * V * (U * V)) ^ 4) <
        (((U * (1 / 2 : ℝ) ^ (w + 1) * V) *
          (H / (16 * (2 : ℝ) ^ w))) ^ 4) := by
  let a : ℝ := (2 : ℝ) ^ w
  let d : ℝ := (3 : ℝ) ^ w
  let l : ℝ := 1 + Real.log H
  let r : ℝ := Real.sqrt q
  have ha : 0 < a := by positivity
  have hd : 0 < d := by positivity
  have hr : 0 ≤ r := by positivity
  have hfour : (4 : ℝ) ^ w = a ^ 2 := by
    calc
      (4 : ℝ) ^ w = ((2 : ℝ) ^ 2) ^ w := by norm_num
      _ = (2 : ℝ) ^ (2 * w) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (w * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ w) ^ 2 := by rw [pow_mul]
      _ = a ^ 2 := by rfl
  have hten : (2 : ℝ) ^ (10 * w) = a ^ 10 := by
    rw [show 10 * w = w * 10 by omega, pow_mul]
  have hhalf : (1 / 2 : ℝ) ^ (w + 1) = 1 / (2 * a) := by
    rw [pow_succ]
    simp only [one_div, inv_pow, a]
    field_simp
  rw [hfour] at hscale₀ hscale₁
  rw [hten] at hmain₁ hmain₂
  change 0 < H at hH
  change 0 < U at hU
  change 0 < V at hV
  change 0 ≤ r at hr
  change 3 * 2 ^ 35 * a ^ 10 * q * l ^ 2 ≤ H ^ 2 * V at hmain₁
  change 2 ^ 35 * a ^ 10 * d * V ^ 3 * r * l ^ 2 ≤ H ^ 2 at hmain₂
  change 256 * a ^ 2 * U * V ≤ H at hscale₀
  change H ≤ 2 * (256 * a ^ 2) * U * V at hscale₁
  let R : ℝ := (U * V * H / (32 * a ^ 2)) ^ 4
  let T₁ : ℝ := 48 * H ^ 3 * U ^ 3 * V ^ 2 * q * l ^ 2
  let T₂ : ℝ := 16 * H ^ 3 * U ^ 3 * V ^ 6 * d * r * l ^ 2
  let T₃ : ℝ := 128 * (U * V) ^ 8
  have hR : 0 < R := by dsimp [R]; positivity
  have hupper₁ : H ^ 2 * V ≤ 512 * a ^ 2 * H * U * V ^ 2 := by
    have := mul_le_mul_of_nonneg_right hscale₁
      (mul_nonneg hH.le hV.le)
    nlinarith
  have hbase₁ :
      3 * 2 ^ 26 * a ^ 8 * q * l ^ 2 ≤ H * U * V ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left
      (show 0 < 512 * a ^ 2 by positivity)).mp
    nlinarith [hmain₁, hupper₁]
  have hT₁ : T₁ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_left hbase₁
      (show 0 ≤ H ^ 3 * U ^ 3 * V ^ 2 by positivity)
    dsimp [T₁, R]
    rw [div_pow]
    field_simp
    nlinarith
  have hupper₂ : H ^ 2 ≤ 512 * a ^ 2 * H * U * V := by
    have := mul_le_mul_of_nonneg_right hscale₁ hH.le
    nlinarith
  have hbase₂ :
      2 ^ 26 * a ^ 8 * d * V ^ 2 * r * l ^ 2 ≤ H * U := by
    apply (mul_le_mul_iff_of_pos_left
      (show 0 < 512 * a ^ 2 * V by positivity)).mp
    nlinarith [hmain₂, hupper₂]
  have hT₂ : T₂ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_left hbase₂
      (show 0 ≤ H ^ 3 * U ^ 3 * V ^ 4 by positivity)
    dsimp [T₂, R]
    rw [div_pow]
    field_simp
    nlinarith
  have hscalePow : (256 * a ^ 2 * U * V) ^ 4 ≤ H ^ 4 :=
    pow_le_pow_left₀ (by positivity) hscale₀ 4
  have hT₃ : T₃ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_right hscalePow
      (show 0 ≤ U ^ 4 * V ^ 4 by positivity)
    dsimp [T₃, R]
    rw [div_pow]
    field_simp
    nlinarith
  rw [hhalf]
  change 8 *
          ((((H * U) ^ 2 * (2 * H * U * l ^ 2)) *
            (3 * V ^ 2 * q + V ^ 4 * (d * V ^ 2 * r))) +
            (2 * U * V * (U * V)) ^ 4) <
        ((U * (1 / (2 * a)) * V) * (H / (16 * a))) ^ 4
  have hleft :
      8 *
          ((((H * U) ^ 2 * (2 * H * U * l ^ 2)) *
            (3 * V ^ 2 * q + V ^ 4 * (d * V ^ 2 * r))) +
            (2 * U * V * (U * V)) ^ 4) = T₁ + T₂ + T₃ := by
    dsimp [T₁, T₂, T₃]
    ring
  have hright :
      ((U * (1 / (2 * a)) * V) * (H / (16 * a))) ^ 4 = R := by
    dsimp [R]
    field_simp
    <;> ring
  rw [hleft, hright]
  nlinarith

/-- Variant of `burgessScaledAlgebra` with an additional global loss `J`.
This is used to make the character bound uniform over all subproducts of the
full squarefree conductor. -/
lemma burgessScaledAlgebra_extraLoss
    (w : ℕ) {q H U V J : ℝ}
    (hH : 0 < H) (hU : 0 < U) (hV : 0 < V) (hJ : 0 < J)
    (hscale₀ : 256 * (4 : ℝ) ^ w * J * U * V ≤ H)
    (hscale₁ : H ≤ 2 * (256 * (4 : ℝ) ^ w * J) * U * V)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 * q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2 * V)
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 *
          (3 : ℝ) ^ w * V ^ 3 * Real.sqrt q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2) :
    8 *
          ((((H * U) ^ 2 *
              (2 * H * U * (1 + Real.log H) ^ 2)) *
            (3 * V ^ 2 * q +
              V ^ 4 * ((3 : ℝ) ^ w * V ^ 2 * Real.sqrt q))) +
            (2 * U * V * (U * V)) ^ 4) <
        (((U * (1 / 2 : ℝ) ^ (w + 1) * V) *
          (H / (16 * (2 : ℝ) ^ w * J))) ^ 4) := by
  let a : ℝ := (2 : ℝ) ^ w
  let d : ℝ := (3 : ℝ) ^ w
  let l : ℝ := 1 + Real.log H
  let r : ℝ := Real.sqrt q
  have ha : 0 < a := by positivity
  have hd : 0 < d := by positivity
  have hr : 0 ≤ r := by positivity
  have hfour : (4 : ℝ) ^ w = a ^ 2 := by
    calc
      (4 : ℝ) ^ w = ((2 : ℝ) ^ 2) ^ w := by norm_num
      _ = (2 : ℝ) ^ (2 * w) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (w * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ w) ^ 2 := by rw [pow_mul]
      _ = a ^ 2 := by rfl
  have hten : (2 : ℝ) ^ (10 * w) = a ^ 10 := by
    rw [show 10 * w = w * 10 by omega, pow_mul]
  have hhalf : (1 / 2 : ℝ) ^ (w + 1) = 1 / (2 * a) := by
    rw [pow_succ]
    simp only [one_div, inv_pow, a]
    field_simp
  rw [hfour] at hscale₀ hscale₁
  rw [hten] at hmain₁ hmain₂
  change 3 * 2 ^ 35 * a ^ 10 * J ^ 5 * q * l ^ 2 ≤ H ^ 2 * V at hmain₁
  change 2 ^ 35 * a ^ 10 * J ^ 5 * d * V ^ 3 * r * l ^ 2 ≤ H ^ 2 at hmain₂
  change 256 * a ^ 2 * J * U * V ≤ H at hscale₀
  change H ≤ 2 * (256 * a ^ 2 * J) * U * V at hscale₁
  let R : ℝ := (U * V * H / (32 * a ^ 2 * J)) ^ 4
  let T₁ : ℝ := 48 * H ^ 3 * U ^ 3 * V ^ 2 * q * l ^ 2
  let T₂ : ℝ := 16 * H ^ 3 * U ^ 3 * V ^ 6 * d * r * l ^ 2
  let T₃ : ℝ := 128 * (U * V) ^ 8
  have hR : 0 < R := by dsimp [R]; positivity
  have hupper₁ : H ^ 2 * V ≤
      512 * a ^ 2 * J * H * U * V ^ 2 := by
    have := mul_le_mul_of_nonneg_right hscale₁
      (mul_nonneg hH.le hV.le)
    nlinarith
  have hbase₁ :
      3 * 2 ^ 26 * a ^ 8 * J ^ 4 * q * l ^ 2 ≤ H * U * V ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left
      (show 0 < 512 * a ^ 2 * J by positivity)).mp
    nlinarith [hmain₁, hupper₁]
  have hT₁ : T₁ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_left hbase₁
      (show 0 ≤ H ^ 3 * U ^ 3 * V ^ 2 by positivity)
    dsimp [T₁, R]
    rw [div_pow]
    field_simp
    nlinarith
  have hupper₂ : H ^ 2 ≤ 512 * a ^ 2 * J * H * U * V := by
    have := mul_le_mul_of_nonneg_right hscale₁ hH.le
    nlinarith
  have hbase₂ :
      2 ^ 26 * a ^ 8 * J ^ 4 * d * V ^ 2 * r * l ^ 2 ≤ H * U := by
    apply (mul_le_mul_iff_of_pos_left
      (show 0 < 512 * a ^ 2 * J * V by positivity)).mp
    nlinarith [hmain₂, hupper₂]
  have hT₂ : T₂ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_left hbase₂
      (show 0 ≤ H ^ 3 * U ^ 3 * V ^ 4 by positivity)
    dsimp [T₂, R]
    rw [div_pow]
    field_simp
    nlinarith
  have hscalePow : (256 * a ^ 2 * J * U * V) ^ 4 ≤ H ^ 4 :=
    pow_le_pow_left₀ (by positivity) hscale₀ 4
  have hT₃ : T₃ ≤ R / 4 := by
    have hm := mul_le_mul_of_nonneg_right hscalePow
      (show 0 ≤ U ^ 4 * V ^ 4 by positivity)
    dsimp [T₃, R]
    rw [div_pow]
    field_simp
    nlinarith
  rw [hhalf]
  change 8 *
          ((((H * U) ^ 2 * (2 * H * U * l ^ 2)) *
            (3 * V ^ 2 * q + V ^ 4 * (d * V ^ 2 * r))) +
            (2 * U * V * (U * V)) ^ 4) <
        ((U * (1 / (2 * a)) * V) * (H / (16 * a * J))) ^ 4
  have hleft :
      8 *
          ((((H * U) ^ 2 * (2 * H * U * l ^ 2)) *
            (3 * V ^ 2 * q + V ^ 4 * (d * V ^ 2 * r))) +
            (2 * U * V * (U * V)) ^ 4) = T₁ + T₂ + T₃ := by
    dsimp [T₁, T₂, T₃]
    ring
  have hright :
      ((U * (1 / (2 * a)) * V) * (H / (16 * a * J))) ^ 4 = R := by
    dsimp [R]
    field_simp
    <;> ring
  rw [hleft, hright]
  nlinarith

/-- The two numerical hypotheses of `burgessScaledAlgebra` follow from one
subpower majorant `P`.  This isolates all analytic growth from the amplifier
algebra. -/
lemma burgessMainComparisons
    (w : ℕ) {q H V P : ℝ}
    (hq₀ : 0 ≤ q) (hV₀ : 0 ≤ V) (hP₀ : 0 ≤ P)
    (hlog₀ : 0 ≤ 1 + Real.log H)
    (hlog : 1 + Real.log H ≤ 128 * P)
    (hqH : q ≤ H ^ 2)
    (hVpow : V ^ 8 ≤ q)
    (hsqrt : Real.sqrt q ≤ 16 * V ^ 4)
    (hloss₂ : (2 : ℝ) ^ (10 * w) ≤ P)
    (hloss₂₃ : (2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w ≤ P)
    (hgrowth : 3 * (2 : ℝ) ^ 53 * P ^ 3 ≤ V) :
    (3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2 * V) ∧
      ((2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w * V ^ 3 *
          Real.sqrt q * (1 + Real.log H) ^ 2 ≤ H ^ 2) := by
  have hlogSq : (1 + Real.log H) ^ 2 ≤ (128 * P) ^ 2 :=
    pow_le_pow_left₀ hlog₀ hlog 2
  have hgrowth₁ : 3 * (2 : ℝ) ^ 49 * P ^ 3 ≤ V := by
    nlinarith [hgrowth]
  have hgrowth₂ : (2 : ℝ) ^ 53 * P ^ 3 ≤ V := by
    nlinarith [hgrowth]
  constructor
  · calc
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * q *
            (1 + Real.log H) ^ 2 ≤
          3 * (2 : ℝ) ^ 35 * P * q *
            (1 + Real.log H) ^ 2 := by gcongr
      _ ≤ 3 * (2 : ℝ) ^ 35 * P * q * (128 * P) ^ 2 := by gcongr
      _ = q * (3 * (2 : ℝ) ^ 49 * P ^ 3) := by ring
      _ ≤ q * V := mul_le_mul_of_nonneg_left hgrowth₁ hq₀
      _ ≤ H ^ 2 * V := mul_le_mul_of_nonneg_right hqH hV₀
  · calc
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w * V ^ 3 *
            Real.sqrt q * (1 + Real.log H) ^ 2 ≤
          (2 : ℝ) ^ 35 * P * V ^ 3 *
            Real.sqrt q * (1 + Real.log H) ^ 2 := by
              calc
                (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w *
                    V ^ 3 * Real.sqrt q * (1 + Real.log H) ^ 2 =
                    (2 : ℝ) ^ 35 *
                      ((2 : ℝ) ^ (10 * w) * (3 : ℝ) ^ w) *
                      V ^ 3 * Real.sqrt q * (1 + Real.log H) ^ 2 := by ring
                _ ≤ _ := by gcongr
      _ ≤ (2 : ℝ) ^ 35 * P * V ^ 3 * (16 * V ^ 4) *
          (1 + Real.log H) ^ 2 := by gcongr
      _ ≤ (2 : ℝ) ^ 35 * P * V ^ 3 * (16 * V ^ 4) *
          (128 * P) ^ 2 := by gcongr
      _ = ((2 : ℝ) ^ 53 * P ^ 3) * V ^ 7 := by ring
      _ ≤ V * V ^ 7 := mul_le_mul_of_nonneg_right hgrowth₂ (by positivity)
      _ = V ^ 8 := by ring
      _ ≤ q := hVpow
      _ ≤ H ^ 2 := hqH

/-- Extra-loss variant in the slightly sub-square-root range.  If
`q ≤ H² P`, one additional factor `P` in the dyadic-scale growth condition
pays both for the shorter interval and for the global character budget. -/
lemma burgessMainComparisons_extraLoss_relaxed
    (w : ℕ) {q H V P J : ℝ}
    (hq₀ : 0 ≤ q) (hV₀ : 0 ≤ V) (hP : 0 < P)
    (_hJ₀ : 0 ≤ J)
    (hlog₀ : 0 ≤ 1 + Real.log H)
    (hlog : 1 + Real.log H ≤ 128 * P)
    (hqH : q ≤ H ^ 2 * P)
    (hVpow : V ^ 8 ≤ q)
    (hsqrt : Real.sqrt q ≤ 16 * V ^ 4)
    (hloss₂ : (2 : ℝ) ^ (10 * w) * J ^ 5 ≤ P)
    (hloss₂₃ : (2 : ℝ) ^ (10 * w) * J ^ 5 * (3 : ℝ) ^ w ≤ P)
    (hgrowth : 3 * (2 : ℝ) ^ 53 * P ^ 4 ≤ V) :
    (3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 * q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2 * V) ∧
      ((2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 *
          (3 : ℝ) ^ w * V ^ 3 * Real.sqrt q *
          (1 + Real.log H) ^ 2 ≤ H ^ 2) := by
  have hlogSq : (1 + Real.log H) ^ 2 ≤ (128 * P) ^ 2 :=
    pow_le_pow_left₀ hlog₀ hlog 2
  have hgrowth₁ : 3 * (2 : ℝ) ^ 49 * P ^ 4 ≤ V := by
    nlinarith [hgrowth]
  have hgrowth₂ : (2 : ℝ) ^ 53 * P ^ 4 ≤ V := by
    nlinarith [hgrowth]
  constructor
  · calc
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 * q *
            (1 + Real.log H) ^ 2 ≤
          3 * (2 : ℝ) ^ 35 * P * q *
            (1 + Real.log H) ^ 2 := by
              calc
                3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 * q *
                    (1 + Real.log H) ^ 2 =
                  3 * (2 : ℝ) ^ 35 *
                    ((2 : ℝ) ^ (10 * w) * J ^ 5) * q *
                    (1 + Real.log H) ^ 2 := by ring
                _ ≤ _ := by gcongr
      _ ≤ 3 * (2 : ℝ) ^ 35 * P * q * (128 * P) ^ 2 := by gcongr
      _ = q * (3 * (2 : ℝ) ^ 49 * P ^ 3) := by ring
      _ ≤ (H ^ 2 * P) * (3 * (2 : ℝ) ^ 49 * P ^ 3) := by gcongr
      _ = H ^ 2 * (3 * (2 : ℝ) ^ 49 * P ^ 4) := by ring
      _ ≤ H ^ 2 * V := mul_le_mul_of_nonneg_left hgrowth₁ (sq_nonneg H)
  · let X : ℝ :=
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 *
        (3 : ℝ) ^ w * V ^ 3 * Real.sqrt q *
        (1 + Real.log H) ^ 2
    have hX : X ≤ (2 : ℝ) ^ 53 * P ^ 3 * V ^ 7 := by
      dsimp only [X]
      calc
        (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 *
              (3 : ℝ) ^ w * V ^ 3 * Real.sqrt q *
              (1 + Real.log H) ^ 2 ≤
            (2 : ℝ) ^ 35 * P * V ^ 3 * Real.sqrt q *
              (1 + Real.log H) ^ 2 := by
                calc
                  (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * w) * J ^ 5 *
                        (3 : ℝ) ^ w * V ^ 3 * Real.sqrt q *
                        (1 + Real.log H) ^ 2 =
                    (2 : ℝ) ^ 35 *
                      ((2 : ℝ) ^ (10 * w) * J ^ 5 * (3 : ℝ) ^ w) *
                      V ^ 3 * Real.sqrt q * (1 + Real.log H) ^ 2 := by ring
                  _ ≤ _ := by gcongr
        _ ≤ (2 : ℝ) ^ 35 * P * V ^ 3 * (16 * V ^ 4) *
            (1 + Real.log H) ^ 2 := by gcongr
        _ ≤ (2 : ℝ) ^ 35 * P * V ^ 3 * (16 * V ^ 4) *
            (128 * P) ^ 2 := by gcongr
        _ = (2 : ℝ) ^ 53 * P ^ 3 * V ^ 7 := by ring
    have hPX : P * X ≤ q := by
      calc
        P * X ≤ P * ((2 : ℝ) ^ 53 * P ^ 3 * V ^ 7) :=
          mul_le_mul_of_nonneg_left hX hP.le
        _ = ((2 : ℝ) ^ 53 * P ^ 4) * V ^ 7 := by ring
        _ ≤ V * V ^ 7 := mul_le_mul_of_nonneg_right hgrowth₂ (by positivity)
        _ = V ^ 8 := by ring
        _ ≤ q := hVpow
    have hPH : P * X ≤ P * H ^ 2 := hPX.trans (by
      calc
        q ≤ H ^ 2 * P := hqH
        _ = P * H ^ 2 := by ring)
    have hPH' : P * X ≤ P * H ^ 2 := hPH
    dsimp only [X] at hPH'
    nlinarith

/-- The dyadic eighth-root scale eventually dominates any fixed multiple of
the cubic `q^(1/64)` loss.  The deliberately coarse threshold hypothesis is
easy to obtain from `tendsto_rpow_atTop`. -/
lemma burgessDyadicShift_dominates_subpower
    (q : ℕ) {C : ℝ}
    (hP₁ : (1 : ℝ) ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹))
    (hlarge :
      256 * C ^ 8 ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹)) :
    C * ((q : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 3 ≤
      burgessDyadicShift q := by
  let P : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  let V : ℝ := burgessDyadicShift q
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hV₀ : 0 ≤ V := by positivity
  have hP40 : P ≤ P ^ 40 := by
    calc
      P = P ^ 1 := by simp
      _ ≤ P ^ 40 := pow_le_pow_right₀ hP₁ (by omega)
  have hcoef : 256 * C ^ 8 ≤ P ^ 40 := hlarge.trans hP40
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ P ^ 24 by positivity)
  have hP64 : P ^ 64 = (q : ℝ) := by
    dsimp [P]
    exact Real.rpow_inv_natCast_pow (n := 64) (by positivity) (by norm_num)
  have hqV : (q : ℝ) < 256 * V ^ 8 := by
    dsimp [V]
    exact_mod_cast lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight q
  have hpowers : (C * P ^ 3) ^ 8 < V ^ 8 := by
    have haux : 256 * C ^ 8 * P ^ 24 ≤ (q : ℝ) := by
      calc
        256 * C ^ 8 * P ^ 24 ≤ P ^ 40 * P ^ 24 := hmul
        _ = P ^ 64 := by ring
        _ = q := hP64
    have : C ^ 8 * P ^ 24 < V ^ 8 := by nlinarith
    calc
      (C * P ^ 3) ^ 8 = C ^ 8 * P ^ 24 := by ring
      _ < V ^ 8 := this
  exact (lt_of_pow_lt_pow_left₀ 8 hV₀ hpowers).le

/-- The same dyadic comparison with a fourth power of the `q^(1/64)`
majorant.  This is the extra factor needed in the relaxed
`q ≤ H² q^(1/64)` range. -/
lemma burgessDyadicShift_dominates_fourth_subpower
    (q : ℕ) {C : ℝ}
    (hP₁ : (1 : ℝ) ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹))
    (hlarge :
      256 * C ^ 8 ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹)) :
    C * ((q : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 4 ≤
      burgessDyadicShift q := by
  let P : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  let V : ℝ := burgessDyadicShift q
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hV₀ : 0 ≤ V := by positivity
  have hP32 : P ≤ P ^ 32 := by
    calc
      P = P ^ 1 := by simp
      _ ≤ P ^ 32 := pow_le_pow_right₀ hP₁ (by omega)
  have hcoef : 256 * C ^ 8 ≤ P ^ 32 := hlarge.trans hP32
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ P ^ 32 by positivity)
  have hP64 : P ^ 64 = (q : ℝ) := by
    dsimp [P]
    exact Real.rpow_inv_natCast_pow (n := 64) (by positivity) (by norm_num)
  have hqV : (q : ℝ) < 256 * V ^ 8 := by
    dsimp [V]
    exact_mod_cast lt_two_hundred_fifty_six_mul_burgessDyadicShift_pow_eight q
  have hpowers : (C * P ^ 4) ^ 8 < V ^ 8 := by
    have haux : 256 * C ^ 8 * P ^ 32 ≤ (q : ℝ) := by
      calc
        256 * C ^ 8 * P ^ 32 ≤ P ^ 32 * P ^ 32 := hmul
        _ = P ^ 64 := by ring
        _ = q := hP64
    have : C ^ 8 * P ^ 32 < V ^ 8 := by nlinarith
    calc
      (C * P ^ 4) ^ 8 = C ^ 8 * P ^ 32 := by ring
      _ < V ^ 8 := this
  exact (lt_of_pow_lt_pow_left₀ 8 hV₀ hpowers).le

/-- Absolute conductor threshold for the fourth-subpower dyadic growth
comparison. -/
theorem exists_burgessFourthGrowthThreshold :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q →
      3 * (2 : ℝ) ^ 53 *
          ((q : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 4 ≤
        burgessDyadicShift q := by
  let C : ℝ := 3 * (2 : ℝ) ^ 53
  have ht : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ ((64 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      max 1 (256 * C ^ 8) ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹) :=
    tendsto_atTop.mp ht (max 1 (256 * C ^ 8))
  rcases eventually_atTop.mp hev with ⟨Q₀, hQ₀⟩
  refine ⟨Q₀, ?_⟩
  intro q hq
  have h := hQ₀ q hq
  apply burgessDyadicShift_dominates_fourth_subpower q
  · exact (le_max_left _ _).trans h
  · exact (le_max_right _ _).trans h

/-- Uniform threshold absorbing the two prime-factor losses and the remaining
fixed coefficient into the dyadic Burgess scale. -/
theorem exists_burgessLossThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s →
      let P := (primeSetModulus s : ℝ) ^ ((64 : ℝ)⁻¹)
      (2 : ℝ) ^ (10 * s.card) ≤ P ∧
      (2 : ℝ) ^ (10 * s.card) * (3 : ℝ) ^ s.card ≤ P ∧
      3 * (2 : ℝ) ^ 53 * P ^ 3 ≤
        burgessDyadicShift (primeSetModulus s) := by
  obtain ⟨N₂, hN₂⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually 1024 64 (by omega) (by omega)
  obtain ⟨N₂₃, hN₂₃⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually 3072 64 (by omega) (by omega)
  let C : ℝ := 3 * (2 : ℝ) ^ 53
  have ht : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ ((64 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      256 * C ^ 8 ≤ (q : ℝ) ^ ((64 : ℝ)⁻¹) :=
    tendsto_atTop.mp ht (256 * C ^ 8)
  rcases eventually_atTop.mp hev with ⟨Nᵣ, hNᵣ⟩
  refine ⟨max 1 (max N₂ (max N₂₃ Nᵣ)), ?_⟩
  intro s hs hq
  let q := primeSetModulus s
  let P : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  have hq1 : 1 ≤ q := (Nat.le_max_left _ _).trans hq
  have hqN₂ : N₂ ≤ q :=
    (Nat.le_max_left N₂ (max N₂₃ Nᵣ)).trans
      ((Nat.le_max_right 1 _).trans hq)
  have hqN₂₃ : N₂₃ ≤ q :=
    (Nat.le_max_left N₂₃ Nᵣ).trans
      ((Nat.le_max_right N₂ (max N₂₃ Nᵣ)).trans
        ((Nat.le_max_right 1 _).trans hq))
  have hqNᵣ : Nᵣ ≤ q :=
    (Nat.le_max_right N₂₃ Nᵣ).trans
      ((Nat.le_max_right N₂ (max N₂₃ Nᵣ)).trans
        ((Nat.le_max_right 1 _).trans hq))
  have hloss₂raw := hN₂ (n := q) hqN₂
  have hloss₂₃raw := hN₂₃ (n := q) hqN₂₃
  rw [primeFactors_primeSetModulus s hs] at hloss₂raw hloss₂₃raw
  have hloss₂ : (2 : ℝ) ^ (10 * s.card) ≤ P := by
    calc
      (2 : ℝ) ^ (10 * s.card) = ((2 : ℝ) ^ 10) ^ s.card := by
        rw [pow_mul]
      _ = (1024 : ℝ) ^ s.card := by norm_num
      _ ≤ P := by simpa [P, q, one_div] using hloss₂raw
  have hloss₂₃ :
      (2 : ℝ) ^ (10 * s.card) * (3 : ℝ) ^ s.card ≤ P := by
    calc
      (2 : ℝ) ^ (10 * s.card) * (3 : ℝ) ^ s.card =
          (((2 : ℝ) ^ 10) * 3) ^ s.card := by rw [pow_mul, mul_pow]
      _ = (3072 : ℝ) ^ s.card := by norm_num
      _ ≤ P := by simpa [P, q, one_div] using hloss₂₃raw
  have hP₁ : (1 : ℝ) ≤ P := by
    apply Real.one_le_rpow
    · exact_mod_cast hq1
    · norm_num
  have hgrowth := burgessDyadicShift_dominates_subpower q
    hP₁ (hNᵣ q hqNᵣ)
  exact ⟨hloss₂, hloss₂₃, by simpa [C, P, q] using hgrowth⟩

/-- Beyond one absolute conductor threshold, the two numerical Burgess
comparisons hold for every interval between `sqrt q` and `q`. -/
theorem exists_burgessMainThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s → ∀ {H : ℕ},
      3 ≤ H → H ≤ primeSetModulus s →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      (3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          primeSetModulus s * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2 * burgessDyadicShift (primeSetModulus s)) ∧
      ((2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          (3 : ℝ) ^ s.card * burgessDyadicShift (primeSetModulus s) ^ 3 *
          Real.sqrt (primeSetModulus s) * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2) := by
  obtain ⟨Q₁, hQ₁⟩ := exists_burgessLossThreshold
  refine ⟨max 3 Q₁, ?_⟩
  intro s hs hq H hH₃ hHq hqH
  have hq₃ : 3 ≤ primeSetModulus s := (Nat.le_max_left _ _).trans hq
  have hqQ₁ : Q₁ ≤ primeSetModulus s := (Nat.le_max_right _ _).trans hq
  have hloss := hQ₁ s hs hqQ₁
  let q := primeSetModulus s
  let V : ℝ := burgessDyadicShift q
  let P : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  have hq₀ : (0 : ℝ) ≤ q := by positivity
  have hV₀ : 0 ≤ V := by positivity
  have hP₀ : 0 ≤ P := by dsimp [P]; positivity
  have hlogH₀ : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
  have hlog₀ : 0 ≤ 1 + Real.log (H : ℝ) := by linarith
  have hlogq₁ : (1 : ℝ) ≤ Real.log (q : ℝ) :=
    one_le_log_nat_of_three_le hq₃
  have hlogHq : Real.log (H : ℝ) ≤ Real.log (q : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hHq)
  have hlogqP : Real.log (q : ℝ) ≤ 64 * P := by
    have h := Real.log_natCast_le_rpow_div q
      (show (0 : ℝ) < (1 : ℝ) / 64 by norm_num)
    calc
      Real.log (q : ℝ) ≤ P * 64 := by
        simpa [P, one_div, div_eq_mul_inv] using h
      _ = 64 * P := by ring
  have hlog : 1 + Real.log (H : ℝ) ≤ 128 * P := by
    calc
      1 + Real.log (H : ℝ) ≤ 2 * Real.log (q : ℝ) := by linarith
      _ ≤ 2 * (64 * P) := by gcongr
      _ = 128 * P := by ring
  have hVpow : V ^ 8 ≤ (q : ℝ) := by
    dsimp [V]
    exact_mod_cast burgessDyadicShift_pow_eight_le (by omega : q ≠ 0)
  have hsqrt : Real.sqrt (q : ℝ) ≤ 16 * V ^ 4 :=
    (sqrt_lt_sixteen_mul_burgessDyadicShift_pow_four q).le
  have hmain := burgessMainComparisons s.card hq₀ hV₀ hP₀ hlog₀
    hlog hqH hVpow hsqrt hloss.1 hloss.2.1 hloss.2.2
  simpa only [q, V, P] using hmain

/-- Ready-to-use certificate at the standard fourth-moment Burgess scale.
Only the two power comparisons and elementary range conditions remain. -/
lemma coprimeBurgessCertificate_of_scaled_parameters
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H U V : ℕ}
    (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hsieve : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ U)
    (hscale₀ :
      (256 : ℝ) * (4 : ℝ) ^ s.card * U * V ≤ H)
    (hscale₁ :
      (H : ℝ) ≤ 2 * (256 * (4 : ℝ) ^ s.card) * U * V)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          primeSetModulus s * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2 * V)
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          (3 : ℝ) ^ s.card * V ^ 3 *
          Real.sqrt (primeSetModulus s) * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2) :
    CoprimeBurgessCertificate s H
      ((H : ℝ) / (16 * (2 : ℝ) ^ s.card)) := by
  have hH₀ : 0 < H := by
    have hscalePos : (0 : ℝ) <
        256 * (4 : ℝ) ^ s.card * U * V := by positivity
    exact_mod_cast hscalePos.trans_le hscale₀
  apply coprimeBurgessCertificate_of_coarse_majorant
      s hs (by positivity) hU₀ hV₀ hHq hUq hVq hUV hsmall hsieve
  exact burgessScaledAlgebra s.card
    (q := (primeSetModulus s : ℝ)) (H := H) (U := U) (V := V)
    (by exact_mod_cast hH₀) (by exact_mod_cast hU₀)
    (by exact_mod_cast hV₀) hscale₀ hscale₁ hmain₁ hmain₂

/-- The scaled-parameter certificate with an additional global loss `J`.
This version is used when one character expansion contains every subproduct
of a larger squarefree conductor: the extra factor makes the individual
character bounds summable over that powerset. -/
lemma coprimeBurgessCertificate_of_scaled_parameters_extraLoss
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H U V : ℕ} {J : ℝ}
    (hJ : 0 < J)
    (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hsieve : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ U)
    (hscale₀ :
      (256 : ℝ) * (4 : ℝ) ^ s.card * J * U * V ≤ H)
    (hscale₁ :
      (H : ℝ) ≤ 2 * (256 * (4 : ℝ) ^ s.card * J) * U * V)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) * J ^ 5 *
          primeSetModulus s * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2 * V)
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) * J ^ 5 *
          (3 : ℝ) ^ s.card * V ^ 3 *
          Real.sqrt (primeSetModulus s) * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2) :
    CoprimeBurgessCertificate s H
      ((H : ℝ) / (16 * (2 : ℝ) ^ s.card * J)) := by
  have hH₀ : 0 < H := by
    have hscalePos : (0 : ℝ) <
        256 * (4 : ℝ) ^ s.card * J * U * V := by positivity
    exact_mod_cast hscalePos.trans_le hscale₀
  apply coprimeBurgessCertificate_of_coarse_majorant
      s hs (by positivity) hU₀ hV₀ hHq hUq hVq hUV hsmall hsieve
  exact burgessScaledAlgebra_extraLoss s.card
    (q := (primeSetModulus s : ℝ)) (H := H) (U := U) (V := V) (J := J)
    (by exact_mod_cast hH₀) (by exact_mod_cast hU₀)
    (by exact_mod_cast hV₀) hJ hscale₀ hscale₁ hmain₁ hmain₂

/-- A quotient by a positive scale is within a factor two of its ambient
length as soon as at least one scale block fits. -/
lemma div_scale_bounds {H d : ℕ} (hd : 0 < d) (hdH : d ≤ H) :
    d * (H / d) ≤ H ∧ H ≤ 2 * d * (H / d) := by
  have hU : 1 ≤ H / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdH)
  have hlow : d * (H / d) ≤ H := Nat.mul_div_le H d
  have hupp : H < d * (H / d + 1) := Nat.lt_mul_div_succ H hd
  constructor
  · exact hlow
  · calc
      H ≤ d * (H / d + 1) := hupp.le
      _ ≤ 2 * d * (H / d) := by nlinarith

/-- The full denominator loss used by the corrected fourth-moment
amplifier. -/
def burgessDenominatorLoss (w V : ℕ) : ℕ :=
  256 * 4 ^ w * V

/-- Canonical number of denominator shifts at the corrected Burgess scale. -/
def burgessDenominatorCount (w V H : ℕ) : ℕ :=
  H / burgessDenominatorLoss w V

lemma burgessDenominatorLoss_pos (w : ℕ) {V : ℕ} (hV : 0 < V) :
    0 < burgessDenominatorLoss w V := by
  simp [burgessDenominatorLoss, hV]

lemma burgessDenominatorCount_scale
    (w V H : ℕ) (hV : 0 < V)
    (hVH : burgessDenominatorLoss w V ≤ H) :
    256 * 4 ^ w * burgessDenominatorCount w V H * V ≤ H ∧
      H ≤ 2 * (256 * 4 ^ w) * burgessDenominatorCount w V H * V := by
  have h := div_scale_bounds
    (burgessDenominatorLoss_pos w hV) hVH
  rw [show burgessDenominatorLoss w V = 256 * 4 ^ w * V by rfl] at h
  constructor
  · simpa only [burgessDenominatorCount, burgessDenominatorLoss,
      mul_assoc, mul_left_comm, mul_comm] using h.1
  · simpa only [burgessDenominatorCount, burgessDenominatorLoss,
      mul_assoc, mul_left_comm, mul_comm] using h.2

/-- A convenient sufficient condition for the no-wrap hypothesis in the
ratio-energy count. -/
lemma burgessDenominatorCount_noWrap_of_sq_lt
    (w V H q : ℕ) (hV : 0 < V)
    (hsq : 2 * H ^ 2 < q * burgessDenominatorLoss w V) :
    2 * (burgessDenominatorCount w V H * H) < q := by
  let d := burgessDenominatorLoss w V
  let U := burgessDenominatorCount w V H
  have hd₀ : 0 < d := burgessDenominatorLoss_pos w hV
  have hlow : d * U ≤ H := by
    dsimp [U, burgessDenominatorCount]
    exact Nat.mul_div_le H d
  have hmul := Nat.mul_le_mul_left (2 * H) hlow
  have hcancel : d * (2 * (U * H)) < d * q := by
    calc
      d * (2 * (U * H)) = (2 * H) * (d * U) := by ring
      _ ≤ (2 * H) * H := hmul
      _ = 2 * H ^ 2 := by ring
      _ < q * d := hsq
      _ = d * q := by ring
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- Canonical denominator count for the extra-loss amplifier. -/
def burgessDenominatorCountExtra (w J V H : ℕ) : ℕ :=
  H / burgessDenominatorLossExtra w J V

lemma burgessDenominatorCountExtra_scale
    (w J V H : ℕ) (hJ : 0 < J) (hV : 0 < V)
    (hfit : burgessDenominatorLossExtra w J V ≤ H) :
    256 * 4 ^ w * J * burgessDenominatorCountExtra w J V H * V ≤ H ∧
      H ≤ 2 * (256 * 4 ^ w * J) *
        burgessDenominatorCountExtra w J V H * V := by
  have h := div_scale_bounds
    (burgessDenominatorLossExtra_pos w hJ hV) hfit
  rw [show burgessDenominatorLossExtra w J V =
      256 * 4 ^ w * J * V by rfl] at h
  constructor
  · simpa only [burgessDenominatorCountExtra, burgessDenominatorLossExtra,
      mul_assoc, mul_left_comm, mul_comm] using h.1
  · simpa only [burgessDenominatorCountExtra, burgessDenominatorLossExtra,
      mul_assoc, mul_left_comm, mul_comm] using h.2

lemma burgessDenominatorCountExtra_noWrap_of_sq_lt
    (w J V H q : ℕ) (hJ : 0 < J) (hV : 0 < V)
    (hsq : 2 * H ^ 2 < q * burgessDenominatorLossExtra w J V) :
    2 * (burgessDenominatorCountExtra w J V H * H) < q := by
  let d := burgessDenominatorLossExtra w J V
  let U := burgessDenominatorCountExtra w J V H
  have hd₀ : 0 < d := burgessDenominatorLossExtra_pos w hJ hV
  have hlow : d * U ≤ H := by
    dsimp [U, burgessDenominatorCountExtra]
    exact Nat.mul_div_le H d
  have hmul := Nat.mul_le_mul_left (2 * H) hlow
  have hcancel : d * (2 * (U * H)) < d * q := by
    calc
      d * (2 * (U * H)) = (2 * H) * (d * U) := by ring
      _ ≤ (2 * H) * H := hmul
      _ = 2 * H ^ 2 := by ring
      _ < q * d := hsq
      _ = d * q := by ring
  exact Nat.lt_of_mul_lt_mul_left hcancel

/-- The canonical choices `V ≈ q^(1/8)` and
`U = H / (256 * 4^w * V)` produce a Burgess certificate once the two
remaining power comparisons hold. -/
lemma coprimeBurgessCertificate_of_dyadic_parameters
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H : ℕ}
    (hq₂ : 2 ≤ primeSetModulus s)
    (hHq : H < primeSetModulus s)
    (hfit :
      (2 * 4 ^ s.card) *
          burgessDenominatorLoss s.card
            (burgessDyadicShift (primeSetModulus s)) ≤ H)
    (hsmall :
      2 * (burgessDenominatorCount s.card
          (burgessDyadicShift (primeSetModulus s)) H * H) <
        primeSetModulus s)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          primeSetModulus s * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2 * burgessDyadicShift (primeSetModulus s))
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) *
          (3 : ℝ) ^ s.card *
          burgessDyadicShift (primeSetModulus s) ^ 3 *
          Real.sqrt (primeSetModulus s) * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2) :
    CoprimeBurgessCertificate s H
      ((H : ℝ) / (16 * (2 : ℝ) ^ s.card)) := by
  let q := primeSetModulus s
  let V := burgessDyadicShift q
  let d := burgessDenominatorLoss s.card V
  let U := burgessDenominatorCount s.card V H
  have hV₀ : 0 < V := burgessDyadicShift_pos q
  have hd₀ : 0 < d := burgessDenominatorLoss_pos s.card hV₀
  have hfactor : 1 ≤ 2 * 4 ^ s.card := by
    have : 0 < 4 ^ s.card := pow_pos (by omega) _
    omega
  have hK : 1 ≤ 256 * 4 ^ s.card := by
    have : 0 < 4 ^ s.card := pow_pos (by omega) _
    omega
  have hdH : d ≤ H := by
    calc
      d = 1 * d := by simp
      _ ≤ (2 * 4 ^ s.card) * d := Nat.mul_le_mul_right d hfactor
      _ ≤ H := hfit
  have hU₀ : 0 < U := Nat.div_pos hdH hd₀
  have hscale := burgessDenominatorCount_scale s.card V H hV₀ hdH
  have hUV : U * V ≤ H := by
    calc
      U * V = 1 * (U * V) := by simp
      _ ≤ (256 * 4 ^ s.card) * (U * V) :=
        Nat.mul_le_mul_right (U * V) hK
      _ = 256 * 4 ^ s.card * U * V := by ring
      _ ≤ H := hscale.1
  have hUH : U ≤ H := by
    calc
      U = U * 1 := by simp
      _ ≤ U * V := Nat.mul_le_mul_left U hV₀
      _ ≤ H := hUV
  have hUq : U < q := hUH.trans_lt hHq
  have hVq : V < q := burgessDyadicShift_lt hq₂
  have hsieveNat : 2 * 4 ^ s.card ≤ U := by
    apply (Nat.le_div_iff_mul_le hd₀).mpr
    simpa [U, d, burgessDenominatorCount] using hfit
  apply coprimeBurgessCertificate_of_scaled_parameters s hs hU₀ hV₀
      hHq.le hUq hVq hUV hsmall
  · exact_mod_cast hsieveNat
  · exact_mod_cast hscale.1
  · exact_mod_cast hscale.2
  · simpa only [q, V, U] using hmain₁
  · simpa only [q, V, U] using hmain₂

/-- Dyadic Burgess parameters with an additional global loss `J`. -/
lemma coprimeBurgessCertificate_of_dyadic_parameters_extraLoss
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H J : ℕ}
    (hJ : 0 < J)
    (hq₂ : 2 ≤ primeSetModulus s)
    (hHq : H < primeSetModulus s)
    (hfit :
      (2 * 4 ^ s.card) *
          burgessDenominatorLossExtra s.card J
            (burgessDyadicShift (primeSetModulus s)) ≤ H)
    (hsmall :
      2 * (burgessDenominatorCountExtra s.card J
          (burgessDyadicShift (primeSetModulus s)) H * H) <
        primeSetModulus s)
    (hmain₁ :
      3 * (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) * (J : ℝ) ^ 5 *
          primeSetModulus s * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2 * burgessDyadicShift (primeSetModulus s))
    (hmain₂ :
      (2 : ℝ) ^ 35 * (2 : ℝ) ^ (10 * s.card) * (J : ℝ) ^ 5 *
          (3 : ℝ) ^ s.card *
          burgessDyadicShift (primeSetModulus s) ^ 3 *
          Real.sqrt (primeSetModulus s) * (1 + Real.log H) ^ 2 ≤
        (H : ℝ) ^ 2) :
    CoprimeBurgessCertificate s H
      ((H : ℝ) / (16 * (2 : ℝ) ^ s.card * J)) := by
  let q := primeSetModulus s
  let V := burgessDyadicShift q
  let d := burgessDenominatorLossExtra s.card J V
  let U := burgessDenominatorCountExtra s.card J V H
  have hV₀ : 0 < V := burgessDyadicShift_pos q
  have hd₀ : 0 < d := burgessDenominatorLossExtra_pos s.card hJ hV₀
  have hfactor : 1 ≤ 2 * 4 ^ s.card := by
    have : 0 < 4 ^ s.card := pow_pos (by omega) _
    omega
  have hK : 1 ≤ 256 * 4 ^ s.card * J := by
    have hp : 0 < 4 ^ s.card := pow_pos (by omega) _
    have hpos : 0 < 256 * 4 ^ s.card * J := by positivity
    omega
  have hdH : d ≤ H := by
    calc
      d = 1 * d := by simp
      _ ≤ (2 * 4 ^ s.card) * d := Nat.mul_le_mul_right d hfactor
      _ ≤ H := hfit
  have hU₀ : 0 < U := Nat.div_pos hdH hd₀
  have hscale := burgessDenominatorCountExtra_scale
    s.card J V H hJ hV₀ hdH
  have hUV : U * V ≤ H := by
    calc
      U * V = 1 * (U * V) := by simp
      _ ≤ (256 * 4 ^ s.card * J) * (U * V) :=
        Nat.mul_le_mul_right (U * V) hK
      _ = 256 * 4 ^ s.card * J * U * V := by ring
      _ ≤ H := hscale.1
  have hUH : U ≤ H := by
    calc
      U = U * 1 := by simp
      _ ≤ U * V := Nat.mul_le_mul_left U hV₀
      _ ≤ H := hUV
  have hUq : U < q := hUH.trans_lt hHq
  have hVq : V < q := burgessDyadicShift_lt hq₂
  have hsieveNat : 2 * 4 ^ s.card ≤ U := by
    apply (Nat.le_div_iff_mul_le hd₀).mpr
    simpa [U, d, burgessDenominatorCountExtra] using hfit
  apply coprimeBurgessCertificate_of_scaled_parameters_extraLoss
      s hs (by exact_mod_cast hJ) hU₀ hV₀ hHq.le hUq hVq hUV hsmall
  · exact_mod_cast hsieveNat
  · exact_mod_cast hscale.1
  · exact_mod_cast hscale.2
  · simpa only [q, V, U] using hmain₁
  · simpa only [q, V, U] using hmain₂

/-- Ready-to-use extra-loss certificate in the slightly sub-square-root
range `q ≤ H² q^(1/64)`.  All remaining hypotheses are elementary scale and
subpower comparisons. -/
lemma coprimeBurgessCertificate_of_relaxed_dyadic_range
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H J : ℕ} (hJ : 0 < J)
    (hq₃ : 3 ≤ primeSetModulus s)
    (hH₃ : 3 ≤ H) (hHq : H < primeSetModulus s)
    (hrelaxed :
      (primeSetModulus s : ℝ) ≤
        (H : ℝ) ^ 2 *
          (primeSetModulus s : ℝ) ^ ((64 : ℝ)⁻¹))
    (hfit :
      (2 * 4 ^ s.card) *
          burgessDenominatorLossExtra s.card J
            (burgessDyadicShift (primeSetModulus s)) ≤ H)
    (hsmall :
      2 * (burgessDenominatorCountExtra s.card J
          (burgessDyadicShift (primeSetModulus s)) H * H) <
        primeSetModulus s)
    (hloss₂ :
      (2 : ℝ) ^ (10 * s.card) * (J : ℝ) ^ 5 ≤
        (primeSetModulus s : ℝ) ^ ((64 : ℝ)⁻¹))
    (hloss₂₃ :
      (2 : ℝ) ^ (10 * s.card) * (J : ℝ) ^ 5 *
          (3 : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((64 : ℝ)⁻¹))
    (hgrowth :
      3 * (2 : ℝ) ^ 53 *
          ((primeSetModulus s : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 4 ≤
        burgessDyadicShift (primeSetModulus s)) :
    CoprimeBurgessCertificate s H
      ((H : ℝ) / (16 * (2 : ℝ) ^ s.card * J)) := by
  let q := primeSetModulus s
  let V : ℝ := burgessDyadicShift q
  let P : ℝ := (q : ℝ) ^ ((64 : ℝ)⁻¹)
  have hqpos : (0 : ℝ) < q := by positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hlogH₀ : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
  have hlog₀ : 0 ≤ 1 + Real.log (H : ℝ) := by linarith
  have hlogq₁ : (1 : ℝ) ≤ Real.log (q : ℝ) :=
    one_le_log_nat_of_three_le hq₃
  have hlogHq : Real.log (H : ℝ) ≤ Real.log (q : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hHq.le)
  have hlogqP : Real.log (q : ℝ) ≤ 64 * P := by
    have h := Real.log_natCast_le_rpow_div q
      (show (0 : ℝ) < (1 : ℝ) / 64 by norm_num)
    calc
      Real.log (q : ℝ) ≤ P * 64 := by
        simpa [P, one_div, div_eq_mul_inv] using h
      _ = 64 * P := by ring
  have hlog : 1 + Real.log (H : ℝ) ≤ 128 * P := by
    calc
      1 + Real.log (H : ℝ) ≤ 2 * Real.log (q : ℝ) := by linarith
      _ ≤ 2 * (64 * P) := by gcongr
      _ = 128 * P := by ring
  have hVpow : V ^ 8 ≤ (q : ℝ) := by
    dsimp [V]
    exact_mod_cast burgessDyadicShift_pow_eight_le (by omega : q ≠ 0)
  have hsqrt : Real.sqrt (q : ℝ) ≤ 16 * V ^ 4 :=
    (sqrt_lt_sixteen_mul_burgessDyadicShift_pow_four q).le
  have hmain := burgessMainComparisons_extraLoss_relaxed s.card
    (q := (q : ℝ)) (H := (H : ℝ)) (V := V) (P := P) (J := (J : ℝ))
    hqpos.le (by positivity) hP (by positivity) hlog₀ hlog
    (by simpa only [q, P] using hrelaxed) hVpow hsqrt
    (by simpa only [P, q] using hloss₂)
    (by simpa only [P, q] using hloss₂₃)
    (by simpa only [P, V, q] using hgrowth)
  exact coprimeBurgessCertificate_of_dyadic_parameters_extraLoss s hs hJ
    (by omega) hHq hfit hsmall hmain.1 hmain.2

/-- In the range where completion exceeds the global unit-square budget,
explicit fit and no-wrap scale comparisons yield the required local
extra-loss Burgess certificate. -/
lemma local_extraLoss_certificate_of_completion_failure
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (t : Finset ℕ) (hts : t ⊆ s) (htne : t.Nonempty)
    {H L : ℕ}
    (hrootFull : (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2)
    (hglobal :
      (16 : ℝ) * (8 : ℝ) ^ s.card *
          Real.log (primeSetModulus s) ≤
        (primeSetModulus s : ℝ) ^ ((4 : ℝ)⁻¹))
    (hglobalLoss :
      (unitSquareGlobalLossBase : ℝ) ^ s.card ≤
        (primeSetModulus s : ℝ) ^ ((128 : ℝ)⁻¹))
    (hq₃ : 3 ≤ primeSetModulus t)
    (hgrowth :
      3 * (2 : ℝ) ^ 53 *
          ((primeSetModulus t : ℝ) ^ ((64 : ℝ)⁻¹)) ^ 4 ≤
        burgessDyadicShift (primeSetModulus t))
    (hbudget₃ : (3 : ℝ) ≤ unitSquareTermBudget s.card H)
    (hfitScale :
      (((2 * 4 ^ t.card) *
          burgessDenominatorLossExtra t.card
            (unitSquareBurgessLoss s.card)
            (burgessDyadicShift (primeSetModulus t)) : ℕ) : ℝ) *
          ((16 : ℝ) * (8 : ℝ) ^ s.card) ≤
        Real.sqrt (primeSetModulus s))
    (hwrapScale :
      (2 : ℝ) * ((16 : ℝ) * (8 : ℝ) ^ s.card) ^ 2 *
          Real.log (primeSetModulus s) ^ 2 <
        (burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) : ℝ))
    (hLH : L ≤ H)
    (hbudget : unitSquareTermBudget s.card H < L)
    (hfailure :
      unitSquareTermBudget s.card H <
        Real.log (primeSetModulus t) *
          Real.sqrt (primeSetModulus t)) :
    CoprimeBurgessCertificate t L
      ((L : ℝ) /
        (16 * (2 : ℝ) ^ t.card * unitSquareBurgessLoss s.card)) := by
  have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
  have hlocal := completion_failure_local_scale hs hts htne
    hrootFull hglobal hfailure
  have hqQnat := primeSetModulus_le_of_subset hs hts
  have hqH : (primeSetModulus t : ℝ) ≤ (H : ℝ) ^ 2 := by
    exact (show (primeSetModulus t : ℝ) ≤ primeSetModulus s by
      exact_mod_cast hqQnat).trans hrootFull
  have hloss := unitSquare_local_losses_le_subpower_of_global_le_sq
    hs hts htne hglobalLoss hlocal.1.le
  have hrelaxed := relaxed_conductor_range_of_budget_lt hts htne
    hqH hloss.1 hbudget
  have hL₃ : 3 ≤ L := by
    have : (3 : ℝ) < L := hbudget₃.trans_lt hbudget
    exact_mod_cast this.le
  have hLq : L < primeSetModulus t := hLH.trans_lt hlocal.2
  have hsqrtQH : Real.sqrt (primeSetModulus s) ≤ H := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (H : ℝ))]
    exact Real.sqrt_le_sqrt hrootFull
  have hApos : (0 : ℝ) < (16 : ℝ) * 8 ^ s.card := by positivity
  have hHL : (H : ℝ) < ((16 : ℝ) * 8 ^ s.card) * L := by
    have := (div_lt_iff₀ hApos).mp hbudget
    simpa [unitSquareTermBudget, mul_assoc, mul_left_comm, mul_comm] using this
  let F : ℕ := (2 * 4 ^ t.card) *
    burgessDenominatorLossExtra t.card
      (unitSquareBurgessLoss s.card)
      (burgessDyadicShift (primeSetModulus t))
  have hfitReal : (F : ℝ) < L := by
    have hFA : (F : ℝ) * ((16 : ℝ) * 8 ^ s.card) ≤
        Real.sqrt (primeSetModulus s) := by simpa only [F] using hfitScale
    have : (F : ℝ) * ((16 : ℝ) * 8 ^ s.card) <
        (L : ℝ) * ((16 : ℝ) * 8 ^ s.card) := by
      calc
        (F : ℝ) * ((16 : ℝ) * 8 ^ s.card) ≤
            Real.sqrt (primeSetModulus s) := hFA
        _ ≤ H := hsqrtQH
        _ < ((16 : ℝ) * 8 ^ s.card) * L := hHL
        _ = (L : ℝ) * ((16 : ℝ) * 8 ^ s.card) := by ring
    nlinarith
  have hfit : F ≤ L := by exact_mod_cast hfitReal.le
  have hqpos : (0 : ℝ) < primeSetModulus t := by positivity
  have hqQ : (primeSetModulus t : ℝ) ≤ primeSetModulus s := by
    exact_mod_cast hqQnat
  have hlogqQ : Real.log (primeSetModulus t) ≤
      Real.log (primeSetModulus s) := Real.log_le_log hqpos hqQ
  have hlogq0 : 0 ≤ Real.log (primeSetModulus t) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ primeSetModulus t by omega))
  have hlogQ0 : 0 ≤ Real.log (primeSetModulus s) :=
    Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ primeSetModulus s from (primeSetModulus_pos s hs)))
  have hHupper : (H : ℝ) <
      ((16 : ℝ) * 8 ^ s.card) *
        (Real.log (primeSetModulus t) *
          Real.sqrt (primeSetModulus t)) := by
    have := (div_lt_iff₀ hApos).mp hfailure
    simpa [unitSquareTermBudget, mul_assoc, mul_left_comm, mul_comm] using this
  have hLsq : (2 : ℝ) * L ^ 2 <
      (primeSetModulus t : ℝ) *
        burgessDenominatorLossExtra t.card
          (unitSquareBurgessLoss s.card)
          (burgessDyadicShift (primeSetModulus t)) := by
    have hsqrtSq : Real.sqrt (primeSetModulus t) ^ 2 =
        (primeSetModulus t : ℝ) := Real.sq_sqrt hqpos.le
    have hLHreal : (L : ℝ) ≤ H := by exact_mod_cast hLH
    have hsqUpper : (2 : ℝ) * L ^ 2 <
        (2 : ℝ) * (((16 : ℝ) * 8 ^ s.card) ^ 2 *
          Real.log (primeSetModulus t) ^ 2) *
          (primeSetModulus t : ℝ) := by
      have hbaseLt := hLHreal.trans_lt hHupper
      have hsq := (sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ (L : ℝ))
        (by positivity)).mpr hbaseLt
      calc
        (2 : ℝ) * L ^ 2 <
            2 * (((16 : ℝ) * 8 ^ s.card) *
              (Real.log (primeSetModulus t) *
                Real.sqrt (primeSetModulus t))) ^ 2 := by nlinarith
        _ = 2 * (((16 : ℝ) * 8 ^ s.card) ^ 2 *
            Real.log (primeSetModulus t) ^ 2) *
            (primeSetModulus t : ℝ) := by
              simp only [mul_pow, hsqrtSq]
              ring
    calc
      (2 : ℝ) * L ^ 2 <
          2 * (((16 : ℝ) * 8 ^ s.card) ^ 2 *
            Real.log (primeSetModulus t) ^ 2) *
            (primeSetModulus t : ℝ) := hsqUpper
      _ ≤ 2 * (((16 : ℝ) * 8 ^ s.card) ^ 2 *
            Real.log (primeSetModulus s) ^ 2) *
            (primeSetModulus t : ℝ) := by gcongr
      _ < (burgessDenominatorLossExtra t.card
            (unitSquareBurgessLoss s.card)
            (burgessDyadicShift (primeSetModulus t)) : ℝ) *
            (primeSetModulus t : ℝ) := by
              apply mul_lt_mul_of_pos_right _ hqpos
              simpa only [mul_assoc] using hwrapScale
      _ = (primeSetModulus t : ℝ) *
          burgessDenominatorLossExtra t.card
            (unitSquareBurgessLoss s.card)
            (burgessDyadicShift (primeSetModulus t)) := by ring
  have hsqNat : 2 * L ^ 2 < primeSetModulus t *
      burgessDenominatorLossExtra t.card
        (unitSquareBurgessLoss s.card)
        (burgessDyadicShift (primeSetModulus t)) := by
    exact_mod_cast hLsq
  have hsmall := burgessDenominatorCountExtra_noWrap_of_sq_lt
    t.card (unitSquareBurgessLoss s.card)
    (burgessDyadicShift (primeSetModulus t)) L (primeSetModulus t)
    (unitSquareBurgessLoss_pos s.card) (burgessDyadicShift_pos _)
    hsqNat
  apply coprimeBurgessCertificate_of_relaxed_dyadic_range t htprime
      (unitSquareBurgessLoss_pos s.card) hq₃ hL₃ hLq hrelaxed
  · simpa only [F] using hfit
  · exact hsmall
  · exact hloss.1
  · exact hloss.2
  · exact hgrowth

/-- Uniform large-conductor certificate.  Only the elementary fit and
no-wrap inequalities for the chosen integer denominator range remain as
hypotheses. -/
theorem exists_coprimeBurgessCertificateThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s → ∀ {H : ℕ},
      3 ≤ H → H < primeSetModulus s →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      (2 * 4 ^ s.card) *
          burgessDenominatorLoss s.card
            (burgessDyadicShift (primeSetModulus s)) ≤ H →
      2 * (burgessDenominatorCount s.card
          (burgessDyadicShift (primeSetModulus s)) H * H) <
        primeSetModulus s →
      CoprimeBurgessCertificate s H
        ((H : ℝ) / (16 * (2 : ℝ) ^ s.card)) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_burgessMainThreshold
  refine ⟨max 3 Q₀, ?_⟩
  intro s hs hq H hH₃ hHq hqH hfit hsmall
  have hq₃ : 3 ≤ primeSetModulus s := (Nat.le_max_left _ _).trans hq
  have hqQ₀ : Q₀ ≤ primeSetModulus s := (Nat.le_max_right _ _).trans hq
  have hmain := hQ₀ s hs hqQ₀ hH₃ hHq.le hqH
  exact coprimeBurgessCertificate_of_dyadic_parameters s hs (by omega)
    hHq hfit hsmall hmain.1 hmain.2

/-- Uniformly for large squarefree conductors, the canonical denominator
range has enough room whenever the interval reaches the square-root scale. -/
theorem exists_burgessFitThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s → ∀ {H : ℕ},
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      (2 * 4 ^ s.card) *
          burgessDenominatorLoss s.card
            (burgessDyadicShift (primeSetModulus s)) ≤ H := by
  obtain ⟨N₁₆, hN₁₆⟩ :=
    const_pow_primeFactors_card_le_rpow_eventually 16 8 (by omega) (by omega)
  have ht : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ ((8 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      (512 : ℝ) ≤ (q : ℝ) ^ ((8 : ℝ)⁻¹) :=
    tendsto_atTop.mp ht 512
  rcases eventually_atTop.mp hev with ⟨Nᵣ, hNᵣ⟩
  refine ⟨max 1 (max N₁₆ Nᵣ), ?_⟩
  intro s hs hq H hqH
  let q := primeSetModulus s
  let V : ℝ := burgessDyadicShift q
  let P : ℝ := (q : ℝ) ^ ((8 : ℝ)⁻¹)
  have hq₁ : 1 ≤ q := (Nat.le_max_left _ _).trans hq
  have hqN₁₆ : N₁₆ ≤ q :=
    (Nat.le_max_left N₁₆ Nᵣ).trans ((Nat.le_max_right 1 _).trans hq)
  have hqNᵣ : Nᵣ ≤ q :=
    (Nat.le_max_right N₁₆ Nᵣ).trans ((Nat.le_max_right 1 _).trans hq)
  have hlossRaw := hN₁₆ (n := q) hqN₁₆
  rw [primeFactors_primeSetModulus s hs] at hlossRaw
  have hloss : (16 : ℝ) ^ s.card ≤ P := by
    simpa [P, q, one_div] using hlossRaw
  have hP₁ : (1 : ℝ) ≤ P := Real.one_le_rpow (by exact_mod_cast hq₁) (by norm_num)
  have hPbig : (512 : ℝ) ≤ P := hNᵣ q hqNᵣ
  have hP64 : P ^ 8 = (q : ℝ) := by
    dsimp [P]
    exact Real.rpow_inv_natCast_pow (n := 8) (by positivity) (by norm_num)
  have hVpow : V ^ 8 ≤ (q : ℝ) := by
    dsimp [V]
    exact_mod_cast burgessDyadicShift_pow_eight_le (by omega : q ≠ 0)
  have hVP : V ≤ P := by
    apply le_of_pow_le_pow_left₀ (by omega : 8 ≠ 0) (by positivity)
    simpa [hP64] using hVpow
  have hPsqrt : Real.sqrt (q : ℝ) = P ^ 4 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    calc
      (q : ℝ) = P ^ 8 := hP64.symm
      _ = P ^ 4 * P ^ 4 := by ring
  have hP2 : (512 : ℝ) ≤ P ^ 2 := by
    calc
      (512 : ℝ) ≤ P := hPbig
      _ = P ^ 1 := by simp
      _ ≤ P ^ 2 := pow_le_pow_right₀ hP₁ (by omega)
  have hfitReal :
      ((2 * 4 ^ s.card) *
          burgessDenominatorLoss s.card
            (burgessDyadicShift q) : ℕ) ≤ (H : ℝ) := by
    have hsqrtH : Real.sqrt (q : ℝ) ≤ H := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ H)]
      exact Real.sqrt_le_sqrt hqH
    norm_num only [burgessDenominatorLoss, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    calc
      (2 : ℝ) * 4 ^ s.card * (256 * 4 ^ s.card * V) =
          512 * (16 : ℝ) ^ s.card * V := by
            rw [show (16 : ℝ) ^ s.card = 4 ^ s.card * 4 ^ s.card by
              rw [← mul_pow]; norm_num]
            ring
      _ ≤ 512 * P * P := by gcongr
      _ ≤ P ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hP2 (show 0 ≤ P ^ 2 by positivity)
        nlinarith
      _ = Real.sqrt (q : ℝ) := hPsqrt.symm
      _ ≤ H := hsqrtH
  exact_mod_cast hfitReal

/-- Final asymptotic Burgess-certificate interface: at square-root interval
length, the sole remaining upper-range condition is the displayed natural
square inequality. -/
theorem exists_coprimeBurgessCertificateThreshold_of_sq_lt :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      Q₀ ≤ primeSetModulus s → ∀ {H : ℕ},
      3 ≤ H → H < primeSetModulus s →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      2 * H ^ 2 < primeSetModulus s *
        burgessDenominatorLoss s.card
          (burgessDyadicShift (primeSetModulus s)) →
      CoprimeBurgessCertificate s H
        ((H : ℝ) / (16 * (2 : ℝ) ^ s.card)) := by
  obtain ⟨Q₁, hQ₁⟩ := exists_coprimeBurgessCertificateThreshold
  obtain ⟨Q₂, hQ₂⟩ := exists_burgessFitThreshold
  refine ⟨max Q₁ Q₂, ?_⟩
  intro s hs hq H hH₃ hHq hqH hsq
  have hq₁ : Q₁ ≤ primeSetModulus s := (Nat.le_max_left _ _).trans hq
  have hq₂ : Q₂ ≤ primeSetModulus s := (Nat.le_max_right _ _).trans hq
  apply hQ₁ s hs hq₁ hH₃ hHq hqH
  · exact hQ₂ s hs hq₂ hqH
  · exact burgessDenominatorCount_noWrap_of_sq_lt _ _ _ _
      (burgessDyadicShift_pos _) hsq

/-- The inclusion--exclusion lower bound specialized as a sufficient
condition for the Burgess certificate. -/
lemma coprimeBurgessCertificate_of_sieve_majorant
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {H U V : ℕ} {B : ℝ}
    (hB : 0 ≤ B)
    (hL₀ : 0 ≤
      (U : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card)
    (hU₀ : 0 < U) (hV₀ : 0 < V)
    (hHq : H ≤ primeSetModulus s)
    (hUq : U < primeSetModulus s)
    (hVq : V < primeSetModulus s)
    (hUV : U * V ≤ H)
    (hsmall : 2 * (U * H) < primeSetModulus s)
    (hstrict :
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus s : ℝ) +
            (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ s.card * V ^ 2 *
                  Real.sqrt (primeSetModulus s)))) +
            ((2 : ℝ) * U * V * (U * V)) ^ 4) <
        ((((U : ℝ) * (1 / 2 : ℝ) ^ s.card -
            (2 : ℝ) ^ s.card) * V) * B) ^ 4) :
    CoprimeBurgessCertificate s H B := by
  exact coprimeBurgessCertificate_of_explicit_majorant s hs hB hL₀
    hU₀ hV₀ hHq hUq hVq hUV hsmall
    (card_primeSetCoprimeDenominators_lower s hs U) hstrict

/-- A finite rough-conductor square-hitting theorem.  If one choice of
amplifier parameters satisfies the explicit Burgess inequality for every
nonprincipal subproduct character, the square-class powerset expansion is
positive somewhere in the interval. -/
lemma exists_isSquare_primeSetModulus_of_uniform_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {M H U V : ℕ} {B : ℝ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hB : 0 ≤ B)
    (hlarge : ∀ p ∈ s, U < p)
    (hshift : ∀ p ∈ s, V < p)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hdom : ((s.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hparams : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      H ≤ primeSetModulus t ∧
      V < primeSetModulus t ∧
      2 * (U * H) < primeSetModulus t ∧
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus t : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ t.card *
                  Real.sqrt (primeSetModulus t)))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * B) ^ 4) :
    ∃ i ∈ Finset.range H,
      IsSquare (((M + i : ℕ) : ZMod (primeSetModulus s))) := by
  apply exists_isSquare_zmod_in_interval_of_uniform_character_bound
    (primeSetModulus_squarefree s hs)
  · simpa [primeFactors_primeSetModulus s hs] using hdom
  · intro t ht
    have ht' : t ∈ s.powerset.filter Finset.Nonempty := by
      simpa [primeFactors_primeSetModulus s hs] using ht
    have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have htne : t.Nonempty := (Finset.mem_filter.mp ht').2
    have hst : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (htsub hp)
    have hp := hparams t ht'
    exact (abs_quadraticPrimeFactorProduct_sum_lt_of_burgess
      t hst htne hH hU₀ hV₀ hB hp.1 hp.2.1
      (fun p hp' ↦ hlarge p (htsub hp'))
      (fun p hp' ↦ hshift p (htsub hp'))
      (fun p hp' ↦ hodd p (htsub hp')) hUV hp.2.2.1 hp.2.2.2).le

/-- Character-domination square-hitting for an arbitrary finite sequence.
This form is needed for the affine discriminant progression in the
Nguyen--Vu quadratic congruence. -/
lemma exists_isSquare_zmod_of_character_domination
    {q H : ℕ} (f : ℕ → ℕ) (hq : Squarefree q)
    (hdom :
      (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
          |∑ i ∈ Finset.range H,
            quadraticPrimeFactorProduct t (f i)|) < H) :
    ∃ i ∈ Finset.range H, IsSquare ((f i : ℕ) : ZMod q) := by
  classical
  by_contra hnone
  push Not at hnone
  let F : Finset ℕ → ℝ := fun t ↦
    ∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (f i)
  have htotal : (∑ t ∈ q.primeFactors.powerset, F t) = 0 := by
    calc
      (∑ t ∈ q.primeFactors.powerset, F t) =
          ∑ i ∈ Finset.range H,
            ∑ t ∈ q.primeFactors.powerset,
              quadraticPrimeFactorProduct t (f i) := by
        simp only [F]
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact sum_quadraticPrimeFactorProduct_eq_zero_of_not_isSquare
          hq (hnone i hi)
  have herase :
      q.primeFactors.powerset.erase ∅ =
        q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hempty : (∅ : Finset ℕ) ∈ q.primeFactors.powerset := by simp
  have hsplit :
      F ∅ + ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t = 0 := by
    rw [← herase, add_comm]
    exact (Finset.sum_erase_add _ _ hempty).trans htotal
  have hFempty : F ∅ = (H : ℝ) := by
    simp [F, quadraticPrimeFactorProduct]
  have hFabs :
      (H : ℝ) ≤ |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| := by
    rw [← hFempty]
    rw [show F ∅ = -(∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t) by
      linarith]
    exact neg_le_abs _
  have habs :
      |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| ≤
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle :
      (H : ℝ) ≤ ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    hFabs.trans habs
  exact (not_lt_of_ge hle) hdom

/-- Uniform character-bound version for an arbitrary finite sequence. -/
lemma exists_isSquare_zmod_of_uniform_character_bound
    {q H : ℕ} (f : ℕ → ℕ) (hq : Squarefree q) {B : ℝ}
    (hsmall :
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hbound : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (f i)| ≤ B) :
    ∃ i ∈ Finset.range H, IsSquare ((f i : ℕ) : ZMod q) := by
  apply exists_isSquare_zmod_of_character_domination f hq
  calc
    (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
        |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (f i)|) ≤
        ∑ _t ∈ q.primeFactors.powerset.filter Finset.Nonempty, B := by
      apply Finset.sum_le_sum
      intro t ht
      exact hbound t ht
    _ = ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B := by
      simp
    _ < _ := hsmall

/-- For one nonprincipal squarefree quadratic character, either completion or
an explicit coprime-denominator Burgess certificate gives the required bound.
Unlike the older uniform-amplifier interface, the Burgess parameters may be
chosen separately for each conductor. -/
lemma abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) (hne : s.Nonempty)
    (M H : ℕ) {B : ℝ} (hH : 0 < H) (hB : 0 ≤ B)
    (hcase :
      Real.log (primeSetModulus s) * Real.sqrt (primeSetModulus s) ≤ B ∨
        CoprimeBurgessCertificate s H B) :
    |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + i)| ≤ B := by
  rcases hcase with hcompletion | hburgess
  · exact (abs_sum_quadraticPrimeFactorProduct_le_completion_long
      s hs hodd hne M H).trans hcompletion
  · rcases hburgess with
      ⟨U, V, hU₀, hV₀, hHq, hUq, hVq, hUV, hsmall, hstrict⟩
    exact (abs_quadraticPrimeFactorProduct_sum_lt_of_coprime_burgess
      s hs hH hU₀ hV₀ hB hHq hUq hVq hodd hUV hsmall
      hstrict (M := M)).le

/-- Exact unit-square hitting with one uniform error allowance.  Every
divisor-class character sum may be discharged trivially, by Fourier
completion, or by its own coprime-denominator Burgess certificate. -/
lemma exists_coprime_isSquare_primeSetModulus_of_budget_cases
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) (M H : ℕ) (hH : 0 < H)
    (hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcases : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H →
        L ≤ H / (∏ p ∈ u, p) + 1 →
        (L : ℝ) ≤ unitSquareTermBudget s.card H ∨
        Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
          unitSquareTermBudget s.card H ∨
        (0 < L ∧ CoprimeBurgessCertificate t L
          (unitSquareTermBudget s.card H))) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime (primeSetModulus s) ∧
        IsSquare ((M + i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_primeSetModulus_of_interval_bounds
      s hs M H (fun _t _u ↦ unitSquareTermBudget s.card H)
  · intro t ht u hu
    exact unitSquareTermBudget_nonneg _ _
  · intro t ht u hu K L hLH hL
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
    have htodd : ∀ p ∈ t, p ≠ 2 := fun p hp ↦ hodd p (hts hp)
    have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
    rcases hcases t ht u hu K L hLH hL with htriv | hcompletion | hburgess
    · exact (abs_sum_quadraticPrimeFactorProduct_le_length
        t htprime K L).trans htriv
    · exact (abs_sum_quadraticPrimeFactorProduct_le_completion_long
        t htprime htodd htne K L).trans hcompletion
    · exact abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
        t htprime htodd htne K L hburgess.1
        (unitSquareTermBudget_nonneg _ _) (Or.inr hburgess.2)
  · exact unitSquareTermBudget_total_lt s hH hlarge

/-- Reduced analytic interface for the unit-square problem.  Once a local
extra-loss Burgess certificate is available precisely in the range where
neither the trivial bound nor completion suffices, the exact
inclusion--exclusion argument is complete. -/
lemma exists_coprime_isSquare_primeSetModulus_of_local_extraLoss_certificates
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2) (M H : ℕ) (hH : 0 < H)
    (hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcert : ∀ t ∈ s.powerset.filter Finset.Nonempty, ∀ L : ℕ,
      L ≤ H →
      unitSquareTermBudget s.card H < L →
      ¬ Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
        unitSquareTermBudget s.card H →
      CoprimeBurgessCertificate t L
        ((L : ℝ) /
          (16 * (2 : ℝ) ^ t.card * unitSquareBurgessLoss s.card))) :
    ∃ i ∈ Finset.range H,
      (M + i).Coprime (primeSetModulus s) ∧
        IsSquare ((M + i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_primeSetModulus_of_budget_cases
      s hs hodd M H hH hlarge
  intro t ht u hu K L hLH hL
  by_cases htriv : (L : ℝ) ≤ unitSquareTermBudget s.card H
  · exact Or.inl htriv
  right
  by_cases hcompletion :
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
        unitSquareTermBudget s.card H
  · exact Or.inl hcompletion
  right
  have huprime : ∀ p ∈ u, p.Prime := by
    intro p hp
    have hpst := Finset.mem_sdiff.mp
      (Finset.mem_powerset.mp hu hp)
    exact hs p hpst.1
  have hud : 0 < ∏ p ∈ u, p :=
    Finset.prod_pos fun p hp ↦ (huprime p hp).pos
  have hLpos : 0 < L := by
    have hbudget_nonneg := unitSquareTermBudget_nonneg s.card H
    exact_mod_cast lt_of_not_ge htriv |>.trans_le' hbudget_nonneg
  exact ⟨hLpos,
    (hcert t ht L hLH (lt_of_not_ge htriv) hcompletion).to_unitSquareTermBudget
      hH (hLH.trans (Nat.le_add_right H 1))⟩

/-- Automatic unit-square interval theorem for large odd squarefree
conductors.  This assembles the exact unit sieve with the completion/Burgess
split suggested in Nguyen--Vu, Remark 7.3. -/
theorem exists_unitSquareAnalyticThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      (∀ p ∈ s, p ≠ 2) → Q₀ ≤ primeSetModulus s →
      ∀ (M H : ℕ), 0 < H →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      ∃ i ∈ Finset.range H,
        (M + i).Coprime (primeSetModulus s) ∧
          IsSquare ((M + i : ℕ) : ZMod (primeSetModulus s)) := by
  obtain ⟨Qcomp, hcomp⟩ := exists_unitSquareCompletionScaleThreshold
  obtain ⟨Qloss, hloss⟩ := exists_unitSquareGlobalLossThreshold
  obtain ⟨Qfit, hfit⟩ := exists_unitSquareFitScaleThreshold
  obtain ⟨Qwrap, hwrap⟩ := exists_unitSquareWrapScaleThreshold
  obtain ⟨Qbudget, hbudget⟩ := exists_unitSquareBudgetThreeThreshold
  obtain ⟨Qgrowth, hgrowth⟩ := exists_burgessFourthGrowthThreshold
  let R : ℕ := max 3 Qgrowth
  refine ⟨max Qcomp (max Qloss (max Qfit (max Qwrap (max Qbudget (R ^ 2))))), ?_⟩
  intro s hs hodd hQ M H hH hroot
  let Q : ℕ := primeSetModulus s
  have hQcomp : Qcomp ≤ Q := by dsimp [Q]; omega
  have hQloss : Qloss ≤ Q := by dsimp [Q]; omega
  have hQfit : Qfit ≤ Q := by dsimp [Q]; omega
  have hQwrap : Qwrap ≤ Q := by dsimp [Q]; omega
  have hQbudget : Qbudget ≤ Q := by dsimp [Q]; omega
  have hR2Q : R ^ 2 ≤ Q := by dsimp [Q]; omega
  have hcompletionScale := hcomp s hs hQcomp
  have hglobalLoss := hloss s hs hQloss
  have hfitLoss := hfit s hs hQfit
  have hbudgetThree := hbudget s hs hQbudget hroot
  have hbudgetMul :
      (3 : ℝ) * ((16 : ℝ) * (8 : ℝ) ^ s.card) ≤ H := by
    dsimp [unitSquareTermBudget] at hbudgetThree
    exact (le_div_iff₀ (show (0 : ℝ) < 16 * 8 ^ s.card by positivity)).mp
      hbudgetThree
  have hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H := by
    calc
      (2 : ℝ) * 4 ^ s.card ≤ 2 * 8 ^ s.card := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (show (0 : ℝ) ≤ 4 by norm_num)
            (show (4 : ℝ) ≤ 8 by norm_num) s.card) (by norm_num)
      _ ≤ 3 * (16 * 8 ^ s.card) := by
        have hp : (0 : ℝ) ≤ 8 ^ s.card := by positivity
        nlinarith
      _ ≤ H := hbudgetMul
  apply exists_coprime_isSquare_primeSetModulus_of_local_extraLoss_certificates
      s hs hodd M H hH hlarge
  intro t ht L hLH hbudgetLt hnotCompletion
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hfailure :
      unitSquareTermBudget s.card H <
        Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) :=
    lt_of_not_ge hnotCompletion
  have hlocal := completion_failure_local_scale hs hts htne hroot
    hcompletionScale hfailure
  have hrel := hlocal.1
  have hQqSq : Q < (primeSetModulus t) ^ 2 := by
    exact_mod_cast (show (Q : ℝ) < (primeSetModulus t : ℝ) ^ 2 by
      simpa only [Q] using hrel)
  have hRlt : R < primeSetModulus t := by
    apply (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp
    exact hR2Q.trans_lt hQqSq
  have hq3 : 3 ≤ primeSetModulus t := by dsimp [R] at hRlt; omega
  have hqgrowth : Qgrowth ≤ primeSetModulus t := by
    dsimp [R] at hRlt
    omega
  have hfitScale := unitSquare_fit_scale hs hts htne hfitLoss
  have hwrapScale := hwrap s hs hQwrap t hts htne hrel
  exact local_extraLoss_certificate_of_completion_failure
    s hs t hts htne hroot hcompletionScale hglobalLoss hq3
    (hgrowth _ hqgrowth) hbudgetThree hfitScale hwrapScale
    hLH hbudgetLt hfailure

/-- Multiplication by a unit transports coprimality along an affine
congruence modulo a prime-set conductor. -/
lemma coprime_primeSet_affine_iff
    {s : Finset ℕ} {D R M i : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s]) :
    (D + R * i).Coprime (primeSetModulus s) ↔
      (M + i).Coprime (primeSetModulus s) := by
  have hcong : D + R * i ≡ R * (M + i) [MOD primeSetModulus s] := by
    calc
      D + R * i ≡ R * M + R * i [MOD primeSetModulus s] := hDM.add_right _
      _ = R * (M + i) := by ring
  rw [Nat.coprime_iff_gcd_eq_one, hcong.gcd_eq,
    ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_mul_iff_left]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hRcop, h⟩⟩

/-- A product character on an affine progression is a constant character
factor times the corresponding translated consecutive sum. -/
lemma quadraticPrimeFactorProduct_affine
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {D R M i : ℕ} (hDM : D ≡ R * M [MOD primeSetModulus s]) :
    quadraticPrimeFactorProduct s (D + R * i) =
      quadraticPrimeFactorProduct s R * quadraticPrimeFactorProduct s (M + i) := by
  rw [← quadraticPrimeFactorProduct_mul hs]
  apply quadraticPrimeFactorProduct_eq_of_modEq hs
  calc
    D + R * i ≡ R * M + R * i [MOD primeSetModulus s] := hDM.add_right _
    _ = R * (M + i) := by ring

/-- The unit-restricted character product has the same affine transport
law when the ratio is a unit modulo the full conductor. -/
lemma restrictedQuadraticPrimeFactorProduct_affine
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hts : t ⊆ s)
    {D R M i : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s]) :
    restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (D + R * i) =
      quadraticPrimeFactorProduct t R *
        restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i) := by
  have hcop := coprime_primeSet_affine_iff hRcop hDM (i := i)
  by_cases h : (M + i).Coprime (primeSetModulus s)
  · simp only [restrictedQuadraticPrimeFactorProduct, if_pos h,
      if_pos (hcop.mpr h)]
    rw [quadraticPrimeFactorProduct_affine
      (fun p hp ↦ hs p (hts hp)) (hDM.of_dvd
        (Finset.prod_dvd_prod_of_subset t s id hts))]
  · simp only [restrictedQuadraticPrimeFactorProduct, if_neg h,
      if_neg (fun hleft ↦ h (hcop.mp hleft)), mul_zero]

/-- Absolute-value transfer for a unit-restricted character sum on an affine
progression. -/
lemma abs_sum_restrictedQuadraticPrimeFactorProduct_affine_le
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (hts : t ⊆ s)
    {D R M H : ℕ} {B : ℝ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hbound : |∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)| ≤ B) :
    |∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (D + R * i)| ≤ B := by
  rw [Finset.sum_congr rfl (fun i hi ↦
      restrictedQuadraticPrimeFactorProduct_affine hs hts hRcop hDM),
    ← Finset.mul_sum, abs_mul]
  calc
    |quadraticPrimeFactorProduct t R| *
          |∑ i ∈ Finset.range H,
            restrictedQuadraticPrimeFactorProduct (primeSetModulus s) t (M + i)| ≤
        1 * B := mul_le_mul
          (abs_quadraticPrimeFactorProduct_le_one
            (fun p hp ↦ hs p (hts hp)) R)
          hbound (abs_nonneg _) (by positivity)
    _ = B := by ring

/-- Arbitrary-sequence version of the exact restricted-character criterion.
It is used for affine discriminant progressions, where the sequence is no
longer a translated consecutive interval. -/
lemma exists_coprime_isSquare_zmod_of_restricted_character_domination
    {q H : ℕ} (f : ℕ → ℕ) (hq : Squarefree q)
    (hdom :
      (∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct q ∅ (f i)) >
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
          |∑ i ∈ Finset.range H,
            restrictedQuadraticPrimeFactorProduct q t (f i)|) :
    ∃ i ∈ Finset.range H,
      (f i).Coprime q ∧ IsSquare ((f i : ℕ) : ZMod q) := by
  classical
  by_contra hnone
  push Not at hnone
  let F : Finset ℕ → ℝ := fun t ↦
    ∑ i ∈ Finset.range H,
      restrictedQuadraticPrimeFactorProduct q t (f i)
  have htotal : (∑ t ∈ q.primeFactors.powerset, F t) = 0 := by
    calc
      (∑ t ∈ q.primeFactors.powerset, F t) =
          ∑ i ∈ Finset.range H,
            ∑ t ∈ q.primeFactors.powerset,
              restrictedQuadraticPrimeFactorProduct q t (f i) := by
        simp only [F]
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [sum_restrictedQuadraticPrimeFactorProduct_powerset hq]
        rw [unitSquareExpansionValue,
          if_neg (fun h ↦ (hnone i hi h.1) h.2)]
  have herase :
      q.primeFactors.powerset.erase ∅ =
        q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hempty : (∅ : Finset ℕ) ∈ q.primeFactors.powerset := by simp
  have hsplit :
      F ∅ + ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t = 0 := by
    rw [← herase, add_comm]
    exact (Finset.sum_erase_add _ _ hempty).trans htotal
  have hFnonneg : 0 ≤ F ∅ := by
    dsimp only [F]
    apply Finset.sum_nonneg
    intro i hi
    by_cases hcop : (f i).Coprime q
    · simp only [restrictedQuadraticPrimeFactorProduct, if_pos hcop,
        quadraticPrimeFactorProduct, Finset.prod_empty]
      norm_num
    · simp only [restrictedQuadraticPrimeFactorProduct, if_neg hcop]
      norm_num
  have hFabs :
      F ∅ ≤ |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| := by
    rw [show F ∅ = -(∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t) by
      linarith]
    exact neg_le_abs _
  have habs :
      |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| ≤
        ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle :
      F ∅ ≤ ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t| :=
    hFabs.trans habs
  exact (not_lt_of_ge hle) hdom

/-- Exact unit sieve on a unit-ratio affine progression.  After
inclusion--exclusion, every local affine character sum is a constant unit
character times the corresponding ordinary translated interval sum. -/
lemma exists_coprime_isSquare_primeSetAffine_of_interval_bounds
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {D R M H : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (B : Finset ℕ → Finset ℕ → ℝ)
    (hB : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, 0 ≤ B t u)
    (hinterval : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H →
        L ≤ H / (∏ p ∈ u, p) + 1 →
        |∑ j ∈ Finset.range L,
          quadraticPrimeFactorProduct t (K + j)| ≤ B t u)
    (hbudget :
      (∑ t ∈ s.powerset.filter Finset.Nonempty,
        ∑ u ∈ (s \ t).powerset, B t u) <
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card) :
    ∃ i ∈ Finset.range H,
      (D + R * i).Coprime (primeSetModulus s) ∧
        IsSquare ((D + R * i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_zmod_of_restricted_character_domination
    (fun i ↦ D + R * i) (primeSetModulus_squarefree s hs)
  rw [primeFactors_primeSetModulus s hs]
  have hprincipal :
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
        ∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct
            (primeSetModulus s) ∅ (D + R * i) := by
    calc
      (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card ≤
          (shiftedPrimeSetCoprimeIndices s M H).card :=
        card_shiftedPrimeSetCoprimeIndices_lower s hs M H
      _ = ∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct
            (primeSetModulus s) ∅ (M + i) :=
        (sum_restrictedQuadraticPrimeFactorProduct_empty s M H).symm
      _ = ∑ i ∈ Finset.range H,
          restrictedQuadraticPrimeFactorProduct
            (primeSetModulus s) ∅ (D + R * i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have haff := restrictedQuadraticPrimeFactorProduct_affine
          hs (Finset.empty_subset s) hRcop hDM (i := i)
        simpa [quadraticPrimeFactorProduct] using haff.symm
  calc
    (∑ t ∈ s.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H,
        restrictedQuadraticPrimeFactorProduct
          (primeSetModulus s) t (D + R * i)|) ≤
        ∑ t ∈ s.powerset.filter Finset.Nonempty,
          ∑ u ∈ (s \ t).powerset, B t u := by
      apply Finset.sum_le_sum
      intro t ht
      have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
      apply abs_sum_restrictedQuadraticPrimeFactorProduct_affine_le
        hs hts hRcop hDM
      apply abs_sum_restrictedQuadraticPrimeFactorProduct_le_divisor_bounds
        hs hts M H (B t)
      intro u hu
      have htu : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
      have hus : u ⊆ s := fun p hp ↦
        (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hu hp)).1
      have hupos : 0 < ∏ p ∈ u, p := Finset.prod_pos fun p hp ↦
        (hs p (hus hp)).pos
      exact abs_divisible_quadraticPrimeFactorProduct_sum_le t htu M H
        (∏ p ∈ u, p) hupos (hB t ht u hu)
        (hinterval t ht u hu)
    _ < (H : ℝ) * (1 / 2 : ℝ) ^ s.card - (2 : ℝ) ^ s.card :=
      hbudget
    _ ≤ _ := hprincipal

/-- Uniform exact-budget form of the affine unit sieve. -/
lemma exists_coprime_isSquare_primeSetAffine_of_budget_cases
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2)
    {D R M : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (H : ℕ) (hH : 0 < H)
    (hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcases : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      ∀ u ∈ (s \ t).powerset, ∀ K L : ℕ,
        L ≤ H →
        L ≤ H / (∏ p ∈ u, p) + 1 →
        (L : ℝ) ≤ unitSquareTermBudget s.card H ∨
        Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
          unitSquareTermBudget s.card H ∨
        (0 < L ∧ CoprimeBurgessCertificate t L
          (unitSquareTermBudget s.card H))) :
    ∃ i ∈ Finset.range H,
      (D + R * i).Coprime (primeSetModulus s) ∧
        IsSquare ((D + R * i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_primeSetAffine_of_interval_bounds
      s hs hRcop hDM (fun _t _u ↦ unitSquareTermBudget s.card H)
  · intro t ht u hu
    exact unitSquareTermBudget_nonneg _ _
  · intro t ht u hu K L hLH hL
    have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have htprime : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (hts hp)
    have htodd : ∀ p ∈ t, p ≠ 2 := fun p hp ↦ hodd p (hts hp)
    have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
    rcases hcases t ht u hu K L hLH hL with htriv | hcompletion | hburgess
    · exact (abs_sum_quadraticPrimeFactorProduct_le_length
        t htprime K L).trans htriv
    · exact (abs_sum_quadraticPrimeFactorProduct_le_completion_long
        t htprime htodd htne K L).trans hcompletion
    · exact abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
        t htprime htodd htne K L hburgess.1
        (unitSquareTermBudget_nonneg _ _) (Or.inr hburgess.2)
  · exact unitSquareTermBudget_total_lt s hH hlarge

/-- Reduced affine interface using the same local certificates as the
consecutive-interval theorem. -/
lemma exists_coprime_isSquare_primeSetAffine_of_local_extraLoss_certificates
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, p ≠ 2)
    {D R M : ℕ}
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (H : ℕ) (hH : 0 < H)
    (hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H)
    (hcert : ∀ t ∈ s.powerset.filter Finset.Nonempty, ∀ L : ℕ,
      L ≤ H →
      unitSquareTermBudget s.card H < L →
      ¬ Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
        unitSquareTermBudget s.card H →
      CoprimeBurgessCertificate t L
        ((L : ℝ) /
          (16 * (2 : ℝ) ^ t.card * unitSquareBurgessLoss s.card))) :
    ∃ i ∈ Finset.range H,
      (D + R * i).Coprime (primeSetModulus s) ∧
        IsSquare ((D + R * i : ℕ) : ZMod (primeSetModulus s)) := by
  apply exists_coprime_isSquare_primeSetAffine_of_budget_cases
      s hs hodd hRcop hDM H hH hlarge
  intro t ht u hu K L hLH hL
  by_cases htriv : (L : ℝ) ≤ unitSquareTermBudget s.card H
  · exact Or.inl htriv
  right
  by_cases hcompletion :
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤
        unitSquareTermBudget s.card H
  · exact Or.inl hcompletion
  right
  have hLpos : 0 < L := by
    have hbudget_nonneg := unitSquareTermBudget_nonneg s.card H
    exact_mod_cast lt_of_not_ge htriv |>.trans_le' hbudget_nonneg
  exact ⟨hLpos,
    (hcert t ht L hLH (lt_of_not_ge htriv) hcompletion).to_unitSquareTermBudget
      hH (hLH.trans (Nat.le_add_right H 1))⟩

/-- Automatic affine unit-square theorem for large odd squarefree conductors.
This is the complete analytic input used by Nguyen--Vu's discriminant
progression. -/
theorem exists_unitSquareAffineAnalyticThreshold :
    ∃ Q₀ : ℕ, ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      (∀ p ∈ s, p ≠ 2) → Q₀ ≤ primeSetModulus s →
      ∀ (D R M H : ℕ),
      R.Coprime (primeSetModulus s) →
      D ≡ R * M [MOD primeSetModulus s] →
      0 < H →
      (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
      ∃ i ∈ Finset.range H,
        (D + R * i).Coprime (primeSetModulus s) ∧
          IsSquare ((D + R * i : ℕ) : ZMod (primeSetModulus s)) := by
  obtain ⟨Qcomp, hcomp⟩ := exists_unitSquareCompletionScaleThreshold
  obtain ⟨Qloss, hloss⟩ := exists_unitSquareGlobalLossThreshold
  obtain ⟨Qfit, hfit⟩ := exists_unitSquareFitScaleThreshold
  obtain ⟨Qwrap, hwrap⟩ := exists_unitSquareWrapScaleThreshold
  obtain ⟨Qbudget, hbudget⟩ := exists_unitSquareBudgetThreeThreshold
  obtain ⟨Qgrowth, hgrowth⟩ := exists_burgessFourthGrowthThreshold
  let T : ℕ := max 3 Qgrowth
  refine ⟨max Qcomp (max Qloss (max Qfit (max Qwrap (max Qbudget (T ^ 2))))), ?_⟩
  intro s hs hodd hQ D R M H hRcop hDM hH hroot
  let Q : ℕ := primeSetModulus s
  have hQcomp : Qcomp ≤ Q := by dsimp [Q]; omega
  have hQloss : Qloss ≤ Q := by dsimp [Q]; omega
  have hQfit : Qfit ≤ Q := by dsimp [Q]; omega
  have hQwrap : Qwrap ≤ Q := by dsimp [Q]; omega
  have hQbudget : Qbudget ≤ Q := by dsimp [Q]; omega
  have hT2Q : T ^ 2 ≤ Q := by dsimp [Q]; omega
  have hcompletionScale := hcomp s hs hQcomp
  have hglobalLoss := hloss s hs hQloss
  have hfitLoss := hfit s hs hQfit
  have hbudgetThree := hbudget s hs hQbudget hroot
  have hbudgetMul :
      (3 : ℝ) * ((16 : ℝ) * (8 : ℝ) ^ s.card) ≤ H := by
    dsimp [unitSquareTermBudget] at hbudgetThree
    exact (le_div_iff₀ (show (0 : ℝ) < 16 * 8 ^ s.card by positivity)).mp
      hbudgetThree
  have hlarge : (2 : ℝ) * (4 : ℝ) ^ s.card ≤ H := by
    calc
      (2 : ℝ) * 4 ^ s.card ≤ 2 * 8 ^ s.card := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (show (0 : ℝ) ≤ 4 by norm_num)
            (show (4 : ℝ) ≤ 8 by norm_num) s.card) (by norm_num)
      _ ≤ 3 * (16 * 8 ^ s.card) := by
        have hp : (0 : ℝ) ≤ 8 ^ s.card := by positivity
        nlinarith
      _ ≤ H := hbudgetMul
  apply exists_coprime_isSquare_primeSetAffine_of_local_extraLoss_certificates
      s hs hodd hRcop hDM H hH hlarge
  intro t ht L hLH hbudgetLt hnotCompletion
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have htne : t.Nonempty := (Finset.mem_filter.mp ht).2
  have hfailure :
      unitSquareTermBudget s.card H <
        Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) :=
    lt_of_not_ge hnotCompletion
  have hlocal := completion_failure_local_scale hs hts htne hroot
    hcompletionScale hfailure
  have hrel := hlocal.1
  have hQqSq : Q < (primeSetModulus t) ^ 2 := by
    exact_mod_cast (show (Q : ℝ) < (primeSetModulus t : ℝ) ^ 2 by
      simpa only [Q] using hrel)
  have hTlt : T < primeSetModulus t := by
    apply (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp
    exact hT2Q.trans_lt hQqSq
  have hq3 : 3 ≤ primeSetModulus t := by dsimp [T] at hTlt; omega
  have hqgrowth : Qgrowth ≤ primeSetModulus t := by
    dsimp [T] at hTlt
    omega
  have hfitScale := unitSquare_fit_scale hs hts htne hfitLoss
  have hwrapScale := hwrap s hs hQwrap t hts htne hrel
  exact local_extraLoss_certificate_of_completion_failure
    s hs t hts htne hroot hcompletionScale hglobalLoss hq3
    (hgrowth _ hqgrowth) hbudgetThree hfitScale hwrapScale
    hLH hbudgetLt hfailure

/-- Absolute-value transfer from a translated consecutive character sum to
an affine progression. -/
lemma abs_sum_quadraticPrimeFactorProduct_affine_le
    {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {D R M H : ℕ} {B : ℝ}
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hbound : |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (M + i)| ≤ B) :
    |∑ i ∈ Finset.range H,
      quadraticPrimeFactorProduct s (D + R * i)| ≤ B := by
  rw [Finset.sum_congr rfl (fun i hi ↦ quadraticPrimeFactorProduct_affine hs hDM),
    ← Finset.mul_sum, abs_mul]
  calc
    |quadraticPrimeFactorProduct s R| *
          |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct s (M + i)| ≤
        1 * B := mul_le_mul (abs_quadraticPrimeFactorProduct_le_one hs R)
          hbound (abs_nonneg _) (by positivity)
    _ = B := by ring

/-- Finite affine-progression version of the composite Burgess square-hitting
theorem.  This is the analytic input for completing the square in Proposition
7.2 of Nguyen--Vu. -/
lemma exists_isSquare_primeSetAffine_of_uniform_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {D R M H U V : ℕ} {B : ℝ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hB : 0 ≤ B)
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hlarge : ∀ p ∈ s, U < p)
    (hshift : ∀ p ∈ s, V < p)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hdom : ((s.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hparams : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      H ≤ primeSetModulus t ∧
      V < primeSetModulus t ∧
      2 * (U * H) < primeSetModulus t ∧
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus t : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ t.card *
                  Real.sqrt (primeSetModulus t)))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * B) ^ 4) :
    ∃ i ∈ Finset.range H,
      IsSquare (((D + R * i : ℕ) : ZMod (primeSetModulus s))) := by
  apply exists_isSquare_zmod_of_uniform_character_bound
    (fun i ↦ D + R * i) (primeSetModulus_squarefree s hs)
  · simpa [primeFactors_primeSetModulus s hs] using hdom
  · intro t ht
    have ht' : t ∈ s.powerset.filter Finset.Nonempty := by
      simpa [primeFactors_primeSetModulus s hs] using ht
    have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have htne : t.Nonempty := (Finset.mem_filter.mp ht').2
    have hst : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (htsub hp)
    have hmoddvd : primeSetModulus t ∣ primeSetModulus s := by
      exact Finset.prod_dvd_prod_of_subset t s id htsub
    apply abs_sum_quadraticPrimeFactorProduct_affine_le hst
      (hDM.of_dvd hmoddvd)
    have hp := hparams t ht'
    exact (abs_quadraticPrimeFactorProduct_sum_lt_of_burgess
      t hst htne hH hU₀ hV₀ hB hp.1 hp.2.1
      (fun p hp' ↦ hlarge p (htsub hp'))
      (fun p hp' ↦ hshift p (htsub hp'))
      (fun p hp' ↦ hodd p (htsub hp')) hUV hp.2.2.1 hp.2.2.2).le

/-- Affine square-hitting with the Nguyen--Vu completion/Burgess split made
separately for every nonempty subproduct character. -/
lemma exists_isSquare_primeSetAffine_of_completion_or_coprime_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {D R M H : ℕ} {B : ℝ}
    (hH : 0 < H) (hB : 0 ≤ B)
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hdom : ((s.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hcases : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤ B ∨
        CoprimeBurgessCertificate t H B) :
    ∃ i ∈ Finset.range H,
      IsSquare (((D + R * i : ℕ) : ZMod (primeSetModulus s))) := by
  apply exists_isSquare_zmod_of_uniform_character_bound
    (fun i ↦ D + R * i) (primeSetModulus_squarefree s hs)
  · simpa [primeFactors_primeSetModulus s hs] using hdom
  · intro t ht
    have ht' : t ∈ s.powerset.filter Finset.Nonempty := by
      simpa [primeFactors_primeSetModulus s hs] using ht
    have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have htne : t.Nonempty := (Finset.mem_filter.mp ht').2
    have hst : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (htsub hp)
    have hmoddvd : primeSetModulus t ∣ primeSetModulus s :=
      Finset.prod_dvd_prod_of_subset t s id htsub
    apply abs_sum_quadraticPrimeFactorProduct_affine_le hst
      (hDM.of_dvd hmoddvd)
    exact abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
      t hst (fun p hp ↦ hodd p (htsub hp)) htne M H hH hB
        (hcases t ht')

/-- Every residue class modulo a positive modulus occupies at most
`H / p + 1` places in `[0,H)`. -/
lemma card_filter_range_modEq_le (H p v : ℕ) (hp : 0 < p) :
    ((Finset.range H).filter fun i ↦ i ≡ v [MOD p]).card ≤ H / p + 1 := by
  rw [← Nat.count_eq_card_filter_range]
  rw [Nat.count_modEq_card H hp v]
  split_ifs <;> omega

/-- Shifted divisibility form of `card_filter_range_modEq_le`. -/
lemma card_filter_range_dvd_add_le (M H p : ℕ) (hp : 0 < p) :
    ((Finset.range H).filter fun i ↦ p ∣ M + i).card ≤ H / p + 1 := by
  letI : NeZero p := ⟨hp.ne'⟩
  let v : ℕ := (-(M : ZMod p)).val
  have hv : (v : ZMod p) = -(M : ZMod p) := ZMod.natCast_zmod_val _
  have hequiv (i : ℕ) : p ∣ M + i ↔ i ≡ v [MOD p] := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [← ZMod.natCast_eq_natCast_iff]
    constructor
    · intro hz
      calc
        (i : ZMod p) = (i : ZMod p) + ((M : ZMod p) + -(M : ZMod p)) := by ring
        _ = ((M + i : ℕ) : ZMod p) + -(M : ZMod p) := by push_cast; ring
        _ = -(M : ZMod p) := by rw [hz]; simp
        _ = (v : ZMod p) := hv.symm
    · intro hiv
      calc
        ((M + i : ℕ) : ZMod p) = (M : ZMod p) + (i : ZMod p) := by push_cast; ring
        _ = (M : ZMod p) + (v : ZMod p) := by rw [hiv]
        _ = 0 := by rw [hv]; ring
  have heq :
      ((Finset.range H).filter fun i ↦ p ∣ M + i) =
        ((Finset.range H).filter fun i ↦ i ≡ v [MOD p]) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hequiv]
  rw [heq]
  exact card_filter_range_modEq_le H p v hp

/-- If the affine ratio is a unit modulo a squarefree conductor, divisibility
by one of its prime factors is a single residue-class condition on the index. -/
lemma card_filter_range_prime_dvd_affine_le
    {s : Finset ℕ} {D R M H p : ℕ}
    (hs : ∀ r ∈ s, r.Prime) (hp : p ∈ s)
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s]) :
    ((Finset.range H).filter fun i ↦ p ∣ D + R * i).card ≤ H / p + 1 := by
  have hpdvd : p ∣ primeSetModulus s := dvd_primeSetModulus hp
  have hRp : p.Coprime R := (hRcop.of_dvd_right hpdvd).symm
  have hequiv (i : ℕ) : p ∣ D + R * i ↔ p ∣ M + i := by
    have hcong : D + R * i ≡ R * (M + i) [MOD p] := by
      calc
        D + R * i ≡ R * M + R * i [MOD p] :=
          (hDM.of_dvd hpdvd).add_right _
        _ = R * (M + i) := by ring
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    constructor
    · intro hleft
      have hright : R * (M + i) ≡ 0 [MOD p] := hcong.symm.trans hleft
      rw [Nat.modEq_zero_iff_dvd, hRp.dvd_mul_left] at hright
      exact Nat.modEq_zero_iff_dvd.mpr hright
    · intro hright
      have hdiv : p ∣ M + i := Nat.modEq_zero_iff_dvd.mp hright
      have hmul : p ∣ R * (M + i) := hRp.dvd_mul_left.mpr hdiv
      exact hcong.trans (Nat.modEq_zero_iff_dvd.mpr hmul)
  have heq :
      ((Finset.range H).filter fun i ↦ p ∣ D + R * i) =
        ((Finset.range H).filter fun i ↦ p ∣ M + i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hequiv]
  rw [heq]
  exact card_filter_range_dvd_add_le M H p (hs p hp).pos

/-- Union bound for the nonunits in an affine interval modulo a squarefree
prime-set conductor. -/
lemma card_filter_range_not_coprime_affine_le
    {s : Finset ℕ} {D R M H : ℕ}
    (hs : ∀ p ∈ s, p.Prime)
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s]) :
    ((Finset.range H).filter fun i ↦
        ¬(D + R * i).Coprime (primeSetModulus s)).card ≤
      ∑ p ∈ s, (H / p + 1) := by
  let bad := (Finset.range H).filter fun i ↦
    ¬(D + R * i).Coprime (primeSetModulus s)
  let fiber : ℕ → Finset ℕ := fun p ↦
    (Finset.range H).filter fun i ↦ p ∣ D + R * i
  have hsub : bad ⊆ s.biUnion fiber := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    obtain ⟨p, hpprime, hpfi, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hi'.2
    have hpqmem : p ∈ (primeSetModulus s).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hpprime, hpq, (primeSetModulus_pos s hs).ne'⟩
    have hps : p ∈ s := by
      rwa [primeFactors_primeSetModulus s hs] at hpqmem
    apply Finset.mem_biUnion.mpr
    exact ⟨p, hps, Finset.mem_filter.mpr ⟨hi'.1, hpfi⟩⟩
  calc
    bad.card ≤ (s.biUnion fiber).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ s, (fiber p).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ s, (H / p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact card_filter_range_prime_dvd_affine_le hs hp hRcop hDM

/-- Crude but uniform upper bound for one local-character powerset expansion. -/
lemma sum_quadraticPrimeFactorProduct_powerset_le_pow
    {q n : ℕ} :
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) ≤
      (2 : ℝ) ^ q.primeFactors.card := by
  calc
    (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n) ≤
        |∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t n| :=
      le_abs_self _
    _ ≤ ∑ t ∈ q.primeFactors.powerset,
        |quadraticPrimeFactorProduct t n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ q.primeFactors.powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      apply abs_quadraticPrimeFactorProduct_le_one
      intro p hp
      exact Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    _ = (2 : ℝ) ^ q.primeFactors.card := by simp

/-- Quantitative square-hitting criterion that also excludes all nonunits.
The error from nonprincipal characters and the maximum possible contribution
of the `K` bad indices together must be smaller than the principal term. -/
lemma exists_coprime_isSquare_zmod_of_uniform_character_bound_and_bad_count
    {q H K : ℕ} (f : ℕ → ℕ) (hq : Squarefree q) {B : ℝ}
    (hbad : ((Finset.range H).filter fun i ↦ ¬(f i).Coprime q).card ≤ K)
    (hdom : (2 : ℝ) ^ q.primeFactors.card * K +
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hbound : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      |∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (f i)| ≤ B) :
    ∃ i ∈ Finset.range H, (f i).Coprime q ∧ IsSquare ((f i : ℕ) : ZMod q) := by
  classical
  by_contra hnone
  push Not at hnone
  let F : Finset ℕ → ℝ := fun t ↦
    ∑ i ∈ Finset.range H, quadraticPrimeFactorProduct t (f i)
  let T : ℝ := ∑ t ∈ q.primeFactors.powerset, F t
  let E : ℝ := ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t|
  have herase :
      q.primeFactors.powerset.erase ∅ =
        q.primeFactors.powerset.filter Finset.Nonempty := by
    ext t
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  have hempty : (∅ : Finset ℕ) ∈ q.primeFactors.powerset := by simp
  have hsplit :
      T = F ∅ + ∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t := by
    dsimp only [T]
    rw [← herase, add_comm]
    exact (Finset.sum_erase_add _ _ hempty).symm
  have hFempty : F ∅ = (H : ℝ) := by
    simp [F, quadraticPrimeFactorProduct]
  have habs :
      |∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t| ≤ E := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hlower : (H : ℝ) - E ≤ T := by
    rw [hsplit, hFempty]
    linarith [neg_le_abs (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, F t)]
  have hTsum : T = ∑ i ∈ Finset.range H,
      ∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t (f i) := by
    dsimp only [T, F]
    rw [Finset.sum_comm]
  have hpoint (i : ℕ) (hi : i ∈ Finset.range H) :
      (∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t (f i)) ≤
        if ¬(f i).Coprime q then (2 : ℝ) ^ q.primeFactors.card else 0 := by
    by_cases hbad' : ¬(f i).Coprime q
    · rw [if_pos hbad']
      exact sum_quadraticPrimeFactorProduct_powerset_le_pow
    · rw [if_neg hbad']
      have hcop' : (f i).Coprime q := not_not.mp hbad'
      have hnotsq : ¬IsSquare ((f i : ℕ) : ZMod q) := hnone i hi hcop'
      rw [sum_quadraticPrimeFactorProduct_eq_zero_of_not_isSquare hq hnotsq]
  have hupper : T ≤
      (((Finset.range H).filter fun i ↦ ¬(f i).Coprime q).card : ℝ) *
        (2 : ℝ) ^ q.primeFactors.card := by
    rw [hTsum]
    calc
      (∑ i ∈ Finset.range H,
          ∑ t ∈ q.primeFactors.powerset, quadraticPrimeFactorProduct t (f i)) ≤
          ∑ i ∈ Finset.range H,
            if ¬(f i).Coprime q then (2 : ℝ) ^ q.primeFactors.card else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hpoint i hi
      _ = (((Finset.range H).filter fun i ↦ ¬(f i).Coprime q).card : ℝ) *
          (2 : ℝ) ^ q.primeFactors.card := by
        calc
          (∑ i ∈ Finset.range H,
              if ¬(f i).Coprime q then (2 : ℝ) ^ q.primeFactors.card else 0) =
              ∑ _i ∈ (Finset.range H).filter (fun i ↦ ¬(f i).Coprime q),
                (2 : ℝ) ^ q.primeFactors.card := by
            rw [Finset.sum_filter]
          _ = _ := by simp
  have hE : E ≤
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B := by
    dsimp only [E]
    calc
      (∑ t ∈ q.primeFactors.powerset.filter Finset.Nonempty, |F t|) ≤
          ∑ _t ∈ q.primeFactors.powerset.filter Finset.Nonempty, B := by
        apply Finset.sum_le_sum
        intro t ht
        exact hbound t ht
      _ = ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * B := by simp
  have hbad' :
      (((Finset.range H).filter fun i ↦ ¬(f i).Coprime q).card : ℝ) ≤ K := by
    exact_mod_cast hbad
  have hpow : 0 ≤ (2 : ℝ) ^ q.primeFactors.card := by positivity
  nlinarith

/-- Unit-square version of affine composite Burgess.  The first term in
`hdom` absorbs every affine value divisible by a conductor prime; the second
absorbs all nonprincipal character sums. -/
lemma exists_coprime_isSquare_primeSetAffine_of_uniform_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {D R M H U V : ℕ} {B : ℝ}
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hB : 0 ≤ B)
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hlarge : ∀ p ∈ s, U < p)
    (hshift : ∀ p ∈ s, V < p)
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hUV : U * V ≤ H)
    (hdom : (2 : ℝ) ^ s.card * (∑ p ∈ s, (H / p + 1)) +
      ((s.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hparams : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      H ≤ primeSetModulus t ∧
      V < primeSetModulus t ∧
      2 * (U * H) < primeSetModulus t ∧
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus t : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ t.card *
                  Real.sqrt (primeSetModulus t)))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * B) ^ 4) :
    ∃ i ∈ Finset.range H,
      (D + R * i).Coprime (primeSetModulus s) ∧
      IsSquare (((D + R * i : ℕ) : ZMod (primeSetModulus s))) := by
  apply exists_coprime_isSquare_zmod_of_uniform_character_bound_and_bad_count
    (fun i ↦ D + R * i) (primeSetModulus_squarefree s hs)
    (K := ∑ p ∈ s, (H / p + 1))
  · exact card_filter_range_not_coprime_affine_le hs hRcop hDM
  · simpa [primeFactors_primeSetModulus s hs] using hdom
  · intro t ht
    have ht' : t ∈ s.powerset.filter Finset.Nonempty := by
      simpa [primeFactors_primeSetModulus s hs] using ht
    have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have htne : t.Nonempty := (Finset.mem_filter.mp ht').2
    have hst : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (htsub hp)
    have hmoddvd : primeSetModulus t ∣ primeSetModulus s := by
      exact Finset.prod_dvd_prod_of_subset t s id htsub
    apply abs_sum_quadraticPrimeFactorProduct_affine_le hst
      (hDM.of_dvd hmoddvd)
    have hp := hparams t ht'
    exact (abs_quadraticPrimeFactorProduct_sum_lt_of_burgess
      t hst htne hH hU₀ hV₀ hB hp.1 hp.2.1
      (fun p hp' ↦ hlarge p (htsub hp'))
      (fun p hp' ↦ hshift p (htsub hp'))
      (fun p hp' ↦ hodd p (htsub hp')) hUV hp.2.2.1 hp.2.2.2).le

/-- Unit-square affine hitting with completion for the smaller subproduct
conductors and independent coprime-denominator Burgess certificates for the
remaining conductors.  This is the finite analytic conclusion required by
Nguyen--Vu's quadratic-congruence step. -/
lemma exists_coprime_isSquare_primeSetAffine_of_completion_or_coprime_burgess
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    {D R M H : ℕ} {B : ℝ}
    (hH : 0 < H) (hB : 0 ≤ B)
    (hRcop : R.Coprime (primeSetModulus s))
    (hDM : D ≡ R * M [MOD primeSetModulus s])
    (hodd : ∀ p ∈ s, p ≠ 2)
    (hdom : (2 : ℝ) ^ s.card * (∑ p ∈ s, (H / p + 1)) +
      ((s.powerset.filter Finset.Nonempty).card : ℝ) * B < H)
    (hcases : ∀ t ∈ s.powerset.filter Finset.Nonempty,
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤ B ∨
        CoprimeBurgessCertificate t H B) :
    ∃ i ∈ Finset.range H,
      (D + R * i).Coprime (primeSetModulus s) ∧
      IsSquare (((D + R * i : ℕ) : ZMod (primeSetModulus s))) := by
  apply exists_coprime_isSquare_zmod_of_uniform_character_bound_and_bad_count
    (fun i ↦ D + R * i) (primeSetModulus_squarefree s hs)
    (K := ∑ p ∈ s, (H / p + 1))
  · exact card_filter_range_not_coprime_affine_le hs hRcop hDM
  · simpa [primeFactors_primeSetModulus s hs] using hdom
  · intro t ht
    have ht' : t ∈ s.powerset.filter Finset.Nonempty := by
      simpa [primeFactors_primeSetModulus s hs] using ht
    have htsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have htne : t.Nonempty := (Finset.mem_filter.mp ht').2
    have hst : ∀ p ∈ t, p.Prime := fun p hp ↦ hs p (htsub hp)
    have hmoddvd : primeSetModulus t ∣ primeSetModulus s :=
      Finset.prod_dvd_prod_of_subset t s id htsub
    apply abs_sum_quadraticPrimeFactorProduct_affine_le hst
      (hDM.of_dvd hmoddvd)
    exact abs_sum_quadraticPrimeFactorProduct_le_of_completion_or_coprime_burgess
      t hst (fun p hp ↦ hodd p (htsub hp)) htne M H hH hB
        (hcases t ht')

/-! ## The valid Nguyen--Vu quadratic-congruence interface

Nguyen and Vu's published proof reduces its analytic input to finding a short
solution of one quadratic congruence.  Their displayed Weyl estimate is false
for general composite moduli, but their Remark 7.3 explains that the required
congruence can instead be obtained from Burgess's character-sum estimate.  The
following lemmas formalize the prime-power lifting, CRT recombination, and the
exact algebraic reduction used by that repair.
-/

/-- One nonsingular Hensel step for a square root.  The proof is entirely
explicit: if `z² - a = p^k w`, a Bezout coefficient for `2z` modulo `p`
chooses a correction `t` for which `z + p^k t` is a root modulo `p^(k+1)`.
The new root remains nonsingular modulo `p`. -/
lemma exists_square_modEq_primePower_succ
    {p k : ℕ} {a z : ℤ} (hk : 0 < k)
    (hcop : IsCoprime (2 * z) (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD ((p ^ k : ℕ) : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * z') (p : ℤ) ∧
      a ≡ z' ^ 2 [ZMOD ((p ^ (k + 1) : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have hcop' := hcop
  obtain ⟨u, v, huv⟩ := hcop
  let t : ℤ := -u * w
  have hpk : (p : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact dvd_pow_self _ (Nat.ne_of_gt hk)
  let z' : ℤ := z + (p ^ k : ℕ) * t
  refine ⟨z', ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hpk
    have hz' : 2 * z' = 2 * z + (p : ℤ) * (2 * d * t) := by
      dsimp only [z']
      rw [hd]
      ring
    rw [hz']
    exact hcop'.add_mul_left_left _
  · rw [Int.modEq_iff_dvd]
    have hlin : (p : ℤ) ∣ w + 2 * z * t := by
      refine ⟨v * w, ?_⟩
      dsimp only [t]
      calc
        w + 2 * z * (-u * w) = (1 - u * (2 * z)) * w := by ring
        _ = ((p : ℤ) * v) * w := by
          rw [show 1 - u * (2 * z) = (p : ℤ) * v by linarith [huv]]
        _ = (p : ℤ) * (v * w) := by ring
    obtain ⟨c, hc⟩ := hlin
    obtain ⟨d, hd⟩ := hpk
    refine ⟨c + d * t ^ 2, ?_⟩
    have hpow : (((p ^ (k + 1) : ℕ) : ℤ)) = (p : ℤ) ^ k * (p : ℤ) := by
      push_cast
      exact pow_succ (p : ℤ) k
    rw [hpow]
    calc
      z' ^ 2 - a =
          ((p ^ k : ℕ) : ℤ) *
            (w + 2 * z * t + ((p ^ k : ℕ) : ℤ) * t ^ 2) := by
        dsimp only [z']
        rw [show a = z ^ 2 - ((p ^ k : ℕ) : ℤ) * w by linarith [hw]]
        push_cast
        ring
      _ = ((p ^ k : ℕ) : ℤ) *
            ((p : ℤ) * c + (p : ℤ) * d * t ^ 2) := by
        rw [hc, hd]
      _ = ((p : ℤ) ^ k * (p : ℤ)) * (c + d * t ^ 2) := by
        push_cast
        ring

/-- One nonsingular Hensel step for a general quadratic polynomial. -/
lemma exists_quadratic_modEq_primePower_succ
    {p k : ℕ} {A B C x z : ℤ} (hk : 0 < k)
    (hcop : IsCoprime (2 * A * z + B) (p : ℤ))
    (h : x ≡ A * z ^ 2 + B * z + C [ZMOD ((p ^ k : ℕ) : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * A * z' + B) (p : ℤ) ∧
      x ≡ A * z' ^ 2 + B * z' + C
        [ZMOD ((p ^ (k + 1) : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have hcop' := hcop
  obtain ⟨u, v, huv⟩ := hcop
  let t : ℤ := -u * w
  have hpk : (p : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact dvd_pow_self _ (Nat.ne_of_gt hk)
  let z' : ℤ := z + (p ^ k : ℕ) * t
  refine ⟨z', ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hpk
    have hz' : 2 * A * z' + B =
        (2 * A * z + B) + (p : ℤ) * (2 * A * d * t) := by
      dsimp only [z']
      rw [hd]
      ring
    rw [hz']
    exact hcop'.add_mul_left_left _
  · rw [Int.modEq_iff_dvd]
    have hlin : (p : ℤ) ∣ w + (2 * A * z + B) * t := by
      refine ⟨v * w, ?_⟩
      dsimp only [t]
      calc
        w + (2 * A * z + B) * (-u * w) =
            (1 - u * (2 * A * z + B)) * w := by ring
        _ = ((p : ℤ) * v) * w := by
          rw [show 1 - u * (2 * A * z + B) = (p : ℤ) * v by
            linarith [huv]]
        _ = (p : ℤ) * (v * w) := by ring
    obtain ⟨c, hc⟩ := hlin
    obtain ⟨d, hd⟩ := hpk
    refine ⟨c + A * d * t ^ 2, ?_⟩
    have hpow : (((p ^ (k + 1) : ℕ) : ℤ)) =
        (p : ℤ) ^ k * (p : ℤ) := by
      push_cast
      exact pow_succ (p : ℤ) k
    rw [hpow]
    calc
      A * z' ^ 2 + B * z' + C - x =
          ((p ^ k : ℕ) : ℤ) *
            (w + (2 * A * z + B) * t +
              A * ((p ^ k : ℕ) : ℤ) * t ^ 2) := by
        dsimp only [z']
        rw [show x = A * z ^ 2 + B * z + C -
            ((p ^ k : ℕ) : ℤ) * w by linarith [hw]]
        push_cast
        ring
      _ = ((p ^ k : ℕ) : ℤ) *
          ((p : ℤ) * c + A * (p : ℤ) * d * t ^ 2) := by
        rw [hc, hd]
        ring
      _ = ((p : ℤ) ^ k * (p : ℤ)) * (c + A * d * t ^ 2) := by
        push_cast
        ring

/-- Iteration of the explicit nonsingular quadratic Hensel step. -/
lemma exists_quadratic_modEq_primePower
    {p e : ℕ} {A B C x z : ℤ} (he : 0 < e)
    (hcop : IsCoprime (2 * A * z + B) (p : ℤ))
    (h : x ≡ A * z ^ 2 + B * z + C [ZMOD (p : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * A * z' + B) (p : ℤ) ∧
      x ≡ A * z' ^ 2 + B * z' + C
        [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  induction e using Nat.case_strong_induction_on with
  | hz => omega
  | hi e ih =>
      by_cases he0 : e = 0
      · subst e
        exact ⟨z, hcop, by simpa using h⟩
      · have hepos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨z', hz'cop, hz'⟩ := ih e le_rfl hepos
        exact exists_quadratic_modEq_primePower_succ hepos hz'cop hz'

/-- If the leading coefficient is divisible by `p` and the linear
coefficient is a unit modulo `p`, the quadratic polynomial represents every
residue modulo every positive power of `p`. -/
lemma exists_quadratic_modEq_primePower_of_dvd_leading
    {p e : ℕ} {A B C x : ℤ} (he : 0 < e)
    (hA : (p : ℤ) ∣ A) (hB : IsCoprime B (p : ℤ)) :
    ∃ z : ℤ, x ≡ A * z ^ 2 + B * z + C
      [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  have hB' := hB
  obtain ⟨u, v, huv⟩ := hB
  let z : ℤ := u * (x - C)
  have hroot : x ≡ A * z ^ 2 + B * z + C [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    obtain ⟨a, ha⟩ := hA
    refine ⟨a * z ^ 2 - v * (x - C), ?_⟩
    calc
      A * z ^ 2 + B * z + C - x =
          (p : ℤ) * a * z ^ 2 + (u * B - 1) * (x - C) := by
        rw [ha]
        dsimp only [z]
        ring
      _ = (p : ℤ) * a * z ^ 2 - (p : ℤ) * v * (x - C) := by
        rw [show u * B - 1 = -(p : ℤ) * v by linarith [huv]]
        ring
      _ = (p : ℤ) * (a * z ^ 2 - v * (x - C)) := by ring
  have hderiv : IsCoprime (2 * A * z + B) (p : ℤ) := by
    obtain ⟨a, ha⟩ := hA
    rw [ha]
    have hc := hB'.add_mul_left_left (2 * a * z)
    rw [show 2 * ((p : ℤ) * a) * z + B =
      B + (p : ℤ) * (2 * a * z) by ring]
    exact hc
  obtain ⟨z', _hz'cop, hz'⟩ :=
    exists_quadratic_modEq_primePower he hderiv hroot
  exact ⟨z', hz'⟩

/-- CRT for two roots of one quadratic polynomial over coprime natural
moduli. -/
lemma exists_quadratic_modEq_mul_of_coprime
    {m n : ℕ} {A B C x z₁ z₂ : ℤ} (hmn : m.Coprime n)
    (hz₁ : x ≡ A * z₁ ^ 2 + B * z₁ + C [ZMOD (m : ℤ)])
    (hz₂ : x ≡ A * z₂ ^ 2 + B * z₂ + C [ZMOD (n : ℤ)]) :
    ∃ z : ℤ, x ≡ A * z ^ 2 + B * z + C
      [ZMOD ((m * n : ℕ) : ℤ)] := by
  obtain ⟨u, hu⟩ := Int.mod_coprime hmn
  let z : ℤ := z₁ + (m : ℤ) * u * (z₂ - z₁)
  have hz1 : z ≡ z₁ [ZMOD (m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-u * (z₂ - z₁), ?_⟩
    dsimp only [z]
    ring
  have hz2 : z ≡ z₂ [ZMOD (n : ℤ)] := by
    have h := (hu.mul_right (z₂ - z₁)).add_left z₁
    change z₁ + (m : ℤ) * u * (z₂ - z₁) ≡ z₂ [ZMOD (n : ℤ)]
    convert h using 1 <;> ring
  have hpoly1 :
      A * z ^ 2 + B * z + C ≡ A * z₁ ^ 2 + B * z₁ + C
        [ZMOD (m : ℤ)] :=
    ((hz1.pow 2).mul_left A).add (hz1.mul_left B) |>.add_right C
  have hpoly2 :
      A * z ^ 2 + B * z + C ≡ A * z₂ ^ 2 + B * z₂ + C
        [ZMOD (n : ℤ)] :=
    ((hz2.pow 2).mul_left A).add (hz2.mul_left B) |>.add_right C
  have hm : x ≡ A * z ^ 2 + B * z + C [ZMOD (m : ℤ)] :=
    hz₁.trans hpoly1.symm
  have hn : x ≡ A * z ^ 2 + B * z + C [ZMOD (n : ℤ)] :=
    hz₂.trans hpoly2.symm
  refine ⟨z, ?_⟩
  have hcop : ((m : ℤ).natAbs).Coprime ((n : ℤ).natAbs) := by simpa using hmn
  have hmn' := (Int.modEq_and_modEq_iff_modEq_mul
    (m := (m : ℤ)) (n := (n : ℤ)) hcop).mp ⟨hm, hn⟩
  simpa only [Nat.cast_mul] using hmn'

/-- Finite CRT for roots of one quadratic polynomial over pairwise coprime
moduli. -/
lemma exists_quadratic_modEq_finset_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    (A B C x : ℤ)
    (hpair : Set.Pairwise (↑s : Set ι) fun i j ↦ (m i).Coprime (m j))
    (hroot : ∀ i ∈ s, ∃ z : ℤ,
      x ≡ A * z ^ 2 + B * z + C [ZMOD (m i : ℤ)]) :
    ∃ z : ℤ, x ≡ A * z ^ 2 + B * z + C
      [ZMOD ((∏ i ∈ s, m i : ℕ) : ℤ)] := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp [Int.modEq_one]⟩
  | @insert i s hi ih =>
      rw [Finset.coe_insert, Set.pairwise_insert] at hpair
      obtain ⟨zi, hzi⟩ := hroot i (Finset.mem_insert_self i s)
      obtain ⟨zs, hzs⟩ := ih hpair.1
        (fun j hj ↦ hroot j (Finset.mem_insert_of_mem hj))
      have hcop : (m i).Coprime (∏ j ∈ s, m j) :=
        Nat.Coprime.prod_right fun j hj ↦
          (hpair.2 j hj (ne_of_mem_of_not_mem hj hi).symm).1
      obtain ⟨z, hz⟩ :=
        exists_quadratic_modEq_mul_of_coprime hcop hzi hzs
      refine ⟨z, ?_⟩
      simpa only [Finset.prod_insert hi] using hz

/-- If the leading coefficient is divisible by every prime of a nonzero
modulus and the linear coefficient is a unit at every such prime, the
quadratic polynomial represents every residue modulo the full modulus. -/
lemma exists_quadratic_modEq_of_primeFactors_linear
    {q : ℕ} {A B C x : ℤ} (hq : q ≠ 0)
    (hA : ∀ p ∈ q.primeFactors, (p : ℤ) ∣ A)
    (hB : ∀ p ∈ q.primeFactors, IsCoprime B (p : ℤ)) :
    ∃ z : ℤ, x ≡ A * z ^ 2 + B * z + C [ZMOD (q : ℤ)] := by
  let s : Finset q.primeFactors := Finset.univ
  let m : q.primeFactors → ℕ := fun p ↦ (p : ℕ) ^ q.factorization p
  have hpair : Set.Pairwise (↑s : Set q.primeFactors)
      fun p r ↦ (m p).Coprime (m r) := by
    intro p _hp r _hr hpr
    exact q.pairwise_coprime_pow_primeFactors_factorization hpr
  have hlocal : ∀ p ∈ s, ∃ z : ℤ,
      x ≡ A * z ^ 2 + B * z + C [ZMOD (m p : ℤ)] := by
    intro p _hp
    have he : 0 < q.factorization p := by
      apply Nat.pos_of_ne_zero
      simpa only [← Finsupp.mem_support_iff, Nat.support_factorization] using p.property
    exact exists_quadratic_modEq_primePower_of_dvd_leading he
      (hA p p.property) (hB p p.property)
  obtain ⟨z, hz⟩ :=
    exists_quadratic_modEq_finset_prod s m A B C x hpair hlocal
  refine ⟨z, ?_⟩
  rw [Nat.prod_primeFactors_coe_pow_factorization hq]
  simpa only [s, m] using hz

/-- A root modulo the unit-leading part of a modulus extends across a coprime
part on which the leading coefficient is prime-divisible and the linear
coefficient is locally a unit. -/
lemma exists_quadratic_root_zmod_mul_of_linear_primeFactors
    {q₁ q₂ A B C x : ℕ} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hqcop : q₁.Coprime q₂)
    (hroot₁ : ∃ z : ZMod q₁,
      (A : ZMod q₁) * z ^ 2 + (B : ZMod q₁) * z + C = x)
    (hA : ∀ p ∈ q₂.primeFactors, p ∣ A)
    (hB : ∀ p ∈ q₂.primeFactors, B.Coprime p) :
    ∃ z : ZMod (q₁ * q₂),
      (A : ZMod (q₁ * q₂)) * z ^ 2 +
        (B : ZMod (q₁ * q₂)) * z + C = x := by
  letI : NeZero q₁ := ⟨hq₁⟩
  obtain ⟨z₁, hz₁⟩ := hroot₁
  have hz₁' : (x : ℤ) ≡
      (A : ℤ) * (z₁.val : ℤ) ^ 2 + (B : ℤ) * z₁.val + C
        [ZMOD (q₁ : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz₁.symm
  obtain ⟨z₂, hz₂⟩ := exists_quadratic_modEq_of_primeFactors_linear
    hq₂ (A := (A : ℤ)) (B := (B : ℤ)) (C := (C : ℤ)) (x := (x : ℤ))
    (fun p hp ↦ by exact_mod_cast hA p hp)
    (fun p hp ↦ (hB p hp).isCoprime)
  obtain ⟨z, hz⟩ :=
    exists_quadratic_modEq_mul_of_coprime hqcop hz₁' hz₂
  letI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero hq₁ hq₂⟩
  refine ⟨(z : ZMod (q₁ * q₂)), ?_⟩
  have hzcast : ((x : ℤ) : ZMod (q₁ * q₂)) =
      (((A : ℤ) * z ^ 2 + (B : ℤ) * z + C : ℤ) : ZMod (q₁ * q₂)) := by
    rw [ZMod.intCast_eq_intCast_iff]
    exact hz
  push_cast at hzcast
  exact hzcast.symm

/-- After removing a common factor from the modulus and both nonconstant
coefficients, a quadratic root for the reduced value lifts to a root of the
original value in the corresponding residue class. -/
lemma quadratic_root_lifts_of_common_factor
    {q r q' A A' B B' C C' x₀ y : ℕ} {z : ℤ}
    (hq : r * q' = q) (hA : r * A' = A) (hB : r * B' = B)
    (hC : x₀ + r * C' = C)
    (hroot : (y : ℤ) ≡
      (A' : ℤ) * z ^ 2 + (B' : ℤ) * z + C' [ZMOD (q' : ℤ)]) :
    ((x₀ + r * y : ℕ) : ℤ) ≡
      (A : ℤ) * z ^ 2 + (B : ℤ) * z + C [ZMOD (q : ℤ)] := by
  rw [Int.modEq_iff_dvd] at hroot ⊢
  obtain ⟨w, hw⟩ := hroot
  refine ⟨w, ?_⟩
  push_cast at *
  calc
    A * z ^ 2 + B * z + C - (x₀ + r * y) =
        r * (A' * z ^ 2 + B' * z + C' - y) := by
      rw [← hA, ← hB, ← hC]
      push_cast
      ring
    _ = r * (q' * w) := by rw [hw]
    _ = q * w := by rw [← hq]; push_cast; ring

/-- Removing the common divisor of the modulus and both nonconstant
coefficients leaves a quadratic whose two nonconstant coefficients have no
common prime factor with the reduced modulus. -/
lemma coprime_reduced_quadratic_coefficients
    (A B q : ℕ) (hq : q ≠ 0) :
    let r := (A.gcd B).gcd q
    ((A / r).gcd (B / r)).Coprime (q / r) := by
  dsimp only
  let d := A.gcd B
  let r := d.gcd q
  have hrpos : 0 < r := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero hq)
  have hrd : r ∣ d := Nat.gcd_dvd_left d q
  have hrA : r ∣ A := hrd.trans (Nat.gcd_dvd_left A B)
  have hrB : r ∣ B := hrd.trans (Nat.gcd_dvd_right A B)
  rw [Nat.gcd_div hrA hrB]
  exact Nat.coprime_div_gcd_div_gcd hrpos

/-- A unit square root modulo an odd prime is nonsingular, since neither
`2` nor the root can be divisible by that prime. -/
lemma isCoprime_two_mul_of_square_modEq_odd_prime
    {p : ℕ} {a z : ℤ} (hp : p.Prime) (hodd : p ≠ 2)
    (ha : IsCoprime a (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    IsCoprime (2 * z) (p : ℤ) := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have hzsq : IsCoprime (z ^ 2) (p : ℤ) := by
    rw [show z ^ 2 = a + (p : ℤ) * w by linarith [hw]]
    exact ha.add_mul_left_left w
  have hz : IsCoprime z (p : ℤ) :=
    (IsCoprime.pow_left_iff (by decide : 0 < 2)).mp hzsq
  have hpnot : ¬p ∣ 2 := by
    intro hp2
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2eq
    · exact hp.ne_one hp1
    · exact hodd hp2eq
  have h2nat : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hpnot
  exact h2nat.isCoprime.mul_left hz

/-- Iteration of the explicit Hensel step through an arbitrary positive
prime-power exponent. -/
lemma exists_square_modEq_primePower
    {p e : ℕ} {a z : ℤ} (he : 0 < e)
    (hcop : IsCoprime (2 * z) (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * z') (p : ℤ) ∧
      a ≡ z' ^ 2 [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  induction e using Nat.case_strong_induction_on with
  | hz => omega
  | hi e ih =>
      by_cases he0 : e = 0
      · subst e
        exact ⟨z, hcop, by simpa using h⟩
      · have hepos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨z', hz'cop, hz'⟩ := ih e le_rfl hepos
        exact exists_square_modEq_primePower_succ hepos hz'cop hz'

/-- Odd-prime specialization: a unit square modulo `p` is a square modulo
every positive power of `p`. -/
lemma exists_square_modEq_primePower_of_odd_prime
    {p e : ℕ} {a z : ℤ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (ha : IsCoprime a (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    ∃ z' : ℤ, a ≡ z' ^ 2 [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  obtain ⟨z', _hz'cop, hz'⟩ := exists_square_modEq_primePower he
    (isCoprime_two_mul_of_square_modEq_odd_prime hp hodd ha h) h
  exact ⟨z', hz'⟩

/-- CRT for two square congruences with coprime natural moduli. -/
lemma exists_square_modEq_mul_of_coprime
    {m n : ℕ} {a x y : ℤ} (hmn : m.Coprime n)
    (hx : a ≡ x ^ 2 [ZMOD (m : ℤ)])
    (hy : a ≡ y ^ 2 [ZMOD (n : ℤ)]) :
    ∃ z : ℤ, a ≡ z ^ 2 [ZMOD ((m * n : ℕ) : ℤ)] := by
  obtain ⟨u, hu⟩ := Int.mod_coprime hmn
  let z : ℤ := x + (m : ℤ) * u * (y - x)
  have hzx : z ≡ x [ZMOD (m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(u * (y - x)), ?_⟩
    dsimp only [z]
    ring
  have hzy : z ≡ y [ZMOD (n : ℤ)] := by
    have h := (hu.mul_right (y - x)).add_left x
    change x + (m : ℤ) * u * (y - x) ≡ y [ZMOD (n : ℤ)]
    convert h using 1 <;> ring
  refine ⟨z, ?_⟩
  have hm : a ≡ z ^ 2 [ZMOD (m : ℤ)] := hx.trans (hzx.pow 2).symm
  have hn : a ≡ z ^ 2 [ZMOD (n : ℤ)] := hy.trans (hzy.pow 2).symm
  have hcop : ((m : ℤ).natAbs).Coprime ((n : ℤ).natAbs) := by simpa using hmn
  have hmn' := (Int.modEq_and_modEq_iff_modEq_mul
    (m := (m : ℤ)) (n := (n : ℤ)) hcop).mp ⟨hm, hn⟩
  simpa only [Nat.cast_mul] using hmn'

/-- Finite CRT for square congruences over pairwise coprime moduli. -/
lemma exists_square_modEq_finset_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (a : ℤ)
    (hpair : Set.Pairwise (↑s : Set ι) fun i j ↦ (m i).Coprime (m j))
    (hsq : ∀ i ∈ s, ∃ z : ℤ, a ≡ z ^ 2 [ZMOD (m i : ℤ)]) :
    ∃ z : ℤ, a ≡ z ^ 2 [ZMOD ((∏ i ∈ s, m i : ℕ) : ℤ)] := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp [Int.modEq_one]⟩
  | @insert i s hi ih =>
      rw [Finset.coe_insert, Set.pairwise_insert] at hpair
      obtain ⟨zi, hzi⟩ := hsq i (Finset.mem_insert_self i s)
      obtain ⟨zs, hzs⟩ := ih hpair.1 (fun j hj ↦ hsq j (Finset.mem_insert_of_mem hj))
      have hcop : (m i).Coprime (∏ j ∈ s, m j) := by
        exact Nat.Coprime.prod_right fun j hj ↦
          (hpair.2 j hj (ne_of_mem_of_not_mem hj hi).symm).1
      obtain ⟨z, hz⟩ := exists_square_modEq_mul_of_coprime hcop hzi hzs
      refine ⟨z, ?_⟩
      simpa only [Finset.prod_insert hi] using hz

/-- For an odd modulus and a residue prime to it, being a square modulo every
prime factor implies being a square modulo the full modulus.  This packages
the Hensel and CRT stages needed after the squarefree Burgess estimate. -/
lemma exists_square_modEq_of_primeFactors
    {q : ℕ} {a : ℤ} (hq : q ≠ 0)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (hunit : ∀ p ∈ q.primeFactors, IsCoprime a (p : ℤ))
    (hsq : ∀ p ∈ q.primeFactors, ∃ z : ℤ,
      a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    ∃ z : ℤ, a ≡ z ^ 2 [ZMOD (q : ℤ)] := by
  let s : Finset q.primeFactors := Finset.univ
  let m : q.primeFactors → ℕ := fun p ↦ (p : ℕ) ^ q.factorization p
  have hpair : Set.Pairwise (↑s : Set q.primeFactors)
      fun p r ↦ (m p).Coprime (m r) := by
    intro p _hp r _hr hpr
    exact q.pairwise_coprime_pow_primeFactors_factorization hpr
  have hlocal : ∀ p ∈ s, ∃ z : ℤ,
      a ≡ z ^ 2 [ZMOD (m p : ℤ)] := by
    intro p _hp
    have he : 0 < q.factorization p := by
      apply Nat.pos_of_ne_zero
      simpa only [← Finsupp.mem_support_iff, Nat.support_factorization] using p.property
    obtain ⟨z, hz⟩ := hsq p p.property
    exact exists_square_modEq_primePower_of_odd_prime
      (Nat.prime_of_mem_primeFactors p.property) (hodd p p.property) he
      (hunit p p.property) hz
  obtain ⟨z, hz⟩ := exists_square_modEq_finset_prod s m a hpair hlocal
  refine ⟨z, ?_⟩
  rw [Nat.prod_primeFactors_coe_pow_factorization hq]
  simpa only [s, m] using hz

/-- A unit square modulo the squarefree radical of an odd nonzero modulus
lifts to an integer square congruence modulo the full modulus. -/
lemma exists_square_modEq_of_coprime_square_primeSet
    {q n : ℕ} (hq : q ≠ 0)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (hcop : n.Coprime (primeSetModulus q.primeFactors))
    (hsq : IsSquare (n : ZMod (primeSetModulus q.primeFactors))) :
    ∃ z : ℤ, (n : ℤ) ≡ z ^ 2 [ZMOD (q : ℤ)] := by
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors hp
  have hlocalRad : ∀ p ∈ (primeSetModulus q.primeFactors).primeFactors,
      IsSquare (n : ZMod p) :=
    (isSquare_zmod_iff_local_of_squarefree
      (primeSetModulus_squarefree q.primeFactors hprime)).mp hsq
  apply exists_square_modEq_of_primeFactors hq hodd
  · intro p hp
    have hpdvd : p ∣ primeSetModulus q.primeFactors := dvd_primeSetModulus hp
    exact (hcop.of_dvd_right hpdvd).isCoprime
  · intro p hp
    letI : NeZero p := ⟨(hprime p hp).ne_zero⟩
    have hpmem : p ∈ (primeSetModulus q.primeFactors).primeFactors := by
      simpa [primeFactors_primeSetModulus q.primeFactors hprime] using hp
    obtain ⟨r, hr⟩ := hlocalRad p hpmem
    refine ⟨(r.val : ℤ), ?_⟩
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    calc
      (n : ZMod p) = r * r := hr
      _ = (r.val : ZMod p) ^ 2 := by
        rw [ZMod.natCast_zmod_val]
        simp [pow_two]

/-- `ZMod` form of `exists_square_modEq_of_coprime_square_primeSet`. -/
lemma isSquare_zmod_of_coprime_square_primeSet
    {q n : ℕ} (hq : q ≠ 0)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (hcop : n.Coprime (primeSetModulus q.primeFactors))
    (hsq : IsSquare (n : ZMod (primeSetModulus q.primeFactors))) :
    IsSquare (n : ZMod q) := by
  obtain ⟨z, hz⟩ := exists_square_modEq_of_coprime_square_primeSet
    hq hodd hcop hsq
  letI : NeZero q := ⟨hq⟩
  refine ⟨(z : ZMod q), ?_⟩
  have hz' : ((z ^ 2 : ℤ) : ZMod q) = ((n : ℤ) : ZMod q) := by
    rw [ZMod.intCast_eq_intCast_iff]
    exact hz.symm
  simpa [pow_two] using hz'.symm

/-- Completing the square over `ZMod q`: when `2A` is a unit, a square value
of the discriminant progression
`B² - 4AC + 4Ax` produces a solution of `Az² + Bz + C = x`.
This is the algebraic bridge from affine square-hitting to the normalized
one-variable congruence in Nguyen--Vu. -/
lemma exists_quadratic_root_of_discriminant_square_zmod
    {q A B C x : ℕ} [NeZero q] (hcop : (2 * A).Coprime q)
    (hsq : IsSquare
      ((B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x)) :
    ∃ z : ZMod q,
      (A : ZMod q) * z ^ 2 + (B : ZMod q) * z + C = x := by
  obtain ⟨y, hy⟩ := hsq
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime (2 * A) hcop
  let z : ZMod q := ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (y - B)
  have hlinear : (2 : ZMod q) * A * z + B = y := by
    have hu : ((2 * A : ℕ) : ZMod q) = (u : ZMod q) := by
      exact (ZMod.coe_unitOfCoprime (2 * A) hcop).symm
    rw [show (2 : ZMod q) * A = ((2 * A : ℕ) : ZMod q) by push_cast; ring, hu]
    change (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (y - B)) + B = y
    rw [← mul_assoc, ← Units.val_mul]
    simp
  have h4cop : (4 * A).Coprime q := by
    have h2 : Nat.Coprime 2 q :=
      Nat.Coprime.of_dvd_left (by exact dvd_mul_right 2 A) hcop
    simpa [show 4 * A = 2 * (2 * A) by ring] using h2.mul_left hcop
  have h4unit : IsUnit (((4 * A : ℕ) : ZMod q)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr h4cop
  refine ⟨z, ?_⟩
  apply sub_eq_zero.mp
  apply (h4unit.mul_right_eq_zero).mp
  calc
    ((4 * A : ℕ) : ZMod q) *
          ((A : ZMod q) * z ^ 2 + (B : ZMod q) * z + C - x) =
        ((2 : ZMod q) * A * z + B) ^ 2 -
          ((B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x) := by
      push_cast
      ring
    _ = y ^ 2 -
          ((B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x) := by
      rw [hlinear]
    _ = 0 := by rw [pow_two, ← hy]; ring

/-- Finite, fully explicit Burgess form of the unit-leading-coefficient case
of Nguyen--Vu Proposition 7.2.  The hypotheses expose the amplifier
inequalities; the conclusion supplies an index `x < H` on which the quadratic
polynomial takes the value `x` modulo the full (possibly nonsquarefree)
modulus. -/
lemma exists_quadratic_root_in_short_interval_of_burgess
    {q A B C D M H U V : ℕ} {E : ℝ}
    (hq : q ≠ 0)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (h2Acop : (2 * A).Coprime q)
    (hD : (D : ZMod q) =
      (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C)
    (hH : 0 < H) (hU₀ : 0 < U) (hV₀ : 0 < V) (hE : 0 ≤ E)
    (hDM : D ≡ (4 * A) * M [MOD primeSetModulus q.primeFactors])
    (hlarge : ∀ p ∈ q.primeFactors, U < p)
    (hshift : ∀ p ∈ q.primeFactors, V < p)
    (hUV : U * V ≤ H)
    (hdom : (2 : ℝ) ^ q.primeFactors.card *
        (∑ p ∈ q.primeFactors, (H / p + 1)) +
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * E < H)
    (hparams : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      H ≤ primeSetModulus t ∧
      V < primeSetModulus t ∧
      2 * (U * H) < primeSetModulus t ∧
      8 *
          (((((H * U : ℕ) : ℝ) ^ 2 *
              (((H : ℝ) * (1 + Real.log U) + U) *
                ((U : ℝ) * (1 + Real.log U)))) *
            (3 * (V : ℝ) ^ 2 * (primeSetModulus t : ℝ) +
              (V : ℝ) ^ 4 *
                ((3 : ℝ) ^ t.card *
                  Real.sqrt (primeSetModulus t)))) +
            ((2 : ℝ) * (U * V) ^ 2) ^ 4) <
        (((U * V : ℕ) : ℝ) * E) ^ 4) :
    ∃ x ∈ Finset.range H, ∃ z : ZMod q,
      (A : ZMod q) * z ^ 2 + (B : ZMod q) * z + C = x := by
  let s := q.primeFactors
  have hs : ∀ p ∈ s, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have h4Acopq : (4 * A).Coprime q := by
    have h2 : Nat.Coprime 2 q :=
      Nat.Coprime.of_dvd_left (by exact dvd_mul_right 2 A) h2Acop
    simpa [show 4 * A = 2 * (2 * A) by ring] using h2.mul_left h2Acop
  have hradq : primeSetModulus s ∣ q := by
    simpa [s, primeSetModulus] using Nat.prod_primeFactors_dvd q
  have h4Acop : (4 * A).Coprime (primeSetModulus s) :=
    h4Acopq.of_dvd_right hradq
  obtain ⟨x, hxH, hxcop, hxsq⟩ :=
    exists_coprime_isSquare_primeSetAffine_of_uniform_burgess
      s hs hH hU₀ hV₀ hE h4Acop hDM hlarge hshift hodd hUV hdom hparams
  have hxsqFull : IsSquare ((D + (4 * A) * x : ℕ) : ZMod q) :=
    isSquare_zmod_of_coprime_square_primeSet hq hodd hxcop hxsq
  have hdisc : ((D + (4 * A) * x : ℕ) : ZMod q) =
      (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hD]
    push_cast
    ring
  refine ⟨x, hxH, ?_⟩
  letI : NeZero q := ⟨hq⟩
  apply exists_quadratic_root_of_discriminant_square_zmod h2Acop
  rwa [← hdisc]

/-- Repaired finite form of Nguyen--Vu Proposition 7.2 in the unit-leading
case.  Small divisor conductors use exact Fourier completion, while every
remaining conductor carries its own coprime-denominator Burgess certificate. -/
lemma exists_quadratic_root_in_short_interval_of_completion_or_coprime_burgess
    {q A B C D M H : ℕ} {E : ℝ}
    (hq : q ≠ 0)
    (hodd : ∀ p ∈ q.primeFactors, p ≠ 2)
    (h2Acop : (2 * A).Coprime q)
    (hD : (D : ZMod q) =
      (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C)
    (hH : 0 < H) (hE : 0 ≤ E)
    (hDM : D ≡ (4 * A) * M [MOD primeSetModulus q.primeFactors])
    (hdom : (2 : ℝ) ^ q.primeFactors.card *
        (∑ p ∈ q.primeFactors, (H / p + 1)) +
      ((q.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * E < H)
    (hcases : ∀ t ∈ q.primeFactors.powerset.filter Finset.Nonempty,
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤ E ∨
        CoprimeBurgessCertificate t H E) :
    ∃ x ∈ Finset.range H, ∃ z : ZMod q,
      (A : ZMod q) * z ^ 2 + (B : ZMod q) * z + C = x := by
  let s := q.primeFactors
  have hs : ∀ p ∈ s, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have h4Acopq : (4 * A).Coprime q := by
    have h2 : Nat.Coprime 2 q :=
      Nat.Coprime.of_dvd_left (by exact dvd_mul_right 2 A) h2Acop
    simpa [show 4 * A = 2 * (2 * A) by ring] using h2.mul_left h2Acop
  have hradq : primeSetModulus s ∣ q := by
    simpa [s, primeSetModulus] using Nat.prod_primeFactors_dvd q
  have h4Acop : (4 * A).Coprime (primeSetModulus s) :=
    h4Acopq.of_dvd_right hradq
  obtain ⟨x, hxH, hxcop, hxsq⟩ :=
    exists_coprime_isSquare_primeSetAffine_of_completion_or_coprime_burgess
      s hs hH hE h4Acop hDM hodd hdom hcases
  have hxsqFull : IsSquare ((D + (4 * A) * x : ℕ) : ZMod q) :=
    isSquare_zmod_of_coprime_square_primeSet hq hodd hxcop hxsq
  have hdisc : ((D + (4 * A) * x : ℕ) : ZMod q) =
      (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hD]
    push_cast
    ring
  refine ⟨x, hxH, ?_⟩
  letI : NeZero q := ⟨hq⟩
  apply exists_quadratic_root_of_discriminant_square_zmod h2Acop
  rwa [← hdisc]

/-- Automatic large-radical form of the unit-leading Nguyen--Vu quadratic
step.  All analytic hypotheses from the preceding explicit version have now
been discharged by the uniform affine Burgess threshold. -/
theorem exists_quadraticRootAnalyticThreshold :
    ∃ Q₀ : ℕ, ∀ {q A B C D M H : ℕ},
      q ≠ 0 →
      (∀ p ∈ q.primeFactors, p ≠ 2) →
      (2 * A).Coprime q →
      (D : ZMod q) =
        (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C →
      Q₀ ≤ primeSetModulus q.primeFactors →
      0 < H →
      (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 →
      D ≡ (4 * A) * M [MOD primeSetModulus q.primeFactors] →
      ∃ x ∈ Finset.range H, ∃ z : ZMod q,
        (A : ZMod q) * z ^ 2 + (B : ZMod q) * z + C = x := by
  obtain ⟨Q₀, hQ₀⟩ := exists_unitSquareAffineAnalyticThreshold
  refine ⟨Q₀, ?_⟩
  intro q A B C D M H hq hodd h2Acop hD hrad hH hroot hDM
  let s := q.primeFactors
  have hs : ∀ p ∈ s, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have h4Acopq : (4 * A).Coprime q := by
    have h2 : Nat.Coprime 2 q :=
      Nat.Coprime.of_dvd_left (by exact dvd_mul_right 2 A) h2Acop
    simpa [show 4 * A = 2 * (2 * A) by ring] using h2.mul_left h2Acop
  have hradq : primeSetModulus s ∣ q := by
    simpa [s, primeSetModulus] using Nat.prod_primeFactors_dvd q
  have h4Acop : (4 * A).Coprime (primeSetModulus s) :=
    h4Acopq.of_dvd_right hradq
  obtain ⟨x, hxH, hxcop, hxsq⟩ :=
    hQ₀ s hs hodd hrad D (4 * A) M H h4Acop hDM hH hroot
  have hxsqFull : IsSquare ((D + (4 * A) * x : ℕ) : ZMod q) :=
    isSquare_zmod_of_coprime_square_primeSet hq hodd hxcop hxsq
  have hdisc : ((D + (4 * A) * x : ℕ) : ZMod q) =
      (B : ZMod q) ^ 2 - (4 : ZMod q) * A * C + (4 : ZMod q) * A * x := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hD]
    push_cast
    ring
  refine ⟨x, hxH, ?_⟩
  letI : NeZero q := ⟨hq⟩
  apply exists_quadratic_root_of_discriminant_square_zmod h2Acop
  rwa [← hdisc]

/-- Full finite residue-class version of the repaired quadratic step.  A
common coefficient/modulus factor first fixes one residue class for `x`; the
reduced modulus is then split into a unit-leading part, handled by
completion/Burgess, and a linear-unit part, handled by Hensel and CRT. -/
lemma exists_quadratic_root_in_residue_interval_of_completion_or_coprime_burgess
    {q r q' q₁ q₂ A A' B B' C C' x₀ D M H : ℕ} {E : ℝ}
    (hq : r * q' = q) (hA : r * A' = A) (hB : r * B' = B)
    (hC : x₀ + r * C' = C)
    (hsplit : q₁ * q₂ = q') (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hqcop : q₁.Coprime q₂)
    (hodd : ∀ p ∈ q₁.primeFactors, p ≠ 2)
    (h2Acop : (2 * A').Coprime q₁)
    (hD : (D : ZMod q₁) =
      (B' : ZMod q₁) ^ 2 - (4 : ZMod q₁) * A' * C')
    (hH : 0 < H) (hE : 0 ≤ E)
    (hDM : D ≡ (4 * A') * M [MOD primeSetModulus q₁.primeFactors])
    (hdom : (2 : ℝ) ^ q₁.primeFactors.card *
        (∑ p ∈ q₁.primeFactors, (H / p + 1)) +
      ((q₁.primeFactors.powerset.filter Finset.Nonempty).card : ℝ) * E < H)
    (hcases : ∀ t ∈ q₁.primeFactors.powerset.filter Finset.Nonempty,
      Real.log (primeSetModulus t) * Real.sqrt (primeSetModulus t) ≤ E ∨
        CoprimeBurgessCertificate t H E)
    (hA₂ : ∀ p ∈ q₂.primeFactors, p ∣ A')
    (hB₂ : ∀ p ∈ q₂.primeFactors, B'.Coprime p) :
    ∃ y ∈ Finset.range H, ∃ z : ℤ,
      ((x₀ + r * y : ℕ) : ℤ) ≡
        (A : ℤ) * z ^ 2 + (B : ℤ) * z + C [ZMOD (q : ℤ)] := by
  obtain ⟨y, hyH, z₁, hz₁⟩ :=
    exists_quadratic_root_in_short_interval_of_completion_or_coprime_burgess
      hq₁ hodd h2Acop hD hH hE hDM hdom hcases
  obtain ⟨z, hz⟩ := exists_quadratic_root_zmod_mul_of_linear_primeFactors
    hq₁ hq₂ hqcop ⟨z₁, hz₁⟩ hA₂ hB₂
  letI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero hq₁ hq₂⟩
  have hred : (y : ℤ) ≡
      (A' : ℤ) * (z.val : ℤ) ^ 2 + (B' : ℤ) * z.val + C'
        [ZMOD ((q₁ * q₂ : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz.symm
  refine ⟨y, hyH, z.val, ?_⟩
  apply quadratic_root_lifts_of_common_factor hq hA hB hC
  simpa only [hsplit] using hred

/-- Automatic large-radical form of the full residue-class quadratic step.
Prime powers on which the quadratic coefficient is a unit are handled by the
uniform affine theorem; the complementary linear-unit prime powers are then
recombined by Hensel and CRT. -/
theorem exists_quadraticRootResidueAnalyticThreshold :
    ∃ Q₀ : ℕ,
      ∀ {q r q' q₁ q₂ A A' B B' C C' x₀ D M H : ℕ},
      r * q' = q → r * A' = A → r * B' = B →
      x₀ + r * C' = C →
      q₁ * q₂ = q' → q₁ ≠ 0 → q₂ ≠ 0 →
      q₁.Coprime q₂ →
      (∀ p ∈ q₁.primeFactors, p ≠ 2) →
      (2 * A').Coprime q₁ →
      (D : ZMod q₁) =
        (B' : ZMod q₁) ^ 2 - (4 : ZMod q₁) * A' * C' →
      Q₀ ≤ primeSetModulus q₁.primeFactors →
      0 < H →
      (primeSetModulus q₁.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 →
      D ≡ (4 * A') * M [MOD primeSetModulus q₁.primeFactors] →
      (∀ p ∈ q₂.primeFactors, p ∣ A') →
      (∀ p ∈ q₂.primeFactors, B'.Coprime p) →
      ∃ y ∈ Finset.range H, ∃ z : ℤ,
        ((x₀ + r * y : ℕ) : ℤ) ≡
          (A : ℤ) * z ^ 2 + (B : ℤ) * z + C [ZMOD (q : ℤ)] := by
  obtain ⟨Q₀, hQ₀⟩ := exists_quadraticRootAnalyticThreshold
  refine ⟨Q₀, ?_⟩
  intro q r q' q₁ q₂ A A' B B' C C' x₀ D M H
    hq hA hB hC hsplit hq₁ hq₂ hqcop hodd h2Acop hD
    hrad hH hroot hDM hA₂ hB₂
  obtain ⟨y, hyH, z₁, hz₁⟩ :=
    hQ₀ hq₁ hodd h2Acop hD hrad hH hroot hDM
  obtain ⟨z, hz⟩ := exists_quadratic_root_zmod_mul_of_linear_primeFactors
    hq₁ hq₂ hqcop ⟨z₁, hz₁⟩ hA₂ hB₂
  letI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero hq₁ hq₂⟩
  have hred : (y : ℤ) ≡
      (A' : ℤ) * (z.val : ℤ) ^ 2 + (B' : ℤ) * z.val + C'
        [ZMOD ((q₁ * q₂ : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz.symm
  refine ⟨y, hyH, z.val, ?_⟩
  apply quadratic_root_lifts_of_common_factor hq hA hB hC
  simpa only [hsplit] using hred

/-- If `g = k * a` and `h = k * q`, a solution of the normalized quadratic
congruence modulo `q` lifts to the congruence modulo `h` used in Nguyen--Vu's
one-variable step. -/
lemma quadratic_step_lifts_of_factorization
    {g h k a q p x : ℕ} {t z₁ z : ℤ}
    (hg : k * a = g) (hh : k * q = h)
    (hnorm :
      (a : ℤ) * (x : ℤ) + t ≡
        (p : ℤ) * (k : ℤ) * z ^ 2 + 2 * (p : ℤ) * z₁ * z
          [ZMOD (q : ℤ)]) :
    (g : ℤ) * (x : ℤ) + (p : ℤ) * z₁ ^ 2 + t * (k : ℤ) ≡
      (p : ℤ) * (z₁ + (k : ℤ) * z) ^ 2 [ZMOD (h : ℤ)] := by
  rw [Int.modEq_iff_dvd] at hnorm ⊢
  obtain ⟨w, hw⟩ := hnorm
  refine ⟨w, ?_⟩
  have hg' : (g : ℤ) = (k : ℤ) * (a : ℤ) := by
    exact_mod_cast hg.symm
  have hh' : (h : ℤ) = (k : ℤ) * (q : ℤ) := by
    exact_mod_cast hh.symm
  calc
    (p : ℤ) * (z₁ + (k : ℤ) * z) ^ 2 -
          ((g : ℤ) * (x : ℤ) + (p : ℤ) * z₁ ^ 2 + t * (k : ℤ)) =
        (k : ℤ) *
          ((p : ℤ) * (k : ℤ) * z ^ 2 + 2 * (p : ℤ) * z₁ * z -
            ((a : ℤ) * (x : ℤ) + t)) := by
      rw [hg']
      ring
    _ = (k : ℤ) * ((q : ℤ) * w) := by rw [hw]
    _ = (h : ℤ) * w := by rw [hh']; ring

/-- GCD-normalized form of `quadratic_step_lifts_of_factorization`. -/
lemma normalized_quadratic_step_lifts
    {g h p x : ℕ} {t z₁ z : ℤ}
    (hnorm :
      ((g / g.gcd h : ℕ) : ℤ) * (x : ℤ) + t ≡
        (p : ℤ) * (g.gcd h : ℤ) * z ^ 2 + 2 * (p : ℤ) * z₁ * z
          [ZMOD ((h / g.gcd h : ℕ) : ℤ)]) :
    (g : ℤ) * (x : ℤ) + (p : ℤ) * z₁ ^ 2 + t * (g.gcd h : ℤ) ≡
      (p : ℤ) * (z₁ + (g.gcd h : ℤ) * z) ^ 2 [ZMOD (h : ℤ)] := by
  apply quadratic_step_lifts_of_factorization
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left g h))
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right g h))
      hnorm

/-- The normalized congruence has a completely elementary solution of size
less than its modulus: set the new square variable to zero and solve the
remaining linear congruence.  Thus Burgess is needed only when the requested
bound is genuinely shorter than the reduced modulus. -/
lemma exists_small_linear_normalized_solution
    {a q : ℕ} {t : ℤ} (hq : 0 < q) (haq : a.Coprime q) :
    ∃ x < q,
      (a : ℤ) * (x : ℤ) + t ≡ 0 [ZMOD (q : ℤ)] := by
  letI : NeZero q := ⟨hq.ne'⟩
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a haq
  let y : ZMod q := -(t : ZMod q)
  let v : ZMod q := (u⁻¹ : (ZMod q)ˣ) * y
  let x : ℕ := v.val
  have hxq : x < q := by
    dsimp [x]
    exact ZMod.val_lt v
  refine ⟨x, hxq, ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have hx : (x : ZMod q) = v := ZMod.natCast_zmod_val v
  rw [hx]
  change (a : ZMod q) * v + (t : ZMod q) = 0
  rw [show (a : ZMod q) = (u : ZMod q) by exact (ZMod.coe_unitOfCoprime a haq).symm]
  change (u : ZMod q) * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * y) + (t : ZMod q) = 0
  rw [← mul_assoc]
  rw [← Units.val_mul]
  simp [y]

/-- Elementary large-bound branch of the one-variable Nguyen--Vu step. -/
lemma exists_quadratic_step_of_reduced_modulus_le
    {g h p B : ℕ} {t z₁ : ℤ} (hh : 0 < h)
    (hB : h / g.gcd h ≤ B) :
    ∃ x ≤ B, ∃ z₂ : ℤ,
      (g : ℤ) * (x : ℤ) + (p : ℤ) * z₁ ^ 2 + t * (g.gcd h : ℤ) ≡
        (p : ℤ) * z₂ ^ 2 [ZMOD (h : ℤ)] := by
  let k := g.gcd h
  let a := g / k
  let q := h / k
  have hkpos : 0 < k := Nat.gcd_pos_of_pos_right g hh
  have hqpos : 0 < q := Nat.div_pos (Nat.gcd_le_right g hh) hkpos
  have haq : a.Coprime q := by
    simpa [a, q, k] using Nat.coprime_div_gcd_div_gcd hkpos
  obtain ⟨x, hxq, hx⟩ := exists_small_linear_normalized_solution hqpos haq (t := t)
  refine ⟨x, hxq.le.trans hB, z₁ + (k : ℤ) * 0, ?_⟩
  apply normalized_quadratic_step_lifts (g := g) (h := h) (p := p)
      (x := x) (t := t) (z₁ := z₁) (z := 0)
  simpa [a, q, k] using hx

/-- The exact extremal quantity from the Formal Conjectures statement. -/
def MaxNotSqSum (N : ℕ) : ℕ :=
  (Finset.Icc 1 N |>.powerset.filter fun A => ∀ S ⊆ A, S ≠ ⊥ →
    ¬ IsSquare (∑ n ∈ S, n)).sup Finset.card

/-- The square-subset-sum-free predicate appearing inside `MaxNotSqSum`. -/
def SquareSubsetSumFree (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S ≠ ∅ → ¬ IsSquare (∑ n ∈ S, n)

/-- Sums of exactly `k` distinct elements of `A`. -/
def restrictedSums (k : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.powersetCard k).image fun S => ∑ a ∈ S, a

lemma mem_restrictedSums_iff {k m : ℕ} {A : Finset ℕ} :
    m ∈ restrictedSums k A ↔
      ∃ S ⊆ A, S.card = k ∧ ∑ a ∈ S, a = m := by
  simp [restrictedSums, and_assoc, and_left_comm]

/-- Translate a finite set of natural numbers. -/
def natTranslate (a : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image fun x => a + x

@[simp] lemma mem_natTranslate {a x : ℕ} {S : Finset ℕ} :
    x ∈ natTranslate a S ↔ ∃ y ∈ S, a + y = x := by
  simp [natTranslate]

lemma card_natTranslate (a : ℕ) (S : Finset ℕ) :
    (natTranslate a S).card = S.card := by
  rw [natTranslate, Finset.card_image_of_injective]
  exact fun _ _ h => Nat.add_left_cancel h

/-- Adjoining one fresh element transports `k`-term sums into
`(k+1)`-term sums. -/
lemma natTranslate_restrictedSums_subset_insert {A : Finset ℕ} {a k : ℕ}
    (ha : a ∉ A) :
    natTranslate a (restrictedSums k A) ⊆
      restrictedSums (k + 1) (insert a A) := by
  intro z hz
  obtain ⟨x, hx, hax⟩ := mem_natTranslate.mp hz
  obtain ⟨T, hTA, hTk, hsum⟩ := mem_restrictedSums_iff.mp hx
  apply mem_restrictedSums_iff.mpr
  refine ⟨insert a T, Finset.insert_subset_insert a hTA, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem]
    · omega
    · exact fun haT => ha (hTA haT)
  · rw [Finset.sum_insert]
    · omega
    · exact fun haT => ha (hTA haT)

/-- Two fresh choices give two translates of the old restricted-sum set
inside the next restricted-sum set. -/
lemma union_natTranslate_restrictedSums_subset_insert_pair
    {A : Finset ℕ} {a b k : ℕ} (ha : a ∉ A) (hb : b ∉ A) (_hab : a ≠ b) :
    natTranslate a (restrictedSums k A) ∪
        natTranslate b (restrictedSums k A) ⊆
      restrictedSums (k + 1) (insert a (insert b A)) := by
  rw [Finset.union_subset_iff]
  constructor
  · intro z hz
    obtain ⟨x, hx, hax⟩ := mem_natTranslate.mp hz
    obtain ⟨T, hTA, hTk, hsum⟩ := mem_restrictedSums_iff.mp hx
    apply mem_restrictedSums_iff.mpr
    refine ⟨insert a T, ?_, ?_, ?_⟩
    · simpa [Finset.insert_comm] using
        (Finset.insert_subset_insert a hTA).trans
          (Finset.subset_insert b (insert a A))
    · rw [Finset.card_insert_of_notMem]
      · omega
      · exact fun haT => ha (hTA haT)
    · rw [Finset.sum_insert]
      · omega
      · exact fun haT => ha (hTA haT)
  · intro z hz
    obtain ⟨x, hx, hbx⟩ := mem_natTranslate.mp hz
    obtain ⟨T, hTA, hTk, hsum⟩ := mem_restrictedSums_iff.mp hx
    apply mem_restrictedSums_iff.mpr
    refine ⟨insert b T, ?_, ?_, ?_⟩
    · exact (Finset.insert_subset_insert b hTA).trans
        (Finset.subset_insert a (insert b A))
    · rw [Finset.card_insert_of_notMem]
      · omega
      · exact fun hbT => hb (hTA hbT)
    · rw [Finset.sum_insert]
      · omega
      · exact fun hbT => hb (hTA hbT)

/-- The strict ordered pairs from a finite linearly ordered set are counted
by the second binomial coefficient. -/
lemma card_strictPairs (S : Finset ℕ) :
    ((S ×ˢ S).filter fun xy => xy.1 < xy.2).card = S.card.choose 2 := by
  exact Finset.card_product_filter_lt

/-- Incidences between translates based at the least remaining element inject
into strict pairs of the translated set. -/
lemma card_sigma_inter_natTranslate_le_choose
    {R S : Finset ℕ} (hR : R.Nonempty) :
    ((R.erase (R.min' hR)).sigma fun b =>
        natTranslate (R.min' hR) S ∩ natTranslate b S).card ≤
      S.card.choose 2 := by
  let a := R.min' hR
  let I := (R.erase a).sigma fun b =>
    natTranslate a S ∩ natTranslate b S
  let P := (S ×ˢ S).filter fun xy => xy.1 < xy.2
  let f : (Σ _b : ℕ, ℕ) → ℕ × ℕ := fun p => (p.2 - p.1, p.2 - a)
  have hmaps : Set.MapsTo f (I : Set (Σ _b : ℕ, ℕ)) (P : Set (ℕ × ℕ)) := by
    rintro ⟨b, z⟩ hz
    rw [Finset.mem_coe, show I = (R.erase a).sigma fun b =>
      natTranslate a S ∩ natTranslate b S by rfl, Finset.mem_sigma] at hz
    change b ∈ R.erase a ∧ z ∈ natTranslate a S ∩ natTranslate b S at hz
    obtain ⟨hb, hz⟩ := hz
    rw [Finset.mem_erase] at hb
    rw [Finset.mem_inter] at hz
    obtain ⟨x, hxS, hax⟩ := mem_natTranslate.mp hz.1
    obtain ⟨y, hyS, hby⟩ := mem_natTranslate.mp hz.2
    have hab : a < b := by
      have hab' : a ≤ b := Finset.min'_le R b hb.2
      omega
    have hza : a ≤ z := by omega
    have hzb : b ≤ z := by omega
    have hxa : z - a = x := by omega
    have hyb : z - b = y := by omega
    rw [Finset.mem_coe, show P = (S ×ˢ S).filter (fun xy => xy.1 < xy.2) by rfl,
      Finset.mem_filter, Finset.mem_product]
    change ((z - b ∈ S ∧ z - a ∈ S) ∧ z - b < z - a)
    rw [hxa, hyb]
    refine ⟨⟨hyS, hxS⟩, ?_⟩
    omega
  have hinj : (I : Set (Σ _b : ℕ, ℕ)).InjOn f := by
    rintro ⟨b, z⟩ hbz ⟨c, w⟩ hcw hfw
    rw [Finset.mem_coe, show I = (R.erase a).sigma fun b =>
      natTranslate a S ∩ natTranslate b S by rfl, Finset.mem_sigma] at hbz hcw
    change b ∈ R.erase a ∧ z ∈ natTranslate a S ∩ natTranslate b S at hbz
    change c ∈ R.erase a ∧ w ∈ natTranslate a S ∩ natTranslate c S at hcw
    rw [Finset.mem_inter] at hbz hcw
    have hza : a ≤ z := by
      obtain ⟨x, _hx, hx⟩ := mem_natTranslate.mp hbz.2.1
      omega
    have hwa : a ≤ w := by
      obtain ⟨x, _hx, hx⟩ := mem_natTranslate.mp hcw.2.1
      omega
    have hzb : b ≤ z := by
      obtain ⟨x, _hx, hx⟩ := mem_natTranslate.mp hbz.2.2
      omega
    have hwc : c ≤ w := by
      obtain ⟨x, _hx, hx⟩ := mem_natTranslate.mp hcw.2.2
      omega
    have hzwsub : z - a = w - a := congrArg Prod.snd hfw
    have hzw : z = w := by omega
    subst w
    have hbcsub : z - b = z - c := congrArg Prod.fst hfw
    have hbc : b = c := by omega
    subst c
    rfl
  calc
    ((R.erase (R.min' hR)).sigma fun b =>
        natTranslate (R.min' hR) S ∩ natTranslate b S).card = I.card := rfl
    _ ≤ P.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = S.card.choose 2 := card_strictPairs S

/-- Elementary growth step in Szemerédi--Vu Lemma 7.9.  If a small even set
has not yet produced as many balanced restricted sums as the ambient set has
elements, two fresh elements enlarge the balanced restricted-sum set by a
factor at least `6/5`. -/
lemma exists_pair_restrictedSums_growth
    {A B : Finset ℕ} {k : ℕ} (hBA : B ⊆ A) (hBcard : B.card = 2 * k)
    (hA16 : 16 ≤ A.card) (hBsmall : 8 * B.card ≤ A.card)
    (hsmall : (restrictedSums k B).card < A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a ∉ B ∧ b ∉ B ∧
      6 * (restrictedSums k B).card ≤
        5 * (restrictedSums (k + 1) (insert a (insert b B))).card := by
  classical
  let S := restrictedSums k B
  let R := A \ B
  have hRcard : R.card = A.card - B.card := by
    dsimp [R]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]
  have hRtwo : 2 ≤ R.card := by
    rw [hRcard]
    omega
  have hR : R.Nonempty := Finset.card_pos.mp (by omega)
  let a := R.min' hR
  by_contra hnone
  push Not at hnone
  have hbad : ∀ b ∈ R.erase a,
      5 * (natTranslate a S ∪ natTranslate b S).card < 6 * S.card := by
    intro b hb
    rw [Finset.mem_erase] at hb
    have haR : a ∈ R := Finset.min'_mem R hR
    have haA : a ∈ A := (Finset.mem_sdiff.mp haR).1
    have haB : a ∉ B := (Finset.mem_sdiff.mp haR).2
    have hbA : b ∈ A := (Finset.mem_sdiff.mp hb.2).1
    have hbB : b ∉ B := (Finset.mem_sdiff.mp hb.2).2
    have hab : a ≠ b := Ne.symm hb.1
    have htarget := hnone a haA b hbA hab haB hbB
    have hsub := union_natTranslate_restrictedSums_subset_insert_pair
      (k := k) haB hbB hab
    have hcard := Finset.card_le_card hsub
    have hcard' : (natTranslate a S ∪ natTranslate b S).card ≤
        (restrictedSums (k + 1) (insert a (insert b B))).card := by
      simpa [S] using hcard
    have htarget' :
        5 * (restrictedSums (k + 1) (insert a (insert b B))).card <
          6 * S.card := by simpa [S] using htarget
    omega
  have hinter : ∀ b ∈ R.erase a,
      4 * S.card <
        5 * (natTranslate a S ∩ natTranslate b S).card := by
    intro b hb
    have hcard := Finset.card_inter_add_card_union
      (natTranslate a S) (natTranslate b S)
    rw [card_natTranslate, card_natTranslate] at hcard
    have := hbad b hb
    omega
  let I := (R.erase a).sigma fun b =>
    natTranslate a S ∩ natTranslate b S
  have hIupper : I.card ≤ S.card.choose 2 := by
    simpa [I, a] using card_sigma_inter_natTranslate_le_choose hR
  have hEraseCard : (R.erase a).card = R.card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.min'_mem R hR)]
  have hIcard : I.card = ∑ b ∈ R.erase a,
      (natTranslate a S ∩ natTranslate b S).card := by
    simp [I]
  have hSpos : 0 < S.card := by
    rw [Finset.card_pos]
    have hkB : k ≤ B.card := by omega
    obtain ⟨T, hT⟩ := (Finset.powersetCard_nonempty.mpr hkB)
    exact ⟨∑ x ∈ T, x, Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩
  have hsumLower :
      ((R.erase a).card : ℚ) * ((4 : ℚ) / 5 * S.card) < I.card := by
    have hne : (R.erase a).Nonempty := by
      rw [← Finset.card_pos, hEraseCard]
      omega
    calc
      ((R.erase a).card : ℚ) * ((4 : ℚ) / 5 * S.card) =
          ∑ _b ∈ R.erase a, ((4 : ℚ) / 5 * S.card) := by simp
      _ < ∑ b ∈ R.erase a,
          ((natTranslate a S ∩ natTranslate b S).card : ℚ) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro b hb
        have hb' : (4 : ℚ) * S.card <
            5 * (natTranslate a S ∩ natTranslate b S).card := by
          exact_mod_cast hinter b hb
        norm_num
        linarith
      _ = I.card := by
        have hIcardQ : (I.card : ℚ) = ∑ b ∈ R.erase a,
            ((natTranslate a S ∩ natTranslate b S).card : ℚ) := by
          exact_mod_cast hIcard
        exact hIcardQ.symm
  have hcountLower :
      ((3 : ℚ) / 4) * A.card ≤ (R.erase a).card := by
    have hcountNat : 3 * A.card ≤ 4 * (R.erase a).card := by
      rw [hEraseCard, hRcard]
      omega
    have hcountQ : (3 : ℚ) * A.card ≤ 4 * (R.erase a).card := by
      exact_mod_cast hcountNat
    linarith
  have hchoose : (S.card.choose 2 : ℚ) =
      (S.card : ℚ) * (S.card - 1) / 2 := by
    exact Nat.cast_choose_two (K := ℚ) S.card
  have hScast : (S.card : ℚ) < A.card := by exact_mod_cast hsmall
  have hIupper' : (I.card : ℚ) ≤ S.card.choose 2 := by exact_mod_cast hIupper
  rw [hchoose] at hIupper'
  have hApos : (0 : ℚ) < A.card := by positivity
  have hSpos' : (0 : ℚ) < S.card := by exact_mod_cast hSpos
  nlinarith

/-- Iterate the balanced restricted-sum growth step until it reaches ambient
cardinality, or record the accumulated `(6/5)^t` growth. -/
lemma exists_balancedBlock_or_growth
    {A : Finset ℕ} (hA16 : 16 ≤ A.card) (t : ℕ)
    (hreserve : 16 * t ≤ A.card) :
    ∃ k ≤ t, ∃ B : Finset ℕ, B ⊆ A ∧ B.card = 2 * k ∧
      (A.card ≤ (restrictedSums k B).card ∨
        (k = t ∧ 6 ^ t ≤ 5 ^ t * (restrictedSums k B).card)) := by
  induction t with
  | zero =>
      refine ⟨0, le_rfl, ∅, Finset.empty_subset A, by simp, Or.inr ⟨rfl, ?_⟩⟩
      simp [restrictedSums]
  | succ t ih =>
      have hreserve' : 16 * t ≤ A.card := by omega
      obtain ⟨k, hkt, B, hBA, hBcard, hlarge | hgrowth⟩ := ih hreserve'
      · exact ⟨k, hkt.trans (Nat.le_succ t), B, hBA, hBcard, Or.inl hlarge⟩
      · obtain ⟨hktEq, hgrowth⟩ := hgrowth
        subst k
        by_cases hlarge : A.card ≤ (restrictedSums t B).card
        · exact ⟨t, Nat.le_succ t, B, hBA, hBcard, Or.inl hlarge⟩
        · have hsmall : (restrictedSums t B).card < A.card := by omega
          have hBsmall : 8 * B.card ≤ A.card := by
            rw [hBcard]
            omega
          obtain ⟨a, haA, b, hbA, hab, haB, hbB, hstep⟩ :=
            exists_pair_restrictedSums_growth hBA hBcard hA16 hBsmall hsmall
          let B' := insert a (insert b B)
          have hB'A : B' ⊆ A := by
            intro x hx
            simp only [B', Finset.mem_insert] at hx
            rcases hx with rfl | rfl | hx
            · exact haA
            · exact hbA
            · exact hBA hx
          have hB'card : B'.card = 2 * (t + 1) := by
            dsimp [B']
            rw [Finset.card_insert_of_notMem]
            · rw [Finset.card_insert_of_notMem hbB, hBcard]
              omega
            · simpa [hab] using haB
          refine ⟨t + 1, le_rfl, B', hB'A, hB'card, Or.inr ⟨rfl, ?_⟩⟩
          calc
            6 ^ (t + 1) = 6 * 6 ^ t := by rw [pow_succ]; ring
            _ ≤ 6 * (5 ^ t * (restrictedSums t B).card) :=
              Nat.mul_le_mul_left 6 hgrowth
            _ = 5 ^ t * (6 * (restrictedSums t B).card) := by ring
            _ ≤ 5 ^ t *
                (5 * (restrictedSums (t + 1) B').card) := by
              apply Nat.mul_le_mul_left
              simpa [B'] using hstep
            _ = 5 ^ (t + 1) * (restrictedSums (t + 1) B').card := by
              rw [pow_succ]
              ring

/-- Power-form consequence: enough accumulated `(6/5)` growth forces a
small balanced block with at least ambient-cardinality many sums. -/
lemma exists_balancedBlock_of_power_bound
    {A : Finset ℕ} (hA16 : 16 ≤ A.card) (t : ℕ)
    (hreserve : 16 * t ≤ A.card)
    (hforce : 5 ^ t * A.card < 6 ^ t) :
    ∃ k ≤ t, ∃ B : Finset ℕ, B ⊆ A ∧ B.card = 2 * k ∧
      A.card ≤ (restrictedSums k B).card := by
  obtain ⟨k, hkt, B, hBA, hBcard, hlarge | ⟨hktEq, hgrowth⟩⟩ :=
    exists_balancedBlock_or_growth hA16 t hreserve
  · exact ⟨k, hkt, B, hBA, hBcard, hlarge⟩
  · subst k
    refine ⟨t, le_rfl, B, hBA, hBcard, ?_⟩
    have hpowpos : 0 < 5 ^ t := pow_pos (by omega) _
    nlinarith

/-- Four growth steps beat one binary digit because
`2 * 5^4 = 1250 < 1296 = 6^4`. -/
lemma balancedBlock_power_force (n u : ℕ) (hu : 0 < u) (hn : n < 2 ^ u) :
    5 ^ (4 * u) * n < 6 ^ (4 * u) := by
  calc
    5 ^ (4 * u) * n < 5 ^ (4 * u) * 2 ^ u :=
      Nat.mul_lt_mul_of_pos_left hn (pow_pos (by omega) _)
    _ = (5 ^ 4 * 2) ^ u := by
      rw [mul_pow, ← pow_mul]
    _ < (6 ^ 4) ^ u := by
      apply Nat.pow_lt_pow_left
      · norm_num
      · omega
    _ = 6 ^ (4 * u) := by rw [pow_mul]

/-- Quantitative Szemerédi--Vu small-block lemma.  Under the explicit reserve
condition, a block of at most eight times the binary logarithm of the ambient
cardinality already has at least ambient-cardinality many balanced sums. -/
lemma exists_small_balancedBlock
    {A : Finset ℕ} (hA16 : 16 ≤ A.card)
    (hreserve : 64 * (Nat.log 2 A.card + 1) ≤ A.card) :
    ∃ k ≤ 4 * (Nat.log 2 A.card + 1), ∃ B : Finset ℕ,
      B ⊆ A ∧ B.card = 2 * k ∧
        A.card ≤ (restrictedSums k B).card := by
  let u := Nat.log 2 A.card + 1
  have hu : 0 < u := by simp [u]
  have hAlog : A.card < 2 ^ u := by
    simpa [u] using Nat.lt_pow_succ_log_self Nat.one_lt_two A.card
  have hreserve' : 16 * (4 * u) ≤ A.card := by
    dsimp [u]
    omega
  have hforce : 5 ^ (4 * u) * A.card < 6 ^ (4 * u) :=
    balancedBlock_power_force A.card u hu hAlog
  simpa [u] using
    exists_balancedBlock_of_power_bound hA16 (4 * u) hreserve' hforce

/-- Union of a list of finite blocks. -/
def blockUnion {α : Type*} [DecidableEq α] : List (Finset α) → Finset α
  | [] => ∅
  | B :: blocks => B ∪ blockUnion blocks

@[simp] lemma blockUnion_nil {α : Type*} [DecidableEq α] :
    blockUnion ([] : List (Finset α)) = ∅ := rfl

@[simp] lemma blockUnion_cons {α : Type*} [DecidableEq α]
    (B : Finset α) (blocks : List (Finset α)) :
    blockUnion (B :: blocks) = B ∪ blockUnion blocks := rfl

lemma mem_blockUnion_iff {α : Type*} [DecidableEq α]
    {x : α} {blocks : List (Finset α)} :
    x ∈ blockUnion blocks ↔ ∃ B ∈ blocks, x ∈ B := by
  induction blocks with
  | nil => simp
  | cons B blocks ih => simp [ih]

lemma subset_blockUnion_of_mem {α : Type*} [DecidableEq α]
    {B : Finset α} {blocks : List (Finset α)} (hB : B ∈ blocks) :
    B ⊆ blockUnion blocks := by
  intro x hx
  exact mem_blockUnion_iff.mpr ⟨B, hB, hx⟩

lemma blockUnion_subset {α : Type*} [DecidableEq α]
    {A : Finset α} {blocks : List (Finset α)}
    (hblocks : ∀ B ∈ blocks, B ⊆ A) :
    blockUnion blocks ⊆ A := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := mem_blockUnion_iff.mp hx
  exact hblocks B hB hxB

/-- Repeatedly apply the small-block lemma to the unused remainder.  This is
the finite disjoint-block supply at the start of Szemerédi--Vu Section 7.10.
Every block is logarithmic in `|A|`, while its balanced sums have cardinality
at least half of `|A|`. -/
lemma exists_many_small_balancedBlocks
    {A : Finset ℕ} (t : ℕ)
    (hspace :
      64 * (Nat.log 2 A.card + 1) +
          8 * (Nat.log 2 A.card + 1) * t ≤ A.card)
    (hhalf : 16 * (Nat.log 2 A.card + 1) * t ≤ A.card) :
    ∃ blocks : List (Finset ℕ),
      blocks.length = t ∧
      blocks.Pairwise Disjoint ∧
      (∀ B ∈ blocks, ∃ k ≤ 4 * (Nat.log 2 A.card + 1),
        B ⊆ A ∧ B.card = 2 * k ∧
          A.card ≤ 2 * (restrictedSums k B).card) ∧
      (blockUnion blocks).card ≤
        8 * (Nat.log 2 A.card + 1) * t := by
  let u := Nat.log 2 A.card + 1
  have hu : 0 < u := by simp [u]
  induction t with
  | zero =>
      refine ⟨[], rfl, by simp, by simp, ?_⟩
      simp
  | succ t ih =>
      have hspace' : 64 * u + 8 * u * t ≤ A.card := by
        have hspaceSucc : 64 * u + 8 * u * (t + 1) ≤ A.card := by
          simpa [u] using hspace
        exact (Nat.add_le_add_left
          (Nat.mul_le_mul_left (8 * u) (Nat.le_succ t)) (64 * u)).trans hspaceSucc
      have hhalf' : 16 * u * t ≤ A.card := by
        have hhalfSucc : 16 * u * (t + 1) ≤ A.card := by
          simpa [u] using hhalf
        exact (Nat.mul_le_mul_left (16 * u) (Nat.le_succ t)).trans hhalfSucc
      obtain ⟨blocks, hlen, hpair, hblocks, hUcard⟩ :=
        ih (by simpa [u] using hspace') (by simpa [u] using hhalf')
      let U := blockUnion blocks
      let R := A \ U
      have hUA : U ⊆ A := by
        apply blockUnion_subset
        intro B hB
        obtain ⟨k, hk, hBA, _⟩ := hblocks B hB
        exact hBA
      have hRcard : R.card = A.card - U.card := by
        dsimp [R]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hUA]
      have hUcard' : U.card ≤ 8 * u * t := by
        simpa [U, u] using hUcard
      have hR64 : 64 * u ≤ R.card := by
        have h64U : 64 * u + U.card ≤ A.card :=
          (Nat.add_le_add_left hUcard' (64 * u)).trans hspace'
        rw [hRcard]
        omega
      have hR16 : 16 ≤ R.card := by omega
      have hRhalf : A.card ≤ 2 * R.card := by
        have h2U : 2 * U.card ≤ A.card := by
          calc
            2 * U.card ≤ 2 * (8 * u * t) := Nat.mul_le_mul_left 2 hUcard'
            _ = 16 * u * t := by ring
            _ ≤ A.card := hhalf'
        rw [hRcard]
        omega
      have hRleA : R.card ≤ A.card := Finset.card_le_card (Finset.sdiff_subset)
      have hlog : Nat.log 2 R.card + 1 ≤ u := by
        dsimp [u]
        exact Nat.add_le_add_right (Nat.log_mono_right hRleA) 1
      have hRreserve : 64 * (Nat.log 2 R.card + 1) ≤ R.card := by
        exact (Nat.mul_le_mul_left 64 hlog).trans hR64
      obtain ⟨k, hk, B, hBR, hBcard, hBsum⟩ :=
        exists_small_balancedBlock hR16 hRreserve
      have hku : k ≤ 4 * u :=
        hk.trans (Nat.mul_le_mul_left 4 hlog)
      have hBsize : B.card ≤ 8 * u := by
        rw [hBcard]
        omega
      have hBA : B ⊆ A := hBR.trans Finset.sdiff_subset
      have hBlarge : A.card ≤ 2 * (restrictedSums k B).card :=
        hRhalf.trans (Nat.mul_le_mul_left 2 hBsum)
      have hBdisj : ∀ C ∈ blocks, Disjoint B C := by
        intro C hC
        rw [Finset.disjoint_left]
        intro x hxB hxC
        have hxR := hBR hxB
        rw [Finset.mem_sdiff] at hxR
        exact hxR.2 (subset_blockUnion_of_mem hC hxC)
      refine ⟨B :: blocks, by simp [hlen], ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨hBdisj, hpair⟩
      · intro C hC
        rw [List.mem_cons] at hC
        rcases hC with rfl | hC
        · exact ⟨k, by simpa [u] using hku, hBA, hBcard, hBlarge⟩
        · exact hblocks C hC
      · calc
          (blockUnion (B :: blocks)).card = (B ∪ U).card := rfl
          _ ≤ B.card + U.card := Finset.card_union_le B U
          _ ≤ 8 * u + 8 * u * t := Nat.add_le_add hBsize hUcard'
          _ = 8 * u * (t + 1) := by ring
          _ = 8 * (Nat.log 2 A.card + 1) * (t + 1) := by rfl

/-- Subset sums supported on disjoint blocks add to a subset sum on their
union. -/
lemma add_mem_subsetSum_union_of_disjoint {A B : Finset ℕ} (hAB : Disjoint A B)
    {x y : ℕ} (hx : x ∈ A.subsetSum) (hy : y ∈ B.subsetSum) :
    x + y ∈ (A ∪ B).subsetSum := by
  rw [Finset.mem_subsetSum_iff] at hx hy ⊢
  obtain ⟨S, hSA, hs⟩ := hx
  obtain ⟨T, hTB, ht⟩ := hy
  refine ⟨S ∪ T, Finset.union_subset_union hSA hTB, ?_⟩
  rw [Finset.sum_union (hAB.mono hSA hTB)]
  omega

/-- Finset-level version of `add_mem_subsetSum_union_of_disjoint`. -/
lemma add_subsetSum_subset_union_subsetSum {A B : Finset ℕ} (hAB : Disjoint A B) :
    A.subsetSum + B.subsetSum ⊆ (A ∪ B).subsetSum := by
  intro z hz
  rw [Finset.mem_add] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact add_mem_subsetSum_union_of_disjoint hAB hx hy

lemma restrictedSums_subset_subsetSum (k : ℕ) (A : Finset ℕ) :
    restrictedSums k A ⊆ A.subsetSum := by
  intro m hm
  obtain ⟨S, hSA, _hScard, hsum⟩ := mem_restrictedSums_iff.mp hm
  rw [Finset.mem_subsetSum_iff]
  exact ⟨S, hSA, hsum⟩

/-- Iterated pointwise sum of a list of finite sets, with `{0}` as the empty
sum. -/
def finsetListSum : List (Finset ℕ) → Finset ℕ
  | [] => {0}
  | S :: sums => S + finsetListSum sums

@[simp] lemma finsetListSum_nil : finsetListSum [] = {0} := rfl

@[simp] lemma finsetListSum_cons (S : Finset ℕ) (sums : List (Finset ℕ)) :
    finsetListSum (S :: sums) = S + finsetListSum sums := rfl

@[simp] lemma finset_add_singleton_zero (S : Finset ℕ) : S + {0} = S := by
  ext x
  simp only [Finset.mem_add, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, rfl, hab⟩
    have hax : a = x := by omega
    simpa [hax] using ha
  · intro hx
    exact ⟨x, hx, 0, rfl, by simp⟩

@[simp] lemma singleton_zero_add_finset (S : Finset ℕ) : {0} + S = S := by
  rw [add_comm, finset_add_singleton_zero]

lemma finsetListSum_append (left right : List (Finset ℕ)) :
    finsetListSum (left ++ right) =
      finsetListSum left + finsetListSum right := by
  induction left with
  | nil => simp [finsetListSum]
  | cons S left ih => simp [finsetListSum, ih, add_assoc]

lemma finsetListSum_nonempty {sums : List (Finset ℕ)}
    (h : ∀ S ∈ sums, S.Nonempty) :
    (finsetListSum sums).Nonempty := by
  induction sums with
  | nil => simp [finsetListSum]
  | cons S sums ih =>
      obtain ⟨x, hx⟩ := h S (by simp)
      obtain ⟨y, hy⟩ := ih (by
        intro T hT
        exact h T (by simp [hT]))
      exact ⟨x + y, Finset.mem_add.mpr ⟨x, hx, y, hy, rfl⟩⟩

lemma List.Forall₂.exists_left_of_mem_right
    {α β : Type*} {R : α → β → Prop} {left : List α} {right : List β}
    (h : List.Forall₂ R left right) {b : β} (hb : b ∈ right) :
    ∃ a ∈ left, R a b := by
  induction h with
  | nil => simp at hb
  | @cons a b left right hab htail ih =>
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a, by simp, hab⟩
      · obtain ⟨c, hc, hcb⟩ := ih hb
        exact ⟨c, by simp [hc], hcb⟩

lemma finset_add_mono {A B C D : Finset ℕ}
    (hAC : A ⊆ C) (hBD : B ⊆ D) : A + B ⊆ C + D := by
  intro z hz
  rw [Finset.mem_add] at hz ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨a, hAC ha, b, hBD hb, rfl⟩

/-- A small-sum pair appearing inside an iterated sumset, with the remaining
summands absorbed into a nonempty translating set. -/
def HasSmallSumPair (K M : ℕ) (root : Finset ℕ) : Prop :=
  ∃ X Y Z : Finset ℕ,
    M ≤ X.card ∧ M ≤ Y.card ∧
    (X + Y).card ≤ K * min X.card Y.card ∧
    X + Y + Z ⊆ root ∧ Z.Nonempty

/-- Binary-tree growth dichotomy for sums of different sets.  If no pair of
subtree sumsets has small relative sumset, cardinality grows by a factor `K`
at every level. -/
lemma binaryTree_growth_or_smallSumPair
    (K M s : ℕ) (hK : 0 < K) (hM : 0 < M)
    (sums : List (Finset ℕ))
    (hlen : sums.length = 2 ^ s)
    (hcard : ∀ S ∈ sums, M ≤ S.card) :
    K ^ s * M ≤ (finsetListSum sums).card ∨
      HasSmallSumPair K M (finsetListSum sums) := by
  induction s generalizing sums with
  | zero =>
      obtain ⟨S, rfl⟩ : ∃ S, sums = [S] := by
        have : sums.length = 1 := by simpa using hlen
        exact List.length_eq_one_iff.mp this
      left
      simpa [finsetListSum] using hcard S (by simp)
  | succ s ih =>
      let left := sums.take (2 ^ s)
      let right := sums.drop (2 ^ s)
      have hsPow : 2 ^ s ≤ sums.length := by
        rw [hlen, pow_succ]
        omega
      have hleftLen : left.length = 2 ^ s := by
        dsimp [left]
        rw [List.length_take_of_le hsPow]
      have hrightLen : right.length = 2 ^ s := by
        dsimp [right]
        rw [List.length_drop, hlen, pow_succ]
        omega
      have hleftCard : ∀ S ∈ left, M ≤ S.card := by
        intro S hS
        exact hcard S (List.mem_of_mem_take hS)
      have hrightCard : ∀ S ∈ right, M ≤ S.card := by
        intro S hS
        exact hcard S (List.mem_of_mem_drop hS)
      have hsplit : sums = left ++ right := by
        exact (List.take_append_drop (2 ^ s) sums).symm
      have hroot : finsetListSum sums =
          finsetListSum left + finsetListSum right := by
        rw [hsplit, finsetListSum_append]
      rcases ih left hleftLen hleftCard with hleftLarge | hleftSmall
      · rcases ih right hrightLen hrightCard with hrightLarge | hrightSmall
        · by_cases hsmall :
            (finsetListSum left + finsetListSum right).card ≤
              K * min (finsetListSum left).card (finsetListSum right).card
          · right
            refine ⟨finsetListSum left, finsetListSum right, {0}, ?_, ?_,
              hsmall, ?_, by simp⟩
            · have hKpow : 1 ≤ K ^ s := one_le_pow₀ hK
              exact le_trans (by nlinarith) hleftLarge
            · have hKpow : 1 ≤ K ^ s := one_le_pow₀ hK
              exact le_trans (by nlinarith) hrightLarge
            · rw [hroot]
              rw [finset_add_singleton_zero]
          · left
            have hmin : K ^ s * M ≤
                min (finsetListSum left).card (finsetListSum right).card :=
              le_min hleftLarge hrightLarge
            have hgrowth :
                K * min (finsetListSum left).card (finsetListSum right).card <
                  (finsetListSum left + finsetListSum right).card := by omega
            rw [hroot, pow_succ]
            nlinarith
        · right
          obtain ⟨X, Y, Z, hXM, hYM, hXY, hsub, hZ⟩ := hrightSmall
          refine ⟨X, Y, finsetListSum left + Z, hXM, hYM, hXY, ?_, ?_⟩
          · rw [hroot]
            have hmono := finset_add_mono
              (Finset.Subset.rfl : finsetListSum left ⊆ finsetListSum left) hsub
            simpa only [add_assoc, add_comm, add_left_comm] using hmono
          · exact (finsetListSum_nonempty (fun S hS =>
                Finset.card_pos.mp (hM.trans_le (hleftCard S hS)))).add hZ
      · right
        obtain ⟨X, Y, Z, hXM, hYM, hXY, hsub, hZ⟩ := hleftSmall
        refine ⟨X, Y, Z + finsetListSum right, hXM, hYM, hXY, ?_, ?_⟩
        · rw [hroot]
          have hmono := finset_add_mono hsub
              (Finset.Subset.rfl : finsetListSum right ⊆ finsetListSum right)
          simpa only [add_assoc] using hmono
        · exact hZ.add (finsetListSum_nonempty (fun S hS =>
              Finset.card_pos.mp (hM.trans_le (hrightCard S hS))))

/-- Truncate the two sides of a small pair to equal cardinality. -/
lemma HasSmallSumPair.equalize {K M : ℕ} {root : Finset ℕ}
    (h : HasSmallSumPair K M root) :
    ∃ X Y Z : Finset ℕ,
      M ≤ X.card ∧ X.card = Y.card ∧
      (X + Y).card ≤ K * X.card ∧
      X + Y + Z ⊆ root ∧ Z.Nonempty := by
  obtain ⟨X, Y, Z, hXM, hYM, hsmall, hsub, hZ⟩ := h
  let m := min X.card Y.card
  have hmX : m ≤ X.card := min_le_left _ _
  have hmY : m ≤ Y.card := min_le_right _ _
  obtain ⟨X', hX'X, hX'card⟩ := Finset.exists_subset_card_eq hmX
  obtain ⟨Y', hY'Y, hY'card⟩ := Finset.exists_subset_card_eq hmY
  have hMm : M ≤ m := le_min hXM hYM
  refine ⟨X', Y', Z, ?_, ?_, ?_, ?_, hZ⟩
  · simpa [hX'card] using hMm
  · rw [hX'card, hY'card]
  · calc
      (X' + Y').card ≤ (X + Y).card :=
        Finset.card_le_card (finset_add_mono hX'X hY'Y)
      _ ≤ K * m := hsmall
      _ = K * X'.card := by rw [hX'card]
  · exact (finset_add_mono (finset_add_mono hX'X hY'Y)
      (Finset.Subset.rfl : Z ⊆ Z)).trans hsub

/-- If every input set lies in `[0,H]`, their iterated sum lies in the
correspondingly dilated interval. -/
lemma finsetListSum_subset_Icc
    {sums : List (Finset ℕ)} {H : ℕ}
    (hbounded : ∀ S ∈ sums, S ⊆ Finset.Icc 0 H) :
    finsetListSum sums ⊆ Finset.Icc 0 (sums.length * H) := by
  induction sums with
  | nil => simp [finsetListSum]
  | cons S sums ih =>
      intro z hz
      rw [finsetListSum_cons, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      have hx' := Finset.mem_Icc.mp (hbounded S (by simp) hx)
      have hy' := Finset.mem_Icc.mp (ih (by
        intro T hT
        exact hbounded T (by simp [hT])) hy)
      rw [Finset.mem_Icc]
      simp only [List.length_cons]
      refine ⟨Nat.zero_le _, ?_⟩
      calc
        x + y ≤ H + sums.length * H := Nat.add_le_add hx'.2 hy'.2
        _ = (sums.length + 1) * H := by ring

/-- Ambient interval growth forces a small equal-cardinality pair somewhere
in the binary sumset tree. -/
lemma exists_equalSmallSumPair_of_interval
    (K M s H : ℕ) (hK : 0 < K) (hM : 0 < M)
    (sums : List (Finset ℕ))
    (hlen : sums.length = 2 ^ s)
    (hcard : ∀ S ∈ sums, M ≤ S.card)
    (hbounded : ∀ S ∈ sums, S ⊆ Finset.Icc 0 H)
    (hgrowth : 2 ^ s * H + 1 < K ^ s * M) :
    ∃ X Y Z : Finset ℕ,
      M ≤ X.card ∧ X.card = Y.card ∧
      (X + Y).card ≤ K * X.card ∧
      X + Y + Z ⊆ finsetListSum sums ∧ Z.Nonempty := by
  rcases binaryTree_growth_or_smallSumPair K M s hK hM sums hlen hcard with
    hlarge | hsmall
  · have hsub := finsetListSum_subset_Icc hbounded
    have hupper : (finsetListSum sums).card ≤ 2 ^ s * H + 1 := by
      calc
        (finsetListSum sums).card ≤
            (Finset.Icc 0 (sums.length * H)).card := Finset.card_le_card hsub
        _ = 2 ^ s * H + 1 := by simp [hlen]
    omega
  · exact hsmall.equalize

lemma disjoint_blockUnion_of_forall {B : Finset ℕ} {blocks : List (Finset ℕ)}
    (h : ∀ C ∈ blocks, Disjoint B C) :
    Disjoint B (blockUnion blocks) := by
  rw [Finset.disjoint_left]
  intro x hxB hxU
  obtain ⟨C, hC, hxC⟩ := mem_blockUnion_iff.mp hxU
  exact Finset.disjoint_left.mp (h C hC) hxB hxC

/-- Sums chosen independently from subset-sum sets of disjoint blocks remain
subset sums of the union of the blocks. -/
lemma finsetListSum_subset_blockUnion_subsetSum
    {blocks sums : List (Finset ℕ)}
    (hpair : blocks.Pairwise Disjoint)
    (hrel : List.Forall₂ (fun B S => S ⊆ B.subsetSum) blocks sums) :
    finsetListSum sums ⊆ (blockUnion blocks).subsetSum := by
  induction hrel with
  | nil => simp [finsetListSum, blockUnion]
  | @cons B S blocks sums hSB htail ih =>
      rw [List.pairwise_cons] at hpair
      have hBU : Disjoint B (blockUnion blocks) :=
        disjoint_blockUnion_of_forall hpair.1
      exact (finset_add_mono hSB (ih hpair.2)).trans
        (add_subsetSum_subset_union_subsetSum hBU)

/-- Choose, for every block supplied above, its large balanced restricted-sum
set. -/
lemma exists_large_balancedSumsets_of_blocks
    {A : Finset ℕ} {blocks : List (Finset ℕ)}
    (hblocks : ∀ B ∈ blocks, ∃ k ≤ 4 * (Nat.log 2 A.card + 1),
      B ⊆ A ∧ B.card = 2 * k ∧
        A.card ≤ 2 * (restrictedSums k B).card) :
    ∃ sums : List (Finset ℕ),
      List.Forall₂ (fun B S =>
        S ⊆ B.subsetSum ∧ A.card ≤ 2 * S.card) blocks sums := by
  induction blocks with
  | nil => exact ⟨[], .nil⟩
  | cons B blocks ih =>
      obtain ⟨k, _hk, _hBA, _hBcard, hlarge⟩ := hblocks B (by simp)
      obtain ⟨sums, hsums⟩ := ih (by
        intro C hC
        exact hblocks C (by simp [hC]))
      refine ⟨restrictedSums k B :: sums, .cons ?_ hsums⟩
      exact ⟨restrictedSums_subset_subsetSum k B, hlarge⟩

/-- Restricted sums inherit the obvious interval bound from the ambient
set. -/
lemma restrictedSums_subset_Icc_of_subset
    {A B : Finset ℕ} {k N : ℕ}
    (hBA : B ⊆ A) (hAN : A ⊆ Finset.Icc 1 N) :
    restrictedSums k B ⊆ Finset.Icc 0 (k * N) := by
  intro m hm
  obtain ⟨T, hTB, hTcard, rfl⟩ := mem_restrictedSums_iff.mp hm
  rw [Finset.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  calc
    ∑ a ∈ T, a ≤ ∑ _a ∈ T, N := by
      apply Finset.sum_le_sum
      intro a ha
      exact (Finset.mem_Icc.mp (hAN (hBA (hTB ha)))).2
    _ = T.card * N := by simp
    _ = k * N := by rw [hTcard]

/-- Bounded version of the balanced-sumset choice. -/
lemma exists_large_balancedSumsets_of_blocks_bounded
    {A : Finset ℕ} {N : ℕ} {blocks : List (Finset ℕ)}
    (hAN : A ⊆ Finset.Icc 1 N)
    (hblocks : ∀ B ∈ blocks, ∃ k ≤ 4 * (Nat.log 2 A.card + 1),
      B ⊆ A ∧ B.card = 2 * k ∧
        A.card ≤ 2 * (restrictedSums k B).card) :
    ∃ sums : List (Finset ℕ),
      List.Forall₂ (fun B S =>
        S ⊆ B.subsetSum ∧ A.card ≤ 2 * S.card ∧
          S ⊆ Finset.Icc 0 (4 * (Nat.log 2 A.card + 1) * N)) blocks sums := by
  induction blocks with
  | nil => exact ⟨[], .nil⟩
  | cons B blocks ih =>
      obtain ⟨k, hk, hBA, _hBcard, hlarge⟩ := hblocks B (by simp)
      obtain ⟨sums, hsums⟩ := ih (by
        intro C hC
        exact hblocks C (by simp [hC]))
      refine ⟨restrictedSums k B :: sums, .cons ?_ hsums⟩
      refine ⟨restrictedSums_subset_subsetSum k B, hlarge, ?_⟩
      exact (restrictedSums_subset_Icc_of_subset hBA hAN).trans (by
        intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        constructor
        · exact hx.1
        · exact hx.2.trans (Nat.mul_le_mul_right N hk))

/-- Distinct-summand reduction in a form ready for the Szemerédi--Vu
different-sumset theorem: the subset sums of `A` contain an iterated sum of
`t` finite sets, each having at least half the cardinality of `A`. -/
lemma exists_large_disjointBlock_sumset
    {A : Finset ℕ} (t : ℕ)
    (hspace :
      64 * (Nat.log 2 A.card + 1) +
          8 * (Nat.log 2 A.card + 1) * t ≤ A.card)
    (hhalf : 16 * (Nat.log 2 A.card + 1) * t ≤ A.card) :
    ∃ blocks sums : List (Finset ℕ),
      blocks.length = t ∧ sums.length = t ∧
      blocks.Pairwise Disjoint ∧
      List.Forall₂ (fun B S =>
        S ⊆ B.subsetSum ∧ A.card ≤ 2 * S.card) blocks sums ∧
      finsetListSum sums ⊆ A.subsetSum := by
  obtain ⟨blocks, hlen, hpair, hblocks, _hUcard⟩ :=
    exists_many_small_balancedBlocks t hspace hhalf
  obtain ⟨sums, hrel⟩ := exists_large_balancedSumsets_of_blocks hblocks
  have hslen : sums.length = t := by
    rw [← hlen]
    exact hrel.length_eq.symm
  refine ⟨blocks, sums, hlen, hslen, hpair, hrel, ?_⟩
  have hrelSub : List.Forall₂ (fun B S => S ⊆ B.subsetSum) blocks sums :=
    hrel.imp fun _ _ h => h.1
  exact (finsetListSum_subset_blockUnion_subsetSum hpair hrelSub).trans
    (Finset.subsetSum_mono (blockUnion_subset fun B hB =>
      (hblocks B hB).choose_spec.2.1))

/-- Quantitative growth-tree output from the distinct-summand reduction.
Under the displayed cubic-scale inequality, the subset sums of `A` contain a
translate of `X+Y`, where `X,Y` have equal cardinality at least `|A|/2` and
small mixed sumset. -/
lemma exists_smallSumPair_in_subsetSum
    {A : Finset ℕ} {N K s : ℕ}
    (hAN : A ⊆ Finset.Icc 1 N)
    (hK : 0 < K) (hA2 : 2 ≤ A.card)
    (hspace :
      64 * (Nat.log 2 A.card + 1) +
          8 * (Nat.log 2 A.card + 1) * (2 ^ s) ≤ A.card)
    (hhalf : 16 * (Nat.log 2 A.card + 1) * (2 ^ s) ≤ A.card)
    (hgrowth :
      2 ^ s * (4 * (Nat.log 2 A.card + 1) * N) + 1 <
        K ^ s * (A.card / 2)) :
    ∃ X Y Z : Finset ℕ,
      A.card / 2 ≤ X.card ∧ X.card = Y.card ∧
      (X + Y).card ≤ K * X.card ∧
      X + Y + Z ⊆ A.subsetSum ∧ Z.Nonempty := by
  obtain ⟨blocks, _hlen, hpair, hblocks, _hUcard⟩ :=
    exists_many_small_balancedBlocks (2 ^ s) hspace hhalf
  obtain ⟨sums, hrel⟩ :=
    exists_large_balancedSumsets_of_blocks_bounded hAN hblocks
  have hslen : sums.length = 2 ^ s := hrel.length_eq.symm.trans _hlen
  have hsCard : ∀ S ∈ sums, A.card / 2 ≤ S.card := by
    intro S hS
    obtain ⟨B, hB, hrelBS⟩ :=
      List.Forall₂.exists_left_of_mem_right hrel hS
    omega
  have hsBound : ∀ S ∈ sums,
      S ⊆ Finset.Icc 0 (4 * (Nat.log 2 A.card + 1) * N) := by
    intro S hS
    obtain ⟨B, hB, hrelBS⟩ :=
      List.Forall₂.exists_left_of_mem_right hrel hS
    exact hrelBS.2.2
  have hMpos : 0 < A.card / 2 := Nat.div_pos (by omega) (by omega)
  obtain ⟨X, Y, Z, hXM, hXYcard, hsmall, hsub, hZ⟩ :=
    exists_equalSmallSumPair_of_interval K (A.card / 2) s
      (4 * (Nat.log 2 A.card + 1) * N) hK hMpos sums hslen hsCard hsBound hgrowth
  refine ⟨X, Y, Z, hXM, hXYcard, hsmall, ?_, hZ⟩
  have hrelSub : List.Forall₂ (fun B S => S ⊆ B.subsetSum) blocks sums :=
    hrel.imp fun _ _ h => h.1
  exact hsub.trans ((finsetListSum_subset_blockUnion_subsetSum hpair hrelSub).trans
    (Finset.subsetSum_mono (blockUnion_subset fun B hB =>
      (hblocks B hB).choose_spec.2.1)))

/-! ## Passage from natural sumsets to the integer inverse problem -/

/-- The faithful image of a finite natural-number set in the additive group
of integers.  Nguyen--Vu's inverse theorems are stated in `ℤ`, while the
distinct-summand construction above naturally lives in `ℕ`. -/
def natToIntFinset (A : Finset ℕ) : Finset ℤ :=
  A.image (Int.ofNatHom : ℕ →+* ℤ)

@[simp] lemma card_natToIntFinset (A : Finset ℕ) :
    (natToIntFinset A).card = A.card := by
  exact Finset.card_image_of_injective A Int.ofNat_injective

lemma natToIntFinset_add (A B : Finset ℕ) :
    natToIntFinset (A + B) = natToIntFinset A + natToIntFinset B := by
  exact Finset.image_add (Int.ofNatHom : ℕ →+* ℤ)

lemma natToIntFinset_nonempty {A : Finset ℕ} :
    (natToIntFinset A).Nonempty ↔ A.Nonempty := by
  simp [natToIntFinset]

/-- Plünnecke--Ruzsa control after faithfully embedding a natural mixed
sumset into `ℤ`.  This is the quantitative input used by the Freiman/Bilu
inverse step in the original Nguyen--Vu route. -/
lemma pluennecke_natToInt
    {X Y : Finset ℕ} {K m n : ℕ}
    (hX : X.Nonempty) (hsmall : (X + Y).card ≤ K * X.card) :
    (m • natToIntFinset Y - n • natToIntFinset Y).card ≤
      K ^ (m + n) * X.card := by
  have hsmall' :
      (natToIntFinset X + natToIntFinset Y).card ≤
        K * (natToIntFinset X).card := by
    rw [← natToIntFinset_add]
    simpa using hsmall
  have hbound := pluennecke_ruzsa_int
    (natToIntFinset_nonempty.mpr hX) hsmall' (m := m) (n := n)
  simpa using hbound

/-- Ruzsa covering after the same faithful embedding.  Thus a small mixed
sumset covers one side by at most `K` translates of the difference set of
the other side. -/
lemma exists_int_cover_of_small_mixed_sumset
    {X Y : Finset ℕ} {K : ℕ}
    (hY : Y.Nonempty) (hsmall : (X + Y).card ≤ K * Y.card) :
    ∃ F ⊆ natToIntFinset X, F.card ≤ K ∧
      natToIntFinset X ⊆ F + (natToIntFinset Y - natToIntFinset Y) := by
  have hsmall' :
      (natToIntFinset X + natToIntFinset Y).card ≤
        K * (natToIntFinset Y).card := by
    rw [← natToIntFinset_add]
    simpa using hsmall
  exact ruzsa_covering_int (natToIntFinset_nonempty.mpr hY) hsmall'

/-- Complete small-mixed-sumset handoff needed for Nguyen--Vu's inverse
argument.  Equal cardinality lets us control all fixed iterated difference
sets on either side and gives bounded Ruzsa covers in both directions. -/
lemma small_mixed_sumset_integer_controls
    {X Y : Finset ℕ} {K : ℕ}
    (hX : X.Nonempty) (hcard : X.card = Y.card)
    (hsmall : (X + Y).card ≤ K * X.card) :
    (∀ m n : ℕ,
      (m • natToIntFinset Y - n • natToIntFinset Y).card ≤
        K ^ (m + n) * X.card) ∧
    (∀ m n : ℕ,
      (m • natToIntFinset X - n • natToIntFinset X).card ≤
        K ^ (m + n) * X.card) ∧
    (∃ F ⊆ natToIntFinset X, F.card ≤ K ∧
      natToIntFinset X ⊆ F + (natToIntFinset Y - natToIntFinset Y)) ∧
    (∃ F ⊆ natToIntFinset Y, F.card ≤ K ∧
      natToIntFinset Y ⊆ F + (natToIntFinset X - natToIntFinset X)) := by
  have hY : Y.Nonempty := Finset.card_pos.mp (by
    rw [← hcard]
    exact hX.card_pos)
  have hsmallY : (X + Y).card ≤ K * Y.card := by simpa [hcard] using hsmall
  have hsmallSwap : (Y + X).card ≤ K * Y.card := by
    simpa only [add_comm] using hsmallY
  refine ⟨fun m n => pluennecke_natToInt (m := m) (n := n) hX hsmall,
    fun m n => ?_, exists_int_cover_of_small_mixed_sumset hY hsmallY, ?_⟩
  · have h := pluennecke_natToInt (m := m) (n := n) hY hsmallSwap
    simpa [hcard] using h
  · exact exists_int_cover_of_small_mixed_sumset hX (by
      simpa only [add_comm, hcard] using hsmall)

/-! ## Collision counting for non-proper progressions -/

/-- In a finite family of directed edges `a → g a`, with injective successor
map and no loops, one can keep at least a third of the sources while making
all chosen source and target vertices disjoint. -/
lemma exists_large_disjoint_edge_sources
    {α : Type*} [DecidableEq α] (g : α → α) (hg : Function.Injective g)
    (s : Finset α) (hne : ∀ a ∈ s, g a ≠ a) :
    ∃ t ⊆ s, s.card ≤ 3 * t.card ∧ Disjoint (t.image g) t := by
  classical
  refine Finset.strongInduction (p := fun s =>
    (∀ a ∈ s, g a ≠ a) →
      ∃ t ⊆ s, s.card ≤ 3 * t.card ∧ Disjoint (t.image g) t) ?_ s hne
  intro s ih hne
  by_cases hs : s = ∅
  · subst s
    exact ⟨∅, by simp⟩
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    letI : Nonempty α := ⟨a⟩
    let bad : Finset α := {a, g a, Function.invFun g a}
    let r := s \ bad
    have hra : a ∉ r := by simp [r, bad]
    have hrs : r ⊂ s := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, by
        intro hrsEq
        exact hra (hrsEq ▸ ha)⟩
    obtain ⟨t, htr, hrcard, hdisj⟩ := ih r hrs (by
      intro u hu
      exact hne u (Finset.sdiff_subset hu))
    have hat : a ∉ t := fun hat => hra (htr hat)
    refine ⟨insert a t, ?_, ?_, ?_⟩
    · intro u hu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact ha
      · exact Finset.sdiff_subset (htr hu)
    · have hbad : bad.card ≤ 3 := by
        dsimp [bad]
        calc
          ({a, g a, Function.invFun g a} : Finset α).card ≤
              ({g a, Function.invFun g a} : Finset α).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({Function.invFun g a} : Finset α).card + 2 := by
            have := Finset.card_insert_le (g a) ({Function.invFun g a} : Finset α)
            omega
          _ = 3 := by simp
      have hsr : s.card ≤ r.card + bad.card := by
        have hinter : (s ∩ bad).card ≤ bad.card :=
          Finset.card_le_card Finset.inter_subset_right
        have hdecomp := Finset.card_sdiff_add_card_inter s bad
        dsimp only [r]
        omega
      rw [Finset.card_insert_of_notMem hat]
      omega
    · rw [Finset.image_insert]
      rw [Finset.disjoint_left]
      intro u huImage huSource
      rw [Finset.mem_insert] at huImage huSource
      rcases huImage with hua | huImage
      · subst u
        rcases huSource with hga | hgat
        · exact (hne a ha) hga
        · have hgatR := htr hgat
          exact (Finset.mem_sdiff.mp hgatR).2 (by simp [bad])
      · rcases huSource with hua | hut
        · subst u
          obtain ⟨v, hvt, hva⟩ := Finset.mem_image.mp huImage
          have hvR := htr hvt
          have hvInv : v = Function.invFun g a := by
            calc
              v = Function.invFun g (g v) := (Function.leftInverse_invFun hg v).symm
              _ = Function.invFun g a := congrArg (Function.invFun g) hva
          exact (Finset.mem_sdiff.mp hvR).2 (by simp [bad, hvInv])
        · exact (Finset.disjoint_left.mp hdisj huImage hut)

/-- Removing one endpoint from each disjoint collision leaves a set which
still maps onto the whole image. -/
lemma card_image_add_card_le_of_disjoint_collisions
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {D T : Finset α} {f : α → β} {g : α → α}
    (hTD : T ⊆ D) (hgTD : T.image g ⊆ D)
    (hdisj : Disjoint (T.image g) T)
    (hginj : Set.InjOn g T)
    (hcoll : ∀ x ∈ T, f (g x) = f x) :
    (D.image f).card + T.card ≤ D.card := by
  have himage : D.image f = (D \ T.image g).image f := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨x, hxD, rfl⟩ := Finset.mem_image.mp hz
      by_cases hxg : x ∈ T.image g
      · obtain ⟨t, htT, htx⟩ := Finset.mem_image.mp hxg
        have htNot : t ∉ T.image g := by
          intro htImage
          exact Finset.disjoint_left.mp hdisj htImage htT
        apply Finset.mem_image.mpr
        refine ⟨t, Finset.mem_sdiff.mpr ⟨hTD htT, htNot⟩, ?_⟩
        rw [← hcoll t htT, htx]
      · exact Finset.mem_image_of_mem f (Finset.mem_sdiff.mpr ⟨hxD, hxg⟩)
    · exact Finset.image_subset_image Finset.sdiff_subset
  have hcardImage : (D.image f).card ≤ (D \ T.image g).card := by
    rw [himage]
    exact Finset.card_image_le
  have hcardTarget : (T.image g).card = T.card :=
    Finset.card_image_of_injOn hginj
  have hdecomp := Finset.card_sdiff_add_card_inter D (T.image g)
  have hinter : D ∩ T.image g = T.image g := Finset.inter_eq_right.mpr hgTD
  rw [hinter, hcardTarget] at hdecomp
  omega

/-- Quantitative form: three copies of the image, plus the number of available
translation collisions, fit inside three copies of the domain. -/
lemma three_mul_card_image_add_card_le_of_translation_collisions
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {D S : Finset α} {f : α → β} {g : α → α}
    (hg : Function.Injective g) (hSD : S ⊆ D) (hgSD : S.image g ⊆ D)
    (hne : ∀ x ∈ S, g x ≠ x)
    (hcoll : ∀ x ∈ S, f (g x) = f x) :
    3 * (D.image f).card + S.card ≤ 3 * D.card := by
  obtain ⟨T, hTS, hST, hdisj⟩ :=
    exists_large_disjoint_edge_sources g hg S hne
  have hTD : T ⊆ D := hTS.trans hSD
  have hgTD : T.image g ⊆ D :=
    (Finset.image_subset_image hTS).trans hgSD
  have hcard := card_image_add_card_le_of_disjoint_collisions
    hTD hgTD hdisj hg.injOn (fun x hx => hcoll x (hTS hx))
  omega

/-! ## Generalized arithmetic progressions -/

/-- An affine generalized arithmetic progression in `ℤ`, presented by a
finite box of coefficients. -/
structure GeneralizedAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace GeneralizedAP

/-- Coefficient vectors in the defining box. -/
abbrev Param (Q : GeneralizedAP) := (i : Fin Q.rank) → Fin (Q.length i + 1)

/-- Evaluation of a coefficient vector. -/
def eval (Q : GeneralizedAP) (x : Q.Param) : ℤ :=
  Q.base + ∑ i : Fin Q.rank, (x i : ℤ) * Q.step i

/-- The finite carrier of a GAP. -/
def carrier (Q : GeneralizedAP) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

/-- A GAP is proper when its coefficient map is injective. -/
def Proper (Q : GeneralizedAP) : Prop := Function.Injective Q.eval

lemma mem_carrier_iff (Q : GeneralizedAP) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

/-- A proper GAP has the cardinality of its coefficient box. -/
lemma card_carrier_of_proper (Q : GeneralizedAP) (hQ : Q.Proper) :
    Q.carrier.card = ∏ i : Fin Q.rank, (Q.length i + 1) := by
  rw [carrier, Finset.card_image_of_injective (Finset.univ : Finset Q.Param) hQ,
    Finset.card_univ]
  simp [Param]

/-- The geometric volume used in the Szemerédi--Vu and Nguyen--Vu papers. -/
def volume (Q : GeneralizedAP) : ℕ :=
  ∏ i : Fin Q.rank, Q.length i

/-- The homogeneous linear part of the GAP evaluation map. -/
def linearEval (Q : GeneralizedAP) (v : Fin Q.rank → ℤ) : ℤ :=
  ∑ i : Fin Q.rank, v i * Q.step i

lemma eval_eq_iff_linearEval_sub_eq_zero (Q : GeneralizedAP)
    (x y : Q.Param) :
    Q.eval x = Q.eval y ↔
      Q.linearEval (fun i => (x i : ℤ) - (y i : ℤ)) = 0 := by
  simp only [eval, linearEval]
  constructor
  · intro h
    have h' : (∑ i, (x i : ℤ) * Q.step i) =
        ∑ i, (y i : ℤ) * Q.step i := add_left_cancel h
    rw [show (∑ i, ((x i : ℤ) - (y i : ℤ)) * Q.step i) =
        (∑ i, (x i : ℤ) * Q.step i) -
          ∑ i, (y i : ℤ) * Q.step i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    exact sub_eq_zero.mpr h'
  · intro h
    rw [show (∑ i, ((x i : ℤ) - (y i : ℤ)) * Q.step i) =
        (∑ i, (x i : ℤ) * Q.step i) -
          ∑ i, (y i : ℤ) * Q.step i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring] at h
    exact congrArg (Q.base + ·) (sub_eq_zero.mp h)

/-- Even without properness, the carrier has no more elements than its
coefficient box. -/
lemma card_carrier_le_box (Q : GeneralizedAP) :
    Q.carrier.card ≤ ∏ i : Fin Q.rank, (Q.length i + 1) := by
  rw [carrier]
  calc
    ((Finset.univ : Finset Q.Param).image Q.eval).card ≤
        (Finset.univ : Finset Q.Param).card := Finset.card_image_le
    _ = ∏ i : Fin Q.rank, (Q.length i + 1) := by
      simp [Param]

/-- A coefficient vector which is killed by the homogeneous evaluation map. -/
def Vanishes (Q : GeneralizedAP) (v : Fin Q.rank → ℤ) : Prop :=
  Q.linearEval v = 0

/-- Paper notation `nQ`: multiply the affine base and every side length by
`n`, while retaining the difference set. -/
def dilate (n : ℕ) (Q : GeneralizedAP) : GeneralizedAP where
  rank := Q.rank
  base := n * Q.base
  step := Q.step
  length i := n * Q.length i

@[simp] lemma rank_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).rank = Q.rank := rfl

@[simp] lemma dilate_dilate (m n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate m).dilate n = Q.dilate (n * m) := by
  cases Q with
  | mk rank base step length =>
      simp [dilate, Nat.cast_mul, mul_assoc]

@[simp] lemma dilate_one (Q : GeneralizedAP) : Q.dilate 1 = Q := by
  cases Q
  simp [dilate]

@[simp] lemma volume_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).volume = n ^ Q.rank * Q.volume := by
  change (∏ i : Fin Q.rank, n * Q.length i) =
    n ^ Q.rank * ∏ i : Fin Q.rank, Q.length i
  rw [Finset.prod_mul_distrib]
  simp

/-- The coefficient-box cardinality of a GAP presentation. -/
def boxCard (Q : GeneralizedAP) : ℕ :=
  ∏ i : Fin Q.rank, (Q.length i + 1)

@[simp] lemma boxCard_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).boxCard =
      ∏ i : Fin Q.rank, (n * Q.length i + 1) := by
  rfl

/-- Geometric volume never exceeds coefficient-box cardinality. -/
lemma volume_le_boxCard (Q : GeneralizedAP) : Q.volume ≤ Q.boxCard := by
  rw [volume, boxCard]
  apply Finset.prod_le_prod'
  intro i _hi
  omega

/-- If no side is degenerate, coefficient-box cardinality is at most
`2^rank` times geometric volume. -/
lemma boxCard_le_two_pow_mul_volume (Q : GeneralizedAP)
    (hpos : ∀ i, 0 < Q.length i) :
    Q.boxCard ≤ 2 ^ Q.rank * Q.volume := by
  rw [boxCard, volume]
  calc
    ∏ i : Fin Q.rank, (Q.length i + 1) ≤
        ∏ i : Fin Q.rank, 2 * Q.length i := by
      apply Finset.prod_le_prod'
      intro i _hi
      have hi := hpos i
      omega
    _ = 2 ^ Q.rank * ∏ i : Fin Q.rank, Q.length i := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Cardinality/volume comparison for a proper nondegenerate GAP. -/
lemma card_carrier_bounds_of_proper (Q : GeneralizedAP)
    (hproper : Q.Proper) (hpos : ∀ i, 0 < Q.length i) :
    Q.volume ≤ Q.carrier.card ∧
      Q.carrier.card ≤ 2 ^ Q.rank * Q.volume := by
  rw [Q.card_carrier_of_proper hproper]
  exact ⟨Q.volume_le_boxCard, Q.boxCard_le_two_pow_mul_volume hpos⟩

/-- The same upper comparison for a positive dilation. -/
lemma boxCard_dilate_le_two_pow_mul_volume_dilate (Q : GeneralizedAP)
    {g : ℕ} (hg : 0 < g) (hpos : ∀ i, 0 < Q.length i) :
    (Q.dilate g).boxCard ≤
      2 ^ Q.rank * (Q.dilate g).volume := by
  apply (Q.dilate g).boxCard_le_two_pow_mul_volume
  intro i
  dsimp [dilate]
  exact Nat.mul_pos hg (hpos i)

/-- For nondegenerate sides, the fourfold coefficient box is at least
`2^rank` times the original box. -/
lemma pow_two_mul_boxCard_le_boxCard_dilate_four (Q : GeneralizedAP)
    (hpos : ∀ i, 0 < Q.length i) :
    2 ^ Q.rank * Q.boxCard ≤ (Q.dilate 4).boxCard := by
  rw [boxCard_dilate, boxCard]
  calc
    2 ^ Q.rank * ∏ i : Fin Q.rank, (Q.length i + 1) =
        ∏ i : Fin Q.rank, 2 * (Q.length i + 1) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i : Fin Q.rank, (4 * Q.length i + 1) := by
      apply Finset.prod_le_prod'
      intro i _hi
      have hi := hpos i
      omega

/-- Properness of a positive integer dilation implies properness of the
original GAP. -/
lemma proper_of_dilate_proper (Q : GeneralizedAP) {n : ℕ} (hn : 0 < n)
    (hproper : (Q.dilate n).Proper) : Q.Proper := by
  intro x y hxy
  let liftParam : Q.Param → (Q.dilate n).Param := fun z i =>
    ⟨z i, by
      have hz : (z i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (z i).isLt
      have hLn : Q.length i ≤ n * Q.length i := by
        calc
          Q.length i = 1 * Q.length i := by simp
          _ ≤ n * Q.length i := Nat.mul_le_mul_right (Q.length i) hn
      dsimp [dilate]
      exact Nat.lt_succ_of_le (hz.trans hLn)⟩
  have hsum : (∑ i, (x i : ℤ) * Q.step i) =
      ∑ i, (y i : ℤ) * Q.step i := by
    exact add_left_cancel hxy
  have hlift : (Q.dilate n).eval (liftParam x) =
      (Q.dilate n).eval (liftParam y) := by
    simp only [eval, dilate, liftParam]
    exact congrArg ((n : ℤ) * Q.base + ·) hsum
  have hliftEq := hproper hlift
  funext i
  have hi := congrFun hliftEq i
  apply Fin.ext
  simpa only [liftParam] using congrArg Fin.val hi

/-- Nguyen--Vu's `t`-properness: the paper dilation `tQ` is proper. -/
def TProper (Q : GeneralizedAP) (t : ℕ) : Prop :=
  (Q.dilate t).Proper

@[simp] lemma tProper_one_iff (Q : GeneralizedAP) :
    Q.TProper 1 ↔ Q.Proper := by
  simp [TProper]

/-- Properness at a product dilation descends to the second factor. -/
lemma tProper_of_tProper_mul (Q : GeneralizedAP) {s t : ℕ}
    (hs : 0 < s) (h : Q.TProper (s * t)) : Q.TProper t := by
  rw [TProper, ← dilate_dilate t s Q] at h
  exact (Q.dilate t).proper_of_dilate_proper hs h

/-- The dyadic specialization used by Nguyen--Vu's first-failure recursion. -/
lemma tProper_of_tProper_two_pow_add (Q : GeneralizedAP)
    {i j : ℕ} (h : Q.TProper (2 ^ (i + j))) : Q.TProper (2 ^ i) := by
  rw [pow_add, Nat.mul_comm] at h
  exact Q.tProper_of_tProper_mul (Nat.pow_pos (by omega)) h

lemma proper_of_tProper (Q : GeneralizedAP) {t : ℕ}
    (ht : 0 < t) (h : Q.TProper t) : Q.Proper := by
  exact Q.proper_of_dilate_proper ht h

/-- If a dyadic dilation first loses properness, there is a last proper
dyadic stage.  This is the finite minimum used by Nguyen--Vu's rank recursion. -/
lemma exists_first_nonproper_two_pow (Q : GeneralizedAP)
    (hproper : Q.Proper) {s : ℕ} (hnot : ¬ Q.TProper (2 ^ s)) :
    ∃ i < s, Q.TProper (2 ^ i) ∧ ¬ Q.TProper (2 ^ (i + 1)) := by
  induction s with
  | zero =>
      exfalso
      apply hnot
      simpa using hproper
  | succ s ih =>
      by_cases hs : Q.TProper (2 ^ s)
      · exact ⟨s, Nat.lt_succ_self s, hs,
          by simpa [Nat.succ_eq_add_one] using hnot⟩
      · obtain ⟨i, his, hi, hinext⟩ := ih hs
        exact ⟨i, his.trans (Nat.lt_succ_self s), hi, hinext⟩

/-! ### Positive presentation

Nguyen--Vu normalize every progression of positive integers by reflecting the
coordinates with negative steps.  The following finite construction records
that normalization without changing either the carrier or properness. -/

def positiveForm (Q : GeneralizedAP) : GeneralizedAP where
  rank := Q.rank
  base := Q.base + ∑ i, if Q.step i < 0 then (Q.length i : ℤ) * Q.step i else 0
  step := fun i => |Q.step i|
  length := Q.length

@[simp] lemma rank_positiveForm (Q : GeneralizedAP) :
    Q.positiveForm.rank = Q.rank := rfl

@[simp] lemma length_positiveForm (Q : GeneralizedAP) (i : Fin Q.rank) :
    Q.positiveForm.length i = Q.length i := rfl

@[simp] lemma step_positiveForm_nonneg (Q : GeneralizedAP)
    (i : Fin Q.rank) : 0 ≤ Q.positiveForm.step i := by
  exact abs_nonneg _

def reflectParam (Q : GeneralizedAP) (x : Q.Param) :
    Q.positiveForm.Param := fun i =>
  if _hi : Q.step i < 0 then
    ⟨Q.length i - (x i : ℕ), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else
    ⟨x i, (x i).isLt⟩

def unreflectParam (Q : GeneralizedAP) (x : Q.positiveForm.Param) :
    Q.Param := fun i =>
  if _hi : Q.step i < 0 then
    ⟨Q.length i - (x i : ℕ), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else
    ⟨x i, by simpa only [length_positiveForm] using (x i).isLt⟩

@[simp] lemma reflectParam_apply_of_neg (Q : GeneralizedAP)
    (x : Q.Param) (i : Fin Q.rank) (hi : Q.step i < 0) :
    (Q.reflectParam x i : ℕ) = Q.length i - (x i : ℕ) := by
  simp [reflectParam, hi]

@[simp] lemma reflectParam_apply_of_nonneg (Q : GeneralizedAP)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 ≤ Q.step i) :
    (Q.reflectParam x i : ℕ) = (x i : ℕ) := by
  simp [reflectParam, not_lt.mpr hi]

lemma reflectParam_leftInverse (Q : GeneralizedAP) :
    Function.LeftInverse Q.unreflectParam Q.reflectParam := by
  intro x
  funext i
  apply Fin.ext
  by_cases hi : Q.step i < 0
  · simp [reflectParam, unreflectParam, hi,
      Nat.sub_sub_self (Nat.le_of_lt_succ (x i).isLt)]
  · simp [reflectParam, unreflectParam, hi]

lemma unreflectParam_leftInverse (Q : GeneralizedAP) :
    Function.LeftInverse Q.reflectParam Q.unreflectParam := by
  intro x
  funext i
  apply Fin.ext
  by_cases hi : Q.step i < 0
  · simp only [reflectParam, unreflectParam, hi, dite_true]
    have hxi := (x i).isLt
    change (x i : ℕ) < Q.length i + 1 at hxi
    exact Nat.sub_sub_self (Nat.le_of_lt_succ hxi)
  · simp [reflectParam, unreflectParam, hi]

lemma reflectParam_bijective (Q : GeneralizedAP) :
    Function.Bijective Q.reflectParam :=
  ⟨Q.reflectParam_leftInverse.injective,
    Q.unreflectParam_leftInverse.surjective⟩

lemma unreflectParam_bijective (Q : GeneralizedAP) :
    Function.Bijective Q.unreflectParam :=
  ⟨Q.unreflectParam_leftInverse.injective,
    Q.reflectParam_leftInverse.surjective⟩

lemma eval_positiveForm_reflectParam (Q : GeneralizedAP)
    (x : Q.Param) : Q.positiveForm.eval (Q.reflectParam x) = Q.eval x := by
  simp only [eval, positiveForm]
  change (Q.base + ∑ i : Fin Q.rank,
      if Q.step i < 0 then (Q.length i : ℤ) * Q.step i else 0) +
      ∑ i : Fin Q.rank, ((Q.reflectParam x i : ℕ) : ℤ) * |Q.step i| =
    Q.base + ∑ i : Fin Q.rank, ((x i : ℕ) : ℤ) * Q.step i
  rw [add_assoc]
  apply congrArg (Q.base + ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : Q.step i < 0
  · rw [if_pos hi, abs_of_neg hi]
    simp only [reflectParam_apply_of_neg Q x i hi]
    have hxi : (x i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (x i).isLt
    have hcast : (((Q.length i - (x i : ℕ) : ℕ) : ℤ)) =
        (Q.length i : ℤ) - (x i : ℤ) := by omega
    rw [hcast]
    ring
  · have hi' : 0 ≤ Q.step i := not_lt.mp hi
    rw [if_neg hi, abs_of_nonneg hi']
    simp only [reflectParam_apply_of_nonneg Q x i hi']
    ring

lemma eval_positiveForm_eq_eval_unreflectParam (Q : GeneralizedAP)
    (x : Q.positiveForm.Param) :
    Q.positiveForm.eval x = Q.eval (Q.unreflectParam x) := by
  rw [← Q.eval_positiveForm_reflectParam (Q.unreflectParam x)]
  rw [Q.unreflectParam_leftInverse x]

lemma carrier_positiveForm (Q : GeneralizedAP) :
    Q.positiveForm.carrier = Q.carrier := by
  ext z
  rw [mem_carrier_iff, mem_carrier_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Q.unreflectParam y,
      (Q.eval_positiveForm_eq_eval_unreflectParam y).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Q.reflectParam x, Q.eval_positiveForm_reflectParam x⟩

lemma proper_positiveForm_iff (Q : GeneralizedAP) :
    Q.positiveForm.Proper ↔ Q.Proper := by
  constructor
  · intro h x y hxy
    apply Q.reflectParam_bijective.1
    apply h
    simpa only [Q.eval_positiveForm_reflectParam] using hxy
  · intro h x y hxy
    apply Q.unreflectParam_bijective.1
    apply h
    simpa only [Q.eval_positiveForm_eq_eval_unreflectParam] using hxy

lemma step_ne_zero_of_proper_length_pos (Q : GeneralizedAP)
    (hproper : Q.Proper) {i : Fin Q.rank} (hlen : 0 < Q.length i) :
    Q.step i ≠ 0 := by
  intro hstep
  let x : Q.Param := fun _ => 0
  let y : Q.Param := fun j =>
    if hji : j = i then
      ⟨1, by subst j; omega⟩
    else 0
  have heval : Q.eval x = Q.eval y := by
    simp only [eval, x, y]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [hstep]
    · simp [hji]
  have hxy := hproper heval
  have hi := congrFun hxy i
  have hval := congrArg Fin.val hi
  have hxval : (x i).val = 0 := rfl
  have hyval : (y i).val = 1 := by simp [y]
  omega

lemma step_positiveForm_pos_of_proper (Q : GeneralizedAP)
    (hproper : Q.Proper) (hpos : ∀ i, 0 < Q.length i)
    (i : Fin Q.rank) : 0 < Q.positiveForm.step i := by
  change 0 < |Q.step i|
  exact abs_pos.mpr (Q.step_ne_zero_of_proper_length_pos hproper (hpos i))

/-- The rank-zero/rank-one base of Nguyen--Vu's proper-embedding theorem:
a proper GAP of rank at most one remains proper under every dilation. -/
lemma proper_dilate_of_rank_le_one (Q : GeneralizedAP)
    (hproper : Q.Proper) (hrank : Q.rank ≤ 1) (t : ℕ) :
    (Q.dilate t).Proper := by
  intro x y hxy
  obtain hrank0 | hrankpos := Q.rank.eq_zero_or_pos
  · funext i
    exact Fin.elim0 (hrank0 ▸ i)
  · have hrank1 : Q.rank = 1 := by omega
    let i0 : Fin Q.rank := ⟨0, hrankpos⟩
    by_cases hlen : Q.length i0 = 0
    · funext i
      apply Fin.ext
      have hi : i = i0 := by
        apply Fin.ext
        have hilt := i.isLt
        change i.val < Q.rank at hilt
        have : i.val = 0 := by omega
        simpa [i0] using this
      subst i
      have hx := (x i0).isLt
      have hy := (y i0).isLt
      dsimp [dilate] at hx hy
      simp only [hlen, mul_zero] at hx hy
      omega
    · have hlenpos : 0 < Q.length i0 := Nat.pos_of_ne_zero hlen
      have hstep : Q.step i0 ≠ 0 :=
        Q.step_ne_zero_of_proper_length_pos hproper hlenpos
      have hcoeff : ((x i0 : ℕ) : ℤ) = ((y i0 : ℕ) : ℤ) := by
        simp only [eval, dilate] at hxy
        have hall : ∀ j : Fin Q.rank, j = i0 := by
          intro j
          apply Fin.ext
          have hjlt := j.isLt
          have : j.val = 0 := by omega
          simpa [i0] using this
        have hsumX : (∑ j : Fin Q.rank,
            ((x j : ℕ) : ℤ) * Q.step j) =
            ((x i0 : ℕ) : ℤ) * Q.step i0 := by
          calc
            _ = ∑ _j : Fin Q.rank,
                ((x i0 : ℕ) : ℤ) * Q.step i0 := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  rw [hall j]
            _ = _ := by simp [hrank1]
        have hsumY : (∑ j : Fin Q.rank,
            ((y j : ℕ) : ℤ) * Q.step j) =
            ((y i0 : ℕ) : ℤ) * Q.step i0 := by
          calc
            _ = ∑ _j : Fin Q.rank,
                ((y i0 : ℕ) : ℤ) * Q.step i0 := by
                  apply Finset.sum_congr rfl
                  intro j _hj
                  rw [hall j]
            _ = _ := by simp [hrank1]
        have hsum :
            ((x i0 : ℕ) : ℤ) * Q.step i0 =
              ((y i0 : ℕ) : ℤ) * Q.step i0 := by
          have hsums := add_left_cancel hxy
          change (∑ j : Fin Q.rank,
              ((x j : ℕ) : ℤ) * Q.step j) =
            ∑ j : Fin Q.rank, ((y j : ℕ) : ℤ) * Q.step j at hsums
          rw [hsumX, hsumY] at hsums
          exact hsums
        exact mul_right_cancel₀ hstep hsum
      funext i
      apply Fin.ext
      have hi : i = i0 := by
        apply Fin.ext
        have hilt := i.isLt
        change i.val < Q.rank at hilt
        have : i.val = 0 := by omega
        simpa [i0] using this
      subst i
      exact_mod_cast hcoeff

lemma tProper_of_proper_rank_le_one (Q : GeneralizedAP)
    (hproper : Q.Proper) (hrank : Q.rank ≤ 1) (t : ℕ) :
    Q.TProper t :=
  Q.proper_dilate_of_rank_le_one hproper hrank t

/-- The rank-zero GAP supported on one integer. -/
def singletonAP (z : ℤ) : GeneralizedAP where
  rank := 0
  base := z
  step := Fin.elim0
  length := Fin.elim0

@[simp] lemma rank_singletonAP (z : ℤ) : (singletonAP z).rank = 0 := rfl

@[simp] lemma eval_singletonAP (z : ℤ) (x : (singletonAP z).Param) :
    (singletonAP z).eval x = z := by
  have hsum :
      (∑ i : Fin 0, ((x i : ℕ) : ℤ) * Fin.elim0 i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact Fin.elim0 i
  change z + (∑ i : Fin 0, ((x i : ℕ) : ℤ) * Fin.elim0 i) = z
  rw [hsum, add_zero]

@[simp] lemma carrier_singletonAP (z : ℤ) :
    (singletonAP z).carrier = {z} := by
  ext w
  simp [mem_carrier_iff, eq_comm]

lemma proper_singletonAP (z : ℤ) : (singletonAP z).Proper := by
  intro x y _hxy
  funext i
  exact Fin.elim0 i

lemma tProper_singletonAP (z : ℤ) (t : ℕ) :
    (singletonAP z).TProper t := by
  exact (singletonAP z).tProper_of_proper_rank_le_one
    (proper_singletonAP z) (by simp) t

lemma proper_of_rank_eq_zero (Q : GeneralizedAP)
    (hrank : Q.rank = 0) : Q.Proper := by
  intro x y _hxy
  funext i
  exact Fin.elim0 (hrank ▸ i)

lemma proper_of_rank_eq_one_step_ne_zero (Q : GeneralizedAP)
    (hrank : Q.rank = 1)
    (hstep : Q.step ⟨0, by omega⟩ ≠ 0) : Q.Proper := by
  let i0 : Fin Q.rank := ⟨0, by omega⟩
  have hall : ∀ j : Fin Q.rank, j = i0 := by
    intro j
    apply Fin.ext
    have hjlt := j.isLt
    have : j.val = 0 := by omega
    simpa [i0] using this
  intro x y hxy
  have hsum : (∑ j : Fin Q.rank, ((x j : ℕ) : ℤ) * Q.step j) =
      ∑ j : Fin Q.rank, ((y j : ℕ) : ℤ) * Q.step j := by
    exact add_left_cancel hxy
  have hsumX : (∑ j : Fin Q.rank,
      ((x j : ℕ) : ℤ) * Q.step j) =
      ((x i0 : ℕ) : ℤ) * Q.step i0 := by
    calc
      _ = ∑ _j : Fin Q.rank,
          ((x i0 : ℕ) : ℤ) * Q.step i0 := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hall j]
      _ = _ := by simp [hrank]
  have hsumY : (∑ j : Fin Q.rank,
      ((y j : ℕ) : ℤ) * Q.step j) =
      ((y i0 : ℕ) : ℤ) * Q.step i0 := by
    calc
      _ = ∑ _j : Fin Q.rank,
          ((y i0 : ℕ) : ℤ) * Q.step i0 := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hall j]
      _ = _ := by simp [hrank]
  rw [hsumX, hsumY] at hsum
  have hstep0 : Q.step i0 ≠ 0 := by
    simpa only [i0] using hstep
  have hcoeff : ((x i0 : ℕ) : ℤ) = ((y i0 : ℕ) : ℤ) :=
    mul_right_cancel₀ hstep0 hsum
  funext i
  apply Fin.ext
  rw [hall i]
  exact_mod_cast hcoeff

lemma carrier_eq_singleton_of_rank_eq_one_step_zero
    (Q : GeneralizedAP) (hrank : Q.rank = 1)
    (hstep : Q.step ⟨0, by omega⟩ = 0) : Q.carrier = {Q.base} := by
  let i0 : Fin Q.rank := ⟨0, by omega⟩
  have hall : ∀ j : Fin Q.rank, j = i0 := by
    intro j
    apply Fin.ext
    have hjlt := j.isLt
    have : j.val = 0 := by omega
    simpa [i0] using this
  have hzero : ∀ j : Fin Q.rank, Q.step j = 0 := by
    intro j
    rw [hall j]
    simpa only [i0] using hstep
  ext z
  rw [mem_carrier_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    simp [eval, hzero]
  · intro hz
    subst z
    exact ⟨fun _ => 0, by simp [eval, hzero]⟩

/-- The exact output contract of Nguyen--Vu's proper-embedding lemma. -/
def IsTProperEmbedding (t : ℕ) (Q Q₀ : GeneralizedAP) : Prop :=
  Q.carrier ⊆ Q₀.carrier ∧
    Q₀.TProper t ∧
    Q₀.rank ≤ Q.rank ∧
    Q₀.carrier.card ≤
      (2 * t) ^ Q.rank * Q.rank ^ (6 * Q.rank ^ 2) * Q.carrier.card ∧
    (¬ Q.Proper → Q₀.rank < Q.rank)

/-- Nguyen--Vu Lemma 3.3 in ranks zero and one. -/
lemma exists_tProperEmbedding_of_rank_le_one (Q : GeneralizedAP)
    (t : ℕ) (ht : 0 < t) (hrank : Q.rank ≤ 1) :
    ∃ Q₀ : GeneralizedAP, IsTProperEmbedding t Q Q₀ := by
  by_cases hproper : Q.Proper
  · refine ⟨Q, ?_⟩
    refine ⟨Finset.Subset.rfl, Q.tProper_of_proper_rank_le_one hproper hrank t,
      le_rfl, ?_, ?_⟩
    · obtain hrank0 | hrankpos := Q.rank.eq_zero_or_pos
      · simp [hrank0]
      · have hrank1 : Q.rank = 1 := by omega
        have hfactor : 1 ≤ 2 * t := by omega
        simpa [hrank1] using Nat.mul_le_mul_right Q.carrier.card hfactor
    · exact fun hnot => (hnot hproper).elim
  · have hrank1 : Q.rank = 1 := by
      obtain hrank0 | hrankpos := Q.rank.eq_zero_or_pos
      · exact (hproper (Q.proper_of_rank_eq_zero hrank0)).elim
      · omega
    let i0 : Fin Q.rank := ⟨0, by omega⟩
    have hstep : Q.step i0 = 0 := by
      by_contra hne
      apply hproper
      apply Q.proper_of_rank_eq_one_step_ne_zero hrank1
      simpa only [i0] using hne
    have hcarrier : Q.carrier = {Q.base} := by
      apply Q.carrier_eq_singleton_of_rank_eq_one_step_zero hrank1
      simpa only [i0] using hstep
    refine ⟨singletonAP Q.base, ?_⟩
    refine ⟨?_, tProper_singletonAP Q.base t, ?_, ?_, ?_⟩
    · rw [hcarrier, carrier_singletonAP]
    · simp [hrank1]
    · simp [hcarrier, hrank1]
      omega
    · intro _hnot
      simp [hrank1]

lemma eval_eq_base_add_linearEval (Q : GeneralizedAP) (x : Q.Param) :
    Q.eval x = Q.base + Q.linearEval (fun i => (x i : ℤ)) := by
  rfl

lemma eval_dilate (n : ℕ) (Q : GeneralizedAP)
    (x : (Q.dilate n).Param) :
    (Q.dilate n).eval x =
      (n : ℤ) * Q.base + Q.linearEval (fun i => (x i : ℤ)) := by
  rfl

@[simp] lemma carrier_dilate_zero (Q : GeneralizedAP) :
    (Q.dilate 0).carrier = {0} := by
  ext z
  rw [mem_carrier_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨x, rfl⟩
    simp only [eval, dilate, Nat.cast_zero, zero_mul]
    have hx0 : ∀ i, (x i : ℤ) = 0 := by
      intro i
      have := (x i).isLt
      dsimp [dilate] at this
      omega
    simp only [zero_add]
    apply Finset.sum_eq_zero
    intro i _
    rw [hx0 i, zero_mul]
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    let x : (Q.dilate 0).Param := fun _ => 0
    refine ⟨x, ?_⟩
    simp [eval, dilate, x]

lemma carrier_dilate_succ (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate (n + 1)).carrier =
      (Q.dilate n).carrier + Q.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (mem_carrier_iff _).mp hz
    let x : (Q.dilate n).Param := fun i =>
      ⟨min (w i : ℕ) (n * Q.length i), by
        exact Nat.lt_succ_of_le (min_le_right _ _)⟩
    let y : Q.Param := fun i =>
      ⟨(w i : ℕ) - min (w i : ℕ) (n * Q.length i), by
        have hwlt : (w i : ℕ) < (n + 1) * Q.length i + 1 := (w i).isLt
        change (w i : ℕ) - min (w i : ℕ) (n * Q.length i) < Q.length i + 1
        simp only [Nat.add_mul] at hwlt
        omega⟩
    apply Finset.mem_add.mpr
    refine ⟨(Q.dilate n).eval x, (mem_carrier_iff _).mpr ⟨x, rfl⟩,
      Q.eval y, (mem_carrier_iff _).mpr ⟨y, rfl⟩, ?_⟩
    rw [← hw]
    have hsum : Q.linearEval (fun i => (w i : ℤ)) =
        Q.linearEval (fun i => (x i : ℤ)) +
          Q.linearEval (fun i => (y i : ℤ)) := by
      simp only [linearEval]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hxle : (x i : ℕ) ≤ (w i : ℕ) := by
        dsimp [x]
        exact min_le_left _ _
      have hxy : (x i : ℕ) + (y i : ℕ) = (w i : ℕ) := by
        have hxval : (x i : ℕ) = min (w i : ℕ) (n * Q.length i) := rfl
        have hyval : (y i : ℕ) =
            (w i : ℕ) - min (w i : ℕ) (n * Q.length i) := rfl
        rw [hxval, hyval]
        exact Nat.add_sub_of_le (min_le_left _ _)
      change ((w i : ℕ) : ℤ) * Q.step i =
        ((x i : ℕ) : ℤ) * Q.step i + ((y i : ℕ) : ℤ) * Q.step i
      have hxy' : ((x i : ℕ) : ℤ) + ((y i : ℕ) : ℤ) = (w i : ℕ) := by
        exact_mod_cast hxy
      rw [← hxy']
      ring
    rw [eval_dilate, eval_dilate, eval_eq_base_add_linearEval]
    push_cast
    rw [hsum]
    ring
  · intro hz
    rw [Finset.mem_add] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨x, hxa⟩ := (mem_carrier_iff _).mp ha
    obtain ⟨y, hyb⟩ := (mem_carrier_iff _).mp hb
    subst a
    subst b
    let w : (Q.dilate (n + 1)).Param := fun i =>
      ⟨(x i : ℕ) + (y i : ℕ), by
        have hxlt : (x i : ℕ) < n * Q.length i + 1 := (x i).isLt
        have hylt : (y i : ℕ) < Q.length i + 1 := (y i).isLt
        change (x i : ℕ) + (y i : ℕ) < (n + 1) * Q.length i + 1
        simp only [Nat.add_mul]
        omega⟩
    apply (mem_carrier_iff _).mpr
    refine ⟨w, ?_⟩
    have hsum : Q.linearEval (fun i => (w i : ℤ)) =
        Q.linearEval (fun i => (x i : ℤ)) +
          Q.linearEval (fun i => (y i : ℤ)) := by
      simp only [linearEval]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (((x i : ℕ) + (y i : ℕ) : ℕ) : ℤ) * Q.step i =
        ((x i : ℕ) : ℤ) * Q.step i + ((y i : ℕ) : ℤ) * Q.step i
      push_cast
      ring
    rw [eval_dilate, eval_dilate, eval_eq_base_add_linearEval]
    push_cast
    rw [hsum]
    ring

/-- The paper dilation has exactly the expected pointwise-sum carrier. -/
lemma nsmul_carrier (n : ℕ) (Q : GeneralizedAP) :
    n • Q.carrier = (Q.dilate n).carrier := by
  induction n with
  | zero =>
      rw [zero_nsmul, carrier_dilate_zero]
      rfl
  | succ n ih =>
      rw [succ_nsmul, ih]
      exact (carrier_dilate_succ n Q).symm

/-- Non-properness supplies the bounded nonzero vanishing vector used by the
rank-reduction step of Szemerédi--Vu. -/
lemma exists_bounded_nonzero_vanishingVector_of_not_proper
    (Q : GeneralizedAP) (hQ : ¬ Q.Proper) :
    ∃ v : Fin Q.rank → ℤ,
      Q.Vanishes v ∧
      (∃ i, v i ≠ 0) ∧
      ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i := by
  rw [Proper, Function.Injective] at hQ
  push_neg at hQ
  obtain ⟨x, y, heval, hxy⟩ := hQ
  let v : Fin Q.rank → ℤ := fun i => (x i : ℤ) - (y i : ℤ)
  refine ⟨v, (eval_eq_iff_linearEval_sub_eq_zero Q x y).mp heval, ?_, ?_⟩
  · by_contra hzero
    push_neg at hzero
    apply hxy
    funext i
    have hcast : (x i : ℤ) = (y i : ℤ) := sub_eq_zero.mp (hzero i)
    apply Fin.ext
    exact_mod_cast hcast
  · intro i
    have hx : (x i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (x i).isLt
    have hy : (y i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (y i).isLt
    dsimp [v]
    constructor <;> omega

/-- Integer coefficient vectors for a GAP presentation. -/
abbrev CoeffVec (Q : GeneralizedAP) := Fin Q.rank → ℤ

/-- A finite integer vector is primitive when its coordinates have a Bézout
combination equal to one.  This certificate is the exact input needed to
complete the vector to an integral basis in Nguyen--Vu's rank reduction. -/
def PrimitiveIntVector {ι : Type*} [Fintype ι] (v : ι → ℤ) : Prop :=
  ∃ a : ι → ℤ, ∑ i, v i * a i = 1

/-- Divide a nonzero finite integer vector by the gcd of its coordinates.
The result is primitive, is no larger coordinatewise, and the original vector
is a nonzero scalar multiple of it. -/
lemma exists_primitiveIntVector_factorization
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℤ)
    (hv : ∃ i, v i ≠ 0) :
    ∃ c : ℤ, ∃ u : ι → ℤ,
      c ≠ 0 ∧
      (∀ i, v i = c * u i) ∧
      PrimitiveIntVector u ∧
      ∀ i, |u i| ≤ |v i| := by
  let c : ℤ := Finset.univ.gcd v
  have hc : c ≠ 0 := by
    intro hc0
    rw [Finset.gcd_eq_zero_iff] at hc0
    obtain ⟨i, hi⟩ := hv
    exact hi (hc0 i (Finset.mem_univ i))
  let u : ι → ℤ := fun i => v i / c
  have hdiv (i : ι) : c ∣ v i :=
    Finset.gcd_dvd (Finset.mem_univ i)
  have hfactor (i : ι) : v i = c * u i := by
    rw [mul_comm]
    exact (Int.ediv_mul_cancel (hdiv i)).symm
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) v
  have hsum : ∑ i, u i * a i = 1 := by
    apply mul_left_cancel₀ hc
    calc
      c * (∑ i, u i * a i) = ∑ i, (c * u i) * a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = ∑ i, v i * a i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hfactor]
      _ = c := ha.symm
      _ = c * 1 := by ring
  refine ⟨c, u, hc, hfactor, ⟨a, hsum⟩, ?_⟩
  intro i
  rw [hfactor i, abs_mul]
  have hcabs : 1 ≤ |c| := Int.one_le_abs hc
  calc
    |u i| = |u i| * 1 := by ring
    _ ≤ |u i| * |c| := by
      exact Int.mul_le_mul_of_nonneg_left hcabs (abs_nonneg _)
    _ = |c| * |u i| := by ring

/-- Failure of `t`-properness gives a nonzero relation whose coordinates lie
in the `t`-dilated difference box. -/
lemma exists_bounded_nonzero_vanishingVector_of_not_tProper
    (Q : GeneralizedAP) {t : ℕ} (hQ : ¬ Q.TProper t) :
    ∃ v : Q.CoeffVec,
      Q.Vanishes v ∧
      (∃ i, v i ≠ 0) ∧
      ∀ i, |v i| ≤ (t : ℤ) * Q.length i := by
  obtain ⟨v, hvVanish, hvNonzero, hvBound⟩ :=
    exists_bounded_nonzero_vanishingVector_of_not_proper (Q.dilate t) hQ
  refine ⟨v, ?_, hvNonzero, ?_⟩
  · exact hvVanish
  · intro i
    rw [abs_le]
    simpa [dilate, Nat.cast_mul] using hvBound i

/-- Primitive normalization of the relation supplied by failed
`t`-properness.  It retains both vanishing and the same coordinate bounds. -/
lemma exists_bounded_primitive_vanishingVector_of_not_tProper
    (Q : GeneralizedAP) {t : ℕ} (hQ : ¬ Q.TProper t) :
    ∃ u : Q.CoeffVec,
      Q.Vanishes u ∧
      PrimitiveIntVector u ∧
      (∃ i, u i ≠ 0) ∧
      ∀ i, |u i| ≤ (t : ℤ) * Q.length i := by
  obtain ⟨v, hvVanish, hvNonzero, hvBound⟩ :=
    Q.exists_bounded_nonzero_vanishingVector_of_not_tProper hQ
  obtain ⟨c, u, hc, hfactor, huPrimitive, huBound⟩ :=
    exists_primitiveIntVector_factorization v hvNonzero
  have huVanish : Q.Vanishes u := by
    have hlinear : Q.linearEval v = c * Q.linearEval u := by
      rw [linearEval, linearEval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hfactor i]
      ring
    rw [Vanishes, hlinear] at hvVanish
    exact (mul_eq_zero.mp hvVanish).resolve_left hc
  have huNonzero : ∃ i, u i ≠ 0 := by
    obtain ⟨a, ha⟩ := huPrimitive
    by_contra hzero
    push_neg at hzero
    simp [hzero] at ha
  refine ⟨u, huVanish, huPrimitive, huNonzero, ?_⟩
  intro i
  exact (huBound i).trans (hvBound i)

def paramVec (Q : GeneralizedAP) (n : ℕ) :
    (Q.dilate n).Param → Q.CoeffVec :=
  fun x i => (x i : ℤ)

lemma paramVec_injective (Q : GeneralizedAP) (n : ℕ) :
    Function.Injective (Q.paramVec n) := by
  intro x y hxy
  funext i
  apply Fin.ext
  have hi := congrFun hxy i
  change ((x i : ℕ) : ℤ) = ((y i : ℕ) : ℤ) at hi
  exact_mod_cast hi

def intBox (Q : GeneralizedAP) (n : ℕ) : Finset Q.CoeffVec :=
  (Finset.univ : Finset (Q.dilate n).Param).image (Q.paramVec n)

lemma card_intBox (Q : GeneralizedAP) (n : ℕ) :
    (Q.intBox n).card = (Q.dilate n).boxCard := by
  rw [intBox, Finset.card_image_of_injective _ (paramVec_injective Q n),
    Finset.card_univ]
  change Fintype.card ((i : Fin Q.rank) → Fin (n * Q.length i + 1)) =
    ∏ i : Fin Q.rank, (n * Q.length i + 1)
  simp

def affineEval (Q : GeneralizedAP) (n : ℕ) (w : Q.CoeffVec) : ℤ :=
  (n : ℤ) * Q.base + Q.linearEval w

lemma image_affineEval_intBox (Q : GeneralizedAP) (n : ℕ) :
    (Q.intBox n).image (Q.affineEval n) = (Q.dilate n).carrier := by
  rw [intBox, Finset.image_image, carrier]
  congr 1

def sourceVec (Q : GeneralizedAP) (v : Q.CoeffVec) (x : Q.Param) :
    Q.CoeffVec := fun i =>
  if 0 ≤ v i then (x i : ℤ) else (Q.length i : ℤ) + (x i : ℤ)

lemma sourceVec_injective (Q : GeneralizedAP) (v : Q.CoeffVec) :
    Function.Injective (Q.sourceVec v) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  dsimp [sourceVec] at hi
  split at hi
  · apply Fin.ext
    exact_mod_cast hi
  · have hi' : (x i : ℤ) = (y i : ℤ) := add_left_cancel hi
    apply Fin.ext
    exact_mod_cast hi'

def collisionSource (Q : GeneralizedAP) (v : Q.CoeffVec) : Finset Q.CoeffVec :=
  (Finset.univ : Finset Q.Param).image (Q.sourceVec v)

lemma card_collisionSource (Q : GeneralizedAP) (v : Q.CoeffVec) :
    (Q.collisionSource v).card = Q.boxCard := by
  rw [collisionSource, Finset.card_image_of_injective _ (sourceVec_injective Q v),
    Finset.card_univ]
  simp [boxCard, Param]

def translateVec (Q : GeneralizedAP) (v w : Q.CoeffVec) : Q.CoeffVec :=
  fun i => w i + v i

lemma translateVec_injective (Q : GeneralizedAP) (v : Q.CoeffVec) :
    Function.Injective (Q.translateVec v) := by
  intro x y hxy
  funext i
  have hi := congrFun hxy i
  dsimp [translateVec] at hi
  exact add_right_cancel hi

lemma translateVec_ne_self_of_nonzero (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∃ i, v i ≠ 0) (w : Q.CoeffVec) : Q.translateVec v w ≠ w := by
  obtain ⟨i, hi⟩ := hv
  intro h
  have h' := congrFun h i
  dsimp [translateVec] at h'
  apply hi
  linarith

lemma affineEval_translateVec_of_vanishes (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : Q.Vanishes v) (n : ℕ) (w : Q.CoeffVec) :
    Q.affineEval n (Q.translateVec v w) = Q.affineEval n w := by
  simp only [affineEval, linearEval, translateVec, Vanishes] at hv ⊢
  have hsum : (∑ i, (w i + v i) * Q.step i) =
      (∑ i, w i * Q.step i) + ∑ i, v i * Q.step i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, hv]
  ring

lemma sourceVec_and_translate_bounds (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i)
    (x : Q.Param) (i : Fin Q.rank) :
    0 ≤ Q.sourceVec v x i ∧
    Q.sourceVec v x i ≤ 2 * Q.length i ∧
    0 ≤ Q.translateVec v (Q.sourceVec v x) i ∧
    Q.translateVec v (Q.sourceVec v x) i ≤ 2 * Q.length i := by
  have hxNat : (x i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (x i).isLt
  have hx : (0 : ℤ) ≤ (x i : ℤ) ∧ (x i : ℤ) ≤ Q.length i := by
    constructor
    · positivity
    · exact_mod_cast hxNat
  obtain ⟨hvlow, hvhigh⟩ := hv i
  by_cases hvi : 0 ≤ v i
  · simp only [sourceVec, hvi, if_pos, translateVec]
    exact ⟨hx.1, by linarith, by linarith, by linarith⟩
  · have hvneg : v i < 0 := lt_of_not_ge hvi
    simp only [sourceVec, hvi, if_false, translateVec]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma sourceVec_mem_intBox_two (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i)
    (x : Q.Param) : Q.sourceVec v x ∈ Q.intBox 2 := by
  let p : (Q.dilate 2).Param := fun i =>
    ⟨(Q.sourceVec v x i).toNat, by
      have hb := (sourceVec_and_translate_bounds Q hv x i).1
      apply (Int.toNat_lt hb).mpr
      have hu := (sourceVec_and_translate_bounds Q hv x i).2.1
      change Q.sourceVec v x i < (2 : ℤ) * Q.length i + 1
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_univ _, ?_⟩
  funext i
  dsimp [paramVec, p]
  exact Int.toNat_of_nonneg (sourceVec_and_translate_bounds Q hv x i).1

lemma translate_sourceVec_mem_intBox_two (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i)
    (x : Q.Param) :
    Q.translateVec v (Q.sourceVec v x) ∈ Q.intBox 2 := by
  let p : (Q.dilate 2).Param := fun i =>
    ⟨(Q.translateVec v (Q.sourceVec v x) i).toNat, by
      have hb := (sourceVec_and_translate_bounds Q hv x i).2.2.1
      apply (Int.toNat_lt hb).mpr
      have hu := (sourceVec_and_translate_bounds Q hv x i).2.2.2
      change Q.translateVec v (Q.sourceVec v x) i <
        (2 : ℤ) * Q.length i + 1
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_univ _, ?_⟩
  funext i
  dsimp [paramVec, p]
  exact Int.toNat_of_nonneg
    (sourceVec_and_translate_bounds Q hv x i).2.2.1

lemma collisionSource_subset_intBox_two (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i) :
    Q.collisionSource v ⊆ Q.intBox 2 := by
  intro w hw
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hw
  exact sourceVec_mem_intBox_two Q hv x

lemma image_translate_collisionSource_subset_intBox_two
    (Q : GeneralizedAP) {v : Q.CoeffVec}
    (hv : ∀ i, -(Q.length i : ℤ) ≤ v i ∧ v i ≤ Q.length i) :
    (Q.collisionSource v).image (Q.translateVec v) ⊆ Q.intBox 2 := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hu
  exact translate_sourceVec_mem_intBox_two Q hv x

/-- A concrete cardinal deficit for a doubled non-proper GAP.  This is the
finite collision-counting core of Szemerédi--Vu Lemma 4.2; the factor `3` is
an inessential weakening of their factor `2`. -/
lemma three_mul_card_carrier_dilate_two_add_boxCard_le_of_not_proper
    (Q : GeneralizedAP) (hQ : ¬ Q.Proper) :
    3 * (Q.dilate 2).carrier.card + Q.boxCard ≤
      3 * (Q.dilate 2).boxCard := by
  obtain ⟨v, hvVanish, hvNonzero, hvBound⟩ :=
    exists_bounded_nonzero_vanishingVector_of_not_proper Q hQ
  have h := Erdos587.three_mul_card_image_add_card_le_of_translation_collisions
    (D := Q.intBox 2) (S := Q.collisionSource v)
    (f := Q.affineEval 2) (g := Q.translateVec v)
    (Q.translateVec_injective v)
    (Q.collisionSource_subset_intBox_two hvBound)
    (Q.image_translate_collisionSource_subset_intBox_two hvBound)
    (fun w _hw => Q.translateVec_ne_self_of_nonzero hvNonzero w)
    (fun w _hw => Q.affineEval_translateVec_of_vanishes hvVanish 2 w)
  rw [Q.image_affineEval_intBox, Q.card_collisionSource, Q.card_intBox] at h
  exact h

/-- Doubling each side of a coefficient box increases its cardinality by at
most `2^rank`.  This converts the collision count above into a deficit whose
constant depends only on the rank. -/
lemma boxCard_dilate_two_le_pow_mul_boxCard (Q : GeneralizedAP) :
    (Q.dilate 2).boxCard ≤ 2 ^ Q.rank * Q.boxCard := by
  rw [boxCard_dilate, boxCard]
  calc
    ∏ i : Fin Q.rank, (2 * Q.length i + 1) ≤
        ∏ i : Fin Q.rank, 2 * (Q.length i + 1) := by
      apply Finset.prod_le_prod'
      intro i _hi
      omega
    _ = 2 ^ Q.rank * ∏ i : Fin Q.rank, (Q.length i + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Fixed-rank form of the non-properness deficit.  In paper notation it says
that a non-proper rank-`d` progression misses at least a
`1 / (3 * 2^d)` fraction of its doubled coefficient box.  The division-free
form is better suited to the subsequent finite recursion. -/
lemma fixed_rank_deficit_of_not_proper (Q : GeneralizedAP)
    (hQ : ¬ Q.Proper) :
    3 * 2 ^ Q.rank * (Q.dilate 2).carrier.card +
        (Q.dilate 2).boxCard ≤
      3 * 2 ^ Q.rank * (Q.dilate 2).boxCard := by
  have hdef :=
    three_mul_card_carrier_dilate_two_add_boxCard_le_of_not_proper Q hQ
  have hbox := boxCard_dilate_two_le_pow_mul_boxCard Q
  calc
    3 * 2 ^ Q.rank * (Q.dilate 2).carrier.card +
          (Q.dilate 2).boxCard ≤
        3 * 2 ^ Q.rank * (Q.dilate 2).carrier.card +
          2 ^ Q.rank * Q.boxCard := Nat.add_le_add_left hbox _
    _ = 2 ^ Q.rank *
          (3 * (Q.dilate 2).carrier.card + Q.boxCard) := by ring
    _ ≤ 2 ^ Q.rank * (3 * (Q.dilate 2).boxCard) :=
      Nat.mul_le_mul_left _ hdef
    _ = 3 * 2 ^ Q.rank * (Q.dilate 2).boxCard := by ring

/-- Coordinatewise characterization of the finite integer coefficient box. -/
lemma mem_intBox_iff (Q : GeneralizedAP) {n : ℕ} {w : Q.CoeffVec} :
    w ∈ Q.intBox n ↔
      ∀ i, 0 ≤ w i ∧ w i ≤ (n : ℤ) * Q.length i := by
  constructor
  · intro hw i
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hw
    dsimp [paramVec]
    have hxlt := (x i).isLt
    dsimp [dilate] at hxlt
    constructor
    · positivity
    · exact_mod_cast (Nat.le_of_lt_succ hxlt)
  · intro hw
    let x : (Q.dilate n).Param := fun i ↦
      ⟨(w i).toNat, by
        apply (Int.toNat_lt (hw i).1).mpr
        have hwi := (hw i).2
        change w i < (n : ℤ) * Q.length i + 1
        omega⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    funext i
    dsimp [paramVec, x]
    exact Int.toNat_of_nonneg (hw i).1

/-- Coefficient boxes are monotone in the dilation parameter. -/
lemma intBox_mono (Q : GeneralizedAP) {m n : ℕ} (hmn : m ≤ n) :
    Q.intBox m ⊆ Q.intBox n := by
  intro w hw
  rw [mem_intBox_iff] at hw ⊢
  intro i
  refine ⟨(hw i).1, (hw i).2.trans ?_⟩
  exact Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (by positivity)

/-- Szemerédi--Vu's non-properness deficit for every dilation `g ≥ 2`.
The same bounded vanishing vector supplies a full copy of the original
coefficient box worth of collisions inside the `g`-fold coefficient box. -/
lemma three_mul_card_carrier_dilate_add_boxCard_le_of_not_proper
    (Q : GeneralizedAP) (hQ : ¬ Q.Proper) {g : ℕ} (hg : 2 ≤ g) :
    3 * (Q.dilate g).carrier.card + Q.boxCard ≤
      3 * (Q.dilate g).boxCard := by
  obtain ⟨v, hvVanish, hvNonzero, hvBound⟩ :=
    exists_bounded_nonzero_vanishingVector_of_not_proper Q hQ
  have hSource : Q.collisionSource v ⊆ Q.intBox g :=
    (Q.collisionSource_subset_intBox_two hvBound).trans (Q.intBox_mono hg)
  have hTarget :
      (Q.collisionSource v).image (Q.translateVec v) ⊆ Q.intBox g :=
    (Q.image_translate_collisionSource_subset_intBox_two hvBound).trans
      (Q.intBox_mono hg)
  have h := Erdos587.three_mul_card_image_add_card_le_of_translation_collisions
    (D := Q.intBox g) (S := Q.collisionSource v)
    (f := Q.affineEval g) (g := Q.translateVec v)
    (Q.translateVec_injective v) hSource hTarget
    (fun w _hw ↦ Q.translateVec_ne_self_of_nonzero hvNonzero w)
    (fun w _hw ↦ Q.affineEval_translateVec_of_vanishes hvVanish g w)
  rw [Q.image_affineEval_intBox, Q.card_collisionSource, Q.card_intBox] at h
  exact h

/-- A `g`-dilated coefficient box grows by at most `g^rank` when `g ≥ 1`. -/
lemma boxCard_dilate_le_pow_mul_boxCard (Q : GeneralizedAP)
    {g : ℕ} (hg : 1 ≤ g) :
    (Q.dilate g).boxCard ≤ g ^ Q.rank * Q.boxCard := by
  rw [boxCard_dilate, boxCard]
  calc
    ∏ i : Fin Q.rank, (g * Q.length i + 1) ≤
        ∏ i : Fin Q.rank, g * (Q.length i + 1) := by
      apply Finset.prod_le_prod'
      intro i _hi
      calc
        g * Q.length i + 1 ≤ g * Q.length i + g :=
          Nat.add_le_add_left hg _
        _ = g * (Q.length i + 1) := by ring
    _ = g ^ Q.rank * ∏ i : Fin Q.rank, (Q.length i + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Division-free fixed-rank deficit for the general `g`-fold dilation. -/
lemma fixed_rank_dilation_deficit_of_not_proper
    (Q : GeneralizedAP) (hQ : ¬ Q.Proper) {g : ℕ} (hg : 2 ≤ g) :
    3 * g ^ Q.rank * (Q.dilate g).carrier.card +
        (Q.dilate g).boxCard ≤
      3 * g ^ Q.rank * (Q.dilate g).boxCard := by
  have hdef :=
    three_mul_card_carrier_dilate_add_boxCard_le_of_not_proper Q hQ hg
  have hbox := boxCard_dilate_le_pow_mul_boxCard Q (by omega : 1 ≤ g)
  calc
    3 * g ^ Q.rank * (Q.dilate g).carrier.card +
          (Q.dilate g).boxCard ≤
        3 * g ^ Q.rank * (Q.dilate g).carrier.card +
          g ^ Q.rank * Q.boxCard := Nat.add_le_add_left hbox _
    _ = g ^ Q.rank *
          (3 * (Q.dilate g).carrier.card + Q.boxCard) := by ring
    _ ≤ g ^ Q.rank * (3 * (Q.dilate g).boxCard) :=
      Nat.mul_le_mul_left _ hdef
    _ = 3 * g ^ Q.rank * (Q.dilate g).boxCard := by ring

/-- Explicit numerical form of Szemerédi--Vu's doubling-drop argument.
If a proper nondegenerate rank-`r` GAP loses properness when doubled, then
one of the ratios `|2Q| / |Q|` or `|4Q| / |2Q|` is below `2^r` by the fixed
division-free gap displayed here.  This is the exact bridge from the
non-properness deficit to Bilu's bounded-doubling lemma. -/
lemma explicit_doubling_drop_of_not_proper_dilate_two
    (Q : GeneralizedAP) (hproper : Q.Proper)
    (hpos : ∀ i, 0 < Q.length i)
    (hnot : ¬ (Q.dilate 2).Proper) :
    let R := 2 ^ Q.rank
    let T := 12 * R
    T * (Q.dilate 2).carrier.card ≤
        (T * R - 1) * Q.carrier.card ∨
      T * (Q.dilate 4).carrier.card ≤
        (T * R - 1) * (Q.dilate 2).carrier.card := by
  let R := 2 ^ Q.rank
  let T := 12 * R
  have hR : 0 < R := by positivity
  have hcard : Q.carrier.card = Q.boxCard := Q.card_carrier_of_proper hproper
  have hdef := fixed_rank_deficit_of_not_proper (Q.dilate 2) hnot
  rw [dilate_dilate] at hdef
  norm_num at hdef
  have hlow : R * Q.carrier.card ≤ (Q.dilate 4).boxCard := by
    rw [hcard]
    exact Q.pow_two_mul_boxCard_le_boxCard_dilate_four hpos
  have hupper : (Q.dilate 4).boxCard ≤ R ^ 2 * Q.carrier.card := by
    rw [hcard]
    have h := Q.boxCard_dilate_le_pow_mul_boxCard (g := 4) (by omega)
    simpa only [R, show 4 ^ Q.rank = (2 ^ Q.rank) ^ 2 by
      rw [show 4 = 2 * 2 by norm_num, mul_pow, pow_two]] using h
  have hscaled :
      R * (3 * (Q.dilate 4).carrier.card + Q.carrier.card) ≤
        R * (3 * R ^ 2 * Q.carrier.card) := by
    calc
      R * (3 * (Q.dilate 4).carrier.card + Q.carrier.card) =
          3 * R * (Q.dilate 4).carrier.card + R * Q.carrier.card := by ring
      _ ≤ 3 * R * (Q.dilate 4).carrier.card +
          (Q.dilate 4).boxCard := Nat.add_le_add_left hlow _
      _ ≤ 3 * R * (Q.dilate 4).boxCard := by
        simpa [R] using hdef
      _ ≤ 3 * R * (R ^ 2 * Q.carrier.card) :=
        Nat.mul_le_mul_left _ hupper
      _ = R * (3 * R ^ 2 * Q.carrier.card) := by ring
  have hthree :
      3 * (Q.dilate 4).carrier.card + Q.carrier.card ≤
        3 * R ^ 2 * Q.carrier.card := by
    exact Nat.le_of_mul_le_mul_left hscaled hR
  change T * (Q.dilate 2).carrier.card ≤
      (T * R - 1) * Q.carrier.card ∨
    T * (Q.dilate 4).carrier.card ≤
      (T * R - 1) * (Q.dilate 2).carrier.card
  by_contra h
  push_neg at h
  rcases h with ⟨hfirst, hsecond⟩
  dsimp [T] at hfirst hsecond
  let U := 12 * R
  let A₀ := 12 * R * R - 1
  change A₀ * Q.carrier.card < U * (Q.dilate 2).carrier.card at hfirst
  change A₀ * (Q.dilate 2).carrier.card <
    U * (Q.dilate 4).carrier.card at hsecond
  have hU : 0 < U := by dsimp [U]; positivity
  have hlarge : 1 < 12 * R * R := by
    calc
      1 < 12 := by norm_num
      _ ≤ 12 * R * R := by
        have hRone : 1 ≤ R := hR
        nlinarith
  have hA₀ : 0 < A₀ := by
    dsimp [A₀]
    exact Nat.sub_pos_of_lt hlarge
  have hA₀step : A₀ + 1 = 12 * R * R := by
    dsimp [A₀]
    exact Nat.sub_add_cancel hlarge.le
  have ha : 0 < Q.carrier.card := by
    rw [hcard, boxCard]
    positivity
  have hlower : A₀ ^ 2 * Q.carrier.card <
      U ^ 2 * (Q.dilate 4).carrier.card := by
    calc
      A₀ ^ 2 * Q.carrier.card = A₀ * (A₀ * Q.carrier.card) := by ring
      _ < A₀ * (U * (Q.dilate 2).carrier.card) :=
        Nat.mul_lt_mul_of_pos_left hfirst hA₀
      _ = U * (A₀ * (Q.dilate 2).carrier.card) := by ring
      _ < U * (U * (Q.dilate 4).carrier.card) :=
        Nat.mul_lt_mul_of_pos_left hsecond hU
      _ = U ^ 2 * (Q.dilate 4).carrier.card := by ring
  have hupperClean :
      U ^ 2 * (Q.dilate 4).carrier.card +
          4 * (A₀ + 1) * Q.carrier.card ≤
        (A₀ + 1) ^ 2 * Q.carrier.card := by
    have hs := Nat.mul_le_mul_left (48 * R ^ 2) hthree
    calc
      U ^ 2 * (Q.dilate 4).carrier.card +
          4 * (A₀ + 1) * Q.carrier.card =
        (48 * R ^ 2) *
          (3 * (Q.dilate 4).carrier.card + Q.carrier.card) := by
            dsimp [U]
            rw [hA₀step]
            ring
      _ ≤ (48 * R ^ 2) * (3 * R ^ 2 * Q.carrier.card) := hs
      _ = (A₀ + 1) ^ 2 * Q.carrier.card := by
        rw [hA₀step]
        ring
  nlinarith

end GeneralizedAP

/-- A finite arithmetic progression `r, r + q, ..., r + Lq`. -/
def natAP (r q L : ℕ) : Finset ℕ :=
  (Finset.range (L + 1)).image fun x => r + q * x

lemma mem_natAP_iff {r q L m : ℕ} :
    m ∈ natAP r q L ↔ ∃ x ≤ L, r + q * x = m := by
  simp [natAP]

lemma card_natAP {r q L : ℕ} (hq : 0 < q) :
    (natAP r q L).card = L + 1 := by
  rw [natAP, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have hmul : q * x = q * y := Nat.add_left_cancel hxy
    exact mul_left_cancel₀ hq.ne' hmul

/-- Arithmetic progressions with the same step add by adding their bases and
lengths. -/
lemma natAP_add_natAP (r₁ r₂ q L₁ L₂ : ℕ) :
    natAP r₁ q L₁ + natAP r₂ q L₂ =
      natAP (r₁ + r₂) q (L₁ + L₂) := by
  ext m
  constructor
  · intro hm
    rw [Finset.mem_add] at hm
    obtain ⟨a, ha, b, hb, rfl⟩ := hm
    obtain ⟨x, hx, rfl⟩ := mem_natAP_iff.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_natAP_iff.mp hb
    apply mem_natAP_iff.mpr
    refine ⟨x + y, by omega, ?_⟩
    ring
  · intro hm
    obtain ⟨z, hz, hzm⟩ := mem_natAP_iff.mp hm
    let x := min z L₁
    let y := z - x
    have hx : x ≤ L₁ := min_le_right _ _
    have hxy : x + y = z := by
      simp only [y]
      exact Nat.add_sub_of_le (min_le_left _ _)
    have hy : y ≤ L₂ := by
      simp only [x, y]
      omega
    rw [← hzm, ← hxy]
    apply Finset.mem_add.mpr
    refine ⟨r₁ + q * x, mem_natAP_iff.mpr ⟨x, hx, rfl⟩,
      r₂ + q * y, mem_natAP_iff.mpr ⟨y, hy, rfl⟩, ?_⟩
    ring

lemma nsmul_natAP (n r q L : ℕ) (hn : 0 < n) :
    n • natAP r q L = natAP (n * r) q (n * L) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp
      · rw [succ_nsmul, ih (Nat.pos_of_ne_zero hn0), natAP_add_natAP]
        simp [Nat.succ_mul]

/-- Divide every member of a finite set by a common factor. -/
def scaleDown (d : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image fun a => a / d

/-- Every subset of a divided set is the exact image of a subset of the
original set.  This is the support-level statement needed to preserve
nonemptiness during divisor iteration. -/
lemma exists_subset_image_div_eq {d : ℕ} {A T : Finset ℕ}
    (hT : T ⊆ scaleDown d A) :
    ∃ S ⊆ A, S.image (fun a => a / d) = T := by
  let S := A.filter fun a => a / d ∈ T
  refine ⟨S, Finset.filter_subset _ _, ?_⟩
  apply Finset.Subset.antisymm
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨a, haS, rfl⟩ := ht
    exact (Finset.mem_filter.mp haS).2
  · intro t ht
    have ht' := hT ht
    rw [scaleDown, Finset.mem_image] at ht'
    obtain ⟨a, haA, rfl⟩ := ht'
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨haA, ht⟩)

/-- Division by `d` is injective on a set all of whose members are divisible
by `d`. -/
lemma div_injOn_of_dvd {d : ℕ} {A : Finset ℕ} (hdiv : ∀ a ∈ A, d ∣ a) :
    Set.InjOn (fun a : ℕ => a / d) A := by
  intro a ha b hb hab
  calc
    a = d * (a / d) := (Nat.mul_div_cancel' (hdiv a ha)).symm
    _ = d * (b / d) := congrArg (d * ·) hab
    _ = b := Nat.mul_div_cancel' (hdiv b hb)

/-- Dividing a finite set by a common divisor preserves its cardinality. -/
lemma card_scaleDown_of_dvd {d : ℕ} {A : Finset ℕ}
    (hdiv : ∀ a ∈ A, d ∣ a) :
    (scaleDown d A).card = A.card := by
  rw [scaleDown, Finset.card_image_of_injOn (div_injOn_of_dvd hdiv)]

/-- Division by a positive common divisor transports the ambient interval
`[1,N]` to `[1,N/d]`. -/
lemma scaleDown_subset_Icc {d N : ℕ} {A : Finset ℕ} (hd : 0 < d)
    (hdiv : ∀ a ∈ A, d ∣ a) (hA : A ⊆ Finset.Icc 1 N) :
    scaleDown d A ⊆ Finset.Icc 1 (N / d) := by
  intro t ht
  rw [scaleDown, Finset.mem_image] at ht
  obtain ⟨a, haA, rfl⟩ := ht
  have haIcc := Finset.mem_Icc.mp (hA haA)
  apply Finset.mem_Icc.mpr
  constructor
  · have hda : d ≤ a := Nat.le_of_dvd (by omega) (hdiv a haA)
    exact Nat.div_pos hda hd
  · exact Nat.div_le_div_right haIcc.2

/-- Every subset of a divided set lifts to a subset of the original set, and
its sum is multiplied by the common factor. -/
lemma exists_subset_sum_eq_mul_of_subset_scaleDown {d : ℕ} {A T : Finset ℕ}
    (hdiv : ∀ a ∈ A, d ∣ a) (hT : T ⊆ scaleDown d A) :
    ∃ S ⊆ A, ∑ a ∈ S, a = d * ∑ t ∈ T, t := by
  let S := A.filter fun a => a / d ∈ T
  have hSA : S ⊆ A := by
    exact Finset.filter_subset _ _
  have himage : S.image (fun a => a / d) = T := by
    apply Finset.Subset.antisymm
    · intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨a, haS, rfl⟩ := ht
      exact (Finset.mem_filter.mp haS).2
    · intro t ht
      have ht' := hT ht
      rw [scaleDown, Finset.mem_image] at ht'
      obtain ⟨a, haA, rfl⟩ := ht'
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨haA, ht⟩)
  have hinj : Set.InjOn (fun a : ℕ => a / d) S :=
    (div_injOn_of_dvd hdiv).mono hSA
  refine ⟨S, hSA, ?_⟩
  calc
    ∑ a ∈ S, a = ∑ a ∈ S, d * (a / d) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Nat.mul_div_cancel' (hdiv a (hSA ha))).symm
    _ = d * ∑ a ∈ S, a / d := by rw [Finset.mul_sum]
    _ = d * ∑ t ∈ S.image (fun a => a / d), t := by
      rw [Finset.sum_image hinj]
    _ = d * ∑ t ∈ T, t := by rw [himage]

/-- The precise divisor-iteration identity used by Nguyen--Vu: a
`(p*d)`-multiple of a square in the divided set lifts to a `p`-multiple of a
square in the original set. -/
lemma lift_p_mul_square_from_scaleDown {p d z : ℕ} {A T : Finset ℕ}
    (hdiv : ∀ a ∈ A, d ∣ a) (hT : T ⊆ scaleDown d A)
    (hsum : ∑ t ∈ T, t = (p * d) * z ^ 2) :
    ∃ S ⊆ A, ∑ a ∈ S, a = p * (d * z) ^ 2 := by
  obtain ⟨S, hSA, hSsum⟩ :=
    exists_subset_sum_eq_mul_of_subset_scaleDown hdiv hT
  refine ⟨S, hSA, ?_⟩
  rw [hSsum, hsum]
  ring

/-- No nonempty subset sum is `p` times a square.  Tracking `p` makes the
Nguyen--Vu common-divisor branch stable under iteration. -/
def PMultipleSquareSubsetSumFree (p : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ∀ z : ℕ, ∑ a ∈ S, a ≠ p * z ^ 2

lemma pMultipleSquareSubsetSumFree_one_iff (A : Finset ℕ) :
    PMultipleSquareSubsetSumFree 1 A ↔ SquareSubsetSumFree A := by
  constructor
  · intro hp S hSA hSne hsq
    obtain ⟨z, hz⟩ := hsq
    exact hp S hSA (Finset.nonempty_iff_ne_empty.mpr hSne) z
      (by simpa [pow_two] using hz)
  · intro hfree S hSA hSne z hsum
    apply hfree S hSA hSne.ne_empty
    refine ⟨z, ?_⟩
    simpa [pow_two] using hsum

/-- Exact predicate transport in the common-divisor branch: if the original
set has no `p`-multiple square subset sum, its quotient has no `(p*d)`-
multiple square subset sum. -/
lemma pMultipleSquareSubsetSumFree_scaleDown {p d : ℕ} {A : Finset ℕ}
    (hdiv : ∀ a ∈ A, d ∣ a) (hfree : PMultipleSquareSubsetSumFree p A) :
    PMultipleSquareSubsetSumFree (p * d) (scaleDown d A) := by
  intro T hT hTne z hsum
  obtain ⟨S, hSA, himage⟩ := exists_subset_image_div_eq hT
  have hSne : S.Nonempty := by
    have hImg : (S.image (fun a : ℕ => a / d)).Nonempty := by
      rwa [himage]
    exact Finset.image_nonempty.mp hImg
  apply hfree S hSA hSne (d * z)
  calc
    ∑ a ∈ S, a = ∑ a ∈ S, d * (a / d) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Nat.mul_div_cancel' (hdiv a (hSA ha))).symm
    _ = d * ∑ a ∈ S, a / d := by rw [Finset.mul_sum]
    _ = d * ∑ t ∈ S.image (fun a => a / d), t := by
      rw [Finset.sum_image ((div_injOn_of_dvd hdiv).mono hSA)]
    _ = d * ∑ t ∈ T, t := by rw [himage]
    _ = d * ((p * d) * z ^ 2) := by rw [hsum]
    _ = p * (d * z) ^ 2 := by ring

/-- If the accumulated divisor at least doubles at every iteration, after
`k` steps it is at least `2^k`. -/
lemma pow_two_le_of_doubling {k : ℕ} {p : ℕ → ℕ} (hp₀ : 1 ≤ p 0)
    (hstep : ∀ i < k, 2 * p i ≤ p (i + 1)) : 2 ^ k ≤ p k := by
  induction k with
  | zero => simpa using hp₀
  | succ k ih =>
    have ih' : 2 ^ k ≤ p k :=
      ih fun i hi => hstep i (hi.trans (Nat.lt_succ_self k))
    calc
      2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
      _ ≤ 2 * p k := Nat.mul_le_mul_left 2 ih'
      _ ≤ p (k + 1) := hstep k (Nat.lt_succ_self k)

/-- Consequently the common-divisor branch can occur at most logarithmically
many times while the accumulated divisor stays at most `n`. -/
lemma iteration_le_log_two {k n : ℕ} {p : ℕ → ℕ} (hp₀ : 1 ≤ p 0)
    (hstep : ∀ i < k, 2 * p i ≤ p (i + 1)) (hpn : p k ≤ n) :
    k ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact (pow_two_le_of_doubling hp₀ hstep).trans hpn

lemma mem_admissible_iff {N : ℕ} {A : Finset ℕ} :
    A ∈ (Finset.Icc 1 N).powerset.filter (fun A => ∀ S ⊆ A, S ≠ ⊥ →
      ¬ IsSquare (∑ n ∈ S, n)) ↔
      A ⊆ Finset.Icc 1 N ∧ SquareSubsetSumFree A := by
  simp [SquareSubsetSumFree]

lemma admissible_nonempty (N : ℕ) :
    ((Finset.Icc 1 N).powerset.filter fun A => ∀ S ⊆ A, S ≠ ⊥ →
      ¬ IsSquare (∑ n ∈ S, n)).Nonempty := by
  refine ⟨∅, ?_⟩
  simp

/-- A positive square in Mathlib's subset-sum finset contradicts
`SquareSubsetSumFree`. -/
lemma not_squareSubsetSumFree_of_mem_subsetSum {A : Finset ℕ} {m : ℕ}
    (hm : m ∈ A.subsetSum) (hmpos : 0 < m) (hmsq : IsSquare m) :
    ¬ SquareSubsetSumFree A := by
  rw [Finset.mem_subsetSum_iff] at hm
  obtain ⟨S, hSA, hsum⟩ := hm
  intro hfree
  apply hfree S hSA
  · rintro rfl
    simp at hsum
    omega
  · simpa [hsum] using hmsq

/-- If a subset-sum set contains a positive arithmetic progression and that
progression contains a square, the original set is not admissible. -/
lemma not_squareSubsetSumFree_of_natAP {A : Finset ℕ} {r q L m : ℕ}
    (hAP : natAP r q L ⊆ A.subsetSum) (hmAP : m ∈ natAP r q L)
    (hmpos : 0 < m) (hmsq : IsSquare m) :
    ¬ SquareSubsetSumFree A :=
  not_squareSubsetSumFree_of_mem_subsetSum (hAP hmAP) hmpos hmsq

/-- A pointwise natural-cardinality estimate bounds the finite supremum. -/
theorem maxNotSqSum_le_of_card_le {N B : ℕ}
    (h : ∀ A ⊆ Finset.Icc 1 N, SquareSubsetSumFree A → A.card ≤ B) :
    MaxNotSqSum N ≤ B := by
  apply Finset.sup_le
  intro A hA
  rw [mem_admissible_iff] at hA
  exact h A hA.1 hA.2

/-- The elementary ambient-set estimate, used for finite exceptional values. -/
theorem maxNotSqSum_le (N : ℕ) : MaxNotSqSum N ≤ N := by
  apply maxNotSqSum_le_of_card_le
  intro A hA _
  exact (Finset.card_le_card hA).trans_eq (by simp)

/-- The supremum is attained by an admissible set. -/
theorem exists_admissible_card_eq (N : ℕ) :
    ∃ A ⊆ Finset.Icc 1 N, SquareSubsetSumFree A ∧ A.card = MaxNotSqSum N := by
  let family := (Finset.Icc 1 N).powerset.filter fun A => ∀ S ⊆ A, S ≠ ⊥ →
    ¬ IsSquare (∑ n ∈ S, n)
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup family (admissible_nonempty N) Finset.card
  rw [mem_admissible_iff] at hA
  exact ⟨A, hA.1, hA.2, hmax.symm⟩

/-- Every admissible set is bounded by the exact finite supremum.  Together
with `exists_admissible_card_eq`, this rules out any gap between the upstream
`Finset.sup` packaging and the finite square-forcing theorem. -/
theorem card_le_maxNotSqSum {N : ℕ} {A : Finset ℕ}
    (hAN : A ⊆ Finset.Icc 1 N) (hfree : SquareSubsetSumFree A) :
    A.card ≤ MaxNotSqSum N := by
  apply Finset.le_sup
  exact mem_admissible_iff.mpr ⟨hAN, hfree⟩

/-- For natural inputs, the upstream cube-root expression is the usual real
power with exponent `3⁻¹`. -/
lemma nthRoot_three_natCast (N : ℕ) :
    Real.nthRoot 3 (N : ℝ) = (N : ℝ) ^ ((3 : ℝ)⁻¹) := by
  exact Real.nthRoot_of_nonneg (Nat.cast_nonneg N)

/-! ## Elementary square-location lemmas -/

/-- Algebraic core of the rank-one GAP case.  If the quadratic displacement
from `p*z₀² + q*t` lies between `t` and `t+L`, the corresponding `p`-multiple
of a square lies in the progression. -/
lemma p_mul_square_mem_natAP_of_bounds (p q z₀ t L x : ℕ)
    (hlo : t ≤ 2 * p * z₀ * x + p * q * x ^ 2)
    (hhi : 2 * p * z₀ * x + p * q * x ^ 2 ≤ t + L) :
    p * (z₀ + q * x) ^ 2 ∈ natAP (p * z₀ ^ 2 + q * t) q L := by
  let e := 2 * p * z₀ * x + p * q * x ^ 2
  have hte : t + (e - t) = e := Nat.add_sub_of_le hlo
  rw [mem_natAP_iff]
  refine ⟨e - t, by omega, ?_⟩
  calc
    p * z₀ ^ 2 + q * t + q * (e - t) =
        p * z₀ ^ 2 + q * (t + (e - t)) := by ring
    _ = p * z₀ ^ 2 + q * e := by rw [hte]
    _ = p * (z₀ + q * x) ^ 2 := by simp only [e]; ring

/-- Initial (`p = 1`) specialization of the rank-one calculation. -/
lemma exists_square_mem_natAP_of_bounds (q z₀ t L x : ℕ)
    (hlo : t ≤ 2 * z₀ * x + q * x ^ 2)
    (hhi : 2 * z₀ * x + q * x ^ 2 ≤ t + L) :
    ∃ m ∈ natAP (z₀ ^ 2 + q * t) q L, IsSquare m := by
  refine ⟨(z₀ + q * x) ^ 2, ?_, ⟨z₀ + q * x, by simp [pow_two]⟩⟩
  simpa using p_mul_square_mem_natAP_of_bounds 1 q z₀ t L x (by simpa using hlo)
    (by simpa using hhi)

/-- An interval whose length reaches the next-square gap contains a square. -/
lemma exists_square_in_interval (a L : ℕ) (hL : 2 * Nat.sqrt a + 1 ≤ L) :
    ∃ z : ℕ, a ≤ z ^ 2 ∧ z ^ 2 ≤ a + L := by
  refine ⟨Nat.sqrt a + 1, ?_, ?_⟩
  · exact (Nat.lt_succ_sqrt' a).le
  · have hsqrt : Nat.sqrt a ^ 2 ≤ a := Nat.sqrt_le' a
    nlinarith

/-- Set-valued form of `exists_square_in_interval`. -/
lemma exists_isSquare_mem_Icc (a L : ℕ) (hL : 2 * Nat.sqrt a + 1 ≤ L) :
    ∃ m ∈ Finset.Icc a (a + L), IsSquare m := by
  obtain ⟨z, haz, hza⟩ := exists_square_in_interval a L hL
  exact ⟨z ^ 2, Finset.mem_Icc.mpr ⟨haz, hza⟩, ⟨z, by simp [pow_two]⟩⟩

/-- Squarefree-kernel version of the elementary square-location argument.
If `q = u² d`, then the square multiples of `q` occur at the indices
`d z²` in the homogeneous progression `q * (t + x)`.  The displayed
bound reaches the first such index after `t`. -/
lemma exists_square_mem_homogeneous_natAP_of_factorization
    (q t L u d : ℕ) (hd : 0 < d) (hu : 0 < u)
    (hq : u ^ 2 * d = q)
    (hL : d * (2 * Nat.sqrt (t / d) + 1) ≤ L) :
    ∃ m ∈ natAP (q * t) q L, 0 < m ∧ IsSquare m := by
  let z := Nat.sqrt (t / d) + 1
  have htLower : t < d * z ^ 2 := by
    have htDiv : t < d * (t / d + 1) := Nat.lt_mul_div_succ t hd
    have hnext : t / d + 1 ≤ z ^ 2 := by
      dsimp [z]
      simpa only [Nat.succ_eq_add_one] using
        Nat.succ_le_iff.mpr (Nat.lt_succ_sqrt' (t / d))
    exact htDiv.trans_le (Nat.mul_le_mul_left d hnext)
  have htUpper : d * z ^ 2 ≤ t + L := by
    have hsqrt : Nat.sqrt (t / d) ^ 2 ≤ t / d := Nat.sqrt_le' _
    have hdiv : d * (t / d) ≤ t := Nat.mul_div_le t d
    dsimp [z]
    nlinarith
  let x := d * z ^ 2 - t
  have hxL : x ≤ L := by
    dsimp [x]
    omega
  refine ⟨(u * d * z) ^ 2, ?_, ?_, ⟨u * d * z, by simp [pow_two]⟩⟩
  · rw [mem_natAP_iff]
    refine ⟨x, hxL, ?_⟩
    have htx : t + x = d * z ^ 2 := by
      dsimp [x]
      omega
    calc
      q * t + q * x = q * (t + x) := by ring
      _ = q * (d * z ^ 2) := by rw [htx]
      _ = (u * d * z) ^ 2 := by rw [← hq]; ring
  · have hz : 0 < z := by dsimp [z]; omega
    positivity

/-- A homogeneous natural arithmetic progression contains a square as soon
as its index length exceeds a simple bound depending only on its step and
starting index.  This wrapper chooses the squarefree kernel of the step. -/
lemma exists_square_mem_homogeneous_natAP (q t L : ℕ) (hqpos : 0 < q)
    (hL : 2 * Nat.sqrt (q * t) + q ≤ L) :
    ∃ m ∈ natAP (q * t) q L, 0 < m ∧ IsSquare m := by
  obtain ⟨d, u, hd, hu, hfactor, _hdsq⟩ := Nat.sq_mul_squarefree_of_pos hqpos
  apply exists_square_mem_homogeneous_natAP_of_factorization
    q t L u d hd hu hfactor
  have hdq : d ≤ q := by
    have huSq : 1 ≤ u ^ 2 := by nlinarith
    calc
      d = 1 * d := by simp
      _ ≤ u ^ 2 * d := Nat.mul_le_mul_right d huSq
      _ = q := hfactor
  have hdiv : d * (t / d) ≤ t := Nat.mul_div_le t d
  have hsqrt : Nat.sqrt (t / d) ^ 2 ≤ t / d := Nat.sqrt_le' _
  have hsq : (d * Nat.sqrt (t / d)) ^ 2 ≤ d * t := by
    calc
      (d * Nat.sqrt (t / d)) ^ 2 =
          d * (d * Nat.sqrt (t / d) ^ 2) := by ring
      _ ≤ d * (d * (t / d)) := by gcongr
      _ ≤ d * t := Nat.mul_le_mul_left d hdiv
  have hsqrtMul : d * Nat.sqrt (t / d) ≤ Nat.sqrt (d * t) := by
    rw [Nat.le_sqrt']
    exact hsq
  have hdt : d * t ≤ q * t := Nat.mul_le_mul_right t hdq
  have hsqrtMono : Nat.sqrt (d * t) ≤ Nat.sqrt (q * t) :=
    Nat.sqrt_le_sqrt hdt
  calc
    d * (2 * Nat.sqrt (t / d) + 1) =
        2 * (d * Nat.sqrt (t / d)) + d := by ring
    _ ≤ 2 * Nat.sqrt (q * t) + q := by omega
    _ ≤ L := hL

/-- Ambient-bound form of the homogeneous rank-one argument.  If the initial
term is at most `H`, it is enough for the index length to dominate the square
root of `H` and the common step. -/
lemma exists_square_mem_homogeneous_natAP_of_start_le
    (q t L H : ℕ) (hqpos : 0 < q) (htH : q * t ≤ H)
    (hL : 2 * Nat.sqrt H + q ≤ L) :
    ∃ m ∈ natAP (q * t) q L, 0 < m ∧ IsSquare m := by
  apply exists_square_mem_homogeneous_natAP q t L hqpos
  exact (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.sqrt_le_sqrt htH)) q).trans hL

/-- A sufficiently long homogeneous arithmetic progression in the subset
sums contradicts square-subset-sum-freeness. -/
lemma not_squareSubsetSumFree_of_homogeneous_natAP
    {A : Finset ℕ} {q t L H : ℕ} (hqpos : 0 < q)
    (htH : q * t ≤ H) (hL : 2 * Nat.sqrt H + q ≤ L)
    (hAP : natAP (q * t) q L ⊆ A.subsetSum) :
    ¬ SquareSubsetSumFree A := by
  obtain ⟨m, hmAP, hmpos, hmsq⟩ :=
    exists_square_mem_homogeneous_natAP_of_start_le q t L H hqpos htH hL
  exact not_squareSubsetSumFree_of_mem_subsetSum (hAP hmAP) hmpos hmsq

/-- Reduction of the final theorem to a uniform bound for every admissible
finite set.  This lemma also isolates all bookkeeping around `Finset.sup`. -/
theorem nguyen_vu_of_eventual_card_bound
    (O : ℕ) (hO : 0 < O) (O' : ℝ) (hO' : 0 < O')
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      SquareSubsetSumFree A →
        (A.card : ℝ) ≤ O' * Real.nthRoot 3 N * (N : ℝ).log ^ O) :
    ∃ᵉ (C > 0) (K > 0), ∀ᶠ N in atTop,
      (MaxNotSqSum N : ℝ) ≤ K * Real.nthRoot 3 N * (N : ℝ).log ^ C := by
  refine ⟨O, hO, O', hO', ?_⟩
  filter_upwards [hbound] with N hN
  obtain ⟨A, hAN, hfree, hcard⟩ := exists_admissible_card_eq N
  rw [← hcard]
  exact hN A hAN hfree

/-- The formal-conjectures statement is exactly equivalent to the uniform
finite Nguyen--Vu estimate for every admissible subset.  In particular, the
remaining mathematical input cannot be avoided by manipulating the
`Finset.sup` definition of `MaxNotSqSum`. -/
theorem nguyen_vu_iff_eventual_uniform_card_bound :
    (∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
      (MaxNotSqSum N : ℝ) ≤
        O' * Real.nthRoot 3 N * (N : ℝ).log ^ O) ↔
    (∃ᵉ (O > 0) (O' > 0), ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Finset.Icc 1 N, SquareSubsetSumFree A →
        (A.card : ℝ) ≤
          O' * Real.nthRoot 3 N * (N : ℝ).log ^ O) := by
  constructor
  · rintro ⟨O, hO, O', hO', hmax⟩
    refine ⟨O, hO, O', hO', ?_⟩
    filter_upwards [hmax] with N hN
    intro A hAN hfree
    calc
      (A.card : ℝ) ≤ (MaxNotSqSum N : ℝ) := by
        exact_mod_cast card_le_maxNotSqSum hAN hfree
      _ ≤ O' * Real.nthRoot 3 N * (N : ℝ).log ^ O := hN
  · rintro ⟨O, hO, O', hO', hbound⟩
    exact nguyen_vu_of_eventual_card_bound O hO O' hO' hbound

/-- Contrapositive interface for the finite Nguyen--Vu theorem: if every set
larger than a real threshold has a nonempty square subset sum, then every
square-subset-sum-free set is at most that threshold. -/
lemma card_le_of_square_forcing {A : Finset ℕ} {B : ℝ}
    (hforce : B < A.card →
      ∃ S ⊆ A, S ≠ ∅ ∧ IsSquare (∑ a ∈ S, a))
    (hfree : SquareSubsetSumFree A) :
    (A.card : ℝ) ≤ B := by
  by_contra hle
  have hlt : B < (A.card : ℝ) := lt_of_not_ge hle
  obtain ⟨S, hSA, hSne, hSq⟩ := hforce hlt
  exact hfree S hSA hSne hSq

/-- Final theorem reduced to the square-producing form proved in Nguyen--Vu:
all sufficiently large subsets above the stated threshold contain a nonempty
square subset sum. -/
theorem nguyen_vu_of_eventual_square_forcing
    (O : ℕ) (hO : 0 < O) (O' : ℝ) (hO' : 0 < O')
    (hforce : ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc 1 N,
      O' * Real.nthRoot 3 N * (N : ℝ).log ^ O < A.card →
        ∃ S ⊆ A, S ≠ ∅ ∧ IsSquare (∑ a ∈ S, a)) :
    ∃ᵉ (C > 0) (K > 0), ∀ᶠ N in atTop,
      (MaxNotSqSum N : ℝ) ≤ K * Real.nthRoot 3 N * (N : ℝ).log ^ C := by
  apply nguyen_vu_of_eventual_card_bound O hO O' hO'
  filter_upwards [hforce] with N hN
  intro A hAN hfree
  exact card_le_of_square_forcing (hN A hAN) hfree

end Erdos587
