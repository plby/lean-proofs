/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Elementary additive-combinatorial core used by Erdős 344 and 360

This module separates the unconditional finite-group subset-sum machinery
from the analytic dependencies used later in `Erdos587.lean`.
-/

open scoped Pointwise

namespace Erdos587

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

end Erdos587
