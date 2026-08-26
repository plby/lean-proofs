/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Coordinate projections and nontriviality in minimal box covers.
Informal source: the projected subcovers in BBMST's exploration construction.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridSlices
import ErdosProblems.Erdos1189.CoordinateDichotomy

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [DecidableEq ι]

def project (I : Finset ι) (H : Box q) : Box q := fun i => if i ∈ I then H i else none

lemma project_project (I J : Finset ι) (H : Box q) :
    project I (project J H) = project (I ∩ J) H := by
  funext i
  by_cases hi : i ∈ I <;> by_cases hj : i ∈ J <;> simp [project, hi, hj]

lemma project_apply_of_mem {I : Finset ι} {H : Box q} {i : ι} (hi : i ∈ I) :
    project I H i = H i := if_pos hi

lemma project_apply_of_notMem {I : Finset ι} {H : Box q} {i : ι} (hi : i ∉ I) :
    project I H i = none := if_neg hi

lemma fixed_project [Fintype ι] (I : Finset ι) (H : Box q) :
    fixed (project I H) = fixed H ∩ I := by
  ext i
  by_cases hi : i ∈ I
  · simp only [mem_fixed, project_apply_of_mem hi, mem_inter, hi, and_true]
  · simp only [mem_fixed, project_apply_of_notMem hi, reduceCtorEq, exists_false,
      mem_inter, hi, and_false]

lemma project_eq_of_fixed_subset [Fintype ι] {I : Finset ι} {H : Box q}
    (h : fixed H ⊆ I) : project I H = H := by
  funext i
  by_cases hi : i ∈ I
  · exact project_apply_of_mem hi
  · rw [project_apply_of_notMem hi]
    cases hv : H i with
    | none => rfl
    | some v => exact False.elim (hi (h (mem_fixed.mpr ⟨v, hv⟩)))

lemma familyFixed_project [Fintype ι] (I : Finset ι) (H : α → Box q) (A : Finset α) :
    familyFixed (fun a => project I (H a)) A = familyFixed H A ∩ I := by
  ext i
  simp only [mem_familyFixed, fixed_project, mem_inter]
  aesop

lemma boxMeasureOn_project (J I : Finset ι) (H : Box q) :
    boxMeasureOn J (project I H) = boxMeasureOn (J ∩ I) H := by
  have hset : J ∩ I = J.filter (fun i => i ∈ I) := by ext i; simp
  unfold boxMeasureOn
  rw [hset, prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ I <;> simp [project, hi]

lemma familyFixed_congr [Fintype ι] {H K : α → Box q} {A : Finset α}
    (h : ∀ a ∈ A, H a = K a) : familyFixed H A = familyFixed K A := by
  ext i
  simp only [mem_familyFixed]
  constructor
  · rintro ⟨a, ha, hi⟩
    exact ⟨a, ha, h a ha ▸ hi⟩
  · rintro ⟨a, ha, hi⟩
    exact ⟨a, ha, (h a ha).symm ▸ hi⟩

lemma project_familyFixed_member [Fintype ι] (H : α → Box q) {A : Finset α} {a : α}
    (ha : a ∈ A) : project (familyFixed H A) (H a) = H a :=
  project_eq_of_fixed_subset fun _ hi => mem_familyFixed.mpr ⟨a, ha, hi⟩

lemma project_projected_familyFixed_member [Fintype ι]
    (I : Finset ι) (H : α → Box q) {A : Finset α} {a : α} (ha : a ∈ A) :
    project (familyFixed (fun b => project I (H b)) A) (H a) = project I (H a) := by
  have hsub : familyFixed (fun b => project I (H b)) A ⊆ I := by
    rw [familyFixed_project]
    exact inter_subset_right
  have h := project_familyFixed_member (fun b => project I (H b)) ha
  rw [project_project, inter_eq_left.mpr hsub] at h
  exact h

lemma project_drop (I : Finset ι) (H : Box q) (i : ι) :
    drop i (project I H) = project (I.erase i) H := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [drop, project]
  · simp [drop, project, hji]

lemma MinimalCoverOn.fixed_nonempty [Fintype ι] {H : α → Box q} {A : Finset α}
    (hA : MinimalCoverOn H A Set.univ) (hF : (familyFixed H A).Nonempty) :
    ∀ a ∈ A, (fixed (H a)).Nonempty := by
  intro a ha
  by_contra hnot
  have hfull : ∀ u : Point q, Contains (H a) u := by
    intro u i v hiv
    exact False.elim (hnot ⟨i, mem_fixed.mpr ⟨v, hiv⟩⟩)
  obtain ⟨i, hi⟩ := hF
  obtain ⟨b, hb, hib⟩ := mem_familyFixed.mp hi
  obtain ⟨u, _, _, hprivate⟩ := hA.private_witness hb
  have hab : a = b := by
    by_contra hab
    exact hprivate a ha hab (hfull u)
  exact hnot ⟨i, hab.symm ▸ hib⟩

omit [DecidableEq ι] in
lemma CoversOn.congr_boxes {H K : α → Box q} {A : Finset α} {X : Set (Point q)}
    (h : CoversOn H A X) (heq : ∀ a ∈ A, H a = K a) : CoversOn K A X := by
  intro u hu
  obtain ⟨a, ha, hua⟩ := h u hu
  exact ⟨a, ha, heq a ha ▸ hua⟩

omit [DecidableEq ι] in
lemma MinimalCoverOn.congr_boxes {H K : α → Box q} {A : Finset α} {X : Set (Point q)}
    (h : MinimalCoverOn H A X) (heq : ∀ a ∈ A, H a = K a) : MinimalCoverOn K A X := by
  refine ⟨h.1.congr_boxes heq, ?_⟩
  intro B hB hcover
  exact h.2 B hB (hcover.congr_boxes (fun a ha => (heq a (hB.subset ha)).symm))

end Erdos1189.Grid
