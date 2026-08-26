/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The measure and disjointness properties of the selected good frame families.
Informal source: BBMST Lemma 4.6.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationNesting

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ} {A : Finset α} {I : Finset ι}

omit [Fintype ι] [DecidableEq ι] in
lemma boxMeasureOn_le_one (hq : ∀ i, 1 ≤ q i) (J : Finset ι) (K : Box q) :
    boxMeasureOn J K ≤ 1 := by
  apply prod_le_one
  · intro i _
    cases K i <;> simp only [Option.elim_none, Option.elim_some] <;> positivity
  · intro i _
    cases K i with
    | none => exact le_rfl
    | some v =>
      have hi : (1 : ℝ) ≤ q i := by exact_mod_cast hq i
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hi

omit [DecidableEq ι] in
lemma boxMeasureOn_le_coordinate (hq : ∀ i, 1 ≤ q i) (J : Finset ι) (K : Box q)
    {j : ι} (hj : j ∈ J) (hfixed : j ∈ fixed K) :
    boxMeasureOn J K ≤ 1 / (q j : ℝ) := by
  classical
  rw [boxMeasureOn_erase hj hfixed]
  exact mul_le_of_le_one_right (by positivity) (boxMeasureOn_le_one hq _ _)

lemma ExplorationTree.entry_outside_measure_eq
    (tree : ExplorationTree H lam ε δ A univ)
    (e : ExplorationEntry H lam ε δ) (he : e ∈ tree.entries) (a : α) (ha : a ∈ e.family) :
    boxMeasureOn (univ \ insert e.label e.pathLabels) (H a) =
      boxMeasureOn (univ.erase e.label) (project e.active (H a)) := by
  rw [boxMeasureOn_project, boxMeasureOn_eq_fixed, boxMeasureOn_eq_fixed]
  congr 1
  ext j
  have hbound : j ∈ fixed (H a) → j ∈ e.pathLabels ∨ j ∈ e.active := by
    intro hj
    have h := tree.entry_original_fixed_subset e he (Grid.mem_familyFixed.mpr ⟨a, ha, hj⟩)
    simpa only [mem_union, mem_sdiff, mem_univ, not_true_eq_false, and_false, false_or] using h
  have hdisj : j ∈ e.pathLabels → j ∈ e.active → False :=
    fun hp hact => disjoint_left.mp (tree.entry_path_disjoint e he) hp hact
  simp only [mem_inter, mem_sdiff, mem_univ, mem_insert, mem_erase, true_and, and_true]
  tauto

lemma ExplorationTree.good_boxes_disjoint (tree : ExplorationTree H lam ε δ A I)
    (hq : ∀ i, 1 ≤ q i) (hδ : 0 < δ) (i j : I) (hij : i ≠ j)
    (hqi : 1 / δ ≤ (q i : ℝ)) (hqj : 1 / δ ≤ (q j : ℝ))
    (F G : Finset α)
    (hF : ∀ a ∈ F, a ∈ (tree.firstEntry i).family ∧
      i.val ∈ fixed (project (tree.firstEntry i).active (H a)) ∧
      δ < boxMeasureOn (univ.erase i.val) (project (tree.firstEntry i).active (H a)))
    (hG : ∀ a ∈ G, a ∈ (tree.firstEntry j).family ∧
      j.val ∈ fixed (project (tree.firstEntry j).active (H a)) ∧
      δ < boxMeasureOn (univ.erase j.val) (project (tree.firstEntry j).active (H a))) :
    Disjoint F G := by
  have hcontra : ∀ (i j : I), tree.firstIndex i < tree.firstIndex j →
      1 / δ ≤ (q j : ℝ) → ∀ a : α,
      a ∈ (tree.firstEntry i).family → j.val ∈ fixed (H a) →
      δ < boxMeasureOn (univ.erase i.val) (project (tree.firstEntry i).active (H a)) →
      False := by
    intro i j hlt hqj a ha hj hm
    have hsub := tree.firstEntry_active_subset i j hlt (Grid.mem_familyFixed.mpr ⟨a, ha, hj⟩)
    have hjActive : j.val ∈ (tree.firstEntry j).active := by
      have h : (tree.firstEntry j).label ∈ (tree.firstEntry j).active :=
        (tree.firstEntry j).step.coordinate_mem
      simpa only [tree.firstEntry_label] using h
    have hji := hsub hjActive
    have hfixed : j.val ∈ fixed (project (tree.firstEntry i).active (H a)) := by
      rw [fixed_project]
      exact mem_inter.mpr ⟨hj, mem_of_mem_erase hji⟩
    have hjErase : j.val ∈ univ.erase i.val :=
      mem_erase.mpr ⟨(mem_erase.mp hji).1, mem_univ _⟩
    have hmle := boxMeasureOn_le_coordinate hq _ _ hjErase hfixed
    have hqpos : (0 : ℝ) < q j := lt_of_lt_of_le (by norm_num)
      (show (1 : ℝ) ≤ q j from by exact_mod_cast hq j)
    have hsmall := (lt_div_iff₀ hqpos).mp (hm.trans_le hmle)
    have hlarge := (div_le_iff₀ hδ).mp hqj
    nlinarith
  apply disjoint_left.mpr
  intro a haF haG
  obtain ⟨haI, _, hmi⟩ := hF a haF
  obtain ⟨haJ, hj, hmj⟩ := hG a haG
  have hi := (hF a haF).2.1
  rw [fixed_project] at hi hj
  rcases lt_trichotomy (tree.firstIndex i) (tree.firstIndex j) with hlt | heq | hgt
  · exact hcontra i j hlt hqj a haI (mem_inter.mp hj).1 hmi
  · exact hij (tree.firstIndex_injective heq)
  · exact hcontra j i hgt hqi a haJ (mem_inter.mp hi).1 hmj

end Erdos1189.Grid
