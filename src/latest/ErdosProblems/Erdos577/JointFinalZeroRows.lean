import ErdosProblems.Erdos577.JointFinalThreeLeaf

/-! Row normalization for the empty-old-leaf case.
Feasibility of the core exchange is not assumed. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma missing_first_common_three (j : Quadrilateral G) (z w : V)
    (hseven : 7 ≤ degreeIn G z j.support + degreeIn G w j.support)
    (hmiss : ¬(G.Adj z (j 0) ∧ G.Adj w (j 0))) :
    degreeIn G z j.support + degreeIn G w j.support = 7 ∧
      ∀ i : Fin 4, i ≠ 0 → G.Adj z (j i) ∧ G.Adj w (j i) := by
  have missed (x y : V) (hh : ¬G.Adj x (j 0))
      (hxy : 7 ≤ degreeIn G x j.support + degreeIn G y j.support) :
      degreeIn G x j.support + degreeIn G y j.support = 7 ∧
        ∀ i : Fin 4, i ≠ 0 → G.Adj x (j i) ∧ G.Adj y (j i) := by
    have hm : j 0 ∈ j.support := (j.mem_support _).mpr ⟨0, rfl⟩
    have he := degreeIn_erase_add G x (j 0) hm
    rw [if_neg hh] at he
    have hc : (j.support.erase (j 0)).card = 3 := by rw [card_erase_of_mem hm, j.card_support]
    have hx3 := degreeIn_le_card G x (j.support.erase (j 0))
    have hy4 := degreeIn_le_card G y j.support
    rw [hc] at hx3
    rw [j.card_support] at hy4
    have hfullx := (degreeIn_eq_card_iff (G := G) x (j.support.erase (j 0))).mp
      (by rw [hc]; omega)
    have hfully := (degreeIn_eq_card_iff (G := G) y j.support).mp
      (by rw [j.card_support]; omega)
    refine ⟨by omega, ?_⟩
    intro i hi
    have hmi : j i ∈ j.support := (j.mem_support _).mpr ⟨i, rfl⟩
    exact ⟨hfullx (j i) (mem_erase.mpr ⟨j.injective.ne hi, hmi⟩), hfully (j i) hmi⟩
  by_cases hz : G.Adj z (j 0)
  · obtain ⟨hs, hrows⟩ := missed w z (fun hw ↦ hmiss ⟨hz, hw⟩) (by omega)
    exact ⟨by omega, fun i hi ↦ (hrows i hi).symm⟩
  · exact missed z w hz hseven

lemma opposite_pair_common_false (j : Quadrilateral G) (y z w : V) (hy : y ∉ j.support)
    (hy0 : G.Adj y (j 0)) (hy2 : G.Adj y (j 2))
    (hseven : 7 ≤ degreeIn G z j.support + degreeIn G w j.support)
    (hno : ¬CommonReplacement G z w y j.support) : False := by
  let common := j.support.filter (G.Adj z) ∩ j.support.filter (G.Adj w)
  have hcard : 3 ≤ common.card := FullRow.common_set_card j z w hseven
  have hr1 := j.replace_using_path y hy 1 0 3 2 (by decide) (by decide)
    hy0 (j.adjacent 3).symm (j.adjacent 2).symm hy2
  have hr3 := j.replace_using_path y hy 3 0 1 2 (by decide) (by decide)
    hy0 (j.adjacent 0) (j.adjacent 1) hy2
  have hnot (i : Fin 4) (hr : QuadOn G (insert y (j.support.erase (j i)))) : j i ∉ common := by
    intro hi
    obtain ⟨hz, hw⟩ := mem_inter.mp hi
    exact hno ⟨j i, (mem_filter.mp hz).1, (mem_filter.mp hz).2, (mem_filter.mp hw).2, hr⟩
  have hsub : common ⊆ {j 0, j 2} := by
    intro u hu
    have huj := (mem_filter.mp (mem_inter.mp hu).1).1
    obtain ⟨i, rfl⟩ := (j.mem_support u).mp huj
    fin_cases i
    · exact mem_insert_self _ _
    · exact False.elim (hnot 1 hr1 hu)
    · exact mem_insert_of_mem (mem_singleton_self _)
    · exact False.elim (hnot 3 hr3 hu)
  have hbound : common.card ≤ 2 := (card_le_card hsub).trans card_le_two
  omega

lemma adjacent_last_pair_labels (j : Quadrilateral G) (y z w : V) (hy : y ∉ j.support)
    (hy2 : degreeIn G y j.support = 2)
    (hseven : 7 ≤ degreeIn G z j.support + degreeIn G w j.support)
    (hno : ¬CommonReplacement G z w y j.support) :
    ∃ v : Quadrilateral G, v.support = j.support ∧
      ∀ i : Fin 4, G.Adj y (v i) ↔ i = 2 ∨ i = 3 := by
  obtain ⟨v, hv, hrow | hrow⟩ := j.exists_two_contact_labels y hy2
  · refine ⟨v.rotate 2, (v.rotate_support 2).trans hv, ?_⟩
    intro i
    rw [Quadrilateral.rotate_apply, hrow]
    fin_cases i <;> decide
  · have hy0 := (hrow 0).mpr (by decide)
    have hy2' := (hrow 2).mpr (by decide)
    exact False.elim (opposite_pair_common_false v y z w (by rwa [hv]) hy0 hy2'
      (by rwa [hv]) (by rwa [hv]))

end Erdos577.JointFinal
