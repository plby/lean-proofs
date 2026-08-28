import ErdosProblems.Erdos577.FullLeafHeavyHigh

/-! Two removable clique vertices and the exact eight-contact bound for two low columns. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma two_clique_replacements {j : Finset V} (hcl : G.IsNClique 4 j)
    {u : V} (hout : u ∉ j) (htwo : 2 ≤ degreeIn G u j) :
    ∃ v ∈ j, ∃ w ∈ j, v ≠ w ∧ QuadOn G (insert u (j.erase v)) ∧
      QuadOn G (insert u (j.erase w)) := by
  by_cases hthree : 3 ≤ degreeIn G u j
  · obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp (by rw [hcl.card_eq]; decide)
    exact ⟨v, hv, w, hw, hvw, clique_replace_of_degree_three hcl hout hthree hv,
      clique_replace_of_degree_three hcl hout hthree hw⟩
  · have he : degreeIn G u j = 2 := by omega
    have hsize : (j \ j.filter (G.Adj u)).card = 2 := by
      rw [card_sdiff_of_subset (filter_subset _ _), hcl.card_eq]
      change 4 - degreeIn G u j = 2
      rw [he]
    have hrep (v : V) (hv : v ∈ j \ j.filter (G.Adj u)) :
        QuadOn G (insert u (j.erase v)) := by
      obtain ⟨hvj, hn⟩ := mem_sdiff.mp hv
      have hnon : ¬G.Adj u v := fun hh ↦ hn (mem_filter.mpr ⟨hvj, hh⟩)
      have hh := degreeIn_erase_add G u v hvj
      rw [if_neg hnon, he] at hh
      exact (clique_replace_iff_two_contacts hcl hout hvj).mpr (by omega)
    obtain ⟨v, hv, w, hw, hvw⟩ := one_lt_card.mp (show 1 < (j \ j.filter (G.Adj u)).card by omega)
    exact ⟨v, (mem_sdiff.mp hv).1, w, (mem_sdiff.mp hw).1, hvw, hrep v hv, hrep w hw⟩

omit [DecidableEq V] in
lemma two_low_columns_le_eight {t j : Finset V} (ht : t.card = 3) (hj : j.card = 4)
    {v w : V} (hv : v ∈ j) (hw : w ∈ j) (hvw : v ≠ w)
    (hvd : degreeIn G v t ≤ 1) (hwd : degreeIn G w t ≤ 1) : contacts G t j ≤ 8 := by
  classical
  have hw' : w ∈ j.erase v := mem_erase.mpr ⟨hvw.symm, hw⟩
  have htwo : ((j.erase v).erase w).card = 2 := by
    rw [card_erase_of_mem hw', card_erase_of_mem hv, hj]
  have hvsum := sum_erase_add (s := j) (fun u ↦ degreeIn G u t) hv
  have hwsum := sum_erase_add (s := j.erase v) (fun u ↦ degreeIn G u t) hw'
  have hrest : (∑ u ∈ (j.erase v).erase w, degreeIn G u t) ≤ 6 := by
    calc
      (∑ u ∈ (j.erase v).erase w, degreeIn G u t) ≤ ∑ _ ∈ (j.erase v).erase w, (3 : ℕ) :=
        sum_le_sum fun u _ ↦ (degreeIn_le_card G u t).trans_eq ht
      _ = 6 := by simp only [sum_const, smul_eq_mul, htwo]
  rw [contacts_comm, contacts]
  omega

end Erdos577.FullLeafHeavy
