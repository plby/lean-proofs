import ErdosProblems.Erdos577.JointThreeRows

/-! Two positive-edge constructions of a quadrilateral with at least five edges. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma two_neighbors_degree {s : Finset V} {u a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hua : G.Adj u a) (hub : G.Adj u b) : 2 ≤ degreeIn G u s := by
  classical
  have hsub : ({a, b} : Finset V) ⊆ s.filter (G.Adj u) :=
    insert_subset (mem_filter.mpr ⟨ha, hua⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨hb, hub⟩))
  have hh := card_le_card hsub
  rw [card_pair_eq_two_iff.mpr hab] at hh
  exact hh

lemma triangle_plus_two_five {t : Finset V} (ht : G.IsNClique 3 t) {u : V}
    (hu : u ∉ t) (hdeg : 2 ≤ degreeIn G u t) :
    QuadOn G (insert u t) ∧ 5 ≤ edgeCount G (insert u t) := by
  refine ⟨QuadOn.of_triangle ht hu hdeg, ?_⟩
  have he : edgeCount G t = 3 := by
    rw [edgeCount_clique ht.isClique, ht.card_eq]
    rfl
  rw [edgeCount_insert G u hu, he]
  omega

lemma edge_triangle_five (z w a b : V) (hw : w ∉ ({z, a, b} : Finset V))
    (hza : G.Adj z a) (hzb : G.Adj z b) (hab : G.Adj a b)
    (hwz : G.Adj w z) (hcontact : G.Adj w a ∨ G.Adj w b) :
    QuadOn G {z, w, a, b} ∧ 5 ≤ edgeCount G {z, w, a, b} := by
  have ht : G.IsNClique 3 {z, a, b} := SimpleGraph.is3Clique_triple_iff.mpr ⟨hza, hzb, hab⟩
  have htwo : 2 ≤ degreeIn G w {z, a, b} := by
    rcases hcontact with ha | hb
    · exact two_neighbors_degree (by simp) (by simp) hza.ne hwz ha
    · exact two_neighbors_degree (by simp) (by simp) hzb.ne hwz hb
  have h := triangle_plus_two_five ht hw htwo
  rwa [insert_comm w z] at h

lemma shared_pair_five (z w a b : V) (hw : w ∉ ({z, a, b} : Finset V))
    (hza : G.Adj z a) (hzb : G.Adj z b) (hab : G.Adj a b)
    (hwa : G.Adj w a) (hwb : G.Adj w b) :
    QuadOn G {z, w, a, b} ∧ 5 ≤ edgeCount G {z, w, a, b} := by
  have ht : G.IsNClique 3 {z, a, b} := SimpleGraph.is3Clique_triple_iff.mpr ⟨hza, hzb, hab⟩
  have htwo : 2 ≤ degreeIn G w {z, a, b} :=
    two_neighbors_degree (by simp) (by simp) hab.ne hwa hwb
  have h := triangle_plus_two_five ht hw htwo
  rwa [insert_comm w z] at h

lemma exact_two_row (v : Quadrilateral G) (u : V) (i j : Fin 4) (hij : i ≠ j)
    (hdeg : degreeIn G u v.support ≤ 2) (hi : G.Adj u (v i)) (hj : G.Adj u (v j)) :
    ∀ k : Fin 4, G.Adj u (v k) ↔ k = i ∨ k = j := by
  have hsub : ({v i, v j} : Finset V) ⊆ v.support.filter (G.Adj u) :=
    insert_subset (mem_filter.mpr ⟨(v.mem_support _).mpr ⟨i, rfl⟩, hi⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨(v.mem_support _).mpr ⟨j, rfl⟩, hj⟩))
  have hcard : ({v i, v j} : Finset V).card = 2 := card_pair_eq_two_iff.mpr (v.injective.ne hij)
  have he : v.support.filter (G.Adj u) = {v i, v j} :=
    (eq_of_subset_of_card_le hsub (by rw [hcard]; exact hdeg)).symm
  intro k
  constructor
  · intro hk
    have hm : v k ∈ v.support.filter (G.Adj u) :=
      mem_filter.mpr ⟨(v.mem_support _).mpr ⟨k, rfl⟩, hk⟩
    rw [he] at hm
    simp only [mem_insert, mem_singleton] at hm
    exact hm.elim (fun hh ↦ Or.inl (v.injective hh)) (fun hh ↦ Or.inr (v.injective hh))
  · rintro (rfl | rfl)
    · exact hi
    · exact hj

lemma exact_extreme_row (v : Quadrilateral G) (u : V)
    (hdeg : degreeIn G u v.support ≤ 2) (h0 : G.Adj u (v 0)) (h3 : G.Adj u (v 3)) :
    ∀ i : Fin 4, G.Adj u (v i) ↔ (9 : ℕ).testBit i.val = true := by
  have hrow := exact_two_row v u 0 3 (by decide) hdeg h0 h3
  have hf : ∀ i : Fin 4, i = 0 ∨ i = 3 ↔ (9 : ℕ).testBit i.val = true := by decide +kernel
  exact fun i ↦ (hrow i).trans (hf i)

end Erdos577.JointFinal
