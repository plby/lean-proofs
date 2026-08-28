import ErdosProblems.Erdos577.CycleLabels
import ErdosProblems.Erdos577.Replacements

/-! Arbitrary cyclic labels and exact replacement criteria in a complete four-set. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Quadrilateral.relabelOfClique (q : Quadrilateral G) (hq : G.IsNClique 4 q.support)
    (e : Fin 4 ↪ Fin 4) : Quadrilateral G :=
  Quadrilateral.ofEdges (e.trans q.toEmbedding) (fun i ↦
    hq.isClique ((q.mem_support _).mpr ⟨e i, rfl⟩)
      ((q.mem_support _).mpr ⟨e (i + 1), rfl⟩)
      (fun h ↦ (q.adjacent i).ne (congrArg q (e.injective (q.injective h)))))

@[simp] lemma Quadrilateral.relabelOfClique_apply (q : Quadrilateral G)
    (hq : G.IsNClique 4 q.support) (e : Fin 4 ↪ Fin 4) (i : Fin 4) :
    q.relabelOfClique hq e i = q (e i) := rfl

lemma Quadrilateral.relabelOfClique_support (q : Quadrilateral G)
    (hq : G.IsNClique 4 q.support) (e : Fin 4 ↪ Fin 4) :
    (q.relabelOfClique hq e).support = q.support := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, rfl⟩ := ((q.relabelOfClique hq e).mem_support v).mp hv
    exact (q.mem_support _).mpr ⟨e i, rfl⟩
  · simp only [Quadrilateral.card_support, le_refl]

lemma clique_replace_iff_two_contacts [DecidableRel G.Adj] {s : Finset V}
    (hs : G.IsNClique 4 s) {z u : V} (hz : z ∉ s) (hu : u ∈ s) :
    QuadOn G (insert z (s.erase u)) ↔ 2 ≤ degreeIn G z (s.erase u) := by
  have hze : z ∉ s.erase u := fun h ↦ hz (mem_erase.mp h).2
  constructor
  · intro hq
    have h := hq.two_le_degreeIn (mem_insert_self _ _)
    rw [degreeIn_insert G z z hze] at h
    simpa only [SimpleGraph.irrefl, if_false, Nat.zero_add] using h
  · intro htwo
    have ht : G.IsNClique 3 (s.erase u) := by
      refine ⟨SimpleGraph.IsClique.subset (coe_subset.mpr (erase_subset u s)) hs.isClique, ?_⟩
      rw [card_erase_of_mem hu, hs.card_eq]
    exact QuadOn.of_triangle ht hze htwo

end Erdos577
