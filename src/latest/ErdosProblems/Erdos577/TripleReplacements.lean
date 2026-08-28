import ErdosProblems.Erdos577.PairReplacements

/-! A two-contact vertex can replace a vertex of the specified old triple. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Quadrilateral

lemma replace_first_three_of_diagonal (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hdiag : G.Adj (q 1) (q 3)) (hdegree : 2 ≤ degreeIn G z q.support) :
    ∃ u : Fin 4, u ≠ 3 ∧ QuadOn G (insert z (q.support.erase (q u))) := by
  obtain ⟨i, j, hne, hi, hj⟩ := q.exists_two_neighbor_indices z hdegree
  fin_cases i <;> fin_cases j
  · exact False.elim (hne rfl)
  · refine ⟨2, by decide, ?_⟩
    exact q.replace_using_path z hz 2 0 3 1 (by decide) (by decide)
      hi ((q.adjacent 3).symm) ((hdiag).symm) hj
  · refine ⟨1, by decide, ?_⟩
    exact q.replace_using_path z hz 1 0 3 2 (by decide) (by decide)
      hi ((q.adjacent 3).symm) ((q.adjacent 2).symm) hj
  · refine ⟨2, by decide, ?_⟩
    exact q.replace_using_path z hz 2 0 1 3 (by decide) (by decide)
      hi (q.adjacent 0) (hdiag) hj
  · refine ⟨2, by decide, ?_⟩
    exact q.replace_using_path z hz 2 1 3 0 (by decide) (by decide)
      hi (hdiag) (((q.adjacent 3).symm).symm) hj
  · exact False.elim (hne rfl)
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 1 3 2 (by decide) (by decide)
      hi (hdiag) ((q.adjacent 2).symm) hj
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 1 2 3 (by decide) (by decide)
      hi (q.adjacent 1) (q.adjacent 2) hj
  · refine ⟨1, by decide, ?_⟩
    exact q.replace_using_path z hz 1 2 3 0 (by decide) (by decide)
      hi (q.adjacent 2) (((q.adjacent 3).symm).symm) hj
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 2 3 1 (by decide) (by decide)
      hi (q.adjacent 2) ((hdiag).symm) hj
  · exact False.elim (hne rfl)
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 2 1 3 (by decide) (by decide)
      hi ((q.adjacent 1).symm) (hdiag) hj
  · refine ⟨2, by decide, ?_⟩
    exact q.replace_using_path z hz 2 3 1 0 (by decide) (by decide)
      hi ((hdiag).symm) ((q.adjacent 0).symm) hj
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 3 2 1 (by decide) (by decide)
      hi ((q.adjacent 2).symm) ((q.adjacent 1).symm) hj
  · refine ⟨0, by decide, ?_⟩
    exact q.replace_using_path z hz 0 3 1 2 (by decide) (by decide)
      hi ((hdiag).symm) (q.adjacent 1) hj
  · exact False.elim (hne rfl)

lemma replace_last_three_of_clique (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hclique : G.IsNClique 4 q.support) (hdegree : 2 ≤ degreeIn G z q.support) :
    ∃ u : Fin 4, u ≠ 0 ∧ QuadOn G (insert z (q.support.erase (q u))) := by
  obtain ⟨i, j, hne, hi, hj⟩ := q.exists_two_neighbor_indices z hdegree
  have hex : ∀ i j : Fin 4, i ≠ j → ∃ u mid : Fin 4, u ≠ 0 ∧ i ≠ mid ∧ mid ≠ j ∧
      ({i, mid, j} : Finset (Fin 4)) = univ.erase u := by decide +kernel
  obtain ⟨u, mid, hu, him, hmj, hcover⟩ := hex i j hne
  have hmem (a : Fin 4) : q a ∈ q.support := (q.mem_support _).mpr ⟨a, rfl⟩
  refine ⟨u, hu, q.replace_using_path z hz u i mid j hne hcover hi ?_ ?_ hj⟩
  · exact hclique.isClique (hmem i) (hmem mid) (fun h ↦ him (q.injective h))
  · exact hclique.isClique (hmem mid) (hmem j) (fun h ↦ hmj (q.injective h))

end Quadrilateral

end Erdos577
