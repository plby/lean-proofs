import ErdosProblems.Erdos577.TriangleRows
import ErdosProblems.Erdos577.Replacements

/-! Dense triangle rows into a complete block give actual universal replacements. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma two_universal_rows_of_ten_clique {t q : Finset V}
    (ht : t.card = 3) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (h : 10 ≤ contacts G t q) :
    ∃ u ∈ t, ∃ v ∈ t, u ≠ v ∧
      (∀ w ∈ q, QuadOn G (insert u (q.erase w))) ∧
      (∀ w ∈ q, QuadOn G (insert v (q.erase w))) := by
  obtain ⟨u, hu, v, hv, hne, hdu, hdv⟩ := two_high_rows_of_ten ht hq.card_eq h
  have hqu : u ∉ q := fun h ↦ disjoint_left.mp hd hu h
  have hqv : v ∉ q := fun h ↦ disjoint_left.mp hd hv h
  exact ⟨u, hu, v, hv, hne, fun _ hw ↦ clique_replace_of_degree_three hq hqu hdu hw,
    fun _ hw ↦ clique_replace_of_degree_three hq hqv hdv hw⟩

lemma every_universal_row_of_eleven_clique {t q : Finset V}
    (ht : t.card = 3) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (h : 11 ≤ contacts G t q) {v : V} (hv : v ∈ t) {w : V} (hw : w ∈ q) :
    QuadOn G (insert v (q.erase w)) :=
  clique_replace_of_degree_three hq (fun h ↦ disjoint_left.mp hd hv h)
    (every_row_high_of_eleven ht hq.card_eq h hv) hw

end Erdos577
