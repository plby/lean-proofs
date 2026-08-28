import ErdosProblems.Erdos577.FullLeafEqualityCore

/-! Every bound in the ten-row degree sum is an equality. -/

namespace Erdos577.FullLeafEquality

open Finset

lemma pointwise_eq_of_sum_eq {I : Type*} {s : Finset I} {f g : I → ℕ}
    (hle : ∀ i ∈ s, f i ≤ g i) (heq : ∑ i ∈ s, f i = ∑ i ∈ s, g i)
    {i : I} (hi : i ∈ s) : f i = g i := by
  classical
  have hrest : (∑ j ∈ s.erase i, f j) ≤ ∑ j ∈ s.erase i, g j :=
    sum_le_sum (fun j hj ↦ hle j (mem_erase.mp hj).2)
  have hf := sum_erase_add (s := s) f hi
  have hg := sum_erase_add (s := s) g hi
  have hpoint := hle i hi
  omega

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma full_row_of_max_contacts {s t : Finset V}
    (heq : contacts G s t = s.card * t.card) {v : V} (hv : v ∈ s) :
    degreeIn G v t = t.card := by
  apply pointwise_eq_of_sum_eq (fun w _ ↦ degreeIn_le_card G w t) ?_ hv
  simpa only [contacts, sum_const, smul_eq_mul] using heq

end Erdos577.FullLeafEquality

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.ten_row_equalities (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) = 30 ∧
      (FullLeafEquality.covered c p s a y).card +
        2 * contacts G (s.erase y) (insert (p.vertices 3) a) = 8 ∧
      (∑ j ∈ FullLeafEquality.further c s a,
        contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j) =
        20 * (FullLeafEquality.further c s a).card + (FullLeafEquality.covered c p s a y).card := by
  have hk := hm.1.three_le_parameter hcard
  have hf := hm.1.further_card hcard
  have hdegree := minimum_degree_sum G ((insert p.leaf s) ∪ insert (p.vertices 3) a)
    (2 * k) (fun v _ ↦ hdeg v)
  rw [hm.1.ten_rows_card] at hdegree
  have hsplit := hm.1.ten_row_split
  have hinside := hm.1.ten_inside_contacts hcard hdeg hn
  have hcore := hm.1.second_core_contacts_le_thirty
  have houtside := hm.outside_contact_budget hcard hdeg hn
  have hcoverage := hm.1.sparse_coverage_bound hcard hn
  exact ⟨by omega, by omega, by omega⟩

theorem Maximal.equality_core_complete (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    G.IsNClique 7 (p.triangle ∪ a) :=
  hm.1.core_complete_of_thirty (hm.ten_row_equalities hcard hdeg hn).1

theorem Maximal.equality_sparse_cover (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    FullLeafEquality.covered c p s a y =
      ((s.erase y) ∪ insert (p.vertices 3) a) \
        (FullLeafEquality.matchedFirst p s a y ∪ FullLeafEquality.matchedSecond p s a y) :=
  hm.1.covered_eq_unmatched hcard hn (hm.ten_row_equalities hcard hdeg hn).2.1

end Erdos577.FullLeafCore
