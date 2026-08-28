import ErdosProblems.Erdos577.FullLeafSixPawBound

/-! When the first rows are at most two, the twelve-contact case is forced exactly. -/

namespace Erdos577.FullLeafSix

open Finset

lemma three_low_rows {V : Type*} {t : Finset V} {f : V → ℕ} {n : ℕ}
    (ht : t.card = 3) (hrow : ∀ v ∈ t, f v ≤ 2)
    (hpaw : ∀ v ∈ t, n + f v ≤ 8) (htotal : 12 ≤ (∑ v ∈ t, f v) + n) :
    n = 6 ∧ ∀ v ∈ t, f v = 2 := by
  have hfirst : (∑ v ∈ t, f v) ≤ 6 := by
    calc
      (∑ v ∈ t, f v) ≤ ∑ _ ∈ t, (2 : ℕ) := sum_le_sum hrow
      _ = 6 := by rw [sum_const, smul_eq_mul, ht]
  have hpaws := sum_le_sum hpaw
  have hpaws' : 3 * n + (∑ v ∈ t, f v) ≤ 24 := by
    simpa only [sum_add_distrib, sum_const, smul_eq_mul, ht] using hpaws
  have hn : n = 6 := by omega
  have hsum : (∑ v ∈ t, f v) = 6 := by omega
  refine ⟨hn, fun v hv ↦ FullLeafEquality.pointwise_eq_of_sum_eq hrow ?_ hv⟩
  simpa only [sum_const, smul_eq_mul, ht] using hsum

end Erdos577.FullLeafSix

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Maximal.low_first_rows_alternative (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (htotal : 12 ≤ contacts G ((s.erase y) ∪ FullLeafEquality.matchedSecond p s a y) j)
    (hrow : ∀ u ∈ s.erase y, degreeIn G u j ≤ 2) :
    contacts G (s.erase y) j = 0 ∨
      (contacts G (FullLeafEquality.matchedSecond p s a y) j = 6 ∧
        ∀ u ∈ s.erase y, degreeIn G u j = 2) := by
  by_cases hz : contacts G (s.erase y) j = 0
  · exact Or.inl hz
  right
  have hsecond : contacts G (FullLeafEquality.matchedSecond p s a y) j ≤ 8 := by
    by_contra hh
    exact hz (hm.second_nine_first_zero hcard hdeg hn hj hjs hja htotal (by omega))
  apply FullLeafSix.three_low_rows hm.1.first_triple_clique.card_eq hrow
  · intro u hu
    by_cases hzero : degreeIn G u j = 0
    · omega
    · exact hm.positive_first_paw_le_eight hcard hdeg hn hj hjs hja htotal hu (by omega)
  · rwa [contacts_union_left G hm.1.matched_triples_disjoint] at htotal

end Erdos577.FullLeafCore
