import ErdosProblems.Erdos577.ClaimTwoSixContributions

/-! The exact global weighted sum and odd first degree contradict the minimum degree. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

lemma Configuration.degree_core_further_split (h : Configuration c p s a y) (u : V) :
    degreeIn G u (p.support ∪ s ∪ a) +
      ∑ j ∈ FullLeafEquality.further c s a, degreeIn G u j = G.degree u := by
  simpa only [contacts, sum_singleton, degreeIn_univ] using h.core_further_split {u}

theorem Maximal.matched_second_inside_sum (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    contacts G (FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) = 21 := by
  calc
    contacts G (FullLeafEquality.matchedSecond p s a y) (p.support ∪ s ∪ a) =
        ∑ _ ∈ FullLeafEquality.matchedSecond p s a y, (7 : ℕ) :=
      sum_congr rfl (fun _ hv ↦ hm.second_matched_inside_degree hcard hdeg hn hv)
    _ = 21 := by
      rw [sum_const, smul_eq_mul, (hm.matched_second_triangle hcard hdeg hn).card_eq]

theorem Maximal.global_weighted_balance (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) :
    3 * G.degree u + contacts G (FullLeafEquality.matchedSecond p s a y) univ =
      36 + 12 * (FullLeafEquality.further c s a).card := by
  have hbalance : 3 * (∑ j ∈ FullLeafEquality.further c s a, degreeIn G u j) +
      (∑ j ∈ FullLeafEquality.further c s a,
        contacts G (FullLeafEquality.matchedSecond p s a y) j) =
      12 * (FullLeafEquality.further c s a).card := by
    calc
      _ = ∑ j ∈ FullLeafEquality.further c s a,
          (3 * degreeIn G u j + contacts G (FullLeafEquality.matchedSecond p s a y) j) := by
        rw [sum_add_distrib, mul_sum]
      _ = ∑ _ ∈ FullLeafEquality.further c s a, (12 : ℕ) :=
        sum_congr rfl (fun _ hj ↦ (hm.further_balance_and_even hcard hdeg hn hu hj).1)
      _ = _ := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
  have hfirst := hm.1.degree_core_further_split u
  rw [hm.first_matched_inside_degree hcard hdeg hn hu] at hfirst
  have hsecond := hm.1.core_further_split (FullLeafEquality.matchedSecond p s a y)
  rw [hm.matched_second_inside_sum hcard hdeg hn] at hsecond
  omega

theorem Maximal.first_global_odd (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    {u : V} (hu : u ∈ s.erase y) : ∃ n : ℕ, G.degree u = 5 + 2 * n := by
  refine ⟨∑ j ∈ FullLeafEquality.further c s a, degreeIn G u j / 2, ?_⟩
  have he : (∑ j ∈ FullLeafEquality.further c s a, degreeIn G u j) =
      2 * ∑ j ∈ FullLeafEquality.further c s a, degreeIn G u j / 2 := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ hj ↦ (hm.further_balance_and_even hcard hdeg hn hu hj).2)
  have hsplit := hm.1.degree_core_further_split u
  rw [hm.first_matched_inside_degree hcard hdeg hn hu, he] at hsplit
  exact hsplit.symm

theorem Maximal.false (hm : Maximal c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) :
    False := by
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (s.erase y).card by
    rw [hm.1.first_triple_clique.card_eq]; decide)
  have hbalance := hm.global_weighted_balance hcard hdeg hn hu
  obtain ⟨n, hnodd⟩ := hm.first_global_odd hcard hdeg hn hu
  have hfirst := hdeg u
  have hsecond := minimum_degree_sum G (FullLeafEquality.matchedSecond p s a y) (2 * k)
    (fun v _ ↦ hdeg v)
  rw [(hm.matched_second_triangle hcard hdeg hn).card_eq] at hsecond
  have hf := hm.1.further_card hcard
  have hk := hm.1.three_le_parameter hcard
  omega

end Erdos577.FullLeafCore
