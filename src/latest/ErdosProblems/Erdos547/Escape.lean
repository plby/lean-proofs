import ErdosProblems.Erdos547.MissingNeighbors

/-!
# Failure of escape produces a dense configuration

All losses are explicit natural numbers. The alternatives are a small set of
high internal minimum degree or two disjoint sets of high cross minimum degree.
No tree-embedding assertion is assumed in this graph-theoretic lemma.
-/

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
/-- Quantitative form of the escape dichotomy. The square budget controls
the deletion loss when an almost complete pair is cleaned. -/
theorem escape_failure_dense_configuration [DecidableEq V] (m d k t : ℕ)
    (hroom : d + k + t < m) (hbudget : m * (d + k) ≤ t ^ 2)
    (hmin : ∀ z, m ≤ G.degree z + d) (x u : V) (hx : G.degree x ≤ m)
    (hfail : ((G.neighborFinset u).filter
      fun z ↦ k ≤ (G.neighborFinset z \ G.neighborFinset x).card).card < k) :
    (∃ C : Finset V, C.Nonempty ∧ C.card ≤ m ∧
      ∀ v ∈ C, m ≤ degreeIn G C v + 3 * (d + k + t) + k) ∨
    (∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ A.card ≤ m ∧ B.card ≤ m ∧
      Disjoint A B ∧ (∀ a ∈ A, m ≤ degreeIn G B a + (d + k + t)) ∧
      ∀ b ∈ B, m ≤ degreeIn G A b + (d + k + t)) := by
  classical
  let B := G.neighborFinset x
  let good := (G.neighborFinset u).filter fun z ↦ k ≤ (G.neighborFinset z \ B).card
  let bad := (G.neighborFinset u).filter fun z ↦ ¬ k ≤ (G.neighborFinset z \ B).card
  have hsplit : good.card + bad.card = G.degree u := by
    have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset u)
      (fun z ↦ k ≤ (G.neighborFinset z \ B).card)
    rw [G.card_neighborFinset_eq_degree] at h
    exact h
  have hbadcard : m - (d + k) ≤ bad.card := by
    change good.card < k at hfail
    have h := hmin u
    omega
  obtain ⟨A, hAbad, hAcard⟩ := Finset.exists_subset_card_eq hbadcard
  have hApos : A.Nonempty := Finset.card_pos.mp (by omega)
  have hAupper : A.card ≤ m := by omega
  have hAeq : A.card + d + k = m := by omega
  have hBupper : B.card ≤ m := by simpa only [B, G.card_neighborFinset_eq_degree] using hx
  have hout (a : V) (ha : a ∈ A) : (G.neighborFinset a \ B).card < k := by
    exact lt_of_not_ge (Finset.mem_filter.mp (hAbad ha)).2
  have hAB (a : V) (ha : a ∈ A) : m ≤ degreeIn G B a + (d + k) := by
    have h₁ := hmin a
    have h₂ := hout a ha
    have h₃ := degreeIn_add_outside G B a
    omega
  have hmissing (a : V) (ha : a ∈ A) : missingIn G B a ≤ d + k := by
    have h₁ := hAB a ha
    have h₂ := degreeIn_add_missingIn G B a
    omega
  have hcap (a : V) (ha : a ∈ A) : G.degree a ≤ m + k := by
    have h₁ := degreeIn_add_outside G B a
    have h₂ := degreeIn_le_card G B a
    have h₃ := hout a ha
    omega
  have hbudgetA : A.card * (d + k) ≤ t ^ 2 :=
    (Nat.mul_le_mul_right (d + k) hAupper).trans hbudget
  obtain ⟨Q, hQB, hQcard, hQmissing, hdrop⟩ := prune_dense_pair G A B (d + k) t
    hmissing hbudgetA
  have hAQ (a : V) (ha : a ∈ A) : m ≤ degreeIn G Q a + (d + k + t) := by
    have h₁ := hAB a ha
    have h₂ := hdrop a
    omega
  have hQA (b : V) (hb : b ∈ Q) : m ≤ degreeIn G A b + (d + k + t) := by
    have h₁ := hQmissing b hb
    have h₂ := degreeIn_add_missingIn G A b
    omega
  have hQpos : Q.Nonempty := by
    obtain ⟨a, ha⟩ := hApos
    have h₁ := hAQ a ha
    have h₂ := degreeIn_le_card G Q a
    exact Finset.card_pos.mp (by omega)
  have hQupper : Q.card ≤ m := (Finset.card_le_card hQB).trans hBupper
  by_cases hdis : Disjoint A Q
  · exact Or.inr ⟨A, Q, hApos, hQpos, hAupper, hQupper, hdis, hAQ, hQA⟩
  · have hI : (A ∩ Q).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdis
    exact Or.inl ⟨A ∩ Q, hI, (Finset.card_le_card Finset.inter_subset_left).trans hAupper,
      dense_intersection_core G A Q m (d + k + t) k hAupper hI hAQ hQA hcap⟩

end Erdos547

#print axioms Erdos547.escape_failure_dense_configuration
