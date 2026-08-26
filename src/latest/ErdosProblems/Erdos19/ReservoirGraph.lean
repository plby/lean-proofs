import ErdosProblems.Erdos19.GraphReservoir

/-! # Realizing a sampled edge set as one reservoir graph -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_graph_realizing_edge_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) :
    ∃ R : _root_.SimpleGraph V, R ≤ G ∧
      (∀ v, R.degree v = (G.incidenceFinset v ∩ P).card) ∧
      (∀ X Y : Finset V, (R.between (X : Set V) (Y : Set V)).edgeFinset.card =
        ((G.between (X : Set V) (Y : Set V)).edgeFinset ∩ P).card) := by
  classical
  let R := fromEdgeSet (P : Set (Sym2 V))
  letI : DecidableRel R.Adj := fun x y ↦ Classical.propDecidable (R.Adj x y)
  have hRG : R ≤ G := by
    intro x y hxy
    have he := hP hxy.1
    simpa only [mem_edgeFinset, mem_edgeSet] using he
  have hRP : R.edgeFinset = P := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [mem_edgeFinset, mem_edgeSet, fromEdgeSet_adj]
      constructor
      · exact And.left
      · intro h
        have hadj : G.Adj x y := by simpa only [mem_edgeFinset, mem_edgeSet] using hP h
        exact ⟨h, hadj.ne⟩
  refine ⟨R, hRG, ?_, ?_⟩
  · intro v
    rw [← card_incidenceFinset_eq_degree]
    congr 1
    rw [incidenceFinset_eq_filter, incidenceFinset_eq_filter, hRP]
    ext e
    simp only [mem_filter, mem_inter]
    constructor
    · intro h
      exact ⟨⟨hP h.1, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  · intro X Y
    have heq : R.between (X : Set V) (Y : Set V) =
        G.between (X : Set V) (Y : Set V) ⊓ R := by
      ext x y
      constructor
      · intro h
        exact ⟨⟨hRG h.1, h.2⟩, h.1⟩
      · intro h
        exact ⟨h.2, h.1.2⟩
    congr 1
    apply Finset.coe_injective
    simp only [coe_edgeFinset, coe_inter]
    rw [heq, edgeSet_inf]
    have hRPset : R.edgeSet = (P : Set (Sym2 V)) := by rw [← coe_edgeFinset, hRP]
    rw [hRPset]

theorem eventually_exists_reservoir_graph (k : ℕ) (hk : 0 < k)
    (alpha epsilon : ℝ) (halpha : 0 < alpha) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∃ R : _root_.SimpleGraph (Fin n), R ≤ G ∧
        (∀ v, |(R.degree v : ℝ) - (n : ℝ) / k| < epsilon * n) ∧
        (∀ X Y : Finset (Fin n), Disjoint X Y →
          alpha * n ≤ (X.card : ℝ) → alpha * n ≤ (Y.card : ℝ) →
          (X.card : ℝ) * Y.card / (2 * k) <
            (R.between (X : Set (Fin n)) (Y : Set (Fin n))).edgeSet.ncard) := by
  obtain ⟨delta, hd, N, hN⟩ :=
    eventually_exists_dense_graph_reservoir k hk alpha epsilon halpha hepsilon
  refine ⟨delta, hd, N, ?_⟩
  intro n hn G hG
  obtain ⟨P, hP, hdegrees, hcuts⟩ := hN n hn G hG
  obtain ⟨R, hRG, hdR, hcR⟩ := exists_graph_realizing_edge_subset G P hP
  refine ⟨R, hRG, ?_, ?_⟩
  · intro v
    rw [hdR]
    exact hdegrees v
  · intro X Y hXY hX hY
    have h := hcuts X Y hXY hX hY
    rw [← hcR] at h
    simpa only [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using h

#print axioms eventually_exists_reservoir_graph

end Erdos19
