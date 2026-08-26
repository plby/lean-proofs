import ErdosProblems.Erdos19.EdgeDegreePartition
import ErdosProblems.Erdos19.PairGraphColoring
import ErdosProblems.Erdos19.PairStarRemainder

/-! # Exact completion from almost saturated high-degree vertices

The vertices that miss the single exceptional color form an independent set.
Consequently the maximum-degree core of the residual pair graph is independent,
and the proved matching-core form of Vizing finishes with exactly the fresh palette.
-/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem incident_degree_lower_of_one_color_exception (J : SetHypergraph V) (m : ℕ)
    (c : J.EdgeColoring (Fin m)) (v : V) (bad : Fin m)
    (hcover : ∀ a, a ≠ bad → v ∈ J.colorCovered c a) :
    m ≤ (J.incidentEdges v).ncard + 1 := by
  classical
  have hpoint (a : Fin m) : 1 ≤ (if v ∈ J.colorCovered c a then 1 else 0) +
      (if a = bad then 1 else 0 : ℕ) := by
    by_cases ha : a = bad
    · simp only [ha, ↓reduceIte]; omega
    · simp only [hcover a ha, ha, ↓reduceIte, Nat.add_zero, le_refl]
  have hsum := sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin m))) ↦ hpoint a)
  simpa only [sum_add_distrib, colorCovered_count, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, sum_ite_eq', mem_univ, ↓reduceIte] using hsum

theorem incident_degree_eq_of_full_color_coverage (J : SetHypergraph V) (m : ℕ)
    (c : J.EdgeColoring (Fin m)) (v : V)
    (hcover : ∀ a, v ∈ J.colorCovered c a) : (J.incidentEdges v).ncard = m := by
  rw [← J.colorCovered_count c v]
  simp only [hcover, ↓reduceIte, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem edgeColorable_of_almost_saturated_partial_coloring (H J : SetHypergraph V)
    (hJH : J ⊆ H) (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (hpair : ∀ e ∈ H, e ∉ J → e.ncard = 2) (m D : ℕ) (hD : 0 < D)
    (hvertices : Fintype.card V = m + D) (color : J.EdgeColoring (Fin m))
    (U Z : Set V)
    (hcover : ∀ v ∈ U, m ≤ (J.incidentEdges v).ncard + if v ∈ Z then 1 else 0)
    (houtside : ∀ v, v ∉ U → (H \ J).twoGraph.degree v < D)
    (hindependent : ∀ x ∈ Z, ∀ y ∈ Z, ¬H.twoGraph.Adj x y) :
    H.EdgeColorable (m + D) := by
  classical
  let K : SetHypergraph V := H \ J
  let G := K.twoGraph
  have hdegreeCard (v : V) : G.degree v = (G.neighborSet v).ncard := by
    rw [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
  have hcounts (v : V) : G.degree v ≤ D ∧ (v ∉ Z → G.degree v < D) := by
    by_cases hvU : v ∈ U
    · have hsplit := H.incident_degree_add_sdiff J hJH v
      have htotal := H.incidentEdges_ncard_le_card_pred hlinear hmin v
      rw [hvertices] at htotal
      have hpairs := K.pair_degree_le_incident_degree K (fun _ he _ ↦ he) v
      have hc := hcover v hvU
      rw [hdegreeCard]
      change (J.incidentEdges v).ncard + (K.incidentEdges v).ncard = _ at hsplit
      change (G.neighborSet v).ncard ≤ (K.incidentEdges v).ncard at hpairs
      by_cases hvZ : v ∈ Z
      · rw [if_pos hvZ] at hc
        exact ⟨by omega, fun h ↦ (h hvZ).elim⟩
      · rw [if_neg hvZ] at hc
        exact ⟨by omega, fun _ ↦ by omega⟩
    · have h := houtside v hvU
      exact ⟨h.le, fun _ ↦ h⟩
  have hcore : Vizing.HasMatchingDegreeCore G D := by
    intro x y z hx hxy _ hy _
    have hxZ : x ∈ Z := by
      by_contra hxnot
      have h := (hcounts x).2 hxnot
      omega
    have hyZ : y ∈ Z := by
      by_contra hynot
      have h := (hcounts y).2 hynot
      omega
    exact (hindependent x hxZ y hyZ ⟨hxy.1, hxy.2.1⟩).elim
  have hKcolor : K.EdgeColorable D := K.edgeColorable_pairs_of_matching_core
    (fun e ↦ hpair e.1 e.2.1 e.2.2) D hD (fun v ↦ (hcounts v).1) hcore
  have hcolor := J.edgeColorable_union K ⟨color⟩ hKcolor
  have hunion : J ∪ K = H := by
    ext e
    constructor
    · rintro (he | he)
      · exact hJH he
      · exact he.1
    · intro he
      by_cases heJ : e ∈ J
      · exact Or.inl heJ
      · exact Or.inr ⟨he, heJ⟩
  simpa only [hunion] using hcolor

#print axioms edgeColorable_of_almost_saturated_partial_coloring

end Erdos19.SetHypergraph
