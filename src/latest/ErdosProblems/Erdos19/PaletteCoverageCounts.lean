import ErdosProblems.Erdos19.MatchingColorExtension
import ErdosProblems.Erdos19.PairStarRemainder
import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Counting special-color coverage and active-color repair requests -/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [Fintype C]

theorem covered_color_count (H : SetHypergraph V) (c : H.EdgeColoring C) (v : V) :
    (∑ a : C, if v ∈ H.coveredVertices {e | c e = a} then 1 else 0) =
      (H.incidentEdges v).ncard := by
  simpa only [H.colorCovered_eq_coveredVertices c] using H.colorCovered_count c v

theorem all_color_absences (H : SetHypergraph V) (c : H.EdgeColoring C) (v : V) :
    (∑ a : C, if v ∈ H.coveredVertices {e | c e = a} then 0 else 1) =
      Fintype.card C - (H.incidentEdges v).ncard := by
  have hsum : (∑ a : C, if v ∈ H.coveredVertices {e | c e = a} then 1 else 0) +
      (∑ a : C, if v ∈ H.coveredVertices {e | c e = a} then 0 else 1) = Fintype.card C := by
    rw [← sum_add_distrib]
    have hpoint (a : C) : (if v ∈ H.coveredVertices {e | c e = a} then 1 else 0) +
        (if v ∈ H.coveredVertices {e | c e = a} then 0 else 1 : ℕ) = 1 := by
      split_ifs <;> rfl
    simp only [hpoint, sum_const, card_univ, smul_eq_mul, mul_one]
  rw [H.covered_color_count c v] at hsum
  omega

theorem special_palette_incident_lower (H : SetHypergraph V) (c : H.EdgeColoring C)
    (S : Finset C) (bad : C) (v : V)
    (hcover : ∀ a ∈ S, a ≠ bad → v ∈ H.coveredVertices {e | c e = a}) :
    S.card ≤ (H.incidentEdges v).ncard + 1 := by
  classical
  have hpoint (a : C) (ha : a ∈ S) : 1 ≤
      (if v ∈ H.coveredVertices {e | c e = a} then 1 else 0) + (if a = bad then 1 else 0 : ℕ) := by
    by_cases hab : a = bad
    · simp only [hab, ↓reduceIte]; omega
    · simp only [hcover a ha hab, hab, ↓reduceIte, Nat.add_zero, le_refl]
  have hsum := sum_le_sum hpoint
  have hpart : (∑ a ∈ S, if v ∈ H.coveredVertices {e | c e = a} then 1 else 0) ≤
      (H.incidentEdges v).ncard := by
    rw [← H.covered_color_count c v]
    exact sum_le_sum_of_subset (subset_univ _)
  have hbad : (∑ a ∈ S, if a = bad then 1 else 0 : ℕ) ≤ 1 := by
    rw [sum_ite_eq']
    split_ifs <;> omega
  simp only [sum_const, smul_eq_mul, mul_one, sum_add_distrib] at hsum
  omega

theorem active_absences_le_all (H : SetHypergraph V) (c : H.EdgeColoring C)
    (p : ℕ) (index : Fin p ↪ C) (v : V) :
    (∑ i : Fin p, if v ∈ H.coveredVertices {e | c e = index i} then 0 else 1) ≤
      Fintype.card C - (H.incidentEdges v).ncard := by
  classical
  rw [← H.all_color_absences c v]
  calc
    _ = ∑ a ∈ univ.map index, if v ∈ H.coveredVertices {e | c e = a} then 0 else 1 := by
      rw [sum_map]
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

theorem active_requests_le_of_incident_lower (H : SetHypergraph V)
    (m p : ℕ) (c : H.EdgeColoring (Fin m)) (index : Fin p ↪ Fin m) (U : Set V) (q : ℕ)
    (hdegree : ∀ v ∈ U, m ≤ (H.incidentEdges v).ncard + q) :
    ∀ v, (∑ i : Fin p, if v ∈ U \ H.coveredVertices {e | c e = index i} then 1 else 0) ≤ q := by
  intro v
  by_cases hvU : v ∈ U
  · have hsum := H.active_absences_le_all c p index v
    have hd := hdegree v hvU
    simp only [Fintype.card_fin] at hsum
    have hpoint (i : Fin p) :
        (if v ∈ U \ H.coveredVertices {e | c e = index i} then 1 else 0 : ℕ) =
        (if v ∈ H.coveredVertices {e | c e = index i} then 0 else 1) := by
      by_cases hv : v ∈ H.coveredVertices {e | c e = index i} <;> simp [hvU, hv]
    simp_rw [hpoint]
    omega
  · have hpoint (i : Fin p) : v ∉ U \ H.coveredVertices {e | c e = index i} :=
      fun h ↦ hvU h.1
    simp only [hpoint, ↓reduceIte, sum_const_zero, Nat.zero_le]

theorem graph_degree_le_colored_incidence_add_residual (H J : SetHypergraph V)
    (hJH : J ⊆ H) (R : _root_.SimpleGraph V) (hrest : (H \ J).twoGraph ≤ R) (v : V) :
    (H.twoGraph.neighborSet v).ncard ≤ (J.incidentEdges v).ncard + (R.neighborSet v).ncard := by
  have hsub : J.twoGraph.neighborSet v ⊆ H.twoGraph.neighborSet v :=
    fun _ h ↦ ⟨h.1, hJH h.2⟩
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hrestCount : (H.twoGraph.neighborSet v \ J.twoGraph.neighborSet v).ncard ≤
      (R.neighborSet v).ncard := by
    apply Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro w hw
    apply hrest
    rw [H.twoGraph_sdiff J]
    exact hw
  have hJcount := J.pair_degree_le_incident_degree J (fun _ he _ ↦ he) v
  omega

#print axioms active_requests_le_of_incident_lower
#print axioms graph_degree_le_colored_incidence_add_residual

end Erdos19.SetHypergraph
