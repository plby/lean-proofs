import ErdosProblems.Erdos745.SprinklingGeometry
import ErdosProblems.Erdos745.ComponentExponential

/-! # The finite conditional sprinkling cut bound -/

open scoped BigOperators Sym2

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos746.BernoulliFinset

def NoEdgesAcross {n : ℕ} (H : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ T, ¬ H.Adj u v

theorem noEdgesAcross_iff_cut {n : ℕ} (H : SimpleGraph (Fin n))
    (S T : Finset (Fin n)) (hST : Disjoint S T) :
    NoEdgesAcross H S T ↔ Disjoint (Erdos746.crossingEdges S T hST) (edgeCoordinates H) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h e he hH
    obtain ⟨u, hu, v, hv, heq⟩ := (Erdos746.mem_crossingEdges_iff hST e).mp he
    rw [mem_edgeCoordinates, heq, SimpleGraph.mem_edgeSet] at hH
    exact h u hu v hv hH
  · intro h u hu v hv huv
    let e : Edge n := ⟨s(u, v), by simpa using huv.ne⟩
    have he : e ∈ Erdos746.crossingEdges S T hST :=
      (Erdos746.mem_crossingEdges_iff hST e).mpr ⟨u, hu, v, hv, rfl⟩
    have hH : e ∈ edgeCoordinates H := by
      rw [mem_edgeCoordinates, SimpleGraph.mem_edgeSet]
      exact huv
    exact h he hH

def SeparatedPair {n : ℕ} (S T : Finset (Fin n)) (t : ℝ) (B : Finset (Edge n)) : Prop :=
  Disjoint S T ∧ t ≤ (S.card : ℝ) ∧ t ≤ (T.card : ℝ) ∧
    NoEdgesAcross (Erdos746.graphOfEdges B) S T

theorem eventMass_separatedPair_le {n : ℕ} {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (S T : Finset (Fin n)) :
    eventMass Finset.univ q (SeparatedPair S T t) ≤ Real.exp (-q * t ^ 2) := by
  by_cases hvalid : Disjoint S T ∧ t ≤ (S.card : ℝ) ∧ t ≤ (T.card : ℝ)
  · have hsub : eventMass Finset.univ q (SeparatedPair S T t) ≤
        eventMass Finset.univ q (fun B ↦ Disjoint (Erdos746.crossingEdges S T hvalid.1) B) := by
      apply eventMass_mono _ hq0 hq1
      intro B hB
      have h := (noEdgesAcross_iff_cut (Erdos746.graphOfEdges B) S T hvalid.1).mp hB.2.2.2
      simpa only [edgeCoordinates_graphOfEdges] using h
    apply hsub.trans
    rw [eventMass_avoids (Finset.subset_univ _), Erdos746.card_crossingEdges]
    apply (absence_pow_le_exp hq1 (S.card * T.card)).trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul hvalid.2.1 hvalid.2.2 ht (Nat.cast_nonneg S.card)
    push_cast
    have hq := mul_le_mul_of_nonneg_left hm hq0
    nlinarith
  · have hevent : SeparatedPair S T t = (fun _ ↦ False) := by
      funext B
      apply propext
      exact ⟨fun h ↦ hvalid ⟨h.1, h.2.1, h.2.2.1⟩, False.elim⟩
    rw [hevent, eventMass_false]
    exact Real.exp_nonneg _

/-- Two unions of large base components with no sprinkled edge between them. -/
def SeparatedLargeUnions {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) (t : ℝ)
    (B : Finset (Edge n)) : Prop :=
  ∃ J ∈ (largeBaseComponents G K).powerset,
    ∃ L ∈ (largeBaseComponents G K).powerset,
      SeparatedPair (componentUnion J) (componentUnion L) t B

theorem eventMass_separatedLargeUnions_le {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ)
    {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    eventMass Finset.univ q (SeparatedLargeUnions G K t) ≤
      (4 : ℝ) ^ (largeBaseComponents G K).card * Real.exp (-q * t ^ 2) := by
  let I := (largeBaseComponents G K).powerset
  calc
    _ ≤ ∑ J ∈ I, eventMass Finset.univ q
        (fun B ↦ ∃ L ∈ I, SeparatedPair (componentUnion J) (componentUnion L) t B) :=
      eventMass_exists_mem_le_sum _ hq0 hq1 _ _
    _ ≤ ∑ J ∈ I, ∑ L ∈ I, eventMass Finset.univ q
        (SeparatedPair (componentUnion J) (componentUnion L) t) :=
      Finset.sum_le_sum (fun J _ ↦ eventMass_exists_mem_le_sum _ hq0 hq1 _ _)
    _ ≤ ∑ _J ∈ I, ∑ _L ∈ I, Real.exp (-q * t ^ 2) :=
      Finset.sum_le_sum (fun J _ ↦ Finset.sum_le_sum
        (fun L _ ↦ eventMass_separatedPair_le hq0 hq1 ht _ _))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, I, Finset.card_powerset, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [← mul_assoc, ← mul_pow]
      norm_num

theorem eventMass_separatedLargeUnions_le_exp {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ)
    {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    eventMass Finset.univ q (SeparatedLargeUnions G K t) ≤
      Real.exp (Real.log 4 * ((n : ℝ) / (K + 1)) - q * t ^ 2) := by
  apply (eventMass_separatedLargeUnions_le G K hq0 hq1 ht).trans
  have hM : ((largeBaseComponents G K).card : ℝ) ≤ (n : ℝ) / (K + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have h := largeBaseComponents_budget G K
    have hr : ((K : ℝ) + 1) * (largeBaseComponents G K).card ≤ n := by exact_mod_cast h
    nlinarith
  have hfour : (4 : ℝ) ^ (largeBaseComponents G K).card =
      Real.exp (Real.log 4 * ((largeBaseComponents G K).card : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hfour, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  nlinarith [mul_le_mul_of_nonneg_left hM hlog]

end

end Erdos745
