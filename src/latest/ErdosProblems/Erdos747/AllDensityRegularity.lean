import ErdosProblems.Erdos747.BernoulliConditioning

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## All-density concentration on ordinary fixed-size subsets -/

/-- Forgetting subtype proofs commutes with intersecting with a prescribed
ordinary subset of the ambient finite set. -/
lemma finsetSubtypeVal_inter_ofSubset {α : Type*}
    (s G : Finset α) (H : Finset ↥s) :
    finsetSubtypeVal s (H ∩ finsetSubtypeOfSubset s G) =
      finsetSubtypeVal s H ∩ G := by
  ext x
  simp only [finsetSubtypeVal, finsetSubtypeOfSubset, Finset.mem_map,
    Finset.mem_inter, Finset.mem_filter, Finset.mem_attach]
  constructor
  · rintro ⟨y, ⟨hyH, -, hyG⟩, rfl⟩
    exact ⟨⟨y, hyH, rfl⟩, hyG⟩
  · rintro ⟨⟨y, hyH, rfl⟩, hyG⟩
    exact ⟨y, ⟨hyH, trivial, hyG⟩, rfl⟩

/-- All-density Chernoff upper tail for an ordinary subset `G ⊆ s` in a
uniform `M`-subset of `s`. -/
lemma powersetCardOrdinaryHit_upper_tail_exp_le {α : Type*}
    (s G : Finset α) (M : ℕ) (theta k : ℝ)
    (hG : G ⊆ s) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (s.powersetCard M)
        (fun H ↦ k ≤ ((H ∩ G).card : ℝ)) ≤
      (s.card + 1 : ℝ) *
        Real.exp ((G.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp theta - 1) - theta * k) := by
  let Gs : Finset ↥s := finsetSubtypeOfSubset s G
  have hGsCard : Gs.card = G.card := by
    rw [← card_finsetSubtypeVal s Gs]
    exact congrArg Finset.card (finsetSubtypeVal_ofSubset s G hG)
  have hraw := powersetCardHitCount_upper_tail_exp_le
    s M Gs theta k hs hM htheta
  have htransport := finsetProbability_powersetSubtypeVal s M
    (fun H ↦ k ≤ ((H ∩ G).card : ℝ))
  calc
    finsetProbability (s.powersetCard M)
        (fun H ↦ k ≤ ((H ∩ G).card : ℝ)) =
      finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ k ≤
          ((finsetSubtypeVal s H ∩ G).card : ℝ)) := htransport.symm
    _ = finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ k ≤ ((H ∩ Gs).card : ℝ)) := by
      apply finsetProbability_congr_event
      intro H _
      rw [← card_finsetSubtypeVal s (H ∩ Gs),
        finsetSubtypeVal_inter_ofSubset]
    _ ≤ (s.card + 1 : ℝ) *
        Real.exp ((Gs.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp theta - 1) - theta * k) := hraw
    _ = (s.card + 1 : ℝ) *
        Real.exp ((G.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp theta - 1) - theta * k) := by rw [hGsCard]

/-- All-density Chernoff lower tail for an ordinary subset `G ⊆ s` in a
uniform `M`-subset of `s`. -/
lemma powersetCardOrdinaryHit_lower_tail_exp_le {α : Type*}
    (s G : Finset α) (M : ℕ) (theta k : ℝ)
    (hG : G ⊆ s) (hs : s.Nonempty) (hM : M ≤ s.card)
    (htheta : 0 ≤ theta) :
    finsetProbability (s.powersetCard M)
        (fun H ↦ ((H ∩ G).card : ℝ) ≤ k) ≤
      (s.card + 1 : ℝ) *
        Real.exp ((G.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp (-theta) - 1) + theta * k) := by
  let Gs : Finset ↥s := finsetSubtypeOfSubset s G
  have hGsCard : Gs.card = G.card := by
    rw [← card_finsetSubtypeVal s Gs]
    exact congrArg Finset.card (finsetSubtypeVal_ofSubset s G hG)
  have hraw := powersetCardHitCount_lower_tail_exp_le
    s M Gs theta k hs hM htheta
  have htransport := finsetProbability_powersetSubtypeVal s M
    (fun H ↦ ((H ∩ G).card : ℝ) ≤ k)
  calc
    finsetProbability (s.powersetCard M)
        (fun H ↦ ((H ∩ G).card : ℝ) ≤ k) =
      finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ ((finsetSubtypeVal s H ∩ G).card : ℝ) ≤ k) :=
      htransport.symm
    _ = finsetProbability ((Finset.univ : Finset ↥s).powersetCard M)
        (fun H ↦ ((H ∩ Gs).card : ℝ) ≤ k) := by
      apply finsetProbability_congr_event
      intro H _
      rw [← card_finsetSubtypeVal s (H ∩ Gs),
        finsetSubtypeVal_inter_ofSubset]
    _ ≤ (s.card + 1 : ℝ) *
        Real.exp ((Gs.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp (-theta) - 1) + theta * k) := hraw
    _ = (s.card + 1 : ℝ) *
        Real.exp ((G.card : ℝ) * ((M : ℝ) / s.card) *
          (Real.exp (-theta) - 1) + theta * k) := by rw [hGsCard]

/-! ### Hypergraph degree and codegree consequences -/

lemma allEdges_nonempty (n : ℕ) (hn : 0 < n) :
    (allEdges n).Nonempty := by
  let i : Fin n := ⟨0, hn⟩
  exact ⟨canonicalEdge n i,
    mem_allEdges.mpr (canonicalEdge_card n i)⟩

lemma vertexDegree_eq_card_inter_incidentEdges {n : ℕ}
    {H : Finset (Edge n)} (v : Vertex n) (hH : H ⊆ allEdges n) :
    vertexDegree H v = (H ∩ incidentEdges n v).card := by
  apply congrArg Finset.card
  ext A
  simp only [vertexDegree, incidentEdges, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro ⟨hA, hv⟩
    exact ⟨hA, hH hA, hv⟩
  · rintro ⟨hA, -, hv⟩
    exact ⟨hA, hv⟩

lemma vertexCodegree_eq_card_inter_pairIncidentEdges {n : ℕ}
    {H : Finset (Edge n)} (u v : Vertex n) (hH : H ⊆ allEdges n) :
    vertexCodegree H u v = (H ∩ pairIncidentEdges n u v).card := by
  apply congrArg Finset.card
  ext A
  simp only [vertexCodegree, pairIncidentEdges, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro ⟨hA, hu, hv⟩
    exact ⟨hA, hH hA, hu, hv⟩
  · rintro ⟨hA, -, hu, hv⟩
    exact ⟨hA, hu, hv⟩

/-- Arbitrary exponential upper tail for one vertex degree in the uniform
fixed-edge random hypergraph, with no density restriction on `M`. -/
lemma sampledVertexDegree_upper_tail_exp_le
    (n M : ℕ) (v : Vertex n) (theta k : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ k ≤ (vertexDegree H v : ℝ)) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (Real.exp theta - 1) -
          theta * k) := by
  have hraw := powersetCardOrdinaryHit_upper_tail_exp_le
    (allEdges n) (incidentEdges n v) M theta k
    (incidentEdges_subset n v) (allEdges_nonempty n hn) hM htheta
  have hdec :
      (fun A B : Edge n ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Edge n)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  have hmean :
      ((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) = (M : ℝ) / n := by
    calc
      ((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) =
        (M : ℝ) *
          ((incidentEdges n v).card / (allEdges n).card) := by ring
      _ = (M : ℝ) * (1 / (n : ℝ)) := by
        rw [incidentEdges_density n v hn]
      _ = (M : ℝ) / n := by ring
  calc
    finsetProbability (sample n M)
        (fun H ↦ k ≤ (vertexDegree H v : ℝ)) =
      finsetProbability (sample n M)
        (fun H ↦ k ≤ ((H ∩ incidentEdges n v).card : ℝ)) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [vertexDegree_eq_card_inter_incidentEdges v
        (Finset.mem_powersetCard.mp hH).1]
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        Real.exp (((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) *
            (Real.exp theta - 1) - theta * k) := by
      simpa only [sample] using hraw
    _ = ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (Real.exp theta - 1) -
          theta * k) := by rw [hmean]

/-- Arbitrary exponential lower tail for one vertex degree in the uniform
fixed-edge random hypergraph, with no density restriction on `M`. -/
lemma sampledVertexDegree_lower_tail_exp_le
    (n M : ℕ) (v : Vertex n) (theta k : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ (vertexDegree H v : ℝ) ≤ k) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (Real.exp (-theta) - 1) +
          theta * k) := by
  have hraw := powersetCardOrdinaryHit_lower_tail_exp_le
    (allEdges n) (incidentEdges n v) M theta k
    (incidentEdges_subset n v) (allEdges_nonempty n hn) hM htheta
  have hdec :
      (fun A B : Edge n ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Edge n)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  have hmean :
      ((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) = (M : ℝ) / n := by
    calc
      ((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) =
        (M : ℝ) *
          ((incidentEdges n v).card / (allEdges n).card) := by ring
      _ = (M : ℝ) * (1 / (n : ℝ)) := by
        rw [incidentEdges_density n v hn]
      _ = (M : ℝ) / n := by ring
  calc
    finsetProbability (sample n M)
        (fun H ↦ (vertexDegree H v : ℝ) ≤ k) =
      finsetProbability (sample n M)
        (fun H ↦ ((H ∩ incidentEdges n v).card : ℝ) ≤ k) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [vertexDegree_eq_card_inter_incidentEdges v
        (Finset.mem_powersetCard.mp hH).1]
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        Real.exp (((incidentEdges n v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) *
            (Real.exp (-theta) - 1) + theta * k) := by
      simpa only [sample] using hraw
    _ = ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) * (Real.exp (-theta) - 1) +
          theta * k) := by rw [hmean]

/-- Arbitrary exponential upper tail for a fixed pair codegree. -/
lemma sampledVertexCodegree_upper_tail_exp_le
    (n M : ℕ) (u v : Vertex n) (theta k : ℝ)
    (huv : u ≠ v) (hn : 0 < n)
    (hM : M ≤ (allEdges n).card) (htheta : 0 ≤ theta) :
    finsetProbability (sample n M)
        (fun H ↦ k ≤ (vertexCodegree H u v : ℝ)) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) *
              (Real.exp theta - 1) - theta * k) := by
  have hraw := powersetCardOrdinaryHit_upper_tail_exp_le
    (allEdges n) (pairIncidentEdges n u v) M theta k
    (pairIncidentEdges_subset n u v) (allEdges_nonempty n hn) hM htheta
  have hdec :
      (fun A B : Edge n ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Edge n)) :=
    Subsingleton.elim _ _
  rw [hdec] at hraw
  have hmean :
      ((pairIncidentEdges n u v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) =
        (M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) := by
    calc
      ((pairIncidentEdges n u v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) =
        (M : ℝ) *
          ((pairIncidentEdges n u v).card / (allEdges n).card) := by ring
      _ = (M : ℝ) * (2 / ((n : ℝ) * (3 * n - 1))) := by
        rw [pairIncidentEdges_density n huv hn]
  calc
    finsetProbability (sample n M)
        (fun H ↦ k ≤ (vertexCodegree H u v : ℝ)) =
      finsetProbability (sample n M)
        (fun H ↦ k ≤ ((H ∩ pairIncidentEdges n u v).card : ℝ)) := by
      apply finsetProbability_congr_event
      intro H hH
      rw [vertexCodegree_eq_card_inter_pairIncidentEdges u v
        (Finset.mem_powersetCard.mp hH).1]
    _ ≤ ((allEdges n).card + 1 : ℝ) *
        Real.exp (((pairIncidentEdges n u v).card : ℝ) *
          ((M : ℝ) / (allEdges n).card) *
            (Real.exp theta - 1) - theta * k) := by
      simpa only [sample] using hraw
    _ = ((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) *
              (Real.exp theta - 1) - theta * k) := by rw [hmean]

/-- Constant-factor upper degree tail, valid on every fixed-size layer. -/
lemma sampledVertexDegree_upper_factor_allDensity_le
    (n M : ℕ) (v : Vertex n) (B : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card) (hB : 1 ≤ B) :
    finsetProbability (sample n M)
        (fun H ↦ B * ((M : ℝ) / n) ≤ vertexDegree H v) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) *
          (B - 1 - B * Real.log B)) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hraw := sampledVertexDegree_upper_tail_exp_le
    n M v (Real.log B) (B * ((M : ℝ) / n))
    hn hM (Real.log_nonneg hB)
  rw [Real.exp_log hBpos] at hraw
  exact hraw.trans_eq (by congr 2 <;> ring)

/-- Constant-factor lower degree tail, valid on every fixed-size layer. -/
lemma sampledVertexDegree_lower_factor_allDensity_le
    (n M : ℕ) (v : Vertex n) (a : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    finsetProbability (sample n M)
        (fun H ↦ (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) *
          (a - 1 - a * Real.log a)) := by
  have hlog : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  have hraw := sampledVertexDegree_lower_tail_exp_le
    n M v (-Real.log a) (a * ((M : ℝ) / n))
    hn hM (by linarith)
  rw [neg_neg, Real.exp_log ha0] at hraw
  exact hraw.trans_eq (by congr 2 <;> ring)

/-- The logarithmic-parameter codegree-six tail on every layer. -/
lemma sampledVertexCodegree_six_allDensity_le
    (n M : ℕ) {u v : Vertex n} (huv : u ≠ v)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ (6 : ℝ) ≤ vertexCodegree H u v) ≤
      ((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) * ((n : ℝ) - 1) -
          Real.log (n : ℝ) * 6) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hraw := sampledVertexCodegree_upper_tail_exp_le
    n M u v (Real.log (n : ℝ)) 6 huv hn hM hlog
  rw [Real.exp_log (by positivity : (0 : ℝ) < n)] at hraw
  exact hraw

end

end Erdos747
