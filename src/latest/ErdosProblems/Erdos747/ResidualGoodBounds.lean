import ErdosProblems.Erdos747.ResidualDegreeBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Explicit inheritance of the complete residual entropy certificate -/

lemma kahnAggregateInsertionGood_reindexGraphAway_explicit
    {n M cap : ℕ} {H : Finset (Edge n)} {Z : Edge n} {C c B q eta g : ℝ}
    (hn : 2 ≤ n) (hZ : Z ∈ allEdges n) (hc : 0 < c)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hg : 0 ≤ g)
    (hmean : 1 ≤ (M : ℝ) / n) (hsize : 6 * (B + 1) ≤ n)
    (hcap : (cap : ℝ) / ((M : ℝ) / n) ≤ g)
    (hq' : residualDegreeTolerance n B q g ≤ 1)
    (hgood : KahnAggregateInsertionGood n M cap C q eta B H)
    (hweight : c^2 * matchingWeightTarget n H ≤ completionWeight H Z) :
    KahnAggregateInsertionGood (n - 1) (reindexGraphAway H Z hZ).card cap
        (residualCountError n C c) (residualDegreeTolerance n B q g)
        (2 * eta) (2 * B) (reindexGraphAway H Z hZ) ∧
      (cap : ℝ) / (((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 2 * g ∧
      ((M : ℝ) / n) / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((n - 1 : ℕ) : ℝ) := by
  rcases hgood with ⟨hH, hpm, hcount, hcodeg, hreg⟩
  have hM : 0 < M := by
    by_contra hbad
    have hz : M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hmean
    norm_num at hmean
  have hPhi : (perfectMatchings n H).card ≠ 0 :=
    Finset.card_ne_zero.mpr (hasPerfectMatching_iff_perfectMatchings_nonempty.mp hpm)
  have hpm' := hasPerfectMatching_reindexGraphAway_of_weightLower hn
    (by simpa only [(mem_sample.mp hH).2] using hM) hZ hPhi hc hweight
  have hcount' := kahnCountLower_reindexGraphAway_explicit_error hn hM hH hZ hc
    hPhi hcount hweight
  rcases degreeAggregateRegular_reindexGraphAway_explicit hn hH hZ
    hB hq heta hg hmean hsize hcap hcodeg hreg hq' with ⟨hreg', hcap', hmean', -⟩
  refine ⟨⟨mem_sample.mpr ⟨reindexGraphAway_subset_allEdges hZ (mem_sample.mp hH).1, rfl⟩,
    hpm', hcount', ?_, hreg'⟩, hcap', hmean'⟩
  intro u v huv
  rw [vertexCodegree_reindexGraphAway]
  exact (vertexCodegree_inducedAway_le H Z _ _).trans
    (hcodeg _ _ (fun h ↦ huv ((outsideVertexEquiv Z hZ).symm.injective (Subtype.ext h))))

lemma residualAggregateInheritanceGood_explicit
    {n M d D cap : ℕ} {a B q eta C c g : ℝ} {H : Finset (Edge n)}
    (hn : 2 ≤ n) (hc : 0 < c)
    (hB : 0 ≤ B) (hq : 0 ≤ q) (heta : 0 ≤ eta) (hg : 0 ≤ g)
    (hmean : 1 ≤ (M : ℝ) / n) (hsize : 6 * (B + 1) ≤ n)
    (hcap : (cap : ℝ) / ((M : ℝ) / n) ≤ g)
    (hq' : residualDegreeTolerance n B q g ≤ 1)
    (hH : H ∈ sample n M)
    (hreg : AggregateLayerRegular n M cap a B q eta B H)
    (hpositive : 0 < (n : ℝ) * Real.log ((M : ℝ) / n) - 2 * n - C * n)
    (hcount : KahnCountLower H C)
    (hlower : ((d + 3 * cap : ℕ) : ℝ) ≤ a * ((M : ℝ) / n))
    (hupper : B * ((M : ℝ) / n) ≤ D) :
    ResidualAggregateInheritanceGood n M d D cap c C (residualCountError n C c)
      (residualDegreeTolerance n B q g) (2 * eta) (2 * B) H := by
  have hgood := kahnAggregateInsertionGood_of_aggregateLayerRegular hH hreg hpositive hcount
  have hPhi : (perfectMatchings n H).card ≠ 0 :=
    Finset.card_ne_zero.mpr (hasPerfectMatching_iff_perfectMatchings_nonempty.mp hgood.2.1)
  have hM : 0 < M := by
    by_contra hbad
    have hz : M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_div] at hmean
    norm_num at hmean
  refine ⟨hPhi, hcount, ?_, ?_, hreg.2.2.1, ?_⟩
  · intro v
    have h : ((d + 3 * cap : ℕ) : ℝ) < vertexDegree H v := hlower.trans_lt (hreg.1 v)
    have hnat : d + 3 * cap < vertexDegree H v := by exact_mod_cast h
    omega
  · intro v
    have h : (vertexDegree H v : ℝ) < D := (hreg.2.1 v).trans_le hupper
    exact le_of_lt (by exact_mod_cast h)
  · intro Z hZ hweight
    have hres := kahnAggregateInsertionGood_reindexGraphAway_explicit hn hZ hc
      hB hq heta hg hmean hsize hcap hq' hgood hweight
    have hJpos : 0 < (reindexGraphAway H Z hZ).card := by
      obtain ⟨F, hFsub, hFcard, -⟩ := hres.1.2.1
      have hFle := Finset.card_le_card hFsub
      omega
    have hJM : (reindexGraphAway H Z hZ).card ≤ M := by
      rw [card_reindexGraphAway]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (mem_sample.mp hH).2
    exact ⟨residualCountError_budget n M _ C c hn hM hJpos hJM hc, hres.1.2.2.2.2⟩

end

end Erdos747
