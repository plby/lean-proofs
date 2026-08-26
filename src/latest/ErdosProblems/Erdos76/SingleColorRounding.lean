import ErdosProblems.Erdos76.CappedGraph
import ErdosProblems.Erdos76.LocalAveraging
import ErdosProblems.Erdos76.UnconditionalRounding

/-! Rounding small triangle weights inside one graph. -/

open Finset
open scoped BigOperators

namespace Erdos76.SingleColorRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

noncomputable def triangleHypergraph (G : SimpleGraph V) :
    FiniteHypergraph (Finset V) (LPDuality.TriangleIndex G) where
  vertexSet := univ.powersetCard 2
  support t := triangleEdgeSet t.val
  support_subset_vertexSet t := triangleEdgeSet_subset_univ_edges t.val

lemma triangleHypergraph_uniform (G : SimpleGraph V) : (triangleHypergraph G).IsUniform 3 :=
  fun t ↦ card_triangleEdgeSet t.property.card_eq

lemma vertexLoad_pair (G : SimpleGraph V) (w : Finset V → ℝ) {a b : V} (hab : a ≠ b) :
    (triangleHypergraph G).vertexLoad (fun t ↦ w t.val) {a, b} =
      fractionalEdgeLoad G w s(a, b) := by
  have hpair : ∀ t : Finset V, {a, b} ∈ triangleEdgeSet t ↔ s(a, b) ∈ t.sym2 := by
    intro t
    simp [triangleEdgeSet, mem_powersetCard, insert_subset_iff, singleton_subset_iff,
      hab, mk_mem_sym2_iff]
  simp only [FiniteHypergraph.vertexLoad, triangleHypergraph, sum_filter, hpair,
    fractionalEdgeLoad]
  exact (sum_subtype (G.cliqueFinset 3) (fun t ↦ SimpleGraph.mem_cliqueFinset_iff)
    (fun t ↦ if s(a, b) ∈ t.sym2 then w t else 0)).symm

lemma fractionalMatching_of_packing {G : SimpleGraph V} {w : Finset V → ℝ}
    (hw : IsFractionalPacking G w) :
    (triangleHypergraph G).IsFractionalMatching (fun t ↦ w t.val) := by
  constructor
  · intro t
    exact hw.1 t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property)
  · intro e he
    have hecard : e.card = 2 := (mem_powersetCard.mp he).2
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hecard
    rw [vertexLoad_pair G w hab]
    by_cases hadj : G.Adj a b
    · exact hw.2 _ (SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hadj))
    · have hzero : fractionalEdgeLoad G w s(a, b) = 0 := by
        apply sum_eq_zero
        intro t ht
        have hc := SimpleGraph.mem_cliqueFinset_iff.mp (mem_filter.mp ht).1
        have hm := mk_mem_sym2_iff.mp (mem_filter.mp ht).2
        exact (hadj (hc.isClique hm.1 hm.2 hab)).elim
      rw [hzero]
      norm_num

lemma pairLoad_le {G : SimpleGraph V} {w : Finset V → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hw : ∀ t ∈ G.cliqueFinset 3, w t ≤ μ)
    {e f : Finset V} (hef : e ≠ f) :
    (triangleHypergraph G).pairLoad (fun t ↦ w t.val) e f ≤ μ := by
  let U := (univ : Finset (LPDuality.TriangleIndex G)).filter fun t ↦
    e ∈ triangleEdgeSet t.val ∧ f ∈ triangleEdgeSet t.val
  have hU : U.card ≤ 1 := by
    rw [card_le_one]
    intro s hs t ht
    simp only [U, mem_filter, mem_univ, true_and] at hs ht
    apply Subtype.ext
    exact two_pairs_determine_triangle hef hs.1 hs.2 ht.1 ht.2
      s.property.card_eq t.property.card_eq
  change (∑ t ∈ U, w t.val) ≤ μ
  rcases U.eq_empty_or_nonempty with hempty | hne
  · simp [hempty, hμ]
  · obtain ⟨t, ht⟩ := card_eq_one.mp (Nat.le_antisymm hU hne.card_pos)
    rw [ht]
    simpa using hw t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property)

lemma matching_packing {G : SimpleGraph V} {M : Finset (LPDuality.TriangleIndex G)}
    (hM : (triangleHypergraph G).IsMatching M) :
    EdgeDisjoint (M.image Subtype.val) := by
  intro s hs t ht hst
  obtain ⟨s', hs', rfl⟩ := mem_image.mp hs
  obtain ⟨t', ht', rfl⟩ := mem_image.mp ht
  have hne : s' ≠ t' := fun h ↦ hst (congrArg Subtype.val h)
  exact inter_card_le_one_of_disjoint_triangleEdgeSet (hM hs' ht' hne)

/-- The proved weighted matching theorem rounds every sufficiently small
fractional triangle weighting, uniformly over all finite graphs. -/
theorem small_weight_rounding (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (W : Type) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) (w : Finset W → ℝ), IsFractionalPacking G w →
      (∀ t ∈ G.cliqueFinset 3, w t ≤ δ) →
      ∃ P : Finset (Finset W), (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
        fractionalSize G w ≤ (P.card : ℝ) + ζ * (Fintype.card W : ℝ) ^ 2 := by
  obtain ⟨Δ, hΔ, hround⟩ := kahnWeightedMatching 3 (by norm_num) ζ hζ
  refine ⟨Δ / 2, by positivity, ?_⟩
  intro W _ _ G w hw hcap
  have hcodeg : (triangleHypergraph G).PairCodegreeLT (fun t ↦ w t.val) Δ := by
    intro e f hef
    exact (pairLoad_le (by positivity) hcap hef).trans_lt (by linarith)
  obtain ⟨M, hM, hsize⟩ := hround (Finset W) (LPDuality.TriangleIndex G)
    (triangleHypergraph G) (fun t ↦ w t.val) (triangleHypergraph_uniform G)
    (fractionalMatching_of_packing hw) hcodeg
  refine ⟨M.image Subtype.val, ?_, matching_packing hM, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := mem_image.mp ht
    exact t'.property
  · have hcard : (M.image Subtype.val).card = M.card := card_image_of_injective M Subtype.val_injective
    have htotal : (triangleHypergraph G).totalWeight (fun t ↦ w t.val) = fractionalSize G w :=
      (sum_subtype (G.cliqueFinset 3) (fun t ↦ SimpleGraph.mem_cliqueFinset_iff) w).symm
    rw [hcard]
    rw [htotal] at hsize
    have hvertices : ((triangleHypergraph G).vertexSet.card : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by
      simp only [triangleHypergraph, card_powersetCard, card_univ, Nat.cast_choose_two]
      have hn : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
      nlinarith
    exact hsize.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvertices hζ.le))

end Erdos76.SingleColorRounding
