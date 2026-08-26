import ErdosProblems.Erdos19.OutlierPacking
import ErdosProblems.Erdos19.OutlierParameters
import ErdosProblems.Erdos19.NearCompleteSmallClasses
import ErdosProblems.Erdos19.SmallSupportColoring
import ErdosProblems.Erdos19.MatchingHypergraphCompletion

/-! # Coloring when the graph part has few missing pairs

No minimum-degree assumption is imposed: exceptional vertices are handled by
cross-matchings before the dense induced graph is packed.
-/

namespace Erdos19.SetHypergraph

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_color_pairComplete_of_few_missing_pairs :
    ∃ K : ℕ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → H.IsPairComplete →
      (∀ e : H, 2 ≤ e.1.ncard) → K * H.missingOrderedPairs.card < n ^ 2 →
      H.EdgeColorable n := by
  classical
  obtain ⟨delta, hd, N₀, hN₀⟩ := eventually_matching_packing_with_outliers (1 / 8) (by norm_num)
  obtain ⟨s, hs⟩ := exists_nat_gt (max 100 (100 / delta))
  have hs100 : 100 ≤ s := by
    have h : (100 : ℝ) < s := (le_max_left _ _).trans_lt hs
    exact le_of_lt (by exact_mod_cast h)
  have hspos : 0 < s := by omega
  have hds : (100 : ℝ) ≤ delta * s := by
    have h : 100 / delta ≤ (s : ℝ) := ((le_max_right _ _).trans_lt hs).le
    have h' := (div_le_iff₀ hd).mp h
    nlinarith only [h']
  obtain ⟨N₁, hN₁⟩ := eventually_small_classes_of_few_missing_pairs
  let C₀ : ℕ := 64 * (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300)))
  let K := C₀ + 1600 * s * s + 1
  refine ⟨K, by dsimp only [K]; positivity,
    max N₁ (max (4 * s * s) (max (2 * N₀) 100)), ?_⟩
  intro n hn H hlinear hcomplete hsize hmissing
  have hn₁ : N₁ ≤ n := by omega
  have hn₀ : 2 * N₀ ≤ n := by omega
  have hnscale : 4 * s * s ≤ n := by omega
  have hn100 : 100 ≤ n := by omega
  have hns : s ≤ n := by nlinarith only [hnscale, hspos]
  have hnpos : 0 < n := by omega
  by_cases hsmall : 8 * H.largePart.vertexSupport.ncard ≤ n
  · simpa only [Fintype.card_fin] using H.edgeColorable_of_support_at_most_eighth hlinear
      hcomplete hsize (by simpa only [Fintype.card_fin] using hnpos)
      (by simpa only [Fintype.card_fin] using hsmall)
  have hsupport : n ≤ 8 * H.largePart.vertexSupport.ncard := by omega
  have hmissing' (c : ℕ) (hc : c ≤ K) : c * H.missingOrderedPairs.card < n ^ 2 :=
    (Nat.mul_le_mul_right _ hc).trans_lt hmissing
  have hC₀ : C₀ ≤ K := by dsimp only [K]; omega
  have hC₁ : 1600 * s * s ≤ K := by dsimp only [K]; omega
  obtain ⟨m, color, hclasses, hm52, _, hm75⟩ := hN₁ n hn₁ s hs100 H H.largePart hlinear
    (fun _ h ↦ h.1) (fun e ↦ e.2.2) H.largePart.vertexSupport
    (fun e v hv ↦ ⟨e, hv⟩) hsupport (hmissing' C₀ hC₀) (hmissing' _ hC₁)
  let X := degreeOutliers H.twoGraph (n / s)
  let C := H.largePart.colorCovered color
  let U := H.largePart.vertexSupport
  have hX : X.ncard ≤ n / s := by
    apply outlier_scale_bound n s X.ncard H.missingOrderedPairs.card hspos hnscale
    · have hcoef : 4 * s * s ≤ K := by
        have h : 4 * s * s ≤ 1600 * s * s :=
          Nat.mul_le_mul_right s (Nat.mul_le_mul_right s (by norm_num))
        exact h.trans hC₁
      simpa only [pow_two] using hmissing' _ hcoef
    · exact H.twoGraph_degreeOutliers_markov n (n / s)
  have hsplit : Xᶜ.ncard + X.ncard = n := by
    have h := Set.ncard_add_ncard_compl X
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, add_comm] using h
  have hb : Xᶜ.ncard = n - X.ncard := by omega
  have hbR : (Xᶜ.ncard : ℝ) = (n : ℝ) - X.ncard := by
    have h : (Xᶜ.ncard : ℝ) + X.ncard = n := by exact_mod_cast hsplit
    linarith only [h]
  have hscale : 100 * (n / s) ≤ n :=
    (Nat.mul_le_mul_right _ hs100).trans (Nat.mul_div_le n s)
  obtain ⟨hmn, hmslack, hroom, hmargin⟩ := outlier_integer_margins n s X.ncard U.ncard m
    hs100 hn100 hX hsupport hm52 hm75
  obtain ⟨hsmallR, hincR⟩ := outlier_real_margins delta hd n s X.ncard hs100 hns hX hds
  rw [← hbR] at hsmallR hincR
  have hbudget (v : Fin n) : (H.twoGraph.neighborSet v).ncard +
      (∑ i : Fin m, if v ∈ C i then 1 else 0) + (if v ∈ U then 1 else 0) ≤ n - 1 := by
    simpa only [Fintype.card_fin] using
      H.large_coloring_parity_degree_budget hlinear hcomplete hsize color v
  have hG (v : ↥(Xᶜ)) : (1 - delta) * Xᶜ.ncard ≤ ((H.twoGraph.induce Xᶜ).degree v : ℝ) := by
    have hbulk := degreeOutliers_bulk_degree H.twoGraph (n / s) v
    have hbulkR : (Xᶜ.ncard : ℝ) ≤
        ((H.twoGraph.induce Xᶜ).neighborSet v).ncard + (n / s : ℕ) := by exact_mod_cast hbulk
    simp only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    have hsmallR' := hsmallR
    push_cast at hsmallR'
    have hxnonneg : (0 : ℝ) ≤ X.ncard := by positivity
    nlinarith only [hbulkR, hsmallR', hxnonneg]
  obtain ⟨M, hM, hMd, hMb⟩ := hN₀ (Fin n) X (by omega) H.twoGraph hG m
    (by simpa only [Fintype.card_fin] using hmn)
    (by
      rw [← hb] at hmslack
      have h : (8 : ℝ) * m ≤ 7 * Xᶜ.ncard := by exact_mod_cast hmslack
      linarith only [h]) C U (n / s) (8 * X.ncard + 1) (by omega) hclasses
    (by
      have hcut := Set.ncard_le_ncard_sdiff_add_ncard U X
      omega)
    (by simpa only [Fintype.card_fin] using hmargin) hsmallR
    (by
      intro v
      have hv : n ≤ (H.twoGraph.neighborSet v.1).ncard + n / s := by
        have hnot := v.2
        change ¬(H.twoGraph.neighborSet v.1).ncard + n / s < Fintype.card (Fin n) at hnot
        simpa only [Fintype.card_fin] using Nat.le_of_not_lt hnot
      have hbv := hbudget v.1
      have hc : (∑ i : Fin m, if v.1 ∈ C i then 1 else 0) ≤ n / s := by omega
      have hle := Nat.add_le_add_right (Nat.add_le_add_right hc (8 * X.ncard + 1)) 1
      exact (Nat.cast_le.mpr hle).trans hincR)
    (by simpa only [Fintype.card_fin] using hbudget)
  have hrest : ∀ e : H, e.1 ∉ H.largePart → e.1.ncard = 2 := by
    intro e he
    have hlo := hsize e
    have hhi : ¬3 ≤ e.1.ncard := fun h ↦ he ⟨e.2, h⟩
    omega
  have havoid : ∀ e : H.largePart, ∀ v ∈ e.1, v ∉ (M (color.color e)).verts := by
    intro e v hv hMv
    exact (hM (color.color e)).2 hMv ⟨e, rfl, hv⟩
  have hMbudget (v : Fin n) : (H.twoGraph.neighborSet v).ncard +
      (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤ n - m - 1 + m := by
    have h := hMb v
    simp only [Fintype.card_fin] at h
    omega
  have hcolor := H.edgeColorable_of_avoiding_matching_family H.largePart (fun _ h ↦ h.1)
    hrest m (n - m - 1) color M (fun i ↦ (hM i).1) hMd havoid hMbudget
  have hpalette : m + (n - m - 1 + 1) = n := by omega
  simpa only [hpalette] using hcolor

#print axioms eventually_color_pairComplete_of_few_missing_pairs

theorem missingOrderedPairs_antitone {V : Type*} [Fintype V]
    {H J : SetHypergraph V} (hHJ : H ⊆ J) :
    J.missingOrderedPairs ⊆ H.missingOrderedPairs := by
  classical
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hp'.1, ?_⟩
  intro hadj
  exact hp'.2 ⟨hadj.1, hHJ hadj.2⟩

theorem eventually_color_of_few_missing_pairs :
    ∃ K : ℕ, 0 < K ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) → K * H.missingOrderedPairs.card < n ^ 2 →
      H.EdgeColorable n := by
  obtain ⟨K, hK, N, hN⟩ := eventually_color_pairComplete_of_few_missing_pairs
  refine ⟨K, hK, N, ?_⟩
  intro n hn H hlinear hsize hmissing
  have hJlinear : H.pairCompletion.IsLinear := pairCompletion_isLinear hlinear
  have hJsize : ∀ e : H.pairCompletion, 2 ≤ e.1.ncard := fun e ↦
    pairCompletion_min_size (fun e he ↦ hsize ⟨e, he⟩) e.1 e.2
  have hJmissing : K * H.pairCompletion.missingOrderedPairs.card < n ^ 2 :=
    (Nat.mul_le_mul_left K (Finset.card_le_card
      (missingOrderedPairs_antitone H.subset_pairCompletion))).trans_lt hmissing
  exact (hN n hn H.pairCompletion hJlinear H.pairCompletion_isPairComplete hJsize hJmissing).of_subset
    H.subset_pairCompletion

theorem eventually_color_of_small_missing_pair_density :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) →
      (H.missingOrderedPairs.card : ℝ) < epsilon * (n : ℝ) ^ 2 → H.EdgeColorable n := by
  obtain ⟨K, hK, N, hN⟩ := eventually_color_of_few_missing_pairs
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨1 / K, by positivity, N, ?_⟩
  intro n hn H hlinear hsize hmissing
  apply hN n hn H hlinear hsize
  have h := mul_lt_mul_of_pos_left hmissing hKR
  have hreal : (K : ℝ) * H.missingOrderedPairs.card < (n : ℝ) ^ 2 := by
    simpa only [← mul_assoc, mul_one_div_cancel hKR.ne', one_mul] using h
  exact_mod_cast hreal

#print axioms eventually_color_of_few_missing_pairs
#print axioms eventually_color_of_small_missing_pair_density

end Erdos19.SetHypergraph
