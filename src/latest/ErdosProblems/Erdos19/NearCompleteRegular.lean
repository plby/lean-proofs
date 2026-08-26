import ErdosProblems.Erdos19.SparseClassCompletion
import ErdosProblems.Erdos19.NearCompleteSmallClasses
import ErdosProblems.Erdos19.MissingPairDensity

/-! # The uniformly dense graph case with large support

The coloring of the large edges and all completion inputs are constructed in
the proof. The density assumption is on every graph vertex.
-/

namespace Erdos19.SetHypergraph

attribute [local instance] Classical.propDecidable

theorem eventually_color_of_dense_twoGraph_and_large_support :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → H.IsPairComplete →
      (∀ e : H, 2 ≤ e.1.ncard) →
      (∀ v, (1 - delta) * n ≤ (H.twoGraph.degree v : ℝ)) →
      n ≤ 8 * H.largePart.vertexSupport.ncard → H.EdgeColorable n := by
  classical
  obtain ⟨delta₀, hd₀, N₀, hN₀⟩ := eventually_color_of_sparse_large_coloring (1 / 4) (by norm_num)
  obtain ⟨s, hs⟩ := exists_nat_gt (max 100 (1 / delta₀))
  have hs100 : 100 ≤ s := by
    have h : (100 : ℝ) < s := (le_max_left _ _).trans_lt hs
    have h' : 100 < s := by exact_mod_cast h
    omega
  have hspos : 0 < s := by omega
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hscale : (1 : ℝ) ≤ delta₀ * s := by
    have h : 1 / delta₀ ≤ (s : ℝ) := ((le_max_right _ _).trans_lt hs).le
    have h' := (div_le_iff₀ hd₀).mp h
    nlinarith only [h']
  let C₀ : ℕ := 64 * (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300)))
  let C₁ : ℕ := 1600 * s * s
  let C : ℕ := C₀ + C₁ + 1
  have hC : (0 : ℝ) < C := by dsimp only [C]; positivity
  let delta := min delta₀ (1 / (2 * C))
  have hd : 0 < delta := by dsimp only [delta]; positivity
  have hdd : delta ≤ delta₀ := min_le_left _ _
  have hCd : (C : ℝ) * delta ≤ 1 / 2 := by
    have h : delta ≤ 1 / (2 * C) := min_le_right _ _
    have h' := (le_div_iff₀ (show (0 : ℝ) < 2 * C by positivity)).mp h
    nlinarith only [h']
  obtain ⟨N₁, hN₁⟩ := eventually_small_classes_of_few_missing_pairs
  refine ⟨delta, hd, max (max N₀ N₁) 1, ?_⟩
  intro n hn H hlinear hcomplete hsize hG hsupport
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn₀ : N₀ ≤ n := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hn₁ : N₁ ≤ n := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hG₀ : ∀ v, (1 - delta₀) * n ≤ (H.twoGraph.degree v : ℝ) := by
    intro v
    have h := mul_le_mul_of_nonneg_right hdd hnR.le
    nlinarith only [h, hG v]
  have hM := H.missingOrderedPairs_le_of_dense_twoGraph n delta hG
  have hmissing (c : ℕ) (hc : c ≤ C) : c * H.missingOrderedPairs.card < n ^ 2 := by
    have hcR : (c : ℝ) ≤ C := by exact_mod_cast hc
    have hcoef : (c : ℝ) * delta ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_right hcR hd.le).trans hCd
    have h₁ := mul_le_mul_of_nonneg_left hM (show (0 : ℝ) ≤ c by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n : ℝ))
    have h' : (c : ℝ) * H.missingOrderedPairs.card < (n : ℝ) ^ 2 := by
      nlinarith only [h₁, h₂, sq_pos_of_pos hnR]
    exact_mod_cast h'
  obtain ⟨m, color, hclasses, _, hroom, hslack⟩ := hN₁ n hn₁ s hs100 H H.largePart hlinear
    (fun _ h ↦ h.1) (fun e ↦ e.2.2) H.largePart.vertexSupport
    (fun e v hv ↦ ⟨e, hv⟩) hsupport
    (hmissing C₀ (by dsimp only [C]; omega))
    (hmissing C₁ (by dsimp only [C]; omega))
  have hm : (m : ℝ) ≤ (1 - 1 / 4) * n := by
    have h : (4 : ℝ) * m ≤ 3 * n := by exact_mod_cast hslack
    linarith only [h]
  have hA : ((n / s : ℕ) : ℝ) ≤ delta₀ * n := by
    apply (Nat.cast_div_le (m := n) (n := s)).trans
    apply (div_le_iff₀ hsR).mpr
    have h := mul_le_mul_of_nonneg_right hscale hnR.le
    nlinarith only [h]
  apply hN₀ n hn₀ H hlinear hcomplete hsize hG₀ m hm color
  · intro i
    exact (Nat.add_le_add_left (hclasses i) m).trans hroom
  · intro i
    have h : ((H.largePart.colorCovered color i).ncard : ℝ) ≤ (n / s : ℕ) := by
      exact_mod_cast hclasses i
    exact h.trans hA
  · exact H.largeDegree_le_of_dense_twoGraph n hlinear hcomplete hsize delta₀ hG₀

#print axioms eventually_color_of_dense_twoGraph_and_large_support

end Erdos19.SetHypergraph
