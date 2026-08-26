import ErdosProblems.Erdos19.NearCompleteLargeEdges
import ErdosProblems.Erdos19.SmallClassRefinement
import ErdosProblems.Erdos19.SmallClassArithmetic

/-! # Small color classes from a small missing-pair count -/

namespace Erdos19.SetHypergraph

open Finset

theorem eventually_small_classes_of_few_missing_pairs :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℕ, 100 ≤ s →
      ∀ H J : SetHypergraph (Fin n), H.IsLinear → J ⊆ H →
      (∀ e : J, 3 ≤ e.1.ncard) → ∀ U : Set (Fin n), (∀ e : J, e.1 ⊆ U) → n ≤ 8 * U.ncard →
      64 * (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300))) *
        H.missingOrderedPairs.card < n ^ 2 →
      1600 * s * s * H.missingOrderedPairs.card < n ^ 2 →
      ∃ m : ℕ, ∃ c : J.EdgeColoring (Fin m),
        (∀ i, (J.colorCovered c i).ncard ≤ n / s) ∧
        100 * m ≤ 52 * U.ncard ∧ m + n / s ≤ U.ncard ∧ 4 * m ≤ 3 * n := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_color_large_edges_of_few_missing_pairs
  refine ⟨max N₀ 1, ?_⟩
  intro n hn s hs H J hlinear hJH hmin U hsupport hU hmissing hmissing'
  have hnpos : 0 < n := by omega
  have hspos : 0 < s := by omega
  have hUle : U.ncard ≤ n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using Set.ncard_le_card U
  have hweight := H.sum_pair_weight_le_missingOrderedPairs J hlinear hJH hmin
  have hsize : ∀ e : J, e.1.ncard ≤ n / s := by
    intro e
    have hsingle : e.1.ncard * (e.1.ncard - 1) ≤
        ∑ f : J, f.1.ncard * (f.1.ncard - 1) :=
      single_le_sum (f := fun f : J ↦ f.1.ncard * (f.1.ncard - 1))
        (fun _ _ ↦ Nat.zero_le _) (mem_univ e)
    have hsmall : 2 * s * s * (e.1.ncard * (e.1.ncard - 1)) < n * n := by
      have h₁ := Nat.mul_le_mul_left (2 * s * s) (hsingle.trans hweight)
      have h₂ : 2 * s * s * H.missingOrderedPairs.card ≤
          1600 * s * s * H.missingOrderedPairs.card := by
        gcongr
        norm_num
      nlinarith only [h₁, h₂, hmissing']
    exact edge_size_le_small_class_scale n s e.1.ncard hspos (by have h := hmin e; omega) hsmall
  have hincidence : (∑ e : J, e.1.ncard) ≤ H.missingOrderedPairs.card := by
    apply le_trans _ hweight
    apply sum_le_sum
    intro e _
    have h : 1 ≤ e.1.ncard - 1 := by have h' := hmin e; omega
    nlinarith only [Nat.mul_le_mul_left e.1.ncard h]
  obtain ⟨q, hq, ⟨color⟩⟩ := hN₀ n ((le_max_left _ _).trans hn) H J hlinear hJH hmin
    U hsupport hU hmissing
  obtain ⟨m, c, hclasses, hm⟩ := J.exists_small_class_recoloring color (n / s) hsize
  have hm' : m ≤ q + ((∑ e : J, e.1.ncard) / (n / s + 1)) * (n / (n / s / 2 + 1)) := by
    simpa only [Fintype.card_fin] using hm
  have hvolume : 1600 * s * s * (∑ e : J, e.1.ncard) ≤ n * n := by
    have h := Nat.mul_le_mul_left (1600 * s * s) hincidence
    nlinarith only [h, hmissing']
  obtain ⟨hm52, hroom, hslack⟩ := small_class_palette_margins n s (∑ e : J, e.1.ncard)
    U.ncard q m hnpos hs hU hUle hq hvolume hm'
  exact ⟨m, c, hclasses, hm52, hroom, hslack⟩

#print axioms eventually_small_classes_of_few_missing_pairs

end Erdos19.SetHypergraph
