import ErdosProblems.Erdos19.MissingPairs
import ErdosProblems.Erdos19.SupportedSmallVolume

/-! # Coloring the large-edge part when the graph part is nearly complete

The support is allowed to be smaller than the ambient vertex set. When it
has at least one eighth of the ambient size, a sufficiently small missing-pair
count gives a coloring with at most `0.51` times the support size colors.
The numerical missing-pair threshold is explicit and deliberately generous.
-/

namespace Erdos19.SetHypergraph

theorem eventually_color_large_edges_of_few_missing_pairs :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H J : SetHypergraph (Fin n),
      H.IsLinear → J ⊆ H → (∀ e : J, 3 ≤ e.1.ncard) →
      ∀ U : Set (Fin n), (∀ e : J, e.1 ⊆ U) → n ≤ 8 * U.ncard →
      64 * (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300))) *
          H.missingOrderedPairs.card < n ^ 2 →
      ∃ q : ℕ, 100 * q ≤ 51 * U.ncard ∧ J.EdgeColorable q := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_small_pair_volume_supported (300 : ℕ) (by norm_num)
  refine ⟨8 * N₀, ?_⟩
  intro n hn H J hlinear hJH hmin U hsupport hU hmissing
  have hUlarge : N₀ ≤ U.ncard := by omega
  have hcharge := H.sum_pair_weight_le_missingOrderedPairs J hlinear hJH hmin
  have hvolume : (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300))) *
      (∑ e : J, e.1.ncard * (e.1.ncard - 1)) < U.ncard ^ 2 := by
    have hsquare : n ^ 2 ≤ 64 * U.ncard ^ 2 := by
      nlinarith only [Nat.mul_le_mul hU hU]
    have hcharge' := Nat.mul_le_mul_left
      (64 * (32 * 300 ^ 2 * (1 + 4 * 300 * (1 + 4 * 300)))) hcharge
    nlinarith only [hmissing, hsquare, hcharge']
  obtain ⟨q, hq, hc⟩ := hN₀ (Fin n) U hUlarge J (hlinear.mono hJH)
    hsupport hmin hvolume
  refine ⟨q, ?_, hc⟩
  norm_num at hq
  omega

#print axioms eventually_color_large_edges_of_few_missing_pairs

end Erdos19.SetHypergraph
