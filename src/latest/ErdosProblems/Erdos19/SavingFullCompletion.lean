import ErdosProblems.Erdos19.SavingCompletionWithBlocks
import ErdosProblems.Erdos19.SavingBranchReduction
import ErdosProblems.Erdos19.ControlledSavingPalette
import ErdosProblems.Erdos19.IntegerBlockReservoir
import ErdosProblems.Erdos19.LowDegreeBuffer

/-! # Unconditional completion outside the near-complete case -/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_edgeColorable_of_many_missing_pairs (s : ℕ) (hs : 0 < s) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) → n ^ 2 ≤ s * H.missingOrderedPairs.card →
      H.EdgeColorable n := by
  classical
  obtain ⟨b, hb, hbs, hsaving⟩ := eventually_colorable_or_controlled_saving (2048 * s)
  have hbpos : 0 < b := by omega
  have hbpow : b ≤ b ^ 4 := Nat.le_self_pow (by omega) b
  let B := 4 * b ^ 4
  let k := 64 * b ^ 4
  let t := 64 * s * k
  let Q := 16 * (1024 * s) * t
  let w := 8 * Q
  let high := 256 * Q
  let L := 100 * k * high + t
  let r := mediumMinimumSize w b
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hkpos : 0 < k := by dsimp only [k]; positivity
  have htpos : 0 < t := by dsimp only [t]; positivity
  have hQpos : 0 < Q := by dsimp only [Q]; positivity
  have hwpos : 0 < w := by dsimp only [w]; positivity
  have hhighpos : 0 < high := by dsimp only [high]; positivity
  have hLpos : 0 < L := by dsimp only [L]; positivity
  have hBlarge : 2048 * s ≤ B := by dsimp only [B]; omega
  have hklarge : 128 * s ≤ k := by dsimp only [k]; omega
  have hk4 : 4 ≤ k := by omega
  have hBk : B ≤ k := by dsimp only [B, k]; omega
  have htlarge : 8 * s * k ≤ t :=
    Nat.mul_le_mul_right k (Nat.mul_le_mul_right s (by norm_num : 8 ≤ 64))
  have hwlarge : 512 ≤ w := by
    have hp := Nat.mul_le_mul hs htpos
    dsimp only [w, Q]
    nlinarith only [hp]
  have hr : 3 ≤ r := by
    have hp : 0 < b ^ 4 := pow_pos hbpos _
    dsimp only [r, mediumMinimumSize]
    nlinarith only [hp, hwlarge]
  obtain ⟨ell, N₀, _, hcomplete⟩ := eventually_complete_saved_palette_with_blocks r
    (1024 * s) t L hr (by omega) htpos hLpos
  obtain ⟨R, N₁, hR, _, hsave⟩ := hsaving w (16 * w) ell hwlarge (by positivity)
  obtain ⟨N₂, hpartition⟩ := eventually_exists_integer_block_reservoir k L hkpos hLpos
  let N := N₀ + N₁ + N₂ + 2 * L + high + 32 * s + w + B + 2048 * s * (4 * w ^ 2) + 1
  refine ⟨N, ?_⟩
  intro n hn H hlinear hmin hmissing
  have hn₀ : N₀ ≤ n := by dsimp only [N] at hn; omega
  have hn₁ : N₁ ≤ n := by dsimp only [N] at hn; omega
  have hn₂ : N₂ ≤ n := by dsimp only [N] at hn; omega
  have hnw : w ≤ n := by dsimp only [N] at hn; omega
  have hnB : B ≤ n := by dsimp only [N] at hn; omega
  have hnC : 2048 * s * (4 * w ^ 2) ≤ n := by dsimp only [N] at hn; omega
  have hnparams : max (2 * L) (max high (32 * s)) ≤ n := by dsimp only [N] at hn; omega
  have hnpos : 0 < n := hwpos.trans_le hnw
  rcases hsave n hn₁ H hlinear hmin with hdone | ⟨old, oldPalette, holdCard, holdControl⟩
  · exact hdone
  let fresh := n / k - 8 * (n / L)
  let m := n - fresh
  have hm : n - n / B ≤ m := by
    have hf : fresh ≤ n / B := (Nat.sub_le _ _).trans (Nat.div_le_div_left hBk hBpos)
    exact Nat.sub_le_sub_left hf n
  obtain ⟨color, S, hS, hSsize, hbounded, hnormal, hlarge⟩ :=
    (H.rankAtLeast r).exists_lifted_controlled_saving_palette n w B m R hwpos hBpos hnw hnB
      (H.rankAtLeast_linear hlinear r) old oldPalette holdCard holdControl hm
  have hScount : S.card ≤ n / (1024 * s) :=
    saving_special_count_bound n s B (4 * w ^ 2) S.card hs hBlarge hnC hSsize
  have hnum : SavingNumericalBounds n s k t w high L S.card :=
    saving_numerical_bounds n s k t w high L S.card hs htpos hklarge htlarge le_rfl le_rfl
      (by dsimp only [L]; omega) (by dsimp only [L]; omega) hnparams hScount
  let Y := degreeOutliers H.twoGraph (n / (4 * s))
  have hYsize : n / (4 * s) ≤ Y.ncard :=
    H.low_degree_buffer_card_lower n s hnpos hmissing
  have hY : ∀ v ∈ Y, n / (4 * s) ≤ (H.twoGraph.neighborSet v)ᶜ.ncard := by
    intro v hv
    have hsum := Set.ncard_add_ncard_compl (H.twoGraph.neighborSet v)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
    change (H.twoGraph.neighborSet v).ncard + n / (4 * s) < Fintype.card (Fin n) at hv
    simp only [Fintype.card_fin] at hv
    omega
  obtain ⟨z, hzLow, hzUp, hzY⟩ := hpartition n hn₂ H.twoGraph Y
  have hblocks : ∀ a, n / t ≤ (Y.toFinset.filter fun v ↦ z v = a).card := by
    intro a
    have hl := hnum.blockRoom.trans (hYsize.trans (hzY a))
    have h := Nat.le_of_mul_le_mul_left hl hkpos
    omega
  apply hcomplete n hn₀ k hk4 H hlinear hmin m color S hS (n / w) (n / (32 * s))
    (n / (4 * s)) (n / (16 * s)) (n / high) hbounded hnormal
    (fun e he ↦ hR.trans (hlarge e he)) hnum.degreeError hnum.freshPositive ?_
    hnum.paletteRoom hnum.specialSmall hnum.bufferDegreeRoom hnum.highSubset
    hnum.highLowDisjoint hnum.initialMissing hnum.finalDegreeRoom hnum.repairBuffer
    Y hY (hnum.traceRoom.trans (Nat.add_le_add_right hYsize 1))
    (hnum.specialBuffer.trans hYsize) z hzLow hzUp hblocks
  exact Nat.sub_add_cancel ((Nat.sub_le _ _).trans (Nat.div_le_self n k))

#print axioms eventually_edgeColorable_of_many_missing_pairs

end Erdos19.SetHypergraph
