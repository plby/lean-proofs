import Arxiv.Arxiv2411_18291.FlatteningIterationCost
import Arxiv.Arxiv2411_18291.PaperSizeParameters
import Arxiv.Arxiv2411_18291.ExchangeConfiguration

/-!
# A limitation of the current repeated-round density estimate

At the printed threshold for triangles, the cost certificate `C^k <= n^(alpha/10)`
cannot hold for any number of rounds reducing the current recurrence to 16.
This concerns the proof's uniform cost estimate, not the existence of designs
or the existence of a more efficient flattening construction.
-/

noncomputable section

namespace Arxiv2411_18291

theorem le_flatteningStep_sq (x : ℕ) : x ≤ (flatteningStep x) ^ 2 := by
  have hs := (Nat.lt_succ_sqrt' x).le
  have hstep : x.sqrt + 1 ≤ flatteningStep x := by
    unfold flatteningStep
    omega
  exact hs.trans (Nat.pow_le_pow_left hstep 2)

theorem le_iterate_flatteningStep_pow (x k : ℕ) :
    x ≤ ((flatteningStep^[k]) x) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc
      _ ≤ ((flatteningStep^[k]) x) ^ (2 ^ k) := ih
      _ ≤ ((flatteningStep ((flatteningStep^[k]) x)) ^ 2) ^ (2 ^ k) :=
        Nat.pow_le_pow_left (le_flatteningStep_sq _) _
      _ = _ := by rw [← pow_mul]; congr 1; omega

theorem triangle_threshold_exceeds_ten_rounds :
    16 ^ (2 ^ 10) < paperSizeThreshold 3 2 := by
  let m := 90 * 3 * paperInverseAlpha 3 2
  change 16 ^ (2 ^ 10) < (4 * 3) ^ m
  calc
    _ = 4 ^ (2 * (2 ^ 10)) := by rw [show (16 : ℕ) = 4 ^ 2 by decide, ← pow_mul]
    _ < 4 ^ m := Nat.pow_lt_pow_right (by decide) (by norm_num [m, paperInverseAlpha])
    _ ≤ _ := Nat.pow_le_pow_left (by decide) _

theorem eleven_le_of_flattening_stops_at_triangle_threshold {k : ℕ}
    (hstop : (flatteningStep^[k]) (paperSizeThreshold 3 2) ≤ 16) : 11 ≤ k := by
  have hn := (le_iterate_flatteningStep_pow (paperSizeThreshold 3 2) k).trans
    (Nat.pow_le_pow_left hstop (2 ^ k))
  by_contra hk
  have hpow : 16 ^ (2 ^ k) ≤ 16 ^ (2 ^ 10) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
  exact (Nat.not_lt_of_ge (hn.trans hpow)) triangle_threshold_exceeds_ten_rounds

theorem triangle_threshold_tenth_alpha :
    (paperSizeThreshold 3 2 : ℝ) ^ (paperAlpha 3 2 / 10) = (12 : ℝ) ^ 27 := by
  have hn0 : (0 : ℝ) < paperSizeThreshold 3 2 := by
    exact_mod_cast Nat.zero_lt_one.trans (paperSizeThreshold_one_lt (by decide : 2 < 3))
  calc
    _ = ((paperSizeThreshold 3 2 : ℝ) ^ paperAlpha 3 2) ^ (1 / 10 : ℝ) := by
      rw [← Real.rpow_mul hn0.le]
      congr 1
      ring
    _ = ((4 * 3 : ℝ) ^ (90 * 3 : ℝ)) ^ (1 / 10 : ℝ) := by
      rw [paperSizeThreshold_rpow_alpha (by decide : 2 < 3)]
      simp only [Nat.cast_ofNat]
    _ = _ := by rw [← Real.rpow_mul (by norm_num)]; norm_num

theorem flattening_iteration_cost_exceeds_triangle_threshold {C : ℝ} (hC : 8109 ≤ C)
    {k : ℕ} (hstop : (flatteningStep^[k]) (paperSizeThreshold 3 2) ≤ 16) :
    (paperSizeThreshold 3 2 : ℝ) ^ (paperAlpha 3 2 / 10) < C ^ k := by
  have hk := eleven_le_of_flattening_stops_at_triangle_threshold hstop
  rw [triangle_threshold_tenth_alpha]
  calc
    (12 : ℝ) ^ 27 < 8109 ^ 11 := by norm_num
    _ ≤ C ^ 11 := by gcongr
    _ ≤ _ := pow_le_pow_right₀ (by linarith only [hC]) hk

theorem uniform_flattening_round_cost_obstruction
    {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
    (S : ExchangeSystem W 3 2) (E : ExchangeSystem U 3 2) {k : ℕ}
    (hstop : (flatteningStep^[k]) (paperSizeThreshold 3 2) ≤ 16) :
    (paperSizeThreshold 3 2 : ℝ) ^ (paperAlpha 3 2 / 10) <
      ((15 + 48 * (E.graph.card : ℝ)) * (3 + 16 * (S.graph.card : ℝ))) ^ k := by
  have hs : (3 : ℝ) ≤ S.graph.card := by
    have h := Finset.card_le_card (S.positive_decomposition.clique_subset S.base_mem)
    rw [card_cliqueEdges] at h
    norm_num at h
    exact_mod_cast h
  have he : (3 : ℝ) ≤ E.graph.card := by
    have h := Finset.card_le_card (E.positive_decomposition.clique_subset E.base_mem)
    rw [card_cliqueEdges] at h
    norm_num at h
    exact_mod_cast h
  apply flattening_iteration_cost_exceeds_triangle_threshold _ hstop
  nlinarith only [hs, he, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr he)]

end Arxiv2411_18291
