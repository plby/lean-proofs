import ErdosProblems.Erdos747.CompleteMatchingCount

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The sharp complete count propagated through deletion -/

/-- The sharp finite deletion-count lower bound initialized by the exact
complete-hypergraph matching count.  In comparison with the earlier deletion
telescope, this retains the linear term `n * log (9 / 2)` which is needed at
the Shamir threshold. -/
lemma deletionHistory_log_count_lower_sharp_initial {n M : ℕ}
    (hn : 1 ≤ n) (hM : 0 < M) (hMtop : M ≤ (allEdges n).card)
    (C b u : ℝ) (hC : 0 ≤ C)
    (e : DeletionHistory (allEdges n) ((allEdges n).card - M))
    (hgood : DeletionHistoryGood C ((allEdges n).card - M) e)
    (hCb : ∀ i < (allEdges n).card - M,
      C * deletionGamma n (allEdges n) i ≤ b)
    (hb1 : b < 1)
    (hstop : stoppedCenteredSum C ((allEdges n).card - M) e ≤ u) :
    2 * (n : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log (n : ℝ) / 2 - 1 -
          (u + (n : ℝ) *
            Real.log (((allEdges n).card : ℝ) / M)) -
          (C * deletionVarianceBudget n (allEdges n) C
            ((allEdges n).card - M)) / (1 - b) ≤
      Real.log
        ((perfectMatchings n
          (historyState e ((allEdges n).card - M) le_rfl)).card : ℝ) := by
  let T := (allEdges n).card - M
  let L := deletionFractionList T e
  let S := stoppedCenteredSum C T e + deletionMeanSum n (allEdges n) T
  let Q := (L.map fun x ↦ x^2).sum
  let V := deletionVarianceBudget n (allEdges n) C T
  have hinit : (perfectMatchings n (allEdges n)).card ≠ 0 := by
    have hfac := factorial_sq_le_card_perfectMatchings_allEdges
      (show 0 < n by omega)
    have : 0 < n.factorial ^ 2 := by positivity
    omega
  have hbounds := deletionHistory_log_ratio_bounds
    C b T e hinit hgood hCb hb1
  dsimp only at hbounds
  have hmean := deletionMeanSum_le_log_ratio n (allEdges n) M hM hMtop
  have hSupper : S ≤
      u + (n : ℝ) * Real.log (((allEdges n).card : ℝ) / M) := by
    dsimp only [S, T]
    exact add_le_add hstop hmean
  have hQ : Q ≤ C * V := by
    simpa only [Q, L, V, T] using
      deletionFractionSquareSum_le_varianceBudget C e hC hgood
  have hden : 0 < 1 - b := sub_pos.mpr hb1
  have hQdiv : Q / (1 - b) ≤ (C * V) / (1 - b) :=
    div_le_div_of_nonneg_right hQ hden.le
  have hratioLower :
      -(u + (n : ℝ) *
          Real.log (((allEdges n).card : ℝ) / M)) -
          (C * V) / (1 - b) ≤
        Real.log
          (((perfectMatchings n (historyState e T le_rfl)).card : ℝ) /
            (perfectMatchings n (allEdges n)).card) := by
    calc
      -(u + (n : ℝ) *
          Real.log (((allEdges n).card : ℝ) / M)) -
            (C * V) / (1 - b) ≤ -S - (C * V) / (1 - b) := by
        linarith
      _ ≤ -S - Q / (1 - b) := by linarith
      _ ≤ Real.log
          (((perfectMatchings n (historyState e T le_rfl)).card : ℝ) /
            (perfectMatchings n (allEdges n)).card) := by
        simpa only [S, Q, L] using hbounds.1
  have hPhi := card_historyState_ne_zero_of_good
    C b e hinit hgood hCb hb1
  have hfinalPos : (0 : ℝ) <
      (perfectMatchings n (historyState e T le_rfl)).card := by
    exact_mod_cast Nat.pos_of_ne_zero hPhi
  have hinitPos : (0 : ℝ) <
      (perfectMatchings n (allEdges n)).card := by
    exact_mod_cast Nat.pos_of_ne_zero hinit
  rw [Real.log_div hfinalPos.ne' hinitPos.ne'] at hratioLower
  have hcomplete := log_card_perfectMatchings_allEdges_sharp hn
  dsimp only [T, V] at hratioLower hfinalPos ⊢
  linarith

/-- Endpoint form of the sharp initialized count telescope. -/
lemma kahnCountLower_historyState_sharp_initial {n M : ℕ}
    (hn : 1 ≤ n) (hM : 0 < M) (hMtop : M ≤ (allEdges n).card)
    (C b u C₀ : ℝ) (hC : 0 ≤ C)
    (e : DeletionHistory (allEdges n) ((allEdges n).card - M))
    (hgood : DeletionHistoryGood C ((allEdges n).card - M) e)
    (hCb : ∀ i < (allEdges n).card - M,
      C * deletionGamma n (allEdges n) i ≤ b)
    (hb1 : b < 1)
    (hstop : stoppedCenteredSum C ((allEdges n).card - M) e ≤ u)
    (hbudget :
      (n : ℝ) * Real.log ((M : ℝ) / n) - 2 * (n : ℝ) -
          C₀ * (n : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log (n : ℝ) / 2 - 1 -
          (u + (n : ℝ) *
            Real.log (((allEdges n).card : ℝ) / M)) -
          (C * deletionVarianceBudget n (allEdges n) C
            ((allEdges n).card - M)) / (1 - b)) :
    KahnCountLower
      (historyState e ((allEdges n).card - M) le_rfl) C₀ := by
  unfold KahnCountLower
  have hcard :
      (historyState e ((allEdges n).card - M) le_rfl).card = M := by
    simp only [card_historyState]
    omega
  rw [hcard]
  exact hbudget.trans (deletionHistory_log_count_lower_sharp_initial
    hn hM hMtop C b u hC e hgood hCb hb1 hstop)

/-- Time-indexed form of the sharp initialized count telescope. -/
lemma kahnCountLower_historyState_at_time_sharp_initial {n t : ℕ}
    (hn : 1 ≤ n) (ht : t < (allEdges n).card)
    (C b u C₀ : ℝ) (hC : 0 ≤ C)
    (e : DeletionHistory (allEdges n) t)
    (hgood : DeletionHistoryGood C t e)
    (hCb : ∀ i < t, C * deletionGamma n (allEdges n) i ≤ b)
    (hb1 : b < 1)
    (hstop : stoppedCenteredSum C t e ≤ u)
    (hbudget :
      (n : ℝ) *
            Real.log ((((allEdges n).card - t : ℕ) : ℝ) / n) -
          2 * (n : ℝ) - C₀ * (n : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log (n : ℝ) / 2 - 1 -
          (u + (n : ℝ) *
            Real.log (((allEdges n).card : ℝ) /
              ((allEdges n).card - t : ℕ))) -
          (C * deletionVarianceBudget n (allEdges n) C t) / (1 - b)) :
    KahnCountLower (historyState e t le_rfl) C₀ := by
  let M := (allEdges n).card - t
  have hM : 0 < M := by dsimp only [M]; omega
  have hMtop : M ≤ (allEdges n).card := Nat.sub_le _ _
  have heq : (allEdges n).card - M = t := by
    dsimp only [M]
    omega
  let e' := castDeletionHistory (allEdges n) heq.symm e
  have hgood' : DeletionHistoryGood C ((allEdges n).card - M) e' := by
    exact (deletionHistoryGood_cast heq.symm C e).2 hgood
  have hCb' : ∀ i < (allEdges n).card - M,
      C * deletionGamma n (allEdges n) i ≤ b := by
    intro i hi
    exact hCb i (by omega)
  have hstop' : stoppedCenteredSum C ((allEdges n).card - M) e' ≤ u := by
    rw [stoppedCenteredSum_cast heq.symm C e]
    exact hstop
  have hc := kahnCountLower_historyState_sharp_initial
    hn hM hMtop C b u C₀ hC e' hgood' hCb' hb1 hstop'
    (by simpa only [M, heq] using hbudget)
  rw [historyState_castDeletionHistory heq.symm e] at hc
  exact hc

/-- A structural certificate promotes a prefix to a good deletion step using
the sharp exact complete-matching initialization. -/
lemma deletionStepGood_of_kahnBootstrapStructure_sharp_initial {n t : ℕ}
    (hn : 1 ≤ n) (ht : t < (allEdges n).card)
    (C₀ L eta q c b u : ℝ)
    (hL : 0 ≤ L) (hc : 0 < c) (hqeta : eta < q)
    (e : DeletionHistory (allEdges n) t)
    (hgood : DeletionHistoryGood (L / c) t e)
    (hCb : ∀ i < t,
      (L / c) * deletionGamma n (allEdges n) i ≤ b)
    (hb1 : b < 1)
    (hstop : stoppedCenteredSum (L / c) t e ≤ u)
    (hbudget :
      (n : ℝ) *
            Real.log ((((allEdges n).card - t : ℕ) : ℝ) / n) -
          2 * (n : ℝ) - C₀ * (n : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log (n : ℝ) / 2 - 1 -
          (u + (n : ℝ) *
            Real.log (((allEdges n).card : ℝ) /
              ((allEdges n).card - t : ℕ))) -
          ((L / c) * deletionVarianceBudget n (allEdges n) (L / c) t) /
            (1 - b))
    (hstructure : KahnBootstrapStructure e C₀ L eta q c) :
    DeletionStepGood (L / c) e := by
  have hC : 0 ≤ L / c := div_nonneg hL hc.le
  have hinit : (perfectMatchings n (allEdges n)).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr
      (hasPerfectMatching_iff_perfectMatchings_nonempty.mp
        (allEdges_hasPerfectMatching n))
  have hPhi := card_historyState_ne_zero_of_good
    (L / c) b e hinit hgood hCb hb1
  have hcount := kahnCountLower_historyState_at_time_sharp_initial
    hn ht (L / c) b u C₀ hC e hgood hCb hb1 hstop hbudget
  rcases hstructure hcount with ⟨hspread, hdom⟩
  have hsubset : historyState e t le_rfl ⊆ allEdges n := by
    intro A hA
    exact (Finset.mem_sdiff.mp hA).1
  refine ⟨hPhi, ?_⟩
  exact weightControlled_of_global_upper_spread_max
    (historyState e t le_rfl) hsubset L eta q c (by omega) hc hqeta
    hPhi hspread hdom

end

end Erdos747
