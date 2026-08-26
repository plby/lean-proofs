import ErdosProblems.Erdos747.PathwiseRegularity

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Finite interfaces for the supercritical deletion argument -/

/-- Equality of time indices induces an equivalence of deletion-history
types. -/
def deletionHistoryCastEquiv {n : ℕ} (H : Finset (Edge n))
    {t u : ℕ} (h : t = u) :
    DeletionHistory H t ≃ DeletionHistory H u where
  toFun := castDeletionHistory H h
  invFun := castDeletionHistory H h.symm
  left_inv e := by
    subst u
    rfl
  right_inv e := by
    subst u
    rfl

/-- Time-indexed form of the fixed-layer marginal law.  At time `t`, the
remaining graph is uniform among the `(K-t)`-edge subgraphs of the complete
3-graph. -/
lemma historyState_probability_eq_sample_at_time {n t : ℕ}
    (ht : t ≤ (allEdges n).card) (P : Finset (Edge n) → Prop) :
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) t))
        (fun e ↦ P (historyState e t le_rfl)) =
      finsetProbability (sample n ((allEdges n).card - t)) P := by
  let M := (allEdges n).card - t
  have hM : M ≤ (allEdges n).card := by
    dsimp only [M]
    omega
  have hindex : (allEdges n).card - M = t := by
    dsimp only [M]
    omega
  let E := deletionHistoryCastEquiv (allEdges n) hindex
  have hequiv := finsetProbability_univ_equiv E
    (fun e : DeletionHistory (allEdges n) t ↦
      P (historyState e t le_rfl))
  have hstate :
      finsetProbability
          (Finset.univ : Finset
            (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (fun e ↦ P (historyState e ((allEdges n).card - M) le_rfl)) =
        finsetProbability
          (Finset.univ : Finset
            (DeletionHistory (allEdges n) ((allEdges n).card - M)))
          (fun e ↦ P (historyState (E e) t le_rfl)) := by
    apply finsetProbability_congr_event
    intro e he
    apply Iff.of_eq
    apply congrArg P
    exact (historyState_castDeletionHistory hindex e).symm
  calc
    finsetProbability
        (Finset.univ : Finset (DeletionHistory (allEdges n) t))
        (fun e ↦ P (historyState e t le_rfl)) =
      finsetProbability
        (Finset.univ : Finset
          (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (fun e ↦ P (historyState (E e) t le_rfl)) := by
          exact hequiv.symm
    _ = finsetProbability
        (Finset.univ : Finset
          (DeletionHistory (allEdges n) ((allEdges n).card - M)))
        (fun e ↦ P
          (historyState e ((allEdges n).card - M) le_rfl)) := hstate.symm
    _ = finsetProbability (sample n M) P :=
      historyState_probability_eq_sample hM P
    _ = finsetProbability (sample n ((allEdges n).card - t)) P := by
      rfl

/-- The concrete Kahn layer certificate supplies exactly the structural
hypothesis consumed by the sharply initialized deletion telescope.  This
packages the deterministic half of one deletion level. -/
lemma deletionStepGood_of_kahnLayerInput_sharp_initial
    {n t d D codegCap Q bNat B e₀ e₁ : ℕ}
    {C₀ L eta q c cTransfer bStop u : ℝ}
    (hn : 2 ≤ n) (ht : t < (allEdges n).card)
    (hL : 0 ≤ L) (hc : 0 < c) (hqeta : eta < q)
    (hcTransfer0 : 0 ≤ cTransfer) (hcTransfer1 : cTransfer ≤ 1)
    (hdb : bNat < d) (hB : 3 * B ≤ e₀ * (Q + 1))
    (he : 2 * (e₀ + e₁) + 12 ≤ n)
    (hq : q ≤ (((n / 2 : ℕ) : ℝ)^3 / (allEdges n).card))
    (hcPow : c ≤ cTransfer^3)
    (e : DeletionHistory (allEdges n) t)
    (hgood : DeletionHistoryGood (L / c) t e)
    (hCb : ∀ i < t,
      (L / c) * deletionGamma n (allEdges n) i ≤ bStop)
    (hbStop1 : bStop < 1)
    (hstop : stoppedCenteredSum (L / c) t e ≤ u)
    (hcountBudget :
      (n : ℝ) *
            Real.log ((((allEdges n).card - t : ℕ) : ℝ) / n) -
          2 * (n : ℝ) - C₀ * (n : ℝ) ≤
        2 * (n : ℝ) * Real.log (n : ℝ) +
          (n : ℝ) * Real.log ((9 : ℝ) / 2) - 2 * (n : ℝ) -
          Real.log (n : ℝ) / 2 - 1 -
          (u + (n : ℝ) *
            Real.log (((allEdges n).card : ℝ) /
              ((allEdges n).card - t : ℕ))) -
          ((L / c) *
            deletionVarianceBudget n (allEdges n) (L / c) t) /
              (1 - bStop))
    (hinput : KahnLayerInput n d D codegCap Q bNat B e₁
      C₀ L eta cTransfer (historyState e t le_rfl)) :
    DeletionStepGood (L / c) e := by
  have hstructure : KahnBootstrapStructure e C₀ L eta q c := by
    intro hcount
    exact kahnLayerInput_implies_bootstrap_conclusion
      hn hcTransfer0 hcTransfer1 hdb hB he hq hcPow hcount hinput
  exact deletionStepGood_of_kahnBootstrapStructure_sharp_initial
    (show 1 ≤ n by omega) ht C₀ L eta q c bStop u hL hc hqeta e
      hgood hCb hbStop1 hstop hcountBudget hstructure

/-- Strict upper-tail form of the stopped deletion-martingale estimate.
The closure theorem uses `u < S`, while the exponential Markov lemma is
stated for `u ≤ S`; this lemma performs that harmless event inclusion once. -/
lemma stoppedCenteredSum_gt_probability_le {n : ℕ}
    {H : Finset (Edge n)} (C theta u : ℝ)
    (hn : 0 < n) (hC : 0 < C) (T : ℕ) (hT : T ≤ H.card)
    (htheta0 : 0 ≤ theta)
    (htheta : ∀ i < T,
      |theta * (C * deletionGamma n H i)| ≤ 1 / 2) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ u < stoppedCenteredSum C T e) ≤
      Real.exp
        (theta^2 * deletionVarianceBudget n H C T - theta * u) := by
  calc
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ u < stoppedCenteredSum C T e) ≤
      finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ u ≤ stoppedCenteredSum C T e) := by
          apply finsetProbability_mono_event
          intro e he hstrict
          exact hstrict.le
    _ ≤ Real.exp
        (theta^2 * deletionVarianceBudget n H C T - theta * u) :=
      stoppedCenteredSum_upper_tail_le C theta u hn hC T hT
        htheta0 htheta

/-- A one-level split bound in ordinary fixed-layer language.  The first
term is the stopped martingale tail; the second is a structural failure
inside an arbitrary graph-level base certificate. -/
lemma deletionLayer_split_probability_le
    {n t d D codegCap Q bNat B e₁ : ℕ}
    {C C₀ L eta cTransfer theta u pStructural : ℝ}
    (Base : Finset (Edge n) → Prop)
    (hn : 0 < n) (ht : t ≤ (allEdges n).card) (hC : 0 < C)
    (htheta0 : 0 ≤ theta)
    (htheta : ∀ i < t,
      |theta * (C * deletionGamma n (allEdges n) i)| ≤ 1 / 2)
    (hStructural :
      finsetProbability (sample n ((allEdges n).card - t))
          (fun H ↦ Base H ∧
            ¬ KahnLayerInput n d D codegCap Q bNat B e₁
              C₀ L eta cTransfer H) ≤ pStructural) :
    finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ u < stoppedCenteredSum C t e) +
        finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ Base (historyState e t le_rfl) ∧
            ¬ KahnLayerInput n d D codegCap Q bNat B e₁
              C₀ L eta cTransfer (historyState e t le_rfl)) ≤
      Real.exp
          (theta^2 * deletionVarianceBudget n (allEdges n) C t -
            theta * u) + pStructural := by
  apply add_le_add
  · exact stoppedCenteredSum_gt_probability_le C theta u hn hC t
      (ht.trans (by rfl)) htheta0 htheta
  · let P : Finset (Edge n) → Prop := fun H ↦ Base H ∧
      ¬ KahnLayerInput n d D codegCap Q bNat B e₁
        C₀ L eta cTransfer H
    change finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ P (historyState e t le_rfl)) ≤ pStructural
    calc
      finsetProbability
          (Finset.univ : Finset (DeletionHistory (allEdges n) t))
          (fun e ↦ P (historyState e t le_rfl)) =
        @finsetProbability _ Finset.univ
          (fun e : DeletionHistory (allEdges n) t ↦
            P (historyState e t le_rfl)) (Classical.decPred _) :=
          finsetProbability_decidable_irrel Finset.univ _ _ _
      _ = @finsetProbability _
          (sample n ((allEdges n).card - t)) P (Classical.decPred _) :=
        historyState_probability_eq_sample_at_time ht P
      _ = finsetProbability (sample n ((allEdges n).card - t)) P :=
        finsetProbability_decidable_irrel _ P _ _
      _ ≤ pStructural := by
        simpa only [P] using hStructural

end

end Erdos747
