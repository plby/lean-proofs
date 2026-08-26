/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ThresholdResidualCapacity

/-!
# Realizing a fresh saturated chunk with prescribed outer roots

The parent-neighbor bound uses each endpoint's source density, not the
common reduced density cutoff. All residual host fields are derived from
whole-endpoint degrees and one permanent deletion budget. In particular a
previously chosen pending root is never changed by this construction.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreshChunkEmbedding

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma58OwnerLocalStep Erdos547b.ZhaoLemma58ThresholdResidualCapacity

/-- Construct the actual threshold step from the source mass display and
literal whole-pair degrees. Zero low source entries need no neighbors. -/
noncomputable def classifiedFreshChunkData
    {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
    (parent : Fin b → V) (whole deleted : Fin 2 → Finset V)
    (N L small : ℕ) (ratio dx dy γ ε ρ d : ℝ)
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (D : ClassifiedThresholdOwnerNumerics F ratio dx dy γ ε N small)
    (hN : 0 < N) (hγ : 0 < γ) (hγdy : γ ≤ dy) (hdy : dy ≤ 1)
    (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (hwhole : ∀ c, (whole c).card = N)
    (hdeleted : ∀ c, deleted c ⊆ whole c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ L)
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (huniform : H.IsUniform ρ (whole 0) (whole 1))
    (hdensity : d ≤ H.edgeDensity (whole 0) (whole 1))
    (hparent : ∀ i c, 0 < (if c = lowSide then dx else dy) →
      ((if c = lowSide then dx else dy) - 2 * ρ) * N ≤
        (#((whole c).filter (H.Adj (parent i))) : ℝ))
    (hparentMargin : (L : ℝ) + 2 ≤ (γ - 3 * ρ) * N)
    (hcomponent : (small : ℝ) + ρ * N + 1 ≤ (d - ρ) * (γ * N - L)) :
    ActualThresholdStepData F H parent whole (residualSide whole deleted) ρ d := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfactor : 0 ≤ d - ρ := sub_nonneg.mpr hρd
  have hhigh : (thresholdHighBudget dy γ N : ℝ) ≤ (dy - γ) * N :=
    thresholdHighBudget_cast_le (mul_nonneg (sub_nonneg.mpr hγdy) hNR.le)
  have hhighOne : (thresholdHighBudget dy γ N : ℝ) ≤ (1 - γ) * N := by
    apply hhigh.trans
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hdy γ) hNR.le
  have hreserve (c) : (thresholdReserve ρ (whole c).card : ℝ) ≤ ρ * N + 1 := by
    rw [hwhole]
    exact (thresholdReserve_lt_target_add_one hρ N).le
  have hdeleteR (c) : ((deleted c).card : ℝ) ≤ L := by exact_mod_cast hdeletedCard c
  have hlive (c) : (N : ℝ) - L ≤ (residualSide whole deleted c).card := by
    have hsum : (residualSide whole deleted c).card + (deleted c).card = N := by
      exact (Finset.card_sdiff_add_card_eq_card (hdeleted c)).trans (hwhole c)
    have hsumR : ((residualSide whole deleted c).card : ℝ) + (deleted c).card = N := by
      exact_mod_cast hsum
    linarith only [hsumR, hdeleteR c]
  refine {
    slack := small
    lowBudget := thresholdLowBudget dx γ N
    highBudget := thresholdHighBudget dy γ N
    lowSide := lowSide
    highSide := highSide
    reserve := fun c => thresholdReserve ρ (whole c).card
    small := D.small
    sides_ne := hsides
    suffix_display := D.suffix_display highSide
    low_le_high := D.lowBudget_le_highBudget
    uniform := huniform
    live_subset := residualSide_subset whole deleted
    whole_disjoint := hdisjoint
    density_lower := hdensity
    factor_nonneg := hfactor
    reserve_regular := fun c => thresholdReserve_covers ρ (whole c).card
    live_capacity := ?_
    parent_neighbours := ?_
    component_margin := ?_ }
  · intro c
    have hcap : (thresholdHighBudget dy γ N : ℝ) + thresholdReserve ρ (whole c).card ≤
        (residualSide whole deleted c).card := by
      have hρN : 0 ≤ ρ * N := mul_nonneg hρ hNR.le
      nlinarith only [hhighOne, hreserve c, hlive c, hparentMargin, hρN]
    exact_mod_cast hcap
  · intro base hbase
    dsimp only
    intro i
    let O := actualThresholdSwitchOrientation F small (thresholdLowBudget dx γ N)
      (thresholdHighBudget dy γ N) lowSide highSide D.small hsides
      (D.suffix_display highSide) base hbase
    let c := branchRootSide F O.orient i
    let before := sideLoadBefore F O.orient i c
    have hpref : before ≤ if c = lowSide then thresholdLowBudget dx γ N
        else thresholdHighBudget dy γ N := O.prefix_root_le D.lowBudget_le_highBudget i
    have htarget : 0 < (if c = lowSide then dx else dy) ∧
        (before : ℝ) ≤ ((if c = lowSide then dx else dy) - γ) * N := by
      by_cases hc : c = lowSide
      · have hlowNonzero : thresholdLowBudget dx γ N ≠ 0 := by
          intro hz
          have hcut : O.cutoff = 0 := by
            change maximalFittingCutoff F base (thresholdLowBudget dx γ N) = 0
            rw [hz]
            exact maximalFittingCutoff_eq_zero_of_budget_zero F base
          exact (O.late_root_high i (by rw [hcut]; exact Nat.zero_le _)) hc
        have hlow : 0 ≤ (dx - γ) * (N : ℝ) := by
          by_contra hneg
          exact hlowNonzero (thresholdLowBudget_eq_zero_of_nonpos (le_of_not_ge hneg))
        have hdx : 0 < dx := by nlinarith only [hlow, hNR, hγ]
        simp only [if_pos hc] at hpref ⊢
        exact ⟨hdx, (show (before : ℝ) ≤ thresholdLowBudget dx γ N by
          exact_mod_cast hpref).trans (thresholdLowBudget_cast_le hlow)⟩
      · simp only [if_neg hc] at hpref ⊢
        exact ⟨hγ.trans_le hγdy, (show (before : ℝ) ≤ thresholdHighBudget dy γ N by
          exact_mod_cast hpref).trans hhigh⟩
    have hneed : ((deleted c).card + (1 + thresholdReserve ρ (whole c).card + before) : ℕ) ≤
        #((whole c).filter (H.Adj (parent i))) := by
      have hneedR : (((deleted c).card + (1 + thresholdReserve ρ (whole c).card + before) : ℕ) : ℝ) ≤
          ((if c = lowSide then dx else dy) - 2 * ρ) * N := by
        push_cast
        nlinarith only [hdeleteR c, hreserve c, htarget.2, hparentMargin]
      exact_mod_cast hneedR.trans (hparent i c htarget.1)
    exact residualSide_filter_card_ge_of_deleted_card_add_le H whole deleted (parent i) c
      (1 + thresholdReserve ρ (whole c).card + before) hneed
  · intro i c
    have hsmallR : (F.size i : ℝ) ≤ small := by exact_mod_cast D.small i
    have hroom : γ * (N : ℝ) - L ≤
        ((residualSide whole deleted c).card : ℝ) - thresholdHighBudget dy γ N := by
      nlinarith only [hlive c, hhighOne]
    calc
      (F.size i : ℝ) + ρ * (whole c).card + 1 ≤ (small : ℝ) + ρ * N + 1 := by
        rw [hwhole]
        linarith only [hsmallR]
      _ ≤ (d - ρ) * (γ * N - L) := hcomponent
      _ ≤ (d - ρ) *
          (((residualSide whole deleted c).card : ℝ) - thresholdHighBudget dy γ N) :=
        mul_le_mul_of_nonneg_left hroom hfactor

/-- Part 1 of the local source embedding, with all host-capacity fields
proved internally. The prescribed outer roots, including a pending root,
remain the literal external parents of every embedded branch. -/
theorem exists_partOne_fresh_chunk_embedding
    {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
    (parent : Fin b → V) (whole deleted : Fin 2 → Finset V)
    (N L small : ℕ) (dx dy γ ε ρ d : ℝ)
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (hN : 0 < N) (hγ : 0 < γ) (hlowHigh : dx ≤ dy) (hdy : dy ≤ 1)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (hsmall : ∀ i, F.size i ≤ small)
    (hmass : (F.order : ℝ) ≤ (dx + dy - 2 * γ - 3 * ε) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (ε * N))
    (hwhole : ∀ c, (whole c).card = N)
    (hdeleted : ∀ c, deleted c ⊆ whole c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ L)
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (huniform : H.IsUniform ρ (whole 0) (whole 1))
    (hdensity : d ≤ H.edgeDensity (whole 0) (whole 1))
    (hparent : ∀ i c, 0 < (if c = lowSide then dx else dy) →
      ((if c = lowSide then dx else dy) - 2 * ρ) * N ≤
        (#((whole c).filter (H.Adj (parent i))) : ℝ))
    (hparentMargin : (L : ℝ) + 2 ≤ (γ - 3 * ρ) * N)
    (hcomponent : (small : ℝ) + ρ * N + 1 ≤ (d - ρ) * (γ * N - L)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding F H parent orient (residualSide whole deleted)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hγdy : γ ≤ dy := by
    by_contra hnot
    have hneg : dx + dy - 2 * γ - 3 * ε < 0 := by
      have hdyγ := lt_of_not_ge hnot
      linarith only [hlowHigh, hdyγ, hε]
    have hnegative := mul_neg_of_neg_of_pos hneg hNR
    have horder : (0 : ℝ) ≤ F.order := Nat.cast_nonneg _
    linarith only [hmass, hnegative, horder]
  let D := ClassifiedThresholdOwnerNumerics.of_partOneMass F dx dy γ ε N small
    hlowHigh hNR.le (mul_nonneg (sub_nonneg.mpr hγdy) hNR.le) hε hsmall hmass hround
  let K := classifiedFreshChunkData F H parent whole deleted N L small 0 dx dy γ ε ρ d
    lowSide highSide hsides D hN hγ hγdy hdy hρ hρd hwhole hdeleted hdeletedCard
    hdisjoint huniform hdensity hparent hparentMargin hcomponent
  exact K.realize F H parent whole (residualSide whole deleted) ρ d

end Erdos547b.ZhaoSourceFreshChunkEmbedding

#print axioms Erdos547b.ZhaoSourceFreshChunkEmbedding.classifiedFreshChunkData
#print axioms Erdos547b.ZhaoSourceFreshChunkEmbedding.exists_partOne_fresh_chunk_embedding
