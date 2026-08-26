import ErdosProblems.Erdos747.ThinningTopBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def aggregateThinningTopError (k : ℕ) (C g q eta B T L zeta : ℝ) : ℝ :=
  let a := aggregatePresentTolerance k C g q eta B
  let p := aggregateSurvivalError k C g q eta B T L
  2 * p + 100 * a / zeta + 100 * (a + p) / zeta

lemma aggregateThinningTopError_nonneg (k : ℕ) (C g q eta B T L zeta : ℝ)
    (hT : 0 ≤ T) (hzeta : 0 ≤ zeta) : 0 ≤ aggregateThinningTopError k C g q eta B T L zeta := by
  have ha := aggregatePresentTolerance_nonneg k C g q eta B
  have hp := aggregateSurvivalError_nonneg k C g q eta B T L hT
  dsimp only [aggregateThinningTopError]
  positivity

lemma aggregateThinningTopError_tendsto_zero
    (k : ℕ → ℕ) (C g q eta L : ℕ → ℝ) (B T zeta : ℝ)
    (hk : Tendsto k atTop atTop) (hL : Tendsto L atTop atTop) (hT : 0 < T)
    (hC : Tendsto C atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0))
    (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun i ↦ aggregateThinningTopError (k i) (C i) (g i) (q i) (eta i) B T (L i) zeta)
      atTop (𝓝 0) := by
  have ha := aggregatePresentTolerance_tendsto_zero_along k C g q eta B hk hC hg hgpos hq heta
  have hp := aggregateSurvivalError_tendsto_zero k C g q eta L B T hk hL hT hC hg hgpos hq heta
  have hlim := ((hp.const_mul 2).add ((ha.const_mul 100).div_const zeta)).add
    (((ha.add hp).const_mul 100).div_const zeta)
  simpa only [aggregateThinningTopError, mul_zero, add_zero, zero_div] using hlim

/-- Both top diagnostics have uniformly vanishing miss probability.
The thinning size and edge density remain free, subject to their genuine
finite collision and mean-degree requirements. -/
lemma eventually_aggregate_thinning_diagnostics
    (k : ℕ → ℕ) (C g q eta L : ℕ → ℝ) (B T zeta : ℝ)
    (hk : Tendsto k atTop atTop) (hL : Tendsto L atTop atTop)
    (hB : 0 ≤ B) (hT : 0 < T) (hzeta : 0 < zeta)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ i in atTop, 0 ≤ C i)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (hq0 : ∀ᶠ i in atTop, 0 ≤ q i)
    (heta : Tendsto eta atTop (𝓝 0)) (heta0 : ∀ᶠ i in atTop, 0 ≤ eta i) :
    ∀ᶠ i in atTop,
      aggregateThinningTopError (k i) (C i) (g i) (q i) (eta i) B T (L i) zeta ≤ 1 / 2 ∧
      ∀ M cap s : ℕ, ∀ H : Finset (Edge (k i)),
      0 < cap → L i ≤ (M : ℝ) / k i →
      (cap : ℝ) / ((M : ℝ) / k i) ≤ g i →
      KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H →
      0 < s → ((s + 1 : ℕ) : ℝ) ≤ T * L i → 4 * (s + 1) * (s + 1) ≤ H.card →
      (¬ GlobalUpperWeightSpread (k i) H (coarseUpperFactor T) zeta →
        finsetProbability (H.powersetCard (s + 1))
            (fun U ↦ ¬ UpperWeightBlockDiagnostic (k i)
              (thinningBlockSize (allEdges (k i)).card zeta) (s + 1) ⟨H, U⟩) ≤
          aggregateThinningTopError (k i) (C i) (g i) (q i) (eta i) B T (L i) zeta) ∧
      (¬ GlobalLowerWeightSpread (k i) H (coarseLowerFactor T) zeta →
        finsetProbability (H.powersetCard (s + 1))
            (fun U ↦ ¬ LowerWeightBlockDiagnostic (k i)
              (thinningBlockSize (allEdges (k i)).card zeta) (s + 1) ⟨H, U⟩) ≤
          aggregateThinningTopError (k i) (C i) (g i) (q i) (eta i) B T (L i) zeta) := by
  let a := fun i ↦ aggregatePresentTolerance (k i) (C i) (g i) (q i) (eta i) B
  let p := fun i ↦ aggregateSurvivalError (k i) (C i) (g i) (q i) (eta i) B T (L i)
  have ha := aggregatePresentTolerance_tendsto_zero_along k C g q eta B hk hC hg hgpos hq heta
  have hspread := eventually_aggregatePresentWeightSpread_along k C g q eta B
    hk hC0 hg hgpos hq0 heta0 hB
  have hsurv := eventually_aggregate_completion_survival k C g q eta L B T
    hk hL hB hT hC hC0 hg hgpos hq hq0 heta heta0
  have htop := (tendsto_order.mp (aggregateThinningTopError_tendsto_zero k C g q eta L B T zeta
    hk hL hT hC hg hgpos hq heta)).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have haHalf := (tendsto_order.mp ha).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have haZeta := (tendsto_order.mp ha).2 (zeta / 2) (half_pos hzeta)
  have hcast : Tendsto (fun i ↦ (k i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hlarge := (hcast.const_mul_atTop hzeta).eventually_ge_atTop 16
  filter_upwards [hspread, hsurv, htop, haHalf, haZeta, hlarge, hk.eventually_ge_atTop 4]
    with i hspreadi hsurvi htopi haHalfi haZetai hlargei hki
  refine ⟨htopi.le, ?_⟩
  intro M cap s H hcap hmean hrelative hgood hs ht hcollision
  have hH := (mem_sample.mp hgood.1).1
  have hMpos : 0 < M := by
    obtain ⟨F, hFsub, hFcard, -⟩ := hgood.2.1
    have hFle := Finset.card_le_card hFsub
    have hHM := (mem_sample.mp hgood.1).2
    omega
  have hpres : PresentWeightSpread H (a i) (a i) := hspreadi M cap hMpos hcap hrelative H hgood
  have ha0 : 0 ≤ a i := aggregatePresentTolerance_nonneg _ _ _ _ _ _
  have hp0 : 0 ≤ p i := aggregateSurvivalError_nonneg _ _ _ _ _ _ _ _ hT.le
  have hK : (k i : ℝ) ≤ (allEdges (k i)).card := by
    have hnat := Finset.card_le_card (canonicalMatching_subset_allEdges (k i))
    rw [canonicalMatching_card] at hnat
    exact_mod_cast hnat
  have hlargeK : 16 ≤ zeta * (allEdges (k i)).card :=
    hlargei.trans (mul_le_mul_of_nonneg_left hK hzeta.le)
  have hsCard : s + 1 ≤ H.card := by nlinarith only [hcollision, Nat.zero_le s]
  constructor
  · intro hglobal
    have hraw := upper_thinning_diagnostic_miss_le (a i) zeta T (p i) hH ha0 haHalfi.le
      hzeta haZetai.le hT.le hp0 hlargeK hsCard hpres hglobal (by
        intro Z hZ
        have hZall := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hZ).1).1
        exact hsurvi M cap H hcap hmean hrelative hgood Z hZall
          (coarseUpperBadNonedge_weight_lower_quarter H T hT.le hZ) H rfl rfl (s + 1)
          (by omega) ht hcollision)
    apply hraw.trans
    change 2 * p i + 100 * a i / zeta ≤
      2 * p i + 100 * a i / zeta + 100 * (a i + p i) / zeta
    exact le_add_of_nonneg_right (by positivity)
  · intro hglobal
    have hraw := lower_thinning_diagnostic_miss_le (a i) zeta T (p i) hH ha0 haHalfi.le
      hzeta haZetai.le hT.le hp0 hlargeK hsCard hpres hglobal (by
        intro Z hZH hZtyp
        have hZall := hH hZH
        apply hsurvi M cap H hcap hmean hrelative hgood Z hZall
          (presentTypical_weight_lower_quarter H (a i) haHalfi.le hZH hZtyp) (H.erase Z)
          (reindexGraphAway_erase_self H hZall) (completionWeight_erase_self H Z) s hs
        · exact (show (s : ℝ) ≤ (s + 1 : ℕ) by exact_mod_cast Nat.le_succ s).trans ht
        · exact collision_bound_erase_of_succ hZH hcollision)
    apply hraw.trans
    change 100 * (a i + p i) / zeta ≤
      2 * p i + 100 * a i / zeta + 100 * (a i + p i) / zeta
    exact le_add_of_nonneg_left (by positivity)

end

end Erdos747
