import ErdosProblems.Erdos747.ThinningAllDensities

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

lemma sample_eq_empty_of_card_lt (n M : ℕ) (hM : (allEdges n).card < M) : sample n M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro H hH
  have h := Finset.card_le_card (mem_sample.mp hH).1
  rw [(mem_sample.mp hH).2] at h
  omega

lemma eventually_aggregate_global_failure_probability_le
    (k : ℕ → ℕ) (C g q eta L : ℕ → ℝ) (B T zeta : ℝ)
    (hk : Tendsto k atTop atTop) (hL : Tendsto L atTop atTop)
    (hB : 0 ≤ B) (hT : 0 < T) (hzeta : 0 < zeta)
    (hC : Tendsto C atTop (𝓝 0)) (hC0 : ∀ᶠ i in atTop, 0 ≤ C i)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (hq0 : ∀ᶠ i in atTop, 0 ≤ q i)
    (heta : Tendsto eta atTop (𝓝 0)) (heta0 : ∀ᶠ i in atTop, 0 ≤ eta i) :
    ∀ᶠ i in atTop, ∀ M cap s : ℕ,
      0 < cap → L i ≤ (M : ℝ) / k i →
      (cap : ℝ) / ((M : ℝ) / k i) ≤ g i →
      0 < s → ((s + 1 : ℕ) : ℝ) ≤ T * L i → 4 * (s + 1) * (s + 1) ≤ M →
      (s + 1) * (s + 1) ≤ thinningBlockSize (allEdges (k i)).card zeta →
      finsetProbability (sample (k i) M)
          (fun H ↦ KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H ∧
            ¬ GlobalUpperWeightSpread (k i) H (coarseUpperFactor T) zeta) ≤
          4 * Real.exp (-(((s + 1 : ℕ) : ℝ) * zeta) / 1024) ∧
      finsetProbability (sample (k i) M)
          (fun H ↦ KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H ∧
            ¬ GlobalLowerWeightSpread (k i) H (coarseLowerFactor T) zeta) ≤
          4 * Real.exp (-(((s + 1 : ℕ) : ℝ) * zeta) / 1024) := by
  let a := fun i ↦ aggregatePresentTolerance (k i) (C i) (g i) (q i) (eta i) B
  let E := fun i ↦ aggregateThinningTopError (k i) (C i) (g i) (q i) (eta i) B T (L i) zeta
  have ha := aggregatePresentTolerance_tendsto_zero_along k C g q eta B hk hC hg hgpos hq heta
  have hspread := eventually_aggregatePresentWeightSpread_along k C g q eta B
    hk hC0 hg hgpos hq0 heta0 hB
  have htop := eventually_aggregate_thinning_diagnostics k C g q eta L B T zeta
    hk hL hB hT hzeta hC hC0 hg hgpos hq hq0 heta heta0
  have haHalf := (tendsto_order.mp ha).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have haZeta := (tendsto_order.mp ha).2 (zeta / 2) (half_pos hzeta)
  have hcast : Tendsto (fun i ↦ (k i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hlarge := (hcast.const_mul_atTop hzeta).eventually_ge_atTop 16
  filter_upwards [hspread, htop, haHalf, haZeta, hlarge]
    with i hspreadi htopi haHalfi haZetai hlargei
  intro M cap s hcap hmean hrelative hs ht hcollision htsq
  by_cases hMtop : M ≤ (allEdges (k i)).card
  · have htM : s + 1 ≤ M := by nlinarith only [hcollision, Nat.zero_le s]
    have hM0 : 0 < M := by omega
    have hpres : ∀ H ∈ sample (k i) M,
        KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H →
        PresentWeightSpread H (a i) (a i) := by
      intro H hHs hgood
      exact hspreadi M cap hM0 hcap hrelative H hgood
    have ha0 : 0 ≤ a i := aggregatePresentTolerance_nonneg _ _ _ _ _ _
    have hE0 : 0 ≤ E i := aggregateThinningTopError_nonneg _ _ _ _ _ _ _ _ _ hT.le hzeta.le
    have hK : (k i : ℝ) ≤ (allEdges (k i)).card := by
      have hnat := Finset.card_le_card (canonicalMatching_subset_allEdges (k i))
      rw [canonicalMatching_card] at hnat
      exact_mod_cast hnat
    have hlargeK := hlargei.trans (mul_le_mul_of_nonneg_left hK hzeta.le)
    have htopBoth : ∀ H ∈ sample (k i) M,
        KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H →
        (¬ GlobalUpperWeightSpread (k i) H (coarseUpperFactor T) zeta →
          finsetProbability (H.powersetCard (s + 1)) (fun U ↦ ¬ UpperWeightBlockDiagnostic (k i)
            (thinningBlockSize (allEdges (k i)).card zeta) (s + 1) ⟨H, U⟩) ≤ E i) ∧
        (¬ GlobalLowerWeightSpread (k i) H (coarseLowerFactor T) zeta →
          finsetProbability (H.powersetCard (s + 1)) (fun U ↦ ¬ LowerWeightBlockDiagnostic (k i)
            (thinningBlockSize (allEdges (k i)).card zeta) (s + 1) ⟨H, U⟩) ≤ E i) := by
      intro H hHs hgood
      exact htopi.2 M cap s H hcap hmean hrelative hgood hs ht
        (by simpa only [(mem_sample.mp hHs).2] using hcollision)
    constructor
    · exact conditionalGlobalUpper_failure_probability_le_all_densities
        (KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B)
        (a i) zeta T (E i) ha0 haHalfi.le hzeta haZetai.le hT.le hlargeK
        htM hMtop (by omega) htsq hE0 htopi.1 hpres (fun H hHs hgood ↦ (htopBoth H hHs hgood).1)
    · exact conditionalGlobalLower_failure_probability_le_all_densities
        (KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B)
        (a i) zeta T (E i) ha0 haHalfi.le hzeta haZetai.le hT.le hlargeK
        htM hMtop (by omega) htsq hE0 htopi.1 hpres (fun H hHs hgood ↦ (htopBoth H hHs hgood).2)
  · have hempty := sample_eq_empty_of_card_lt (k i) M (lt_of_not_ge hMtop)
    simp only [hempty, finsetProbability, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, zero_div]
    constructor <;> positivity

end

end Erdos747
