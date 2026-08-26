import ErdosProblems.Erdos747.ResidualPresentBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def residualPresentTolerance (k : ℕ) (C c g q eta B : ℝ) : ℝ :=
  aggregatePresentTolerance (k - 1) (residualCountError k C c) (2 * g)
    (residualDegreeTolerance k B q g) (2 * eta) (2 * B)

lemma residualPresentTolerance_nonneg (k : ℕ) (C c g q eta B : ℝ) :
    0 ≤ residualPresentTolerance k C c g q eta B := Real.sqrt_nonneg _

lemma residualCountError_tendsto_zero_along (k : ℕ → ℕ) (C : ℕ → ℝ) (c : ℝ)
    (hk : Tendsto k atTop atTop) (hC : Tendsto C atTop (𝓝 0)) :
    Tendsto (fun i ↦ residualCountError (k i) (C i) c) atTop (𝓝 0) := by
  have hpred : Tendsto (fun i ↦ k i - 1) atTop atTop :=
    (nat_sub_const_tendsto_atTop 1).comp hk
  have hcast : Tendsto (fun i ↦ ((k i - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpred
  have hinv : Tendsto (fun i ↦ (1 : ℝ) / ((k i - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hlast : Tendsto (fun i ↦ (3 - 2 * Real.log c) / ((k i - 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hratio : Tendsto (fun i ↦ (1 : ℝ) + 1 / ((k i - 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hinv
  have hlim := (hC.mul hratio).add hlast
  norm_num only [zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hk.eventually_ge_atTop 2] with i hi
  change C i * ((1 : ℝ) + 1 / ((k i - 1 : ℕ) : ℝ)) +
    (3 - 2 * Real.log c) / ((k i - 1 : ℕ) : ℝ) = residualCountError (k i) (C i) c
  unfold residualCountError
  rw [Nat.cast_sub (by omega : 1 ≤ k i), Nat.cast_one]
  have hkR : (1 : ℝ) < k i := by exact_mod_cast hi
  field_simp [(sub_pos.mpr hkR).ne']
  ring

lemma residualDegreeTolerance_tendsto_zero_along
    (k : ℕ → ℕ) (B : ℝ) (q g : ℕ → ℝ)
    (hk : Tendsto k atTop atTop) (hq : Tendsto q atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun i ↦ residualDegreeTolerance (k i) B (q i) (g i)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun i ↦ (k i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hlast : Tendsto (fun i ↦ 12 * (B + 1) / k i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  simpa only [residualDegreeTolerance, mul_zero, add_zero] using
    ((hq.const_mul 2).add (hg.const_mul 6)).add hlast

lemma residualPresentTolerance_tendsto_zero_along
    (k : ℕ → ℕ) (C g q eta : ℕ → ℝ) (c B : ℝ)
    (hk : Tendsto k atTop atTop) (hC : Tendsto C atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun i ↦ residualPresentTolerance (k i) (C i) c (g i) (q i) (eta i) B)
      atTop (𝓝 0) := by
  apply aggregatePresentTolerance_tendsto_zero_along
    (fun i ↦ k i - 1) (fun i ↦ residualCountError (k i) (C i) c)
    (fun i ↦ 2 * g i) (fun i ↦ residualDegreeTolerance (k i) B (q i) (g i))
    (fun i ↦ 2 * eta i) (2 * B)
  · exact (nat_sub_const_tendsto_atTop 1).comp hk
  · exact residualCountError_tendsto_zero_along k C c hk hC
  · simpa only [mul_zero] using hg.const_mul 2
  · filter_upwards [hgpos] with i hi
    positivity
  · exact residualDegreeTolerance_tendsto_zero_along k B q g hk hq hg
  · simpa only [mul_zero] using heta.const_mul 2

lemma kahnAggregateInsertionGood_residualPresentWeightSpread
    {k M cap : ℕ} {H : Finset (Edge k)} {Z : Edge k} {C c g q eta B : ℝ}
    (hk : 4 ≤ k) (hcap : 0 < cap) (hZ : Z ∈ allEdges k)
    (hC : 0 ≤ C) (hc : 0 < c) (hc1 : c ≤ 1) (hg : 0 < g)
    (hq : 0 ≤ q) (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hmean : 1 ≤ (M : ℝ) / k) (hsize : 6 * (B + 1) ≤ k)
    (hrelative : (cap : ℝ) / ((M : ℝ) / k) ≤ g)
    (hq' : residualDegreeTolerance k B q g ≤ 1)
    (hR : 1 < entropyRatioEnvelope (2 * g))
    (hgood : KahnAggregateInsertionGood k M cap C q eta B H)
    (hweight : c^2 * matchingWeightTarget k H ≤ completionWeight H Z) :
    PresentWeightSpread (reindexGraphAway H Z hZ)
        (residualPresentTolerance k C c g q eta B) (residualPresentTolerance k C c g q eta B) ∧
      ((M : ℝ) / k) / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((k - 1 : ℕ) : ℝ) := by
  obtain ⟨hres, hcap', hmean'⟩ := kahnAggregateInsertionGood_reindexGraphAway_explicit
    (by omega : 2 ≤ k) hZ hc hB hq heta hg.le hmean hsize hrelative hq' hgood hweight
  have hJpos : 0 < (reindexGraphAway H Z hZ).card := by
    obtain ⟨F, hFsub, hFcard, -⟩ := hres.2.1
    have hFle := Finset.card_le_card hFsub
    omega
  refine ⟨?_, hmean'⟩
  exact kahnAggregateInsertionGood_presentWeightSpread_of_relativeCodegree
    (by omega : 3 ≤ k - 1) hJpos hcap (residualCountError_nonneg k C c hC hc hc1)
    (by positivity) (by unfold residualDegreeTolerance; positivity)
    (by positivity) (by positivity) hR hcap' hres

lemma eventually_kahnAggregateInsertionGood_residualPresentWeightSpread
    (k : ℕ → ℕ) (C g q eta : ℕ → ℝ) (c B : ℝ)
    (hk : Tendsto k atTop atTop) (hC0 : ∀ᶠ i in atTop, 0 ≤ C i)
    (hc : 0 < c) (hc1 : c ≤ 1) (hB : 0 ≤ B)
    (hg : Tendsto g atTop (𝓝 0)) (hgpos : ∀ᶠ i in atTop, 0 < g i)
    (hq : Tendsto q atTop (𝓝 0)) (hq0 : ∀ᶠ i in atTop, 0 ≤ q i)
    (heta0 : ∀ᶠ i in atTop, 0 ≤ eta i) :
    ∀ᶠ i in atTop, ∀ M cap : ℕ, ∀ H : Finset (Edge (k i)), ∀ Z : Edge (k i),
      ∀ hZ : Z ∈ allEdges (k i), 0 < cap → 1 ≤ (M : ℝ) / k i →
      (cap : ℝ) / ((M : ℝ) / k i) ≤ g i →
      KahnAggregateInsertionGood (k i) M cap (C i) (q i) (eta i) B H →
      c^2 * matchingWeightTarget (k i) H ≤ completionWeight H Z →
      PresentWeightSpread (reindexGraphAway H Z hZ)
          (residualPresentTolerance (k i) (C i) c (g i) (q i) (eta i) B)
          (residualPresentTolerance (k i) (C i) c (g i) (q i) (eta i) B) ∧
        ((M : ℝ) / k i) / 2 ≤ ((reindexGraphAway H Z hZ).card : ℝ) / ((k i - 1 : ℕ) : ℝ) := by
  have hq' := (tendsto_order.mp (residualDegreeTolerance_tendsto_zero_along k B q g hk hq hg)).2
    1 (by norm_num : (0 : ℝ) < 1)
  have hg2 : Tendsto (fun i ↦ 2 * g i) atTop (𝓝 0) := by simpa only [mul_zero] using hg.const_mul 2
  have hg2pos : ∀ᶠ i in atTop, 0 < 2 * g i := by filter_upwards [hgpos] with i hi; positivity
  have hR := (entropyRatioEnvelope_tendsto_atTop _ hg2 hg2pos).eventually_ge_atTop 2
  have hcast : Tendsto (fun i ↦ (k i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  filter_upwards [hk.eventually_ge_atTop 4, hC0, hgpos, hq0, heta0, hq', hR,
    hcast.eventually_ge_atTop (6 * (B + 1))] with i hki hCi hgi hqi hetai hq'i hRi hsizei
  intro M cap H Z hZ hcap hmean hrelative hgood hweight
  exact kahnAggregateInsertionGood_residualPresentWeightSpread hki hcap hZ
    hCi hc hc1 hgi hqi hetai hB hmean hsizei hrelative hq'i.le (by linarith) hgood hweight

end

end Erdos747
