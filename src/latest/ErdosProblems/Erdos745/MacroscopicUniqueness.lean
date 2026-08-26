import ErdosProblems.Erdos745.SprinklingBound
import ErdosProblems.Erdos745.SupercriticalAssembly

/-! # Supercritical macroscopic uniqueness and the KSS logarithmic theorem -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

def smallMassPartial (lam : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), smallMassTerm lam k

theorem tendsto_smallMassPartial {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (smallMassPartial lam) atTop (𝓝 (smallMassLimit lam)) :=
  (tendsto_smallMass_partialSums hlam).comp (tendsto_add_atTop_nat 1)

theorem exists_close_smaller_parameter {lam e : ℝ} (hlam : 1 < lam) (he : 0 < e) :
    ∃ lam0 : ℝ, 1 < lam0 ∧ lam0 < lam ∧ |smallMassLimit lam0 - smallMassLimit lam| < e := by
  obtain ⟨r, hr, hclose⟩ := (Metric.continuousAt_iff.mp (continuousAt_smallMassLimit hlam)) e he
  let d := min ((lam - 1) / 2) (r / 2)
  have hd : 0 < d := lt_min (by linarith) (by linarith)
  have hd1 : d ≤ (lam - 1) / 2 := min_le_left _ _
  have hdr : d ≤ r / 2 := min_le_right _ _
  refine ⟨lam - d, by linarith, by linarith, ?_⟩
  have hdist : dist (lam - d) lam < r := by
    rw [Real.dist_eq, show lam - d - lam = -d by ring, abs_neg, abs_of_pos hd]
    linarith
  simpa only [Real.dist_eq] using hclose hdist

theorem exists_sprinkling_parameters {lam δ ε : ℝ} (hlam : 1 < lam) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ lam0 : ℝ, ∃ K : ℕ, 1 < lam0 ∧ lam0 < lam ∧
      smallMassPartial lam0 K - smallMassPartial lam K < ε * δ / 4 ∧
        Real.log 4 / ((K : ℝ) + 1) < (lam - lam0) * δ ^ 2 / 4 := by
  let e := ε * δ / 16
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨lam0, hlam0, h01, hclose⟩ := exists_close_smaller_parameter hlam he
  have ht0 : Tendsto (fun K ↦ |smallMassPartial lam0 K - smallMassLimit lam0|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_smallMassPartial hlam0).sub_const (smallMassLimit lam0)).abs
  have ht1 : Tendsto (fun K ↦ |smallMassPartial lam K - smallMassLimit lam|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_smallMassPartial hlam).sub_const (smallMassLimit lam)).abs
  have htE : Tendsto (fun K : ℕ ↦ Real.log 4 / ((K : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have heE : 0 < (lam - lam0) * δ ^ 2 / 4 := by positivity
  obtain ⟨K, hK0, hK1, hKE⟩ :=
    (((tendsto_order.mp ht0).2 e he).and
      (((tendsto_order.mp ht1).2 e he).and ((tendsto_order.mp htE).2 _ heE))).exists
  refine ⟨lam0, K, hlam0, h01, ?_, hKE⟩
  have h0 := (abs_lt.mp hK0).2
  have h1 := (abs_lt.mp hK1).1
  have hc := (abs_lt.mp hclose).2
  dsimp [e] at h0 h1 hc
  nlinarith [mul_pos hε hδ]

def smallVertexLossRatio (lam0 lam δ : ℝ) (K n : ℕ) : ℝ :=
  (expectation lam0 n (fun G ↦ ((smallComponentVertices G K).card : ℝ)) -
    expectation lam n (fun G ↦ ((smallComponentVertices G K).card : ℝ))) / (δ * n / 2)

theorem tendsto_smallVertexLossRatio {lam0 lam δ : ℝ}
    (hlam0 : 0 ≤ lam0) (hlam : 0 ≤ lam) (hδ : 0 < δ) (K : ℕ) :
    Tendsto (smallVertexLossRatio lam0 lam δ K) atTop
      (𝓝 ((smallMassPartial lam0 K - smallMassPartial lam K) / (δ / 2))) := by
  have ht := ((tendsto_smallComponentVertices_mean hlam0 K).sub
    (tendsto_smallComponentVertices_mean hlam K)).div_const (δ / 2)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold smallVertexLossRatio
  field_simp

theorem tendsto_sprinkleError_zero {lam0 lam δ : ℝ} {K : ℕ}
    (hK : Real.log 4 / ((K : ℝ) + 1) < (lam - lam0) * δ ^ 2 / 4) :
    Tendsto (sprinkleError lam0 lam δ K) atTop (𝓝 0) := by
  have hneg : Real.log 4 / ((K : ℝ) + 1) - (lam - lam0) * δ ^ 2 / 4 < 0 := by linarith
  exact Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hneg)

/-- In the exact independent-edge model, two components of positive linear size
have probability tending to zero at every fixed supercritical parameter. -/
theorem supercritical_macroscopic_uniqueness {lam : ℝ} (hlam : 1 < lam) :
    MacroscopicUniqueness lam := by
  intro δ hδ
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n ↦ ha.trans_le (probability_nonneg _ _ _))
  · intro ε hε
    obtain ⟨lam0, K, hlam0, h01, hgap, hKE⟩ := exists_sprinkling_parameters hlam hδ hε
    have hlam00 : 0 ≤ lam0 := (zero_lt_one.trans hlam0).le
    have hlam00' : 0 ≤ lam := (zero_lt_one.trans hlam).le
    let ell := (smallMassPartial lam0 K - smallMassPartial lam K) / (δ / 2)
    have hell : ell < ε / 2 := by
      dsimp [ell]
      apply (div_lt_iff₀ (by positivity : 0 < δ / 2)).mpr
      nlinarith
    have ht : Tendsto (fun n ↦ smallVertexLossRatio lam0 lam δ K n + sprinkleError lam0 lam δ K n)
        atTop (𝓝 ell) := by
      simpa only [add_zero] using (tendsto_smallVertexLossRatio hlam00 hlam00' hδ K).add
        (tendsto_sprinkleError_zero hKE)
    have hsmall := (tendsto_order.mp ht).2 ε (hell.trans (by linarith))
    have hlarge : ∀ᶠ n : ℕ in atTop, (K : ℝ) ≤ δ * n :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop K
    filter_upwards [hsmall, hlarge,
      tendsto_natCast_atTop_atTop.eventually_gt_atTop lam] with n hn hKn hln
    exact (probability_macro_le_sprinkling hlam00 h01 hln hδ hKn).trans_lt hn

/-- The corrected KSS logarithmic conclusion for each fixed `lam > 1`. -/
theorem kss_logarithmic : KSSLogarithmicStatement := by
  intro lam hlam A hA
  exact logarithmic_upper_of_macroscopic_uniqueness hlam
    (supercritical_macroscopic_uniqueness hlam) hA

end

end Erdos745
