import ErdosProblems.Erdos67.StationaryDilationIdentity
import ErdosProblems.Erdos67.StationaryHarmonicCutoff
import ErdosProblems.Erdos67.StationaryLimit

/-!
# Finite conditional-dilation estimates

The two errors are the boundary of the multiplicative averaging box and the
discarded part of the harmonic interval. Both are estimated explicitly.
-/

open scoped BigOperators Topology
open Finset Filter
open MeasureTheory hiding average

namespace Erdos67.StationaryModel

open FiniteEntropy StationaryDilationAverage StationaryHarmonicAverage

theorem abs_finite_expectation_le {A : Type*} [Fintype A] (P : FinProb A)
    (F : A → ℝ) (B : ℝ) (hF : ∀ a, |F a| ≤ B) :
    |∑ a, P a * F a| ≤ B := by
  calc
    |∑ a, P a * F a| ≤ ∑ a, |P a * F a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, P a * B := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (prob_nonneg P a)]
      exact mul_le_mul_of_nonneg_left (hF a) (prob_nonneg P a)
    _ = B := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

/-- Uniform averaging of an observable over the multiplicative box. -/
noncomputable def boxMean (t : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ a : Fin (t + 1) → Fin (t + 1), uniformVector a * F (boxValue a)

theorem abs_boxMean_dilation_sub_le (t d : ℕ) (hd : 0 < d) (hdt : d ≤ t + 1)
    (F : ℕ → ℝ) (B : ℝ) (hF : ∀ n, |F n| ≤ B) :
    |boxMean t (fun D ↦ F (d * D)) - boxMean t F| ≤ 2 * B / (t + 1 : ℕ) := by
  let i : Fin (t + 1) := ⟨d - 1, by omega⟩
  have hi : i.val + 1 = d := by dsimp [i]; omega
  simpa only [boxMean, hi] using abs_uniform_dilation_sub_le i F B hF

theorem abs_boxMean_truncated_dilation_sub_le (t d M : ℕ)
    (hd : 0 < d) (hdt : d ≤ t + 1) (hM : M ≤ t + 1)
    (G : ℕ → ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ D N, |G D N| ≤ B) :
    |boxMean t (fun D ↦ truncatedAverage (t + 1) M (G (d * D))) -
      boxMean t (fun D ↦ truncatedAverage (t + 1) M (G D))| ≤
        2 * B / (t + 1 : ℕ) := by
  unfold boxMean
  rw [sum_mul_truncatedAverage, sum_mul_truncatedAverage, ← truncatedAverage_sub]
  apply abs_truncatedAverage_le (Nat.succ_pos t) hM _ _ (by positivity)
  intro N
  exact abs_boxMean_dilation_sub_le t d hd hdt (fun D ↦ G D N) B (fun D ↦ hG D N)

theorem abs_boxMean_truncated_sub_le (t d : ℕ) (hd : 0 < d)
    (G : ℕ → ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ D N, |G D N| ≤ B) :
    |boxMean t (fun D ↦ truncatedAverage (t + 1) ((t + 1) / d) (G D)) -
      boxMean t (fun D ↦ average (t + 1) (G D))| ≤
        (d : ℝ) * B / mass (t + 1) := by
  unfold boxMean
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply abs_finite_expectation_le
  intro a
  rw [abs_sub_comm]
  exact abs_average_sub_truncated_le (G (boxValue a)) B hB (hG _) (Nat.succ_pos t) d hd

theorem abs_boxMean_dilated_cutoff_sub_le (t d : ℕ) (hd : 0 < d) (hdt : d ≤ t + 1)
    (G : ℕ → ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ D N, |G D N| ≤ B) :
    |boxMean t (fun D ↦ truncatedAverage (t + 1) ((t + 1) / d) (G (d * D))) -
      boxMean t (fun D ↦ average (t + 1) (G D))| ≤
        2 * B / (t + 1 : ℕ) + (d : ℝ) * B / mass (t + 1) := by
  apply (abs_sub_le _
    (boxMean t (fun D ↦ truncatedAverage (t + 1) ((t + 1) / d) (G D))) _).trans
  exact add_le_add
    (abs_boxMean_truncated_dilation_sub_le t d ((t + 1) / d) hd hdt
      (Nat.div_le_self _ _) G B hB hG)
    (abs_boxMean_truncated_sub_le t d hd G B hB hG)

/-- The divisibility indicator, expressed on the recorded residue. -/
noncomputable def residueZeroIndicator (d : ℕ+) (ω : Configuration) : ℝ :=
  if ω.2 d = 0 then 1 else 0

theorem continuous_residueZeroIndicator (d : ℕ+) : Continuous (residueZeroIndicator d) := by
  have h : Continuous (fun z : ZMod d.val ↦ if z = 0 then (1 : ℝ) else 0) :=
    continuous_of_discreteTopology
  exact h.comp ((continuous_apply d).comp continuous_snd)

noncomputable def conditionalDilationTest (d : ℕ+) (F : C((ℤ → Bool), ℝ)) :
    C(Configuration, ℝ) :=
  ⟨fun ω ↦ residueZeroIndicator d ω * F (signDilation d.val ω),
    (continuous_residueZeroIndicator d).mul (F.continuous.comp (continuous_signDilation d.val))⟩

theorem conditionalDilationTest_sample (d : ℕ+) (F : C((ℤ → Bool), ℝ))
    (f : ℕ → Bool) (D N : ℕ) :
    conditionalDilationTest d F (sample f D N) =
      if d.val ∣ N then F (signDilation d.val (sample f D N)) else 0 := by
  simp only [conditionalDilationTest, ContinuousMap.coe_mk, residueZeroIndicator, sample,
    ZMod.natCast_eq_zero_iff, ite_mul, one_mul, zero_mul]

theorem harmonic_average_conditional_dilation (T : ℕ) (d : ℕ+)
    (F : C((ℤ → Bool), ℝ)) (f : ℕ → Bool) (D : ℕ) :
    (d.val : ℝ) * average T (fun N ↦ conditionalDilationTest d F (sample f D N)) =
      truncatedAverage T (T / d.val) (fun N ↦ F ((sample f (d.val * D) N).1)) := by
  simp_rw [conditionalDilationTest_sample]
  unfold average truncatedAverage
  rw [← mul_div_assoc]
  simp_rw [mul_ite, mul_zero]
  rw [harmonic_sum_divisible_succ T d.val d.pos
    (fun N ↦ F (signDilation d.val (sample f D N)))]
  simp_rw [signDilation_sample]

theorem integral_samplingLaw_conditional_dilation (t : ℕ) (d : ℕ+)
    (F : C((ℤ → Bool), ℝ)) (f : ℕ → Bool) :
    (d.val : ℝ) * (∫ ω, conditionalDilationTest d F ω
      ∂(samplingLaw f t : Measure Configuration)) =
      boxMean t (fun D ↦ truncatedAverage (t + 1) ((t + 1) / d.val)
        (fun N ↦ F ((sample f (d.val * D) N).1))) := by
  rw [integral_samplingLaw, Finset.mul_sum]
  unfold boxMean
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_left_comm, harmonic_average_conditional_dilation]

theorem abs_integral_samplingLaw_conditional_dilation_sub_le
    (t : ℕ) (d : ℕ+) (hdt : d.val ≤ t + 1)
    (F : C((ℤ → Bool), ℝ)) (f : ℕ → Bool) :
    |(d.val : ℝ) * (∫ ω, conditionalDilationTest d F ω
      ∂(samplingLaw f t : Measure Configuration)) -
        ∫ ω, F ω.1 ∂(samplingLaw f t : Measure Configuration)| ≤
      2 * ‖F‖ / (t + 1 : ℕ) + (d.val : ℝ) * ‖F‖ / mass (t + 1) := by
  let F0 : C(Configuration, ℝ) := ⟨fun ω ↦ F ω.1, F.continuous.comp continuous_fst⟩
  change |(d.val : ℝ) * (∫ ω, conditionalDilationTest d F ω
    ∂(samplingLaw f t : Measure Configuration)) -
      ∫ ω, F0 ω ∂(samplingLaw f t : Measure Configuration)| ≤ _
  rw [integral_samplingLaw_conditional_dilation, integral_samplingLaw]
  exact abs_boxMean_dilated_cutoff_sub_le t d.val d.pos hdt
    (fun D N ↦ F ((sample f D N).1)) ‖F‖ (norm_nonneg _)
    (fun D N ↦ by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm ((sample f D N).1))

theorem conditional_dilation_error_tendsto_zero (d : ℕ) (B : ℝ) :
    Tendsto (fun t : ℕ ↦ 2 * B / (t + 1 : ℕ) + (d : ℝ) * B / mass (t + 1))
      atTop (nhds 0) := by
  have hsucc : Tendsto (fun t : ℕ ↦ t + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ n) tendsto_id
  have hcast : Tendsto (fun t : ℕ ↦ ((t + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsucc
  have hfirst : Tendsto (fun t : ℕ ↦ 2 * B / (t + 1 : ℕ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := 2 * B)).mul (tendsto_inv_atTop_zero.comp hcast)
  have hsecond : Tendsto (fun t : ℕ ↦ (d : ℝ) * B / mass (t + 1))
      atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := (d : ℝ) * B)).mul (tendsto_inv_mass.comp hsucc)
  simpa only [add_zero] using hfirst.add hsecond

/-- Conditional dilation for every fixed positive dilation and continuous sign
observable. The cutoff and box errors vanish along the same subsequence. -/
theorem samplingLaw_limit_conditional_dilation
    (f : ℕ → Bool) (Q : ProbabilityMeasure Configuration) (r : ℕ → ℕ)
    (hr : StrictMono r) (hQ : Tendsto (samplingLaw f ∘ r) atTop (nhds Q))
    (d : ℕ+) (F : C((ℤ → Bool), ℝ)) :
    (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
      (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration) := by
  have htest := tendsto_integral_continuous_observable hQ
    (conditionalDilationTest d F) (conditionalDilationTest d F).continuous
  have hplain := tendsto_integral_continuous_observable hQ
    (fun ω ↦ F ω.1) (F.continuous.comp continuous_fst)
  have hlim := ((htest.const_mul (d.val : ℝ)).sub hplain).abs
  have herror := (conditional_dilation_error_tendsto_zero d.val ‖F‖).comp hr.tendsto_atTop
  have hbound : ∀ᶠ n in atTop,
      |(d.val : ℝ) * (∫ ω, conditionalDilationTest d F ω
        ∂(samplingLaw f (r n) : Measure Configuration)) -
          ∫ ω, F ω.1 ∂(samplingLaw f (r n) : Measure Configuration)| ≤
        2 * ‖F‖ / (r n + 1 : ℕ) + (d.val : ℝ) * ‖F‖ / mass (r n + 1) := by
    filter_upwards [hr.tendsto_atTop.eventually (eventually_ge_atTop d.val)] with n hn
    exact abs_integral_samplingLaw_conditional_dilation_sub_le (r n) d
      (hn.trans (Nat.le_succ _)) F f
  have hle := le_of_tendsto_of_tendsto hlim herror hbound
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))).symm

/-- The stationary model with all conditional-dilation identities and all block
moment bounds is obtained from the original bounded-discrepancy hypothesis. -/
theorem exists_stationary_dilation_limit_with_moments
    (f : ℕ → Bool) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ d M, 0 < d → |homogeneousSum f d M| ≤ C) :
    ∃ Q : ProbabilityMeasure Configuration,
      Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration) ∧
        (∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
          (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
            (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration)) ∧
        ∀ M, (∫ ω, blockSum M ω ^ 2 ∂(Q : Measure Configuration)) ≤ 4 * C ^ 2 := by
  obtain ⟨Q, r, hr, hQ, hstationary, hmom⟩ :=
    exists_stationary_sampling_limit_with_moments f C hC hbound
  exact ⟨Q, hstationary, samplingLaw_limit_conditional_dilation f Q r hr hQ, hmom⟩

end Erdos67.StationaryModel
