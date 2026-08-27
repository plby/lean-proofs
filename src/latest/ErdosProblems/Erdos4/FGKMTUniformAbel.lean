import ErdosProblems.Erdos4.FGKMTUniformHarmonic
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound
import BoundedGaps.Maynard.LogarithmicAbelMain

/-! Abel summation with an explicit logarithmic modulus error. -/

open scoped BigOperators Topology

namespace Erdos4.FGKMT

open BoundedGaps.Maynard MeasureTheory

noncomputable def squarefreeHarmonicWeight (W n : ℕ) : ℝ :=
  if Squarefree n ∧ n.Coprime W then 1 / (Nat.totient n : ℝ) else 0

theorem squarefreeHarmonicWeight_zero (W : ℕ) : squarefreeHarmonicWeight W 0 = 0 := by
  simp [squarefreeHarmonicWeight]

theorem sum_start_one_eq {f : ℕ → ℝ} (hf : f 0 = 0) (T : ℕ) :
    (∑ n ∈ Finset.Icc 0 T, f n) = ∑ n ∈ Finset.Icc 1 T, f n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
  · intro n hn hnnot
    have hnle := (Finset.mem_Icc.mp hn).2
    have hnot : ¬(1 ≤ n ∧ n ≤ T) := by simpa only [Finset.mem_Icc] using hnnot
    have hnzero : n = 0 := by omega
    simpa only [hnzero] using hf

theorem cumulative_squarefreeHarmonicWeight (W : ℕ) (x : ℝ) :
    abelCumulative (squarefreeHarmonicWeight W) x = squarefreeCoprimeInvTotientMean W ⌊x⌋₊ := by
  unfold abelCumulative
  rw [sum_start_one_eq (squarefreeHarmonicWeight_zero W)]
  rfl

theorem squarefreeHarmonic_uniform_real_error {W : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    {x : ℝ} (hx : 1 ≤ x) :
    |squarefreeCoprimeInvTotientMean W ⌊x⌋₊ - coprimeHarmonicDensity W * Real.log x| ≤
      (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ)) := by
  have hfirst := squarefreeHarmonic_uniform_log_error (Q := ⌊x⌋₊) hW hSq
  have hfloor := abs_log_natFloor_sub_log_le_log_two_global hx
  have hρ0 := harmonicDensity_nonneg W
  have hρ1 := harmonicDensity_le_one hW
  have hlogW := Real.log_natCast_nonneg W
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hsecond : |coprimeHarmonicDensity W * (Real.log (⌊x⌋₊ : ℝ) - Real.log x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    exact (mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hfloor.trans hlog2)
  have hsplit : squarefreeCoprimeInvTotientMean W ⌊x⌋₊ - coprimeHarmonicDensity W * Real.log x =
      (squarefreeCoprimeInvTotientMean W ⌊x⌋₊ - coprimeHarmonicDensity W * Real.log (⌊x⌋₊ : ℝ)) +
        coprimeHarmonicDensity W * (Real.log (⌊x⌋₊ : ℝ) - Real.log x) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans (by nlinarith))

theorem weighted_harmonic_error {W T : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hT : 1 ≤ T)
    {f : ℝ → ℝ} {V : ℝ}
    (hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) T, DifferentiableAt ℝ f t)
    (hfDeriv : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) T))
    (hvariation : (∫ t in (1 : ℝ)..T, |deriv f t|) ≤ V) :
    |(∑ n ∈ Finset.Icc 1 T, f n * squarefreeHarmonicWeight W n) -
        logarithmicAbelMain T (coprimeHarmonicDensity W) f| ≤
      (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ)) * (|f T| + V) := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hE : 0 ≤ (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ)) := by
    have hh := uniformHarmonicConstant_pos
    positivity
  have hlogcont : ContinuousOn (fun t : ℝ => coprimeHarmonicDensity W * Real.log t)
      (Set.Icc (1 : ℝ) T) :=
    continuousOn_const.mul (continuousOn_id.log (fun t ht => (zero_lt_one.trans_le ht.1).ne'))
  have hh := abs_weightedSum_sub_logarithmicAbelMain_le (V := V) hT (squarefreeHarmonicWeight_zero W) hE
    hfDiff hfDeriv.integrableOn_Icc
    (hfDeriv.abs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    ((hfDeriv.mul hlogcont).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (fun t ht => by
      rw [cumulative_squarefreeHarmonicWeight]
      exact squarefreeHarmonic_uniform_real_error hW hSq ht.1)
    (by rw [← intervalIntegral.integral_of_le hTreal]; exact hvariation)
  rw [sum_start_one_eq (f := fun n => f n * squarefreeHarmonicWeight W n)
    (by rw [squarefreeHarmonicWeight_zero, mul_zero])] at hh
  exact hh

theorem monotone_variation_le_one {f : ℝ → ℝ} {T : ℝ} (hT : 1 ≤ T)
    (hfDiff : ∀ t ∈ Set.Icc (1 : ℝ) T, DifferentiableAt ℝ f t)
    (hfDeriv : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) T))
    (hderiv : ∀ t ∈ Set.Icc (1 : ℝ) T, deriv f t ≤ 0)
    (hf1 : f 1 ≤ 1) (hfT : 0 ≤ f T) :
    (∫ t in (1 : ℝ)..T, |deriv f t|) ≤ 1 := by
  have hcont : ContinuousOn (deriv f) (Set.uIcc 1 T) := by
    rw [Set.uIcc_of_le hT]
    exact hfDeriv
  have hFTC : (∫ t in (1 : ℝ)..T, deriv f t) = f T - f 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hcont.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact (hfDiff t ht).hasDerivAt
  have heq : (∫ t in (1 : ℝ)..T, |deriv f t|) = -(∫ t in (1 : ℝ)..T, deriv f t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact abs_of_nonpos (hderiv t ht)
  rw [heq, hFTC]
  linarith

end Erdos4.FGKMT
