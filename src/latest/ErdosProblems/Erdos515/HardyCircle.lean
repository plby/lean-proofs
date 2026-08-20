import Mathlib.Analysis.Polynomial.Fourier
import ErdosProblems.Erdos515.External.Ray.Misc.Circle

/-!
# Hardy-series Parseval on the unit circle

This focused module contains the small Hardy-space fragment needed by the Prawitz proof.  It is
kept separate from the formalization of Erdős Problem 764 so that importing Prawitz does not pull
in the umbrella `Mathlib` import used by that unrelated development.
-/

namespace Erdos515.Prawitz.HardyCircle

open Complex MeasureTheory Set Filter
open scoped Real Topology Polynomial ComplexConjugate

noncomputable section

def hardySum (u : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, u n * z ^ n

def partialPoly (u : ℕ → ℂ) (N : ℕ) : ℂ[X] :=
  ∑ n ∈ Finset.range N, Polynomial.monomial n (u n)

lemma eval_partialPoly (u : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (partialPoly u N).eval z = ∑ n ∈ Finset.range N, u n * z ^ n := by
  simp [partialPoly, Polynomial.eval_finsetSum, mul_comm]

lemma coeff_partialPoly (u : ℕ → ℂ) (N n : ℕ) :
    (partialPoly u N).coeff n = if n < N then u n else 0 := by
  classical
  simp [partialPoly, Polynomial.coeff_monomial, eq_comm]

lemma support_partialPoly_subset (u : ℕ → ℂ) (N : ℕ) :
    (partialPoly u N).support ⊆ Finset.range N := by
  intro n hn
  simp only [Polynomial.mem_support_iff] at hn
  by_contra h
  have hN : ¬ n < N := by simpa using h
  exact hn (by simp [coeff_partialPoly, hN])

lemma sum_range_sq_norm_eq_support (u : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 =
      ∑ n ∈ (partialPoly u N).support, ‖(partialPoly u N).coeff n‖ ^ 2 := by
  classical
  rw [Finset.sum_subset (support_partialPoly_subset u N)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [coeff_partialPoly, hn]
  · intro n _ hnS
    have hz : (partialPoly u N).coeff n = 0 := Polynomial.notMem_support_iff.mp hnS
    rw [hz]
    simp

lemma finite_norm_parseval (u : ℕ → ℂ) (N : ℕ) :
    Real.circleAverage
        (fun z ↦ ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 := by
  simp_rw [← eval_partialPoly]
  rw [← (partialPoly u N).sum_sq_norm_coeff_eq_circleAverage]
  exact (sum_range_sq_norm_eq_support u N).symm

lemma two_mul_re_mul_conj (a c : ℂ) :
    2 * (a * conj c).re = ‖a + c‖ ^ 2 - ‖a‖ ^ 2 - ‖c‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  ring

lemma finite_inner_parseval (u v : ℕ → ℂ) (N : ℕ) :
    Real.circleAverage
        (fun z ↦ ((∑ n ∈ Finset.range N, u n * z ^ n) *
          conj (∑ n ∈ Finset.range N, v n * z ^ n)).re) 0 1 =
      ∑ n ∈ Finset.range N, (u n * conj (v n)).re := by
  let U : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range N, u n * z ^ n
  let V : ℂ → ℂ := fun z ↦ ∑ n ∈ Finset.range N, v n * z ^ n
  have hU : Continuous U := by
    dsimp [U]
    fun_prop
  have hV : Continuous V := by
    dsimp [V]
    fun_prop
  have hiU : CircleIntegrable (fun z ↦ ‖U z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (hU.norm.pow 2).continuousOn
  have hiV : CircleIntegrable (fun z ↦ ‖V z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact (hV.norm.pow 2).continuousOn
  have hiUV : CircleIntegrable (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 := by
    apply ContinuousOn.circleIntegrable'
    exact ((hU.add hV).norm.pow 2).continuousOn
  have hpoint : (fun z ↦ 2 * (U z * conj (V z)).re) =
      fun z ↦ ‖U z + V z‖ ^ 2 - ‖U z‖ ^ 2 - ‖V z‖ ^ 2 := by
    funext z
    exact two_mul_re_mul_conj (U z) (V z)
  have havg : 2 * Real.circleAverage (fun z ↦ (U z * conj (V z)).re) 0 1 =
      Real.circleAverage (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 -
        Real.circleAverage (fun z ↦ ‖U z‖ ^ 2) 0 1 -
          Real.circleAverage (fun z ↦ ‖V z‖ ^ 2) 0 1 := by
    have hsmul := Real.circleAverage_fun_smul (a := (2 : ℝ))
      (f := fun z ↦ (U z * conj (V z)).re) (c := (0 : ℂ)) (R := (1 : ℝ))
    rw [show 2 * Real.circleAverage (fun z ↦ (U z * conj (V z)).re) 0 1 =
        Real.circleAverage (fun z ↦ 2 * (U z * conj (V z)).re) 0 1 by
      simpa only [smul_eq_mul] using hsmul.symm]
    rw [hpoint]
    change Real.circleAverage
        ((fun z ↦ ‖U z + V z‖ ^ 2) - (fun z ↦ ‖U z‖ ^ 2) -
          (fun z ↦ ‖V z‖ ^ 2)) 0 1 = _
    rw [Real.circleAverage_sub (hiUV.sub hiU) hiV,
      Real.circleAverage_sub hiUV hiU]
  have hUeq : Real.circleAverage (fun z ↦ ‖U z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n‖ ^ 2 := by
    simpa [U] using finite_norm_parseval u N
  have hVeq : Real.circleAverage (fun z ↦ ‖V z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖v n‖ ^ 2 := by
    simpa [V] using finite_norm_parseval v N
  have hUVeq : Real.circleAverage (fun z ↦ ‖U z + V z‖ ^ 2) 0 1 =
      ∑ n ∈ Finset.range N, ‖u n + v n‖ ^ 2 := by
    simpa only [U, V, Finset.sum_add_distrib, add_mul] using
      finite_norm_parseval (fun n ↦ u n + v n) N
  rw [hUeq, hVeq, hUVeq] at havg
  have hcoeff : (∑ n ∈ Finset.range N, ‖u n + v n‖ ^ 2) -
      (∑ n ∈ Finset.range N, ‖u n‖ ^ 2) -
        (∑ n ∈ Finset.range N, ‖v n‖ ^ 2) =
      2 * ∑ n ∈ Finset.range N, (u n * conj (v n)).re := by
    calc
      _ = ∑ n ∈ Finset.range N,
          (‖u n + v n‖ ^ 2 - ‖u n‖ ^ 2 - ‖v n‖ ^ 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = ∑ n ∈ Finset.range N, 2 * (u n * conj (v n)).re := by
            apply Finset.sum_congr rfl
            intro n _
            exact (two_mul_re_mul_conj (u n) (v n)).symm
      _ = _ := by rw [Finset.mul_sum]
  rw [hcoeff] at havg
  exact mul_left_cancel₀ two_ne_zero havg

lemma uniform_partial_hardySum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖)) :
    TendstoUniformlyOn
      (fun N z ↦ ∑ n ∈ Finset.range N, u n * z ^ n) (hardySum u) atTop
      (Metric.sphere (0 : ℂ) 1) := by
  apply tendstoUniformlyOn_tsum_nat hu
  intro n z hz
  rw [norm_mul, norm_pow]
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  simp [hznorm]

lemma tendsto_circleAverage_of_uniform {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ}
    (hf : ∀ N, ContinuousOn (f N) (Metric.sphere (0 : ℂ) 1))
    (h : TendstoUniformlyOn f g atTop (Metric.sphere (0 : ℂ) 1)) :
    Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (Real.circleAverage g 0 1)) := by
  unfold Real.circleAverage
  apply tendsto_const_nhds.smul
    (TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (Filter.Eventually.of_forall fun N ↦
        (hf N).comp (continuous_circleMap 0 1).continuousOn
          (fun x _ ↦ by simpa only [abs_one] using circleMap_mem_sphere' 0 1 x)) ?_)
  have hc := h.comp (circleMap 0 1)
  exact hc.mono (by
    intro x _
    simpa only [Set.mem_preimage, abs_one] using circleMap_mem_sphere' 0 1 x)

lemma norm_partial_hardySum_le_tsum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖))
    (N : ℕ) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ≤ ∑' n, ‖u n‖ := by
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  calc
    ‖∑ n ∈ Finset.range N, u n * z ^ n‖ ≤
        ∑ n ∈ Finset.range N, ‖u n * z ^ n‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N, ‖u n‖ := by simp [norm_mul, norm_pow, hznorm]
    _ ≤ ∑' n, ‖u n‖ := hu.sum_le_tsum (Finset.range N) (fun n _ ↦ norm_nonneg _)

lemma norm_hardySum_le_tsum {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖))
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ‖hardySum u z‖ ≤ ∑' n, ‖u n‖ := by
  have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
  have hs : Summable (fun n ↦ ‖u n * z ^ n‖) := by
    simpa [norm_mul, norm_pow, hznorm] using hu
  calc
    ‖hardySum u z‖ ≤ ∑' n, ‖u n * z ^ n‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n, ‖u n‖ := by congr 1; funext n; simp [norm_mul, norm_pow, hznorm]

lemma uniform_partial_inner {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    TendstoUniformlyOn
      (fun N z ↦ ((∑ n ∈ Finset.range N, u n * z ^ n) *
        conj (∑ n ∈ Finset.range N, v n * z ^ n)).re)
      (fun z ↦ (hardySum u z * conj (hardySum v z)).re) atTop
      (Metric.sphere (0 : ℂ) 1) := by
  let U : ℕ → ℂ → ℂ := fun N z ↦ ∑ n ∈ Finset.range N, u n * z ^ n
  let V : ℕ → ℂ → ℂ := fun N z ↦ ∑ n ∈ Finset.range N, v n * z ^ n
  have hU : TendstoUniformlyOn U (hardySum u) atTop (Metric.sphere (0 : ℂ) 1) := by
    simpa only [U] using uniform_partial_hardySum hu
  have hV : TendstoUniformlyOn V (hardySum v) atTop (Metric.sphere (0 : ℂ) 1) := by
    simpa only [V] using uniform_partial_hardySum hv
  have hVc : TendstoUniformlyOn (fun N z ↦ conj (V N z))
      (fun z ↦ conj (hardySum v z)) atTop (Metric.sphere (0 : ℂ) 1) := by
    exact Complex.isometry_conj.uniformContinuous.comp_tendstoUniformlyOn hV
  have hpair : TendstoUniformlyOn (fun N z ↦ (U N z, conj (V N z)))
      (fun z ↦ (hardySum u z, conj (hardySum v z))) atTop
      (Metric.sphere (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hU hVc ⊢
    intro ε hε
    filter_upwards [hU ε hε, hVc ε hε] with N hUN hVN
    intro z hz
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hUN z hz, hVN z hz⟩
  let Bu : ℝ := ∑' n, ‖u n‖
  let Bv : ℝ := ∑' n, ‖v n‖
  let s : Set (ℂ × ℂ) := Metric.closedBall 0 Bu ×ˢ Metric.closedBall 0 Bv
  have hs : Bornology.IsBounded s := by
    exact Metric.isBounded_closedBall.prod Metric.isBounded_closedBall
  have hpartial : ∀ N z, z ∈ Metric.sphere (0 : ℂ) 1 →
      (U N z, conj (V N z)) ∈ s := by
    intro N z hz
    constructor
    · simpa [s, Bu, Metric.mem_closedBall] using norm_partial_hardySum_le_tsum hu N hz
    · simpa [s, Bv, Metric.mem_closedBall, Complex.norm_conj] using
        norm_partial_hardySum_le_tsum hv N hz
  have hlimit : ∀ z, z ∈ Metric.sphere (0 : ℂ) 1 →
      (hardySum u z, conj (hardySum v z)) ∈ s := by
    intro z hz
    constructor
    · simpa [s, Bu, Metric.mem_closedBall] using norm_hardySum_le_tsum hu hz
    · simpa [s, Bv, Metric.mem_closedBall, Complex.norm_conj] using
        norm_hardySum_le_tsum hv hz
  have hmul := hs.uniformContinuousOn_smul.comp_tendstoUniformlyOn_eventually
    (Filter.Eventually.of_forall hpartial) hlimit hpair
  have hre := Complex.uniformContinuous_re.comp_tendstoUniformlyOn hmul
  simpa only [U, V, Function.uncurry_apply_pair, smul_eq_mul, Function.comp_def] using hre

lemma summable_re_mul_conj {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    Summable (fun n ↦ (u n * conj (v n)).re) := by
  let Bv : ℝ := ∑' n, ‖v n‖
  have hv_le : ∀ n, ‖v n‖ ≤ Bv := by
    intro n
    have h := hv.sum_le_tsum {n} (fun i _ ↦ norm_nonneg (v i))
    simpa [Bv] using h
  apply (hu.mul_left Bv).of_norm_bounded
  intro n
  calc
    ‖(u n * conj (v n)).re‖ ≤ ‖u n * conj (v n)‖ := Complex.abs_re_le_norm _
    _ = ‖u n‖ * ‖v n‖ := by simp [norm_mul]
    _ ≤ ‖u n‖ * Bv := mul_le_mul_of_nonneg_left (hv_le n) (norm_nonneg (u n))
    _ = Bv * ‖u n‖ := mul_comm _ _

theorem infinite_inner_parseval {u v : ℕ → ℂ}
    (hu : Summable (fun n ↦ ‖u n‖)) (hv : Summable (fun n ↦ ‖v n‖)) :
    Real.circleAverage (fun z ↦ (hardySum u z * conj (hardySum v z)).re) 0 1 =
      ∑' n, (u n * conj (v n)).re := by
  let f : ℕ → ℂ → ℝ := fun N z ↦
    ((∑ n ∈ Finset.range N, u n * z ^ n) *
      conj (∑ n ∈ Finset.range N, v n * z ^ n)).re
  have hf_cont : ∀ N, ContinuousOn (f N) (Metric.sphere (0 : ℂ) 1) := by
    intro N
    apply Continuous.continuousOn
    dsimp [f]
    fun_prop
  have hleft : Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (Real.circleAverage (fun z ↦ (hardySum u z * conj (hardySum v z)).re) 0 1)) :=
    tendsto_circleAverage_of_uniform hf_cont (by
      simpa only [f] using uniform_partial_inner hu hv)
  have hright : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (u n * conj (v n)).re) atTop
      (𝓝 (∑' n, (u n * conj (v n)).re)) :=
    (summable_re_mul_conj hu hv).hasSum.tendsto_sum_nat
  have hright' : Tendsto (fun N ↦ Real.circleAverage (f N) 0 1) atTop
      (𝓝 (∑' n, (u n * conj (v n)).re)) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall fun N ↦ by
      symm
      simpa only [f] using finite_inner_parseval u v N
  exact tendsto_nhds_unique hleft hright'

theorem infinite_norm_parseval {u : ℕ → ℂ} (hu : Summable (fun n ↦ ‖u n‖)) :
    Real.circleAverage (fun z ↦ ‖hardySum u z‖ ^ 2) 0 1 = ∑' n, ‖u n‖ ^ 2 := by
  have hreal (x : ℝ) : (((x : ℂ) ^ 2).re) = x ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  simpa only [Complex.mul_conj', hreal] using infinite_inner_parseval hu hu

end

end Erdos515.Prawitz.HardyCircle
