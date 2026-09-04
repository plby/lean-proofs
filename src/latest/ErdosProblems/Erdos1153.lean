/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1153.
https://www.erdosproblems.com/forum/thread/1153

Informal authors:
- Terence Tao

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1153.md
-/
import ErdosProblems.Erdos1153.Erdos1153Base

open scoped BigOperators Topology
open Finset Set Polynomial Filter MeasureTheory

namespace Erdos1153

lemma test_heightDropKernel_eq_integral {eta t : ℝ} (heta : 0 < eta) :
    heightDropKernel eta t =
      ∫ s in eta..2 * eta, s / (t ^ 2 + s ^ 2) := by
  have hden : ∀ s ∈ Set.uIcc eta (2 * eta), t ^ 2 + s ^ 2 ≠ 0 := by
    intro s hs
    have hspos : 0 < s := by
      rw [Set.uIcc_of_le (by linarith)] at hs
      linarith [hs.1]
    positivity
  have hderiv : ∀ s ∈ Set.uIcc eta (2 * eta),
      HasDerivAt (fun u : ℝ ↦ Real.log (t ^ 2 + u ^ 2) / 2)
        (s / (t ^ 2 + s ^ 2)) s := by
    intro s hs
    have hinner : HasDerivAt (fun u : ℝ ↦ t ^ 2 + u ^ 2) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).const_add (t ^ 2)
    have hout : HasDerivAt (fun u : ℝ ↦ Real.log (t ^ 2 + u ^ 2) / 2)
        (((t ^ 2 + s ^ 2)⁻¹ * (2 * s)) / 2) s := by
      simpa [Function.comp_def] using
        ((Real.hasDerivAt_log (hden s hs)).comp s hinner).div_const 2
    apply hout.congr_deriv
    field_simp
  have hcont : ContinuousOn (fun s : ℝ ↦ s / (t ^ 2 + s ^ 2))
      (Set.uIcc eta (2 * eta)) := by
    apply ContinuousOn.div continuousOn_id
      (continuousOn_const.add (continuousOn_id.pow 2))
    exact hden
  rw [heightDropKernel]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : 0 < t ^ 2 + eta ^ 2 := by positivity
  have h2 : 0 < t ^ 2 + (2 * eta) ^ 2 := by positivity
  rw [Real.log_div h2.ne' h1.ne']
  ring

lemma test_integral_cauchy_numerator {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, s / (t ^ 2 + s ^ 2) = Real.pi := by
  have heq : (fun t : ℝ ↦ s / (t ^ 2 + s ^ 2)) =
      fun t ↦ Real.pi * upperPoissonKernel s t := by
    funext t
    unfold upperPoissonKernel
    field_simp [Real.pi_ne_zero]
  rw [heq, MeasureTheory.integral_const_mul, integral_upperPoissonKernel hs]
  ring

lemma test_integrable_heightDrop_product {eta : ℝ} (heta : 0 < eta) :
    Integrable (Function.uncurry (fun s t : ℝ ↦ s / (t ^ 2 + s ^ 2)))
      ((volume.restrict (Set.uIoc eta (2 * eta))).prod volume) := by
  let μ := volume.restrict (Set.uIoc eta (2 * eta))
  have huIoc : Set.uIoc eta (2 * eta) = Set.Ioc eta (2 * eta) :=
    Set.uIoc_of_le (by linarith)
  let : IsFiniteMeasure μ := by
    dsimp only [μ]
    rw [huIoc]
    infer_instance
  have hmeas : Measurable
      (Function.uncurry (fun s t : ℝ ↦ s / (t ^ 2 + s ^ 2))) :=
    measurable_fst.div
      ((measurable_snd.pow_const 2).add (measurable_fst.pow_const 2))
  apply (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [huIoc] at hs
      linarith [hs.1]
    have heq : (fun t : ℝ ↦ s / (t ^ 2 + s ^ 2)) =
        fun t ↦ Real.pi * upperPoissonKernel s t := by
      funext t
      unfold upperPoissonKernel
      field_simp [Real.pi_ne_zero]
    simp only [Function.uncurry_apply_pair]
    rw [heq]
    exact (integrable_upperPoissonKernel hspos.ne').const_mul Real.pi
  · refine (integrable_const Real.pi : Integrable (fun _ : ℝ ↦ Real.pi) μ).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [huIoc] at hs
      linarith [hs.1]
    have hnorm : (fun t : ℝ ↦ ‖s / (t ^ 2 + s ^ 2)‖) =
        fun t ↦ s / (t ^ 2 + s ^ 2) := by
      funext t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg hspos.le (by positivity)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm, test_integral_cauchy_numerator hspos]

lemma test_integral_heightDropKernel {eta : ℝ} (heta : 0 < eta) :
    ∫ t : ℝ, heightDropKernel eta t = Real.pi * eta := by
  let f : ℝ → ℝ → ℝ := fun s t ↦ s / (t ^ 2 + s ^ 2)
  have hprod : Integrable (Function.uncurry f)
      ((volume.restrict (Set.uIoc eta (2 * eta))).prod volume) :=
    test_integrable_heightDrop_product heta
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod
  have hleft : (∫ s in eta..2 * eta, ∫ t : ℝ, f s t) =
      Real.pi * eta := by
    rw [intervalIntegral.integral_congr (fun s hs ↦
      test_integral_cauchy_numerator (by
        rw [Set.uIcc_of_le (by linarith)] at hs
        linarith [hs.1]))]
    simp
    ring
  have hright : (∫ t : ℝ, ∫ s in eta..2 * eta, f s t) =
      ∫ t : ℝ, heightDropKernel eta t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [test_heightDropKernel_eq_integral heta]
  rw [hleft, hright] at hswap
  exact hswap.symm

lemma test_integrable_heightDropKernel {eta : ℝ} (heta : 0 < eta) :
    Integrable (heightDropKernel eta) := by
  have hmajor : Integrable (fun t : ℝ ↦
      (3 / 2 : ℝ) * eta ^ 2 / (t ^ 2 + eta ^ 2)) := by
    have heq : (fun t : ℝ ↦
        (3 / 2 : ℝ) * eta ^ 2 / (t ^ 2 + eta ^ 2)) =
        fun t ↦ (3 * Real.pi * eta / 2) * upperPoissonKernel eta t := by
      funext t
      unfold upperPoissonKernel
      field_simp [Real.pi_ne_zero]
    rw [heq]
    exact (integrable_upperPoissonKernel heta.ne').const_mul
      (3 * Real.pi * eta / 2)
  apply hmajor.mono'
  · have hcont : Continuous (heightDropKernel eta) := by
      unfold heightDropKernel
      apply Continuous.div_const
      apply Continuous.log
      · apply Continuous.div
        · fun_prop
        · fun_prop
        · intro t
          positivity
      · intro t
        positivity
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (heightDropKernel_nonneg heta)]
    exact heightDropKernel_le heta

lemma test_integrableOn_Ioi_inv_sq {D : ℝ} (hD : 0 < D) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Ioi D) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hD
  apply h.congr_fun _ measurableSet_Ioi
  intro t ht
  change t ^ (-2 : ℝ) = (t ^ 2)⁻¹
  rw [Real.rpow_neg (le_of_lt (hD.trans ht)), Real.rpow_two]

lemma test_integral_Ioi_inv_sq {D : ℝ} (hD : 0 < D) :
    ∫ t in Set.Ioi D, (t ^ 2)⁻¹ = D⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hD
  have heq : (∫ t in Set.Ioi D, (t ^ 2)⁻¹) =
      ∫ t in Set.Ioi D, t ^ (-2 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t ^ 2)⁻¹ = t ^ (-2 : ℝ)
    symm
    rw [Real.rpow_neg (le_of_lt (hD.trans ht)), Real.rpow_two]
  rw [heq, h]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

lemma test_heightDropKernel_tail_right {eta D : ℝ}
    (heta : 0 < eta) (hD : 0 < D) :
    ∫ t in Set.Ioi D, heightDropKernel eta t ≤
      (3 / 2 : ℝ) * eta ^ 2 / D := by
  have hmajor : IntegrableOn (fun t : ℝ ↦
      (3 / 2 : ℝ) * eta ^ 2 * (t ^ 2)⁻¹) (Set.Ioi D) :=
    (test_integrableOn_Ioi_inv_sq hD).const_mul ((3 / 2 : ℝ) * eta ^ 2)
  have hker : IntegrableOn (heightDropKernel eta) (Set.Ioi D) :=
    (test_integrable_heightDropKernel heta).integrableOn
  calc
    (∫ t in Set.Ioi D, heightDropKernel eta t) ≤
        ∫ t in Set.Ioi D, (3 / 2 : ℝ) * eta ^ 2 * (t ^ 2)⁻¹ := by
      apply setIntegral_mono_on hker hmajor measurableSet_Ioi
      intro t ht
      have htpos : 0 < t := hD.trans ht
      have hbase := heightDropKernel_le (t := t) heta
      calc
        heightDropKernel eta t ≤
            (3 / 2 : ℝ) * eta ^ 2 / (t ^ 2 + eta ^ 2) := hbase
        _ ≤ (3 / 2 : ℝ) * eta ^ 2 * (t ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg eta]
    _ = (3 / 2 : ℝ) * eta ^ 2 / D := by
      rw [MeasureTheory.integral_const_mul, test_integral_Ioi_inv_sq hD]
      ring

lemma test_heightDropKernel_even (eta t : ℝ) :
    heightDropKernel eta (-t) = heightDropKernel eta t := by
  unfold heightDropKernel
  congr 3 <;> ring

lemma test_heightDropKernel_tail_left {eta D : ℝ}
    (heta : 0 < eta) (hD : 0 < D) :
    ∫ t in Set.Iic (-D), heightDropKernel eta t ≤
      (3 / 2 : ℝ) * eta ^ 2 / D := by
  have hchange := integral_comp_neg_Ioi D (heightDropKernel eta)
  simp_rw [test_heightDropKernel_even] at hchange
  rw [← hchange]
  exact test_heightDropKernel_tail_right heta hD

lemma test_heightDropKernel_tail {eta D : ℝ}
    (heta : 0 < eta) (hD : 0 < D) :
    ∫ t in Set.Iic (-D) ∪ Set.Ioi D, heightDropKernel eta t ≤
      3 * eta ^ 2 / D := by
  have hdisj : Disjoint (Set.Iic (-D)) (Set.Ioi D) := by
    rw [Set.disjoint_left]
    intro t htleft htright
    simp only [Set.mem_Iic] at htleft
    simp only [Set.mem_Ioi] at htright
    linarith
  have hker := test_integrable_heightDropKernel heta
  rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    hker.integrableOn hker.integrableOn]
  have hleft := test_heightDropKernel_tail_left heta hD
  have hright := test_heightDropKernel_tail_right heta hD
  calc
    (∫ t in Set.Iic (-D), heightDropKernel eta t) +
        ∫ t in Set.Ioi D, heightDropKernel eta t ≤
        (3 / 2 : ℝ) * eta ^ 2 / D + (3 / 2 : ℝ) * eta ^ 2 / D :=
      add_le_add hleft hright
    _ = 3 * eta ^ 2 / D := by ring

lemma test_heightDropKernel_core_mass {eta D : ℝ}
    (heta : 0 < eta) (hD : 0 < D) :
    Real.pi * eta - 3 * eta ^ 2 / D ≤
      ∫ t in -D..D, heightDropKernel eta t := by
  have hker := test_integrable_heightDropKernel heta
  have hcomp : (Set.Ioc (-D) D)ᶜ = Set.Iic (-D) ∪ Set.Ioi D := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Ioc, Set.mem_union, Set.mem_Iic,
      Set.mem_Ioi, not_and_or, not_lt, not_le]
  have hsplit : (∫ t : ℝ, heightDropKernel eta t) =
      (∫ t in Set.Ioc (-D) D, heightDropKernel eta t) +
        ∫ t in (Set.Ioc (-D) D)ᶜ, heightDropKernel eta t :=
    (integral_add_compl measurableSet_Ioc hker).symm
  rw [hcomp] at hsplit
  have htail := test_heightDropKernel_tail heta hD
  rw [test_integral_heightDropKernel heta] at hsplit
  rw [intervalIntegral.integral_of_le (by linarith)]
  linarith

lemma test_heightDropKernel_interval_mass_lower {eta c R y : ℝ}
    (heta : 0 < eta) (hy : |y - c| ≤ R) {D : ℝ}
    (hD : 0 < D) :
    Real.pi * eta - 3 * eta ^ 2 / D ≤
      ∫ x in c - (R + D)..c + (R + D), heightDropKernel eta (x - y) := by
  have hcore := test_heightDropKernel_core_mass heta hD
  have hleft : y - D ≥ c - (R + D) := by
    rw [abs_le] at hy
    linarith [hy.1]
  have hright : y + D ≤ c + (R + D) := by
    rw [abs_le] at hy
    linarith [hy.2]
  have hnonneg : ∀ x, 0 ≤ heightDropKernel eta (x - y) :=
    fun x ↦ heightDropKernel_nonneg heta
  have hker := test_integrable_heightDropKernel heta
  have htrans : IntervalIntegrable (fun x ↦ heightDropKernel eta (x - y))
      volume (c - (R + D)) (c + (R + D)) := by
    have h := (hker.intervalIntegrable
      (a := c - (R + D) - y) (b := c + (R + D) - y)).comp_sub_right y
    convert h using 1 <;> ring
  have hmono := intervalIntegral.integral_mono_interval
    (a := y - D) (b := y + D) (c := c - (R + D)) (d := c + (R + D))
    hleft (by linarith) hright
    (Filter.Eventually.of_forall fun x ↦ hnonneg x) htrans
  have hshift : (∫ x in y - D..y + D, heightDropKernel eta (x - y)) =
      ∫ t in -D..D, heightDropKernel eta t := by
    convert (intervalIntegral.integral_comp_sub_right (f := heightDropKernel eta)
      (a := y - D) (b := y + D) y) using 1 <;> ring_nf
  rw [hshift] at hmono
  exact hcore.trans hmono

lemma test_localNodeCount_le_of_heightDrop_on_interval {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {c R D eta E rhoMax : ℝ}
    (hR : 0 ≤ R) (hD : 0 < D) (heta : 0 < eta)
    (hcore : 0 ≤ Real.pi * eta - 3 * eta ^ 2 / D)
    (happrox : ∀ x ∈ Set.Icc (c - (R + D)) (c + (R + D)),
      (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) ≤
        Real.pi * eta * rhoMax + E) :
    (localNodeCount X c R : ℝ) *
        (Real.pi * eta - 3 * eta ^ 2 / D) ≤
      (n : ℝ) * (2 * (R + D)) * (Real.pi * eta * rhoMax + E) := by
  let s : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ |c - X k| ≤ R
  let F : ℝ → ℝ := fun x ↦
    (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k)
  have hker := test_integrable_heightDropKernel heta
  have htermInt : ∀ k : Fin n, IntervalIntegrable
      (fun x ↦ heightDropKernel eta (x - X k)) volume
        (c - (R + D)) (c + (R + D)) := by
    intro k
    have h := (hker.intervalIntegrable
      (a := c - (R + D) - X k) (b := c + (R + D) - X k)).comp_sub_right (X k)
    convert h using 1 <;> ring
  have hsumInt : IntervalIntegrable
      (fun x ↦ ∑ k : Fin n, heightDropKernel eta (x - X k)) volume
        (c - (R + D)) (c + (R + D)) := by
    have hb := IntervalIntegrable.sum Finset.univ (fun k _ ↦ htermInt k)
    apply hb.congr_ae
    filter_upwards with x
    show (∑ k : Fin n, fun u : ℝ ↦ heightDropKernel eta (u - X k)) x =
      ∑ k : Fin n, heightDropKernel eta (x - X k)
    exact Finset.sum_apply x Finset.univ _
  have hFInt : IntervalIntegrable F volume
      (c - (R + D)) (c + (R + D)) := hsumInt.const_mul _
  have hsumLower : (localNodeCount X c R : ℝ) *
      (Real.pi * eta - 3 * eta ^ 2 / D) ≤
      ∑ k : Fin n, ∫ x in c - (R + D)..c + (R + D),
        heightDropKernel eta (x - X k) := by
    have hfiltered : ∑ _k ∈ s, (Real.pi * eta - 3 * eta ^ 2 / D) ≤
        ∑ k ∈ s, ∫ x in c - (R + D)..c + (R + D),
          heightDropKernel eta (x - X k) := by
      apply Finset.sum_le_sum
      intro k hk
      apply test_heightDropKernel_interval_mass_lower heta
      · simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and,
          abs_sub_comm] using hk
      · exact hD
    have hsubset : (∑ k ∈ s, ∫ x in c - (R + D)..c + (R + D),
        heightDropKernel eta (x - X k)) ≤
        ∑ k : Fin n, ∫ x in c - (R + D)..c + (R + D),
          heightDropKernel eta (x - X k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k _ _
      exact intervalIntegral.integral_nonneg (by linarith)
        (fun x _ ↦ heightDropKernel_nonneg heta)
    calc
      (localNodeCount X c R : ℝ) *
          (Real.pi * eta - 3 * eta ^ 2 / D) =
          ∑ _k ∈ s, (Real.pi * eta - 3 * eta ^ 2 / D) := by
        simp only [localNodeCount, s, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ s, ∫ x in c - (R + D)..c + (R + D),
          heightDropKernel eta (x - X k) := hfiltered
      _ ≤ ∑ k : Fin n, ∫ x in c - (R + D)..c + (R + D),
          heightDropKernel eta (x - X k) := hsubset
  have hsumEq : (∑ k : Fin n, ∫ x in c - (R + D)..c + (R + D),
      heightDropKernel eta (x - X k)) =
      ∫ x in c - (R + D)..c + (R + D),
        ∑ k : Fin n, heightDropKernel eta (x - X k) := by
    rw [intervalIntegral.integral_finsetSum]
    intro k _
    exact htermInt k
  have hFbound : (∫ x in c - (R + D)..c + (R + D), F x) ≤
      2 * (R + D) * (Real.pi * eta * rhoMax + E) := by
    have hpoint : ∀ x ∈ Set.Icc (c - (R + D)) (c + (R + D)),
        F x ≤ Real.pi * eta * rhoMax + E := happrox
    have hconstInt : IntervalIntegrable
        (fun _x : ℝ ↦ Real.pi * eta * rhoMax + E) volume
        (c - (R + D)) (c + (R + D)) := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by linarith) hFInt hconstInt
      (fun x hx ↦ hpoint x hx)
    rw [intervalIntegral.integral_const] at hmono
    simpa only [smul_eq_mul] using (show
      (∫ x in c - (R + D)..c + (R + D), F x) ≤
        2 * (R + D) * (Real.pi * eta * rhoMax + E) by
      convert hmono using 1 <;> ring)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [hsumEq] at hsumLower
  have hscale : (∫ x in c - (R + D)..c + (R + D),
      ∑ k : Fin n, heightDropKernel eta (x - X k)) =
      (n : ℝ) * (∫ x in c - (R + D)..c + (R + D), F x) := by
    unfold F
    rw [intervalIntegral.integral_const_mul]
    field_simp [hnR.ne']
  rw [hscale] at hsumLower
  exact hsumLower.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hFbound hnR.le)

lemma test_heightDropKernel_interval_mass_upper {eta a b y : ℝ}
    (heta : 0 < eta) (hab : a ≤ b) :
    ∫ x in a..b, heightDropKernel eta (x - y) ≤ Real.pi * eta := by
  rw [intervalIntegral.integral_comp_sub_right]
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hker := test_integrable_heightDropKernel heta
  have hmono : (∫ t in Set.Ioc (a - y) (b - y), heightDropKernel eta t) ≤
      ∫ t : ℝ, heightDropKernel eta t := by
    exact MeasureTheory.setIntegral_le_integral hker
      (Filter.Eventually.of_forall fun t ↦ heightDropKernel_nonneg heta)
  rw [test_integral_heightDropKernel heta] at hmono
  exact hmono

lemma test_localNodeCount_lower_of_heightDrop_on_interval {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {c R D eta E rhoMin Tail : ℝ}
    (hD : 0 ≤ D) (hDR : D ≤ R) (heta : 0 < eta)
    (happrox : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
      Real.pi * eta * rhoMin - E ≤
        (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k))
    (htail : ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k ↦ ¬ |c - X k| ≤ R),
          ∫ x in c - (R - D)..c + (R - D),
            heightDropKernel eta (x - X k) ≤ Tail) :
    (n : ℝ) * (2 * (R - D)) * (Real.pi * eta * rhoMin - E) - Tail ≤
      (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
  let s : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ |c - X k| ≤ R
  let t : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ ¬ |c - X k| ≤ R
  let F : ℝ → ℝ := fun x ↦
    (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k)
  have hker := test_integrable_heightDropKernel heta
  have htermInt : ∀ k : Fin n, IntervalIntegrable
      (fun x ↦ heightDropKernel eta (x - X k)) volume
        (c - (R - D)) (c + (R - D)) := by
    intro k
    have h := (hker.intervalIntegrable
      (a := c - (R - D) - X k) (b := c + (R - D) - X k)).comp_sub_right (X k)
    convert h using 1 <;> ring
  have hsumInt : IntervalIntegrable
      (fun x ↦ ∑ k : Fin n, heightDropKernel eta (x - X k)) volume
        (c - (R - D)) (c + (R - D)) := by
    have hb := IntervalIntegrable.sum Finset.univ (fun k _ ↦ htermInt k)
    apply hb.congr_ae
    filter_upwards with x
    show (∑ k : Fin n, fun u : ℝ ↦ heightDropKernel eta (u - X k)) x =
      ∑ k : Fin n, heightDropKernel eta (x - X k)
    exact Finset.sum_apply x Finset.univ _
  have hFInt : IntervalIntegrable F volume
      (c - (R - D)) (c + (R - D)) := hsumInt.const_mul _
  have hFlower : (2 * (R - D)) * (Real.pi * eta * rhoMin - E) ≤
      ∫ x in c - (R - D)..c + (R - D), F x := by
    have hconstInt : IntervalIntegrable
        (fun _x : ℝ ↦ Real.pi * eta * rhoMin - E) volume
        (c - (R - D)) (c + (R - D)) := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by linarith) hconstInt hFInt
      (fun x hx ↦ happrox x hx)
    rw [intervalIntegral.integral_const] at hmono
    simpa only [smul_eq_mul] using (show
      2 * (R - D) * (Real.pi * eta * rhoMin - E) ≤
        ∫ x in c - (R - D)..c + (R - D), F x by
      convert hmono using 1 <;> ring)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscaled : (n : ℝ) * (2 * (R - D)) *
      (Real.pi * eta * rhoMin - E) ≤
      ∑ k : Fin n, ∫ x in c - (R - D)..c + (R - D),
        heightDropKernel eta (x - X k) := by
    have hmul := mul_le_mul_of_nonneg_left hFlower hnR.le
    have hsumEq : (∑ k : Fin n, ∫ x in c - (R - D)..c + (R - D),
        heightDropKernel eta (x - X k)) =
        (n : ℝ) * (∫ x in c - (R - D)..c + (R - D), F x) := by
      rw [← intervalIntegral.integral_finsetSum (fun k _ ↦ htermInt k)]
      unfold F
      rw [intervalIntegral.integral_const_mul]
      field_simp [hnR.ne']
    rw [hsumEq]
    simpa only [mul_assoc] using hmul
  have hunion : s ∪ t = Finset.univ := by
    ext k
    simp only [s, t, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    tauto
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro k hks hkt
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hks
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hkt
    exact hkt hks
  have hsplit : (∑ k : Fin n, ∫ x in c - (R - D)..c + (R - D),
      heightDropKernel eta (x - X k)) =
      (∑ k ∈ s, ∫ x in c - (R - D)..c + (R - D),
        heightDropKernel eta (x - X k)) +
      (∑ k ∈ t, ∫ x in c - (R - D)..c + (R - D),
        heightDropKernel eta (x - X k)) := by
    rw [← Finset.sum_union hdisj, hunion]
  rw [hsplit] at hscaled
  have hins : (∑ k ∈ s, ∫ x in c - (R - D)..c + (R - D),
      heightDropKernel eta (x - X k)) ≤
      (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
    calc
      (∑ k ∈ s, ∫ x in c - (R - D)..c + (R - D),
          heightDropKernel eta (x - X k)) ≤
          ∑ _k ∈ s, Real.pi * eta := by
        apply Finset.sum_le_sum
        intro k hk
        exact test_heightDropKernel_interval_mass_upper heta (by linarith)
      _ = (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
        simp only [localNodeCount, s, Finset.sum_const, nsmul_eq_mul]
  have htail' : (∑ k ∈ t, ∫ x in c - (R - D)..c + (R - D),
      heightDropKernel eta (x - X k)) ≤ Tail := by
    simpa only [t] using htail
  linarith

lemma test_sum_union_le_add { α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hdisj : Disjoint s (t \ s) := Finset.disjoint_sdiff
  have heq : s ∪ (t \ s) = s ∪ t := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [← heq, Finset.sum_union hdisj]
  have hsub : (∑ x ∈ t \ s, f x) ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun x _ _ ↦ hf x)
  exact add_le_add le_rfl hsub

lemma test_sum_biUnion_le_sum_sum {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (test_sum_union_le_add (t a) (s.biUnion t) f hf).trans
        (add_le_add le_rfl ih)

lemma test_exists_linear_shell {N : ℕ} {D q : ℝ}
    (hN : 0 < N) (hD : 0 < D) (hqlower : D ≤ q)
    (hqupper : q ≤ (N : ℝ) * D) :
    ∃ j < N, ((j + 1 : ℕ) : ℝ) * D ≤ q ∧
      q ≤ ((j + 2 : ℕ) : ℝ) * D := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      rcases N with _ | N
      · omega
      · rcases N with _ | N
        · refine ⟨0, by omega, ?_, ?_⟩
          · norm_num at hqlower ⊢
            exact hqlower
          · norm_num at hqupper ⊢
            exact hqupper.trans (by nlinarith [hD])
        · by_cases hq : q ≤ ((N + 1 : ℕ) : ℝ) * D
          · obtain ⟨j, hjN, hjlo, hjhi⟩ :=
              ih (N + 1) (by omega) (by omega) hq
            exact ⟨j, by omega, hjlo, hjhi⟩
          · refine ⟨N, by omega, ?_, ?_⟩
            · have hq' : ((N + 1 : ℕ) : ℝ) * D < q := lt_of_not_ge hq
              exact hq'.le
            · convert hqupper using 1 <;> norm_num

lemma test_heightDropKernel_interval_mass_le_of_separated
    {eta a b y d : ℝ} (heta : 0 < eta) (hab : a ≤ b) (hd : 0 < d)
    (hsep : ∀ x ∈ Set.Icc a b, d ≤ |x - y|) :
    ∫ x in a..b, heightDropKernel eta (x - y) ≤
      (b - a) * ((3 / 2 : ℝ) * eta ^ 2 / d ^ 2) := by
  have hker := test_integrable_heightDropKernel heta
  have htrans : IntervalIntegrable (fun x ↦ heightDropKernel eta (x - y))
      volume a b := by
    have h := (hker.intervalIntegrable (a := a - y) (b := b - y)).comp_sub_right y
    convert h using 1 <;> ring
  have hconst : IntervalIntegrable
      (fun _x : ℝ ↦ (3 / 2 : ℝ) * eta ^ 2 / d ^ 2) volume a b :=
    intervalIntegrable_const
  have hpoint : ∀ x ∈ Set.Icc a b,
      heightDropKernel eta (x - y) ≤ (3 / 2 : ℝ) * eta ^ 2 / d ^ 2 := by
    intro x hx
    have hbase := heightDropKernel_le (t := x - y) heta
    have hsq : d ^ 2 ≤ (x - y) ^ 2 := by
      have h := (sq_le_sq₀ hd.le (abs_nonneg (x - y))).2 (hsep x hx)
      simpa only [sq_abs] using h
    have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
    calc
      heightDropKernel eta (x - y) ≤
          (3 / 2 : ℝ) * eta ^ 2 / ((x - y) ^ 2 + eta ^ 2) := hbase
      _ ≤ (3 / 2 : ℝ) * eta ^ 2 / d ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) hd2
          (by nlinarith [sq_nonneg eta])
  have hmono := intervalIntegral.integral_mono_on hab htrans hconst hpoint
  rw [intervalIntegral.integral_const] at hmono
  simpa only [smul_eq_mul] using hmono

lemma test_heightDropKernel_annulus_sum_le {n N : ℕ}
    (X : NodeConfiguration n) {c R S D eta B : ℝ}
    (hN : 0 < N) (hS : 0 ≤ S)
    (hD : 0 < D) (hDR : D ≤ R)
    (heta : 0 < eta) (hcover : S + D ≤ (N : ℝ) * D)
    (hshellRight : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
          X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤ B)
    (hshellLeft : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
          (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤ B) :
    ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k ↦ ¬ |c - X k| ≤ R ∧ |c - X k| ≤ S),
          ∫ x in c - (R - D)..c + (R - D),
            heightDropKernel eta (x - X k) ≤
      6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) := by
  classical
  let outside : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦
      ¬ |c - X k| ≤ R ∧ |c - X k| ≤ S
  let right : ℕ → Finset (Fin n) := fun j ↦
    (Finset.univ : Finset (Fin n)).filter fun k ↦
      ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
        X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D
  let left : ℕ → Finset (Fin n) := fun j ↦
    (Finset.univ : Finset (Fin n)).filter fun k ↦
      ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
        (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D
  let mass : Fin n → ℝ := fun k ↦
    ∫ x in c - (R - D)..c + (R - D), heightDropKernel eta (x - X k)
  have hmassNonneg : ∀ k, 0 ≤ mass k := by
    intro k
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun x _ ↦ heightDropKernel_nonneg heta)
  have houtsideSubset : outside ⊆
      (Finset.range N).biUnion right ∪ (Finset.range N).biUnion left := by
    intro k hk
    have hkpair : ¬ |c - X k| ≤ R ∧ |c - X k| ≤ S := by
      simpa only [outside, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    have hkout : ¬ |c - X k| ≤ R := hkpair.1
    have hkS : |c - X k| ≤ S := hkpair.2
    have hside : c + R < X k ∨ X k < c - R := by
      rw [not_le] at hkout
      by_cases h : 0 ≤ c - X k
      · right
        rw [abs_of_nonneg h] at hkout
        linarith
      · left
        rw [abs_of_nonpos (le_of_not_ge h)] at hkout
        linarith
    rcases hside with hright | hleft
    · let q : ℝ := X k - (c + (R - D))
      have hqD : D ≤ q := by dsimp [q]; linarith
      have hqcover : q ≤ S + D := by
        rw [abs_of_nonpos (by linarith)] at hkS
        dsimp [q]
        linarith
      obtain ⟨j, hjN, hjlo, hjhi⟩ :=
        test_exists_linear_shell hN hD hqD (hqcover.trans hcover)
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.mpr hjN, ?_⟩
      simpa only [right, Finset.mem_filter, Finset.mem_univ, true_and, q] using
        And.intro hjlo hjhi
    · let q : ℝ := (c - (R - D)) - X k
      have hqD : D ≤ q := by dsimp [q]; linarith
      have hqcover : q ≤ S + D := by
        rw [abs_of_nonneg (by linarith)] at hkS
        dsimp [q]
        linarith
      obtain ⟨j, hjN, hjlo, hjhi⟩ :=
        test_exists_linear_shell hN hD hqD (hqcover.trans hcover)
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.mpr hjN, ?_⟩
      simpa only [left, Finset.mem_filter, Finset.mem_univ, true_and, q] using
        And.intro hjlo hjhi
  have hmassRight : ∀ j < N, ∀ k ∈ right j,
      mass k ≤ 3 * (R - D) * eta ^ 2 /
        ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by
    intro j hjN k hk
    have hkpair :
        ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
          X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D := by
      simpa only [right, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    have hk' : ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) := hkpair.1
    have hdj : 0 < ((j + 1 : ℕ) : ℝ) * D := by positivity
    have hsep : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
        ((j + 1 : ℕ) : ℝ) * D ≤ |x - X k| := by
      intro x hx
      rw [abs_of_nonpos (by linarith [hx.2, hk'])]
      linarith [hx.2, hk']
    have h := test_heightDropKernel_interval_mass_le_of_separated heta
      (by linarith) hdj hsep
    dsimp only [mass]
    calc
      (∫ x in c - (R - D)..c + (R - D),
          heightDropKernel eta (x - X k)) ≤
          ((c + (R - D)) - (c - (R - D))) *
            ((3 / 2 : ℝ) * eta ^ 2 /
              ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) := h
      _ = 3 * (R - D) * eta ^ 2 /
          ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by ring
  have hmassLeft : ∀ j < N, ∀ k ∈ left j,
      mass k ≤ 3 * (R - D) * eta ^ 2 /
        ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by
    intro j hjN k hk
    have hkpair :
        ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
          (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D := by
      simpa only [left, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    have hk' : ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k := hkpair.1
    have hdj : 0 < ((j + 1 : ℕ) : ℝ) * D := by positivity
    have hsep : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
        ((j + 1 : ℕ) : ℝ) * D ≤ |x - X k| := by
      intro x hx
      rw [abs_of_nonneg (by linarith [hx.1, hk'])]
      linarith [hx.1, hk']
    have h := test_heightDropKernel_interval_mass_le_of_separated heta
      (by linarith) hdj hsep
    dsimp only [mass]
    calc
      (∫ x in c - (R - D)..c + (R - D),
          heightDropKernel eta (x - X k)) ≤
          ((c + (R - D)) - (c - (R - D))) *
            ((3 / 2 : ℝ) * eta ^ 2 /
              ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) := h
      _ = 3 * (R - D) * eta ^ 2 /
          ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by ring
  have hrightSum : ∑ k ∈ (Finset.range N).biUnion right, mass k ≤
      B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) := by
    calc
      ∑ k ∈ (Finset.range N).biUnion right, mass k ≤
          ∑ j ∈ Finset.range N, ∑ k ∈ right j, mass k :=
        test_sum_biUnion_le_sum_sum _ _ _ hmassNonneg
      _ ≤ ∑ j ∈ Finset.range N,
          B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
            (((j + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        calc
          ∑ k ∈ right j, mass k ≤
              ∑ _k ∈ right j,
                3 * (R - D) * eta ^ 2 /
                  ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by
            exact Finset.sum_le_sum (fun k hk ↦ hmassRight j hjN k hk)
          _ = ((right j).card : ℝ) *
              (3 * (R - D) * eta ^ 2 /
                ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) := by simp
          _ ≤ B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
              (((j + 1 : ℕ) : ℝ)⁻¹) := by
            have hcard := hshellRight j hjN
            have hjpos : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
            have hRD : 0 ≤ R - D := sub_nonneg.mpr hDR
            have hfactor : 0 ≤ 3 * (R - D) * eta ^ 2 := by positivity
            have hsqInv : (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
                (((j + 1 : ℕ) : ℝ)⁻¹) := by
              rw [inv_le_inv₀ (by positivity) (by positivity)]
              nlinarith [show 1 ≤ ((j + 1 : ℕ) : ℝ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)]
            have hB : 0 ≤ B := (Nat.cast_nonneg (right j).card).trans hcard
            have hmul := mul_le_mul hcard hsqInv (by positivity) hB
            calc
              ((right j).card : ℝ) *
                  (3 * (R - D) * eta ^ 2 /
                    ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) =
                  (((right j).card : ℝ) *
                    (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) *
                    (3 * (R - D) * eta ^ 2 / D ^ 2) := by
                field_simp
              _ ≤ B * (((j + 1 : ℕ) : ℝ)⁻¹) *
                    (3 * (R - D) * eta ^ 2 / D ^ 2) := by
                have hcoef : 0 ≤ 3 * (R - D) * eta ^ 2 / D ^ 2 :=
                  div_nonneg hfactor (sq_nonneg D)
                exact mul_le_mul_of_nonneg_right hmul hcoef
              _ = B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
                  (((j + 1 : ℕ) : ℝ)⁻¹) := by ring
      _ = B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) := by
        rw [harmonic, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
        rw [Finset.mul_sum]
  have hleftSum : ∑ k ∈ (Finset.range N).biUnion left, mass k ≤
      B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) := by
    -- The left shells obey the identical estimate.
    calc
      ∑ k ∈ (Finset.range N).biUnion left, mass k ≤
          ∑ j ∈ Finset.range N, ∑ k ∈ left j, mass k :=
        test_sum_biUnion_le_sum_sum _ _ _ hmassNonneg
      _ ≤ ∑ j ∈ Finset.range N,
          B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
            (((j + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        calc
          ∑ k ∈ left j, mass k ≤
              ∑ _k ∈ left j,
                3 * (R - D) * eta ^ 2 /
                  ((((j + 1 : ℕ) : ℝ) * D) ^ 2) := by
            exact Finset.sum_le_sum (fun k hk ↦ hmassLeft j hjN k hk)
          _ = ((left j).card : ℝ) *
              (3 * (R - D) * eta ^ 2 /
                ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) := by simp
          _ ≤ B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
              (((j + 1 : ℕ) : ℝ)⁻¹) := by
            have hcard := hshellLeft j hjN
            have hsqInv : (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
                (((j + 1 : ℕ) : ℝ)⁻¹) := by
              rw [inv_le_inv₀ (by positivity) (by positivity)]
              have hjone : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
                exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
              nlinarith
            have hB : 0 ≤ B := (Nat.cast_nonneg (left j).card).trans hcard
            have hmul := mul_le_mul hcard hsqInv (by positivity) hB
            calc
              ((left j).card : ℝ) *
                  (3 * (R - D) * eta ^ 2 /
                    ((((j + 1 : ℕ) : ℝ) * D) ^ 2)) =
                  (((left j).card : ℝ) *
                    (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) *
                    (3 * (R - D) * eta ^ 2 / D ^ 2) := by
                field_simp
              _ ≤ B * (((j + 1 : ℕ) : ℝ)⁻¹) *
                    (3 * (R - D) * eta ^ 2 / D ^ 2) := by
                have hcoef : 0 ≤ 3 * (R - D) * eta ^ 2 / D ^ 2 := by
                  exact div_nonneg (by positivity) (sq_nonneg D)
                exact mul_le_mul_of_nonneg_right hmul hcoef
              _ = B * (3 * (R - D) * eta ^ 2 / D ^ 2) *
                  (((j + 1 : ℕ) : ℝ)⁻¹) := by ring
      _ = B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) := by
        rw [harmonic, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
        rw [Finset.mul_sum]
  have hout : ∑ k ∈ outside, mass k ≤
      (∑ k ∈ (Finset.range N).biUnion right, mass k) +
        ∑ k ∈ (Finset.range N).biUnion left, mass k := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg houtsideSubset
      (fun k _ _ ↦ hmassNonneg k)).trans
        (test_sum_union_le_add _ _ mass hmassNonneg)
  dsimp only [outside, mass] at hout ⊢
  calc
    ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k ↦ ¬ |c - X k| ≤ R ∧ |c - X k| ≤ S),
          ∫ x in c - (R - D)..c + (R - D),
            heightDropKernel eta (x - X k) ≤
        (∑ k ∈ (Finset.range N).biUnion right, mass k) +
          ∑ k ∈ (Finset.range N).biUnion left, mass k := hout
    _ ≤ B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) +
        B * (3 * (R - D) * eta ^ 2 / D ^ 2) * (harmonic N : ℝ) :=
      add_le_add hrightSum hleftSum
    _ = 6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) := by ring

/-! The preceding measure-theoretic kernel estimates are now connected back to
the potential approximation proved in the main development. -/

lemma test_abs_heightDrop_average_sub_density_le_uniform
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B x eta gap M : ℝ} (hA : -1 ≤ A) (hB : B ≤ 1)
    (heta : 0 < eta) (hgap : 0 < gap) (hx : |x| ≤ 1)
    (hsep : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hM : 0 ≤ M) (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) :
    |(1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) -
        Real.pi * eta *
          exteriorDensity X (normalizationLevel X) A B x 0| ≤
      9 * uniformAffineError n eta gap M := by
  have hn : 0 < n := by omega
  have h₁ := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := A) (B := B) (x := x) (eta := eta) (gap := gap) (M := M)
    hA hB heta hgap hx hsep hM hnorm hLeb
  have h₂ := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := A) (B := B) (x := x) (eta := 2 * eta) (gap := gap) (M := M)
    hA hB (mul_pos (by norm_num) heta) hgap hx hsep hM hnorm hLeb
  have havg := heightDropKernel_average_approx_boundaryDensity hn X
    (normalizationLevel X) A B x eta
    (uniformAffineError n eta gap M)
    (uniformAffineError n (2 * eta) gap M) heta h₁ (by
      convert h₂ using 1 <;> norm_num)
  have htwo := uniformAffineError_two_mul_le (gap := gap) hn heta hM
  exact havg.trans (by linarith)

noncomputable def test_densityLipschitzConstant (gap M : ℝ) : ℝ :=
  (1 / Real.pi ^ 2) * (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
    weightedPotentialBound M

lemma test_densityLipschitzConstant_nonneg {gap : ℝ} (hgap : 0 ≤ gap) (M : ℝ) :
    0 ≤ test_densityLipschitzConstant gap M := by
  unfold test_densityLipschitzConstant
  have hinv : 0 ≤ gap⁻¹ := inv_nonneg.mpr hgap
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (mul_nonneg (by norm_num) (add_nonneg hinv (pow_nonneg hinv 3))))
    (weightedPotentialBound_nonneg M)

lemma test_abs_boundaryDensity_sub_le_uniform
    {n : ℕ} (hn : 0 < n) (X : NodeConfiguration n)
    {alpha A B x y gap M : ℝ}
    (hgap : 0 < gap) (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hsepx : ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hsepy : ∀ v ∉ Set.Icc A B, gap ≤ |y - v|)
    (hM : 0 ≤ M) (halpha : |alpha| ≤ M) :
    |exteriorDensity X alpha A B x 0 - exteriorDensity X alpha A B y 0| ≤
      test_densityLipschitzConstant gap M * |x - y| := by
  have hraw := abs_exteriorDensity_sub_le hn X alpha A B x y gap
    hgap hx hy hsepx hsepy
  have hmass := exteriorWeightedMass_le_weightedPotentialBound hn X alpha A B
  have hweight := weightedPotentialBound_mono_abs hM halpha
  have hfactor : 0 ≤
      (1 / Real.pi ^ 2) * (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) := by
    positivity
  calc
    |exteriorDensity X alpha A B x 0 - exteriorDensity X alpha A B y 0| ≤
        (1 / Real.pi ^ 2) * (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
          exteriorWeightedMass X alpha A B * |x - y| := hraw
    _ ≤ (1 / Real.pi ^ 2) * (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
          weightedPotentialBound alpha * |x - y| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hfactor) (abs_nonneg _)
    _ ≤ (1 / Real.pi ^ 2) * (6 * (gap⁻¹ + (gap⁻¹) ^ 3)) *
          weightedPotentialBound M * |x - y| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight hfactor) (abs_nonneg _)
    _ = test_densityLipschitzConstant gap M * |x - y| := rfl

lemma test_heightDropKernel_far_sum_le {n : ℕ}
    (X : NodeConfiguration n) {c R D S eta : ℝ}
    (hD : 0 ≤ D) (hDR : D ≤ R) (hRS : R < S) (heta : 0 < eta) :
    ∑ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k ↦ S < |c - X k|),
        ∫ x in c - (R - D)..c + (R - D), heightDropKernel eta (x - X k) ≤
      (n : ℝ) * (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2) := by
  have hd : 0 < S - (R - D) := by linarith
  calc
    ∑ k ∈ (Finset.univ : Finset (Fin n)).filter (fun k ↦ S < |c - X k|),
        ∫ x in c - (R - D)..c + (R - D), heightDropKernel eta (x - X k) ≤
        ∑ _k ∈ (Finset.univ : Finset (Fin n)).filter (fun k ↦ S < |c - X k|),
          3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkS : S < |c - X k| := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
      have hsep : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
          S - (R - D) ≤ |x - X k| := by
        intro x hx
        have htri : |c - X k| ≤ |c - x| + |x - X k| := by
          calc
            |c - X k| = |(c - x) + (x - X k)| := by ring_nf
            _ ≤ |c - x| + |x - X k| := abs_add_le _ _
        have hcx : |c - x| ≤ R - D := by
          rw [abs_le]
          constructor <;> linarith [hx.1, hx.2]
        linarith
      have hmass := test_heightDropKernel_interval_mass_le_of_separated
        heta (by linarith) hd hsep
      calc
        (∫ x in c - (R - D)..c + (R - D),
            heightDropKernel eta (x - X k)) ≤
            ((c + (R - D)) - (c - (R - D))) *
              ((3 / 2 : ℝ) * eta ^ 2 / (S - (R - D)) ^ 2) := hmass
        _ = 3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2 := by ring
    _ ≤ ∑ _k : Fin n,
          3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k _ _
      positivity
    _ = (n : ℝ) * (3 * (R - D) * eta ^ 2 /
          (S - (R - D)) ^ 2) := by simp

noncomputable def test_intervalNodeCount {n : ℕ} (X : NodeConfiguration n)
    (L U : ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun k ↦ L ≤ X k ∧ X k ≤ U).card

lemma test_intervalNodeCount_eq_localNodeCount {n : ℕ}
    (X : NodeConfiguration n) {L D : ℝ} (hD : 0 ≤ D) :
    test_intervalNodeCount X L (L + D) =
      localNodeCount X (L + D / 2) (D / 2) := by
  unfold test_intervalNodeCount localNodeCount
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [abs_le]
  constructor
  · intro hk
    constructor <;> linarith [hk.1, hk.2]
  · intro hk
    constructor <;> linarith [hk.1, hk.2]

lemma test_intervalNodeCount_le_of_heightDrop {n : ℕ} (hn : 0 < n)
    (X : NodeConfiguration n) {L D eta E rhoMax : ℝ}
    (hD : 0 < D) (heta : 0 < eta)
    (hetaD : 12 * eta ≤ Real.pi * D)
    (happrox : ∀ x ∈ Set.Icc (L - D / 2) (L + D + D / 2),
      (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) ≤
        Real.pi * eta * rhoMax + E) :
    (test_intervalNodeCount X L (L + D) : ℝ) ≤
      4 * (n : ℝ) * D * (rhoMax + E / (Real.pi * eta)) := by
  have hpiEta : 0 < Real.pi * eta := mul_pos Real.pi_pos heta
  have hsmall : 3 * eta ^ 2 / (D / 2) ≤ Real.pi * eta / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hetaD heta.le
    rw [div_le_iff₀ (half_pos hD)]
    nlinarith
  have hcore : Real.pi * eta / 2 ≤
      Real.pi * eta - 3 * eta ^ 2 / (D / 2) := by
    linarith
  have hcoreNonneg : 0 ≤ Real.pi * eta - 3 * eta ^ 2 / (D / 2) :=
    (div_nonneg hpiEta.le (by norm_num)).trans hcore
  have hcount := test_localNodeCount_le_of_heightDrop_on_interval hn X
    (c := L + D / 2) (R := D / 2) (D := D / 2)
    (eta := eta) (E := E) (rhoMax := rhoMax)
    (by positivity) (by positivity) heta hcoreNonneg (by
      intro x hx
      apply happrox x
      constructor <;> linarith [hx.1, hx.2])
  rw [← test_intervalNodeCount_eq_localNodeCount X hD.le] at hcount
  have hcountNonneg : 0 ≤ (test_intervalNodeCount X L (L + D) : ℝ) := by
    positivity
  have hmul : (test_intervalNodeCount X L (L + D) : ℝ) *
      (Real.pi * eta / 2) ≤
      (n : ℝ) * (2 * ((D / 2) + D / 2)) *
        (Real.pi * eta * rhoMax + E) :=
    (mul_le_mul_of_nonneg_left hcore hcountNonneg).trans hcount
  have hscaled := mul_le_mul_of_nonneg_right hmul (show 0 ≤ (2 : ℝ) by norm_num)
  have hproduct :
      (test_intervalNodeCount X L (L + D) : ℝ) * (Real.pi * eta) ≤
        4 * (n : ℝ) * D * (Real.pi * eta * rhoMax + E) := by
    calc
      (test_intervalNodeCount X L (L + D) : ℝ) * (Real.pi * eta) =
          ((test_intervalNodeCount X L (L + D) : ℝ) *
            (Real.pi * eta / 2)) * 2 := by ring
      _ ≤
          ((n : ℝ) * (2 * ((D / 2) + D / 2)) *
            (Real.pi * eta * rhoMax + E)) * 2 := hscaled
      _ = 4 * (n : ℝ) * D * (Real.pi * eta * rhoMax + E) := by ring
  have hdiv := (le_div_iff₀ hpiEta).2 hproduct
  calc
    (test_intervalNodeCount X L (L + D) : ℝ) ≤
        (4 * (n : ℝ) * D * (Real.pi * eta * rhoMax + E)) /
          (Real.pi * eta) := hdiv
    _ = 4 * (n : ℝ) * D * (rhoMax + E / (Real.pi * eta)) := by
      field_simp [hpiEta.ne']

lemma test_localNodeCount_lower_with_annulus_tail {n N : ℕ}
    (hn : 0 < n) (X : NodeConfiguration n)
    {c R S D eta E rhoMin B : ℝ}
    (hN : 0 < N) (hD : 0 < D) (hDR : D ≤ R) (hRS : R < S)
    (heta : 0 < eta) (hcover : S + D ≤ (N : ℝ) * D)
    (happrox : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
      Real.pi * eta * rhoMin - E ≤
        (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k))
    (hshellRight : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
          X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤ B)
    (hshellLeft : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
          (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤ B) :
    (n : ℝ) * (2 * (R - D)) * (Real.pi * eta * rhoMin - E) -
        (6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) +
          (n : ℝ) *
            (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2)) ≤
      (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
  let mass : Fin n → ℝ := fun k ↦
    ∫ x in c - (R - D)..c + (R - D), heightDropKernel eta (x - X k)
  let annulus : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦
      ¬ |c - X k| ≤ R ∧ |c - X k| ≤ S
  let far : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ S < |c - X k|
  let outside : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter fun k ↦ ¬ |c - X k| ≤ R
  have hnonneg : ∀ k, 0 ≤ mass k := by
    intro k
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun x _ ↦ heightDropKernel_nonneg heta)
  have houtside : outside = annulus ∪ far := by
    ext k
    simp only [outside, annulus, far, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    constructor
    · intro hk
      by_cases hS : |c - X k| ≤ S
      · exact Or.inl ⟨hk, hS⟩
      · exact Or.inr (lt_of_not_ge hS)
    · intro hk
      rcases hk with hk | hk
      · exact hk.1
      · exact fun hR ↦ (not_lt_of_ge (hR.trans (le_of_lt hRS))) hk
  have hannulus : ∑ k ∈ annulus, mass k ≤
      6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) := by
    simpa only [annulus, mass] using
      test_heightDropKernel_annulus_sum_le X hN
        (le_of_lt ((lt_of_lt_of_le hD hDR).trans hRS))
        hD hDR heta hcover hshellRight hshellLeft
  have hfar : ∑ k ∈ far, mass k ≤
      (n : ℝ) * (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2) := by
    simpa only [far, mass] using
      test_heightDropKernel_far_sum_le X hD.le hDR hRS heta
  have htail : ∑ k ∈ outside, mass k ≤
      6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) +
        (n : ℝ) * (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2) := by
    rw [houtside]
    exact (test_sum_union_le_add annulus far mass hnonneg).trans
      (add_le_add hannulus hfar)
  apply test_localNodeCount_lower_of_heightDrop_on_interval hn X
    (c := c) (R := R) (D := D) (eta := eta) (E := E)
    (rhoMin := rhoMin)
    (Tail := 6 * B * (R - D) * eta ^ 2 / D ^ 2 * (harmonic N : ℝ) +
      (n : ℝ) * (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2))
    hD.le hDR heta happrox
  simpa only [outside, mass] using htail

noncomputable def test_smoothedDensityError
    (n : ℕ) (eta gap M : ℝ) : ℝ :=
  9 * uniformAffineError n eta gap M

noncomputable def test_shellCardBound
    (n : ℕ) (D eta gap M : ℝ) : ℝ :=
  4 * (n : ℝ) * D *
    (localDensityUpper gap M +
      test_smoothedDensityError n eta gap M / (Real.pi * eta))

/-! A finite, completely explicit local counting law.  All analytic input is
encapsulated in the already-proved affine-potential estimate; the remaining
terms are the boundary-density variation, harmonic annulus tail, and fixed
far tail. -/
lemma test_localNodeCount_lower_uniform {n N : ℕ}
    (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B c R S D eta gap M : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hM : 0 ≤ M)
    (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ))
    (hN : 0 < N) (hD : 0 < D) (hDR : D ≤ R) (hRS : R < S)
    (heta : 0 < eta) (hetaD : 12 * eta ≤ Real.pi * D)
    (hcoverLower : S + D ≤ (N : ℝ) * D)
    (hcoverUpper : (N : ℝ) * D ≤ S + 2 * D)
    (hgap : 0 < gap)
    (hregular : ∀ x, |x - c| ≤ S + R + 3 * D →
      |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    (n : ℝ) * (2 * (R - D)) *
          (Real.pi * eta *
              (exteriorDensity X (normalizationLevel X) A B c 0 -
                test_densityLipschitzConstant gap M * (R - D)) -
            test_smoothedDensityError n eta gap M) -
        (6 * test_shellCardBound n D eta gap M * (R - D) * eta ^ 2 /
              D ^ 2 * (harmonic N : ℝ) +
          (n : ℝ) *
            (3 * (R - D) * eta ^ 2 / (S - (R - D)) ^ 2)) ≤
      (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
  have hn : 0 < n := by omega
  let E := test_smoothedDensityError n eta gap M
  let rhoMax := localDensityUpper gap M
  let Lrho := test_densityLipschitzConstant gap M
  let rhoC := exteriorDensity X (normalizationLevel X) A B c 0
  let shellB := test_shellCardBound n D eta gap M
  have hregc : |c| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |c - v| := by
    apply hregular c
    rw [sub_self, abs_zero]
    have hRpos : 0 < R := lt_of_lt_of_le hD hDR
    have hSpos : 0 < S := hRpos.trans hRS
    linarith
  have havgApprox : ∀ x, |x - c| ≤ S + R + 3 * D →
      |(1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) -
        Real.pi * eta * exteriorDensity X (normalizationLevel X) A B x 0| ≤ E := by
    intro x hx
    obtain ⟨hxunit, hxsep⟩ := hregular x hx
    simpa only [E, test_smoothedDensityError] using
      test_abs_heightDrop_average_sub_density_le_uniform hn2 X hA hB
        heta hgap hxunit hxsep hM hnorm hLeb
  have hdensityUpper : ∀ x, |x - c| ≤ S + R + 3 * D →
      exteriorDensity X (normalizationLevel X) A B x 0 ≤ rhoMax := by
    intro x hx
    obtain ⟨hxunit, hxsep⟩ := hregular x hx
    simpa only [rhoMax] using exteriorDensity_le_localDensityUpper hn X
      hgap hxunit hxsep hM hnorm
  have hdensityVar : ∀ x, |x - c| ≤ S + R + 3 * D →
      |exteriorDensity X (normalizationLevel X) A B x 0 - rhoC| ≤
        Lrho * |x - c| := by
    intro x hx
    obtain ⟨hxunit, hxsep⟩ := hregular x hx
    simpa only [rhoC, Lrho] using
      test_abs_boundaryDensity_sub_le_uniform hn X hgap hxunit hregc.1
        hxsep hregc.2 hM hnorm
  have havgUpper : ∀ x, |x - c| ≤ S + R + 3 * D →
      (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) ≤
        Real.pi * eta * rhoMax + E := by
    intro x hx
    have happ := (abs_le.mp (havgApprox x hx)).2
    have hrho := hdensityUpper x hx
    have hcoef : 0 ≤ Real.pi * eta := (mul_pos Real.pi_pos heta).le
    have := mul_le_mul_of_nonneg_left hrho hcoef
    linarith
  have hshellRight : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
          X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤
        shellB := by
    intro j hj
    let q : ℝ := c + (R - D) + ((j + 1 : ℕ) : ℝ) * D
    have hjcast : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show j + 1 ≤ N by omega)
    have hqbound : ∀ x ∈ Set.Icc (q - D / 2) (q + D + D / 2),
        |x - c| ≤ S + R + 3 * D := by
      intro x hx
      have hxlow : c ≤ x := by
        have hjone : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ j + 1 by omega)
        have hjD := mul_le_mul_of_nonneg_right hjone hD.le
        have hterm : 0 ≤ ((j + 1 : ℕ) : ℝ) * D - D / 2 := by
          linarith
        have hqc : c ≤ q - D / 2 := by
          dsimp only [q]
          rw [show c + (R - D) + ((j + 1 : ℕ) : ℝ) * D - D / 2 =
              c + ((R - D) + (((j + 1 : ℕ) : ℝ) * D - D / 2)) by ring]
          exact le_add_of_nonneg_right
            (add_nonneg (sub_nonneg.mpr hDR) hterm)
        exact hqc.trans hx.1
      rw [abs_of_nonneg (by linarith)]
      have hjmul := mul_le_mul_of_nonneg_right hjcast hD.le
      have hjbound : ((j + 1 : ℕ) : ℝ) * D ≤ S + 2 * D :=
        hjmul.trans hcoverUpper
      calc
        x - c ≤ (q + D + D / 2) - c := sub_le_sub_right hx.2 c
        _ = (R - D) + ((j + 1 : ℕ) : ℝ) * D + D + D / 2 := by
          dsimp only [q]
          ring
        _ ≤ (R - D) + (S + 2 * D) + D + D / 2 := by
          gcongr
        _ ≤ S + R + 3 * D := by linarith
    have hcard := test_intervalNodeCount_le_of_heightDrop hn X hD heta hetaD
      (L := q) (E := E) (rhoMax := rhoMax) (fun x hx ↦
        havgUpper x (hqbound x hx))
    have heq : (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ X k - (c + (R - D)) ∧
          X k - (c + (R - D)) ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) =
        (test_intervalNodeCount X q (q + D) : ℝ) := by
      congr 1
      unfold test_intervalNodeCount
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [q]
      have hjtwo : ((j + 2 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show j + 2 = (j + 1) + 1 by omega)
      rw [hjtwo]
      constructor <;> intro hk <;> constructor <;> linarith [hk.1, hk.2]
    rw [heq]
    simpa only [shellB, test_shellCardBound, rhoMax, E] using hcard
  have hshellLeft : ∀ j < N,
      (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
          (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) ≤
        shellB := by
    intro j hj
    let q : ℝ := c - (R - D) - ((j + 2 : ℕ) : ℝ) * D
    have hjcast : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show j + 1 ≤ N by omega)
    have hjtwo : ((j + 2 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show j + 2 = (j + 1) + 1 by omega)
    have hqbound : ∀ x ∈ Set.Icc (q - D / 2) (q + D + D / 2),
        |x - c| ≤ S + R + 3 * D := by
      intro x hx
      have hxhigh : x ≤ c := by
        have hjone : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ j + 1 by omega)
        have hjD := mul_le_mul_of_nonneg_right hjone hD.le
        have hterm : 0 ≤ ((j + 1 : ℕ) : ℝ) * D - D / 2 := by
          linarith
        have hqc : q + D + D / 2 ≤ c := by
          dsimp only [q]
          rw [hjtwo]
          rw [show c - (R - D) - (((j + 1 : ℕ) : ℝ) + 1) * D + D + D / 2 =
              c - ((R - D) + (((j + 1 : ℕ) : ℝ) * D - D / 2)) by ring]
          exact sub_le_self c (add_nonneg (sub_nonneg.mpr hDR) hterm)
        exact hx.2.trans hqc
      rw [abs_of_nonpos (by linarith)]
      have hjmul := mul_le_mul_of_nonneg_right hjcast hD.le
      have hjbound : ((j + 1 : ℕ) : ℝ) * D ≤ S + 2 * D :=
        hjmul.trans hcoverUpper
      calc
        -(x - c) = c - x := by ring
        _ ≤ c - (q - D / 2) := sub_le_sub_left hx.1 c
        _ = (R - D) + ((j + 1 : ℕ) : ℝ) * D + D + D / 2 := by
          dsimp only [q]
          rw [hjtwo]
          ring
        _ ≤ (R - D) + (S + 2 * D) + D + D / 2 := by
          gcongr
        _ ≤ S + R + 3 * D := by linarith
    have hcard := test_intervalNodeCount_le_of_heightDrop hn X hD heta hetaD
      (L := q) (E := E) (rhoMax := rhoMax) (fun x hx ↦
        havgUpper x (hqbound x hx))
    have heq : (((Finset.univ : Finset (Fin n)).filter fun k ↦
        ((j + 1 : ℕ) : ℝ) * D ≤ (c - (R - D)) - X k ∧
          (c - (R - D)) - X k ≤ ((j + 2 : ℕ) : ℝ) * D).card : ℝ) =
        (test_intervalNodeCount X q (q + D) : ℝ) := by
      congr 1
      unfold test_intervalNodeCount
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [q]
      rw [hjtwo]
      constructor <;> intro hk <;> constructor <;> linarith [hk.1, hk.2]
    rw [heq]
    simpa only [shellB, test_shellCardBound, rhoMax, E] using hcard
  have havgLower : ∀ x ∈ Set.Icc (c - (R - D)) (c + (R - D)),
      Real.pi * eta * (rhoC - Lrho * (R - D)) - E ≤
        (1 / (n : ℝ)) * ∑ k : Fin n, heightDropKernel eta (x - X k) := by
    intro x hx
    have hxR : |x - c| ≤ R - D := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hxreg : |x - c| ≤ S + R + 3 * D := by
      have hRnonneg : 0 ≤ R - D := sub_nonneg.mpr hDR
      have hSpos : 0 < S := (lt_of_lt_of_le hD hDR).trans hRS
      exact hxR.trans (by linarith)
    have happ := (abs_le.mp (havgApprox x hxreg)).1
    have hvar := hdensityVar x hxreg
    have hrho : rhoC - Lrho * (R - D) ≤
        exteriorDensity X (normalizationLevel X) A B x 0 := by
      have hL : 0 ≤ Lrho := by
        dsimp only [Lrho]
        exact test_densityLipschitzConstant_nonneg hgap.le M
      have hmul := mul_le_mul_of_nonneg_left hxR hL
      have hlower := (abs_le.mp hvar).1
      linarith
    have hcoef : 0 ≤ Real.pi * eta := (mul_pos Real.pi_pos heta).le
    have := mul_le_mul_of_nonneg_left hrho hcoef
    linarith
  simpa only [rhoC, Lrho, E, shellB] using
    test_localNodeCount_lower_with_annulus_tail hn X hN hD hDR hRS heta
      hcoverLower havgLower hshellRight hshellLeft

/-! ## Geometry of the finite Joukowski ellipse -/

lemma test_abs_joukowskiMap_re_sub_le {center radius r : ℝ} {w : ℂ}
    (hradius : 0 ≤ radius) (hr : 0 < r) (hw : ‖w‖ = r) :
    |(joukowskiMap center radius w).re - center| ≤
      radius * (r + r⁻¹) / 2 := by
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz, norm_zero] at hw
    linarith
  have hnormInv : ‖w⁻¹‖ = r⁻¹ := by rw [norm_inv, hw]
  have hre : |(w + w⁻¹).re| ≤ r + r⁻¹ := by
    calc
      |(w + w⁻¹).re| ≤ ‖w + w⁻¹‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ + ‖w⁻¹‖ := norm_add_le _ _
      _ = r + r⁻¹ := by rw [hw, hnormInv]
  have hhalf : 0 ≤ radius / 2 := by positivity
  have hcoefRe : ((radius : ℂ) / 2).re = radius / 2 := by norm_num
  have hcoefIm : ((radius : ℂ) / 2).im = 0 := by norm_num
  rw [joukowskiMap, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    hcoefRe, hcoefIm, zero_mul, sub_zero]
  rw [show center + radius / 2 * (w + w⁻¹).re - center =
      radius / 2 * (w + w⁻¹).re by ring]
  rw [abs_mul, abs_of_nonneg hhalf]
  calc
    radius / 2 * |(w + w⁻¹).re| ≤
        radius / 2 * (r + r⁻¹) := mul_le_mul_of_nonneg_left hre hhalf
    _ = radius * (r + r⁻¹) / 2 := by ring

lemma test_abs_joukowskiMap_im_le {center radius r : ℝ} {w : ℂ}
    (hradius : 0 ≤ radius) (hr : 1 < r) (hw : ‖w‖ = r) :
    |(joukowskiMap center radius w).im| ≤
      radius * (r - r⁻¹) / 2 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz, norm_zero] at hw
    linarith
  have hnormSq : Complex.normSq w = r ^ 2 := by
    rw [← Complex.sq_norm, hw]
  have him : |w.im| ≤ r := by simpa only [hw] using Complex.abs_im_le_norm w
  have hfactor : 0 ≤ 1 - (r ^ 2)⁻¹ := by
    rw [sub_nonneg, inv_le_one₀]
    · nlinarith
    · positivity
  have himEq : (joukowskiMap center radius w).im =
      radius / 2 * (w.im * (1 - (r ^ 2)⁻¹)) := by
    have hcoefRe : ((radius : ℂ) / 2).re = radius / 2 := by norm_num
    have hcoefIm : ((radius : ℂ) / 2).im = 0 := by norm_num
    rw [joukowskiMap, Complex.add_im, Complex.ofReal_im, zero_add,
      Complex.mul_im, hcoefRe, hcoefIm, zero_mul, add_zero, Complex.add_im,
      Complex.inv_im, hnormSq]
    field_simp [hr0.ne']
    ring
  rw [himEq, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ radius / 2),
    abs_of_nonneg hfactor]
  calc
    radius / 2 * (|w.im| * (1 - (r ^ 2)⁻¹)) ≤
        radius / 2 * (r * (1 - (r ^ 2)⁻¹)) := by
      gcongr
    _ = radius * (r - r⁻¹) / 2 := by
      field_simp [hr0.ne']

lemma test_norm_complexNodalValue_height_mono {n : ℕ}
    (X : NodeConfiguration n) (x eta₁ eta₂ : ℝ)
    (heta : eta₁ ^ 2 ≤ eta₂ ^ 2) :
    ‖complexNodalValue X ((x : ℂ) + eta₁ * Complex.I)‖ ≤
      ‖complexNodalValue X ((x : ℂ) + eta₂ * Complex.I)‖ := by
  unfold complexNodalValue
  rw [norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro k hk
    exact norm_nonneg _
  · intro k hk
    have hsquare₁ :
        ‖((x : ℂ) + eta₁ * Complex.I) - (X k : ℂ)‖ ^ 2 =
          (x - X k) ^ 2 + eta₁ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring
    have hsquare₂ :
        ‖((x : ℂ) + eta₂ * Complex.I) - (X k : ℂ)‖ ^ 2 =
          (x - X k) ^ 2 + eta₂ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (((x : ℂ) + eta₁ * Complex.I) - (X k : ℂ)),
      norm_nonneg (((x : ℂ) + eta₂ * Complex.I) - (X k : ℂ))]

lemma test_norm_nodal_on_joukowski_ellipse_le
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B center radius r gap M : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hM : 0 ≤ M)
    (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ))
    (hradius : 0 < radius) (hr : 1 < r) (hgap : 0 < gap)
    (hregular : ∀ x,
      |x - center| ≤ radius * (r + r⁻¹) / 2 →
        |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    ∀ w : ℂ, ‖w‖ = r →
      ‖((nodalPolynomial X).map Complex.ofRealHom).eval
          ((center : ℂ) + (radius : ℂ) * ((w ^ 2 + 1) / (2 * w)))‖ ≤
        nodalScale X * Real.exp ((n : ℝ) *
          (Real.pi * (radius * (r - r⁻¹) / 2) *
              (exteriorDensity X (normalizationLevel X) A B center 0 +
                test_densityLipschitzConstant gap M *
                  (radius * (r + r⁻¹) / 2)) +
            uniformAffineError n (radius * (r - r⁻¹) / 2) gap M)) := by
  intro w hw
  have hn : 0 < n := by omega
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hw0 : w ≠ 0 := by
    intro hwz
    rw [hwz, norm_zero] at hw
    linarith
  let z := joukowskiMap center radius w
  let etaMax : ℝ := radius * (r - r⁻¹) / 2
  let horiz : ℝ := radius * (r + r⁻¹) / 2
  have hetaMax : 0 < etaMax := by
    dsimp only [etaMax]
    have : 0 < r - r⁻¹ := by
      rw [sub_pos]
      exact (inv_lt_iff_one_lt_mul₀ hr0).2 (by nlinarith)
    positivity
  have hzre : |z.re - center| ≤ horiz := by
    simpa only [z, horiz] using
      test_abs_joukowskiMap_re_sub_le hradius.le hr0 hw
  have hzim : |z.im| ≤ etaMax := by
    simpa only [z, etaMax] using test_abs_joukowskiMap_im_le hradius.le hr hw
  obtain ⟨hzunit, hzsep⟩ := hregular z.re hzre
  have hcenterReg := hregular center (by
    rw [sub_self, abs_zero]
    positivity)
  have hvar := test_abs_boundaryDensity_sub_le_uniform hn X hgap
    hzunit hcenterReg.1 hzsep hcenterReg.2 hM hnorm
  have hrho : exteriorDensity X (normalizationLevel X) A B z.re 0 ≤
      exteriorDensity X (normalizationLevel X) A B center 0 +
        test_densityLipschitzConstant gap M * horiz := by
    have hright := (abs_le.mp hvar).2
    have hmul := mul_le_mul_of_nonneg_left hzre
      (test_densityLipschitzConstant_nonneg hgap.le M)
    linarith
  have hzroot : ∀ k, ((z.re : ℂ) + etaMax * Complex.I) ≠ (X k : ℂ) := by
    intro k hk
    have him := congrArg Complex.im hk
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one] at him
    norm_num at him
    exact hetaMax.ne' him
  have happ := abs_logPotential_sub_boundaryDensity_affine_le_uniform hn2 X
    (A := A) (B := B) (x := z.re) (eta := etaMax) (gap := gap) (M := M)
    hA hB hetaMax hgap hzunit hzsep hM hnorm hLeb
  have hpot := norm_complexNodalValue_le_of_affine_potential hn X hzroot happ
  have hmonoExp :
      nodalScale X * Real.exp ((n : ℝ) *
          (Real.pi * etaMax *
              exteriorDensity X (normalizationLevel X) A B z.re 0 +
            uniformAffineError n etaMax gap M)) ≤
        nodalScale X * Real.exp ((n : ℝ) *
          (Real.pi * etaMax *
              (exteriorDensity X (normalizationLevel X) A B center 0 +
                test_densityLipschitzConstant gap M * horiz) +
            uniformAffineError n etaMax gap M)) := by
    apply mul_le_mul_of_nonneg_left _ (nodalScale_pos hn X).le
    apply Real.exp_le_exp.mpr
    have hcoef : 0 ≤ (n : ℝ) * (Real.pi * etaMax) := by positivity
    nlinarith
  have hheight :
      ‖complexNodalValue X ((z.re : ℂ) + z.im * Complex.I)‖ ≤
        ‖complexNodalValue X ((z.re : ℂ) + etaMax * Complex.I)‖ := by
    apply test_norm_complexNodalValue_height_mono
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg z.im) hetaMax.le).2 hzim
  have hzcoord : (z.re : ℂ) + z.im * Complex.I = z := by
    apply Complex.ext <;> simp
  rw [hzcoord] at hheight
  rw [← complexNodalPolynomial_eval, complexNodalPolynomial] at hheight
  have hJ : (center : ℂ) + (radius : ℂ) * ((w ^ 2 + 1) / (2 * w)) = z := by
    dsimp only [z]
    rw [joukowskiMap_eq_ellipseQuotient center radius hw0]
    field_simp [hw0]
    push_cast
    ring
  rw [hJ]
  simpa only [etaMax, horiz] using hheight.trans (hpot.trans hmonoExp)

lemma test_abs_nodal_on_local_interval_le_amplitude
    {n : ℕ} (X : NodeConfiguration n)
    {A B rate center radius : ℝ} (hAB : A ≤ B) (hrate : 0 ≤ rate)
    (hradius : 0 ≤ radius) (hleft : A ≤ center - radius)
    (hright : center + radius ≤ B) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |(nodalPolynomial X).eval (center + radius * x)| ≤
        Real.exp (rate * radius) * amplitude X A B rate center hAB := by
  intro x hx
  let y := center + radius * x
  have hxr : |radius * x| ≤ radius := by
    rw [abs_mul, abs_of_nonneg hradius]
    have hxabs : |x| ≤ 1 := abs_le.mpr hx
    nlinarith [mul_le_mul_of_nonneg_left hxabs hradius]
  have hycenter : |y - center| ≤ radius := by
    dsimp only [y]
    convert hxr using 1 <;> ring_nf
  have hy : y ∈ Set.Icc A B := by
    rw [abs_le] at hycenter
    constructor <;> linarith [hycenter.1, hycenter.2]
  have hpoly := abs_nodal_le_amplitude X (rate := rate) hAB hy
  have hamp := amplitude_le_exp_mul_amplitude X hAB hrate
    (x := y) (y := center)
  have hexp : Real.exp (rate * |y - center|) ≤ Real.exp (rate * radius) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hycenter hrate)
  calc
    |(nodalPolynomial X).eval (center + radius * x)| =
        |(nodalPolynomial X).eval y| := rfl
    _ ≤ amplitude X A B rate y hAB := hpoly
    _ ≤ Real.exp (rate * |y - center|) *
        amplitude X A B rate center hAB := hamp
    _ ≤ Real.exp (rate * radius) * amplitude X A B rate center hAB :=
      mul_le_mul_of_nonneg_right hexp (amplitude_nonneg X hAB)

noncomputable def test_localEllipseBound {n : ℕ} (X : NodeConfiguration n)
    (A B center radius r gap M : ℝ) : ℝ :=
  nodalScale X * Real.exp ((n : ℝ) *
    (Real.pi * (radius * (r - r⁻¹) / 2) *
        (exteriorDensity X (normalizationLevel X) A B center 0 +
          test_densityLipschitzConstant gap M *
            (radius * (r + r⁻¹) / 2)) +
      uniformAffineError n (radius * (r - r⁻¹) / 2) gap M))

lemma test_abs_nodal_derivative_le_of_local_potential
    {n m : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B rate center radius r gap M : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hAB : A ≤ B)
    (hM : 0 ≤ M) (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ))
    (hrate : 0 ≤ rate) (hradius : 0 < radius)
    (hleft : A ≤ center - radius) (hright : center + radius ≤ B)
    (hr : 1 < r) (hgap : 0 < gap)
    (hregular : ∀ x,
      |x - center| ≤ radius * (r + r⁻¹) / 2 →
        |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) :
    |(nodalPolynomial X).derivative.eval center| ≤
      (((m + 1 : ℕ) : ℝ) *
          (Real.exp (rate * radius) * amplitude X A B rate center hAB +
            (n : ℝ) * (2 *
              (test_localEllipseBound X A B center radius r gap M /
                r ^ (m + 1)))) +
        (n : ℝ) * (2 *
          (test_localEllipseBound X A B center radius r gap M /
            r ^ (m + 1))) * ((n + 1 : ℕ) : ℝ)) /
        radius := by
  have hn : 0 < n := by omega
  have hdeg : (nodalPolynomial X).natDegree ≤ n := by
    simpa [nodalPolynomial] using
      (Lagrange.natDegree_nodal (s := (Finset.univ : Finset (Fin n)))
        (v := X.nodes)).le
  let Aedge := Real.exp (rate * radius) * amplitude X A B rate center hAB
  let Mellipse := test_localEllipseBound X A B center radius r gap M
  have hAedge : 0 ≤ Aedge := by
    dsimp only [Aedge]
    exact mul_nonneg (Real.exp_pos _).le
      (amplitude_nonneg X (rate := rate) (x := center) hAB)
  have hMellipse : 0 ≤ Mellipse := by
    dsimp only [Mellipse, test_localEllipseBound]
    exact mul_nonneg (nodalScale_pos hn X).le (Real.exp_pos _).le
  have hreal := test_abs_nodal_on_local_interval_le_amplitude X hAB hrate
    hradius.le hleft hright
  have hellipse := test_norm_nodal_on_joukowski_ellipse_le hn2 X hA hB hM
    hnorm hLeb hradius hr hgap hregular
  simpa only [Aedge, Mellipse] using
    abs_derivative_eval_center_le_of_joukowski_bound
      (p := nodalPolynomial X) (N := n) (m := m) hdeg hradius hAedge hr
        hMellipse hreal hellipse

/-! ### A finite Abel lemma for reciprocal distances

The geometric-shell argument used at the end of the proof is most cleanly
separated from the interpolation data.  `test_cutoff` is the distribution
function of one positive distance.  The following two lemmas are a finite
summation-by-parts statement, so no measurability of the node-counting step
function is needed. -/

noncomputable def test_cutoff (d R : ℝ) : ℝ :=
  if d ≤ R then 1 else 0

lemma test_cutoff_abel_le {R : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hRpos : ∀ j, 0 < R j) (hRmono : Monotone R) (J : ℕ) :
    test_cutoff d (R J) / R J +
        ∑ j ∈ Finset.range J,
          test_cutoff d (R j) * (1 / R j - 1 / R (j + 1)) ≤
      1 / d := by
  by_cases hlast : d ≤ R J
  · let s : ℕ := Nat.find (show ∃ j, d ≤ R j from ⟨J, hlast⟩)
    have hs : d ≤ R s := Nat.find_spec (show ∃ j, d ≤ R j from ⟨J, hlast⟩)
    have hsJ : s ≤ J := Nat.find_min' (show ∃ j, d ≤ R j from ⟨J, hlast⟩) hlast
    have hbefore : ∀ j, j < s → ¬ d ≤ R j := by
      intro j hj h
      exact (not_lt_of_ge
        (Nat.find_min' (show ∃ j, d ≤ R j from ⟨J, hlast⟩) h)) hj
    have hafter : ∀ j, s ≤ j → d ≤ R j := by
      intro j hj
      exact hs.trans (hRmono hj)
    have hsum :
        ∑ j ∈ Finset.range J,
            test_cutoff d (R j) * (1 / R j - 1 / R (j + 1)) =
          1 / R s - 1 / R J := by
      rw [← Finset.sum_range_add_sum_Ico
        (fun j ↦ test_cutoff d (R j) *
          (1 / R j - 1 / R (j + 1))) hsJ]
      have hzero : ∑ j ∈ Finset.range s,
          test_cutoff d (R j) * (1 / R j - 1 / R (j + 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [test_cutoff, if_neg (hbefore j (Finset.mem_range.mp hj))]
        ring
      rw [hzero, zero_add]
      calc
        ∑ j ∈ Finset.Ico s J,
            test_cutoff d (R j) * (1 / R j - 1 / R (j + 1)) =
            ∑ j ∈ Finset.Ico s J, (1 / R j - 1 / R (j + 1)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [test_cutoff, if_pos (hafter j (Finset.mem_Ico.mp hj).1)]
              ring
        _ = 1 / R s - 1 / R J := by
          rw [Finset.sum_Ico_eq_sub _ hsJ,
            Finset.sum_range_sub', Finset.sum_range_sub']
          ring
    rw [test_cutoff, if_pos hlast, hsum]
    have hRs : 0 < R s := hRpos s
    have hdiv : 1 / R s ≤ 1 / d := one_div_le_one_div_of_le hd hs
    linarith
  · have hall : ∀ j < J, ¬ d ≤ R j := by
      intro j hj h
      exact hlast (h.trans (hRmono hj.le))
    rw [test_cutoff, if_neg hlast]
    have hzero : ∑ j ∈ Finset.range J,
        test_cutoff d (R j) * (1 / R j - 1 / R (j + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [test_cutoff, if_neg (hall j (Finset.mem_range.mp hj))]
      ring
    rw [hzero]
    norm_num
    exact hd.le

lemma test_localNodeCount_eq_sum_cutoff {n : ℕ} (X : NodeConfiguration n)
    (c R : ℝ) :
    (localNodeCount X c R : ℝ) =
      ∑ k : Fin n, test_cutoff |c - X k| R := by
  classical
  unfold localNodeCount test_cutoff
  exact (Finset.sum_boole (fun k : Fin n ↦ |c - X k| ≤ R) Finset.univ).symm

lemma test_geometric_count_reciprocal_le {n J : ℕ}
    (X : NodeConfiguration n) {c R₀ ratio kappa : ℝ}
    (hc : ∀ k, c ≠ X k) (hR₀ : 0 < R₀) (hratio : 1 < ratio)
    (hcount : ∀ j ≤ J,
      kappa * (R₀ * ratio ^ j) ≤
        (localNodeCount X c (R₀ * ratio ^ j) : ℝ)) :
    kappa * (1 + (J : ℝ) * (1 - 1 / ratio)) ≤
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k ↦ |c - X k| ≤ R₀ * ratio ^ J), 1 / |c - X k| := by
  classical
  let R : ℕ → ℝ := fun j ↦ R₀ * ratio ^ j
  have hratio0 : 0 < ratio := lt_trans (by norm_num) hratio
  have hRpos : ∀ j, 0 < R j := by
    intro j
    exact mul_pos hR₀ (pow_pos hratio0 _)
  have hRmono : Monotone R := by
    intro i j hij
    dsimp only [R]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hratio.le hij) hR₀.le
  let W : Fin n → ℝ := fun k ↦
    test_cutoff |c - X k| (R J) / R J +
      ∑ j ∈ Finset.range J,
        test_cutoff |c - X k| (R j) * (1 / R j - 1 / R (j + 1))
  have hW : ∀ k, W k ≤ 1 / |c - X k| := by
    intro k
    apply test_cutoff_abel_le (abs_pos.mpr (sub_ne_zero.mpr (hc k))) hRpos hRmono
  have hupper : ∑ k : Fin n, W k ≤
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
        (fun k ↦ |c - X k| ≤ R₀ * ratio ^ J), 1 / |c - X k| := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k hk
    by_cases hterminal : |c - X k| ≤ R₀ * ratio ^ J
    · rw [if_pos hterminal]
      exact hW k
    · rw [if_neg hterminal]
      have hall : ∀ j < J, ¬ |c - X k| ≤ R j := by
        intro j hj h
        apply hterminal
        exact h.trans (hRmono hj.le)
      dsimp only [W]
      have hlast : ¬ |c - X k| ≤ R J := by
        simpa only [R] using hterminal
      rw [test_cutoff, if_neg hlast]
      have hzero : ∑ j ∈ Finset.range J,
          test_cutoff |c - X k| (R j) *
            (1 / R j - 1 / R (j + 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [test_cutoff, if_neg (hall j (Finset.mem_range.mp hj))]
        ring
      rw [hzero]
      norm_num
  have hrewrite :
      ∑ k : Fin n, W k =
        (localNodeCount X c (R J) : ℝ) / R J +
          ∑ j ∈ Finset.range J,
            (localNodeCount X c (R j) : ℝ) *
              (1 / R j - 1 / R (j + 1)) := by
    dsimp only [W]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    rw [← Finset.sum_div]
    rw [← test_localNodeCount_eq_sum_cutoff]
    apply congrArg₂ (.+.) rfl
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_mul]
    rw [← test_localNodeCount_eq_sum_cutoff]
  have hcoeff : ∀ j, 0 ≤ 1 / R j - 1 / R (j + 1) := by
    intro j
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (hRpos j)
    exact hRmono (Nat.le_succ j)
  have hlower :
      kappa * R J / R J +
          ∑ j ∈ Finset.range J,
            (kappa * R j) * (1 / R j - 1 / R (j + 1)) ≤
        ∑ k : Fin n, W k := by
    rw [hrewrite]
    exact add_le_add
      (div_le_div_of_nonneg_right (hcount J le_rfl) (hRpos J).le)
      (Finset.sum_le_sum fun j hj ↦
        mul_le_mul_of_nonneg_right
          (hcount j (Finset.mem_range.mp hj).le) (hcoeff j))
  have hgeom :
      kappa * R J / R J +
          ∑ j ∈ Finset.range J,
            (kappa * R j) * (1 / R j - 1 / R (j + 1)) =
        kappa * (1 + (J : ℝ) * (1 - 1 / ratio)) := by
    have hratioNe : ratio ≠ 0 := hratio0.ne'
    have hRne : ∀ j, R j ≠ 0 := fun j ↦ (hRpos j).ne'
    have hterm : ∀ j,
        (kappa * R j) * (1 / R j - 1 / R (j + 1)) =
          kappa * (1 - 1 / ratio) := by
      intro j
      dsimp only [R]
      field_simp [hR₀.ne', hratioNe]
      ring
    rw [mul_div_cancel_right₀ kappa (hRne J)]
    simp_rw [hterm]
    simp
    ring
  rw [← hgeom]
  exact hlower.trans hupper

lemma test_lebesgue_lower_of_geometric_count {n J : ℕ}
    (X : NodeConfiguration n) {z R₀ ratio kappa rate derivC : ℝ}
    (hz : ∀ k, z ≠ X k) (hR₀ : 0 < R₀) (hratio : 1 < ratio)
    (hrate : 0 ≤ rate) (hderivC : 0 < derivC)
    (hcount : ∀ j ≤ J,
      kappa * (R₀ * ratio ^ j) ≤
        (localNodeCount X z (R₀ * ratio ^ j) : ℝ))
    (hderiv : ∀ k, |z - X k| ≤ R₀ * ratio ^ J →
      |(nodalPolynomial X).derivative.eval (X k)| ≤
        derivC * |(nodalPolynomial X).eval z| *
          Real.exp (rate * |z - X k|)) :
    (Real.exp (-rate * (R₀ * ratio ^ J)) / derivC) *
        (kappa * (1 + (J : ℝ) * (1 - 1 / ratio))) ≤
      lebesgueFunction X z := by
  classical
  let Rterm : ℝ := R₀ * ratio ^ J
  have hratio0 : 0 < ratio := lt_trans (by norm_num) hratio
  have hRterm : 0 < Rterm := mul_pos hR₀ (pow_pos hratio0 _)
  have hrecip := test_geometric_count_reciprocal_le X hz hR₀ hratio hcount
  have hscale : 0 ≤ Real.exp (-rate * Rterm) / derivC := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hrecip hscale
  have hpoint : ∀ k, |z - X k| ≤ Rterm →
      (Real.exp (-rate * Rterm) / derivC) * (1 / |z - X k|) ≤
        |(nodalPolynomial X).eval z| /
          (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := by
    intro k hk
    have hdist : 0 < |z - X k| := abs_pos.mpr (sub_ne_zero.mpr (hz k))
    have hderpos : 0 < |(nodalPolynomial X).derivative.eval (X k)| :=
      abs_pos.mpr (nodalPolynomial_derivative_at_node_ne_zero X k)
    have hexp : Real.exp (rate * |z - X k|) ≤ Real.exp (rate * Rterm) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hrate)
    have hderR : |(nodalPolynomial X).derivative.eval (X k)| ≤
        derivC * |(nodalPolynomial X).eval z| * Real.exp (rate * Rterm) :=
      (hderiv k (by simpa only [Rterm] using hk)).trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hderivC.le (abs_nonneg _)))
    have hbase : Real.exp (-rate * Rterm) / derivC ≤
        |(nodalPolynomial X).eval z| /
          |(nodalPolynomial X).derivative.eval (X k)| := by
      rw [show -rate * Rterm = -(rate * Rterm) by ring, Real.exp_neg]
      apply (div_le_div_iff₀ hderivC hderpos).2
      have hmul := mul_le_mul_of_nonneg_left hderR
        (show 0 ≤ (Real.exp (rate * Rterm))⁻¹ by positivity)
      calc
        (Real.exp (rate * Rterm))⁻¹ *
            |(nodalPolynomial X).derivative.eval (X k)| ≤
            (Real.exp (rate * Rterm))⁻¹ *
              (derivC * |(nodalPolynomial X).eval z| *
                Real.exp (rate * Rterm)) := hmul
        _ = |(nodalPolynomial X).eval z| * derivC := by
          field_simp
    calc
      (Real.exp (-rate * Rterm) / derivC) * (1 / |z - X k|) =
          (Real.exp (-rate * Rterm) / derivC) / |z - X k| := by ring
      _ ≤ (|(nodalPolynomial X).eval z| /
          |(nodalPolynomial X).derivative.eval (X k)|) / |z - X k| :=
        div_le_div_of_nonneg_right hbase hdist.le
      _ = |(nodalPolynomial X).eval z| /
          (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := by
        ring
  have hsum :
      (Real.exp (-rate * Rterm) / derivC) *
          (∑ k ∈ (Finset.univ : Finset (Fin n)).filter
            (fun k ↦ |z - X k| ≤ Rterm), 1 / |z - X k|) ≤
        ∑ k : Fin n,
          |(nodalPolynomial X).eval z| /
            (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := by
    rw [Finset.mul_sum]
    calc
      ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
            (fun k ↦ |z - X k| ≤ Rterm),
          (Real.exp (-rate * Rterm) / derivC) * (1 / |z - X k|) ≤
          ∑ k ∈ (Finset.univ : Finset (Fin n)).filter
            (fun k ↦ |z - X k| ≤ Rterm),
            |(nodalPolynomial X).eval z| /
              (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpoint k (by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk)
      _ ≤ ∑ k : Fin n,
            |(nodalPolynomial X).eval z| /
              (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k hk hnot
        positivity
  have hformula := lebesgueFunction_eq_nodal_sum X hz
  calc
    (Real.exp (-rate * (R₀ * ratio ^ J)) / derivC) *
        (kappa * (1 + (J : ℝ) * (1 - 1 / ratio))) ≤
        (Real.exp (-rate * Rterm) / derivC) *
          (∑ k ∈ (Finset.univ : Finset (Fin n)).filter
            (fun k ↦ |z - X k| ≤ Rterm), 1 / |z - X k|) := by
      simpa only [Rterm] using hscaled
    _ ≤ ∑ k : Fin n,
          |(nodalPolynomial X).eval z| /
            (|(nodalPolynomial X).derivative.eval (X k)| * |z - X k|) := hsum
    _ = lebesgueFunction X z := by
      rw [hformula]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-! ### The common logarithmic scale -/

noncomputable def test_logScale (n : ℕ) : ℝ := Real.log (n : ℝ)

noncomputable def test_minRadius (n : ℕ) : ℝ :=
  test_logScale n ^ 5 / (n : ℝ)

noncomputable def test_maxRadius (n : ℕ) : ℝ :=
  (test_logScale n ^ 3)⁻¹

noncomputable def test_logRange (n : ℕ) : ℝ :=
  test_logScale n - 8 * Real.log (test_logScale n)

noncomputable def test_shellRatio (Q : ℕ) : ℝ :=
  1 + 1 / (Q : ℝ)

noncomputable def test_shellSteps (Q n : ℕ) : ℕ :=
  ⌊(Q : ℝ) * test_logRange n⌋₊

lemma test_tendsto_logScale : Tendsto test_logScale atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma test_tendsto_inv_logScale :
    Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹) atTop (𝓝 0) :=
  test_tendsto_logScale.inv_tendsto_atTop

lemma test_tendsto_logScale_pow_div_nat (m : ℕ) :
    Tendsto (fun n : ℕ ↦ test_logScale n ^ m / (n : ℝ))
      atTop (𝓝 0) := by
  have h := Real.isLittleO_pow_log_id_atTop (n := m)
  have ht := h.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ m / (n : ℝ))
    atTop (𝓝 0) at ht
  exact ht

lemma test_tendsto_log_logScale_div_logScale :
    Tendsto (fun n : ℕ ↦
      Real.log (test_logScale n) / test_logScale n) atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    test_tendsto_logScale

lemma test_tendsto_logRange_div_logScale :
    Tendsto (fun n : ℕ ↦ test_logRange n / test_logScale n)
      atTop (𝓝 1) := by
  have h := test_tendsto_log_logScale_div_logScale.const_mul 8
  have ht : Tendsto (fun n : ℕ ↦
      (1 : ℝ) - 8 * (Real.log (test_logScale n) / test_logScale n))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h
  apply ht.congr'
  filter_upwards [test_tendsto_logScale.eventually (eventually_gt_atTop 0)] with n hn
  unfold test_logRange
  field_simp [hn.ne']

lemma test_tendsto_logScale_mul_log_shellBase :
    Tendsto (fun n : ℕ ↦ test_logScale n *
      Real.log (1 + 1 / test_logScale n)) atTop (𝓝 1) := by
  have ht := (Real.tendsto_mul_log_one_add_div_atTop 1).comp
    test_tendsto_logScale
  apply ht.congr'
  exact Eventually.of_forall (fun n ↦ by rfl)

lemma test_tendsto_logScale_mul_ellipseHeightFactor :
    Tendsto (fun n : ℕ ↦ test_logScale n *
      (((1 + 1 / test_logScale n) -
        (1 + 1 / test_logScale n)⁻¹) / 2)) atTop (𝓝 1) := by
  have hi := test_tendsto_inv_logScale
  have hfrac : Tendsto (fun n : ℕ ↦
      (2 + (test_logScale n)⁻¹) /
        (2 * (1 + (test_logScale n)⁻¹))) atTop (𝓝 1) := by
    have ht := (hi.const_add 2).div ((hi.const_add 1).const_mul 2) (by norm_num)
    norm_num at ht
    apply ht.congr'
    exact Eventually.of_forall (fun n ↦ by rfl)
  apply hfrac.congr'
  filter_upwards [test_tendsto_logScale.eventually (eventually_gt_atTop 0)] with q hq
  field_simp [hq.ne']
  ring

lemma test_tendsto_exp_inv_logScale :
    Tendsto (fun n : ℕ ↦ Real.exp ((test_logScale n)⁻¹))
      atTop (𝓝 1) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp
    test_tendsto_inv_logScale
  change Tendsto (fun n : ℕ ↦ Real.exp ((test_logScale n)⁻¹))
    atTop (𝓝 (Real.exp 0)) at ht
  simpa using ht

noncomputable def test_affineHeightConstant (gap M : ℝ) : ℝ :=
  (1 / Real.pi ^ 2) * weightedPotentialBound M *
    (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2))

lemma test_affineHeightConstant_nonneg (gap M : ℝ) :
    0 ≤ test_affineHeightConstant gap M := by
  unfold test_affineHeightConstant
  have hi : 0 ≤ (gap ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg gap)
  exact mul_nonneg
    (mul_nonneg (by positivity) (weightedPotentialBound_nonneg M))
    (mul_nonneg (by norm_num) (add_nonneg hi (sq_nonneg _)))

noncomputable def test_affineRatioMajorant
    (n Q : ℕ) (gap M : ℝ) : ℝ :=
  9 * (test_affineHeightConstant gap M / test_logScale n ^ 10 +
    12 * (Q : ℝ) / (Real.pi * test_logScale n ^ 2) +
    (Q : ℝ) ^ 2 *
      (logSquareConstant + 1 / 2 + 2 * M) /
        (Real.pi ^ 2 * test_logScale n ^ 6))

lemma test_tendsto_affineRatioMajorant (Q : ℕ) (gap M : ℝ) :
    Tendsto (fun n : ℕ ↦ test_affineRatioMajorant n Q gap M)
      atTop (𝓝 0) := by
  have hi := test_tendsto_inv_logScale
  have h10 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 10)
      atTop (𝓝 0) := by simpa using hi.pow 10
  have h2 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 2)
      atTop (𝓝 0) := by simpa using hi.pow 2
  have h6 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 6)
      atTop (𝓝 0) := by simpa using hi.pow 6
  have hfirst := h10.const_mul (test_affineHeightConstant gap M)
  have hsecond := h2.const_mul (12 * (Q : ℝ) / Real.pi)
  have hthird := h6.const_mul
    ((Q : ℝ) ^ 2 * (logSquareConstant + 1 / 2 + 2 * M) /
      Real.pi ^ 2)
  convert ((hfirst.add hsecond).add hthird).const_mul 9 using 1
  · funext n
    unfold test_affineRatioMajorant
    simp only [div_eq_mul_inv, inv_pow]
    ring
  · ring_nf

lemma test_affineRatio_le_majorant {n Q : ℕ} {eta gap M : ℝ}
    (hn2 : 2 ≤ n) (hQ : 0 < Q) (hM : 0 ≤ M) (heta : 0 < eta)
    (hetaLower : test_logScale n ^ 3 / ((Q : ℝ) * (n : ℝ)) ≤ eta)
    (hetaUpper : eta ≤ (test_logScale n ^ 5)⁻¹) :
    test_smoothedDensityError n eta gap M / (Real.pi * eta) ≤
      test_affineRatioMajorant n Q gap M := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < test_logScale n := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hpiEta : 0 < Real.pi * eta := mul_pos Real.pi_pos heta
  have hlogTwo : Real.log (2 * (n : ℝ)) ≤ 2 * test_logScale n := by
    rw [show (2 * (n : ℝ)) = (2 : ℝ) * (n : ℝ) by ring]
    rw [Real.log_mul (by norm_num) hnR.ne']
    have hlog2 : Real.log 2 ≤ test_logScale n := by
      unfold test_logScale
      exact Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show 0 < (n : ℝ) by exact_mod_cast hn) (by exact_mod_cast hn2)
    change Real.log 2 ≤ Real.log (n : ℝ) at hlog2
    change Real.log 2 + Real.log (n : ℝ) ≤
      2 * Real.log (n : ℝ)
    linarith
  have hetaInv : eta⁻¹ ≤
      (Q : ℝ) * (n : ℝ) / test_logScale n ^ 3 := by
    rw [show eta⁻¹ = 1 / eta by simp]
    apply (div_le_iff₀ heta).2
    have hK : 0 < (Q : ℝ) * (n : ℝ) / test_logScale n ^ 3 := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hetaLower hK.le
    calc
      1 = ((Q : ℝ) * (n : ℝ) / test_logScale n ^ 3) *
          (test_logScale n ^ 3 / ((Q : ℝ) * (n : ℝ))) := by
            field_simp [hQR.ne', hnR.ne', hq.ne']
      _ ≤ ((Q : ℝ) * (n : ℝ) / test_logScale n ^ 3) * eta := hmul
  have hetaInvSq : eta⁻¹ ^ 2 ≤
      ((Q : ℝ) * (n : ℝ) / test_logScale n ^ 3) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr heta.le) hetaInv 2
  have hetaSq : eta ^ 2 ≤ (test_logScale n ^ 5)⁻¹ ^ 2 :=
    pow_le_pow_left₀ heta.le hetaUpper 2
  have hnInvPowers :
      logSquareConstant / (n : ℝ) ^ 2 +
          1 / (2 * (n : ℝ) ^ 3) + 2 * M / (n : ℝ) ^ 7 ≤
        logSquareConstant + 1 / 2 + 2 * M := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hlogSq : 0 ≤ logSquareConstant := logSquareConstant_nonneg
    have h1 : logSquareConstant / (n : ℝ) ^ 2 ≤ logSquareConstant := by
      exact div_le_self hlogSq (one_le_pow₀ hn1)
    have h2 : 1 / (2 * (n : ℝ) ^ 3) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [one_le_pow₀ hn1 (n := 3)]
    have h3 : 2 * M / (n : ℝ) ^ 7 ≤ 2 * M := by
      exact div_le_self (mul_nonneg (by norm_num) hM) (one_le_pow₀ hn1)
    linarith
  unfold test_smoothedDensityError uniformAffineError uniformInteriorError
  unfold test_affineRatioMajorant
  have hheight : test_affineHeightConstant gap M * eta ^ 2 ≤
      test_affineHeightConstant gap M / test_logScale n ^ 10 := by
    calc
      test_affineHeightConstant gap M * eta ^ 2 ≤
          test_affineHeightConstant gap M *
            ((test_logScale n ^ 5)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hetaSq
          (test_affineHeightConstant_nonneg gap M)
      _ = test_affineHeightConstant gap M / test_logScale n ^ 10 := by
        field_simp [hq.ne']
  have hfirst :
      (Real.log (2 * (n : ℝ)) + 10 * test_logScale n) /
          ((n : ℝ) * (Real.pi * eta)) ≤
        12 * (Q : ℝ) / (Real.pi * test_logScale n ^ 2) := by
    have hnum : Real.log (2 * (n : ℝ)) + 10 * test_logScale n ≤
        12 * test_logScale n := by linarith
    have hnum0 : 0 ≤ Real.log (2 * (n : ℝ)) +
        10 * test_logScale n := by
      have : 0 ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ 2 * n by omega))
      positivity
    calc
      (Real.log (2 * (n : ℝ)) + 10 * test_logScale n) /
          ((n : ℝ) * (Real.pi * eta)) =
          (Real.log (2 * (n : ℝ)) + 10 * test_logScale n) * eta⁻¹ /
            ((n : ℝ) * Real.pi) := by field_simp
      _ ≤ (12 * test_logScale n) *
          ((Q : ℝ) * (n : ℝ) / test_logScale n ^ 3) /
            ((n : ℝ) * Real.pi) := by gcongr
      _ = 12 * (Q : ℝ) / (Real.pi * test_logScale n ^ 2) := by
        field_simp [hq.ne', hnR.ne', Real.pi_ne_zero]
  have hsecond :
      (logSquareConstant / (n : ℝ) ^ 4 +
          1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9) /
          ((Real.pi * eta) ^ 2) ≤
        (Q : ℝ) ^ 2 * (logSquareConstant + 1 / 2 + 2 * M) /
          (Real.pi ^ 2 * test_logScale n ^ 6) := by
    have hB0 : 0 ≤ logSquareConstant / (n : ℝ) ^ 4 +
          1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9 := by
      positivity [logSquareConstant_nonneg]
    have hC0 : 0 ≤ logSquareConstant + 1 / 2 + 2 * M := by
      positivity [logSquareConstant_nonneg]
    calc
      (logSquareConstant / (n : ℝ) ^ 4 +
          1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9) /
          ((Real.pi * eta) ^ 2) =
        (logSquareConstant / (n : ℝ) ^ 2 +
          1 / (2 * (n : ℝ) ^ 3) + 2 * M / (n : ℝ) ^ 7) *
            eta⁻¹ ^ 2 / ((n : ℝ) ^ 2 * Real.pi ^ 2) := by
              field_simp [hnR.ne', heta.ne', Real.pi_ne_zero]
      _ ≤ (logSquareConstant + 1 / 2 + 2 * M) *
          (((Q : ℝ) * (n : ℝ) / test_logScale n ^ 3) ^ 2) /
            ((n : ℝ) ^ 2 * Real.pi ^ 2) := by gcongr
      _ = (Q : ℝ) ^ 2 * (logSquareConstant + 1 / 2 + 2 * M) /
          (Real.pi ^ 2 * test_logScale n ^ 6) := by
        field_simp [hq.ne', hnR.ne', Real.pi_ne_zero]
  rw [show (1 / Real.pi ^ 2) * weightedPotentialBound M *
      (3 * ((gap ^ 2)⁻¹ + ((gap ^ 2)⁻¹) ^ 2)) =
      test_affineHeightConstant gap M by rfl]
  calc
    9 *
        (Real.pi * eta * (test_affineHeightConstant gap M * eta ^ 2) +
          ((Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) / (n : ℝ) +
            1 / (Real.pi * eta) *
              (logSquareConstant / (n : ℝ) ^ 4 +
                1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9))) /
          (Real.pi * eta) =
      9 * (test_affineHeightConstant gap M * eta ^ 2 +
        (Real.log (2 * (n : ℝ)) + 10 * Real.log (n : ℝ)) /
          ((n : ℝ) * (Real.pi * eta)) +
        (logSquareConstant / (n : ℝ) ^ 4 +
          1 / (2 * (n : ℝ) ^ 5) + 2 * M / (n : ℝ) ^ 9) /
            ((Real.pi * eta) ^ 2)) := by
      field_simp [hpiEta.ne']
      ring
    _ ≤ test_affineRatioMajorant n Q gap M := by
      unfold test_affineRatioMajorant
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hheight hfirst) hsecond) (by norm_num)

lemma test_annulus_normalization_identity
    {nR D R eta q p e H : ℝ}
    (hn : nR ≠ 0) (hD : D ≠ 0) (hR : R ≠ 0)
    (hq : q ≠ 0) (hp : p ≠ 0) (heta : eta = D / q ^ 2) :
    6 * (4 * nR * D * e) * (R - D) * eta ^ 2 / D ^ 2 * H /
        (nR * R * (p * eta)) =
      (24 / (p * q ^ 2)) * ((e * H) * ((R - D) / R)) := by
  rw [heta]
  field_simp [hn, hD, hR, hq, hp]
  ring

lemma test_far_normalization_identity
    {nR D R eta q p Q T : ℝ}
    (hn : nR ≠ 0) (hD : D ≠ 0) (hR : R ≠ 0)
    (hq : q ≠ 0) (hp : p ≠ 0) (hQ : Q ≠ 0) (hT : T ≠ 0)
    (hDdef : D = R / Q) (heta : eta = D / q ^ 2) :
    nR * (3 * (R - D) * eta ^ 2 / T ^ 2) /
        (nR * R * (p * eta)) =
      (3 / (p * Q * q ^ 2)) * ((R - D) / T ^ 2) := by
  rw [heta, hDdef]
  field_simp [hn, hR, hq, hp, hQ, hT]

lemma test_add_tail_bounds
    {u v a b den d : ℝ} (hden : 0 ≤ den)
    (hu : u ≤ a * den) (hv : v ≤ b * den) (hab : a + b ≤ d) :
    u + v ≤ den * d := by
  calc
    u + v ≤ a * den + b * den := add_le_add hu hv
    _ = den * (a + b) := by ring
    _ ≤ den * d := mul_le_mul_of_nonneg_left hab hden

lemma test_count_conclusion
    {nR R rho delta p tail bulk count : ℝ}
    (hbulk : 2 * nR * R * (rho - delta / 2) * p ≤ bulk)
    (hraw : bulk - tail ≤ count * p)
    (htail : tail ≤ nR * R * p * (delta / 2))
    (hscale : 0 ≤ nR * R * p * delta) :
    2 * nR * R * (rho - delta) * p ≤ count * p := by
  have htail' : tail ≤ nR * R * p * delta := by
    calc
      tail ≤ nR * R * p * (delta / 2) := htail
      _ = (nR * R * p * delta) / 2 := by ring
      _ ≤ nR * R * p * delta := by linarith
  calc
    2 * nR * R * (rho - delta) * p =
        2 * nR * R * (rho - delta / 2) * p - nR * R * p * delta := by ring
    _ ≤ 2 * nR * R * (rho - delta / 2) * p - tail :=
      sub_le_sub_left htail' _
    _ ≤ bulk - tail := sub_le_sub_right hbulk tail
    _ ≤ count * p := hraw

lemma test_localNodeCount_log_window_of_controls
    {A B gap M S delta : ℝ} {Q n : ℕ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hM : 0 ≤ M)
    (hgap : 0 < gap) (hS : 0 < S) (hdelta : 0 < delta)
    (hQ : 2 ≤ Q)
    (hQloss : 2 * localDensityUpper gap M / (Q : ℝ) ≤ delta / 4)
    (haff : test_affineRatioMajorant n Q gap M < delta / 8)
    (htail :
      24 * (localDensityUpper gap M + delta / 8) * (1 + test_logScale n) /
          (Real.pi * test_logScale n ^ 2) +
        12 / (Real.pi * (Q : ℝ) * test_logScale n ^ 2 * S ^ 2) < delta / 2)
    (hcontrol : S * (Q : ℝ) / test_logScale n ^ 5 + 2 / (n : ℝ) < 1)
    (hLsmall : test_densityLipschitzConstant gap M * test_maxRadius n < delta / 8)
    (hmaxS : test_maxRadius n < S / 4)
    (hmaxOne : test_maxRadius n < 1)
    (hqLarge : 2 ≤ test_logScale n)
    (hn2 : 2 ≤ n) :
    ∀ X : NodeConfiguration n,
      |normalizationLevel X| ≤ M →
      (∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) →
      ∀ c : ℝ,
        (∀ x, |x - c| ≤ 2 * S →
          |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) →
        0 ≤ exteriorDensity X (normalizationLevel X) A B c 0 →
        ∀ R : ℝ, test_minRadius n ≤ R → R ≤ test_maxRadius n →
          2 * (n : ℝ) * R *
              (exteriorDensity X (normalizationLevel X) A B c 0 - delta) ≤
            (localNodeCount X c R : ℝ) := by
  let rhoU := localDensityUpper gap M
  let L := test_densityLipschitzConstant gap M
  have hL : 0 ≤ L := by
    exact test_densityLipschitzConstant_nonneg hgap.le M
  have hQpos : 0 < Q := by omega
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hSsq : 0 < S ^ 2 := sq_pos_of_pos hS
  intro X hnorm hLeb c hregular hrho0 R hRmin hRmax
  have hn : 0 < n := by omega
  let q := test_logScale n
  let D := R / (Q : ℝ)
  let eta := D / q ^ 2
  let N : ℕ := ⌈S / D + 1⌉₊
  let rho := exteriorDensity X (normalizationLevel X) A B c 0
  let E := test_smoothedDensityError n eta gap M
  have hq : 0 < q := by dsimp only [q]; linarith
  have hRminPos : 0 < test_minRadius n := by
    unfold test_minRadius
    positivity
  have hRpos : 0 < R := hRminPos.trans_le hRmin
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos hRpos hQR
  have hDR : D ≤ R := by
    dsimp only [D]
    have hQone : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
    exact div_le_self hRpos.le hQone
  have hRS : R < S := hRmax.trans_lt (hmaxS.trans (by linarith))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaD : 12 * eta ≤ Real.pi * D := by
    dsimp only [eta]
    have hq2 : 4 ≤ q ^ 2 := by nlinarith
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have hcoef : 12 / q ^ 2 ≤ Real.pi := by
      rw [div_le_iff₀ (sq_pos_of_pos hq)]
      nlinarith
    calc
      12 * eta = (12 / q ^ 2) * D := by dsimp only [eta]; ring
      _ ≤ Real.pi * D := mul_le_mul_of_nonneg_right hcoef hD.le
  have hN : 0 < N := by
    change 0 < ⌈S / D + 1⌉₊
    exact Nat.ceil_pos.2 (by positivity)
  have hceilLower : S / D + 1 ≤ (N : ℝ) := by
    exact Nat.le_ceil _
  have hceilUpper : (N : ℝ) < S / D + 2 := by
    dsimp only [N]
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ S / D + 1)).trans_eq
      (by ring)
  have hcoverLower : S + D ≤ (N : ℝ) * D := by
    have := mul_le_mul_of_nonneg_right hceilLower hD.le
    calc S + D = (S / D + 1) * D := by field_simp [hD.ne']
      _ ≤ (N : ℝ) * D := this
  have hcoverUpper : (N : ℝ) * D ≤ S + 2 * D := by
    have := mul_le_mul_of_nonneg_right hceilUpper.le hD.le
    calc (N : ℝ) * D ≤ (S / D + 2) * D := this
      _ = S + 2 * D := by field_simp [hD.ne']
  have hgeom : S + R + 3 * D ≤ 2 * S := by
    have h3D : 3 * D ≤ 3 * R / 2 := by
      have hQtwo : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      have hDhalf : D ≤ R / 2 := by
        dsimp only [D]
        apply (div_le_iff₀ hQR).2
        nlinarith
      linarith
    have hRquarter : R < S / 4 := hRmax.trans_lt hmaxS
    linarith
  have hregRaw : ∀ x, |x - c| ≤ S + R + 3 * D →
      |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v| := by
    intro x hx
    exact hregular x (hx.trans hgeom)
  have hetaLower : test_logScale n ^ 3 /
        ((Q : ℝ) * (n : ℝ)) ≤ eta := by
    dsimp only [eta, D, q]
    unfold test_minRadius at hRmin
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    calc
      test_logScale n ^ 3 / ((Q : ℝ) * (n : ℝ)) =
          (test_logScale n ^ 5 / (n : ℝ)) /
            ((Q : ℝ) * test_logScale n ^ 2) := by
        field_simp [hnR.ne', hQR.ne', hq.ne']
      _ ≤ R / ((Q : ℝ) * test_logScale n ^ 2) :=
        div_le_div_of_nonneg_right hRmin (by positivity)
      _ = R / (Q : ℝ) / test_logScale n ^ 2 := by ring
  have hetaUpper : eta ≤ (test_logScale n ^ 5)⁻¹ := by
    dsimp only [eta, D, q]
    unfold test_maxRadius at hRmax
    have hQone : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
    calc
      R / (Q : ℝ) / test_logScale n ^ 2 ≤
          (test_logScale n ^ 3)⁻¹ / (Q : ℝ) /
            test_logScale n ^ 2 := by gcongr
      _ ≤ (test_logScale n ^ 3)⁻¹ / test_logScale n ^ 2 := by
        exact div_le_div_of_nonneg_right
          (div_le_self (inv_nonneg.mpr (pow_nonneg hq.le 3)) hQone)
          (sq_nonneg _)
      _ = (test_logScale n ^ 5)⁻¹ := by
        field_simp [hq.ne']
  have he : E / (Real.pi * eta) < delta / 8 := by
    have hmajor := test_affineRatio_le_majorant (gap := gap) hn2 hQpos hM heta
      hetaLower hetaUpper
    exact hmajor.trans_lt (by simpa only [E] using haff)
  have he0 : 0 ≤ E / (Real.pi * eta) := by
    dsimp only [E]
    exact div_nonneg
      (by
        unfold test_smoothedDensityError
        exact mul_nonneg (by norm_num)
          (uniformAffineError_nonneg hn heta hM))
      (mul_nonneg Real.pi_pos.le heta.le)
  have hrhoU : rho ≤ rhoU := by
    obtain ⟨hcabs, hcsep⟩ := hregular c (by rw [sub_self, abs_zero]; linarith)
    dsimp only [rho, rhoU]
    exact exteriorDensity_le_localDensityUpper hn X hgap hcabs hcsep hM hnorm
  have hNle : N ≤ n := by
    have hDlower : test_logScale n ^ 5 /
        ((Q : ℝ) * (n : ℝ)) ≤ D := by
      dsimp only [D]
      unfold test_minRadius at hRmin
      calc
        test_logScale n ^ 5 / ((Q : ℝ) * (n : ℝ)) =
            (test_logScale n ^ 5 / (n : ℝ)) / (Q : ℝ) := by ring
        _ ≤ R / (Q : ℝ) := div_le_div_of_nonneg_right hRmin hQR.le
    have hSD : S / D ≤ S * (Q : ℝ) * (n : ℝ) /
        test_logScale n ^ 5 := by
      apply (div_le_div_iff₀ hD (by positivity)).2
      have hmul := mul_le_mul_of_nonneg_left hDlower hS.le
      field_simp [hQR.ne', (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn).ne', hq.ne'] at hmul ⊢
      nlinarith
    have hNcast : (N : ℝ) < (n : ℝ) := by
      calc
        (N : ℝ) < S / D + 2 := hceilUpper
        _ ≤ S * (Q : ℝ) * (n : ℝ) / test_logScale n ^ 5 + 2 := by
          linarith
        _ = (n : ℝ) *
            (S * (Q : ℝ) / test_logScale n ^ 5 + 2 / (n : ℝ)) := by
          field_simp [show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn]
        _ < (n : ℝ) := by
          have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
          exact (mul_lt_mul_of_pos_left hcontrol hnR).trans_eq (mul_one _)
    have : N < n := by exact_mod_cast hNcast
    exact this.le
  have hharm : (harmonic N : ℝ) ≤ 1 + q := by
    calc
      (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
      _ ≤ 1 + Real.log (n : ℝ) := by
        gcongr
      _ = 1 + q := by rfl
  have hraw := test_localNodeCount_lower_uniform hn2 X hA hB hM hnorm hLeb
    hN hD hDR hRS heta hetaD hcoverLower hcoverUpper hgap hregRaw
  have hLsmallR : L * (R - D) ≤ delta / 8 := by
    have hRDnonneg : 0 ≤ R - D := sub_nonneg.mpr hDR
    calc
      L * (R - D) ≤ L * R := mul_le_mul_of_nonneg_left (sub_le_self R hD.le) hL
      _ ≤ L * test_maxRadius n := mul_le_mul_of_nonneg_left hRmax hL
      _ ≤ delta / 8 := hLsmall.le
  have hbulk :
      2 * (n : ℝ) * R * (rho - delta / 2) * (Real.pi * eta) ≤
        (n : ℝ) * (2 * (R - D)) *
          (Real.pi * eta * (rho - L * (R - D)) - E) := by
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hpiEta0 : 0 < Real.pi * eta := mul_pos Real.pi_pos heta
    have hEbound : E ≤ Real.pi * eta * (delta / 8) := by
      simpa only [mul_comm] using (div_le_iff₀ hpiEta0).mp he.le
    have hDloss : 2 * D * rho ≤ R * (delta / 4) := by
      have hrhoNonneg : 0 ≤ rho := by simpa only [rho] using hrho0
      have hDrho : 2 * D * rho ≤ 2 * R * rhoU / (Q : ℝ) := by
        calc
          2 * D * rho ≤ 2 * D * rhoU :=
            mul_le_mul_of_nonneg_left hrhoU (by positivity)
          _ = 2 * R * rhoU / (Q : ℝ) := by dsimp only [D]; ring
      have hm := mul_le_mul_of_nonneg_left hQloss hRpos.le
      exact hDrho.trans (by
        calc
          2 * R * rhoU / (Q : ℝ) =
              R * (2 * rhoU / (Q : ℝ)) := by ring
          _ ≤ R * (delta / 4) := hm)
    have hsumLoss : L * (R - D) + delta / 8 ≤ delta / 4 := by
      linarith
    have hother : 2 * (R - D) *
        (L * (R - D) + delta / 8) ≤ R * (delta / 2) := by
      have hleft : 2 * (R - D) ≤ 2 * R := by linarith
      have hloss0 : 0 ≤ L * (R - D) + delta / 8 := by positivity
      have h2R0 : 0 ≤ 2 * R := by positivity
      have hmul := mul_le_mul hleft hsumLoss hloss0 h2R0
      calc
        2 * (R - D) * (L * (R - D) + delta / 8) ≤
            (2 * R) * (delta / 4) := hmul
        _ = R * (delta / 2) := by ring
    have htotalLoss : 2 * D * rho +
        2 * (R - D) * (L * (R - D) + delta / 8) ≤ R * delta := by
      calc
        2 * D * rho + 2 * (R - D) *
            (L * (R - D) + delta / 8) ≤
            R * (delta / 4) + R * (delta / 2) := add_le_add hDloss hother
        _ = (3 / 4 : ℝ) * (R * delta) := by ring
        _ ≤ 1 * (R * delta) :=
          mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hRpos.le hdelta.le)
        _ = R * delta := by ring
    have hcore :
        2 * R * (rho - delta / 2) ≤
          2 * (R - D) * (rho - L * (R - D) - delta / 8) := by
      calc
        2 * R * (rho - delta / 2) =
            2 * (R - D) * (rho - L * (R - D) - delta / 8) +
              (2 * D * rho + 2 * (R - D) *
                (L * (R - D) + delta / 8) - R * delta) := by ring
        _ ≤ 2 * (R - D) * (rho - L * (R - D) - delta / 8) :=
          add_le_of_nonpos_right (sub_nonpos.mpr htotalLoss)
    have hcoreMul :
        (2 * R * (rho - delta / 2)) * (Real.pi * eta) ≤
          (2 * (R - D) * (rho - L * (R - D) - delta / 8)) *
            (Real.pi * eta) :=
      mul_le_mul_of_nonneg_right hcore hpiEta0.le
    have hright :
        2 * (R - D) * (Real.pi * eta *
            (rho - L * (R - D) - delta / 8)) ≤
          2 * (R - D) *
            (Real.pi * eta * (rho - L * (R - D)) - E) := by
      have hRD : 0 ≤ 2 * (R - D) := by positivity
      apply mul_le_mul_of_nonneg_left _ hRD
      have hsub := sub_le_sub_left hEbound
        (Real.pi * eta * (rho - L * (R - D)))
      calc
        Real.pi * eta * (rho - L * (R - D) - delta / 8) =
            Real.pi * eta * (rho - L * (R - D)) -
              Real.pi * eta * (delta / 8) := by ring
        _ ≤ Real.pi * eta * (rho - L * (R - D)) - E := hsub
    have hbase :
        (2 * R * (rho - delta / 2)) * (Real.pi * eta) ≤
          2 * (R - D) *
            (Real.pi * eta * (rho - L * (R - D)) - E) := by
      calc
        (2 * R * (rho - delta / 2)) * (Real.pi * eta) ≤
            (2 * (R - D) * (rho - L * (R - D) - delta / 8)) *
              (Real.pi * eta) := hcoreMul
        _ = 2 * (R - D) * (Real.pi * eta *
              (rho - L * (R - D) - delta / 8)) := by ring
        _ ≤ 2 * (R - D) *
            (Real.pi * eta * (rho - L * (R - D)) - E) := hright
    calc
      2 * (n : ℝ) * R * (rho - delta / 2) * (Real.pi * eta) =
          (n : ℝ) *
            (2 * R * (rho - delta / 2) * (Real.pi * eta)) := by ring
      _ ≤ (n : ℝ) *
          (2 * (R - D) *
            (Real.pi * eta * (rho - L * (R - D)) - E)) :=
        mul_le_mul_of_nonneg_left hbase hnR
      _ = (n : ℝ) * (2 * (R - D)) *
          (Real.pi * eta * (rho - L * (R - D)) - E) := by ring
  have hshellNonneg : 0 ≤ test_shellCardBound n D eta gap M := by
    unfold test_shellCardBound
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hD.le)
      (add_nonneg (localDensityUpper_nonneg gap M) he0)
  have hannulus :
      6 * test_shellCardBound n D eta gap M * (R - D) * eta ^ 2 /
          D ^ 2 * (harmonic N : ℝ) /
          ((n : ℝ) * R * (Real.pi * eta)) ≤
        24 * (rhoU + delta / 8) * (1 + q) /
          (Real.pi * q ^ 2) := by
    have hRD : 0 ≤ R - D := sub_nonneg.mpr hDR
    have hRpos : 0 < R := hD.trans_le hDR
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have he' := he.le
    have hsum : rhoU + E / (Real.pi * eta) ≤ rhoU + delta / 8 := by linarith
    have hharm0 : 0 ≤ (harmonic N : ℝ) := by
      exact_mod_cast (harmonic_pos hN.ne').le
    have hupper0 : 0 ≤ rhoU + delta / 8 := by
      exact add_nonneg (localDensityUpper_nonneg gap M) (by positivity)
    have hupperProd0 : 0 ≤ (rhoU + delta / 8) * (1 + q) :=
      mul_nonneg hupper0 (by linarith)
    have hprod :
        (rhoU + E / (Real.pi * eta)) * (harmonic N : ℝ) ≤
          (rhoU + delta / 8) * (1 + q) :=
      mul_le_mul hsum hharm hharm0 hupper0
    have hratio : (R - D) / R ≤ 1 := (div_le_one hRpos).2 (sub_le_self R hD.le)
    have hratio0 : 0 ≤ (R - D) / R := div_nonneg hRD hRpos.le
    have hprod0 : 0 ≤ (rhoU + E / (Real.pi * eta)) *
        (harmonic N : ℝ) := mul_nonneg
          (add_nonneg (localDensityUpper_nonneg gap M) he0) hharm0
    have hprod' :
        ((rhoU + E / (Real.pi * eta)) * (harmonic N : ℝ)) *
            ((R - D) / R) ≤
          (rhoU + delta / 8) * (1 + q) := by
      simpa only [mul_one] using
        (mul_le_mul hprod hratio hratio0 hupperProd0)
    have heq :
        6 * test_shellCardBound n D eta gap M * (R - D) * eta ^ 2 /
              D ^ 2 * (harmonic N : ℝ) /
              ((n : ℝ) * R * (Real.pi * eta)) =
          (24 / (Real.pi * q ^ 2)) *
            (((rhoU + E / (Real.pi * eta)) * (harmonic N : ℝ)) *
              ((R - D) / R)) := by
      rw [show test_shellCardBound n D eta gap M =
        4 * (n : ℝ) * D * (rhoU + E / (Real.pi * eta)) by rfl]
      exact test_annulus_normalization_identity hnR.ne' hD.ne' hRpos.ne'
        hq.ne' Real.pi_ne_zero rfl
    rw [heq]
    calc
      (24 / (Real.pi * q ^ 2)) *
          (((rhoU + E / (Real.pi * eta)) * (harmonic N : ℝ)) *
            ((R - D) / R)) ≤
          (24 / (Real.pi * q ^ 2)) *
            ((rhoU + delta / 8) * (1 + q)) :=
        mul_le_mul_of_nonneg_left hprod' (by positivity)
      _ = 24 * (rhoU + delta / 8) * (1 + q) /
          (Real.pi * q ^ 2) := by ring
  have hfar :
      (n : ℝ) * (3 * (R - D) * eta ^ 2 /
          (S - (R - D)) ^ 2) /
          ((n : ℝ) * R * (Real.pi * eta)) ≤
        12 / (Real.pi * (Q : ℝ) * q ^ 2 * S ^ 2) := by
    have hRquarter : R ≤ S / 4 := hRmax.trans hmaxS.le
    have hsep : S / 2 ≤ S - (R - D) := by
      have hRDquarter : R - D ≤ S / 4 :=
        (sub_le_self R hD.le).trans hRquarter
      linarith only [hRDquarter, hS]
    have hsepSq : (S / 2) ^ 2 ≤ (S - (R - D)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsep 2
    have hsepPos : 0 < S - (R - D) := (half_pos hS).trans_le hsep
    have hRDone : R - D ≤ 1 := by
      exact (sub_le_self R hD.le).trans (hRmax.trans hmaxOne.le)
    have hcross : (R - D) * S ^ 2 ≤ 4 * (S - (R - D)) ^ 2 := by
      calc
        (R - D) * S ^ 2 ≤ 1 * S ^ 2 :=
          mul_le_mul_of_nonneg_right hRDone (sq_nonneg S)
        _ ≤ 4 * (S - (R - D)) ^ 2 := by
          nlinarith only [hsepSq]
    have hfrac : (R - D) / (S - (R - D)) ^ 2 ≤ 4 / S ^ 2 := by
      exact (div_le_div_iff₀ (sq_pos_of_pos hsepPos) hSsq).2 hcross
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have heq :
        (n : ℝ) * (3 * (R - D) * eta ^ 2 /
            (S - (R - D)) ^ 2) /
            ((n : ℝ) * R * (Real.pi * eta)) =
          (3 / (Real.pi * (Q : ℝ) * q ^ 2)) *
            ((R - D) / (S - (R - D)) ^ 2) := by
      exact test_far_normalization_identity hnR.ne' hD.ne' hRpos.ne'
        hq.ne' Real.pi_ne_zero hQR.ne' hsepPos.ne' rfl rfl
    rw [heq]
    calc
      (3 / (Real.pi * (Q : ℝ) * q ^ 2)) *
          ((R - D) / (S - (R - D)) ^ 2) ≤
          (3 / (Real.pi * (Q : ℝ) * q ^ 2)) * (4 / S ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 12 / (Real.pi * (Q : ℝ) * q ^ 2 * S ^ 2) := by ring
  have htailBound :
      6 * test_shellCardBound n D eta gap M * (R - D) * eta ^ 2 /
            D ^ 2 * (harmonic N : ℝ) +
        (n : ℝ) * (3 * (R - D) * eta ^ 2 /
          (S - (R - D)) ^ 2) ≤
        (n : ℝ) * R * (Real.pi * eta) * (delta / 2) := by
    have hden : 0 < (n : ℝ) * R * (Real.pi * eta) := by positivity
    have ha := (div_le_iff₀ hden).mp hannulus
    have hf := (div_le_iff₀ hden).mp hfar
    have hsum := add_le_add ha hf
    have ht : 24 * (rhoU + delta / 8) * (1 + q) /
          (Real.pi * q ^ 2) +
        12 / (Real.pi * (Q : ℝ) * q ^ 2 * S ^ 2) ≤ delta / 2 := by
      simpa only [rhoU, q] using htail.le
    have hsum' := test_add_tail_bounds hden.le ha hf ht
    simpa only [mul_assoc] using hsum'
  have htotal :
      2 * (n : ℝ) * R * (rho - delta) * (Real.pi * eta) ≤
        (localNodeCount X c R : ℝ) * (Real.pi * eta) := by
    have h := hbulk
    dsimp only [rho, L, E] at hraw h ⊢
    exact test_count_conclusion h hraw htailBound (by positivity)
  exact (mul_le_mul_iff_of_pos_right (mul_pos Real.pi_pos heta)).mp
    (by simpa only [rho] using htotal)

lemma test_eventually_localNodeCount_log_window
    {A B gap M S delta : ℝ} {Q : ℕ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hM : 0 ≤ M)
    (hgap : 0 < gap) (hS : 0 < S) (hdelta : 0 < delta)
    (hQ : 2 ≤ Q)
    (hQloss : 2 * localDensityUpper gap M / (Q : ℝ) ≤ delta / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ X : NodeConfiguration n,
      |normalizationLevel X| ≤ M →
      (∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ)) →
      ∀ c : ℝ,
        (∀ x, |x - c| ≤ 2 * S →
          |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|) →
        0 ≤ exteriorDensity X (normalizationLevel X) A B c 0 →
        ∀ R : ℝ, test_minRadius n ≤ R → R ≤ test_maxRadius n →
          2 * (n : ℝ) * R *
              (exteriorDensity X (normalizationLevel X) A B c 0 - delta) ≤
            (localNodeCount X c R : ℝ) := by
  let rhoU := localDensityUpper gap M
  let L := test_densityLipschitzConstant gap M
  have hQpos : 0 < Q := by omega
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hi := test_tendsto_inv_logScale
  have hi2 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 2)
      atTop (𝓝 0) := by simpa using hi.pow 2
  have hi3 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 3)
      atTop (𝓝 0) := by simpa using hi.pow 3
  have hi5 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 5)
      atTop (𝓝 0) := by simpa using hi.pow 5
  have hnatInv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have htailLim : Tendsto (fun n : ℕ ↦
      24 * (rhoU + delta / 8) * (1 + test_logScale n) /
          (Real.pi * test_logScale n ^ 2) +
        12 / (Real.pi * (Q : ℝ) * test_logScale n ^ 2 * S ^ 2))
      atTop (𝓝 0) := by
    have hfirst := (hi2.add hi).const_mul
      (24 * (rhoU + delta / 8) / Real.pi)
    have hsecond := hi2.const_mul (12 / (Real.pi * (Q : ℝ) * S ^ 2))
    have ht : Tendsto (fun n ↦
        24 * (rhoU + delta / 8) / Real.pi *
            ((test_logScale n)⁻¹ ^ 2 + (test_logScale n)⁻¹) +
          12 / (Real.pi * (Q : ℝ) * S ^ 2) *
            (test_logScale n)⁻¹ ^ 2) atTop (𝓝 0) := by
      simpa using hfirst.add hsecond
    apply ht.congr'
    filter_upwards [test_tendsto_logScale.eventually (eventually_gt_atTop 0)] with n hqn
    field_simp [hqn.ne', Real.pi_ne_zero, hQR.ne', hS.ne']
  have hcontrolLim : Tendsto (fun n : ℕ ↦
      S * (Q : ℝ) / test_logScale n ^ 5 + 2 / (n : ℝ))
      atTop (𝓝 0) := by
    have hfirst := hi5.const_mul (S * (Q : ℝ))
    have hsecond := hnatInv.const_mul 2
    convert hfirst.add hsecond using 1
    · funext n
      simp only [div_eq_mul_inv, inv_pow]
    · ring_nf
  have hLmaxLim : Tendsto (fun n : ℕ ↦ L * test_maxRadius n)
      atTop (𝓝 0) := by
    convert hi3.const_mul L using 1
    · funext n
      simp only [test_maxRadius, inv_pow]
    · ring_nf
  have hmaxLim : Tendsto test_maxRadius atTop (𝓝 0) := by
    convert hi3 using 1
    funext n
    simp only [test_maxRadius, inv_pow]
  have haff :=
    (test_tendsto_affineRatioMajorant Q gap M).eventually_lt_const
      (by linarith : 0 < delta / 8)
  have htail := htailLim.eventually_lt_const (by linarith : 0 < delta / 2)
  have hcontrol := hcontrolLim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hLsmall := hLmaxLim.eventually_lt_const (by linarith : 0 < delta / 8)
  have hmaxS := hmaxLim.eventually_lt_const (by positivity : 0 < S / 4)
  have hmaxOne := hmaxLim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hqLarge := test_tendsto_logScale.eventually (eventually_ge_atTop 2)
  filter_upwards [haff, htail, hcontrol, hLsmall, hmaxS, hmaxOne,
      hqLarge, eventually_ge_atTop 2] with n haff htail hcontrol hLsmall
      hmaxS hmaxOne hqLarge hn2
  exact test_localNodeCount_log_window_of_controls hA hB hM hgap hS hdelta
    hQ hQloss haff (by simpa only [rhoU] using htail) hcontrol
    (by simpa only [L] using hLsmall) hmaxS hmaxOne hqLarge hn2

/-! ### A logarithmic-scale derivative estimate -/

noncomputable def test_derivativeRadius (n : ℕ) : ℝ :=
  (test_logScale n ^ 4)⁻¹

noncomputable def test_derivativeBase (n : ℕ) : ℝ :=
  1 + 1 / test_logScale n

noncomputable def test_derivativeHeight (n : ℕ) : ℝ :=
  test_derivativeRadius n *
    (test_derivativeBase n - (test_derivativeBase n)⁻¹) / 2

noncomputable def test_derivativeHoriz (n : ℕ) : ℝ :=
  test_derivativeRadius n *
    (test_derivativeBase n + (test_derivativeBase n)⁻¹) / 2

noncomputable def test_derivativeExponent
    (n : ℕ) (rho gap M : ℝ) : ℝ :=
  (n : ℝ) *
    (Real.pi * test_derivativeHeight n *
        (rho + test_densityLipschitzConstant gap M *
          (test_maxRadius n + test_derivativeHoriz n)) +
      uniformAffineError n (test_derivativeHeight n) gap M)

noncomputable def test_derivativeCutoff
    (n : ℕ) (rho gap M : ℝ) : ℕ :=
  ⌈test_derivativeExponent n rho gap M /
      Real.log (test_derivativeBase n) + 8 * test_logScale n ^ 2⌉₊

lemma test_exp_div_pow_eq {E r : ℝ} {m : ℕ} (hr : 0 < r) :
    Real.exp E / r ^ m = Real.exp (E - (m : ℝ) * Real.log r) := by
  have hp : r ^ m = Real.exp ((m : ℝ) * Real.log r) := by
    rw [← Real.exp_log (pow_pos hr m), Real.log_pow]
  rw [div_eq_mul_inv, hp, ← Real.exp_neg, ← Real.exp_add]
  congr 1

lemma test_exp_div_pow_le_safety
    {E r s : ℝ} {m : ℕ} (hr : 1 < r) (hs : 0 ≤ s)
    (hm : E / Real.log r + s ≤ (m : ℝ)) :
    Real.exp E / r ^ m ≤ Real.exp (-s * Real.log r) := by
  rw [test_exp_div_pow_eq (zero_lt_one.trans hr)]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hmul := mul_le_mul_of_nonneg_right hm hlog.le
  have hcancel : (E / Real.log r) * Real.log r = E := by
    field_simp [hlog.ne']
  rw [add_mul, hcancel] at hmul
  linarith

lemma test_scale_le_of_anchor
    {h nR rate scale amp : ℝ} (hh : 0 < h) (hn : 0 < nR)
    (hlower : (h / (2 * nR)) * scale * Real.exp (-rate * h) ≤ amp) :
    scale ≤ (2 * nR / h) * Real.exp (rate * h) * amp := by
  let F := (2 * nR / h) * Real.exp (rate * h)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hmul := mul_le_mul_of_nonneg_left hlower hF
  calc
    scale = F * ((h / (2 * nR)) * scale * Real.exp (-rate * h)) := by
      dsimp only [F]
      have hexp : Real.exp (rate * h) * Real.exp (-rate * h) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1 <;> ring_nf
      symm
      calc
        (2 * nR / h) * Real.exp (rate * h) *
            ((h / (2 * nR)) * scale * Real.exp (-rate * h)) =
            ((2 * nR / h) * (h / (2 * nR))) * scale *
              (Real.exp (rate * h) * Real.exp (-rate * h)) := by ring
        _ = scale := by rw [hexp]; field_simp [hh.ne', hn.ne']
    _ ≤ F * amp := hmul
    _ = (2 * nR / h) * Real.exp (rate * h) * amp := by rfl

lemma test_localEllipseBound_le_derivativeExponent
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B z center gap M : ℝ}
    (hgap : 0 < gap) (hM : 0 ≤ M)
    (hnorm : |normalizationLevel X| ≤ M)
    (hzunit : |z| ≤ 1)
    (hcenterunit : |center| ≤ 1)
    (hzsep : ∀ v ∉ Set.Icc A B, gap ≤ |z - v|)
    (hcentersep : ∀ v ∉ Set.Icc A B, gap ≤ |center - v|)
    (hdist : |center - z| ≤ test_maxRadius n) :
    test_localEllipseBound X A B center (test_derivativeRadius n)
        (test_derivativeBase n) gap M ≤
      nodalScale X * Real.exp
        (test_derivativeExponent n
          (exteriorDensity X (normalizationLevel X) A B z 0) gap M) := by
  have hn : 0 < n := by omega
  let L := test_densityLipschitzConstant gap M
  have hL : 0 ≤ L := test_densityLipschitzConstant_nonneg hgap.le M
  have hvar := test_abs_boundaryDensity_sub_le_uniform hn X hgap
    hcenterunit hzunit hcentersep hzsep hM hnorm
  have hrho :
      exteriorDensity X (normalizationLevel X) A B center 0 ≤
        exteriorDensity X (normalizationLevel X) A B z 0 +
          L * test_maxRadius n := by
    have hright := (abs_le.mp hvar).2
    have hmul := mul_le_mul_of_nonneg_left hdist hL
    dsimp only [L] at hright hmul ⊢
    linarith
  unfold test_localEllipseBound
  change nodalScale X * Real.exp ((n : ℝ) *
      (Real.pi * test_derivativeHeight n *
          (exteriorDensity X (normalizationLevel X) A B center 0 +
            test_densityLipschitzConstant gap M * test_derivativeHoriz n) +
        uniformAffineError n (test_derivativeHeight n) gap M)) ≤
    nodalScale X * Real.exp
      (test_derivativeExponent n
        (exteriorDensity X (normalizationLevel X) A B z 0) gap M)
  apply mul_le_mul_of_nonneg_left _ (nodalScale_pos hn X).le
  apply Real.exp_le_exp.mpr
  have hheight : 0 ≤ test_derivativeHeight n := by
    have hq : 0 < test_logScale n := by
      unfold test_logScale
      exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hb : 1 < 1 + 1 / test_logScale n := by
      linarith [one_div_pos.mpr hq]
    have hdifference : 0 < (1 + 1 / test_logScale n) -
        (1 + 1 / test_logScale n)⁻¹ := by
      rw [sub_pos]
      exact ((inv_lt_one₀ (zero_lt_one.trans hb)).2 hb).trans hb
    have hradius : 0 < test_derivativeRadius n := by
      unfold test_derivativeRadius
      positivity
    unfold test_derivativeHeight
    exact div_nonneg
      (mul_nonneg hradius.le (by
        simpa only [test_derivativeBase] using hdifference.le)) (by norm_num)
  have hinside :
      exteriorDensity X (normalizationLevel X) A B center 0 +
          L * test_derivativeHoriz n ≤
        exteriorDensity X (normalizationLevel X) A B z 0 +
          L * (test_maxRadius n + test_derivativeHoriz n) := by
    linarith
  unfold test_derivativeExponent
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hinside
      (mul_nonneg Real.pi_pos.le hheight)) le_rfl

lemma test_truncated_derivative_expression_le
    {nR mR radius edge amp tail mainC tailC tailBound : ℝ}
    (hnR : 0 ≤ nR) (hmR : 0 ≤ mR) (hradius : 0 < radius)
    (hedge : 0 ≤ edge) (hamp : 0 ≤ amp) (htail0 : 0 ≤ tail)
    (htailC : 0 ≤ tailC)
    (hsize : (mR + 1) + (nR + 1) ≤ 3 * nR)
    (hmain : (mR + 1) * edge / radius ≤ mainC)
    (htail : tail ≤ tailC * amp)
    (htailScalar : 6 * nR ^ 2 * tailC / radius ≤ tailBound) :
    ((mR + 1) * (edge * amp + nR * (2 * tail)) +
        nR * (2 * tail) * (nR + 1)) / radius ≤
      (mainC + tailBound) * amp := by
  have hmain' : ((mR + 1) * edge * amp) / radius ≤ mainC * amp := by
    calc
      (mR + 1) * edge * amp / radius =
          ((mR + 1) * edge / radius) * amp := by ring
      _ ≤ mainC * amp := mul_le_mul_of_nonneg_right hmain hamp
  have hsum0 : 0 ≤ (mR + 1) + (nR + 1) := by positivity
  have htail' :
      (2 * nR * tail * ((mR + 1) + (nR + 1))) / radius ≤
        tailBound * amp := by
    calc
      2 * nR * tail * ((mR + 1) + (nR + 1)) / radius ≤
          2 * nR * (tailC * amp) * (3 * nR) / radius := by
        gcongr
      _ = (6 * nR ^ 2 * tailC / radius) * amp := by ring
      _ ≤ tailBound * amp :=
        mul_le_mul_of_nonneg_right htailScalar hamp
  calc
    ((mR + 1) * (edge * amp + nR * (2 * tail)) +
          nR * (2 * tail) * (nR + 1)) / radius =
        ((mR + 1) * edge * amp) / radius +
          (2 * nR * tail * ((mR + 1) + (nR + 1))) / radius := by ring
    _ ≤ mainC * amp + tailBound * amp := add_le_add hmain' htail'
    _ = (mainC + tailBound) * amp := by ring

lemma test_abs_nodal_derivative_le_of_controls
    {n : ℕ} (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {A B z center gap M delta : ℝ}
    (hA : -1 ≤ A) (hB : B ≤ 1) (hAB : A ≤ B)
    (hM : 0 ≤ M) (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc A B, lebesgueFunction X v ≤ (n : ℝ))
    (hgap : 0 < gap) (hdelta : 0 < delta)
    (hrho0 : 0 ≤ exteriorDensity X (normalizationLevel X) A B z 0)
    (hzunit : |z| ≤ 1)
    (hzsep : ∀ v ∉ Set.Icc A B, gap ≤ |z - v|)
    (hdist : |center - z| ≤ test_maxRadius n)
    (hleft : A ≤ center - test_derivativeRadius n)
    (hright : center + test_derivativeRadius n ≤ B)
    (hanchorA0 : -1 ≤ center - (test_logScale n)⁻¹)
    (hanchorB0 : center + (test_logScale n)⁻¹ ≤ 1)
    (hanchorA : A ≤ center - (test_logScale n)⁻¹)
    (hanchorB : center + (test_logScale n)⁻¹ ≤ B)
    (hregular : ∀ x,
      |x - center| ≤ test_derivativeHoriz n →
        |x| ≤ 1 ∧ ∀ v ∉ Set.Icc A B, gap ≤ |x - v|)
    (hmle : test_derivativeCutoff n
        (exteriorDensity X (normalizationLevel X) A B z 0) gap M ≤ n)
    (hmain :
      (((test_derivativeCutoff n
          (exteriorDensity X (normalizationLevel X) A B z 0) gap M + 1 : ℕ) : ℝ) *
          Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)) /
          test_derivativeRadius n ≤
        (n : ℝ) *
          (Real.pi * exteriorDensity X (normalizationLevel X) A B z 0 +
            3 * delta / 4))
    (htailScalar :
      6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 *
                Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ (n : ℝ) * delta / 4) :
    |(nodalPolynomial X).derivative.eval center| ≤
      (n : ℝ) *
        (Real.pi * exteriorDensity X (normalizationLevel X) A B z 0 + delta) *
          amplitude X A B (test_logScale n ^ 2) center hAB := by
  have hn : 0 < n := by omega
  let q := test_logScale n
  let radius := test_derivativeRadius n
  let r := test_derivativeBase n
  let rho := exteriorDensity X (normalizationLevel X) A B z 0
  let E := test_derivativeExponent n rho gap M
  let m := test_derivativeCutoff n rho gap M
  let amp := amplitude X A B (q ^ 2) center hAB
  let Mellipse := test_localEllipseBound X A B center radius r gap M
  let tail := Mellipse / r ^ (m + 1)
  have hq : 0 < q := by
    dsimp only [q, test_logScale]
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hradius : 0 < radius := by
    dsimp only [radius, test_derivativeRadius]
    positivity
  have hr : 1 < r := by
    dsimp only [r, test_derivativeBase]
    linarith [one_div_pos.mpr hq]
  have hhoriz : 0 ≤ test_derivativeHoriz n := by
    unfold test_derivativeHoriz
    have hr0 : 0 < test_derivativeBase n := zero_lt_one.trans hr
    exact div_nonneg
      (mul_nonneg hradius.le (add_nonneg hr0.le (inv_nonneg.mpr hr0.le)))
      (by norm_num)
  have hcenterReg := hregular center (by
    rw [sub_self, abs_zero]
    exact hhoriz)
  have hMellipse : Mellipse ≤ nodalScale X * Real.exp E := by
    exact test_localEllipseBound_le_derivativeExponent hn2 X hgap hM hnorm
      hzunit hcenterReg.1 hzsep hcenterReg.2 hdist
  have hamp0 : 0 ≤ amp := by
    exact amplitude_nonneg X hAB
  have hanchor := amplitude_anchor_lower hn2 X hAB (sq_nonneg q)
    (inv_pos.mpr hq) hanchorA0 hanchorB0 hanchorA hanchorB
  have hscale : nodalScale X ≤
      2 * (n : ℝ) * q * Real.exp q * amp := by
    have hs := test_scale_le_of_anchor (inv_pos.mpr hq)
      (show 0 < (n : ℝ) by exact_mod_cast hn) hanchor
    dsimp only [amp]
    convert hs using 1 <;> field_simp [hq.ne'] <;> ring
  have hmLower : E / Real.log r + 8 * q ^ 2 ≤ (m : ℝ) := by
    dsimp only [m, test_derivativeCutoff, E, rho, q, r]
    exact Nat.le_ceil _
  have hsafety : Real.exp E / r ^ (m + 1) ≤
      Real.exp (-8 * q ^ 2 * Real.log r) := by
    have hmcast : E / Real.log r + 8 * q ^ 2 ≤ ((m + 1 : ℕ) : ℝ) := by
      exact hmLower.trans (by exact_mod_cast Nat.le_succ m)
    convert test_exp_div_pow_le_safety (E := E) (r := r)
      (s := 8 * q ^ 2) (m := m + 1) hr
      (mul_nonneg (by norm_num) (sq_nonneg q)) hmcast using 1 <;> ring_nf
  have htail0 : 0 ≤ tail := by
    dsimp only [tail, Mellipse]
    exact div_nonneg
      (by
        unfold test_localEllipseBound
        exact mul_nonneg (nodalScale_pos hn X).le (Real.exp_pos _).le)
      (pow_nonneg (zero_lt_one.trans hr).le _)
  have htail : tail ≤
      (2 * (n : ℝ) * q *
        Real.exp (q - 8 * q ^ 2 * Real.log r)) * amp := by
    have hdiv : Mellipse / r ^ (m + 1) ≤
        (nodalScale X * Real.exp E) / r ^ (m + 1) :=
      div_le_div_of_nonneg_right hMellipse
        (pow_pos (zero_lt_one.trans hr) (m + 1)).le
    have hprod : nodalScale X * Real.exp E / r ^ (m + 1) ≤
        (2 * (n : ℝ) * q * Real.exp q * amp) *
          Real.exp (-8 * q ^ 2 * Real.log r) := by
      calc
        nodalScale X * Real.exp E / r ^ (m + 1) =
            nodalScale X * (Real.exp E / r ^ (m + 1)) := by ring
        _ ≤ (2 * (n : ℝ) * q * Real.exp q * amp) *
              Real.exp (-8 * q ^ 2 * Real.log r) := by
          exact mul_le_mul hscale hsafety
            (div_nonneg (Real.exp_pos E).le
              (pow_nonneg (zero_lt_one.trans hr).le _))
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) hq.le)
                (Real.exp_pos q).le) hamp0)
    calc
      tail ≤ nodalScale X * Real.exp E / r ^ (m + 1) := hdiv
      _ ≤ (2 * (n : ℝ) * q * Real.exp q * amp) *
          Real.exp (-8 * q ^ 2 * Real.log r) := hprod
      _ = (2 * (n : ℝ) * q *
          Real.exp (q - 8 * q ^ 2 * Real.log r)) * amp := by
        have hexp : Real.exp q * Real.exp (-8 * q ^ 2 * Real.log r) =
            Real.exp (q - 8 * q ^ 2 * Real.log r) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          (2 * (n : ℝ) * q * Real.exp q * amp) *
              Real.exp (-8 * q ^ 2 * Real.log r) =
              2 * (n : ℝ) * q *
                (Real.exp q * Real.exp (-8 * q ^ 2 * Real.log r)) * amp := by ring
          _ = (2 * (n : ℝ) * q *
              Real.exp (q - 8 * q ^ 2 * Real.log r)) * amp := by rw [hexp]
  have hraw := test_abs_nodal_derivative_le_of_local_potential
    (m := m) hn2 X hA hB hAB hM hnorm hLeb (sq_nonneg q)
      hradius hleft hright hr hgap hregular
  have hmcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
  have hsize : ((m : ℝ) + 1) + ((n : ℝ) + 1) ≤ 3 * (n : ℝ) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hbound := test_truncated_derivative_expression_le
    (nR := (n : ℝ)) (mR := (m : ℝ)) (radius := radius)
    (edge := Real.exp (q ^ 2 * radius)) (amp := amp) (tail := tail)
    (mainC := (n : ℝ) * (Real.pi * rho + 3 * delta / 4))
    (tailC := 2 * (n : ℝ) * q *
      Real.exp (q - 8 * q ^ 2 * Real.log r))
    (tailBound := (n : ℝ) * delta / 4)
    (Nat.cast_nonneg n) (Nat.cast_nonneg m) hradius (Real.exp_pos _).le
    hamp0 htail0 (by positivity) hsize
    (by simpa only [m, rho, q, radius, Nat.cast_add, Nat.cast_one] using hmain) htail
    (by simpa only [q, r, radius] using htailScalar)
  calc
    |(nodalPolynomial X).derivative.eval center| ≤
        ((((m + 1 : ℕ) : ℝ) *
            (Real.exp (q ^ 2 * radius) * amp +
              (n : ℝ) * (2 * tail)) +
          (n : ℝ) * (2 * tail) * ((n + 1 : ℕ) : ℝ)) / radius) := by
      simpa only [m, q, radius, r, amp, Mellipse, tail] using hraw
    _ ≤ ((n : ℝ) * (Real.pi * rho + 3 * delta / 4) +
          (n : ℝ) * delta / 4) * amp := by
      simpa only [Nat.cast_add, Nat.cast_one] using hbound
    _ = (n : ℝ) * (Real.pi * rho + delta) * amp := by ring
    _ = (n : ℝ) *
        (Real.pi * exteriorDensity X (normalizationLevel X) A B z 0 + delta) *
          amplitude X A B (test_logScale n ^ 2) center hAB := by rfl

noncomputable def test_derivativeHeightRatio (n : ℕ) : ℝ :=
  test_derivativeHeight n /
    (test_derivativeRadius n * Real.log (test_derivativeBase n))

noncomputable def test_derivativeSlack (n : ℕ) (gap M : ℝ) : ℝ :=
  let H := test_derivativeHeightRatio n
  let rhoU := localDensityUpper gap M
  let L := test_densityLipschitzConstant gap M
  Real.pi * |H - 1| * rhoU +
    Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) +
    Real.pi * H * test_affineRatioMajorant n 2 gap M +
    (8 * test_logScale n ^ 2 + 2) /
      ((n : ℝ) * test_derivativeRadius n)

noncomputable def test_derivativeTotalSlack (n : ℕ) (gap M : ℝ) : ℝ :=
  let edge := Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)
  Real.pi * localDensityUpper gap M * |edge - 1| +
    test_derivativeSlack n gap M * edge

lemma test_ratio_cancel {a b x y : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hy : y ≠ 0) :
    a * x / (a * y) = b * x / (b * y) := by
  field_simp [ha, hb, hy]

lemma test_tendsto_derivativeHeightRatio :
    Tendsto test_derivativeHeightRatio atTop (𝓝 1) := by
  have hnum := test_tendsto_logScale_mul_ellipseHeightFactor
  have hden := test_tendsto_logScale_mul_log_shellBase
  have ht := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have ht' : Tendsto
      ((fun n : ℕ ↦ test_logScale n *
          (((1 + 1 / test_logScale n) -
            (1 + 1 / test_logScale n)⁻¹) / 2)) /
        (fun n : ℕ ↦ test_logScale n *
          Real.log (1 + 1 / test_logScale n))) atTop (𝓝 1) := by
    simpa using ht
  apply ht'.congr'
  filter_upwards [test_tendsto_logScale.eventually (eventually_gt_atTop 0)] with n hq
  have hradius : 0 < test_derivativeRadius n := by
    unfold test_derivativeRadius
    positivity
  have hb : 1 < test_derivativeBase n := by
    unfold test_derivativeBase
    linarith [one_div_pos.mpr hq]
  have hlog : 0 < Real.log (test_derivativeBase n) := Real.log_pos hb
  rw [show test_derivativeHeightRatio n =
      test_derivativeRadius n *
          ((test_derivativeBase n - (test_derivativeBase n)⁻¹) / 2) /
        (test_derivativeRadius n * Real.log (test_derivativeBase n)) by
    unfold test_derivativeHeightRatio test_derivativeHeight
    ring]
  change test_logScale n *
      ((test_derivativeBase n - (test_derivativeBase n)⁻¹) / 2) /
        (test_logScale n * Real.log (test_derivativeBase n)) =
    test_derivativeRadius n *
      ((test_derivativeBase n - (test_derivativeBase n)⁻¹) / 2) /
        (test_derivativeRadius n * Real.log (test_derivativeBase n))
  exact test_ratio_cancel hq.ne' hradius.ne' hlog.ne'

lemma test_tendsto_derivativeHoriz :
    Tendsto test_derivativeHoriz atTop (𝓝 0) := by
  have hi := test_tendsto_inv_logScale
  have hrad : Tendsto test_derivativeRadius atTop (𝓝 0) := by
    convert (hi.pow 4) using 1
    · funext n
      simp only [test_derivativeRadius, inv_pow]
    · ring_nf
  have hbase : Tendsto test_derivativeBase atTop (𝓝 1) := by
    unfold test_derivativeBase
    simpa using tendsto_const_nhds.add hi
  have hbaseInv : Tendsto (fun n ↦ (test_derivativeBase n)⁻¹)
      atTop (𝓝 1) := by
    simpa using hbase.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hfactor : Tendsto (fun n ↦
      (test_derivativeBase n + (test_derivativeBase n)⁻¹) / 2)
      atTop (𝓝 1) := by
    convert (hbase.add hbaseInv).div_const 2 using 1 <;> norm_num
  unfold test_derivativeHoriz
  convert hrad.mul hfactor using 1
  · funext n
    ring
  · norm_num

lemma test_tendsto_derivativeEdge :
    Tendsto (fun n : ℕ ↦
      Real.exp (test_logScale n ^ 2 * test_derivativeRadius n))
      atTop (𝓝 1) := by
  have hi := test_tendsto_inv_logScale
  have hi2 : Tendsto (fun n : ℕ ↦ (test_logScale n)⁻¹ ^ 2)
      atTop (𝓝 0) := by simpa using hi.pow 2
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hi2
  convert hexp using 1
  · funext n
    congr 1
    by_cases hq : test_logScale n = 0
    · simp [test_derivativeRadius, hq]
    · unfold test_derivativeRadius
      field_simp [hq]
  · norm_num

lemma test_tendsto_derivativeSlack (gap M : ℝ) :
    Tendsto (fun n : ℕ ↦ test_derivativeSlack n gap M) atTop (𝓝 0) := by
  let rhoU := localDensityUpper gap M
  let L := test_densityLipschitzConstant gap M
  have hH := test_tendsto_derivativeHeightRatio
  have hHabs : Tendsto (fun n : ℕ ↦ |test_derivativeHeightRatio n - 1|)
      atTop (𝓝 0) := by
    simpa using (hH.sub_const 1).abs
  have hwindow : Tendsto (fun n : ℕ ↦
      test_maxRadius n + test_derivativeHoriz n) atTop (𝓝 0) := by
    have hmax : Tendsto test_maxRadius atTop (𝓝 0) := by
      have hi := test_tendsto_inv_logScale
      convert hi.pow 3 using 1
      · funext n
        simp only [test_maxRadius, inv_pow]
      · ring_nf
    simpa using hmax.add test_tendsto_derivativeHoriz
  have hfirst := hHabs.const_mul (Real.pi * rhoU)
  have hsecond := (hH.mul hwindow).const_mul (Real.pi * L)
  have hthird := (hH.mul (test_tendsto_affineRatioMajorant 2 gap M)).const_mul Real.pi
  have hlast : Tendsto (fun n : ℕ ↦
      (8 * test_logScale n ^ 2 + 2) /
        ((n : ℝ) * test_derivativeRadius n)) atTop (𝓝 0) := by
    have h6 := (test_tendsto_logScale_pow_div_nat 6).const_mul 8
    have h4 := (test_tendsto_logScale_pow_div_nat 4).const_mul 2
    have ht := h6.add h4
    convert ht using 1
    · funext n
      by_cases hn : n = 0
      · simp [hn, test_derivativeRadius]
      by_cases hq : test_logScale n = 0
      · simp [test_derivativeRadius, hq]
      · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        unfold test_derivativeRadius
        field_simp [hq, hnR]
    · norm_num
  have ht := ((hfirst.add hsecond).add hthird).add hlast
  convert ht using 1
  · funext n
    unfold test_derivativeSlack
    dsimp only [rhoU, L]
    ring
  · norm_num

lemma test_tendsto_derivativeTotalSlack (gap M : ℝ) :
    Tendsto (fun n : ℕ ↦ test_derivativeTotalSlack n gap M)
      atTop (𝓝 0) := by
  have hedge := test_tendsto_derivativeEdge
  have habs : Tendsto (fun n : ℕ ↦
      |Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) - 1|)
      atTop (𝓝 0) := by
    simpa using (hedge.sub_const 1).abs
  have hfirst := habs.const_mul
    (Real.pi * localDensityUpper gap M)
  have hsecond := (test_tendsto_derivativeSlack gap M).mul hedge
  convert hfirst.add hsecond using 1
  · funext n
    rfl
  · norm_num

lemma test_ceil_normalized_le
    {E logR safety nR radius C : ℝ}
    (hlog : 0 < logR) (hn : 0 < nR) (hradius : 0 < radius)
    (hE : 0 ≤ E) (hsafety : 0 ≤ safety)
    (hC : E / (nR * radius * logR) ≤ C) :
    (((⌈E / logR + safety⌉₊ + 1 : ℕ) : ℝ) /
        (nR * radius)) ≤
      C + (safety + 2) / (nR * radius) := by
  have hx : 0 ≤ E / logR + safety :=
    add_nonneg (div_nonneg hE hlog.le) hsafety
  have hceil : (⌈E / logR + safety⌉₊ : ℝ) < E / logR + safety + 1 :=
    Nat.ceil_lt_add_one hx
  have hcast : ((⌈E / logR + safety⌉₊ + 1 : ℕ) : ℝ) ≤
      E / logR + safety + 2 := by
    norm_num at hceil ⊢
    linarith
  have hden : 0 < nR * radius := mul_pos hn hradius
  calc
    ((⌈E / logR + safety⌉₊ + 1 : ℕ) : ℝ) / (nR * radius) ≤
        (E / logR + safety + 2) / (nR * radius) :=
      div_le_div_of_nonneg_right hcast hden.le
    _ = E / (nR * radius * logR) +
        (safety + 2) / (nR * radius) := by
      field_simp [hlog.ne', hn.ne', hradius.ne']
      ring
    _ ≤ C + (safety + 2) / (nR * radius) :=
      add_le_add hC le_rfl

lemma test_derivativeCutoff_normalized_le
    {n : ℕ} (hn2 : 2 ≤ n) {rho gap M : ℝ}
    (hgap : 0 < gap) (hM : 0 ≤ M) (hrho0 : 0 ≤ rho)
    (hrhoU : rho ≤ localDensityUpper gap M)
    (hetaLower : test_logScale n ^ 3 / (2 * (n : ℝ)) ≤
      test_derivativeHeight n)
    (hetaUpper : test_derivativeHeight n ≤ (test_logScale n ^ 5)⁻¹) :
    (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) /
        ((n : ℝ) * test_derivativeRadius n)) ≤
      Real.pi * rho + test_derivativeSlack n gap M := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let q := test_logScale n
  let radius := test_derivativeRadius n
  let eta := test_derivativeHeight n
  let r := test_derivativeBase n
  let H := test_derivativeHeightRatio n
  let L := test_densityLipschitzConstant gap M
  let rhoU := localDensityUpper gap M
  let U := uniformAffineError n eta gap M
  let E := test_derivativeExponent n rho gap M
  have hq : 0 < q := by
    dsimp only [q, test_logScale]
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hradius : 0 < radius := by
    dsimp only [radius, test_derivativeRadius]
    positivity
  have hr : 1 < r := by
    dsimp only [r, test_derivativeBase]
    linarith [one_div_pos.mpr hq]
  have hlog : 0 < Real.log r := Real.log_pos hr
  have heta : 0 < eta := by
    dsimp only [eta, test_derivativeHeight, test_derivativeRadius,
      test_derivativeBase]
    have hb0 : 0 < 1 + 1 / q := by positivity
    have hb1 : 1 < 1 + 1 / q := by linarith [one_div_pos.mpr hq]
    have hd : 0 < (1 + 1 / q) - (1 + 1 / q)⁻¹ := by
      rw [sub_pos]
      exact ((inv_lt_one₀ hb0).2 hb1).trans hb1
    positivity
  have hH : 0 ≤ H := by
    dsimp only [H, test_derivativeHeightRatio]
    exact div_nonneg heta.le (mul_nonneg hradius.le hlog.le)
  have hL : 0 ≤ L := by
    exact test_densityLipschitzConstant_nonneg hgap.le M
  have hrhoUNonneg : 0 ≤ rhoU := by
    exact localDensityUpper_nonneg gap M
  have hwindow : 0 ≤ test_maxRadius n + test_derivativeHoriz n := by
    have hmax : 0 ≤ test_maxRadius n := by
      unfold test_maxRadius
      positivity
    have hhoriz : 0 ≤ test_derivativeHoriz n := by
      unfold test_derivativeHoriz
      exact div_nonneg
        (mul_nonneg hradius.le
          (add_nonneg (zero_lt_one.trans hr).le
            (inv_nonneg.mpr (zero_lt_one.trans hr).le))) (by norm_num)
    positivity
  have hU : 0 ≤ U := by
    exact uniformAffineError_nonneg hn heta hM
  have hE : 0 ≤ E := by
    dsimp only [E, test_derivativeExponent, eta, U, L]
    exact mul_nonneg (Nat.cast_nonneg n)
      (add_nonneg
        (mul_nonneg
          (mul_nonneg Real.pi_pos.le heta.le)
          (add_nonneg hrho0 (mul_nonneg hL hwindow))) hU)
  have hmajor := test_affineRatio_le_majorant (n := n) (Q := 2)
    (gap := gap) hn2 (by norm_num) hM heta hetaLower hetaUpper
  have hUratio0 : 0 ≤ U / (Real.pi * eta) := by positivity
  have hUratio : U / (Real.pi * eta) ≤ test_affineRatioMajorant n 2 gap M := by
    have hsmoothed : test_smoothedDensityError n eta gap M = 9 * U := rfl
    rw [hsmoothed] at hmajor
    have hnine : U / (Real.pi * eta) ≤ 9 * U / (Real.pi * eta) := by
      have := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 9) hUratio0
      calc
        U / (Real.pi * eta) = 1 * (U / (Real.pi * eta)) := by ring
        _ ≤ 9 * (U / (Real.pi * eta)) := this
        _ = 9 * U / (Real.pi * eta) := by ring
    exact hnine.trans hmajor
  have hUscaled : U / (radius * Real.log r) ≤
      Real.pi * H * test_affineRatioMajorant n 2 gap M := by
    have hfactor0 : 0 ≤ Real.pi * H := mul_nonneg Real.pi_pos.le hH
    have hmul := mul_le_mul_of_nonneg_left hUratio hfactor0
    have heq : U / (radius * Real.log r) =
        (Real.pi * H) * (U / (Real.pi * eta)) := by
      dsimp only [H, test_derivativeHeightRatio, eta, radius, r]
      field_simp [Real.pi_ne_zero,
        (show test_derivativeHeight n ≠ 0 by exact heta.ne'),
        hradius.ne', hlog.ne']
    rw [heq]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hHr : H * rho ≤ rho + |H - 1| * rhoU := by
    have hfirst : (H - 1) * rho ≤ |H - 1| * rho :=
      mul_le_mul_of_nonneg_right (le_abs_self (H - 1)) hrho0
    have hsecond : |H - 1| * rho ≤ |H - 1| * rhoU :=
      mul_le_mul_of_nonneg_left hrhoU (abs_nonneg _)
    calc
      H * rho = rho + (H - 1) * rho := by ring
      _ ≤ rho + |H - 1| * rho := add_le_add le_rfl hfirst
      _ ≤ rho + |H - 1| * rhoU := add_le_add le_rfl hsecond
  have hbase : E / ((n : ℝ) * radius * Real.log r) ≤
      Real.pi * rho +
        (Real.pi * |H - 1| * rhoU +
          Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) +
          Real.pi * H * test_affineRatioMajorant n 2 gap M) := by
    have hpi := mul_le_mul_of_nonneg_left hHr Real.pi_pos.le
    have hpi' :
        Real.pi * (H * rho) +
            Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) ≤
          Real.pi * (rho + |H - 1| * rhoU) +
            Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) :=
      add_le_add hpi le_rfl
    have hsum := add_le_add hpi' hUscaled
    have heq : E / ((n : ℝ) * radius * Real.log r) =
        Real.pi * H *
            (rho + L * (test_maxRadius n + test_derivativeHoriz n)) +
          U / (radius * Real.log r) := by
      dsimp only [E, test_derivativeExponent, H,
        test_derivativeHeightRatio, eta, radius, r, L, U]
      field_simp [hnR.ne', hradius.ne', hlog.ne']
    rw [heq]
    calc
      Real.pi * H * (rho + L *
          (test_maxRadius n + test_derivativeHoriz n)) +
          U / (radius * Real.log r) =
          (Real.pi * (H * rho) +
            Real.pi * H * L *
              (test_maxRadius n + test_derivativeHoriz n)) +
            U / (radius * Real.log r) := by ring
      _ ≤ (Real.pi * (rho + |H - 1| * rhoU) +
            Real.pi * H * L *
              (test_maxRadius n + test_derivativeHoriz n)) +
            Real.pi * H * test_affineRatioMajorant n 2 gap M := hsum
      _ = Real.pi * rho +
          (Real.pi * |H - 1| * rhoU +
            Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) +
            Real.pi * H * test_affineRatioMajorant n 2 gap M) := by ring
  have hceil := test_ceil_normalized_le
    (E := E) (logR := Real.log r) (safety := 8 * q ^ 2)
    (nR := (n : ℝ)) (radius := radius)
    (C := Real.pi * rho +
      (Real.pi * |H - 1| * rhoU +
        Real.pi * H * L * (test_maxRadius n + test_derivativeHoriz n) +
        Real.pi * H * test_affineRatioMajorant n 2 gap M))
    hlog hnR hradius hE (mul_nonneg (by norm_num) (sq_nonneg q)) hbase
  unfold test_derivativeCutoff test_derivativeSlack
  dsimp only [E, q, r, radius, H, rhoU, L] at hceil ⊢
  convert hceil using 1
  ring

lemma test_ellipseFactor_bounds {q : ℝ} (hq : 1 ≤ q) :
    1 / (2 * q) ≤
        ((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2 ∧
      ((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2 ≤ 1 / q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hb : 0 < 1 + 1 / q := by positivity
  constructor
  · rw [show ((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2 =
        (2 * q + 1) / (2 * q * (q + 1)) by
      field_simp [hq0.ne', hb.ne']
      ring]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * q)
      (by positivity : 0 < 2 * q * (q + 1))).2
    nlinarith [sq_nonneg q]
  · rw [show ((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2 =
        (2 * q + 1) / (2 * q * (q + 1)) by
      field_simp [hq0.ne', hb.ne']
      ring]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * q * (q + 1)) hq0).2
    nlinarith [sq_nonneg q]

lemma test_derivativeHeight_bounds {n : ℕ} (hn : 0 < n)
    (hq : 1 ≤ test_logScale n)
    (hq8 : test_logScale n ^ 8 ≤ (n : ℝ)) :
    test_logScale n ^ 3 / (2 * (n : ℝ)) ≤ test_derivativeHeight n ∧
      test_derivativeHeight n ≤ (test_logScale n ^ 5)⁻¹ := by
  let q := test_logScale n
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hfLower, hfUpper⟩ := test_ellipseFactor_bounds hq
  have hrad : test_derivativeRadius n = q⁻¹ ^ 4 := by
    dsimp only [q, test_derivativeRadius]
    rw [inv_pow]
  have hheight : test_derivativeHeight n =
      test_derivativeRadius n *
        (((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2) := by
    unfold test_derivativeHeight test_derivativeBase
    dsimp only [q]
    ring
  constructor
  · rw [hheight]
    have hmul := mul_le_mul_of_nonneg_left hfLower
      (show 0 ≤ test_derivativeRadius n by
        unfold test_derivativeRadius
        positivity)
    calc
      q ^ 3 / (2 * (n : ℝ)) ≤ q ^ 3 / (2 * q ^ 8) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith
      _ = q⁻¹ ^ 4 * (1 / (2 * q)) := by
        field_simp [hq0.ne']
      _ = test_derivativeRadius n * (1 / (2 * q)) := by rw [hrad]
      _ ≤ test_derivativeRadius n *
          (((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2) := hmul
  · rw [hheight]
    calc
      test_derivativeRadius n *
          (((1 + 1 / q) - (1 + 1 / q)⁻¹) / 2) ≤
          test_derivativeRadius n * (1 / q) :=
        mul_le_mul_of_nonneg_left hfUpper (by
          unfold test_derivativeRadius
          positivity)
      _ = (test_logScale n ^ 5)⁻¹ := by
        rw [hrad]
        dsimp only [q]
        field_simp [hq0.ne']

lemma test_eventually_derivative_scalar_controls
    {gap M delta : ℝ} (hgap : 0 < gap) (hM : 0 ≤ M)
    (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ rho : ℝ,
      0 ≤ rho → rho ≤ localDensityUpper gap M →
      test_derivativeCutoff n rho gap M ≤ n ∧
      (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) *
          Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)) /
          test_derivativeRadius n ≤
        (n : ℝ) * (Real.pi * rho + 3 * delta / 4) ∧
      6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 *
                Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ (n : ℝ) * delta / 4 := by
  let rhoU := localDensityUpper gap M
  have htotal :=
    (test_tendsto_derivativeTotalSlack gap M).eventually_lt_const
      (by linarith : 0 < 3 * delta / 4)
  have hqLarge := test_tendsto_logScale.eventually (eventually_ge_atTop 1)
  have hq8small := (test_tendsto_logScale_pow_div_nat 8).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  have hq5lim : Tendsto
      (fun n : ℕ => 48 * (test_logScale n ^ 5 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (test_tendsto_logScale_pow_div_nat 5).const_mul 48
  have hq5small := hq5lim.eventually_lt_const hdelta
  have hradLim : Tendsto test_derivativeRadius atTop (𝓝 0) := by
    have hi := test_tendsto_inv_logScale
    convert hi.pow 4 using 1
    · funext n
      simp only [test_derivativeRadius, inv_pow]
    · ring_nf
  have hradProductLim : Tendsto
      (fun n : ℕ => (Real.pi * rhoU + 3 * delta / 4) *
        test_derivativeRadius n) atTop (𝓝 0) := by
    simpa using hradLim.const_mul (Real.pi * rhoU + 3 * delta / 4)
  have hradSmall := hradProductLim.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [htotal, hqLarge, hq8small, hq5small, hradSmall,
      eventually_ge_atTop 2] with n htotal hqLarge hq8small hq5small
      hradSmall hn2
  intro rho hrho0 hrhoU
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < test_logScale n := zero_lt_one.trans_le hqLarge
  have hradius : 0 < test_derivativeRadius n := by
    unfold test_derivativeRadius
    positivity
  have hq8 : test_logScale n ^ 8 ≤ (n : ℝ) := by
    have h := hq8small.le
    rw [div_le_one hnR] at h
    exact h
  obtain ⟨hetaLower, hetaUpper⟩ :=
    test_derivativeHeight_bounds hn hqLarge hq8
  have hnorm := test_derivativeCutoff_normalized_le hn2 hgap hM
    hrho0 hrhoU hetaLower hetaUpper
  let edge := Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)
  have hedge0 : 0 < edge := Real.exp_pos _
  have hedge1 : 1 ≤ edge := by
    dsimp only [edge]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (sq_nonneg _) hradius.le)
  have hslack :
      (Real.pi * rho + test_derivativeSlack n gap M) * edge ≤
        Real.pi * rho + test_derivativeTotalSlack n gap M := by
    have hrhoTerm : Real.pi * rho * (edge - 1) ≤
        Real.pi * rhoU * |edge - 1| := by
      have hedgeDiff : 0 ≤ edge - 1 := sub_nonneg.mpr hedge1
      calc
        Real.pi * rho * (edge - 1) ≤ Real.pi * rhoU * (edge - 1) := by
          gcongr
        _ ≤ Real.pi * rhoU * |edge - 1| := by
          rw [abs_of_nonneg hedgeDiff]
    unfold test_derivativeTotalSlack
    dsimp only [edge, rhoU] at hrhoTerm ⊢
    calc
      (Real.pi * rho + test_derivativeSlack n gap M) *
          Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) =
          Real.pi * rho +
            Real.pi * rho *
              (Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) - 1) +
            test_derivativeSlack n gap M *
              Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) := by ring
      _ ≤ Real.pi * rho +
          Real.pi * localDensityUpper gap M *
            |Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) - 1| +
          test_derivativeSlack n gap M *
            Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) := by
        linarith
      _ = Real.pi * rho +
          (Real.pi * localDensityUpper gap M *
              |Real.exp (test_logScale n ^ 2 * test_derivativeRadius n) - 1| +
            test_derivativeSlack n gap M *
              Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)) := by ring
  have hmain :
      (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) * edge) /
          test_derivativeRadius n ≤
        (n : ℝ) * (Real.pi * rho + 3 * delta / 4) := by
    have hscaled := mul_le_mul_of_nonneg_right hnorm hedge0.le
    have hcore := hscaled.trans hslack
    have hcore' :
        (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) /
            ((n : ℝ) * test_derivativeRadius n)) * edge ≤
          Real.pi * rho + 3 * delta / 4 :=
      hcore.trans (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hcore' hnR.le
    calc
      ((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) * edge /
          test_derivativeRadius n =
          (n : ℝ) *
            ((((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) /
              ((n : ℝ) * test_derivativeRadius n)) * edge) := by
        field_simp [hnR.ne', hradius.ne']
      _ ≤ (n : ℝ) * (Real.pi * rho + 3 * delta / 4) := hmul
  have hmle : test_derivativeCutoff n rho gap M ≤ n := by
    have hedgeLower :
        (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) /
            test_derivativeRadius n) ≤
          (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) * edge) /
            test_derivativeRadius n := by
      have hcast0 : 0 ≤
          ((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hedge1 hcast0
      exact (div_le_div_of_nonneg_right (by simpa using hmul) hradius.le)
    have hupper := hedgeLower.trans hmain
    have hC : Real.pi * rho + 3 * delta / 4 ≤
        Real.pi * rhoU + 3 * delta / 4 := by
      gcongr
    have hupper' := hupper.trans
      (mul_le_mul_of_nonneg_left hC hnR.le)
    have hradC : test_derivativeRadius n *
        (Real.pi * rhoU + 3 * delta / 4) ≤ 1 := by
      simpa [mul_comm] using hradSmall.le
    have hcast :
        ((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      calc
        ((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) =
            (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) /
              test_derivativeRadius n) * test_derivativeRadius n := by
          field_simp [hradius.ne']
        _ ≤ (n : ℝ) * (Real.pi * rhoU + 3 * delta / 4) *
              test_derivativeRadius n :=
          mul_le_mul_of_nonneg_right hupper' hradius.le
        _ = (n : ℝ) * (test_derivativeRadius n *
              (Real.pi * rhoU + 3 * delta / 4)) := by ring
        _ ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hradC hnR.le
        _ = (n : ℝ) := by ring
    have hcastNat : test_derivativeCutoff n rho gap M + 1 ≤ n := by
      exact_mod_cast hcast
    omega
  have hlogLower : 1 / (2 * test_logScale n) ≤
      Real.log (test_derivativeBase n) := by
    have hraw := Real.le_log_one_add_of_nonneg
      (show 0 ≤ 1 / test_logScale n by positivity)
    unfold test_derivativeBase
    calc
      1 / (2 * test_logScale n) ≤
          2 * (1 / test_logScale n) /
            (1 / test_logScale n + 2) := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * test_logScale n)
          (by positivity : 0 < 1 / test_logScale n + 2)).2
        field_simp [hq.ne']
        nlinarith
      _ ≤ Real.log (1 + 1 / test_logScale n) := hraw
  have hexponent : test_logScale n -
      8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n) ≤
        -3 * test_logScale n := by
    have hmul := mul_le_mul_of_nonneg_left hlogLower
      (show 0 ≤ (8 : ℝ) * test_logScale n ^ 2 by positivity)
    have hfour : 4 * test_logScale n ≤
        8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n) := by
      calc
        4 * test_logScale n =
            8 * test_logScale n ^ 2 * (1 / (2 * test_logScale n)) := by
          field_simp [hq.ne']
          ring
        _ ≤ 8 * test_logScale n ^ 2 *
            Real.log (test_derivativeBase n) := hmul
    linarith
  have hexp : Real.exp (test_logScale n -
      8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n)) ≤
        ((n : ℝ) ^ 3)⁻¹ := by
    have h := Real.exp_le_exp.mpr hexponent
    calc
      Real.exp (test_logScale n -
          8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n)) ≤
          Real.exp (-3 * test_logScale n) := h
      _ = ((n : ℝ) ^ 3)⁻¹ := by
        unfold test_logScale
        rw [show -3 * Real.log (n : ℝ) =
          -(Real.log ((n : ℝ) ^ 3)) by rw [Real.log_pow]; norm_num]
        rw [Real.exp_neg, Real.exp_log]
        positivity
  have htail :
      6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 *
                Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ (n : ℝ) * delta / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hexp
      (by positivity : 0 ≤ 6 * (n : ℝ) ^ 2 *
        (2 * (n : ℝ) * test_logScale n))
    have hpre : 6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ 12 * test_logScale n ^ 5 := by
      calc
        6 * (n : ℝ) ^ 2 *
              (2 * (n : ℝ) * test_logScale n *
                Real.exp (test_logScale n -
                  8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n))) /
              test_derivativeRadius n =
            (6 * (n : ℝ) ^ 2 * (2 * (n : ℝ) * test_logScale n)) *
              Real.exp (test_logScale n -
                8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n)) /
              test_derivativeRadius n := by ring
        _ ≤ (6 * (n : ℝ) ^ 2 * (2 * (n : ℝ) * test_logScale n)) *
              ((n : ℝ) ^ 3)⁻¹ / test_derivativeRadius n :=
          div_le_div_of_nonneg_right hmul hradius.le
        _ = 12 * test_logScale n ^ 5 := by
          unfold test_derivativeRadius
          field_simp [hnR.ne', hq.ne']
          ring
    calc
      6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ 12 * test_logScale n ^ 5 := hpre
      _ ≤ (n : ℝ) * delta / 4 := by
        have := hq5small.le
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
        calc
          12 * test_logScale n ^ 5 * 4 = 48 * test_logScale n ^ 5 := by ring
          _ ≤ (n : ℝ) * delta := by
            have hdiv : (48 * test_logScale n ^ 5) / (n : ℝ) ≤ delta := by
              calc
                (48 * test_logScale n ^ 5) / (n : ℝ) =
                    48 * (test_logScale n ^ 5 / (n : ℝ)) := by ring
                _ ≤ delta := this
            simpa [mul_comm] using (div_le_iff₀ hnR).mp hdiv
  exact ⟨hmle, by simpa only [edge] using hmain, htail⟩

/-! ### Geometric-shell asymptotics used in the final assembly -/

lemma test_shellRatio_gt_one {Q : ℕ} (hQ : 0 < Q) :
    1 < test_shellRatio Q := by
  unfold test_shellRatio
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  linarith [one_div_pos.mpr hQR]

lemma test_tendsto_shellSteps_div_logScale (Q : ℕ) :
    Tendsto (fun n : ℕ =>
      (test_shellSteps Q n : ℝ) / test_logScale n) atTop (𝓝 (Q : ℝ)) := by
  have hqpos := test_tendsto_logScale.eventually (eventually_gt_atTop 0)
  have hrangeRatio := test_tendsto_logRange_div_logScale
  have hrangePos : ∀ᶠ n : ℕ in atTop, 0 ≤ test_logRange n := by
    have hhalf := hrangeRatio.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [hqpos, hhalf] with n hq hhalf
    have : 0 < test_logRange n / test_logScale n := by linarith
    rcases div_pos_iff.mp this with hpos | hneg
    · exact hpos.1.le
    · linarith [hneg.2, hq]
  let err : ℕ → ℝ := fun n =>
    ((Q : ℝ) * test_logRange n - (test_shellSteps Q n : ℝ)) /
      test_logScale n
  have herr0 : Tendsto err atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ test_tendsto_inv_logScale
    · filter_upwards [hqpos, hrangePos] with n hq hrange
      apply div_nonneg _ hq.le
      exact sub_nonneg.mpr (by
        unfold test_shellSteps
        exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) hrange))
    · filter_upwards [hqpos, hrangePos] with n hq hrange
      change err n ≤ (test_logScale n)⁻¹
      dsimp only [err]
      rw [inv_eq_one_div]
      have hfloor := Nat.lt_floor_add_one ((Q : ℝ) * test_logRange n)
      have hnum : (Q : ℝ) * test_logRange n -
          (test_shellSteps Q n : ℝ) ≤ 1 := by
        unfold test_shellSteps
        linarith
      exact div_le_div_of_nonneg_right hnum hq.le
  have hmain : Tendsto (fun n : ℕ =>
      (Q : ℝ) * (test_logRange n / test_logScale n))
      atTop (𝓝 ((Q : ℝ) * 1)) := hrangeRatio.const_mul (Q : ℝ)
  have hsub := hmain.sub herr0
  convert hsub using 1
  · funext n
    dsimp only [err]
    by_cases hq : test_logScale n = 0
    · simp [hq]
    · field_simp [hq]
      ring
  · ring_nf

lemma test_shell_terminal_le_maxRadius {Q n : ℕ}
    (hQ : 0 < Q) (hn : 0 < n) (hq : 0 < test_logScale n)
    (hrange : 0 ≤ test_logRange n) :
    test_minRadius n * test_shellRatio Q ^ test_shellSteps Q n ≤
      test_maxRadius n := by
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hr : 1 < test_shellRatio Q := test_shellRatio_gt_one hQ
  have hr0 : 0 < test_shellRatio Q := zero_lt_one.trans hr
  have hlog : Real.log (test_shellRatio Q) ≤ 1 / (Q : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hr0
    unfold test_shellRatio at h ⊢
    linarith
  have hsteps : (test_shellSteps Q n : ℝ) ≤
      (Q : ℝ) * test_logRange n := by
    unfold test_shellSteps
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) hrange)
  have hexponent : (test_shellSteps Q n : ℝ) *
      Real.log (test_shellRatio Q) ≤ test_logRange n := by
    calc
      (test_shellSteps Q n : ℝ) * Real.log (test_shellRatio Q) ≤
          ((Q : ℝ) * test_logRange n) * (1 / (Q : ℝ)) := by
        exact mul_le_mul hsteps hlog (Real.log_nonneg hr.le)
          (mul_nonneg (Nat.cast_nonneg Q) hrange)
      _ = test_logRange n := by field_simp [hQR.ne']
  have hpow : test_shellRatio Q ^ test_shellSteps Q n ≤
      Real.exp (test_logRange n) := by
    calc
      test_shellRatio Q ^ test_shellSteps Q n =
          Real.exp ((test_shellSteps Q n : ℝ) *
            Real.log (test_shellRatio Q)) := by
        rw [Real.exp_nat_mul, Real.exp_log hr0]
      _ ≤ Real.exp (test_logRange n) := Real.exp_le_exp.mpr hexponent
  have hmul := mul_le_mul_of_nonneg_left hpow (by
    unfold test_minRadius
    positivity : 0 ≤ test_minRadius n)
  calc
    test_minRadius n * test_shellRatio Q ^ test_shellSteps Q n ≤
        test_minRadius n * Real.exp (test_logRange n) := hmul
    _ = test_maxRadius n := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      unfold test_minRadius test_maxRadius test_logRange test_logScale
      rw [Real.exp_sub, Real.exp_log hnR]
      rw [show Real.exp (8 * Real.log (Real.log (n : ℝ))) =
          Real.log (n : ℝ) ^ 8 by
        rw [show 8 * Real.log (Real.log (n : ℝ)) =
            (8 : ℕ) * Real.log (Real.log (n : ℝ)) by norm_num,
          Real.exp_nat_mul]
        congr 1
        exact Real.exp_log hq]
      field_simp [hnR.ne', hq.ne']

lemma test_tendsto_shell_gain (Q : ℕ) :
    Tendsto (fun n : ℕ =>
      (1 + (test_shellSteps Q n : ℝ) *
        (1 - 1 / test_shellRatio Q)) / test_logScale n)
      atTop (𝓝 ((Q : ℝ) / ((Q : ℝ) + 1))) := by
  by_cases hQnat : Q = 0
  · subst Q
    simpa [test_shellSteps, test_shellRatio] using test_tendsto_inv_logScale
  have hsteps := test_tendsto_shellSteps_div_logScale Q
  have hone := test_tendsto_inv_logScale
  have hcoef : 1 - 1 / test_shellRatio Q = 1 / ((Q : ℝ) + 1) := by
    unfold test_shellRatio
    have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast hQnat
    field_simp [hQ]
    ring
  have ht := hone.add (hsteps.const_mul (1 / ((Q : ℝ) + 1)))
  convert ht using 1
  · funext n
    rw [hcoef]
    by_cases hq : test_logScale n = 0
    · simp [hq]
    · field_simp [hq]
  · ring_nf

lemma test_tendsto_shell_edge :
    Tendsto (fun n : ℕ => Real.exp (-(test_logScale n)⁻¹))
      atTop (𝓝 1) := by
  have ht := Real.continuous_exp.continuousAt.tendsto.comp
    test_tendsto_inv_logScale.neg
  convert ht using 1 <;> simp [Function.comp_def]

lemma test_tendsto_density_parameter {rho0 : ℝ} (hrho0 : 0 < rho0) :
    Tendsto (fun k : ℕ =>
      2 * (rho0 - ((k : ℝ))⁻¹) /
        (Real.pi * rho0 + ((k : ℝ))⁻¹))
      atTop (𝓝 (2 / Real.pi)) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hrho : Tendsto (fun _ : ℕ => rho0) atTop (𝓝 rho0) := tendsto_const_nhds
  have hpirho : Tendsto (fun _ : ℕ => Real.pi * rho0)
      atTop (𝓝 (Real.pi * rho0)) := tendsto_const_nhds
  have hnum := (hrho.sub hi).const_mul 2
  have hden := hpirho.add hi
  have hden0 : Real.pi * rho0 + 0 ≠ 0 := by positivity
  have ht := hnum.div hden hden0
  have hlim : 2 * (rho0 - 0) / (Real.pi * rho0 + 0) =
      2 / Real.pi := by
    field_simp [hrho0.ne', Real.pi_ne_zero]
    ring
  rw [hlim] at ht
  change Tendsto (fun k : ℕ =>
    2 * (rho0 - ((k : ℝ))⁻¹) /
      (Real.pi * rho0 + ((k : ℝ))⁻¹)) atTop (𝓝 (2 / Real.pi)) at ht
  exact ht

lemma test_tendsto_scaled_nat_ratio {L : ℕ} (hL : 0 < L) :
    Tendsto (fun k : ℕ =>
      (((L * k : ℕ) : ℝ) / (((L * k : ℕ) : ℝ) + 1)))
      atTop (𝓝 1) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hconst : Tendsto (fun _ : ℕ => (L : ℝ)) atTop (𝓝 (L : ℝ)) :=
    tendsto_const_nhds
  have ht := hconst.div (hconst.add hi) (by simpa using hLR)
  have hlim : (L : ℝ) / ((L : ℝ) + 0) = 1 := by
    field_simp [hLR]
    ring
  rw [hlim] at ht
  change Tendsto (fun k : ℕ =>
    (L : ℝ) / ((L : ℝ) + ((k : ℝ))⁻¹)) atTop (𝓝 1) at ht
  have hkpos : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  apply ht.congr'
  filter_upwards [hkpos] with k hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  change (L : ℝ) / ((L : ℝ) + ((k : ℝ))⁻¹) =
    ((L * k : ℕ) : ℝ) / (((L * k : ℕ) : ℝ) + 1)
  push_cast
  field_simp [hkR, hLR]

lemma test_exists_shell_parameters {rho0 rhoU epsilon : ℝ}
    (hrho0 : 0 < rho0) (hrhoU : 0 ≤ rhoU) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, ∃ delta : ℝ,
      2 ≤ Q ∧ 0 < delta ∧ delta < rho0 ∧
      2 * rhoU / (Q : ℝ) ≤ delta / 4 ∧
      2 / Real.pi - epsilon / 2 <
        (2 * (rho0 - delta) / (Real.pi * rho0 + delta)) *
          ((Q : ℝ) / ((Q : ℝ) + 1)) := by
  obtain ⟨L, hL⟩ := exists_nat_ge (max 1 (8 * rhoU))
  have hLone : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hLrho : 8 * rhoU ≤ (L : ℝ) := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := zero_lt_one.trans_le hLone
    exact_mod_cast this
  have hproduct := (test_tendsto_density_parameter hrho0).mul
    (test_tendsto_scaled_nat_ratio hLpos)
  have hlimit : (2 / Real.pi) * 1 = 2 / Real.pi := by ring
  rw [hlimit] at hproduct
  have htarget := hproduct.eventually_const_lt
    (by linarith : 2 / Real.pi - epsilon / 2 < 2 / Real.pi)
  have hi : Tendsto (fun k : ℕ => ((k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hdeltaSmall := hi.eventually_lt_const hrho0
  have hevent : ∀ᶠ k : ℕ in atTop,
      (2 * (rho0 - ((k : ℝ))⁻¹) /
          (Real.pi * rho0 + ((k : ℝ))⁻¹)) *
            ((((L * k : ℕ) : ℝ) / (((L * k : ℕ) : ℝ) + 1))) >
          2 / Real.pi - epsilon / 2 ∧
        ((k : ℝ))⁻¹ < rho0 ∧ 2 ≤ k := by
    filter_upwards [htarget, hdeltaSmall, eventually_ge_atTop 2] with
        k htarget hdeltaSmall hk2
    exact ⟨htarget, hdeltaSmall, hk2⟩
  obtain ⟨k, htarget, hdeltaSmall, hk2⟩ := hevent.exists
  let Q : ℕ := L * k
  let delta : ℝ := ((k : ℝ))⁻¹
  have hkpos : 0 < k := by omega
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hQ2 : 2 ≤ Q := by
    dsimp only [Q]
    calc
      2 ≤ k := hk2
      _ = 1 * k := (Nat.one_mul k).symm
      _ ≤ L * k := Nat.mul_le_mul_right k (show 1 ≤ L by omega)
  have hQposNat : 0 < Q := Nat.zero_lt_two.trans_le hQ2
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQposNat
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hQloss : 2 * rhoU / (Q : ℝ) ≤ delta / 4 := by
    dsimp only [Q, delta]
    push_cast
    rw [inv_eq_one_div, div_div]
    apply (div_le_div_iff₀
      (mul_pos (by exact_mod_cast hLpos) hkR)
      (mul_pos hkR (by norm_num : (0 : ℝ) < 4))).2
    have hmul := mul_le_mul_of_nonneg_right hLrho hkR.le
    nlinarith
  refine ⟨Q, delta, hQ2, hdelta, ?_, hQloss, ?_⟩
  · simpa only [delta] using hdeltaSmall
  · simpa only [Q, delta] using htarget

lemma test_density_ratio_mono {rho0 rho delta : ℝ}
    (hrho0 : 0 < rho0) (hdelta : 0 < delta) (hdeltarho : delta < rho0)
    (hrho : rho0 ≤ rho) :
    2 * (rho0 - delta) / (Real.pi * rho0 + delta) ≤
      2 * (rho - delta) / (Real.pi * rho + delta) := by
  have hden0 : 0 < Real.pi * rho0 + delta := by positivity
  have hrhopos : 0 < rho := hrho0.trans_le hrho
  have hden : 0 < Real.pi * rho + delta := by positivity
  apply (div_le_div_iff₀ hden0 hden).2
  rw [show
    2 * (rho - delta) * (Real.pi * rho0 + delta) =
      2 * (rho0 - delta) * (Real.pi * rho + delta) +
        2 * delta * (Real.pi + 1) * (rho - rho0) by ring]
  exact le_add_of_nonneg_right
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hdelta.le)
        (by positivity : 0 ≤ Real.pi + 1))
      (sub_nonneg.mpr hrho))

lemma test_eventually_exp_localization_small {h : ℝ} (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ 2 / h *
          Real.exp (-test_logScale n ^ 2 * h) < 1 := by
  have hqLarge := test_tendsto_logScale.eventually
    (eventually_ge_atTop (3 / h))
  have hnLarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (4 / h))
  filter_upwards [hqLarge, hnLarge, eventually_ge_atTop 2] with
      n hqLarge hnLarge hn2
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < test_logScale n := by
    unfold test_logScale
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hhq : 3 ≤ h * test_logScale n := by
    have := mul_le_mul_of_nonneg_left hqLarge hh.le
    field_simp [hh.ne'] at this
    linarith
  have hexponent : -test_logScale n ^ 2 * h ≤
      -3 * test_logScale n := by
    have hmul := mul_le_mul_of_nonneg_right hhq hq.le
    nlinarith
  have hexp : Real.exp (-test_logScale n ^ 2 * h) ≤
      ((n : ℝ) ^ 3)⁻¹ := by
    calc
      Real.exp (-test_logScale n ^ 2 * h) ≤
          Real.exp (-3 * test_logScale n) := Real.exp_le_exp.mpr hexponent
      _ = ((n : ℝ) ^ 3)⁻¹ := by
        unfold test_logScale
        rw [show -3 * Real.log (n : ℝ) =
          -(Real.log ((n : ℝ) ^ 3)) by rw [Real.log_pow]; norm_num]
        rw [Real.exp_neg, Real.exp_log]
        positivity
  have hmul := mul_le_mul_of_nonneg_left hexp
    (by positivity : 0 ≤ 4 * (n : ℝ) ^ 2 / h)
  calc
    4 * (n : ℝ) ^ 2 / h * Real.exp (-test_logScale n ^ 2 * h) ≤
        4 * (n : ℝ) ^ 2 / h * ((n : ℝ) ^ 3)⁻¹ := hmul
    _ = 4 / (h * (n : ℝ)) := by field_simp [hh.ne', hnR.ne']
    _ < 1 := by
      rw [div_lt_one (mul_pos hh hnR)]
      have hmulLarge := mul_lt_mul_of_pos_left hnLarge hh
      field_simp [hh.ne'] at hmulLarge
      linarith

lemma test_amplitudeMaximizer_near_anchor {n : ℕ}
    (hn2 : 2 ≤ n) (X : NodeConfiguration n)
    {a b x h rate : ℝ} (hab : a ≤ b) (hh : 0 < h)
    (hrate : 0 < rate) (ha0 : -1 ≤ a) (hb0 : b ≤ 1)
    (ha : -1 ≤ x - h) (hb : x + h ≤ 1)
    (hleft : a ≤ x - h) (hright : x + h ≤ b)
    (hLeb : ∀ v ∈ Set.Icc a b, lebesgueFunction X v ≤ (n : ℝ))
    (hsmall : 4 * (n : ℝ) ^ 2 / h * Real.exp (-rate * h) < 1) :
    |x - amplitudeMaximizer X a b rate x hab| ≤ 2 * h := by
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let z := amplitudeMaximizer X a b rate x hab
  have hlower := amplitude_maximizer_exp_lower hn2 X hab hrate.le hh
    ha0 hb0 ha hb hleft hright hLeb
  by_contra hnear
  have hdist : 2 * h < |x - z| := lt_of_not_ge hnear
  have hexpStrict : Real.exp (-rate * |x - z|) <
      Real.exp (-rate * (2 * h)) := by
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_neg_left hdist (neg_lt_zero.mpr hrate)
  have hchain :
      (h / (4 * (n : ℝ) ^ 2)) * Real.exp (-rate * h) <
        Real.exp (-rate * (2 * h)) := by
    have hlower' :
        (h / (4 * (n : ℝ) ^ 2)) * Real.exp (-rate * h) ≤
          Real.exp (-rate * |x - z|) := by
      simpa only [z] using hlower
    exact hlower'.trans_lt hexpStrict
  have hexpTwo : Real.exp (-rate * (2 * h)) =
      Real.exp (-rate * h) * Real.exp (-rate * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpTwo] at hchain
  have hcancel : h / (4 * (n : ℝ) ^ 2) < Real.exp (-rate * h) := by
    exact (mul_lt_mul_iff_of_pos_right (Real.exp_pos (-rate * h))).mp hchain
  have hcoef : 0 < 4 * (n : ℝ) ^ 2 / h := by positivity
  have hmul := mul_lt_mul_of_pos_left hcancel hcoef
  have hone : (4 * (n : ℝ) ^ 2 / h) *
      (h / (4 * (n : ℝ) ^ 2)) = 1 := by
    field_simp [hh.ne', hnR.ne']
  rw [hone] at hmul
  linarith

lemma test_eventually_geometry_small {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 1 ≤ test_logScale n ∧ 0 ≤ test_logRange n ∧
      test_maxRadius n + test_derivativeHoriz n ≤ d / 16 ∧
      test_maxRadius n + (test_logScale n)⁻¹ ≤ d / 8 := by
  have hi := test_tendsto_inv_logScale
  have hmax : Tendsto test_maxRadius atTop (𝓝 0) := by
    convert hi.pow 3 using 1
    · funext n
      simp only [test_maxRadius, inv_pow]
    · ring_nf
  have hsumDeriv : Tendsto (fun n : ℕ =>
      test_maxRadius n + test_derivativeHoriz n) atTop (𝓝 0) := by
    simpa using hmax.add test_tendsto_derivativeHoriz
  have hsumAnchor : Tendsto (fun n : ℕ =>
      test_maxRadius n + (test_logScale n)⁻¹) atTop (𝓝 0) := by
    simpa using hmax.add hi
  have hderivSmall := hsumDeriv.eventually_lt_const (by positivity : 0 < d / 16)
  have hanchorSmall := hsumAnchor.eventually_lt_const (by positivity : 0 < d / 8)
  have hqLarge := test_tendsto_logScale.eventually (eventually_ge_atTop 1)
  have hrangeRatio := test_tendsto_logRange_div_logScale
  have hhalf := hrangeRatio.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop 2, hqLarge, hhalf, hderivSmall,
      hanchorSmall] with n hn2 hqLarge hhalf hderivSmall hanchorSmall
  have hq : 0 < test_logScale n := zero_lt_one.trans_le hqLarge
  have hrange : 0 ≤ test_logRange n := by
    have hratio : 0 < test_logRange n / test_logScale n := by linarith
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact hpos.1.le
    · linarith [hneg.2, hq]
  exact ⟨hn2, hqLarge, hrange, hderivSmall.le, hanchorSmall.le⟩

lemma test_eventually_shell_scalar {Q : ℕ} {D target : ℝ}
    (hlimit : target < D * ((Q : ℝ) / ((Q : ℝ) + 1))) :
    ∀ᶠ n : ℕ in atTop,
      target < Real.exp (-(test_logScale n)⁻¹) * D *
        ((1 + (test_shellSteps Q n : ℝ) *
          (1 - 1 / test_shellRatio Q)) / test_logScale n) := by
  have ht := test_tendsto_shell_edge.mul
    ((test_tendsto_shell_gain Q).const_mul D)
  have htarget := ht.eventually_const_lt (by simpa [mul_assoc] using hlimit)
  filter_upwards [htarget] with n hn
  simpa only [mul_assoc] using hn

lemma test_shell_derivative_bound {n : ℕ} (hn2 : 2 ≤ n)
    (X : NodeConfiguration n) {a b d gap M delta z rho Rterm : ℝ}
    (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b) (hd : 0 < d)
    (hM : 0 ≤ M) (hnorm : |normalizationLevel X| ≤ M)
    (hLeb : ∀ v ∈ Set.Icc a b, lebesgueFunction X v ≤ (n : ℝ))
    (hgap : 0 < gap) (hgapLe : gap ≤ d / 8) (hdelta : 0 < delta)
    (hqLarge : 1 ≤ test_logScale n)
    (hgeomDeriv : test_maxRadius n + test_derivativeHoriz n ≤ d / 16)
    (hgeomAnchor : test_maxRadius n + (test_logScale n)⁻¹ ≤ d / 8)
    (hzCore : z ∈ Set.Icc (a + 3 * d / 8) (b - 3 * d / 8))
    (hzUnit : |z| ≤ 1)
    (hzSep : ∀ v ∉ Set.Icc a b, gap ≤ |z - v|)
    (hampz : amplitude X a b (test_logScale n ^ 2) z hab.le =
      |(nodalPolynomial X).eval z|)
    (hrhoNonneg : 0 ≤ rho)
    (hterminal : Rterm ≤ test_maxRadius n)
    (hmle : test_derivativeCutoff n rho gap M ≤ n)
    (hmain :
      (((test_derivativeCutoff n rho gap M + 1 : ℕ) : ℝ) *
          Real.exp (test_logScale n ^ 2 * test_derivativeRadius n)) /
          test_derivativeRadius n ≤
        (n : ℝ) * (Real.pi * rho + 3 * delta / 4))
    (htail :
      6 * (n : ℝ) ^ 2 *
          (2 * (n : ℝ) * test_logScale n *
            Real.exp (test_logScale n -
              8 * test_logScale n ^ 2 * Real.log (test_derivativeBase n))) /
          test_derivativeRadius n ≤ (n : ℝ) * delta / 4)
    (hrhoDef : rho = exteriorDensity X (normalizationLevel X) a b z 0) :
    ∀ k, |z - X k| ≤ Rterm →
      |(nodalPolynomial X).derivative.eval (X k)| ≤
        ((n : ℝ) * (Real.pi * rho + delta)) *
          |(nodalPolynomial X).eval z| *
            Real.exp (test_logScale n ^ 2 * |z - X k|) := by
  have hn : 0 < n := by omega
  have hq : 0 < test_logScale n := zero_lt_one.trans_le hqLarge
  have hmaxNonneg : 0 ≤ test_maxRadius n := by
    unfold test_maxRadius
    positivity
  have hhorizNonneg : 0 ≤ test_derivativeHoriz n := by
    unfold test_derivativeHoriz test_derivativeRadius test_derivativeBase
    have hb' : 0 < 1 + 1 / test_logScale n := by positivity
    positivity
  have hradiusLeMax : test_derivativeRadius n ≤ test_maxRadius n := by
    have hiq : 0 ≤ (test_logScale n)⁻¹ := by positivity
    have hiqOne : (test_logScale n)⁻¹ ≤ 1 := (inv_le_one₀ hq).2 hqLarge
    unfold test_derivativeRadius test_maxRadius
    rw [← inv_pow, ← inv_pow]
    calc
      (test_logScale n)⁻¹ ^ 4 =
          (test_logScale n)⁻¹ ^ 3 * (test_logScale n)⁻¹ := by ring
      _ ≤ (test_logScale n)⁻¹ ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left hiqOne (pow_nonneg hiq 3)
      _ = (test_logScale n)⁻¹ ^ 3 := by ring
  intro k hk
  have hkdist : |X k - z| ≤ test_maxRadius n := by
    rw [abs_sub_comm]
    exact hk.trans hterminal
  have hkdistBounds := abs_le.mp hkdist
  have hmaxSmall : test_maxRadius n ≤ d / 16 := by
    linarith [hgeomDeriv, hhorizNonneg]
  have hkLower : a ≤ X k - test_derivativeRadius n := by
    linarith [hzCore.1, hkdistBounds.1, hradiusLeMax]
  have hkUpper : X k + test_derivativeRadius n ≤ b := by
    linarith [hzCore.2, hkdistBounds.2, hradiusLeMax]
  have hkAnchorLower : a ≤ X k - (test_logScale n)⁻¹ := by
    linarith [hzCore.1, hkdistBounds.1, hgeomAnchor]
  have hkAnchorUpper : X k + (test_logScale n)⁻¹ ≤ b := by
    linarith [hzCore.2, hkdistBounds.2, hgeomAnchor]
  have hkRegular : ∀ y,
      |y - X k| ≤ test_derivativeHoriz n →
        |y| ≤ 1 ∧ ∀ v ∉ Set.Icc a b, gap ≤ |y - v| := by
    intro y hy
    have hyz : |y - z| ≤ d / 16 := by
      calc
        |y - z| = |(y - X k) + (X k - z)| := by ring_nf
        _ ≤ |y - X k| + |X k - z| := abs_add_le _ _
        _ ≤ test_derivativeHoriz n + test_maxRadius n := add_le_add hy hkdist
        _ ≤ d / 16 := by simpa [add_comm] using hgeomDeriv
    rw [abs_le] at hyz
    have hyLower : a + 5 * d / 16 ≤ y := by linarith [hzCore.1]
    have hyUpper : y ≤ b - 5 * d / 16 := by linarith [hzCore.2]
    constructor
    · rw [abs_le]
      constructor <;> linarith
    · intro v hv
      have hv' : v < a ∨ b < v := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hv
      rcases hv' with hvleft | hvright
      · rw [abs_of_nonneg (by linarith)]
        linarith [hzCore.1, hgapLe]
      · rw [abs_of_nonpos (by linarith)]
        linarith [hzCore.2, hgapLe]
  have hraw := test_abs_nodal_derivative_le_of_controls hn2 X
    ha hb hab.le hM hnorm hLeb hgap hdelta (by simpa [hrhoDef] using hrhoNonneg)
    hzUnit hzSep hkdist hkLower hkUpper (ha.trans hkAnchorLower)
    (hkAnchorUpper.trans hb) hkAnchorLower hkAnchorUpper hkRegular
    (by simpa [hrhoDef] using hmle) (by simpa [hrhoDef] using hmain)
    (by simpa [hrhoDef] using htail)
  have hamp := amplitude_le_exp_mul_amplitude X hab.le (sq_nonneg (test_logScale n))
    (x := X k) (y := z)
  rw [hampz] at hamp
  have hcoef : 0 ≤ (n : ℝ) * (Real.pi * rho + delta) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hamp hcoef
  have hraw' : |(nodalPolynomial X).derivative.eval (X k)| ≤
      (n : ℝ) * (Real.pi * rho + delta) *
        amplitude X a b (test_logScale n ^ 2) (X k) hab.le := by
    simpa [hrhoDef] using hraw
  exact hraw'.trans (by
    calc
      (n : ℝ) * (Real.pi * rho + delta) *
          amplitude X a b (test_logScale n ^ 2) (X k) hab.le ≤
        (n : ℝ) * (Real.pi * rho + delta) *
          (Real.exp (test_logScale n ^ 2 * |X k - z|) *
            |(nodalPolynomial X).eval z|) := hscaled
      _ = ((n : ℝ) * (Real.pi * rho + delta)) *
          |(nodalPolynomial X).eval z| *
            Real.exp (test_logScale n ^ 2 * |z - X k|) := by
        rw [abs_sub_comm]
        ring)

theorem erdos_1153 : (∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : Erdos1153.NodeConfiguration n,
      ∃ x ∈ Set.Icc a b,
        (2 / Real.pi - ε) * Real.log (n : ℝ) ≤ Erdos1153.lebesgueFunction X x) := by
  intro a b ha hab hb epsilon hepsilon
  let d : ℝ := b - a
  let gap0 : ℝ := d / 4
  let M : ℝ := localNormalizationBound a b
  let rho0 : ℝ := densityTestHeight gap0 M / (10 * Real.pi)
  let gap : ℝ := d / 8
  let S : ℝ := d / 16
  let h : ℝ := d / 16
  have hd : 0 < d := by dsimp only [d]; linarith
  have hgap0 : 0 < gap0 := by dsimp only [gap0]; positivity
  have hgap : 0 < gap := by dsimp only [gap]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  have hh : 0 < h := by dsimp only [h]; positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact localNormalizationBound_nonneg hab
  have hrho0 : 0 < rho0 := by
    dsimp only [rho0]
    exact div_pos (densityTestHeight_pos gap0 M)
      (mul_pos (by norm_num) Real.pi_pos)
  let rhoU : ℝ := localDensityUpper gap M
  have hrhoU : 0 ≤ rhoU := by
    dsimp only [rhoU]
    exact localDensityUpper_nonneg gap M
  obtain ⟨Q, delta, hQ2, hdelta, hdeltarho, hQloss, hparameter⟩ :=
    test_exists_shell_parameters hrho0 hrhoU hepsilon
  let D : ℝ := 2 * (rho0 - delta) / (Real.pi * rho0 + delta)
  have hDpos : 0 < D := by
    dsimp only [D]
    exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hdeltarho)) (by positivity)
  have hscalar := test_eventually_shell_scalar
    (Q := Q) (D := D) (target := 2 / Real.pi - epsilon)
    (by
      dsimp only [D]
      have : 2 / Real.pi - epsilon < 2 / Real.pi - epsilon / 2 := by
        linarith
      exact this.trans hparameter)
  have hboundary := eventually_boundaryDensity_lower ha hab hb
  have hcount := test_eventually_localNodeCount_log_window
    ha hb hM hgap hS hdelta hQ2 (by simpa only [rhoU] using hQloss)
  have hderivScalar := test_eventually_derivative_scalar_controls
    hgap hM hdelta
  have hlocalize := test_eventually_exp_localization_small hh
  have hgeometry := test_eventually_geometry_small hd
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ X : NodeConfiguration n,
      ∃ x ∈ Set.Icc a b,
        (2 / Real.pi - epsilon) * Real.log (n : ℝ) ≤
          lebesgueFunction X x := by
    filter_upwards [hscalar, hboundary, hcount, hderivScalar,
        hlocalize, hgeometry] with n hscalar hboundary hcount
        hderivScalar hlocalize hgeometry
    rcases hgeometry with ⟨hn2, hqLarge, hrange, hgeomDeriv, hgeomAnchor⟩
    have hn : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hq : 0 < test_logScale n := zero_lt_one.trans_le hqLarge
    have hq0 : 0 ≤ test_logScale n := hq.le
    have hlogNonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have htargetNat :
        (2 / Real.pi - epsilon) * Real.log (n : ℝ) ≤ (n : ℝ) := by
      have hpi : 2 / Real.pi < 1 := by
        rw [div_lt_one Real.pi_pos]
        linarith [Real.pi_gt_three]
      have hcoef : 2 / Real.pi - epsilon ≤ 1 := by linarith
      have hlogLe : Real.log (n : ℝ) ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hnR
        linarith
      exact (mul_le_mul_of_nonneg_right hcoef hlogNonneg).trans
        (by simpa using hlogLe)
    intro X
    by_cases hLeb : ∀ v ∈ Set.Icc a b,
        lebesgueFunction X v ≤ (n : ℝ)
    · have hnorm : |normalizationLevel X| ≤ M := by
        dsimp only [M]
        exact abs_normalizationLevel_le_of_le_nat hn2 X ha hab hb hLeb
      let x0 : ℝ := (a + b) / 2
      let rate : ℝ := test_logScale n ^ 2
      let z : ℝ := amplitudeMaximizer X a b rate x0 hab.le
      have hrate : 0 < rate := by dsimp only [rate]; positivity
      have hx0left : a ≤ x0 - h := by
        dsimp only [x0, h, d]
        linarith
      have hx0right : x0 + h ≤ b := by
        dsimp only [x0, h, d]
        linarith
      have hx0left0 : -1 ≤ x0 - h := ha.trans hx0left
      have hx0right0 : x0 + h ≤ 1 := hx0right.trans hb
      have hzNear : |x0 - z| ≤ 2 * h := by
        exact test_amplitudeMaximizer_near_anchor hn2 X hab.le hh hrate
          ha hb hx0left0 hx0right0 hx0left hx0right hLeb
          (by simpa only [rate, mul_assoc] using hlocalize)
      have hzCore : z ∈ Set.Icc (a + 3 * d / 8) (b - 3 * d / 8) := by
        rw [abs_le] at hzNear
        dsimp only [z, x0, h] at hzNear ⊢
        constructor <;> linarith
      have hzMid : z ∈ Set.Icc (a + (b - a) / 4)
          (b - (b - a) / 4) := by
        dsimp only [d] at hzCore
        constructor <;> linarith [hzCore.1, hzCore.2]
      let rho : ℝ := exteriorDensity X (normalizationLevel X) a b z 0
      have hrhoLower : rho0 ≤ rho := by
        have := hboundary X hLeb z hzMid
        simpa only [rho0, rho, gap0, M, d] using this
      have hrhoNonneg : 0 ≤ rho := hrho0.le.trans hrhoLower
      have hzUnit : |z| ≤ 1 := by
        rw [abs_le]
        constructor
        · have : a ≤ z := by linarith [hzCore.1, hd]
          linarith
        · have : z ≤ b := by linarith [hzCore.2, hd]
          linarith
      have hzSep : ∀ v ∉ Set.Icc a b, gap ≤ |z - v| := by
        intro v hv
        have haz : a ≤ z := by linarith [hzCore.1, hd]
        have hzb : z ≤ b := by linarith [hzCore.2, hd]
        have hv' : v < a ∨ b < v := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hv
        rcases hv' with hvleft | hvright
        · rw [abs_of_nonneg (sub_nonneg.mpr (hvleft.le.trans haz))]
          dsimp only [gap]
          linarith [hzCore.1]
        · rw [abs_of_nonpos (sub_nonpos.mpr (hzb.trans hvright.le))]
          dsimp only [gap]
          linarith [hzCore.2]
      have hrhoUpper : rho ≤ rhoU := by
        dsimp only [rhoU, rho]
        exact exteriorDensity_le_localDensityUpper hn X hgap hzUnit hzSep hM hnorm
      have hregularCount : ∀ y, |y - z| ≤ 2 * S →
          |y| ≤ 1 ∧ ∀ v ∉ Set.Icc a b, gap ≤ |y - v| := by
        intro y hy
        rw [abs_le] at hy
        have hyLower : a + d / 4 ≤ y := by
          dsimp only [S] at hy
          linarith [hzCore.1]
        have hyUpper : y ≤ b - d / 4 := by
          dsimp only [S] at hy
          linarith [hzCore.2]
        constructor
        · rw [abs_le]
          constructor <;> linarith
        · intro v hv
          have hv' : v < a ∨ b < v := by
            simpa only [Set.mem_Icc, not_and_or, not_le] using hv
          rcases hv' with hvleft | hvright
          · rw [abs_of_nonneg (by linarith)]
            dsimp only [gap]
            linarith
          · rw [abs_of_nonpos (by linarith)]
            dsimp only [gap]
            linarith
      let R0 : ℝ := test_minRadius n
      let ratio : ℝ := test_shellRatio Q
      let J : ℕ := test_shellSteps Q n
      let Rterm : ℝ := R0 * ratio ^ J
      have hQpos : 0 < Q := by omega
      have hratio : 1 < ratio := by
        dsimp only [ratio]
        exact test_shellRatio_gt_one hQpos
      have hR0 : 0 < R0 := by
        dsimp only [R0, test_minRadius]
        positivity
      have hterminal : Rterm ≤ test_maxRadius n := by
        dsimp only [Rterm, R0, ratio, J]
        exact test_shell_terminal_le_maxRadius hQpos hn hq hrange
      have hcountR : ∀ j ≤ J,
          (2 * (n : ℝ) * (rho - delta)) * (R0 * ratio ^ j) ≤
            (localNodeCount X z (R0 * ratio ^ j) : ℝ) := by
        intro j hj
        have hpowOne : 1 ≤ ratio ^ j := one_le_pow₀ hratio.le
        have hmin : test_minRadius n ≤ R0 * ratio ^ j := by
          dsimp only [R0]
          exact (le_mul_iff_one_le_right hR0).2 hpowOne
        have hpowMono : ratio ^ j ≤ ratio ^ J :=
          pow_le_pow_right₀ hratio.le hj
        have hmax : R0 * ratio ^ j ≤ test_maxRadius n := by
          exact (mul_le_mul_of_nonneg_left hpowMono hR0.le).trans
            (by simpa only [Rterm] using hterminal)
        have hc := hcount X hnorm hLeb z hregularCount hrhoNonneg
          (R0 * ratio ^ j) hmin hmax
        dsimp only [rho] at hc ⊢
        convert hc using 1 <;> ring
      have hzNe : ∀ k, z ≠ X k := by
        have hampLower := amplitude_anchor_lower hn2 X hab.le hrate.le hh
          hx0left0 hx0right0 hx0left hx0right
        have hpositive : 0 <
            (h / (2 * (n : ℝ))) * nodalScale X * Real.exp (-rate * h) := by
          exact mul_pos
            (mul_pos (div_pos hh (mul_pos (by norm_num) hnR))
              (nodalScale_pos hn X))
            (Real.exp_pos _)
        have hampPos : 0 < amplitude X a b rate x0 hab.le :=
          hpositive.trans_le hampLower
        intro k hzk
        have hpzero : (nodalPolynomial X).eval z = 0 := by
          rw [hzk]
          exact nodalPolynomial_eval_node X k
        have hampeq : amplitude X a b rate x0 hab.le =
            |(nodalPolynomial X).eval z| * Real.exp (-rate * |x0 - z|) := by
          rfl
        rw [hampeq, hpzero, abs_zero, zero_mul] at hampPos
        exact (lt_irrefl 0 hampPos)
      obtain ⟨hmle, hmain, htail⟩ :=
        hderivScalar rho hrhoNonneg hrhoUpper
      have hampzRate : amplitude X a b rate z hab.le =
          |(nodalPolynomial X).eval z| := by
        dsimp only [z]
        exact amplitude_at_maximizer_eq_abs X hab.le hrate.le
      have hampz : amplitude X a b (test_logScale n ^ 2) z hab.le =
          |(nodalPolynomial X).eval z| := by
        simpa only [rate] using hampzRate
      have hderiv := test_shell_derivative_bound hn2 X ha hb hab hd
        hM hnorm hLeb hgap (by dsimp only [gap]; rfl) hdelta
        hqLarge hgeomDeriv hgeomAnchor hzCore
        hzUnit hzSep hampz hrhoNonneg hterminal hmle hmain htail (by rfl)
      have hderivC : 0 < (n : ℝ) * (Real.pi * rho + delta) := by positivity
      have hAbel := test_lebesgue_lower_of_geometric_count X hzNe hR0
        hratio (sq_nonneg (test_logScale n)) hderivC hcountR hderiv
      have hrateTerminal : test_logScale n ^ 2 * Rterm ≤
          (test_logScale n)⁻¹ := by
        calc
          test_logScale n ^ 2 * Rterm ≤
              test_logScale n ^ 2 * test_maxRadius n :=
            mul_le_mul_of_nonneg_left hterminal (sq_nonneg _)
          _ = (test_logScale n)⁻¹ := by
            unfold test_maxRadius
            rw [inv_eq_one_div, inv_eq_one_div]
            field_simp [hq.ne']
      have hedge : Real.exp (-(test_logScale n)⁻¹) ≤
          Real.exp (-(test_logScale n ^ 2) * Rterm) := by
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using neg_le_neg hrateTerminal
      have hdensity := test_density_ratio_mono hrho0 hdelta hdeltarho hrhoLower
      have hshellNonneg : 0 ≤ 1 + (J : ℝ) * (1 - 1 / ratio) := by
        have hratio0 : 0 < ratio := zero_lt_one.trans hratio
        have hcoef : 0 ≤ 1 - 1 / ratio := by
          exact sub_nonneg.mpr ((div_le_one hratio0).2 hratio.le)
        positivity
      have hfactor :
          Real.exp (-(test_logScale n)⁻¹) * D *
              (1 + (J : ℝ) * (1 - 1 / ratio)) ≤
            (Real.exp (-(test_logScale n ^ 2) * Rterm) /
                ((n : ℝ) * (Real.pi * rho + delta))) *
              ((2 * (n : ℝ) * (rho - delta)) *
                (1 + (J : ℝ) * (1 - 1 / ratio))) := by
        have hprod : Real.exp (-(test_logScale n)⁻¹) * D ≤
            Real.exp (-(test_logScale n ^ 2) * Rterm) *
              (2 * (rho - delta) / (Real.pi * rho + delta)) := by
          exact mul_le_mul hedge hdensity hDpos.le (Real.exp_pos _).le
        have hprod' := mul_le_mul_of_nonneg_right hprod hshellNonneg
        calc
          Real.exp (-(test_logScale n)⁻¹) * D *
              (1 + (J : ℝ) * (1 - 1 / ratio)) ≤
            (Real.exp (-(test_logScale n ^ 2) * Rterm) *
              (2 * (rho - delta) / (Real.pi * rho + delta))) *
                (1 + (J : ℝ) * (1 - 1 / ratio)) := hprod'
          _ = (Real.exp (-(test_logScale n ^ 2) * Rterm) /
                ((n : ℝ) * (Real.pi * rho + delta))) *
              ((2 * (n : ℝ) * (rho - delta)) *
                (1 + (J : ℝ) * (1 - 1 / ratio))) := by
            field_simp [hnR.ne', (ne_of_gt (by positivity : 0 < Real.pi * rho + delta))]
      have htargetFactor :
          (2 / Real.pi - epsilon) * test_logScale n ≤
            Real.exp (-(test_logScale n)⁻¹) * D *
              (1 + (J : ℝ) * (1 - 1 / ratio)) := by
        have hs := hscalar
        dsimp only [J, ratio] at hs ⊢
        have hmul := mul_le_mul_of_nonneg_right hs.le hq.le
        calc
          (2 / Real.pi - epsilon) * test_logScale n ≤
              (Real.exp (-(test_logScale n)⁻¹) * D *
                ((1 + (test_shellSteps Q n : ℝ) *
                  (1 - 1 / test_shellRatio Q)) / test_logScale n)) *
                    test_logScale n := hmul
          _ = Real.exp (-(test_logScale n)⁻¹) * D *
              (1 + (test_shellSteps Q n : ℝ) *
                (1 - 1 / test_shellRatio Q)) := by
            field_simp [hq.ne']
      refine ⟨z, ?_, ?_⟩
      · exact amplitudeMaximizer_mem X hab.le
      · change (2 / Real.pi - epsilon) * test_logScale n ≤
          lebesgueFunction X z
        exact htargetFactor.trans (hfactor.trans hAbel)
    · push_neg at hLeb
      obtain ⟨x, hx, hlarge⟩ := hLeb
      exact ⟨x, hx, htargetNat.trans hlarge.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  exact ⟨N, fun n hn X => hN n hn X⟩

end Erdos1153

alias _root_.Erdos1153.erdos1153 := _root_.Erdos1153.erdos_1153
