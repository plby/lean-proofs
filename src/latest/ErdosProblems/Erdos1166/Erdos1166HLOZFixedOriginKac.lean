import ErdosProblems.Erdos1166.Erdos1166HLOZExternalUpper

namespace Erdos1166.HLOZFixedOriginKac

open MeasureTheory Set
open scoped BigOperators

/-!
A fixed-origin version of the Kac moment argument.  Unlike the spatial
collision moment used for the maximal local time, the first time contributes
one more return-kernel factor.  Consequently the bound is `r! * G^r`, with no
factor proportional to the time horizon.
-/

variable {Site' Ω : Type*} [DecidableEq Site'] [MeasurableSpace Ω]

/-- All selected times hit one prescribed site. -/
def fixedHitSet (n r : ℕ) (X : Ω → Fin (n + 1) → Site') (x : Site')
    (t : KacMoment.TimeTuple n r) : Set Ω :=
  {ω | ∀ i, X ω (t i) = x}

theorem fixedHitSet_comp_perm (n r : ℕ)
    (X : Ω → Fin (n + 1) → Site') (x : Site')
    (t : KacMoment.TimeTuple n r) (σ : Equiv.Perm (Fin r)) :
    fixedHitSet n r X x (t ∘ σ) = fixedHitSet n r X x t := by
  ext ω
  simp only [fixedHitSet, Set.mem_setOf_eq, Function.comp_apply]
  constructor
  · intro h i
    simpa using h (σ.symm i)
  · intro h i
    exact h (σ i)

/-- The fixed-origin weight: the first selected time is a return from time
zero, and all later factors are the ordinary successive gaps. -/
noncomputable def fixedGapWeight (n k : ℕ) (q : Fin (n + 1) → ℝ)
    (t : KacMoment.TimeTuple n (k + 1)) : ℝ :=
  q (t 0) * KacMoment.gapWeight n k q t

/-- Summing fixed-origin weights over increasing time tuples costs one Green
factor per selected time and no free choice of a starting time. -/
theorem sum_sorted_fixedGapWeight_le (n k : ℕ)
    (q : Fin (n + 1) → ℝ) (hq : ∀ d, 0 ≤ q d) :
    ∑ t ∈ KacMoment.sortedTuples n (k + 1), fixedGapWeight n k q t ≤
      (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
  classical
  let target : Finset
      (Fin (n + 1) × (Fin k → Fin (n + 1))) := Finset.univ
  let W : (Fin (n + 1) × (Fin k → Fin (n + 1))) → ℝ :=
    fun p ↦ q p.1 * ∏ i : Fin k, q (p.2 i)
  calc
    ∑ t ∈ KacMoment.sortedTuples n (k + 1), fixedGapWeight n k q t =
        ∑ p ∈ (KacMoment.sortedTuples n (k + 1)).image
          (KacMoment.gapEncode n k), W p := by
      rw [Finset.sum_image (KacMoment.gapEncode_injOn_sorted n k)]
      apply Finset.sum_congr rfl
      intro t _ht
      rfl
    _ ≤ ∑ p ∈ target, W p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro p _hp _hnot
        exact mul_nonneg (hq p.1) (Finset.prod_nonneg fun i _ ↦ hq (p.2 i))
    _ = (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
      simp only [target, W]
      rw [Fintype.sum_prod_type]
      calc
        ∑ x : Fin (n + 1), ∑ f : Fin k → Fin (n + 1),
            q x * ∏ i, q (f i) =
            ∑ x : Fin (n + 1), q x *
              (∑ d : Fin (n + 1), q d) ^ k := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [← Finset.mul_sum, Fintype.sum_pow]
        _ = (∑ d : Fin (n + 1), q d) *
              (∑ d : Fin (n + 1), q d) ^ k := by
          rw [Finset.sum_mul]
        _ = (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Integral of one fixed-hit indicator. -/
private theorem integral_fixedHitIndicator
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site') (x : Site')
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : KacMoment.TimeTuple n r,
      MeasurableSet (fixedHitSet n r X x t))
    (t : KacMoment.TimeTuple n r) :
    ∫ ω, (fixedHitSet n r X x t).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ =
      μ.real (fixedHitSet n r X x t) := by
  exact integral_indicator_one (hMeas t)

/-- Exact expansion of the fixed-site local-time power as a finite sum of
fixed-hit indicators. -/
private theorem finiteLocalTime_pow_indicator_sum
    (n r : ℕ) (X : Ω → Fin (n + 1) → Site') (x : Site')
    (ω : Ω) :
    ((KacMoment.finiteLocalTime n (X ω) x ^ r : ℕ) : ℝ) =
      ∑ t : KacMoment.TimeTuple n r,
        (fixedHitSet n r X x t).indicator (fun _ ↦ (1 : ℝ)) ω := by
  rw [KacMoment.localTime_pow_eq_tuple_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro t _ht
  unfold KacMoment.hitIndicator fixedHitSet Set.indicator
  split_ifs <;> simp_all

/-- Fixed-origin Kac moment bound from a return-kernel factorization. -/
theorem integral_finiteLocalTime_pow_le_factorial_mul_green
    (n k : ℕ) (X : Ω → Fin (n + 1) → Site') (x : Site')
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : KacMoment.TimeTuple n (k + 1),
      MeasurableSet (fixedHitSet n (k + 1) X x t))
    (q : Fin (n + 1) → ℝ) (hq : ∀ d, 0 ≤ q d)
    (hKernel : ∀ t ∈ KacMoment.sortedTuples n (k + 1),
      μ.real (fixedHitSet n (k + 1) X x t) ≤ fixedGapWeight n k q t) :
    ∫ ω, ((KacMoment.finiteLocalTime n (X ω) x ^ (k + 1) : ℕ) : ℝ) ∂μ ≤
      (((k + 1).factorial : ℕ) : ℝ) *
        (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
  have hIntegral :
      ∫ ω, ((KacMoment.finiteLocalTime n (X ω) x ^ (k + 1) : ℕ) : ℝ) ∂μ =
        ∑ t : KacMoment.TimeTuple n (k + 1),
          μ.real (fixedHitSet n (k + 1) X x t) := by
    simp_rw [finiteLocalTime_pow_indicator_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro t _ht
      exact integral_fixedHitIndicator n (k + 1) X x μ hMeas t
    · intro t _ht
      exact (integrable_const (1 : ℝ)).indicator (hMeas t)
  rw [hIntegral]
  calc
    ∑ t : KacMoment.TimeTuple n (k + 1),
        μ.real (fixedHitSet n (k + 1) X x t) ≤
        (((k + 1).factorial : ℕ) : ℝ) *
          ∑ t ∈ KacMoment.sortedTuples n (k + 1),
            μ.real (fixedHitSet n (k + 1) X x t) := by
      apply KacMoment.sum_weight_le_factorial_mul_sorted
      · intro t
        exact measureReal_nonneg
      · intro t σ
        rw [fixedHitSet_comp_perm]
    _ ≤ (((k + 1).factorial : ℕ) : ℝ) *
          ∑ t ∈ KacMoment.sortedTuples n (k + 1),
            fixedGapWeight n k q t := by
      gcongr
      exact hKernel _ (by assumption)
    _ ≤ (((k + 1).factorial : ℕ) : ℝ) *
        (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
      gcongr
      exact sum_sorted_fixedGapWeight_le n k q hq

/-- Binomial moments are bounded by the corresponding Green powers.  This is
the exact input expected by `measureReal_ge_le_of_binomial_moments`. -/
theorem integral_choose_finiteLocalTime_le_green_pow
    (n k : ℕ)
    (X : Ω → Fin (n + 1) → Site') (x : Site')
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hMeas : ∀ t : KacMoment.TimeTuple n (k + 1),
      MeasurableSet (fixedHitSet n (k + 1) X x t))
    (q : Fin (n + 1) → ℝ) (hq : ∀ d, 0 ≤ q d)
    (hKernel : ∀ t ∈ KacMoment.sortedTuples n (k + 1),
      μ.real (fixedHitSet n (k + 1) X x t) ≤
        fixedGapWeight n k q t) :
    ∫ ω, ((KacMoment.finiteLocalTime n (X ω) x).choose (k + 1) : ℝ) ∂μ ≤
      (∑ d : Fin (n + 1), q d) ^ (k + 1) := by
  have hpow := integral_finiteLocalTime_pow_le_factorial_mul_green
    n k X x μ hMeas q hq hKernel
  have hpowInt : Integrable
      (fun ω ↦ ((KacMoment.finiteLocalTime n (X ω) x ^ (k + 1) : ℕ) : ℝ)) μ := by
    rw [show (fun ω ↦
        ((KacMoment.finiteLocalTime n (X ω) x ^ (k + 1) : ℕ) : ℝ)) =
        fun ω ↦ ∑ t : KacMoment.TimeTuple n (k + 1),
          (fixedHitSet n (k + 1) X x t).indicator (fun _ ↦ (1 : ℝ)) ω by
      funext ω
      exact finiteLocalTime_pow_indicator_sum n (k + 1) X x ω]
    apply integrable_finset_sum
    intro t _ht
    exact (integrable_const (1 : ℝ)).indicator (hMeas t)
  have hfacPos : (0 : ℝ) < (k + 1).factorial := by positivity
  have hdivInt : Integrable (fun ω ↦
      (KacMoment.finiteLocalTime n (X ω) x : ℝ) ^ (k + 1) /
        ((k + 1).factorial : ℝ)) μ := by
    convert hpowInt.div_const ((k + 1).factorial : ℝ) using 1
    funext ω
    norm_num
  calc
    ∫ ω, ((KacMoment.finiteLocalTime n (X ω) x).choose (k + 1) : ℝ) ∂μ ≤
        ∫ ω, (KacMoment.finiteLocalTime n (X ω) x : ℝ) ^ (k + 1) /
          ((k + 1).factorial : ℝ) ∂μ := by
      apply integral_mono_of_nonneg
      · filter_upwards with ω
        positivity
      · exact hdivInt
      · filter_upwards with ω
        exact Nat.choose_le_pow_div (k + 1)
          (KacMoment.finiteLocalTime n (X ω) x)
    _ = (∫ ω,
          ((KacMoment.finiteLocalTime n (X ω) x ^ (k + 1) : ℕ) : ℝ) ∂μ) /
          ((k + 1).factorial : ℝ) := by
      rw [integral_div]
      congr 1
      apply integral_congr_ae
      filter_upwards with ω
      norm_num
    _ ≤ (((k + 1).factorial : ℝ) *
          (∑ d : Fin (n + 1), q d) ^ (k + 1)) /
          ((k + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right hpow hfacPos.le
    _ = (∑ d : Fin (n + 1), q d) ^ (k + 1) := by field_simp

end Erdos1166.HLOZFixedOriginKac
