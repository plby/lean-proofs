import ErdosProblems.Erdos1002.NearResonantMultipliers
import ErdosProblems.Erdos1002.RamanujanSums
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite near-resonant vector Abel bridge

This file puts the near-resonant multiplier estimates into the Hilbert space
actually used by the dyadic square-function argument.  The coordinates are
the modes `K < n ≤ 2K`, equipped with their Euclidean (`ℓ²`) norm; multiplier
weights retain the finite-coordinate supremum norm.

The main result is
`norm_finiteNearRamanujanMultiplierVector_le_of_partialSum`.  Its only
arithmetic hypothesis is a dimensionally precise uniform `ℓ²` bound for the
truncated Ramanujan vectors.  The proof records the terminal Abel term,
every discrete variation term, and the endpoint assumptions.  The empty
block `K = 0` is treated separately at the end.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace Erdos1002

noncomputable section

/-! ## Euclidean vector Abel summation -/

/-- The finite set of Fourier modes in the half-open dyadic block
`K < n ≤ 2K`. -/
abbrev nearDyadicIndex (K : ℕ) := {n : ℕ // n ∈ Finset.Ioc K (2 * K)}

/-- The Hilbert space `ℓ² {n : K < n ≤ 2K}`. -/
abbrev NearDyadicEuclidean (K : ℕ) := EuclideanSpace ℂ (nearDyadicIndex K)

/-- Coordinatewise multiplication of a Euclidean vector by a finite
sup-norm multiplier. -/
def euclideanCoordinateMul {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) (w : ι → ℂ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i ↦ x i * w i)

/-- Closed-interval partial sum of Euclidean vectors. -/
def euclideanIntervalPartialSum {ι : Type*} [Fintype ι]
    (u : ℕ → EuclideanSpace ℂ ι) (a b : ℕ) : EuclideanSpace ℂ ι :=
  ∑ n ∈ Finset.Icc a b, u n

/-- Exact finite Abel summation in Euclidean space. -/
theorem euclideanVectorDiscreteAbel_identity {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (u : ℕ → EuclideanSpace ℂ ι) (w : ℕ → ι → ℂ)
    {a b : ℕ} (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b, euclideanCoordinateMul (u n) (w n)) =
      euclideanCoordinateMul (euclideanIntervalPartialSum u a b) (w b) +
        ∑ n ∈ Finset.Ico a b,
          euclideanCoordinateMul (euclideanIntervalPartialSum u a n)
            (w n - w (n + 1)) := by
  have h := vectorDiscreteAbel_identity
    (fun n i ↦ u n i) w hab
  ext i
  simpa only [euclideanCoordinateMul, euclideanIntervalPartialSum,
    WithLp.ofLp_toLp, WithLp.ofLp_sum, WithLp.ofLp_add,
    Finset.sum_apply, Pi.add_apply, Pi.sub_apply,
    coordinateMul, vectorIntervalPartialSum] using!
      congrFun h i

/-- An `ℓ²` vector times an `ℓ∞` multiplier has the expected product bound. -/
theorem norm_euclideanCoordinateMul_le {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℂ ι) (w : ι → ℂ) :
    ‖euclideanCoordinateMul x w‖ ≤ ‖x‖ * ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
  simp only [euclideanCoordinateMul, WithLp.ofLp_toLp, norm_mul, mul_pow]
  calc
    ∑ i, ‖x i‖ ^ 2 * ‖w i‖ ^ 2 ≤
        ∑ i, ‖x i‖ ^ 2 * ‖w‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w i) 2)
        (sq_nonneg _)
    _ = (∑ i, ‖x i‖ ^ 2) * ‖w‖ ^ 2 := by
      rw [Finset.sum_mul]

/-- Norm form of finite Euclidean Abel summation, with the terminal term and
all variations explicit. -/
theorem norm_euclidean_vector_sum_coordinateMul_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ℕ → EuclideanSpace ℂ ι) (w : ℕ → ι → ℂ)
    {a b : ℕ} (hab : a ≤ b) (M : ℝ)
    (hM : ∀ n ∈ Finset.Icc a b,
      ‖euclideanIntervalPartialSum u a n‖ ≤ M) :
    ‖∑ n ∈ Finset.Icc a b, euclideanCoordinateMul (u n) (w n)‖ ≤
      M * (‖w b‖ + ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
  rw [euclideanVectorDiscreteAbel_identity u w hab]
  calc
    ‖euclideanCoordinateMul (euclideanIntervalPartialSum u a b) (w b) +
        ∑ n ∈ Finset.Ico a b,
          euclideanCoordinateMul (euclideanIntervalPartialSum u a n)
            (w n - w (n + 1))‖ ≤
      ‖euclideanCoordinateMul (euclideanIntervalPartialSum u a b) (w b)‖ +
        ∑ n ∈ Finset.Ico a b,
          ‖euclideanCoordinateMul (euclideanIntervalPartialSum u a n)
            (w n - w (n + 1))‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ ‖euclideanIntervalPartialSum u a b‖ * ‖w b‖ +
        ∑ n ∈ Finset.Ico a b,
          ‖euclideanIntervalPartialSum u a n‖ * ‖w n - w (n + 1)‖ := by
      gcongr with n hn
      · exact norm_euclideanCoordinateMul_le _ _
      · exact norm_euclideanCoordinateMul_le _ _
    _ ≤ M * ‖w b‖ +
        ∑ n ∈ Finset.Ico a b, M * ‖w n - w (n + 1)‖ := by
      gcongr with n hn
      · exact hM b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
      · exact hM n (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩)
    _ = M * (‖w b‖ + ∑ n ∈ Finset.Ico a b, ‖w n - w (n + 1)‖) := by
      rw [mul_add, Finset.mul_sum]

/-! ## The sampled near-`J` multiplier and its variation -/

/-- Sup-norm multiplier vector on the manuscript dyadic block `K < n ≤ 2K`. -/
def nearJDyadicMultiplierVector (a ε : ℝ) (K : ℕ) (x : ℝ) :
    nearDyadicIndex K → ℂ :=
  fun n ↦ nearJReciprocalSquare a ε (n : ℕ) x

/-- Uniform finite-coordinate supremum bound for the sampled multiplier. -/
theorem norm_nearJDyadicMultiplierVector_le
    (a ε : ℝ) (K : ℕ) (x : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ‖nearJDyadicMultiplierVector a ε K x‖ ≤
      32 * Real.pi * nearProfileDecayConstant := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg)).mpr
  intro n
  exact norm_nearJ_le a ε ((n : ℕ) / x ^ 2) ha hε haε

/-- The reciprocal-square profile has a continuous derivative away from the
singular endpoint `x = 0`. -/
theorem continuousOn_deriv_nearJReciprocalSquare_Ioi
    (a ε n : ℝ) (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4) :
    ContinuousOn (fun x ↦ deriv (nearJReciprocalSquare a ε n) x) (Ioi 0) := by
  have harg : ContinuousOn (fun x : ℝ => n / x ^ 2) (Ioi 0) := by
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt hx))
  have hcoef : ContinuousOn (fun x : ℝ => -2 * n / x ^ 3) (Ioi 0) := by
    exact continuousOn_const.div (continuousOn_id.pow 3)
      (fun x hx => pow_ne_zero 3 (ne_of_gt hx))
  have houter : ContinuousOn
      (fun x : ℝ => deriv (nearJ a ε) (n / x ^ 2)) (Ioi 0) := by
    simpa only [Function.comp_def] using!
      (nearJ_deriv_continuous a ε ha hε haε).continuousOn.comp harg
        (fun _ _ => mem_univ _)
  have hexplicit : ContinuousOn
      (fun x : ℝ => (-2 * n / x ^ 3) •
        deriv (nearJ a ε) (n / x ^ 2)) (Ioi 0) :=
    hcoef.smul houter
  apply hexplicit.congr
  intro x hx
  exact (nearJReciprocalSquare_hasDerivAt a ε n x ha hε haε
    (ne_of_gt hx)).deriv

/-- One coordinate variation over `[p,p+1]` is bounded by the dyadic maximum
of the derivative. -/
theorem norm_nearJReciprocalSquare_nat_sub_succ_le_integral_max
    (a ε : ℝ) (K p : ℕ) (n : nearDyadicIndex K)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hp : 0 < p) :
    ‖nearJReciprocalSquare a ε (n : ℕ) (p : ℝ) -
        nearJReciprocalSquare a ε (n : ℕ) ((p + 1 : ℕ) : ℝ)‖ ≤
      ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x := by
  let f : ℝ → ℂ := nearJReciprocalSquare a ε (n : ℕ)
  let G : ℝ → ℝ := nearJReciprocalSquareDyadicMax a ε K
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpSucc : (p : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by norm_num
  have hsubIoi : uIcc (p : ℝ) ((p + 1 : ℕ) : ℝ) ⊆ Ioi (0 : ℝ) := by
    rw [uIcc_of_le hpSucc]
    intro x hx
    exact hpR.trans_le hx.1
  have hderivCont : ContinuousOn (fun x ↦ deriv f x)
      (uIcc (p : ℝ) ((p + 1 : ℕ) : ℝ)) := by
    exact (continuousOn_deriv_nearJReciprocalSquare_Ioi
      a ε (n : ℕ) ha hε haε).mono hsubIoi
  have hGCont : ContinuousOn G
      (uIcc (p : ℝ) ((p + 1 : ℕ) : ℝ)) := by
    exact (nearJReciprocalSquareDyadicMax_continuousOn_Ioi
      a ε K ha hε haε).mono hsubIoi
  have hftc :
      ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ), deriv f x =
        f ((p + 1 : ℕ) : ℝ) - f (p : ℝ) := by
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x hx =>
        (nearJReciprocalSquare_hasDerivAt a ε (n : ℕ) x ha hε haε
          (ne_of_gt (hsubIoi hx))).differentiableAt)
      hderivCont.intervalIntegrable
  have hnmem : (n : ℕ) ∈ Finset.Icc K (2 * K) := by
    have hnIoc : K < (n : ℕ) ∧ (n : ℕ) ≤ 2 * K :=
      Finset.mem_Ioc.mp n.property
    exact Finset.mem_Icc.mpr ⟨hnIoc.1.le, hnIoc.2⟩
  calc
    ‖nearJReciprocalSquare a ε (n : ℕ) (p : ℝ) -
        nearJReciprocalSquare a ε (n : ℕ) ((p + 1 : ℕ) : ℝ)‖ =
        ‖∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ), deriv f x‖ := by
      rw [hftc]
      change ‖f (p : ℝ) - f ((p + 1 : ℕ) : ℝ)‖ =
        ‖f ((p + 1 : ℕ) : ℝ) - f (p : ℝ)‖
      rw [show f (p : ℝ) - f ((p + 1 : ℕ) : ℝ) =
        -(f ((p + 1 : ℕ) : ℝ) - f (p : ℝ)) by abel, norm_neg]
    _ ≤ ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ), ‖deriv f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hpSucc
    _ ≤ ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ), G x := by
      apply intervalIntegral.integral_mono_on hpSucc
        hderivCont.norm.intervalIntegrable hGCont.intervalIntegrable
      intro x _hx
      unfold G nearJReciprocalSquareDyadicMax
      exact Finset.le_sup' (s := Finset.Icc K (2 * K))
        (fun m : ℕ => ‖deriv (nearJReciprocalSquare a ε (m : ℝ)) x‖)
        hnmem

/-- Supremum-norm variation over one integer interval. -/
theorem norm_nearJDyadicMultiplierVector_sub_succ_le_integral_max
    (a ε : ℝ) (K p : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hp : 0 < p) :
    ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
        nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x := by
  have hnonneg : 0 ≤
      ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact nearJReciprocalSquareDyadicMax_nonneg a ε K x
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro n
  simpa only [nearJDyadicMultiplierVector, Pi.sub_apply] using!
    norm_nearJReciprocalSquare_nat_sub_succ_le_integral_max
      a ε K p n ha hε haε hp

/-- The entire discrete variation is bounded by one interval integral.  The
proof explicitly verifies integrability before joining adjacent intervals. -/
theorem sum_norm_nearJDyadicMultiplierVector_sub_succ_le_intervalIntegral
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      ∫ x : ℝ in (P : ℝ)..(U : ℝ),
        nearJReciprocalSquareDyadicMax a ε K x := by
  let G : ℝ → ℝ := nearJReciprocalSquareDyadicMax a ε K
  have hGIoi : IntegrableOn G (Ioi (0 : ℝ)) :=
    nearJReciprocalSquareDyadicMax_integrableOn_Ioi
      a ε K ha hε haε hK
  have hint : ∀ p ∈ Set.Ico P U,
      IntervalIntegrable G volume (p : ℝ) ((p + 1 : ℕ) : ℝ) := by
    intro p hp
    have hPp : P ≤ p := hp.1
    have hpR : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast hP.trans_le hPp
    rw [intervalIntegrable_iff, uIoc_of_le (by norm_num)]
    exact hGIoi.mono_set (by
      intro x hx
      exact hpR.trans hx.1)
  calc
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
        ∑ p ∈ Finset.Ico P U,
          ∫ x : ℝ in (p : ℝ)..((p + 1 : ℕ) : ℝ), G x := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_nearJDyadicMultiplierVector_sub_succ_le_integral_max
        a ε K p ha hε haε (hP.trans_le (Finset.mem_Ico.mp hp).1)
    _ = ∫ x : ℝ in (P : ℝ)..(U : ℝ), G x := by
      exact intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun p : ℕ ↦ (p : ℝ)) hPU hint

/-- Uniform total-variation bound supplied by the reciprocal-square dyadic
envelope. -/
theorem sum_norm_nearJDyadicMultiplierVector_sub_succ_le
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      32 * Real.pi * nearProfileDecayConstant := by
  have hPUR : (P : ℝ) ≤ (U : ℝ) := by exact_mod_cast hPU
  calc
    ∑ p ∈ Finset.Ico P U,
        ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
          nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
        ∫ x : ℝ in (P : ℝ)..(U : ℝ),
          nearJReciprocalSquareDyadicMax a ε K x :=
      sum_norm_nearJDyadicMultiplierVector_sub_succ_le_intervalIntegral
        a ε K P U ha hε haε hK hP hPU
    _ = ∫ x in Set.Ioc (P : ℝ) (U : ℝ),
          nearJReciprocalSquareDyadicMax a ε K x := by
      rw [intervalIntegral.integral_of_le hPUR]
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
          nearJReciprocalSquareDyadicMax a ε K x := by
      apply MeasureTheory.integral_mono_measure
        (Measure.restrict_mono_set volume (by
          intro x hx
          have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
          exact hPR.trans hx.1))
        (Eventually.of_forall fun x ↦
          nearJReciprocalSquareDyadicMax_nonneg a ε K x)
        (nearJReciprocalSquareDyadicMax_integrableOn_Ioi
          a ε K ha hε haε hK)
    _ ≤ 32 * Real.pi * nearProfileDecayConstant :=
      integral_nearJReciprocalSquareDyadicMax_Ioi_le
        a ε K ha hε haε hK

/-- Combined bound for the terminal Abel term and all variation terms. -/
theorem nearJDyadicMultiplierVector_terminal_add_variation_le
    (a ε : ℝ) (K P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U) :
    ‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ +
        ∑ p ∈ Finset.Ico P U,
          ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
            nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)‖ ≤
      64 * Real.pi * nearProfileDecayConstant := by
  have hterminal := norm_nearJDyadicMultiplierVector_le
    a ε K (U : ℝ) ha hε haε
  have hvariation := sum_norm_nearJDyadicMultiplierVector_sub_succ_le
    a ε K P U ha hε haε hK hP hPU
  linarith

/-! ## Ramanujan multiplier bridge -/

/-- The `ℓ²(K < n ≤ 2K)` vector with coordinates `c_p(-n) / p²`. -/
def nearRamanujanVectorTerm (K p : ℕ) : NearDyadicEuclidean K :=
  WithLp.toLp 2 (fun n ↦
    ramanujanSum p (-((n : ℕ) : ℤ)) / (((p : ℝ) ^ 2 : ℝ) : ℂ))

@[simp] theorem nearRamanujanVectorTerm_apply
    (K p : ℕ) (n : nearDyadicIndex K) :
    nearRamanujanVectorTerm K p n =
      ramanujanSum p (-((n : ℕ) : ℤ)) /
        (((p : ℝ) ^ 2 : ℝ) : ℂ) := by
  rfl

/-- The finite vector multiplier sum corresponding to the manuscript's
near-resonant dyadic block.  Taking `P = 3` represents `2 < p ≤ U`. -/
def finiteNearRamanujanMultiplierVector
    (a ε : ℝ) (K P U : ℕ) : NearDyadicEuclidean K :=
  ∑ p ∈ Finset.Icc P U,
    euclideanCoordinateMul (nearRamanujanVectorTerm K p)
      (nearJDyadicMultiplierVector a ε K (p : ℝ))

/-- Coordinate formula showing that the Hilbert-space vector is exactly the
finite multiplier sum from the Fourier calculation. -/
theorem finiteNearRamanujanMultiplierVector_apply
    (a ε : ℝ) (K P U : ℕ) (n : nearDyadicIndex K) :
    finiteNearRamanujanMultiplierVector a ε K P U n =
      ∑ p ∈ Finset.Icc P U,
        (ramanujanSum p (-((n : ℕ) : ℤ)) /
          (((p : ℝ) ^ 2 : ℝ) : ℂ)) *
        nearJReciprocalSquare a ε (n : ℕ) (p : ℝ) := by
  simp only [finiteNearRamanujanMultiplierVector, Finset.sum_apply,
    euclideanCoordinateMul, WithLp.ofLp_toLp, WithLp.ofLp_sum,
    nearRamanujanVectorTerm, nearJDyadicMultiplierVector]

/-- Exact finite Abel decomposition, including the upper-endpoint term. -/
theorem finiteNearRamanujanMultiplierVector_eq_abel
    (a ε : ℝ) (K P U : ℕ) (hPU : P ≤ U) :
    finiteNearRamanujanMultiplierVector a ε K P U =
      euclideanCoordinateMul
          (euclideanIntervalPartialSum (nearRamanujanVectorTerm K) P U)
          (nearJDyadicMultiplierVector a ε K (U : ℝ)) +
        ∑ p ∈ Finset.Ico P U,
          euclideanCoordinateMul
            (euclideanIntervalPartialSum (nearRamanujanVectorTerm K) P p)
            (nearJDyadicMultiplierVector a ε K (p : ℝ) -
              nearJDyadicMultiplierVector a ε K ((p + 1 : ℕ) : ℝ)) := by
  exact euclideanVectorDiscreteAbel_identity
    (nearRamanujanVectorTerm K)
    (fun p ↦ nearJDyadicMultiplierVector a ε K (p : ℝ)) hPU

/-- Finite form of the multiplier estimate used in (3.11).  Its sole
arithmetic input is the displayed uniform `ℓ²` bound for every truncated
Ramanujan vector sum. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_of_partialSum
    (a ε : ℝ) (K P U : ℕ) (M : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U)
    (hRamanujan : ∀ R ∈ Finset.Icc P U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) P R‖ ≤ M) :
    ‖finiteNearRamanujanMultiplierVector a ε K P U‖ ≤
      M * (64 * Real.pi * nearProfileDecayConstant) := by
  have hMnonneg : 0 ≤ M := by
    have hPP : P ∈ Finset.Icc P U := Finset.mem_Icc.mpr ⟨le_rfl, hPU⟩
    exact (norm_nonneg
      (euclideanIntervalPartialSum (nearRamanujanVectorTerm K) P P)).trans
      (hRamanujan P hPP)
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K P U‖ ≤
        M *
          (‖nearJDyadicMultiplierVector a ε K (U : ℝ)‖ +
            ∑ p ∈ Finset.Ico P U,
              ‖nearJDyadicMultiplierVector a ε K (p : ℝ) -
                nearJDyadicMultiplierVector a ε K
                  ((p + 1 : ℕ) : ℝ)‖) := by
      exact norm_euclidean_vector_sum_coordinateMul_le
        (nearRamanujanVectorTerm K)
        (fun p ↦ nearJDyadicMultiplierVector a ε K (p : ℝ))
        hPU M hRamanujan
    _ ≤ M * (64 * Real.pi * nearProfileDecayConstant) := by
      exact mul_le_mul_of_nonneg_left
        (nearJDyadicMultiplierVector_terminal_add_variation_le
          a ε K P U ha hε haε hK hP hPU)
        hMnonneg

/-- Squared `ℓ²` form of the finite multiplier estimate. -/
theorem sum_norm_sq_finiteNearRamanujanMultiplierVector_le_of_partialSum
    (a ε : ℝ) (K P U : ℕ) (M : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hP : 0 < P) (hPU : P ≤ U)
    (hRamanujan : ∀ R ∈ Finset.Icc P U,
      ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) P R‖ ≤ M) :
    ∑ n : nearDyadicIndex K,
        ‖finiteNearRamanujanMultiplierVector a ε K P U n‖ ^ 2 ≤
      (M * (64 * Real.pi * nearProfileDecayConstant)) ^ 2 := by
  rw [← EuclideanSpace.norm_sq_eq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_finiteNearRamanujanMultiplierVector_le_of_partialSum
      a ε K P U M ha hε haε hK hP hPU hRamanujan) 2

/-- The dyadic block `0 < n ≤ 0` is empty, so the finite multiplier vector
is exactly zero; the positive-`K` theorem above loses no endpoint case. -/
theorem finiteNearRamanujanMultiplierVector_zero_frequencyBlock
    (a ε : ℝ) (P U : ℕ) :
    finiteNearRamanujanMultiplierVector a ε 0 P U = 0 := by
  ext n
  have hn : 0 < (n : ℕ) ∧ (n : ℕ) ≤ 0 := Finset.mem_Ioc.mp n.property
  omega

theorem norm_finiteNearRamanujanMultiplierVector_zero_frequencyBlock
    (a ε : ℝ) (P U : ℕ) :
    ‖finiteNearRamanujanMultiplierVector a ε 0 P U‖ = 0 := by
  rw [finiteNearRamanujanMultiplierVector_zero_frequencyBlock, norm_zero]

end

end Erdos1002
