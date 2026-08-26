import ErdosProblems.Erdos906.PointwiseLogTail

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Set
open scoped ENNReal NNReal Polynomial Topology

namespace CofiniteDerivatives

noncomputable section

/-- The iid product law of uniform complex coefficients on the closed unit disk. -/
def P : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ ↦ uniformDisk)

instance P.isProbabilityMeasure : IsProbabilityMeasure P := by
  unfold P
  infer_instance

/-- Keep points in the closed unit disk and send all other points to zero. -/
noncomputable def clipDisk (z : ℂ) : ℂ := by
  classical
  exact if z ∈ closedBall (0 : ℂ) 1 then z else 0

@[simp]
theorem clipDisk_eq_self {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    clipDisk z = z := by
  simp [clipDisk, hz]

@[simp]
theorem clipDisk_eq_zero {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) 1) :
    clipDisk z = 0 := by
  simp [clipDisk, hz]

theorem measurable_clipDisk : Measurable clipDisk := by
  exact measurable_id.piecewise measurableSet_closedBall measurable_const

theorem norm_clipDisk_le_one (z : ℂ) : ‖clipDisk z‖ ≤ 1 := by
  by_cases hz : z ∈ closedBall (0 : ℂ) 1
  · rw [clipDisk_eq_self hz]
    simpa [mem_closedBall, dist_eq_norm] using! hz
  · rw [clipDisk_eq_zero hz]
    simp

/-- The clipped random Fock sample path. -/
def randomFock (ω : ℕ → ℂ) : ℂ → ℂ :=
  fockFunction (fun k ↦ clipDisk (ω k))

/-- The `n`-th derivative of a clipped random Fock sample path. -/
def randomFockDeriv (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv n (randomFock ω) z

/-- Every clipped sample path is entire. -/
theorem analyticOnNhd_randomFock (ω : ℕ → ℂ) :
    AnalyticOnNhd ℂ (randomFock ω) Set.univ := by
  exact analyticOnNhd_fockFunction (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k))

/-- Every iterated derivative of every clipped sample path is entire. -/
theorem analyticOnNhd_randomFockDeriv (n : ℕ) (ω : ℕ → ℂ) :
    AnalyticOnNhd ℂ (randomFockDeriv n ω) Set.univ := by
  exact analyticOnNhd_iteratedDeriv_fockFunction (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k)) n

/-- Each coordinate lies in the closed unit disk almost surely. -/
theorem P_ae_coordinate_mem_closedBall (k : ℕ) :
    ∀ᵐ ω ∂P, ω k ∈ closedBall (0 : ℂ) 1 := by
  simpa [P] using!
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ uniformDisk) k).quasiMeasurePreserving.ae
      uniformDisk_ae_mem_closedBall

/-- Each coordinate is nonzero almost surely. -/
theorem P_ae_coordinate_ne_zero (k : ℕ) :
    ∀ᵐ ω ∂P, ω k ≠ 0 := by
  have hnonzero : ∀ᵐ z ∂uniformDisk, z ≠ 0 := by
    rw [ae_iff]
    simpa only [compl_ofPred, not_ne_iff] using! uniformDisk_singleton 0
  simpa [P] using!
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ uniformDisk) k).quasiMeasurePreserving.ae
      hnonzero

/-- Almost surely every coordinate is unchanged by clipping and is nonzero. -/
theorem P_ae_forall_clipDisk_eq_and_ne_zero :
    ∀ᵐ ω ∂P, ∀ k, clipDisk (ω k) = ω k ∧ ω k ≠ 0 := by
  rw [ae_all_iff]
  intro k
  filter_upwards [P_ae_coordinate_mem_closedBall k, P_ae_coordinate_ne_zero k] with ω hmem hne
  exact ⟨clipDisk_eq_self hmem, hne⟩

/-- Almost surely the random Fock sample path is not represented by a complex polynomial. -/
theorem P_ae_randomFock_nonpolynomial :
    ∀ᵐ ω ∂P, ¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = randomFock ω z := by
  filter_upwards [P_ae_forall_clipDisk_eq_and_ne_zero] with ω hω
  apply not_exists_polynomial_eval_eq_fockFunction
    (fun k ↦ clipDisk (ω k)) (fun k ↦ norm_clipDisk_le_one (ω k))
  intro k
  rw [(hω k).1]
  exact (hω k).2

/-- Exact series formula for a random Fock derivative. -/
theorem randomFockDeriv_eq_tsum (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) :
    randomFockDeriv n ω z =
      ∑' m : ℕ, clipDisk (ω (n + m)) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * z ^ m := by
  exact iteratedDeriv_fockFunction_eq_tsum (fun k ↦ clipDisk (ω k))
    (fun k ↦ norm_clipDisk_le_one (ω k)) n z

/-- Random Fock derivative evaluation is jointly measurable in the coefficient sequence and
the complex evaluation point. -/
theorem measurable_randomFockDeriv (n : ℕ) :
    Measurable (fun p : (ℕ → ℂ) × ℂ ↦ randomFockDeriv n p.1 p.2) := by
  let partialSum : ℕ → ((ℕ → ℂ) × ℂ) → ℂ := fun N p ↦
    ∑ m ∈ Finset.range N,
      clipDisk (p.1 (n + m)) * Real.sqrt ((n + m).factorial : ℝ) /
        (m.factorial : ℂ) * p.2 ^ m
  have hpartial : ∀ N, Measurable (partialSum N) := by
    intro N
    dsimp [partialSum]
    refine Finset.measurable_fun_sum (Finset.range N) fun m _ ↦ ?_
    have hcoord : Measurable (fun p : (ℕ → ℂ) × ℂ ↦ clipDisk (p.1 (n + m))) :=
      measurable_clipDisk.comp ((measurable_pi_apply (n + m)).comp measurable_fst)
    exact ((hcoord.mul_const (Real.sqrt ((n + m).factorial : ℝ) : ℂ)).div_const
      (m.factorial : ℂ)).mul (measurable_snd.pow_const m)
  apply measurable_of_tendsto_metrizable hpartial
  rw [tendsto_pi_nhds]
  intro p
  rw [randomFockDeriv_eq_tsum]
  exact (summable_fockIteratedSeries (fun k ↦ clipDisk (p.1 k))
    (fun k ↦ norm_clipDisk_le_one (p.1 k)) n p.2).hasSum.tendsto_sum_nat

/-- A bounded coefficient sequence reconstructed from every coordinate except `j`, with the
missing coordinate set to zero. -/
def clippedWithout (j : ℕ) (η : {k // k ≠ j} → ℂ) (k : ℕ) : ℂ :=
  if hk : k = j then 0 else clipDisk (η ⟨k, hk⟩)

@[simp]
theorem clippedWithout_self (j : ℕ) (η : {k // k ≠ j} → ℂ) :
    clippedWithout j η j = 0 := by
  simp [clippedWithout]

@[simp]
theorem clippedWithout_ne {j k : ℕ} (η : {k // k ≠ j} → ℂ) (hk : k ≠ j) :
    clippedWithout j η k = clipDisk (η ⟨k, hk⟩) := by
  simp [clippedWithout, hk]

theorem norm_clippedWithout_le_one (j : ℕ) (η : {k // k ≠ j} → ℂ) (k : ℕ) :
    ‖clippedWithout j η k‖ ≤ 1 := by
  by_cases hk : k = j
  · simp [clippedWithout, hk]
  · rw [clippedWithout_ne η hk]
    exact norm_clipDisk_le_one _

/-- `clippedWithout` packaged as a bounded Fock coefficient sequence. -/
def boundedClippedWithout (j : ℕ) (η : {k // k ≠ j} → ℂ) :
    BoundedFockCoefficients :=
  ⟨clippedWithout j η, norm_clippedWithout_le_one j η⟩

theorem measurable_boundedClippedWithout (j : ℕ) :
    Measurable (boundedClippedWithout j) := by
  refine (measurable_pi_iff.2 fun k ↦ ?_).subtype_mk
  by_cases hk : k = j
  · subst k
    simp
  · have hcoordinate : Measurable
        (fun η : ({q // q ≠ j} → ℂ) ↦ clipDisk (η ⟨k, hk⟩)) :=
      measurable_clipDisk.comp
        (measurable_pi_apply (X := fun _ : {q // q ≠ j} ↦ ℂ) ⟨k, hk⟩)
    simpa [boundedClippedWithout, clippedWithout, hk] using! hcoordinate

/-- The derivative remainder after deleting the floor saddle coordinate. -/
def randomFockRemainder (n : ℕ) (z : ℂ)
    (η : {k // k ≠ n + pointwiseSaddleIndex n z} → ℂ) : ℂ :=
  iteratedDeriv n
    (fockFunction (boundedClippedWithout (n + pointwiseSaddleIndex n z) η).1) z

theorem measurable_randomFockRemainder (n : ℕ) (z : ℂ) :
    Measurable (randomFockRemainder n z) := by
  exact (measurable_iteratedDeriv_fockFunction n z).comp
    (measurable_boundedClippedWithout (n + pointwiseSaddleIndex n z))

/-- Split a pointwise derivative series into one term and the series with that coefficient
deleted. -/
theorem pointwiseDerivativeSeries_split (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n m : ℕ) (z : ℂ) :
    pointwiseDerivativeSeries ξ n z =
      saddleMonomial n m z * ξ (n + m) +
        pointwiseDerivativeSeries (fun k ↦ if k = n + m then 0 else ξ k) n z := by
  rw [pointwiseDerivativeSeries,
    (summable_pointwiseDerivativeSeries hξ n z).tsum_eq_add_tsum_ite m,
    pointwiseDerivativeSeries]
  congr 1
  · ring
  · apply tsum_congr
    intro q
    by_cases hq : q = m
    · subst q
      simp
    · simp [hq]

/-- Exact decomposition of a random Fock derivative into its clipped floor saddle coordinate
and a measurable function of all complementary coordinates. -/
theorem randomFockDeriv_decomposition (n : ℕ) (ω : ℕ → ℂ) (z : ℂ) :
    randomFockDeriv n ω z =
      saddleMonomial n (pointwiseSaddleIndex n z) z *
          clipDisk (ω (n + pointwiseSaddleIndex n z)) +
        randomFockRemainder n z
          (fun i : {k // k ≠ n + pointwiseSaddleIndex n z} ↦ ω i) := by
  let m := pointwiseSaddleIndex n z
  let ξ : ℕ → ℂ := fun k ↦ clipDisk (ω k)
  have hξ : ∀ k, ‖ξ k‖ ≤ 1 := fun k ↦ norm_clipDisk_le_one (ω k)
  rw [randomFockDeriv, randomFock,
    ← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ n z,
    pointwiseDerivativeSeries_split ξ hξ n m z]
  congr 1
  rw [randomFockRemainder,
    ← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction
      (boundedClippedWithout (n + m)
        (fun i : {k // k ≠ n + m} ↦ ω i)).1
      (boundedClippedWithout (n + m)
        (fun i : {k // k ≠ n + m} ↦ ω i)).2 n z]
  apply tsum_congr
  intro q
  by_cases hq : q = m
  · subst q
    simp [boundedClippedWithout]
  · simp [boundedClippedWithout, clippedWithout, ξ]

/-- The affine field obtained by exposing the raw saddle coordinate and clipping every
complementary coordinate. -/
def randomFockAffineSaddle (n : ℕ) (z : ℂ) (ω : ℕ → ℂ) : ℂ :=
  saddleMonomial n (pointwiseSaddleIndex n z) z *
      ω (n + pointwiseSaddleIndex n z) +
    randomFockRemainder n z
      (fun i : {k // k ≠ n + pointwiseSaddleIndex n z} ↦ ω i)

theorem measurable_randomFockAffineSaddle (n : ℕ) (z : ℂ) :
    Measurable (randomFockAffineSaddle n z) := by
  exact (measurable_const.mul (measurable_pi_apply _)).add
    ((measurable_randomFockRemainder n z).comp <|
      measurable_pi_iff.2 fun i ↦ measurable_pi_apply i.1)

/-- On the full-measure support of the product law, the exposed raw coordinate is also
unchanged by clipping. -/
theorem randomFockDeriv_eq_affineSaddle_ae (n : ℕ) (z : ℂ) :
    (fun ω ↦ randomFockDeriv n ω z) =ᵐ[P] randomFockAffineSaddle n z := by
  filter_upwards [P_ae_coordinate_mem_closedBall (n + pointwiseSaddleIndex n z)] with ω hω
  rw [randomFockDeriv_decomposition, clipDisk_eq_self hω]
  rfl

/-- Pointwise logarithmic lower tail for the iid uniform-disk random Fock function. The
hypotheses are exactly the floor saddle range at the fixed pair `(n,z)`. -/
theorem P_pointwise_log_lowerTail
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hraw :
      P {ω | pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n} ≤
        ENNReal.ofReal (Real.exp (-2 * s)) := by
    simpa [P, randomFockAffineSaddle] using!
      infinitePi_pointwise_floor_lowerTail
        (fun _ : ℕ ↦ uniformDisk) (n + pointwiseSaddleIndex n z) rfl
        (randomFockRemainder n z) (measurable_randomFockRemainder n z)
        n z s hx hzn
  calc
    P {ω | pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
        s + pointwiseSaddleLoss n} =
        P {ω | pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n} := by
      apply measure_congr
      filter_upwards [randomFockDeriv_eq_affineSaddle_ae n z] with ω hω
      change
        (pointwisePotential n z - Real.log ‖randomFockDeriv n ω z‖ >
          s + pointwiseSaddleLoss n) =
        (pointwisePotential n z - Real.log ‖randomFockAffineSaddle n z ω‖ >
          s + pointwiseSaddleLoss n)
      rw [hω]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * s)) := hraw

end

end CofiniteDerivatives
