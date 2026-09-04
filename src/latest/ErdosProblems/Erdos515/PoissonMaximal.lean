import ErdosProblems.Erdos515.Prawitz
import ErdosProblems.Erdos515.CircleCutoff
import ErdosProblems.Erdos515.PoissonKernelBounds
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# A one-dimensional Hardy--Littlewood maximal estimate

This file contains the real-variable part of the Poisson maximal estimate used in the
Hardy--Littlewood step of the proof of Erdős Problem 515.  The maximal function is deliberately
defined directly, rather than through an external package: this keeps the analytic dependency
small and gives an explicit weak `(1,1)` constant on the real line.
-/

open Filter MeasureTheory Metric Set

open scoped ENNReal NNReal

namespace Erdos515
namespace Prawitz
namespace HardyLittlewood

noncomputable section

/-- The uncentred Hardy--Littlewood maximal function on the real line. -/
def ballAverage (u : ℝ → ℝ≥0∞) (z r : ℝ) : ℝ≥0∞ :=
  (volume (ball z r))⁻¹ * ∫⁻ y in ball z r, u y ∂volume

/-- The uncentred Hardy--Littlewood maximal function on the real line. -/
def globalMaximalFunction (u : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ z : ℝ, ⨆ r : ℝ,
    (ball z r).indicator (fun _ ↦ ballAverage u z r) x

/-- Every ball average containing `x` is bounded by the uncentred maximal function at `x`. -/
theorem laverage_le_globalMaximalFunction {u : ℝ → ℝ≥0∞} {x z r : ℝ}
    (hx : x ∈ ball z r) :
    ballAverage u z r ≤ globalMaximalFunction u x := by
  exact le_iSup_of_le z <| le_iSup_of_le r <| by simp [globalMaximalFunction, hx]

private def truncatedBalls (B : Set (ℝ × ℝ)) (k : ℕ) : Set (ℝ × ℝ) :=
  {i | i ∈ B ∧ 0 < i.2 ∧ i.2 ≤ k}

private lemma truncatedBalls_mono (B : Set (ℝ × ℝ)) : Monotone (truncatedBalls B) := by
  intro i j hij p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.trans (Nat.cast_le.mpr hij)⟩

private lemma volume_ball_four_le (z r : ℝ) :
    volume (ball z (4 * r)) ≤ 4 * volume (ball z r) := by
  rw [Real.volume_ball, Real.volume_ball]
  by_cases hr : 0 ≤ r
  · calc
      ENNReal.ofReal (2 * (4 * r)) = ENNReal.ofReal (4 * (2 * r)) := by congr 1 <;> ring
      _ = ENNReal.ofReal 4 * ENNReal.ofReal (2 * r) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 4 * ENNReal.ofReal (2 * r) := by norm_num
      _ ≤ 4 * ENNReal.ofReal (2 * r) := le_rfl
  · have hr' : r ≤ 0 := le_of_not_ge hr
    simp [ENNReal.ofReal_eq_zero.mpr, hr']

/-- The covering estimate behind weak type `(1,1)` on `ℝ`. -/
theorem measure_biUnion_ball_le_lintegral
    (B : Set (ℝ × ℝ)) (l : ℝ≥0∞) (u : ℝ → ℝ≥0∞)
    (hB : ∀ i ∈ B,
      l * volume (ball i.1 i.2) ≤ ∫⁻ x in ball i.1 i.2, u x ∂volume) :
    l * volume (⋃ i ∈ B, ball i.1 i.2) ≤ 4 * ∫⁻ x, u x ∂volume := by
  have htrunc (k : ℕ) :
      l * volume (⋃ i ∈ truncatedBalls B k, ball i.1 i.2) ≤
        4 * ∫⁻ x, u x ∂volume := by
    obtain ⟨D, hDB, hDdisj, hDcover⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_ball
        (truncatedBalls B k) Prod.fst Prod.snd k (fun i hi ↦ hi.2.2) 4 (by norm_num)
    have hDcount : D.Countable :=
      hDdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
        (fun i hi ↦ nonempty_ball.mpr ((hDB hi).2.1))
    let : Countable D := hDcount.to_subtype
    calc
      l * volume (⋃ i ∈ truncatedBalls B k, ball i.1 i.2) ≤
          l * volume (⋃ i ∈ D, ball i.1 (4 * i.2)) := by
        apply mul_le_mul le_rfl
        · apply measure_mono
          intro x hx
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          obtain ⟨j, hj, hij⟩ := hDcover i hi
          exact mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩
        · exact bot_le
        · exact bot_le
      _ ≤ l * ∑' i : D, volume (ball i.val.1 (4 * i.val.2)) := by
        gcongr
        exact measure_biUnion_le volume hDcount (fun i ↦ ball i.1 (4 * i.2))
      _ ≤ l * ∑' i : D, 4 * volume (ball i.val.1 i.val.2) := by
        gcongr
        exact volume_ball_four_le i.val.1 i.val.2
      _ = 4 * ∑' i : D, l * volume (ball i.val.1 i.val.2) := by
        simp_rw [ENNReal.tsum_mul_left]
        ac_rfl
      _ ≤ 4 * ∑' i : D, ∫⁻ x in ball i.val.1 i.val.2, u x ∂volume := by
        gcongr
        exact hB i.val ((hDB i.property).1)
      _ = 4 * ∫⁻ x in ⋃ i ∈ D, ball i.1 i.2, u x ∂volume := by
        have hunion : (⋃ i ∈ D, ball i.1 i.2) =
            ⋃ i : D, ball i.val.1 i.val.2 := by
          ext x
          simp
        rw [hunion]
        congr 1
        exact (lintegral_iUnion (fun i : D ↦ measurableSet_ball)
          (fun i j hij ↦ hDdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)) u).symm
      _ ≤ 4 * ∫⁻ x, u x ∂volume := by
        gcongr
        exact Measure.restrict_le_self
  have hsets :
      (⋃ i ∈ B, ball i.1 i.2) =
        ⋃ k, ⋃ i ∈ truncatedBalls B k, ball i.1 i.2 := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hiB, hxi⟩
      have hir : 0 < i.2 := pos_of_mem_ball hxi
      obtain ⟨k, hk⟩ := exists_nat_ge i.2
      exact ⟨k, i, ⟨hiB, hir, hk⟩, hxi⟩
    · rintro ⟨k, i, hi, hxi⟩
      exact ⟨i, hi.1, hxi⟩
  rw [hsets]
  have hmono : Monotone (fun k ↦ ⋃ i ∈ truncatedBalls B k, ball i.1 i.2) := by
    intro i j hij
    exact biUnion_mono (truncatedBalls_mono B hij) (fun _ _ ↦ Subset.rfl)
  rw [hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le htrunc

/-- Weak type `(1,1)` for the uncentred Hardy--Littlewood maximal function on `ℝ`. -/
theorem weak_type_globalMaximalFunction (u : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * volume {x | t < globalMaximalFunction u x} ≤
      4 * ∫⁻ x, u x ∂volume := by
  let B : Set (ℝ × ℝ) :=
    {i | t * volume (ball i.1 i.2) ≤ ∫⁻ y in ball i.1 i.2, u y ∂volume}
  calc
    t * volume {x | t < globalMaximalFunction u x} ≤
        t * volume (⋃ i ∈ B, ball i.1 i.2) := by
      gcongr
      intro x hx
      change t < globalMaximalFunction u x at hx
      rw [globalMaximalFunction] at hx
      obtain ⟨z, hz⟩ := lt_iSup_iff.mp hx
      obtain ⟨r, hr⟩ := lt_iSup_iff.mp hz
      have hxr : x ∈ ball z r := by
        by_contra hnot
        simp [hnot] at hr
      refine mem_iUnion₂.mpr ⟨(z, r), ?_, hxr⟩
      change t * volume (ball z r) ≤ ∫⁻ y in ball z r, u y ∂volume
      exact ENNReal.mul_le_of_le_div (by
        simpa [hxr, ballAverage, div_eq_mul_inv, mul_comm] using hr.le)
    _ ≤ 4 * ∫⁻ x, u x ∂volume :=
      measure_biUnion_ball_le_lintegral B t u (fun i hi ↦ hi)

/-- The dyadic envelope which occurs after decomposing the Poisson kernel into the regions
`|x-y| < 2^n δ`.  The numerical coefficient `8` is intentionally generous; it absorbs the
comparison between the disk Poisson kernel and the real Cauchy kernel. -/
def dyadicPoissonEnvelope (δ : ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, 8 * (2⁻¹ : ℝ≥0∞) ^ n * ballAverage u x ((2 : ℝ) ^ n * δ)

/-- A dyadic Poisson envelope is pointwise at most sixteen times the Hardy--Littlewood maximal
function. -/
theorem dyadicPoissonEnvelope_le (δ : ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) :
    dyadicPoissonEnvelope δ u x ≤ 16 * globalMaximalFunction u x := by
  calc
    dyadicPoissonEnvelope δ u x ≤
        ∑' n : ℕ, 8 * (2⁻¹ : ℝ≥0∞) ^ n * globalMaximalFunction u x := by
      apply ENNReal.tsum_le_tsum
      intro n
      gcongr
      rcases lt_or_ge 0 ((2 : ℝ) ^ n * δ) with hδ | hδ
      · apply laverage_le_globalMaximalFunction
        simpa [mem_ball] using hδ
      · simp [ballAverage, ball_eq_empty.2 hδ]
    _ = (8 * globalMaximalFunction u x) * ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
      simp_rw [show ∀ n : ℕ,
        8 * (2⁻¹ : ℝ≥0∞) ^ n * globalMaximalFunction u x =
          (8 * globalMaximalFunction u x) * (2⁻¹ : ℝ≥0∞) ^ n by
            intro n; ac_rfl]
      rw [ENNReal.tsum_mul_left]
    _ = (8 * globalMaximalFunction u x) * 2 := by rw [ENNReal.tsum_geometric_two]
    _ = 16 * globalMaximalFunction u x := by ring

/-- The weak `(1,1)` estimate for every dyadic Poisson envelope. -/
theorem weak_type_dyadicPoissonEnvelope (δ : ℝ) (u : ℝ → ℝ≥0∞) (t : ℝ≥0∞) :
    t * volume {x | t < dyadicPoissonEnvelope δ u x} ≤
      64 * ∫⁻ x, u x ∂volume := by
  rcases eq_or_ne t ∞ with rfl | ht
  · simp
  calc
    t * volume {x | t < dyadicPoissonEnvelope δ u x} ≤
        t * volume {x | t / 16 < globalMaximalFunction u x} := by
      apply mul_le_mul le_rfl
      · apply measure_mono
        intro x hx
        change t < dyadicPoissonEnvelope δ u x at hx
        change t / 16 < globalMaximalFunction u x
        apply (ENNReal.div_lt_iff (a := globalMaximalFunction u x)
          (b := (16 : ℝ≥0∞)) (c := t)
          (Or.inl (by norm_num : (16 : ℝ≥0∞) ≠ 0))
          (Or.inl (by norm_num : (16 : ℝ≥0∞) ≠ ∞))).2
        simpa [mul_comm] using hx.trans_le (dyadicPoissonEnvelope_le δ u x)
      · exact bot_le
      · exact bot_le
    _ = 16 * ((t / 16) * volume {x | t / 16 < globalMaximalFunction u x}) := by
      have ht_eq : t = 16 * (t / 16) :=
        (ENNReal.mul_div_cancel' (a := (16 : ℝ≥0∞)) (b := t)
          (by norm_num) (by norm_num)).symm
      exact (congrArg
        (fun a : ℝ≥0∞ ↦ a * volume {x | t / 16 < globalMaximalFunction u x}) ht_eq).trans
          (mul_assoc 16 (t / 16) (volume {x | t / 16 < globalMaximalFunction u x}))
    _ ≤ 16 * (4 * ∫⁻ x, u x ∂volume) := by
      exact mul_le_mul le_rfl (weak_type_globalMaximalFunction u (t / 16)) bot_le bot_le
    _ = 64 * ∫⁻ x, u x ∂volume := by ring

private lemma exists_dyadic_cauchy_bound {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ n : ℕ, |t| < (2 : ℝ) ^ n * δ ∧
      δ / (δ ^ 2 + t ^ 2) ≤ 4 / ((4 : ℝ) ^ n * δ) := by
  by_cases ht : |t| < δ
  · refine ⟨0, by simpa, ?_⟩
    norm_num
    rw [div_le_div_iff₀ (by positivity : 0 < δ ^ 2 + t ^ 2) hδ]
    nlinarith [sq_nonneg t, sq_pos_of_pos hδ]
  · have ht' : δ ≤ |t| := le_of_not_gt ht
    have hx : (1 : ℝ) ≤ |t| / δ := (le_div_iff₀ hδ).2 (by simpa using ht')
    obtain ⟨n, hnlow, hnhigh⟩ :=
      exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine ⟨n + 1, (div_lt_iff₀ hδ).1 hnhigh, ?_⟩
    have hlower : (2 : ℝ) ^ n * δ ≤ |t| := (le_div_iff₀ hδ).1 hnlow
    have hsquare : ((2 : ℝ) ^ n * δ) ^ 2 ≤ t ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (by positivity : 0 ≤ (2 : ℝ) ^ n * δ) (abs_nonneg t)).2 hlower
    have hright : 0 < ((2 : ℝ) ^ n) ^ 2 * δ := by positivity
    have hrewrite :
        4 / ((4 : ℝ) ^ (n + 1) * δ) = 1 / (((2 : ℝ) ^ n) ^ 2 * δ) := by
      rw [pow_succ]
      have hp : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
      rw [hp]
      field_simp
    rw [hrewrite, div_le_div_iff₀ (by positivity : 0 < δ ^ 2 + t ^ 2) hright]
    nlinarith [sq_pos_of_pos hδ]

/-- The real Cauchy approximate identity convolved with nonnegative data. -/
def cauchyConvolution (δ : ℝ) (u : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (δ / (δ ^ 2 + (y - x) ^ 2)) * u y ∂volume

private lemma cauchy_density_le_dyadic_density {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (x : ℝ) :
    ENNReal.ofReal (4 / ((4 : ℝ) ^ n * δ)) ≤
      8 * (2⁻¹ : ℝ≥0∞) ^ n * (volume (ball x ((2 : ℝ) ^ n * δ)))⁻¹ := by
  rw [Real.volume_ball]
  rw [ENNReal.ofReal_le_iff_le_toReal]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((2 : ℝ) ^ n * δ))]
    field_simp
    have hp : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hp, div_pow]
    norm_num
    field_simp
    norm_num
  · finiteness

/-- The Cauchy approximate identity is bounded pointwise by the dyadic Poisson envelope. -/
theorem cauchyConvolution_le_dyadicPoissonEnvelope {δ : ℝ} (hδ : 0 < δ)
    {u : ℝ → ℝ≥0∞} (hu : Measurable u) (x : ℝ) :
    cauchyConvolution δ u x ≤ dyadicPoissonEnvelope δ u x := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n y ↦
    (ball x ((2 : ℝ) ^ n * δ)).indicator
      (fun y ↦ (8 * (2⁻¹ : ℝ≥0∞) ^ n *
        (volume (ball x ((2 : ℝ) ^ n * δ)))⁻¹) * u y) y
  calc
    cauchyConvolution δ u x ≤ ∫⁻ y, ∑' n : ℕ, F n y ∂volume := by
      apply lintegral_mono
      intro y
      obtain ⟨n, hnball, hnkernel⟩ := exists_dyadic_cauchy_bound hδ (y - x)
      have hyball : y ∈ ball x ((2 : ℝ) ^ n * δ) := by
        rw [mem_ball, Real.dist_eq]
        simpa [abs_sub_comm] using hnball
      calc
        ENNReal.ofReal (δ / (δ ^ 2 + (y - x) ^ 2)) * u y ≤
            ENNReal.ofReal (4 / ((4 : ℝ) ^ n * δ)) * u y :=
          mul_le_mul (ENNReal.ofReal_le_ofReal hnkernel) le_rfl bot_le bot_le
        _ ≤ (8 * (2⁻¹ : ℝ≥0∞) ^ n *
              (volume (ball x ((2 : ℝ) ^ n * δ)))⁻¹) * u y :=
          mul_le_mul (cauchy_density_le_dyadic_density hδ n x) le_rfl bot_le bot_le
        _ = F n y := by simp [F, hyball]
        _ ≤ ∑' n : ℕ, F n y := ENNReal.le_tsum n
    _ = ∑' n : ℕ, ∫⁻ y, F n y ∂volume := by
      rw [lintegral_tsum]
      intro n
      exact (((measurable_const.mul hu).indicator measurableSet_ball).aemeasurable)
    _ = dyadicPoissonEnvelope δ u x := by
      unfold dyadicPoissonEnvelope ballAverage
      apply tsum_congr
      intro n
      rw [show (∫⁻ y, F n y ∂volume) =
          (8 * (2⁻¹ : ℝ≥0∞) ^ n *
            (volume (ball x ((2 : ℝ) ^ n * δ)))⁻¹) *
              ∫⁻ y in ball x ((2 : ℝ) ^ n * δ), u y ∂volume by
        rw [show F n = (ball x ((2 : ℝ) ^ n * δ)).indicator
            (fun y ↦ (8 * (2⁻¹ : ℝ≥0∞) ^ n *
              (volume (ball x ((2 : ℝ) ^ n * δ)))⁻¹) * u y) by rfl]
        rw [lintegral_indicator measurableSet_ball]
        exact lintegral_const_mul _ hu]
      ring

/-- The normalized disk Poisson kernel written as a function of the angular difference. -/
def normalizedPoissonKernel (ρ t : ℝ) : ℝ :=
  (1 - ρ ^ 2) / (1 + ρ ^ 2 - 2 * ρ * Real.cos t)

private lemma normalized_denominator_eq (ρ t : ℝ) :
    1 + ρ ^ 2 - 2 * ρ * Real.cos t =
      (1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2 := by
  rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul_eq_one_sub]
  ring_nf

/-- On the principal angular interval the disk Poisson kernel is bounded by a fixed multiple of
the real Cauchy kernel.  The constant `256` is deliberately non-optimal, which keeps the two
elementary regimes `ρ ≤ 1/2` and `ρ ≥ 1/2` uniform. -/
theorem normalizedPoissonKernel_le_cauchy {ρ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ht : |t| ≤ Real.pi) :
    normalizedPoissonKernel ρ t ≤
      256 * ((1 - ρ) / ((1 - ρ) ^ 2 + t ^ 2)) := by
  have hδ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have ht_sq : t ^ 2 ≤ Real.pi ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg t) Real.pi_pos.le).2 ht
  have hpi_sq : Real.pi ^ 2 ≤ 16 := by
    simpa [show (4 : ℝ) ^ 2 = 16 by norm_num] using
      (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 4)).2 Real.pi_le_four
  have hE : 0 < (1 - ρ) ^ 2 + t ^ 2 := by positivity
  rw [normalizedPoissonKernel, normalized_denominator_eq]
  have hD : 0 < (1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2 := by
    positivity
  rw [div_le_iff₀ hD]
  rw [show 256 * ((1 - ρ) / ((1 - ρ) ^ 2 + t ^ 2)) *
      ((1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2) =
      (256 * (1 - ρ) * ((1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2)) /
        ((1 - ρ) ^ 2 + t ^ 2) by field_simp]
  rw [le_div_iff₀ hE]
  by_cases hρhalf : ρ ≤ (1 : ℝ) / 2
  · have hδhalf : (1 : ℝ) / 2 ≤ 1 - ρ := by linarith
    have hDlower : (1 - ρ) ^ 2 ≤
        (1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2 := by
      nlinarith [mul_nonneg hρ0 (sq_nonneg (Real.sin (t / 2)))]
    have hEupper : (1 - ρ) ^ 2 + t ^ 2 ≤ 17 := by
      nlinarith [sq_nonneg (1 - ρ), ht_sq, hpi_sq]
    nlinarith [sq_nonneg (1 - ρ), sq_nonneg (Real.sin (t / 2))]
  · have hρhalf' : (1 : ℝ) / 2 ≤ ρ := le_of_not_ge hρhalf
    have ht_half : |t / 2| ≤ Real.pi / 2 := by
      rw [abs_div]
      norm_num
      exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 ht
    have hJordan := Real.mul_abs_le_abs_sin ht_half
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hsin_sq : t ^ 2 / 16 ≤ Real.sin (t / 2) ^ 2 := by
      have hsnonneg : 0 ≤ |Real.sin (t / 2)| := abs_nonneg _
      have hleftnonneg : 0 ≤ |t| / Real.pi := div_nonneg (abs_nonneg _) hpi_pos.le
      have hj' : |t| / Real.pi ≤ |Real.sin (t / 2)| := by
        calc
          |t| / Real.pi = (2 / Real.pi) * (|t| / 2) := by field_simp
          _ = (2 / Real.pi) * |t / 2| := by rw [abs_div]; norm_num
          _ ≤ |Real.sin (t / 2)| := hJordan
      have hsquare := (sq_le_sq₀ hleftnonneg hsnonneg).2 hj'
      have hpi16 : Real.pi ^ 2 ≤ 16 := hpi_sq
      have hpi_ne : Real.pi ≠ 0 := hpi_pos.ne'
      rw [div_pow, sq_abs] at hsquare
      calc
        t ^ 2 / 16 ≤ t ^ 2 / Real.pi ^ 2 := by
          exact div_le_div_of_nonneg_left (sq_nonneg t) (sq_pos_of_pos hpi_pos) hpi16
        _ ≤ Real.sin (t / 2) ^ 2 := by simpa [sq_abs] using hsquare
    have hDlower : (1 - ρ) ^ 2 + t ^ 2 / 8 ≤
        (1 - ρ) ^ 2 + 4 * ρ * Real.sin (t / 2) ^ 2 := by
      nlinarith [sq_nonneg (Real.sin (t / 2))]
    nlinarith [sq_nonneg (1 - ρ), sq_nonneg t, sq_nonneg (Real.sin (t / 2))]

private lemma norm_circlePoint_sub_sq (R r x θ : ℝ) :
    ‖circlePoint R x - circlePoint r θ‖ ^ 2 =
      R ^ 2 + r ^ 2 - 2 * R * r * Real.cos (x - θ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp only [circlePoint, map_mul, Complex.normSq_apply, Complex.exp_re,
    Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  simp [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq θ]

/-- The geometric disk Poisson kernel agrees with the normalized angular kernel. -/
theorem poissonKernel_circlePoint_eq_normalized {R r x θ : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) :
    poissonKernel 0 (circlePoint r θ) (circlePoint R x) =
      normalizedPoissonKernel (r / R) (x - θ) := by
  rw [poissonKernel_def]
  simp only [sub_zero]
  rw [norm_circlePoint_sub_sq]
  simp only [normalizedPoissonKernel, circlePoint, Complex.norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    abs_of_nonneg hR.le]
  field_simp

/-- The Poisson formula, after taking norms and shifting the angular interval to be centred at
`θ`. -/
theorem poisson_enorm_le_lintegral {q : ℂ → ℂ} {R r θ : ℝ}
    (hq : DiffContOnCl ℂ q (ball 0 R)) (hR : 0 < R)
    (hr0 : 0 ≤ r) (hrR : r < R) :
    ENNReal.ofReal ‖q (circlePoint r θ)‖ ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹) *
        ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (poissonKernel 0 (circlePoint r θ)
            (circlePoint R (x + (θ - Real.pi)))) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ := by
  have hw : circlePoint r θ ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    simp [circlePoint, Complex.norm_exp, abs_of_nonneg hr0, hrR]
  have hp := hq.circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_eq_integral_add (θ - Real.pi)] at hp
  simp only [circleMap, zero_add] at hp
  rw [ofReal_norm]
  rw [← hp]
  calc
    ‖(2 * Real.pi)⁻¹ •
        ∫ x in (0 : ℝ)..2 * Real.pi,
          poissonKernel 0 (circlePoint r θ)
            (circlePoint R (x + (θ - Real.pi))) •
            q (circlePoint R (x + (θ - Real.pi)))‖ₑ ≤
        ‖(2 * Real.pi)⁻¹‖ₑ *
          ‖∫ x in (0 : ℝ)..2 * Real.pi,
            poissonKernel 0 (circlePoint r θ)
              (circlePoint R (x + (θ - Real.pi))) •
              q (circlePoint R (x + (θ - Real.pi)))‖ₑ := by
      exact enorm_smul_le
    _ ≤ ‖(2 * Real.pi)⁻¹‖ₑ *
        ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
          ‖poissonKernel 0 (circlePoint r θ)
              (circlePoint R (x + (θ - Real.pi))) •
              q (circlePoint R (x + (θ - Real.pi)))‖ₑ := by
      gcongr
      rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      exact enorm_integral_le_lintegral_enorm _
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
        ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (poissonKernel 0 (circlePoint r θ)
            (circlePoint R (x + (θ - Real.pi)))) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ := by
      congr 1
      · rw [Real.enorm_eq_ofReal]
        positivity
      · apply lintegral_congr
        intro x
        rw [enorm_smul]
        simp only [Real.enorm_eq_ofReal_abs]
        rw [← ofReal_norm (q (circlePoint R (x + (θ - Real.pi))))]
        congr 1
        rw [abs_of_nonneg]
        rw [poissonKernel_def]
        apply div_nonneg
        · simp only [sub_zero, circlePoint, Complex.norm_mul,
            Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg hR.le]
          nlinarith [sq_nonneg (R - r)]
        · positivity

private theorem shifted_poisson_lintegral_le_cauchy {q : ℂ → ℂ} {R r θ : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hrR : r < R)
    (hboundary : Continuous (boundaryNorm q R))
    (hθ : θ ∈ angularInterval) :
    (∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (poissonKernel 0 (circlePoint r θ)
          (circlePoint R (x + (θ - Real.pi)))) *
        ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖) ≤
      256 * ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal ((1 - r / R) /
          ((1 - r / R) ^ 2 + (x - Real.pi) ^ 2)) *
        threePeriodCutoff q R (x + (θ - Real.pi)) := by
  rw [← lintegral_const_mul]
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have ht : |x - Real.pi| ≤ Real.pi := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hρ0 : 0 ≤ r / R := div_nonneg hr0 hR.le
    have hρ1 : r / R < 1 := (div_lt_one hR).2 hrR
    have hkernel := normalizedPoissonKernel_le_cauchy hρ0 hρ1 ht
    have hangle : x + (θ - Real.pi) - θ = x - Real.pi := by ring
    have hywindow : x + (θ - Real.pi) ∈ Icc (θ - Real.pi) (θ + Real.pi) := by
      constructor <;> linarith [hx.1, hx.2]
    rw [poissonKernel_circlePoint_eq_normalized hR hr0, hangle]
    rw [threePeriodCutoff_eq_boundaryNorm hθ hywindow]
    unfold boundaryNorm
    calc
      ENNReal.ofReal (normalizedPoissonKernel (r / R) (x - Real.pi)) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ ≤
        ENNReal.ofReal (256 * ((1 - r / R) /
          ((1 - r / R) ^ 2 + (x - Real.pi) ^ 2))) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hkernel) le_rfl bot_le bot_le
      _ = 256 * (ENNReal.ofReal ((1 - r / R) /
          ((1 - r / R) ^ 2 + (x - Real.pi) ^ 2)) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
        norm_num
        ring
  · exact (by fun_prop : Measurable (fun x : ℝ ↦
      ENNReal.ofReal ((1 - r / R) / ((1 - r / R) ^ 2 + (x - Real.pi) ^ 2)))).mul
        ((measurable_threePeriodCutoff hboundary).comp (by fun_prop))

private theorem shifted_cauchy_lintegral_le_cauchyConvolution
    (δ : ℝ) (u : ℝ → ℝ≥0∞) (θ : ℝ) :
    (∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (δ / (δ ^ 2 + (x - Real.pi) ^ 2)) *
          u (x + (θ - Real.pi))) ≤ cauchyConvolution δ u θ := by
  let d : ℝ := θ - Real.pi
  let f : ℝ → ℝ≥0∞ := fun y ↦
    ENNReal.ofReal (δ / (δ ^ 2 + (y - θ) ^ 2)) * u y
  have htranslate := (measurePreserving_add_right volume d).setLIntegral_comp_emb
    (measurableEmbedding_addRight d) f (Ioc (0 : ℝ) (2 * Real.pi))
  have hEq :
      (∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
        ENNReal.ofReal (δ / (δ ^ 2 + (x - Real.pi) ^ 2)) *
          u (x + (θ - Real.pi))) =
      ∫⁻ y in Ioc (θ - Real.pi) (θ + Real.pi),
        ENNReal.ofReal (δ / (δ ^ 2 + (y - θ) ^ 2)) * u y := by
    simpa only [d, f, Set.image_add_const_Ioc, zero_add,
      show (2 * Real.pi + (θ - Real.pi) : ℝ) = θ + Real.pi by ring,
      show ∀ x : ℝ, x + (θ - Real.pi) - θ = x - Real.pi by intro x; ring]
      using htranslate
  rw [hEq]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

/-- A fixed radial value of a holomorphic function is controlled by the real-line
Hardy--Littlewood maximal function of its three-period boundary cutoff.  All constants are
absolute; the deliberately generous value `4096 = 256 * 16` keeps the analytic and real-variable
parts separate. -/
theorem circlePoint_enorm_le_globalMaximalFunction {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {R r θ : ℝ}
    (hR0 : 0 < R) (hR1 : R < 1) (hr0 : 0 ≤ r) (hrR : r < R)
    (hθ : θ ∈ angularInterval) :
    ENNReal.ofReal ‖q (circlePoint r θ)‖ ≤
      4096 * globalMaximalFunction (threePeriodCutoff q R) θ := by
  have hqR : DiffContOnCl ℂ q (ball 0 R) :=
    hq.diffContOnCl_ball (closedBall_subset_ball hR1)
  have hboundary : Continuous (boundaryNorm q R) := by
    apply Continuous.norm
    apply hq.continuousOn.comp_continuous
    · unfold circlePoint
      fun_prop
    · intro x
      rw [mem_ball_zero_iff]
      rw [show ‖circlePoint R x‖ = |R| by simp [circlePoint, Complex.norm_exp]]
      rw [abs_of_pos hR0]
      exact hR1
  have hδ : 0 < 1 - r / R := sub_pos.mpr ((div_lt_one hR0).2 hrR)
  have hcutoff : Measurable (threePeriodCutoff q R) :=
    measurable_threePeriodCutoff hboundary
  have hnormalization : ENNReal.ofReal ((2 * Real.pi)⁻¹) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    apply inv_le_one_of_one_le₀
    nlinarith [Real.two_le_pi]
  calc
    ENNReal.ofReal ‖q (circlePoint r θ)‖ ≤
        ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (poissonKernel 0 (circlePoint r θ)
              (circlePoint R (x + (θ - Real.pi)))) *
            ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ :=
      poisson_enorm_le_lintegral hqR hR0 hr0 hrR
    _ ≤ ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal (poissonKernel 0 (circlePoint r θ)
            (circlePoint R (x + (θ - Real.pi)))) *
          ENNReal.ofReal ‖q (circlePoint R (x + (θ - Real.pi)))‖ :=
      mul_le_of_le_one_left bot_le hnormalization
    _ ≤ 256 * ∫⁻ x in Ioc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal ((1 - r / R) /
            ((1 - r / R) ^ 2 + (x - Real.pi) ^ 2)) *
          threePeriodCutoff q R (x + (θ - Real.pi)) :=
      shifted_poisson_lintegral_le_cauchy hR0 hr0 hrR hboundary hθ
    _ ≤ 256 * cauchyConvolution (1 - r / R) (threePeriodCutoff q R) θ := by
      exact mul_le_mul le_rfl
        (shifted_cauchy_lintegral_le_cauchyConvolution
          (1 - r / R) (threePeriodCutoff q R) θ) bot_le bot_le
    _ ≤ 256 * dyadicPoissonEnvelope (1 - r / R) (threePeriodCutoff q R) θ := by
      exact mul_le_mul le_rfl
        (cauchyConvolution_le_dyadicPoissonEnvelope hδ hcutoff θ) bot_le bot_le
    _ ≤ 256 * (16 * globalMaximalFunction (threePeriodCutoff q R) θ) := by
      exact mul_le_mul le_rfl
        (dyadicPoissonEnvelope_le (1 - r / R) (threePeriodCutoff q R) θ) bot_le bot_le
    _ = 4096 * globalMaximalFunction (threePeriodCutoff q R) θ := by ring

/-- Weak `(1,1)` control of the supremum over every radius below a fixed outer circle. -/
theorem weak_type_circlePoint_sup {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {R : ℝ}
    (hR0 : 0 < R) (hR1 : R < 1) (t : ℝ≥0∞) :
    t * volume (angularInterval ∩
      {θ | ∃ r ∈ Ioo (0 : ℝ) R, t < ENNReal.ofReal ‖q (circlePoint r θ)‖}) ≤
      16384 * ∫⁻ x, threePeriodCutoff q R x ∂volume := by
  rcases eq_or_ne t ∞ with rfl | ht
  · simp
  calc
    t * volume (angularInterval ∩
        {θ | ∃ r ∈ Ioo (0 : ℝ) R, t < ENNReal.ofReal ‖q (circlePoint r θ)‖}) ≤
        t * volume {θ | t / 4096 <
          globalMaximalFunction (threePeriodCutoff q R) θ} := by
      apply mul_le_mul le_rfl
      · apply measure_mono
        rintro θ ⟨hθ, r, hr, hvalue⟩
        change t / 4096 < globalMaximalFunction (threePeriodCutoff q R) θ
        apply (ENNReal.div_lt_iff (a := globalMaximalFunction (threePeriodCutoff q R) θ)
          (b := (4096 : ℝ≥0∞)) (c := t)
          (Or.inl (by norm_num : (4096 : ℝ≥0∞) ≠ 0))
          (Or.inl (by norm_num : (4096 : ℝ≥0∞) ≠ ∞))).2
        simpa [mul_comm] using hvalue.trans_le
          (circlePoint_enorm_le_globalMaximalFunction hq hR0 hR1 hr.1.le hr.2 hθ)
      · exact bot_le
      · exact bot_le
    _ = 4096 * ((t / 4096) * volume {θ | t / 4096 <
          globalMaximalFunction (threePeriodCutoff q R) θ}) := by
      have ht_eq : t = 4096 * (t / 4096) :=
        (ENNReal.mul_div_cancel' (a := (4096 : ℝ≥0∞)) (b := t)
          (by norm_num) (by norm_num)).symm
      exact (congrArg (fun a : ℝ≥0∞ ↦ a * volume {θ | t / 4096 <
          globalMaximalFunction (threePeriodCutoff q R) θ}) ht_eq).trans
        (mul_assoc 4096 (t / 4096) (volume {θ | t / 4096 <
          globalMaximalFunction (threePeriodCutoff q R) θ}))
    _ ≤ 4096 * (4 * ∫⁻ x, threePeriodCutoff q R x ∂volume) := by
      exact mul_le_mul le_rfl
        (weak_type_globalMaximalFunction (threePeriodCutoff q R) (t / 4096)) bot_le bot_le
    _ = 16384 * ∫⁻ x, threePeriodCutoff q R x ∂volume := by ring

end

end HardyLittlewood
end Prawitz
end Erdos515
