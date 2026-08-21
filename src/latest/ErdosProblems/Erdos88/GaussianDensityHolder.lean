import ErdosProblems.Erdos88.GaussianCommonEnvelope

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

noncomputable def threeSpectralQuarterBase (t : ℝ) : ℝ :=
  |t| ^ (1 / 4 : ℝ) * (1 + t ^ 2) ^ (-3 / 4 : ℝ)

lemma abs_rpow_quarter_le_one_add_sq_rpow (t : ℝ) :
    |t| ^ (1 / 4 : ℝ) ≤ (1 + t ^ 2) ^ (1 / 8 : ℝ) := by
  have hsq : |t| ^ (1 / 4 : ℝ) = (t ^ 2) ^ (1 / 8 : ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg t)]
    congr 1
    norm_num
  rw [hsq]
  exact Real.rpow_le_rpow (sq_nonneg t) (by linarith [sq_nonneg t]) (by norm_num)

lemma threeSpectralQuarterBase_le (t : ℝ) :
    threeSpectralQuarterBase t ≤ (1 + t ^ 2) ^ (-5 / 8 : ℝ) := by
  unfold threeSpectralQuarterBase
  calc
    |t| ^ (1 / 4 : ℝ) * (1 + t ^ 2) ^ (-3 / 4 : ℝ) ≤
        (1 + t ^ 2) ^ (1 / 8 : ℝ) *
          (1 + t ^ 2) ^ (-3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (abs_rpow_quarter_le_one_add_sq_rpow t)
        (Real.rpow_nonneg (by positivity) _)
    _ = (1 + t ^ 2) ^ (-5 / 8 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      norm_num

lemma threeSpectralQuarterBase_nonneg (t : ℝ) :
    0 ≤ threeSpectralQuarterBase t := by
  unfold threeSpectralQuarterBase
  positivity

lemma threeSpectralQuarterBase_integrable :
    Integrable threeSpectralQuarterBase := by
  have hmajor : Integrable (fun t : ℝ ↦ (1 + t ^ 2) ^ (-5 / 8 : ℝ)) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := ℝ) (μ := volume) (r := (5 / 4 : ℝ)) (by norm_num)
    convert h using 1 <;> norm_num [Real.norm_eq_abs, sq_abs]
  apply hmajor.mono
  · exact (continuous_abs.rpow_const (by norm_num)).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun t ↦ Or.inl (by
          change 1 + t ^ 2 ≠ 0
          positivity))) |>.aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (threeSpectralQuarterBase_nonneg t),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact threeSpectralQuarterBase_le t

noncomputable def threeSpectralQuarterMass (s : ℝ) : ℝ :=
  ∫ t : ℝ, |t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t

lemma integrable_abs_rpow_quarter_mul_threeSpectralEnvelope
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ ↦ |t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t) := by
  let R : ℝ := (2 * Real.sqrt s)⁻¹
  have hR : 0 < R := by dsimp only [R]; positivity
  have hscaled := threeSpectralQuarterBase_integrable.comp_div hR.ne'
  have hconst := hscaled.const_mul (R ^ (1 / 4 : ℝ))
  refine hconst.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [R, threeSpectralQuarterBase]
  unfold threeSpectralEnvelope
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hfirst :
      R ^ (1 / 4 : ℝ) * (|t| / R) ^ (1 / 4 : ℝ) = |t| ^ (1 / 4 : ℝ) := by
    rw [← Real.mul_rpow hR.le (div_nonneg (abs_nonneg t) hR.le)]
    congr 1
    field_simp [hR.ne']
  have hsecond : (t / R) ^ 2 = 4 * s * t ^ 2 := by
    dsimp only [R]
    field_simp [hsqrt.ne']
    rw [Real.sq_sqrt hs.le]
    ring
  have habsquot : |t / (2 * Real.sqrt s)⁻¹| = |t| / R := by
    rw [abs_div, abs_of_pos hR]
  rw [hsecond]
  rw [habsquot, ← mul_assoc, hfirst]

lemma threeSpectralQuarterMass_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ threeSpectralQuarterMass s := by
  unfold threeSpectralQuarterMass
  apply integral_nonneg
  intro t
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
    (threeSpectralEnvelope_nonneg hs t)

open BooleanSlices

lemma norm_exp_I_mul_sub_exp_I_mul_le_rpow_quarter (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) -
        Complex.exp (Complex.I * (b : ℂ))‖ ≤
      2 * |a - b| ^ (1 / 4 : ℝ) := by
  by_cases hle : |a - b| ≤ 1
  · calc
      ‖Complex.exp (Complex.I * (a : ℂ)) -
          Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| :=
        Erdos88.BooleanSlices.norm_exp_I_mul_sub_exp_I_mul_le a b
      _ ≤ |a - b| ^ (1 / 4 : ℝ) :=
        Real.self_le_rpow_of_le_one (abs_nonneg _) hle (by norm_num)
      _ ≤ 2 * |a - b| ^ (1 / 4 : ℝ) := by
        have hpow := Real.rpow_nonneg (abs_nonneg (a - b)) (1 / 4 : ℝ)
        nlinarith
  · have hbase : 1 ≤ |a - b| := le_of_lt (lt_of_not_ge hle)
    have hone : 1 ≤ |a - b| ^ (1 / 4 : ℝ) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow zero_le_one hbase (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc
      ‖Complex.exp (Complex.I * (a : ℂ)) -
          Complex.exp (Complex.I * (b : ℂ))‖ ≤ 2 :=
        Erdos88.BooleanSlices.norm_exp_I_mul_sub_exp_I_mul_le_two a b
      _ ≤ 2 * |a - b| ^ (1 / 4 : ℝ) := by nlinarith

lemma norm_inverseFourier_phase_sub_le_rpow_quarter (t x y : ℝ) :
    ‖Complex.exp (-(((t * x : ℝ) : ℂ) * Complex.I)) -
        Complex.exp (-(((t * y : ℝ) : ℂ) * Complex.I))‖ ≤
      2 * |t| ^ (1 / 4 : ℝ) * |x - y| ^ (1 / 4 : ℝ) := by
  have h := norm_exp_I_mul_sub_exp_I_mul_le_rpow_quarter (-t * x) (-t * y)
  convert h using 1
  · congr 2 <;> push_cast <;> ring
  · rw [show -t * x - -t * y = (-t) * (x - y) by ring, abs_mul,
      abs_neg, Real.mul_rpow (abs_nonneg t) (abs_nonneg (x - y))]
    ring

theorem inverseFourierDensityCandidate_holder_of_modulus_le_threeEnvelope
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (hmod : ∀ t, diagonalCharModulus a lam t ≤ threeSpectralEnvelope s t)
    (x y : ℝ) :
    |inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) x -
        inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam) y| ≤
      (threeSpectralQuarterMass s / Real.pi) * |x - y| ^ (1 / 4 : ℝ) := by
  let phi : ℝ → ℂ := diagonalCenteredCharProduct a lam
  let phase : ℝ → ℝ → ℂ := fun u t ↦
    Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))
  have hchar : Integrable phi :=
    diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
      a lam hs hmod
  have hphaseNorm (u t : ℝ) : ‖phi t * phase u t‖ = ‖phi t‖ := by
    dsimp only [phase]
    rw [norm_mul, Complex.norm_exp]
    simp
  have hphaseInt (u : ℝ) : Integrable (fun t ↦ phi t * phase u t) := by
    apply hchar.mono
    · exact ((continuous_diagonalCenteredCharProduct a lam).mul (by fun_prop)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [hphaseNorm]
  have hdiffInt : Integrable (fun t ↦ phi t * phase x t - phi t * phase y t) :=
    (hphaseInt x).sub (hphaseInt y)
  have hpoint (t : ℝ) :
      ‖phi t * phase x t - phi t * phase y t‖ ≤
        (2 * |x - y| ^ (1 / 4 : ℝ)) *
          (|t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t) := by
    rw [← mul_sub, norm_mul]
    have hphi : ‖phi t‖ ≤ threeSpectralEnvelope s t := by
      dsimp only [phi]
      rw [norm_diagonalCenteredCharProduct]
      exact hmod t
    have hphase : ‖phase x t - phase y t‖ ≤
        2 * |t| ^ (1 / 4 : ℝ) * |x - y| ^ (1 / 4 : ℝ) := by
      exact norm_inverseFourier_phase_sub_le_rpow_quarter t x y
    calc
      ‖phi t‖ * ‖phase x t - phase y t‖ ≤
          threeSpectralEnvelope s t *
            (2 * |t| ^ (1 / 4 : ℝ) * |x - y| ^ (1 / 4 : ℝ)) :=
        mul_le_mul hphi hphase (norm_nonneg _) (threeSpectralEnvelope_nonneg hs.le t)
      _ = (2 * |x - y| ^ (1 / 4 : ℝ)) *
          (|t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t) := by ring
  have hmajorInt : Integrable (fun t : ℝ ↦
      (2 * |x - y| ^ (1 / 4 : ℝ)) *
        (|t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t)) :=
    (integrable_abs_rpow_quarter_mul_threeSpectralEnvelope hs).const_mul _
  have hnormIntegral :
      ‖∫ t : ℝ, phi t * phase x t - phi t * phase y t‖ ≤
        (2 * |x - y| ^ (1 / 4 : ℝ)) * threeSpectralQuarterMass s := by
    calc
      ‖∫ t : ℝ, phi t * phase x t - phi t * phase y t‖ ≤
          ∫ t : ℝ, ‖phi t * phase x t - phi t * phase y t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (2 * |x - y| ^ (1 / 4 : ℝ)) *
          (|t| ^ (1 / 4 : ℝ) * threeSpectralEnvelope s t) := by
        apply integral_mono hdiffInt.norm hmajorInt
        exact hpoint
      _ = (2 * |x - y| ^ (1 / 4 : ℝ)) * threeSpectralQuarterMass s := by
        rw [integral_const_mul]
        rfl
  unfold inverseFourierDensityCandidate
  have hinter :
      (∫ t : ℝ, phi t * phase x t) - ∫ t : ℝ, phi t * phase y t =
        ∫ t : ℝ, phi t * phase x t - phi t * phase y t := by
    rw [integral_sub (hphaseInt x) (hphaseInt y)]
  change abs ((((((2 * Real.pi : ℝ) : ℂ))⁻¹ *
      (∫ t : ℝ, phi t * phase x t)).re) -
    (((((2 * Real.pi : ℝ) : ℂ))⁻¹ *
      (∫ t : ℝ, phi t * phase y t)).re)) ≤ _
  rw [← Complex.sub_re, ← mul_sub, hinter]
  calc
    abs (((((2 * Real.pi : ℝ) : ℂ))⁻¹ *
        (∫ t : ℝ, phi t * phase x t - phi t * phase y t)).re) ≤
        norm (((((2 * Real.pi : ℝ) : ℂ))⁻¹ *
          (∫ t : ℝ, phi t * phase x t - phi t * phase y t))) :=
      Complex.abs_re_le_norm _
    _ = (2 * Real.pi)⁻¹ *
        ‖∫ t : ℝ, phi t * phase x t - phi t * phase y t‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    _ ≤ (2 * Real.pi)⁻¹ *
        ((2 * |x - y| ^ (1 / 4 : ℝ)) * threeSpectralQuarterMass s) := by
      gcongr
    _ = (threeSpectralQuarterMass s / Real.pi) *
        |x - y| ^ (1 / 4 : ℝ) := by
      field_simp [Real.pi_ne_zero]

lemma diagonalCenteredLaw_absTail_le_optimized
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1) (r : ℝ) :
    (diagonalCenteredLaw a lam).real {z | r ≤ |z|} ≤
      2 * Real.exp (-r / 4 + 1 / 8) := by
  have hV : partialVariance a lam Finset.univ = 1 := by
    simpa only [partialVariance, totalVariance] using hsum
  have htail := diagonalPartialSum_absTail_le_optimized
    a lam Finset.univ (by rw [hV]; norm_num) (x := r)
  rw [hV, Real.sqrt_one] at htail
  norm_num at htail
  rw [← map_diagonalPartialSum_univ_eq_diagonalCenteredLaw a lam]
  have hset : MeasurableSet {z : ℝ | r ≤ |z|} :=
    measurableSet_Ici.preimage continuous_abs.measurable
  rw [measureReal_def, Measure.map_apply
    (continuous_diagonalPartialSum a lam Finset.univ).measurable hset]
  change ((Measure.pi fun _ : ι ↦ standardGaussian)
    {z | r ≤ |diagonalPartialSum a lam Finset.univ z|}).toReal ≤ _
  simpa only [measureReal_def] using htail

theorem density_le_exp_of_holder_and_quadratic_tail
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ → ℝ)
    (hdens : Erdos88.Esseen.HasContinuousDensity mu p)
    {L : ℝ} (hL : 0 ≤ L)
    (hholder : ∀ x y,
      |p x - p y| ≤ L * |x - y| ^ (1 / 4 : ℝ))
    (htail : ∀ r : ℝ,
      mu.real {z | r ≤ |z|} ≤ 2 * Real.exp (-r / 4 + 1 / 8))
    (y : ℝ) :
    p y ≤ (Real.exp (3 / 8) + L) * Real.exp (-|y| / 80) := by
  let d : ℝ := Real.exp (-|y| / 20)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdle : d ≤ 1 := by
    dsimp only [d]
    rw [← Real.exp_zero, Real.exp_le_exp]
    linarith [abs_nonneg y]
  have hdist {z : ℝ} (hz : z ∈ Icc (y - d) (y + d)) : |y - z| ≤ d := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hpoint (z : ℝ) (hz : z ∈ Icc (y - d) (y + d)) :
      p y ≤ p z + L * d ^ (1 / 4 : ℝ) := by
    have hpow := Real.rpow_le_rpow (abs_nonneg (y - z)) (hdist hz)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hhold := hholder y z
    have habs := le_abs_self (p y - p z)
    calc
      p y ≤ p z + |p y - p z| := by linarith
      _ ≤ p z + L * |y - z| ^ (1 / 4 : ℝ) := by gcongr
      _ ≤ p z + L * d ^ (1 / 4 : ℝ) := by gcongr
  have hpInt : IntervalIntegrable p volume (y - d) (y + d) :=
    hdens.intervalIntegrable _ _
  have hmajorInt : IntervalIntegrable
      (fun z ↦ p z + L * d ^ (1 / 4 : ℝ)) volume (y - d) (y + d) :=
    hpInt.add intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on (by linarith)
    intervalIntegrable_const hmajorInt hpoint
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add hpInt intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hball : Erdos88.Esseen.smallBall mu d y ≤
      2 * Real.exp (-|y| / 4 + 3 / 8) := by
    have hsubset : Icc (y - d) (y + d) ⊆ {z : ℝ | |y| - d ≤ |z|} := by
      intro z hz
      have habs := abs_sub_abs_le_abs_sub y z
      have := hdist hz
      change |y| - d ≤ |z|
      linarith
    have hmono : Erdos88.Esseen.smallBall mu d y ≤
        mu.real {z : ℝ | |y| - d ≤ |z|} := by
      exact measureReal_mono hsubset
    calc
      Erdos88.Esseen.smallBall mu d y ≤
          mu.real {z : ℝ | |y| - d ≤ |z|} := hmono
      _ ≤ 2 * Real.exp (- (|y| - d) / 4 + 1 / 8) := htail _
      _ ≤ 2 * Real.exp (-|y| / 4 + 3 / 8) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        linarith
  have hmass := hdens.smallBall_eq_integral d y hd.le
  have hraw : 2 * d * p y ≤
      2 * Real.exp (-|y| / 4 + 3 / 8) +
        2 * d * (L * d ^ (1 / 4 : ℝ)) := by
    rw [show y + d - (y - d) = 2 * d by ring] at hint
    rw [← hmass] at hint
    linarith
  have hdiv : p y ≤
      Real.exp (-|y| / 4 + 3 / 8) / d +
        L * d ^ (1 / 4 : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 2 * d)).mp
    calc
      p y * (2 * d) = 2 * d * p y := by ring
      _ ≤ 2 * Real.exp (-|y| / 4 + 3 / 8) +
          2 * d * (L * d ^ (1 / 4 : ℝ)) := hraw
      _ = (Real.exp (-|y| / 4 + 3 / 8) / d +
          L * d ^ (1 / 4 : ℝ)) * (2 * d) := by
        field_simp [hd.ne']
  have hfirst : Real.exp (-|y| / 4 + 3 / 8) / d =
      Real.exp (-|y| / 5 + 3 / 8) := by
    dsimp only [d]
    rw [← Real.exp_sub]
    congr 1
    ring
  have hquarter : d ^ (1 / 4 : ℝ) = Real.exp (-|y| / 80) := by
    dsimp only [d]
    rw [← Real.exp_mul]
    congr 1
    ring
  have hexp : Real.exp (-|y| / 5) ≤ Real.exp (-|y| / 80) := by
    rw [Real.exp_le_exp]
    linarith [abs_nonneg y]
  calc
    p y ≤ Real.exp (-|y| / 4 + 3 / 8) / d +
        L * d ^ (1 / 4 : ℝ) := hdiv
    _ = Real.exp (3 / 8) * Real.exp (-|y| / 5) +
        L * Real.exp (-|y| / 80) := by
      rw [hfirst, hquarter, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (3 / 8) * Real.exp (-|y| / 80) +
        L * Real.exp (-|y| / 80) := by gcongr
    _ = (Real.exp (3 / 8) + L) * Real.exp (-|y| / 80) := by ring

theorem smallBall_le_exp_of_density_exp
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ → ℝ)
    (hdens : Erdos88.Esseen.HasContinuousDensity mu p)
    {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ y, p y ≤ C * Real.exp (-|y| / 80))
    {eps : ℝ} (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) (x : ℝ) :
    Erdos88.Esseen.smallBall mu eps x ≤
      2 * eps * C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
  have hpoint (y : ℝ) (hy : y ∈ Icc (x - eps) (x + eps)) :
      p y ≤ C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
    have hdist : |x - y| ≤ eps := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have habs := abs_sub_abs_le_abs_sub x y
    have harg : -|y| / 80 ≤ 1 / 80 + (-|x| / 80) := by
      linarith
    calc
      p y ≤ C * Real.exp (-|y| / 80) := hp y
      _ ≤ C * Real.exp (1 / 80 + (-|x| / 80)) := by
        gcongr
      _ = C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
        rw [Real.exp_add]
        ring
  rw [hdens.smallBall_eq_integral eps x heps]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps),
          C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.intervalIntegrable _ _) intervalIntegrable_const hpoint
    _ = 2 * eps * C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

theorem smallBall_diagonalCenteredLaw_le_exp_of_relative_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    {eps : ℝ} (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) (x : ℝ) :
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
      2 * eps *
        (Real.exp (3 / 8) +
          threeSpectralQuarterMass (min rho 1 / 192) / Real.pi) *
        Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
  let s : ℝ := min rho 1 / 192
  let p : ℝ → ℝ :=
    inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam)
  have hs : 0 < s := by dsimp only [s]; positivity
  have hmod : ∀ t, diagonalCharModulus a lam t ≤
      threeSpectralEnvelope s t := by
    intro t
    exact diagonalCharModulus_le_relative_rankTwoEnvelope
      a lam hsum hrho htail t
  letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
    diagonalCenteredLaw_isProbabilityMeasure a lam
  have hchar : Integrable (charFun (diagonalCenteredLaw a lam)) := by
    rw [charFun_diagonalCenteredLaw]
    exact diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
      a lam hs hmod
  have hdens : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p := by
    have h := hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) hchar
    simpa only [p, charFun_diagonalCenteredLaw] using h
  let L : ℝ := threeSpectralQuarterMass s / Real.pi
  have hL : 0 ≤ L := div_nonneg
    (threeSpectralQuarterMass_nonneg hs.le) Real.pi_pos.le
  have hholder : ∀ y z, |p y - p z| ≤
      L * |y - z| ^ (1 / 4 : ℝ) := by
    intro y z
    exact inverseFourierDensityCandidate_holder_of_modulus_le_threeEnvelope
      a lam hs hmod y z
  have hp : ∀ y, p y ≤
      (Real.exp (3 / 8) + L) * Real.exp (-|y| / 80) :=
    density_le_exp_of_holder_and_quadratic_tail
      (diagonalCenteredLaw a lam) p hdens hL hholder
        (diagonalCenteredLaw_absTail_le_optimized a lam hsum)
  have hC : 0 ≤ Real.exp (3 / 8) + L :=
    add_nonneg (Real.exp_pos _).le hL
  simpa only [s, L, p] using
    smallBall_le_exp_of_density_exp
      (diagonalCenteredLaw a lam) p hdens hC hp heps hepsOne x

theorem exists_eta_diagonalCenteredLaw_nonuniform_of_relative_rankTwo_tail
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (a lam : ι → ℝ), totalVariance a lam = 1 →
        (∀ S : Finset ι, S.card ≤ 2 →
          rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2) →
        ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 → ∀ x : ℝ,
          Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
            (eps / eta) * Real.exp (-eta * |x|) := by
  let s : ℝ := min rho 1 / 192
  let C : ℝ := Real.exp (3 / 8) + threeSpectralQuarterMass s / Real.pi
  let A : ℝ := 2 * C * Real.exp (1 / 80)
  let eta : ℝ := min (1 / 160) A⁻¹
  have hs : 0 < s := by dsimp only [s]; positivity
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg (Real.exp_pos _)
      (div_nonneg (threeSpectralQuarterMass_nonneg hs.le) Real.pi_pos.le)
  have hA : 0 < A := by dsimp only [A]; positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaOne : eta < 1 :=
    lt_of_le_of_lt (min_le_left (1 / 160 : ℝ) A⁻¹) (by norm_num)
  refine ⟨eta, heta, hetaOne, ?_⟩
  intro ι _instFintype _instDecidableEq a lam hsum htail eps heps hepsOne x
  have hraw := smallBall_diagonalCenteredLaw_le_exp_of_relative_rankTwo_tail
    a lam hsum hrho htail heps.le hepsOne x
  have hetaRate : eta ≤ 1 / 80 := by
    exact (min_le_left (1 / 160 : ℝ) A⁻¹).trans (by norm_num)
  have hAeta : A ≤ eta⁻¹ := by
    have hetaInv : eta ≤ A⁻¹ := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hetaInv hA.le
    rw [inv_mul_cancel₀ hA.ne'] at hmul
    have hmul' : A * eta ≤ 1 := by nlinarith
    simpa only [one_div] using (le_div_iff₀ heta).2 hmul'
  have hexp : Real.exp (-|x| / 80) ≤ Real.exp (-eta * |x|) := by
    rw [Real.exp_le_exp]
    have habs := abs_nonneg x
    nlinarith
  calc
    Erdos88.Esseen.smallBall (diagonalCenteredLaw a lam) eps x ≤
        2 * eps * C * Real.exp (1 / 80) * Real.exp (-|x| / 80) := by
      simpa only [s, C] using hraw
    _ = eps * A * Real.exp (-|x| / 80) := by
      dsimp only [A]
      ring
    _ ≤ eps * eta⁻¹ * Real.exp (-eta * |x|) := by
      gcongr
    _ = (eps / eta) * Real.exp (-eta * |x|) := by
      rw [div_eq_mul_inv]

theorem exists_eta_gaussianQuadraticCenteredLaw_nonuniform_of_relative_robustRankThree
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ {n : ℕ} (f : Fin n → ℝ)
        {F : Matrix (Fin n) (Fin n) ℝ}, F.IsHermitian →
        ∀ {sigma : ℝ}, 0 < sigma →
          sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f →
          RobustRankAt 3 (rho * frobeniusSq F) F →
          ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 → ∀ x : ℝ,
            Erdos88.Esseen.smallBall
                ((gaussianQuadraticCenteredLaw f F).map
                  (fun z ↦ z / sigma)) eps x ≤
              (eps / eta) * Real.exp (-eta * |x|) := by
  obtain ⟨eta, heta, hetaOne, hdiag⟩ :=
    exists_eta_diagonalCenteredLaw_nonuniform_of_relative_rankTwo_tail rho hrho
  refine ⟨eta, heta, hetaOne, ?_⟩
  intro n f F hF sigma hsigma hsigmaSq hrob eps heps hepsOne x
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  have hsum : totalVariance a lam = 1 :=
    totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  have hrobTwo : RobustRankAt 2 (rho * frobeniusSq F) F :=
    robustRankAt_anti_rank (by norm_num) hrob
  have htail : ∀ S : Finset (Fin n), S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2 := by
    intro S hS
    have hraw := robustRankAt_eigenvalue_tail hF hrobTwo S hS
    have hsigmaSqPos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
    have htotal : (∑ i, (lam i) ^ 2) = frobeniusSq F / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div, sum_sq_eigenvalues_eq_frobeniusSq]
    have hout : (∑ i with i ∉ S, (lam i) ^ 2) =
        (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
    rw [htotal, hout]
    calc
      rho * (frobeniusSq F / sigma ^ 2) =
          (rho * frobeniusSq F) / sigma ^ 2 := by rw [mul_div_assoc]
      _ ≤ (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 :=
        (div_le_div_iff_of_pos_right hsigmaSqPos).2 hraw
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  exact hdiag a lam hsum htail heps hepsOne x

end Erdos88.GaussianQuadratic
