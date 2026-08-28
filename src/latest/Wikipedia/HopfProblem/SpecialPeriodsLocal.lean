import Wikipedia.HopfProblem.PeriodFamily
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Explicit local solutions of the elliptic period equations

Proposition 3.11 constructs local sections of the affine period problem at the
two elliptic points by `μ₁ = (2 - τ) / 3` and `μ₂ = (1 - τ) / 2`.  These local
sections also admit the explicit choices `β₁ = 2τ/3 - i` and `β₂ = 3τ/2 - i`.
Their discriminant is identically `-1`.

We construct concrete holomorphic disc models for both triples.  The first
parameter has a simple zero relative to `ρ`, and the second has a double zero
relative to `i`, with the order-three and order-four elliptic equivariance,
respectively.  This establishes local analytic solvability; it does not identify
these local triples with restrictions of a global solution of Theorem 3.4.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The upper-half-plane fixed point `exp(π i / 3)`, in algebraic coordinates. -/
def rho : ℂ := (1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2

@[simp] theorem rho_re : rho.re = 1 / 2 := by
  norm_num [rho, Complex.div_re, Complex.normSq_apply]

@[simp] theorem rho_im : rho.im = Real.sqrt 3 / 2 := by
  norm_num [rho, Complex.div_im, Complex.normSq_apply]

theorem rho_im_pos : 0 < rho.im := by
  rw [rho_im]
  positivity

theorem rho_eq_exp : rho = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  unfold rho
  ring

theorem rho_sq : rho ^ 2 = rho - 1 := by
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, rho_re, rho_im, Complex.sub_re, Complex.one_re]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · simp only [pow_two, Complex.mul_im, rho_re, rho_im, Complex.sub_im, Complex.one_im]
    ring

theorem norm_rho : ‖rho‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, Complex.sq_norm, Complex.normSq_apply,
    rho_re, rho_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem rho_cube : rho ^ 3 = -1 := by
  calc
    rho ^ 3 = rho * rho ^ 2 := by ring
    _ = rho * (rho - 1) := by rw [rho_sq]
    _ = -1 := by linear_combination rho_sq

theorem conj_rho : starRingEnd ℂ rho = 1 - rho := by
  apply Complex.ext <;> simp
  ring

/-- A Cayley coordinate taking zero to a prescribed upper-half-plane point. -/
def cayley (a z : ℂ) : ℂ := (a - starRingEnd ℂ a * z) / (1 - z)

@[simp] theorem cayley_zero (a : ℂ) : cayley a 0 = a := by
  simp [cayley]

theorem one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hz

theorem cayley_im (a z : ℂ) :
    (cayley a z).im = a.im * (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  simp only [cayley, Complex.div_im, Complex.sub_im, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.normSq_apply]
  ring

theorem cayley_im_pos {a z : ℂ} (ha : 0 < a.im) (hz : ‖z‖ < 1) :
    0 < (cayley a z).im := by
  rw [cayley_im]
  apply div_pos
  · apply mul_pos ha
    rw [sub_pos, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hz)

theorem cayley_contDiffOn (a : ℂ) :
    ContDiffOn ℂ ω (cayley a) (Metric.ball 0 1) := by
  apply ContDiffOn.div
  · exact contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id)
  · exact contDiffOn_const.sub contDiffOn_id
  · intro z hz
    exact one_sub_ne_zero_of_norm_lt_one (by simpa using hz)

/-- The local section at the order-three point used in Proposition 3.11,
completed by an explicit solution of its beta equation. -/
def sectionThree (τ : ℂ) : PeriodPoint :=
  ⟨τ, (2 - τ) / 3, 2 * τ / 3 - Complex.I⟩

/-- The local section at the order-four point used in Proposition 3.11,
completed by an explicit solution of its beta equation. -/
def sectionFour (τ : ℂ) : PeriodPoint :=
  ⟨τ, (1 - τ) / 2, 3 * τ / 2 - Complex.I⟩

theorem sectionThree_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionThree τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionThree, PeriodPoint.discriminant]
  field_simp
  ring

theorem sectionFour_discriminant (τ : ℂ) (hτ : τ.im ≠ 0) :
    (sectionFour τ).discriminant = -1 := by
  apply mul_left_cancel₀ hτ
  simp [sectionFour, PeriodPoint.discriminant]
  field_simp
  ring

theorem sectionThree_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionThree τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionThree_discriminant τ hτ.ne']
  norm_num

theorem sectionFour_admissible {τ : ℂ} (hτ : 0 < τ.im) :
    (sectionFour τ).Admissible := by
  refine ⟨hτ, ?_⟩
  rw [sectionFour_discriminant τ hτ.ne']
  norm_num

theorem sectionThree_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionThree τ).step₁ = sectionThree ((τ - 1) / τ) := by
  apply PeriodPoint.ext <;> simp [sectionThree, PeriodPoint.step₁] <;> field_simp <;> ring

theorem sectionFour_step (τ : ℂ) (hτ : τ ≠ 0) :
    (sectionFour τ).step₂ = sectionFour (-1 / τ) := by
  apply PeriodPoint.ext <;> simp [sectionFour, PeriodPoint.step₂] <;> field_simp <;> ring

/-- The negative order-three rotation in the paper's linearising coordinate. -/
def rotateThree (z : ℂ) : ℂ := -rho * z

/-- The negative order-four rotation in the paper's linearising coordinate. -/
def rotateFour (z : ℂ) : ℂ := -Complex.I * z

@[simp] theorem norm_rotateThree (z : ℂ) : ‖rotateThree z‖ = ‖z‖ := by
  simp [rotateThree, norm_rho]

@[simp] theorem norm_rotateFour (z : ℂ) : ‖rotateFour z‖ = ‖z‖ := by
  simp [rotateFour]

theorem rotateThree_cube (z : ℂ) : rotateThree (rotateThree (rotateThree z)) = z := by
  change -rho * (-rho * (-rho * z)) = z
  calc
    -rho * (-rho * (-rho * z)) = -(rho ^ 3) * z := by ring
    _ = z := by rw [rho_cube]; ring

theorem rotateFour_fourth (z : ℂ) :
    rotateFour (rotateFour (rotateFour (rotateFour z))) = z := by
  simp [rotateFour, ← mul_assoc]

/-- An explicit order-one elliptic branch with value `ρ` at zero. -/
def tauThree (z : ℂ) : ℂ := cayley rho z

/-- An explicit order-two elliptic branch with value `i` at zero. -/
def tauFour (z : ℂ) : ℂ := cayley Complex.I (z ^ 2)

@[simp] theorem tauThree_zero : tauThree 0 = rho := cayley_zero rho

@[simp] theorem tauFour_zero : tauFour 0 = Complex.I := by simp [tauFour]

theorem tauThree_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauThree z).im :=
  cayley_im_pos rho_im_pos hz

theorem tauFour_im_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (tauFour z).im := by
  apply cayley_im_pos (by simp)
  rw [norm_pow]
  nlinarith [norm_nonneg z]

theorem tauThree_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauThree z ≠ 0 := by
  intro he
  have := tauThree_im_pos hz
  simp [he] at this

theorem tauFour_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : tauFour z ≠ 0 := by
  intro he
  have := tauFour_im_pos hz
  simp [he] at this

theorem tauThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauThree (rotateThree z) = (tauThree z - 1) / tauThree z := by
  have hd : 1 - z ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz
  have hr : 1 + rho * z ≠ 0 := by
    simpa only [rotateThree, neg_mul, sub_neg_eq_add] using
      one_sub_ne_zero_of_norm_lt_one (show ‖rotateThree z‖ < 1 by simpa using hz)
  have hn : rho - (1 - rho) * (-rho * z) = rho + z := by
    linear_combination -z * rho_sq
  rw [eq_div_iff (tauThree_ne_zero hz)]
  simp only [tauThree, cayley, conj_rho, rotateThree]
  rw [hn]
  simp only [neg_mul, sub_neg_eq_add]
  field_simp
  linear_combination (1 - z ^ 2) * rho_sq

theorem tauFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    tauFour (rotateFour z) = -1 / tauFour z := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hd : 1 - z ^ 2 ≠ 0 := one_sub_ne_zero_of_norm_lt_one hz2
  have hp : 1 + z ^ 2 ≠ 0 := by
    intro h
    have he : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right h
    simp [he] at hz2
  simp [tauFour, cayley, rotateFour, mul_pow, Complex.I_sq]
  field_simp
  ring_nf
  simp

theorem tauThree_contDiffOn : ContDiffOn ℂ ω tauThree (Metric.ball 0 1) :=
  cayley_contDiffOn rho

theorem tauFour_contDiffOn : ContDiffOn ℂ ω tauFour (Metric.ball 0 1) := by
  apply (cayley_contDiffOn Complex.I).comp (contDiffOn_id.pow 2)
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right, norm_pow, id_eq] at *
  nlinarith [norm_nonneg z]

/-- A concrete admissible local period triple at the order-three point. -/
def localThree (z : ℂ) : PeriodPoint := sectionThree (tauThree z)

/-- A concrete admissible local period triple at the order-four point. -/
def localFour (z : ℂ) : PeriodPoint := sectionFour (tauFour z)

theorem localThree_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localThree z).Admissible :=
  sectionThree_admissible (tauThree_im_pos hz)

theorem localFour_admissible {z : ℂ} (hz : ‖z‖ < 1) : (localFour z).Admissible :=
  sectionFour_admissible (tauFour_im_pos hz)

theorem localThree_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localThree (rotateThree z) = (localThree z).step₁ := by
  rw [localThree, tauThree_rotate hz]
  exact (sectionThree_step _ (tauThree_ne_zero hz)).symm

theorem localFour_rotate {z : ℂ} (hz : ‖z‖ < 1) :
    localFour (rotateFour z) = (localFour z).step₂ := by
  rw [localFour, tauFour_rotate hz]
  exact (sectionFour_step _ (tauFour_ne_zero hz)).symm

theorem cayley_sub_center (a : ℂ) {z : ℂ} (hz : z ≠ 1) :
    cayley a z - a = z * ((a - starRingEnd ℂ a) / (1 - z)) := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold cayley
  field_simp
  ring

/-- The first branch has the exact vanishing order required in Theorem 3.4(i). -/
theorem tauThree_order : analyticOrderAt (fun z => tauThree z - rho) 0 = 1 := by
  have ht : AnalyticAt ℂ tauThree 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id) (by simp)
  apply (ht.sub analyticAt_const).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z => (rho - starRingEnd ℂ rho) / (1 - z), ?_, ?_, ?_⟩
  · exact analyticAt_const.div (analyticAt_const.sub analyticAt_id) (by simp)
  · simp only [sub_zero, div_one]
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hh
    linarith [rho_im_pos]
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    simp only [sub_zero, pow_one, smul_eq_mul]
    exact cayley_sub_center rho (by
      intro he
      simp [he] at hz)

/-- The second branch has order two, while its base rotation has order four. -/
theorem tauFour_order : analyticOrderAt (fun z => tauFour z - Complex.I) 0 = 2 := by
  have ht : AnalyticAt ℂ tauFour 0 := by
    exact (analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))).div
      (analyticAt_const.sub (analyticAt_id.pow 2)) (by simp)
  apply (ht.sub analyticAt_const).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z => (2 * Complex.I) / (1 - z ^ 2), ?_, ?_, ?_⟩
  · exact analyticAt_const.div (analyticAt_const.sub (analyticAt_id.pow 2)) (by simp)
  · simp
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hz2 : z ^ 2 ≠ 1 := by
      intro he
      have hn : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
      simp [he] at hn
    simpa [tauFour, sub_zero, smul_eq_mul, two_mul] using cayley_sub_center Complex.I hz2

/-- The actual open unit disc, with its inherited complex-manifold atlas. -/
def unitDisc : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

abbrev Disc := unitDisc

theorem disc_norm_lt_one (z : Disc) : ‖(z : ℂ)‖ < 1 := by
  simpa [unitDisc] using z.property

theorem tauThree_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauThree z) :=
  tauThree_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

theorem tauFour_holomorphic :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : Disc => tauFour z) :=
  tauFour_contDiffOn.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => z.property)

/-- A fully constructed holomorphic period map on the first elliptic disc.
All holomorphicity and nondegeneracy obligations are discharged here. -/
def threePeriodMap : HolomorphicPeriodMap ℂ Disc where
  point z := ⟨localThree z, localThree_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauThree_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauThree_holomorphic).div_const 3
  holomorphic_beta := ((contMDiff_const.mul tauThree_holomorphic).div_const 3).sub contMDiff_const

/-- A fully constructed holomorphic period map on the second elliptic disc. -/
def fourPeriodMap : HolomorphicPeriodMap ℂ Disc where
  point z := ⟨localFour z, localFour_admissible (disc_norm_lt_one z)⟩
  holomorphic_tau := tauFour_holomorphic
  holomorphic_mu := (contMDiff_const.sub tauFour_holomorphic).div_const 2
  holomorphic_beta := ((contMDiff_const.mul tauFour_holomorphic).div_const 2).sub contMDiff_const

end Wikipedia.HopfProblem.SpecialPeriods
