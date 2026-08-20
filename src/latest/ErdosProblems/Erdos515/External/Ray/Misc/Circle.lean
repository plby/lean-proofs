module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Complex

/-!
## `Circle` facts
-/

open Classical
open Complex (arg exp I slitPlane)
open Metric (sphere)
open Set
open scoped Real ComplexConjugate
noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- `-z = Circle.exp π * z` (Mathlib now provides `Neg Circle` and `HasDistribNeg Circle`) -/
lemma Circle.neg_def (z : Circle) : -z = Circle.exp π * z := by
  apply Circle.ext
  simp only [Circle.coe_neg, Circle.coe_mul, Circle.coe_exp, Complex.exp_pi_mul_I, neg_one_mul]

@[simp] lemma Circle.neg_ne (z : Circle) : -z ≠ z := Circle.neg_ne_self z

lemma Circle.arg_neg_one : arg (-1 : Circle).val = π := by
  simp only [Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one]

@[simp] lemma Circle.mem_slitPlane (z : Circle) : z.val ∈ slitPlane ↔ z ≠ -1 := by
  simp only [Complex.mem_slitPlane_iff_arg, ne_eq, Circle.ext_iff, Complex.ext_norm_arg_iff,
    norm_zero, Complex.arg_zero, Circle.norm_coe, true_and, one_ne_zero, false_and, not_false_iff,
    and_true, coe_neg, norm_neg, Circle.coe_one, Complex.arg_neg_one, norm_one]

@[fun_prop] lemma Continuous.circle_exp {f : X → ℝ} (fc : Continuous f) :
    Continuous (fun x ↦ Circle.exp (f x)) := by fun_prop

instance : Inhabited Circle where
  default := 1

instance : Nonempty Circle := by infer_instance

instance : Infinite Circle := by
  rw [Circle.argEquiv.infinite_iff]
  apply Set.Infinite.to_subtype
  exact Ioc_infinite (by linarith [Real.pi_pos])

-- Courtesy of Junyan Xu, see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/No.20continuous.2C.20injective.20maps.20.60Circle.20.E2.86.92.20.E2.84.9D.20.60/near/534054211
lemma AddCircle.isConnected_compl_singleton {T : ℝ} [h : Fact (0 < T)]
    (s : AddCircle T) : IsConnected {s}ᶜ := by
  obtain ⟨s⟩ := s
  have := isConnected_iff_connectedSpace.mp
    (isConnected_Ioo <| show s < s + T by linarith [h.out])
  have : Set.Ioo s (s + T) ≃ₜ _ :=
    (AddCircle.openPartialHomeomorphCoe T s).toHomeomorphSourceTarget
  exact isConnected_iff_connectedSpace.mpr <|
    this.surjective.connectedSpace this.continuous

-- Courtesy of Junyan Xu, see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/No.20continuous.2C.20injective.20maps.20.60Circle.20.E2.86.92.20.E2.84.9D.20.60/near/534054211
lemma Circle.isConnected_compl_singleton (s : Circle) : IsConnected {s}ᶜ := by
  have e := AddCircle.homeomorphCircle'
  have : Fact (0 < 2 * Real.pi) := ⟨by simp [Real.pi_pos]⟩
  rw [← e.isConnected_preimage]
  convert AddCircle.isConnected_compl_singleton (e.symm s)
  aesop

/-- There are no continuous, injective maps `Circle → ℝ` -/
lemma Circle.not_continuous_or_not_injective {f : Circle → ℝ} (cont : Continuous f)
    (inj : f.Injective) : False := by
  obtain ⟨a,_,lo⟩ := isCompact_univ.exists_isMinOn univ_nonempty cont.continuousOn
  obtain ⟨b,_,hi⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cont.continuousOn
  simp only [isMinOn_iff, mem_univ, forall_const, isMaxOn_iff] at lo hi
  by_cases ab : f a = f b
  · have e : ∀ x y, f x = f y := by intro x y; linarith [lo x, hi x, lo y, hi y]
    specialize e (-1) 1
    simp only [inj.eq_iff, neg_ne] at e
  · replace ab : f a < f b := Ne.lt_of_le ab (lo b)
    obtain ⟨x,m⟩ := Infinite.exists_notMem_finset {a, b}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at m
    have ax : f a < f x := (inj.ne_iff.mpr m.1).symm.lt_of_le (lo x)
    have xb : f x < f b := (inj.ne_iff.mpr m.2).lt_of_le (hi x)
    have connect : (f '' {x}ᶜ).OrdConnected :=
      ((Circle.isConnected_compl_singleton x).image _ cont.continuousOn).isPreconnected.ordConnected
    have mem := connect.out (x := f a) (y := f b) (by aesop) (by aesop) ⟨ax.le, xb.le⟩
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, inj.eq_iff, not_and_self,
      exists_const] at mem

/-- If `f : Circle → Circle` is continuous and injective, it is surjective -/
lemma Circle.surjective_of_injective {f : Circle → Circle} (cont : Continuous f)
    (inj : f.Injective) : f.Surjective := by
  intro c
  by_contra s
  simp only [not_exists] at s
  set g : Circle → ℝ := fun z ↦ arg (f z / -c : Circle)
  have gc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    refine (Complex.continuousAt_arg ?_).comp (by fun_prop)
    simp only [Circle.mem_slitPlane, ne_eq, div_eq_iff_eq_mul', neg_mul_neg, mul_one, s,
      not_false_eq_true]
  have gi : g.Injective := Circle.injective_arg.comp (div_left_injective.comp inj)
  exact Circle.not_continuous_or_not_injective gc gi

/-- If `f : Circle → Circle` is continuous and injective, it is a homeomorphism -/
public lemma Circle.isHomeomorph_of_injective {f : Circle → Circle} (cont : Continuous f)
    (inj : f.Injective) : IsHomeomorph f := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨cont, inj, surjective_of_injective cont inj⟩

@[simp] public lemma Complex.conj_circleMap {c : ℂ} {r : ℝ} {t : ℝ} :
    conj (circleMap c r t) = circleMap (conj c) r (-t) := by
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_neg,
    neg_mul, ← Complex.exp_conj, Complex.conj_I, mul_neg]

/-- Only diagonal expoential integrals survive -/
public lemma integral_exp_mul_I (n : ℤ) :
    ∫ t in -π..π, exp (n * t * I) = if n = 0 then 2 * π else 0 := by
  by_cases n0 : n = 0
  · simp [n0, two_mul]
  · have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ exp (n * t * I)) (n * I * exp (n * t * I)) t := by
      intro t
      simp only [← mul_assoc, mul_comm _ I]
      generalize I * n = c
      simp only [mul_comm c]
      apply HasDerivAt.cexp
      nth_rw 2 [← (by simp : (1 : ℝ) * c = c)]
      exact (hasDerivAt_id t).ofReal_comp.mul_const _
    have d : deriv (fun t : ℝ ↦ exp (n * t * I) / (n * I)) = fun t : ℝ ↦ exp (n * t * I) := by
      ext t
      rw [deriv_div_const, (hd t).deriv, mul_div_cancel_left₀ _ (by simp [n0])]
    rw [intervalIntegral.integral_deriv_eq_sub' (E := ℂ) _ d (a := -π) (b := π)]
    · simp only [n0, if_false, mul_assoc, Complex.exp_int_mul, Complex.ofReal_neg, neg_mul,
        Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, sub_self, Complex.ofReal_zero]
    · exact fun t _ ↦ (hd t).differentiableAt.div_const _
    · fun_prop

/-- `circleMap` is continuous on `ℝ × ℝ` -/
@[fun_prop] public theorem continuous_circleMap_full {c : ℂ} :
    Continuous fun x : ℝ × ℝ ↦ circleMap c x.1 x.2 := by
  continuity

/-- `circleMap` is analytic in `t` -/
@[fun_prop] theorem analyticAt_circleMap {c : ℂ} {r t : ℝ} : AnalyticAt ℝ (circleMap c r) t := by
  unfold circleMap
  refine analyticAt_const.add (analyticAt_const.mul (analyticAt_cexp.restrictScalars.comp ?_))
  exact Complex.analyticAt_ofReal.mul analyticAt_const

/-- The derivative of `circleMap` w.r.t. the radius -/
lemma HasDerivAt.circleMap_radius {c : ℂ} {r t : ℝ} :
    HasDerivAt (fun r ↦ circleMap c r t) (circleMap 0 1 t) r := by
  simp only [circleMap, zero_add]
  exact ((hasDerivAt_id _).ofReal_comp.mul_const _).const_add _

/-- `circleMap` is surjective from `|t| ≤ π` -/
public lemma exists_circleMap_le {r : ℝ} {z : ℂ} (m : ‖z‖ = r) :
    ∃ t, |t| ≤ π ∧ circleMap 0 r t = z := by
  replace m : z ∈ sphere 0 |r| := by simp [← m]
  simp only [← image_circleMap_Ioc, mem_image, mem_Ioc] at m
  obtain ⟨t,⟨t0,t1⟩,tz⟩ := m
  by_cases t0 : t ≤ π
  · exact ⟨t, abs_le.mpr ⟨by linarith, by linarith⟩, tz⟩
  · refine ⟨t - 2 * π, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
    simp only [circleMap, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_mul,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one, zero_add, ← tz]

public lemma abs_le_mul_norm_circleMap {t : ℝ} (m : |t| ≤ π) :
    |t| ≤ π/2 * ‖circleMap 0 1 t - 1‖ := by
  suffices h : t ^ 2 ≤ π ^ 2 / 2 ^ 2 * Complex.normSq (circleMap 0 1 t - 1) by
    rw [← sq_le_sq₀ (by bound) (by bound)]
    simp only [sq_abs, Complex.norm_def, mul_pow, div_pow]
    rwa [Real.sq_sqrt (by bound)]
  rw [mul_comm, ← div_le_iff₀ (by bound)]
  simp only [circleMap, Complex.exp_mul_I, Complex.normSq_apply, Complex.sub_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, one_mul,
    Complex.one_im, sub_zero, Complex.ofReal_re, Complex.ofReal_im, ← pow_two, zero_mul,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  simp only [sub_sq, mul_one, one_pow, Real.cos_sq']
  ring_nf
  have b := Real.cos_le_one_sub_mul_cos_sq m
  rw [inv_pow, ← div_eq_mul_inv, div_mul_eq_mul_div, mul_div_assoc, mul_comm (t^2)]
  rw [div_mul_eq_mul_div, mul_div_assoc] at b ⊢
  linarith [b]
