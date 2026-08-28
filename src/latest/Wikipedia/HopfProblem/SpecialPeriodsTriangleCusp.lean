import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The actual normalized cusp coordinate

The cusp translation is normalized by dividing by its positive width.
The resulting exponential is a holomorphic open surjection onto the
punctured unit disc, and its fibres are exactly the integer cusp orbits.
These statements concern the cyclic cusp action only; precise invariance
of a horodisc under the full triangle group is a separate assertion.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem width_coe_ne_zero : (width : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr width_ne_zero

private theorem divide_width_im_pos (z : ℍ) : 0 < ((z : ℂ) / width).im := by
  simpa only [Complex.div_ofReal_im, UpperHalfPlane.coe_im] using div_pos z.im_pos width_pos

private theorem multiply_width_im_pos (z : ℍ) : 0 < ((width : ℂ) * z).im := by
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, UpperHalfPlane.coe_im] using mul_pos width_pos z.im_pos

/-- The normalized upper-half-plane coordinate `ζ = z / width`. -/
def normalizeCusp (z : ℍ) : ℍ := UpperHalfPlane.ofComplex ((z : ℂ) / width)

def denormalizeCusp (z : ℍ) : ℍ := UpperHalfPlane.ofComplex ((width : ℂ) * z)

@[simp] theorem normalizeCusp_coe (z : ℍ) : (normalizeCusp z : ℂ) = (z : ℂ) / width :=
  congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (divide_width_im_pos z))

@[simp] theorem denormalizeCusp_coe (z : ℍ) :
    (denormalizeCusp z : ℂ) = (width : ℂ) * z :=
  congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos (multiply_width_im_pos z))

theorem normalizeCusp_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω normalizeCusp := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => (z : ℂ) / width) :=
    (contDiff_id.div_const (width : ℂ)).contMDiff.comp UpperHalfPlane.contMDiff_coe
  intro z
  exact (UpperHalfPlane.contMDiffAt_ofComplex (divide_width_im_pos z)).comp z (h z)

theorem denormalizeCusp_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω denormalizeCusp := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => (width : ℂ) * z) :=
    contMDiff_const.mul UpperHalfPlane.contMDiff_coe
  intro z
  exact (UpperHalfPlane.contMDiffAt_ofComplex (multiply_width_im_pos z)).comp z (h z)

/-- Normalization of the cusp is an actual biholomorphism of upper
half-planes, not merely a formal change of variables. -/
def cuspNormalization : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℍ ℍ ω where
  toFun := normalizeCusp
  invFun := denormalizeCusp
  left_inv z := by
    apply UpperHalfPlane.ext
    rw [denormalizeCusp_coe, normalizeCusp_coe]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ width_coe_ne_zero]
  right_inv z := by
    apply UpperHalfPlane.ext
    rw [normalizeCusp_coe, denormalizeCusp_coe]
    exact mul_div_cancel_left₀ _ width_coe_ne_zero
  contMDiff_toFun := normalizeCusp_holomorphic
  contMDiff_invFun := denormalizeCusp_holomorphic

theorem normalizeCusp_cusp_zpow (n : ℤ) (z : ℍ) :
    normalizeCusp (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) =
      (-(n : ℝ)) +ᵥ normalizeCusp z := by
  apply UpperHalfPlane.ext
  rw [normalizeCusp_coe, triangleGeometricRepresentation_cusp_zpow_coe,
    UpperHalfPlane.coe_vadd, normalizeCusp_coe]
  push_cast
  rw [sub_div, mul_div_cancel_right₀ _ width_coe_ne_zero]
  ring

@[simp] theorem normalizeCusp_cusp (z : ℍ) :
    normalizeCusp (triangleGeometricRepresentation triangleCuspGenerator z) =
      (-1 : ℝ) +ᵥ normalizeCusp z := by
  simpa using normalizeCusp_cusp_zpow 1 z

/-- The source's actual exponential cusp coordinate. -/
def cuspQ (z : ℍ) : ℂ := Periodic.qParam width z

theorem cuspQ_eq_exp (z : ℍ) :
    cuspQ z = Complex.exp (2 * Real.pi * Complex.I * z / width) := rfl

theorem cuspQ_eq_normalized (z : ℍ) : cuspQ z = Periodic.qParam 1 (normalizeCusp z) := by
  simp [cuspQ, Periodic.qParam, mul_div_assoc]

theorem cuspQ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspQ :=
  (Periodic.contDiff_qParam (h := width) ω).contMDiff.comp UpperHalfPlane.contMDiff_coe

theorem cuspQ_continuous : Continuous cuspQ := cuspQ_holomorphic.continuous

theorem cuspQ_ne_zero (z : ℍ) : cuspQ z ≠ 0 := Periodic.qParam_ne_zero z

/-- The strict complex derivative in the ordinary upper-half-plane
coordinate, including its exact nonzero coefficient. -/
theorem cuspQ_hasStrictDerivAt (z : ℍ) :
    HasStrictDerivAt (cuspQ ∘ UpperHalfPlane.ofComplex)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
  have h : HasStrictDerivAt (Periodic.qParam width)
      (cuspQ z * (2 * Real.pi * Complex.I / width)) (z : ℂ) := by
    simpa only [id_eq, mul_one] using!
      (((hasStrictDerivAt_id (z : ℂ)).const_mul
        (2 * Real.pi * Complex.I)).div_const (width : ℂ)).cexp
  apply h.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
  change Periodic.qParam width w = Periodic.qParam width (UpperHalfPlane.ofComplex w)
  exact congrArg (Periodic.qParam width) hw.symm

theorem cuspQ_deriv_ne_zero (z : ℍ) :
    deriv (cuspQ ∘ UpperHalfPlane.ofComplex) (z : ℂ) ≠ 0 := by
  rw [(cuspQ_hasStrictDerivAt z).hasDerivAt.deriv]
  exact mul_ne_zero (cuspQ_ne_zero z)
    (div_ne_zero Complex.two_pi_I_ne_zero width_coe_ne_zero)

theorem cuspQ_norm (z : ℍ) :
    ‖cuspQ z‖ = Real.exp (-2 * Real.pi * z.im / width) :=
  Periodic.norm_qParam width z

theorem cuspQ_norm_lt_one (z : ℍ) : ‖cuspQ z‖ < 1 :=
  Periodic.norm_qParam_lt_one width_pos z.im_pos

/-- Horodiscs are exactly inverse images of smaller punctured discs. -/
theorem cuspQ_norm_lt_exp_iff (A : ℝ) (z : ℍ) :
    ‖cuspQ z‖ < Real.exp (-2 * Real.pi * A / width) ↔ A < z.im :=
  Periodic.norm_qParam_lt_iff width_pos A z

theorem cuspQ_cusp_zpow (n : ℤ) (z : ℍ) :
    cuspQ (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) = cuspQ z := by
  rw [cuspQ, triangleGeometricRepresentation_cusp_zpow_coe, cuspQ]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-n, ?_⟩
  push_cast
  rw [mul_div_assoc, sub_div, mul_div_cancel_right₀ _ width_coe_ne_zero]
  ring

@[simp] theorem cuspQ_cusp (z : ℍ) :
    cuspQ (triangleGeometricRepresentation triangleCuspGenerator z) = cuspQ z := by
  simpa using cuspQ_cusp_zpow 1 z

/-- Equality of cusp coordinates means exactly equality modulo an
integer power of the actual cusp transformation. -/
theorem cuspQ_eq_iff (z w : ℍ) :
    cuspQ z = cuspQ w ↔
      ∃ n : ℤ, triangleGeometricRepresentation (triangleCuspGenerator ^ n) w = z := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Periodic.qParam_left_inv_mod_period width_ne_zero (z : ℂ)
    obtain ⟨n, hn⟩ := Periodic.qParam_left_inv_mod_period width_ne_zero (w : ℂ)
    change Periodic.invQParam width (cuspQ z) = (z : ℂ) + m * width at hm
    change Periodic.invQParam width (cuspQ w) = (w : ℂ) + n * width at hn
    rw [h, hn] at hm
    refine ⟨m - n, ?_⟩
    apply UpperHalfPlane.ext
    rw [triangleGeometricRepresentation_cusp_zpow_coe]
    push_cast
    linear_combination hm
  · rintro ⟨n, rfl⟩
    exact cuspQ_cusp_zpow n w

theorem cuspQ_eq_iff_existsUnique (z w : ℍ) :
    cuspQ z = cuspQ w ↔
      ∃! n : ℤ, triangleGeometricRepresentation (triangleCuspGenerator ^ n) w = z := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (cuspQ_eq_iff z w).mp h
    refine ⟨n, hn, fun m hm => ?_⟩
    exact triangleGeometricRepresentation_cusp_orbit_injective w (hm.trans hn.symm)
  · rintro ⟨n, hn, _⟩
    exact (cuspQ_eq_iff z w).mpr ⟨n, hn⟩

/-- The punctured unit disc with its inherited complex manifold structure. -/
def puncturedDisc : TopologicalSpace.Opens ℂ :=
  ⟨{q : ℂ | q ≠ 0 ∧ ‖q‖ < 1},
    isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)⟩

abbrev PuncturedDisc := puncturedDisc

def cuspQMap (z : ℍ) : PuncturedDisc :=
  ⟨cuspQ z, cuspQ_ne_zero z, cuspQ_norm_lt_one z⟩

@[simp] theorem cuspQMap_coe (z : ℍ) : (cuspQMap z : ℂ) = cuspQ z := rfl

theorem cuspQMap_eq_iff (z w : ℍ) :
    cuspQMap z = cuspQMap w ↔
      ∃ n : ℤ, triangleGeometricRepresentation (triangleCuspGenerator ^ n) w = z :=
  Subtype.ext_iff.trans (cuspQ_eq_iff z w)

theorem cuspQMap_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspQMap := by
  intro z
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w : ℍ => (cuspQMap w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω cuspQMap z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (cuspQ_holomorphic z)

theorem cuspQMap_continuous : Continuous cuspQMap := cuspQMap_holomorphic.continuous

theorem cuspQMap_surjective : Function.Surjective cuspQMap := by
  intro q
  refine ⟨⟨Periodic.invQParam width q,
    Periodic.im_invQParam_pos_of_norm_lt_one width_pos q.property.2 q.property.1⟩, ?_⟩
  apply Subtype.ext
  exact Periodic.qParam_right_inv width_ne_zero q.property.1

private theorem qParam_width_isOpenMap : IsOpenMap (Periodic.qParam width) := by
  change IsOpenMap (Complex.exp ∘ (fun z : ℂ => 2 * Real.pi * Complex.I * z / width))
  apply Complex.isOpenMap_exp.comp
  have he : (fun z : ℂ => 2 * Real.pi * Complex.I * z / width) =
      (fun z : ℂ => (2 * Real.pi * Complex.I / width) * z) := by
    funext z
    ring
  rw [he]
  exact (Homeomorph.mulLeft₀ _ (div_ne_zero Complex.two_pi_I_ne_zero
    width_coe_ne_zero)).isOpenMap

theorem cuspQ_isOpenMap : IsOpenMap cuspQ :=
  qParam_width_isOpenMap.comp UpperHalfPlane.isOpenEmbedding_coe.isOpenMap

theorem cuspQMap_isOpenMap : IsOpenMap cuspQMap :=
  puncturedDisc.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr cuspQ_isOpenMap

theorem cuspQMap_isOpenQuotientMap : IsOpenQuotientMap cuspQMap :=
  ⟨cuspQMap_surjective, cuspQMap_continuous, cuspQMap_isOpenMap⟩

theorem cuspQ_tendsto_atImInfty :
    Tendsto cuspQ UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) :=
  (Periodic.qParam_tendsto width_pos).comp UpperHalfPlane.tendsto_coe_atImInfty

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
