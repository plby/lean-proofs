import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCutoff
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmoothDescent
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyBase
import Wikipedia.HopfProblem.EllipticLogGaugeRotation
import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.EllipticFamilyAction

/-!
# Smooth angular corrections in the original elliptic disc

An order-periodic real vector function descends through the actual normalized
exponential.  The principal logarithm is used only to specify its value;
smoothness is proved through the original local inverse charts of the
exponential.  A concrete radial cutoff makes the correction identically zero
near the disc centre, so no angular chart is used at the centre.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic Elliptic.LogGauge CuspUniformization SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℝ ℂ
local notation "IV" => modelWithCornersSelf ℝ RealCoordinates

/-- The angular value, specified by the normalized logarithm. -/
def angularValue (j : Kind) (h : ℝ → RealCoordinates) (θ : ℝ) (z : ℂ) :
    RealCoordinates := h ((j.order : ℝ) * (logarithm z).re - θ)

/-- Every logarithmic representative gives exactly the same real vector. -/
theorem angularValue_exponential (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (θ : ℝ) (z : ℂ) :
    angularValue j h θ (exponential z) = h ((j.order : ℝ) * z.re - θ) := by
  obtain ⟨k, hk⟩ := (exponential_eq_iff (logarithm (exponential z)) z).mp
    (exponential_logarithm (exponential_ne_zero z))
  unfold angularValue
  rw [hk]
  simp only [Complex.add_re, Complex.intCast_re]
  rw [show (j.order : ℝ) * (z.re + k) - θ =
    ((j.order : ℝ) * z.re - θ) + (k : ℝ) * j.order by ring]
  exact hp.int_mul k ((j.order : ℝ) * z.re - θ)

private theorem angularTime_contDiff (j : Kind) (θ : ℝ) :
    ContDiff ℝ ∞ (fun z : ℂ => (j.order : ℝ) * z.re - θ) :=
  (contDiff_const.mul Complex.reCLM.contDiff).sub contDiff_const

/-- Real smoothness away from zero follows from actual exponential local inverses. -/
theorem angularValue_contDiffAt (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (hs : ContDiff ℝ ∞ h)
    (θ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (angularValue j h θ) z := by
  have hq := CuspCircleNormalTrivialization.isLocalDiffeomorph_real_of_complex
    SpecialPeriods.CuspFamily.exponential_isLocalDiffeomorph
  have hf : ContMDiff I₁ IV ∞ (angularValue j h θ ∘ exponential) := by
    exact (hs.comp (angularTime_contDiff j θ)).contMDiff.congr
      (angularValue_exponential j h hp θ)
  have hi : ContMDiffAt I₁ I₁ ∞
      (hq (logarithm z)).localInverse z := by
    simpa only [exponential_logarithm hz] using
      (hq (logarithm z)).localInverse_contMDiffAt.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)
  have he := (hq (logarithm z)).localInverse_eventuallyEq_right
  rw [exponential_logarithm hz] at he
  have hm := hf.contMDiffAt.comp z hi
  have hm' : ContMDiffAt I₁ IV ∞ (angularValue j h θ) z := by
    apply hm.congr_of_eventuallyEq
    filter_upwards [he] with w hw
    change angularValue j h θ w =
      angularValue j h θ (exponential ((hq (logarithm z)).localInverse w))
    rw [show exponential ((hq (logarithm z)).localInverse w) = w from hw]
  exact hm'.contDiffAt

/-- Homogeneous monodromy is exactly covariance under the original clockwise rotation. -/
theorem angularValue_rotation (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ))
    (hh : ∀ t, flatLinear j (h (t + 1)) = h t)
    (θ : ℝ) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    angularValue j h θ (familyRotation j z) = flatLinear j (angularValue j h θ z) := by
  obtain ⟨k, hk⟩ := logarithm_familyRotation j z hz
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hre : (logarithm (familyRotation j z : ℂ)).re =
      (logarithm (z : ℂ)).re - 1 / (j.order : ℝ) + k := by
    have hdiv : (1 / (j.order : ℂ)) = (((1 : ℝ) / j.order : ℝ) : ℂ) := by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    rw [hk, Complex.add_re, Complex.sub_re, hdiv, Complex.ofReal_re, Complex.intCast_re]
  unfold angularValue
  rw [hre]
  have ht : (j.order : ℝ) * ((logarithm (z : ℂ)).re - 1 / j.order + k) - θ =
      ((j.order : ℝ) * (logarithm (z : ℂ)).re - θ - 1) + (k : ℝ) * j.order := by
    field_simp [hm]
    ring
  rw [ht, hp.int_mul]
  have he := hh ((j.order : ℝ) * (logarithm (z : ℂ)).re - θ - 1)
  rw [sub_add_cancel] at he
  exact he.symm

/-- The exact original disc rotation preserves the root radius. -/
theorem familyRotation_norm (j : Kind) (z : Disc) :
    ‖(familyRotation j z : ℂ)‖ = ‖(z : ℂ)‖ := by
  rw [familyRotation_val, norm_mul, normalPhase_norm, one_mul]

/-- The explicit cutoff angular vector, also defined at the centre. -/
def radialCorrection (j : Kind) (h : ℝ → RealCoordinates) (θ a : ℝ) (z : ℂ) :
    RealCoordinates := radialCutoff a (‖z‖ ^ 2) • angularValue j h θ z

@[simp] theorem radialCorrection_zero (j : Kind) (h : ℝ → RealCoordinates) (θ a : ℝ) :
    radialCorrection j h θ a 0 = 0 := by
  rw [radialCorrection, norm_zero, zero_pow (by decide : 2 ≠ 0),
    radialCutoff_eq_zero_of_nonpos a le_rfl, zero_smul]

/-- The correction is literally zero on the inner disc. -/
theorem radialCorrection_eq_zero (j : Kind) (h : ℝ → RealCoordinates)
    (θ a : ℝ) {z : ℂ} (hz : ‖z‖ ^ 2 ≤ a ^ 2 / 4) :
    radialCorrection j h θ a z = 0 := by
  rw [radialCorrection, radialCutoff_eq_zero_of_le a _ hz, zero_smul]

private theorem normSquared_contDiff : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := by
  have h : (fun z : ℂ => ‖z‖ ^ 2) = (fun z : ℂ => z.re ^ 2 + z.im ^ 2) := by
    funext z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [h]
  exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

/-- The actual cutoff removes the angular singularity, with no chosen angle at the centre. -/
theorem radialCorrection_contDiff (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (hs : ContDiff ℝ ∞ h)
    (θ : ℝ) {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (radialCorrection j h θ a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hU : {w : ℂ | ‖w‖ ^ 2 < a ^ 2 / 4} ∈ 𝓝 (0 : ℂ) := by
      have ho : IsOpen {w : ℂ | ‖w‖ ^ 2 < a ^ 2 / 4} :=
        isOpen_lt normSquared_contDiff.continuous continuous_const
      apply ho.mem_nhds
      change ‖(0 : ℂ)‖ ^ 2 < a ^ 2 / 4
      rw [norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
    have hc : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : RealCoordinates)) 0 := contDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [hU] with w hw
    exact radialCorrection_eq_zero j h θ a hw.le
  · exact ((radialCutoff_contDiff a).contDiffAt.comp z normSquared_contDiff.contDiffAt).smul
      (angularValue_contDiffAt j h hp hs θ hz)

/-- Restriction of the same ambient vector to the original open disc. -/
def discCorrection (j : Kind) (h : ℝ → RealCoordinates) (θ a : ℝ) (z : Disc) :
    RealCoordinates := radialCorrection j h θ a z

theorem discCorrection_contMDiff (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (hs : ContDiff ℝ ∞ h)
    (θ : ℝ) {a : ℝ} (ha : 0 < a) :
    ContMDiff I₁ IV ∞ (discCorrection j h θ a) :=
  (radialCorrection_contDiff j h hp hs θ ha).contMDiff.comp contMDiff_subtype_val

/-- The radial extension still commutes with the unchanged affine finite action. -/
theorem discCorrection_rotation (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ))
    (hh : ∀ t, flatLinear j (h (t + 1)) = h t) (θ a : ℝ) (z : Disc) :
    discCorrection j h θ a (familyRotation j z) = flatLinear j (discCorrection j h θ a z) := by
  by_cases hz : (z : ℂ) = 0
  · have he : z = Elliptic.discZero := Subtype.ext hz
    subst z
    rw [familyRotation_zero]
    change radialCorrection j h θ a 0 = flatLinear j (radialCorrection j h θ a 0)
    rw [radialCorrection_zero, map_zero]
  · change radialCutoff a (‖(familyRotation j z : ℂ)‖ ^ 2) •
        angularValue j h θ (familyRotation j z) =
      flatLinear j (radialCutoff a (‖(z : ℂ)‖ ^ 2) • angularValue j h θ z)
    rw [familyRotation_norm, angularValue_rotation j h hp hh θ z hz, map_smul]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
