import Wikipedia.HopfProblem.OrbitPairSphereGreatCircle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Actual normalized variations of sphere-valued paths

If `γ` is unit length and `V` is pointwise perpendicular to `γ`, the affine
variation `γ + s V` never vanishes. Normalization gives a globally smooth
sphere-valued family. Its parameter derivative at zero is exactly `V`, and
zeros of `V` give genuinely fixed endpoints.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereNormalVariation

open NoExoticSixSphere TwoParameterCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def family (γ V : ℝ → E) (p : ℝ × ℝ) : E :=
  NormedSpace.normalize (γ p.2 + p.1 • V p.2)

theorem affine_ne_zero {γ V : ℝ → E} (hγ : ∀ t, ‖γ t‖ = 1)
    (hV : ∀ t, inner ℝ (γ t) (V t) = 0) (s t : ℝ) : γ t + s • V t ≠ 0 := by
  intro he
  have hi := congrArg (fun z => inner ℝ (γ t) z) he
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hγ, hV, one_pow, mul_zero, add_zero, inner_zero_right] at hi
  norm_num at hi

theorem norm_family {γ V : ℝ → E} (hγ : ∀ t, ‖γ t‖ = 1)
    (hV : ∀ t, inner ℝ (γ t) (V t) = 0) (p : ℝ × ℝ) : ‖family γ V p‖ = 1 :=
  NormedSpace.norm_normalize (affine_ne_zero hγ hV p.1 p.2)

theorem contDiff_family {γ V : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (V t) = 0) :
    ContDiff ℝ ∞ (family γ V) := by
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.2 + p.1 • V p.2) :=
    (hγ.comp contDiff_snd).add (contDiff_fst.smul (hV.comp contDiff_snd))
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hn := affine_ne_zero hunit horth p.1 p.2
  exact (((contDiffAt_norm ℝ hn).comp p hA.contDiffAt).inv
    (norm_ne_zero_iff.mpr hn)).smul hA.contDiffAt

theorem family_zero {γ V : ℝ → E} (hunit : ∀ t, ‖γ t‖ = 1) (t : ℝ) :
    family γ V (0, t) = γ t := by
  simp only [family, zero_smul, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (hunit t)

theorem family_of_field_zero {γ V : ℝ → E} (hunit : ∀ t, ‖γ t‖ = 1)
    {t : ℝ} (ht : V t = 0) (s : ℝ) : family γ V (s, t) = γ t := by
  simp only [family, ht, smul_zero, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (hunit t)

theorem hasDerivAt_family_zero {γ V : ℝ → E} (hunit : ∀ t, ‖γ t‖ = 1)
    (horth : ∀ t, inner ℝ (γ t) (V t) = 0) (t : ℝ) :
    HasDerivAt (fun s => family γ V (s, t)) (V t) 0 := by
  have hd : HasDerivAt (fun s : ℝ => γ t + s • V t) (V t) 0 := by
    simpa only [one_smul, zero_add, id_eq, Pi.add_apply] using!
      (hasDerivAt_const (0 : ℝ) (γ t)).add ((hasDerivAt_id 0).smul_const (V t))
  have hdq : HasDerivAt (fun s : ℝ => ‖γ t + s • V t‖ ^ 2) 0 0 := by
    simpa only [zero_smul, add_zero, horth, mul_zero] using hd.norm_sq
  have hsqrt := hdq.sqrt (by simp only [zero_smul, add_zero, hunit, one_pow, ne_eq,
    one_ne_zero, not_false_eq_true])
  have hn : HasDerivAt (fun s : ℝ => ‖γ t + s • V t‖) 0 0 := by
    simpa only [Real.sqrt_sq (norm_nonneg _), zero_div] using hsqrt
  have hni := hn.inv (by simp only [zero_smul, add_zero, hunit, ne_eq, one_ne_zero,
    not_false_eq_true])
  simpa only [family, NormedSpace.normalize, Pi.inv_apply, Pi.smul_apply, zero_smul,
    add_zero, hunit, inv_one, neg_zero, zero_div, one_smul] using! hni.fun_smul hd

theorem first_family_zero {γ V : ℝ → E} (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (V t) = 0) (t : ℝ) :
    first (family γ V) (0, t) = V t := by
  have hA := contDiff_family hγ hV hunit horth
  exact (hasDerivAt_first ((hA.differentiable (by simp)) (0, t))).unique
    (hasDerivAt_family_zero hunit horth t)

theorem second_first_family_zero {γ V : ℝ → E}
    (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (V t) = 0) (t : ℝ) :
    second (first (family γ V)) (0, t) = deriv V t := by
  have hA := contDiff_family hγ hV hunit horth
  have hd := hasDerivAt_second (((contDiff_first hA).differentiable (by simp)) (0, t))
  have he : (fun r => first (family γ V) (0, r)) = V :=
    funext (first_family_zero hγ hV hunit horth)
  rw [he] at hd
  exact hd.deriv.symm

theorem second_second_family_zero {γ V : ℝ → E}
    (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (V t) = 0) (t : ℝ) :
    second (second (family γ V)) (0, t) = deriv (deriv γ) t := by
  have hA := contDiff_family hγ hV hunit horth
  have he₀ : (fun r => family γ V (0, r)) = γ := funext (family_zero hunit)
  have he₁ : (fun r => second (family γ V) (0, r)) = deriv γ := by
    funext r
    have hd := hasDerivAt_second ((hA.differentiable (by simp)) (0, r))
    rw [he₀] at hd
    exact hd.deriv.symm
  have hd := hasDerivAt_second (((contDiff_second hA).differentiable (by simp)) (0, t))
  rw [he₁] at hd
  exact hd.deriv.symm

theorem hasDerivAt_deriv_energy {γ V : ℝ → E}
    (hγ : ContDiff ℝ ∞ γ) (hV : ContDiff ℝ ∞ V)
    (hunit : ∀ t, ‖γ t‖ = 1) (horth : ∀ t, inner ℝ (γ t) (V t) = 0)
    (l u w : ℝ) (hl : V l = 0) (hu : V u = 0)
    (hacc : ∀ t, deriv (deriv γ) t = (-w ^ 2) • γ t) :
    HasDerivAt (deriv (fun s => SpherePathEnergy.energy (fun t => family γ V (s, t)) l u))
      (2 * ∫ t in l..u, (‖deriv V t‖ ^ 2 - w ^ 2 * ‖V t‖ ^ 2)) 0 := by
  have hA := contDiff_family hγ hV hunit horth
  have hd := SpherePathEnergy.hasDerivAt_deriv_energy_of_geodesic hA
    (norm_family hunit horth) 0 l u w
    (fun s => (family_of_field_zero hunit hl s).trans (family_zero hunit l).symm)
    (fun s => (family_of_field_zero hunit hu s).trans (family_zero hunit u).symm)
    (fun t => by rw [second_second_family_zero hγ hV hunit horth, hacc, family_zero hunit])
  simpa only [second_first_family_zero hγ hV hunit horth,
    first_family_zero hγ hV hunit horth] using hd

end Wikipedia.HopfProblem.OrbitPair.SphereNormalVariation
