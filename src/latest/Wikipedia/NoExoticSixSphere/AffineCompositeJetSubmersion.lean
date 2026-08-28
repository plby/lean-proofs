import Wikipedia.NoExoticSixSphere.AffineCompositeDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual spatial-jet submersivity after a nonlinear target map

Affine variations with zero value keep the nonlinear map's input fixed at
the chosen source point. Their actual spatial derivatives can therefore be
prescribed using the source and target differential splittings. Differentiating
this exact parameter-line identity proves surjectivity of the jet derivative.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.AffineComposite

open AffinePerturbation

variable {X V E W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem contDiffAt_composite (g : X → E) (i : X → V) (r : E → W) (a : ℝ)
    (p : Parameters V E) (x : X) (hg : ContDiffAt ℝ ∞ g x) (hi : ContDiffAt ℝ ∞ i x)
    (hr : ContDiffAt ℝ ∞ r (ambient g i a p x)) :
    ContDiffAt ℝ ∞ (uncurry (composite g i r a)) (p, x) := by
  have hg' : ContDiffAt ℝ ∞ (fun z : Parameters V E × X ↦ g z.2) (p, x) :=
    hg.comp (p, x) contDiffAt_snd
  have hi' : ContDiffAt ℝ ∞ (fun z : Parameters V E × X ↦ i z.2) (p, x) :=
    hi.comp (p, x) contDiffAt_snd
  have hA : ContDiffAt ℝ ∞ (fun z : Parameters V E × X ↦ z.1.1) (p, x) :=
    (contDiff_fst.comp contDiff_fst).contDiffAt
  have hb : ContDiffAt ℝ ∞ (fun z : Parameters V E × X ↦ z.1.2) (p, x) :=
    (contDiff_snd.comp contDiff_fst).contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun z : Parameters V E × X ↦ value z.1 (i z.2)) (p, x) :=
    (hA.clm_apply hi').add hb
  have ha : ContDiffAt ℝ ∞ (uncurry (ambient g i a)) (p, x) :=
    hg'.add (hv.const_smul a)
  exact hr.comp (p, x) ha

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

theorem surjective_fderiv_spatial_parameter (g : X → E) (i : X → V) (r : E → W)
    (a : ℝ) (ha : a ≠ 0) (p : Parameters V E) (x : X)
    (hg : ContDiffAt ℝ ∞ g x) (hi : ContDiffAt ℝ ∞ i x)
    (hr : ContDiffAt ℝ ∞ r (ambient g i a p x))
    (hJ : Injective (fderiv ℝ i x)) (hR : Surjective (fderiv ℝ r (ambient g i a p x))) :
    Surjective (fderiv ℝ (fun q : Parameters V E ↦ fderiv ℝ (composite g i r a q) x) p) := by
  let D := fun q : Parameters V E ↦ fderiv ℝ (composite g i r a q) x
  have hD : ContDiffAt ℝ ∞ D p :=
    (contDiffAt_composite g i r a p x hg hi hr).fderiv contDiffAt_const (by simp)
  have hDd : HasFDerivAt D (fderiv ℝ D p) p := (hD.differentiableAt (by simp)).hasFDerivAt
  intro L
  obtain ⟨q, hq0, hqL⟩ := exists_zero_value_prescribed_composition (i x)
    (fderiv ℝ i x) hJ (fderiv ℝ r (ambient g i a p x)) hR ha L
  have he (t : ℝ) : D (p + t • q) = D p + t • L := by
    change fderiv ℝ (composite g i r a (p + t • q)) x = _
    rw [fderiv_composite_add_smul_of_zero g i r a p q x
      (hg.differentiableAt (by simp)) (hi.differentiableAt (by simp))
      (hr.differentiableAt (by simp)) hq0 t, hqL]
  have ht : HasDerivAt (fun t : ℝ ↦ p + t • q) q 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const q).const_add p
  have hDd' : HasFDerivAt D (fderiv ℝ D p) (p + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hDd
  have hc := hDd'.comp_hasDerivAt 0 ht
  have he' : (fun t : ℝ ↦ D (p + t • q)) = fun t ↦ D p + t • L := funext he
  change HasDerivAt (fun t : ℝ ↦ D (p + t • q)) (fderiv ℝ D p q) 0 at hc
  rw [he'] at hc
  have hm : HasDerivAt (fun t : ℝ ↦ D p + t • L) L 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const L).const_add (D p)
  exact ⟨q, hc.unique hm⟩

end NoExoticSixSphere.AffineComposite
