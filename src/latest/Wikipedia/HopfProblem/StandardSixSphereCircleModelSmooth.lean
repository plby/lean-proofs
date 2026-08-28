import Wikipedia.HopfProblem.StandardSixSphereCircleModelBasic
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The native smooth standard-six-sphere complement model

This upgrades the explicit homeomorphism to a diffeomorphism. The domain is
the original open complement in Mathlib's stereographic six-sphere atlas.
The target has the ordinary product of Euclidean three-space and Mathlib's
stereographic three-sphere atlas. No charted space is replaced or transported.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

local notation "ProductModel" => ModelWithCorners.prod 𝓘(ℝ, Base) (𝓡 3)

theorem contDiff_base {n : WithTop ℕ∞} : ContDiff ℝ n base :=
  contDiff_fst.comp split.contDiff

theorem contDiff_normal {n : WithTop ℕ∞} : ContDiff ℝ n normal :=
  contDiff_snd.comp split.contDiff

/-- The actual inclusion of the open complement into Euclidean seven-space. -/
theorem contMDiff_complement_ambient :
    ContMDiff (𝓡 6) 𝓘(ℝ, Ambient) ∞ (fun p : Complement => p.val.val) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  exact (contMDiff_coe_sphere (n := 6)).comp
    (contMDiff_subtype_val (U := complement))

theorem contMDiff_complement_base :
    ContMDiff (𝓡 6) 𝓘(ℝ, Base) ∞ (fun p : Complement => base p.val.val) :=
  contDiff_base.comp_contMDiff contMDiff_complement_ambient

theorem contMDiff_complement_normal :
    ContMDiff (𝓡 6) 𝓘(ℝ, Normal) ∞ (fun p : Complement => normal p.val.val) :=
  contDiff_normal.comp_contMDiff contMDiff_complement_ambient

theorem contMDiff_normalRadius :
    ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞ normalRadius :=
  contMDiff_norm_of_ne_zero contMDiff_complement_normal normal_ne_zero

theorem contMDiff_inv_normalRadius :
    ContMDiff (𝓡 6) 𝓘(ℝ, ℝ) ∞ (fun p : Complement => (normalRadius p)⁻¹) :=
  contMDiff_invNorm_of_ne_zero contMDiff_complement_normal normal_ne_zero

/-- Smoothness of the literal forward map in the existing native atlases. -/
theorem contMDiff_forward : ContMDiff (𝓡 6) ProductModel ∞ forward := by
  have : Fact (Module.finrank ℝ Normal = 3 + 1) := ⟨by simp [Normal]⟩
  have hb : ContMDiff (𝓡 6) 𝓘(ℝ, Base) ∞ (fun p : Complement => (forward p).1) :=
    contMDiff_inv_normalRadius.smul contMDiff_complement_base
  have hn : ContMDiff (𝓡 6) 𝓘(ℝ, Normal) ∞
      (fun p : Complement => (normalRadius p)⁻¹ • normal p.val.val) :=
    contMDiff_inv_normalRadius.smul contMDiff_complement_normal
  have hu : ContMDiff (𝓡 6) (𝓡 3) ∞ (fun p : Complement => (forward p).2) :=
    hn.codRestrict_sphere normalized_normal_mem_sphere
  exact hb.prodMk hu

/-- Smoothness of the inverse formula before its two native restrictions. -/
theorem contMDiff_inverseAmbient :
    ContMDiff ProductModel 𝓘(ℝ, Ambient) ∞
      (fun q : Base × NormalSphere => inverseAmbient q.1 q.2) := by
  have : Fact (Module.finrank ℝ Normal = 3 + 1) := ⟨by simp [Normal]⟩
  have hs : ContMDiff ProductModel 𝓘(ℝ, ℝ) ∞
      (fun q : Base × NormalSphere => inverseScale q.1) :=
    contDiff_inverseScale.comp_contMDiff contMDiff_fst
  have hu : ContMDiff ProductModel 𝓘(ℝ, Normal) ∞
      (fun q : Base × NormalSphere => q.2.val) :=
    (contMDiff_coe_sphere (n := 3)).comp contMDiff_snd
  have hp : ContMDiff ProductModel 𝓘(ℝ, Base × Normal) ∞
      (fun q : Base × NormalSphere => (q.1, q.2.val)) :=
    contMDiff_fst.prodMk_space hu
  have hj : ContMDiff ProductModel 𝓘(ℝ, Ambient) ∞
      (fun q : Base × NormalSphere => join q.1 q.2.val) :=
    split.symm.contDiff.comp_contMDiff hp
  exact hs.smul hj

theorem contMDiff_inverseSphere :
    ContMDiff ProductModel (𝓡 6) ∞
      (fun q : Base × NormalSphere => (inverse q).val) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  exact contMDiff_inverseAmbient.codRestrict_sphere
    (fun q => inverseAmbient_mem_sphere q.1 q.2)

/-- The inverse is smooth into the original open-subset atlas. -/
theorem contMDiff_inverse : ContMDiff ProductModel (𝓡 6) ∞ inverse :=
  (ContMDiff.subtypeVal_comp_iff complement inverse).mp contMDiff_inverseSphere

/-- The standard six-sphere minus its equatorial two-sphere is smoothly
`ℝ³ × S³`, with the actual pre-existing atlases on both sides. -/
def diffeomorph : Complement ≃ₘ⟮𝓡 6, ProductModel⟯ Base × NormalSphere where
  toEquiv := homeomorph.toEquiv
  contMDiff_toFun := contMDiff_forward
  contMDiff_invFun := contMDiff_inverse

@[simp] theorem diffeomorph_apply (p : Complement) :
    diffeomorph p = forward p := rfl

@[simp] theorem diffeomorph_symm_apply (q : Base × NormalSphere) :
    diffeomorph.symm q = inverse q := rfl

/-- Forgetting smoothness recovers the original explicit homeomorphism. -/
@[simp] theorem diffeomorph_toHomeomorph :
    diffeomorph.toHomeomorph = homeomorph := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
