import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeHomeomorph
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeSmoothFunctions

/-!
# The native smooth equatorial tube chart

The literal open tube of radius `r ≤ 1` is diffeomorphic to the ordinary
product of the standard two-sphere with the open normal four-ball. The
maps are exactly the existing tube homeomorphism, and all sphere,
Euclidean, product, and open-subset atlases remain unchanged.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

local notation "ProductModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, Normal)

/-- The original inclusion of the open tube into Euclidean seven-space. -/
theorem contMDiff_openTube_ambient (r : ℝ) :
    ContMDiff (𝓡 6) 𝓘(ℝ, Ambient) ∞
      (fun p : openTube r => p.val.val) := by
  have : Fact (Module.finrank ℝ Ambient = 6 + 1) := ⟨by simp [Ambient]⟩
  exact (contMDiff_coe_sphere (n := 6)).comp
    (contMDiff_subtype_val (U := openTube r))

theorem contMDiff_openForward (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff ProductModel (𝓡 6) ∞ (openForward r hr1) := by
  apply (ContMDiff.subtypeVal_comp_iff (openTube r) (openForward r hr1)).mp
  exact Smooth.contMDiff_point_normalBall r hr1

theorem contMDiff_openInverse_fst (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff (𝓡 6) (𝓡 2) ∞
      (fun p : openTube r => (openInverse r hr1 p).1) :=
  Smooth.contMDiff_normalizedBase (Subtype.val : openTube r → Sphere)
    (contMDiff_subtype_val (U := openTube r))
    (fun p => p.property.trans_le hr1)

theorem contMDiff_openInverse_snd (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff (𝓡 6) 𝓘(ℝ, Normal) ∞
      (fun p : openTube r => (openInverse r hr1 p).2) := by
  apply (ContMDiff.subtypeVal_comp_iff (normalBall r)
    (fun p : openTube r => (openInverse r hr1 p).2)).mp
  exact contDiff_normal.comp_contMDiff (contMDiff_openTube_ambient r)

theorem contMDiff_openInverse (r : ℝ) (hr1 : r ≤ 1) :
    ContMDiff (𝓡 6) ProductModel ∞ (openInverse r hr1) :=
  (contMDiff_openInverse_fst r hr1).prodMk (contMDiff_openInverse_snd r hr1)

/-- The actual open tube in the original six-sphere, with its native atlas. -/
def openDiffeomorph (r : ℝ) (hr1 : r ≤ 1) :
    OpenDomain r ≃ₘ⟮ProductModel, 𝓡 6⟯ ↥(openTube r) where
  toEquiv := (openHomeomorph r hr1).toEquiv
  contMDiff_toFun := contMDiff_openForward r hr1
  contMDiff_invFun := contMDiff_openInverse r hr1

@[simp] theorem openDiffeomorph_apply (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) :
    openDiffeomorph r hr1 q = openForward r hr1 q := rfl

@[simp] theorem openDiffeomorph_symm_apply (r : ℝ) (hr1 : r ≤ 1) (p : openTube r) :
    (openDiffeomorph r hr1).symm p = openInverse r hr1 p := rfl

/-- Forgetting smoothness gives precisely the existing literal homeomorphism. -/
@[simp] theorem openDiffeomorph_toHomeomorph (r : ℝ) (hr1 : r ≤ 1) :
    (openDiffeomorph r hr1).toHomeomorph = openHomeomorph r hr1 := rfl

@[simp] theorem openDiffeomorph_val_val (r : ℝ) (hr1 : r ≤ 1) (q : OpenDomain r) :
    (openDiffeomorph r hr1 q).val.val = ambient q.1 q.2.val := rfl

@[simp] theorem openDiffeomorph_symm_fst_val (r : ℝ) (hr1 : r ≤ 1) (p : openTube r) :
    ((openDiffeomorph r hr1).symm p).1.val = ‖base p.val.val‖⁻¹ • base p.val.val := rfl

@[simp] theorem openDiffeomorph_symm_snd_val (r : ℝ) (hr1 : r ≤ 1) (p : openTube r) :
    ((openDiffeomorph r hr1).symm p).2.val = normal p.val.val := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
