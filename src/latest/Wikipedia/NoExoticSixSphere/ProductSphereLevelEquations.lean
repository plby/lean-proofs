import Wikipedia.NoExoticSixSphere.ProductSphereRadialExtension
import Wikipedia.NoExoticSixSphere.ProductSphereNormEquations
import Wikipedia.NoExoticSixSphere.VectorAugmentedSurjection

/-!
# Regular ambient equations for the actual product-sphere level

The two norm equations augment the radial extension of the original
regular map. Their full ambient differential is surjective. The final
equation space is an ordered Hilbert product, with the first sphere's
normal coordinate followed by the second sphere's normal coordinate
and then the original target coordinates.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductSphereLevelEquations

variable {E G F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rawEquations (a : UnitSphere E × UnitSphere G) (g : UnitSphere E × UnitSphere G → F)
    (v : Ambient E G) : (ℝ × ℝ) × F := (normEquations v, extend a g v)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem rawEquations_inclusion (a : UnitSphere E × UnitSphere G)
    (g : UnitSphere E × UnitSphere G → F) (x : UnitSphere E × UnitSphere G) :
    rawEquations a g (inclusion x) = (0, g x) := by
  rw [rawEquations, normEquations_inclusion, extend_inclusion]

def equationCoordinates : ((ℝ × ℝ) × F) ≃L[ℝ] WithLp 2 (ℝ × WithLp 2 (ℝ × F)) :=
  (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ F).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (WithLp 2 (ℝ × F))).symm)

def equations (a : UnitSphere E × UnitSphere G) (g : UnitSphere E × UnitSphere G → F) :
    Ambient E G → WithLp 2 (ℝ × WithLp 2 (ℝ × F)) := equationCoordinates ∘ rawEquations a g

theorem equations_apply (a : UnitSphere E × UnitSphere G)
    (g : UnitSphere E × UnitSphere G → F) (v : Ambient E G) :
    equations a g v = WithLp.toLp 2 (‖v.fst‖ ^ 2 - 1,
      WithLp.toLp 2 (‖v.snd‖ ^ 2 - 1, extend a g v)) := rfl

theorem equations_inclusion (a : UnitSphere E × UnitSphere G)
    (g : UnitSphere E × UnitSphere G → F) (x : UnitSphere E × UnitSphere G) :
    equations a g (inclusion x) = WithLp.toLp 2 (0, WithLp.toLp 2 (0, g x)) := by
  change equationCoordinates (rawEquations a g (inclusion x)) = _
  rw [rawEquations_inclusion]
  rfl

variable {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ G = n + 1)]

theorem contDiffAt_rawEquations (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x) :
    ContDiffAt ℝ ∞ (rawEquations a g) (inclusion x) :=
  contDiff_normEquations.contDiffAt.prodMk (contDiffAt_extend a hg)

theorem surjective_fderiv_rawEquations (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x)
    (hreg : Surjective (mfderiv ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) g x)) :
    Surjective (fderiv ℝ (rawEquations a g) (inclusion x)) := by
  let L := fderiv ℝ normEquations (inclusion x)
  let D := fderiv ℝ (extend a g) (inclusion x)
  have hL : HasFDerivAt normEquations L (inclusion x) :=
    (contDiff_normEquations.differentiable (by simp) _).hasFDerivAt
  have hD : HasFDerivAt (extend a g) D (inclusion x) :=
    ((contDiffAt_extend a hg).differentiableAt (by simp)).hasFDerivAt
  have hpair : fderiv ℝ (rawEquations a g) (inclusion x) = L.prod D := (hL.prodMk hD).fderiv
  rw [hpair]
  apply surjective_vector_augmented_differential L D
    (inclusionDifferential (m := m) (n := n) x) (surjective_fderiv_normEquations x)
  · intro v
    exact congrArg
      (fun A : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ × ℝ ↦ A v)
      (norm_equations_comp_inclusion (m := m) (n := n) x)
  · rw [show D.comp (inclusionDifferential (m := m) (n := n) x) =
        mfderiv ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) g x from differential_extend_comp_inclusion a hg]
    exact hreg

theorem contDiffAt_equations (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x) :
    ContDiffAt ℝ ∞ (equations a g) (inclusion x) :=
  (equationCoordinates (F := F)).contDiff.contDiffAt.comp (inclusion x)
    (contDiffAt_rawEquations a hg)

theorem surjective_fderiv_equations (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x)
    (hreg : Surjective (mfderiv ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) g x)) :
    Surjective (fderiv ℝ (equations a g) (inclusion x)) := by
  rw [equations, fderiv_comp (inclusion x) (equationCoordinates (F := F)).differentiableAt
    ((contDiffAt_rawEquations a hg).differentiableAt (by simp)), ContinuousLinearEquiv.fderiv]
  exact (equationCoordinates (F := F)).surjective.comp (surjective_fderiv_rawEquations a hg hreg)

end NoExoticSixSphere.ProductSphereLevelEquations
