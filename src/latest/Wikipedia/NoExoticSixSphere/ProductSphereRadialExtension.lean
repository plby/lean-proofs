import Wikipedia.NoExoticSixSphere.ProductSphereAmbient

/-!
# Radial extension of a map on the genuine product of spheres

The extension uses both actual radial retractions. Its restriction to the
native product inclusion is exactly the original map, and its ambient
differential composed with that inclusion's differential is the original
manifold differential.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductSphereLevelEquations

variable {E G F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def extend (a : UnitSphere E × UnitSphere G) (g : UnitSphere E × UnitSphere G → F) :
    Ambient E G → F := g ∘ retract a

theorem extend_inclusion (a : UnitSphere E × UnitSphere G)
    (g : UnitSphere E × UnitSphere G → F) (x : UnitSphere E × UnitSphere G) :
    extend a g (inclusion x) = g x := by
  change g (retract a (inclusion x)) = g x
  rw [retract_inclusion]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ G = n + 1)]

theorem contDiffAt_extend (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x) :
    ContDiffAt ℝ ∞ (extend a g) (inclusion x) := by
  have hg' : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g (retract a (inclusion x)) := by
    rw [retract_inclusion]
    exact hg
  exact (hg'.comp (inclusion x) (contMDiffAt_retract (m := m) (n := n) a x)).contDiffAt

theorem differential_extend_comp_inclusion (a : UnitSphere E × UnitSphere G)
    {g : UnitSphere E × UnitSphere G → F} {x : UnitSphere E × UnitSphere G}
    (hg : ContMDiffAt ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) ∞ g x) :
    (fderiv ℝ (extend a g) (inclusion x)).comp (inclusionDifferential (m := m) (n := n) x) =
      mfderiv ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, F) g x := by
  have he : extend a g ∘ inclusion = g := funext (extend_inclusion a g)
  have h := mfderiv_comp x
    ((contDiffAt_extend a hg).differentiableAt (by simp)).mdifferentiableAt
    ((contMDiff_inclusion (m := m) (n := n)).mdifferentiableAt (by simp))
  rw [he, mfderiv_eq_fderiv] at h
  exact h.symm

end NoExoticSixSphere.ProductSphereLevelEquations
