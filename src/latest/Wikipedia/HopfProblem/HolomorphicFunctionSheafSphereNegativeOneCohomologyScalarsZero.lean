import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyScalars
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH0Constancy

/-!
# Actual degree-zero sphere cohomology with its sheaf-induced scalars

Evaluation at the actual point at infinity identifies global
holomorphic sections with the complex numbers. The native degree-zero
Ext comparison is linear for the module induced by the original
pointwise scalar sheaf endomorphisms.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

/-- Evaluation at infinity on the actual algebra of global holomorphic sections. -/
def sphereGlobalSectionsEquiv : GlobalSections 𝓘(ℂ) RiemannSphere ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofBijective (globalSectionsEval 𝓘(ℂ) RiemannSphere ∞) (by
    constructor
    · intro s t h
      apply ContMDiffMap.ext
      intro x
      change s (toTopOpen RiemannSphere ∞) = t (toTopOpen RiemannSphere ∞) at h
      exact (sphere_globalSection_apply_eq s x (toTopOpen RiemannSphere ∞)).trans
        (h.trans (sphere_globalSection_apply_eq t x (toTopOpen RiemannSphere ∞)).symm)
    · intro c
      exact ⟨algebraMap ℂ (GlobalSections 𝓘(ℂ) RiemannSphere) c, rfl⟩)

@[simp] theorem sphereGlobalSectionsEquiv_apply
    (s : GlobalSections 𝓘(ℂ) RiemannSphere) :
    sphereGlobalSectionsEquiv s = s (toTopOpen RiemannSphere ∞) := rfl

/-- The inverse is the literal constant holomorphic section. -/
@[simp] theorem sphereGlobalSectionsEquiv_symm_apply (c : ℂ) :
    sphereGlobalSectionsEquiv.symm c =
      algebraMap ℂ (GlobalSections 𝓘(ℂ) RiemannSphere) c := by
  apply sphereGlobalSectionsEquiv.injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  rfl

/-- The native Ext/global-section comparison is linear for the scalar
action induced by the actual scalar sheaf maps. -/
def sphereH0GlobalLinearEquiv :
    letI := sphereCohomologyModule 0
    CategoryTheory.Sheaf.H.{0} sphereSheaf 0 ≃ₗ[ℂ]
      GlobalSections 𝓘(ℂ) RiemannSphere := by
  letI := sphereCohomologyModule 0
  refine { __ := h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere, map_smul' := ?_ }
  intro c x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality
    (hT := (show Limits.IsTerminal (⊤ : Opens (TopCat.of RiemannSphere)) from
      Limits.isTerminalTop)) (sphereScalarEnd c) x).symm

@[simp] theorem sphereH0GlobalLinearEquiv_apply
    (x : CategoryTheory.Sheaf.H.{0} sphereSheaf 0) :
    letI := sphereCohomologyModule 0
    sphereH0GlobalLinearEquiv x = h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere x := rfl

/-- Genuine degree-zero sphere cohomology is complex-linearly `ℂ`,
by the native comparison followed by evaluation at infinity. -/
def sphereH0LinearEquiv :
    letI := sphereCohomologyModule 0
    CategoryTheory.Sheaf.H.{0} sphereSheaf 0 ≃ₗ[ℂ] ℂ := by
  letI := sphereCohomologyModule 0
  exact sphereH0GlobalLinearEquiv.trans sphereGlobalSectionsEquiv.toLinearEquiv

@[simp] theorem sphereH0LinearEquiv_apply
    (x : CategoryTheory.Sheaf.H.{0} sphereSheaf 0) :
    letI := sphereCohomologyModule 0
    sphereH0LinearEquiv x =
      h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere x (toTopOpen RiemannSphere ∞) := rfl

/-- The inverse is the actual Ext class of the literal constant section. -/
theorem sphereH0LinearEquiv_symm_apply (c : ℂ) :
    letI := sphereCohomologyModule 0
    sphereH0LinearEquiv.symm c =
      (h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere).symm
        (algebraMap ℂ (GlobalSections 𝓘(ℂ) RiemannSphere) c) := by
  let := sphereCohomologyModule 0
  exact congrArg (h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere).symm
    (sphereGlobalSectionsEquiv_symm_apply c)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
