import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsCharts
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothMultipliers

/-!
# Genuine smooth multipliers on the sphere form sheaf

A smooth sphere function pulls back along the actual two affine
parametrizations.  Multiplying the form coefficients by those pullbacks
preserves their derivative transition, since both chart values refer to
the same actual sphere point.  These literal operations form the smooth
multiplier action and the complex scalar action on the form sheaf.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

/-- The genuine affine pullback of a smooth sphere function. -/
def globalCoefficient (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere) (b : Bool) :
    SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) ℂ :=
  ⟨fun z => g (RiemannSphere.standardCharts.affineMap b z),
    g.contMDiff.comp (affineMap_smooth b)⟩

@[simp] theorem globalCoefficient_apply
    (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere) (b : Bool) (z : ℂ) :
    globalCoefficient g b z = g (RiemannSphere.standardCharts.affineMap b z) := rfl

/-- Literal multiplication of an actual form section by a smooth sphere function. -/
def multiplySection (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere)
    (U : Opens RiemannSphere) (s : Section U) : Section U :=
  sectionMk U
    (fun b => SmoothFunctions.globalRestriction 𝓘(ℝ, ℂ) ℂ (globalCoefficient g b)
      (coordinateOpen U b) * coefficient s b) (by
    intro z hz h₀ hInf
    change g (RiemannSphere.standardCharts.affineMap false z) * coefficient s false ⟨z, h₀⟩ =
      transition z * (g (RiemannSphere.standardCharts.affineMap true z⁻¹) *
        coefficient s true ⟨z⁻¹, hInf⟩)
    rw [condition s z hz h₀ hInf,
      RiemannSphere.standardCharts.affineMap_inversion false z hz]
    exact mul_left_comm _ _ _)

@[simp] theorem multiplySection_apply
    (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere)
    (U : Opens RiemannSphere) (s : Section U) (b : Bool) (z : coordinateOpen U b) :
    coefficient (multiplySection g U s) b z =
      g (RiemannSphere.standardCharts.affineMap b z) * coefficient s b z := rfl

/-- Pointwise coefficient extensionality for actual form-sheaf endomorphisms. -/
theorem sheafEnd_ext {f g : sheaf ⟶ sheaf}
    (h : ∀ (U : Opens RiemannSphere) (s : Section U) (b : Bool) (z : coordinateOpen U b),
      coefficient (f.hom.app (op U) s) b z = coefficient (g.hom.app (op U) s) b z) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact section_ext (h U.unop s)

/-- Actual smooth multiplication as a morphism of the form sheaf. -/
def multiplier (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere) : sheaf ⟶ sheaf where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        ({ toFun := multiplySection g U.unop
           map_zero' := by
             apply section_ext
             intro b z
             exact mul_zero _
           map_add' := by
             intro s t
             apply section_ext
             intro b z
             exact mul_add _ _ _ } : Section U.unop →+ Section U.unop)
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        apply section_ext
        intro b z
        rfl }

/-- Smooth multipliers form the actual endomorphism-ring action. -/
def multiplierRingHom :
    SmoothFunctions.GlobalFunction 𝓘(ℝ, ℂ) RiemannSphere →+* End sheaf where
  toFun := multiplier
  map_zero' := by
    apply sheafEnd_ext
    intro U s b z
    exact zero_mul _
  map_one' := by
    apply sheafEnd_ext
    intro U s b z
    exact one_mul _
  map_add' f g := by
    apply sheafEnd_ext
    intro U s b z
    exact add_mul _ _ _
  map_mul' f g := by
    apply sheafEnd_ext
    intro U s b z
    exact mul_assoc _ _ _

/-- The genuine complex scalar action on the actual form sheaf. -/
def scalarEnd : ℂ →+* End sheaf :=
  multiplierRingHom.comp (SmoothFunctions.constantGlobalRingHom 𝓘(ℝ, ℂ) RiemannSphere)

@[simp] theorem scalarEnd_apply (c : ℂ) (U : Opens RiemannSphere) (s : Section U)
    (b : Bool) (z : coordinateOpen U b) :
    coefficient ((scalarEnd c).asHom.hom.app (op U) s) b z = c * coefficient s b z := rfl

/-- The endomorphism action agrees with the actual pointwise complex
module structure on these derivative-compatible form sections. -/
theorem scalarEnd_eq_smul (c : ℂ) (U : Opens RiemannSphere) (s : Section U) :
    (scalarEnd c).asHom.hom.app (op U) s = c • s := by
  apply section_ext
  intro b z
  rfl

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
