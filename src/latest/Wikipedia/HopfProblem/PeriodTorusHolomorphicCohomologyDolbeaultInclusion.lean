import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGeometry

/-!
# Inclusion of native holomorphic torus functions into smooth functions

Restricting scalars in the unchanged native quotient charts proves that
every genuine holomorphic section is a genuine real-smooth section with
identical values. The actual sheaf inclusion is monic.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂

/-- The actual complex-linear inclusion retains every original function value. -/
def inclusionSection (p : PeriodDomain) (U : Opens p.Torus) :
    HolomorphicSection p U →ₗ[ℂ] SmoothSection p U where
  toFun f := ⟨f, by
    have hf := f.contMDiff
    rw [contMDiff_iff] at hf ⊢
    exact ⟨hf.1, fun x y => ((hf.2 x y).of_le (by simp)).restrict_scalars ℝ⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusionSection_apply (p : PeriodDomain) (U : Opens p.Torus)
    (f : HolomorphicSection p U) (x : U) : inclusionSection p U f x = f x := rfl

/-- The actual inclusion of the original holomorphic-function sheaf. -/
def inclusion (p : PeriodDomain) : holomorphicSheaf p ⟶ smoothSheaf p where
  hom :=
    { app U := AddCommGrpCat.ofHom (inclusionSection p U.unop).toAddMonoidHom
      naturality _ _ _ := rfl }

instance inclusion_mono (p : PeriodDomain) : Mono (inclusion p) := by
  have h (U : (Opens (TopCat.of p.Torus))ᵒᵖ) : Mono ((inclusion p).hom.app U) := by
    apply ConcreteCategory.mono_of_injective
    intro f g he
    exact ContMDiffMap.ext fun x => congrArg (fun s : SmoothSection p U.unop => s x) he
  have : Mono (inclusion p).hom := NatTrans.mono_of_mono_app _
  exact (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of p.Torus)).mono_of_mono_map this

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
