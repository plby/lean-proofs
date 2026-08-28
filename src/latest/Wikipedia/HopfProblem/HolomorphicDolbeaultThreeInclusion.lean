import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFunctions

/-!
# The actual holomorphic-to-smooth sheaf inclusion

All sections and their pointwise scalar actions retain the original
complex atlas; scalar restriction changes only differentiability proofs.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Functions

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

def inclusionLinearMap (U : Opens M) :
    HolomorphicSection E M U →ₗ[ℂ] SmoothSection E M U where
  toFun := inclusionSection E M U
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusionLinearMap_apply (U : Opens M) (s : HolomorphicSection E M U) :
    inclusionLinearMap E M U s = inclusionSection E M U s := rfl

/-- Inclusion of the original holomorphic sheaf into its actual smooth sheaf. -/
def inclusion : holomorphicSheaf E M ⟶ smoothSheaf E M where
  hom :=
    { app U := AddCommGrpCat.ofHom (inclusionLinearMap E M U.unop).toAddMonoidHom
      naturality _ _ _ := rfl }

/-- The actual inclusion is injective, without any geometric hypotheses. -/
instance inclusion_mono : Mono (inclusion E M) := by
  have h (U : (Opens (TopCat.of M))ᵒᵖ) : Mono ((inclusion E M).hom.app U) := by
    apply ConcreteCategory.mono_of_injective
    intro f g he
    exact ContMDiffMap.ext fun x => congrArg (fun s : SmoothSection E M U.unop => s x) he
  have : Mono (inclusion E M).hom := NatTrans.mono_of_mono_app _
  exact (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of M)).mono_of_mono_map this

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Functions
