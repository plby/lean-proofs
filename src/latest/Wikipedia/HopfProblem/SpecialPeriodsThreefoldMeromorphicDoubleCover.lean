import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCover
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackRegular

/-!
# The connected double regular cover for meromorphic descent

The two maps retain the same original regular base point and choose
either of two original period vectors.  Equality of their meromorphic
pullbacks is an identity-principle statement on this actual connected
product, with its inherited complex atlas.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

abbrev DoubleModel := ℂ × (ComplexPlane₂ × ComplexPlane₂)
abbrev DoubleCover := TriangleRegularPoint × (ComplexPlane₂ × ComplexPlane₂)

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "ID" => modelWithCornersSelf ℂ DoubleModel

@[instance_reducible] def doubleCoverChartedSpace : ChartedSpace DoubleModel DoubleCover :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ (ComplexPlane₂ × ComplexPlane₂)) DoubleCover)

attribute [local instance] coverChartedSpace cover_isManifold doubleCoverChartedSpace

theorem doubleCover_isManifold : IsManifold ID ω DoubleCover := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ComplexPlane₂ × ComplexPlane₂))
    TriangleRegularPoint (ComplexPlane₂ × ComplexPlane₂)

attribute [local instance] doubleCover_isManifold

/-- The first original fibre vector, at the unchanged free regular base point. -/
def leftProjection : ContMDiffMap ID IF DoubleCover Cover ω :=
  ⟨fun x => (x.1, x.2.1), by
    rw [modelWithCornersSelf_prod (E := ℂ) (F := ComplexPlane₂ × ComplexPlane₂),
      modelWithCornersSelf_prod (E := ℂ) (F := ComplexPlane₂)]
    exact contMDiff_fst.prodMk
      ((ContinuousLinearMap.fst ℂ ComplexPlane₂ ComplexPlane₂).contMDiff.comp contMDiff_snd)⟩

/-- The second original fibre vector, at the unchanged free regular base point. -/
def rightProjection : ContMDiffMap ID IF DoubleCover Cover ω :=
  ⟨fun x => (x.1, x.2.2), by
    rw [modelWithCornersSelf_prod (E := ℂ) (F := ComplexPlane₂ × ComplexPlane₂),
      modelWithCornersSelf_prod (E := ℂ) (F := ComplexPlane₂)]
    exact contMDiff_fst.prodMk
      ((ContinuousLinearMap.snd ℂ ComplexPlane₂ ComplexPlane₂).contMDiff.comp contMDiff_snd)⟩

@[simp] theorem leftProjection_apply (x : DoubleCover) :
    leftProjection x = (x.1, x.2.1) := rfl

@[simp] theorem rightProjection_apply (x : DoubleCover) :
    rightProjection x = (x.1, x.2.2) := rfl

theorem leftProjection_isOpenMap : IsOpenMap leftProjection :=
  IsOpenMap.id.prodMap isOpenMap_fst

theorem rightProjection_isOpenMap : IsOpenMap rightProjection :=
  IsOpenMap.id.prodMap isOpenMap_snd

/-- Both maps have exactly the same original sphere coordinate. -/
theorem projectionSphere_left_eq_right (x : DoubleCover) :
    projectionSphere (toThreefold (leftProjection x)) =
      projectionSphere (toThreefold (rightProjection x)) := by
  simp only [leftProjection_apply, rightProjection_apply, projectionSphere_toThreefold]

def leftPullback : HolomorphicMeromorphic.Function IF Cover →ₐ[ℂ]
    HolomorphicMeromorphic.Function ID DoubleCover :=
  HolomorphicMeromorphic.pullbackAlgHom ID IF leftProjection leftProjection_isOpenMap ⊤

def rightPullback : HolomorphicMeromorphic.Function IF Cover →ₐ[ℂ]
    HolomorphicMeromorphic.Function ID DoubleCover :=
  HolomorphicMeromorphic.pullbackAlgHom ID IF rightProjection rightProjection_isOpenMap ⊤

/-- One equality of genuine fraction germs forces equality on the
entire connected original double cover. -/
theorem leftPullback_eq_rightPullback_of_germ_eq
    (s : HolomorphicMeromorphic.Function IF Cover) (x : DoubleCover)
    (hx : leftPullback s ⟨x, by trivial⟩ = rightPullback s ⟨x, by trivial⟩) :
    leftPullback s = rightPullback s := by
  let : ConnectedSpace (⊤ : Opens DoubleCover) :=
    isConnected_iff_connectedSpace.mp isConnected_univ
  exact HolomorphicMeromorphic.section_eq_of_germ_eq ID DoubleCover
    (leftPullback s) (rightPullback s) ⟨x, by trivial⟩ hx

/-- A nonempty actual holomorphic neighborhood with fibre-independent
values makes the two full meromorphic pullbacks equal everywhere. -/
theorem leftPullback_eq_rightPullback_of_local_factor
    (s : HolomorphicMeromorphic.Function IF Cover) (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (u : U)
    (hp : ∀ x : U, s ⟨x.val, by trivial⟩ =
      HolomorphicMeromorphic.sectionGerm IF Cover U x p)
    (hconstant : ∀ (z : TriangleRegularPoint) (v w : ComplexPlane₂)
      (hv : (z, v) ∈ U) (hw : (z, w) ∈ U), p ⟨(z, v), hv⟩ = p ⟨(z, w), hw⟩) :
    leftPullback s = rightPullback s := by
  let L := HolomorphicMeromorphic.pullbackOpen ID IF leftProjection U
  let R := HolomorphicMeromorphic.pullbackOpen ID IF rightProjection U
  let T : Opens DoubleCover := L ⊓ R
  have hTL : T ≤ L := inf_le_left
  have hTR : T ≤ R := inf_le_right
  let pL := HolomorphicMeromorphic.holomorphicPullback ID IF leftProjection U p
  let pR := HolomorphicMeromorphic.holomorphicPullback ID IF rightProjection U p
  have hrestr : HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTL pL =
      HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTR pR := by
    apply ContMDiffMap.ext
    intro x
    exact hconstant x.val.1 x.val.2.1 x.val.2.2 x.property.1 x.property.2
  let x : DoubleCover := (u.val.1, (u.val.2, u.val.2))
  have hxT : x ∈ T := ⟨u.property, u.property⟩
  let t : T := ⟨x, hxT⟩
  apply leftPullback_eq_rightPullback_of_germ_eq s x
  have hleft := HolomorphicMeromorphic.pullbackSection_holomorphic_representation
    ID IF leftProjection leftProjection_isOpenMap (show U ≤ ⊤ from le_top) s p hp
    (Set.inclusion hTL t)
  have hright := HolomorphicMeromorphic.pullbackSection_holomorphic_representation
    ID IF rightProjection rightProjection_isOpenMap (show U ≤ ⊤ from le_top) s p hp
    (Set.inclusion hTR t)
  calc
    leftPullback s ⟨x, by trivial⟩ =
        HolomorphicMeromorphic.sectionGerm ID DoubleCover L (Set.inclusion hTL t) pL := hleft
    _ = HolomorphicMeromorphic.sectionGerm ID DoubleCover T t
        (HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTL pL) :=
      (HolomorphicMeromorphic.sectionGerm_restrict ID DoubleCover hTL t pL).symm
    _ = HolomorphicMeromorphic.sectionGerm ID DoubleCover T t
        (HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTR pR) :=
      congrArg (HolomorphicMeromorphic.sectionGerm ID DoubleCover T t) hrestr
    _ = HolomorphicMeromorphic.sectionGerm ID DoubleCover R (Set.inclusion hTR t) pR :=
      HolomorphicMeromorphic.sectionGerm_restrict ID DoubleCover hTR t pR
    _ = rightPullback s ⟨x, by trivial⟩ := hright.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
