import Wikipedia.HopfProblem.FundamentalGroupVanKampen
import Wikipedia.HopfProblem.FundamentalGroupSimplyConnected

/-!
# A simply connected patch and overlap preserve the old fundamental group

Use the proved two-open-set van Kampen universal property. The identity
on the old group and the trivial homomorphism on the new group extend to
an actual inverse of the old inclusion. Uniqueness proves the other inverse
identity. Thus the literal inclusion, not an unspecified group isomorphism,
preserves the fundamental group and detects simple connectedness.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachmentConnectivity

open FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] (D : TwoOpenCover X)

section TrivialGroups

variable [Subsingleton D.OverlapGroup] [Subsingleton D.VGroup]

def oldGroupRetraction : FundamentalGroup X D.base →* D.UGroup :=
  D.lift (MonoidHom.id D.UGroup) 1 (by
    apply MonoidHom.ext
    intro g
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg]
    change D.overlapHomU 1 = 1
    exact map_one D.overlapHomU)

theorem oldGroupRetraction_comp_inclusion :
    (oldGroupRetraction D).comp D.inclusionHomU = MonoidHom.id D.UGroup :=
  D.lift_comp_inclusionU (MonoidHom.id D.UGroup) 1 _

theorem inclusion_comp_oldGroupRetraction :
    D.inclusionHomU.comp (oldGroupRetraction D) = MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · apply MonoidHom.ext
    intro g
    change D.inclusionHomU (oldGroupRetraction D (D.inclusionHomU g)) = D.inclusionHomU g
    rw [show oldGroupRetraction D (D.inclusionHomU g) = g from
      DFunLike.congr_fun (oldGroupRetraction_comp_inclusion D) g]
  · apply MonoidHom.ext
    intro g
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg]
    change D.inclusionHomU (oldGroupRetraction D (D.inclusionHomV 1)) = D.inclusionHomV 1
    simp only [map_one]

theorem inclusionU_bijective : Bijective D.inclusionHomU := by
  have hleft : LeftInverse (oldGroupRetraction D) D.inclusionHomU :=
    fun g ↦ DFunLike.congr_fun (oldGroupRetraction_comp_inclusion D) g
  have hright : RightInverse (oldGroupRetraction D) D.inclusionHomU :=
    fun g ↦ DFunLike.congr_fun (inclusion_comp_oldGroupRetraction D) g
  exact ⟨hleft.injective, hright.surjective⟩

def inclusionUEquiv : D.UGroup ≃* FundamentalGroup X D.base :=
  MulEquiv.ofBijective D.inclusionHomU (inclusionU_bijective D)

end TrivialGroups

theorem simplyConnected_iff_old [SimplyConnectedSpace D.V] [SimplyConnectedSpace D.overlap] :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace D.U := by
  let : PathConnectedSpace D.U := isPathConnected_iff_pathConnectedSpace.mp D.pathConnectedU
  let : PathConnectedSpace X :=
    ⟨⟨D.base⟩, fun x y ↦ ⟨(D.pathTo x).symm.trans (D.pathTo y)⟩⟩
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    let : Subsingleton D.UGroup := (inclusionU_bijective D).injective.subsingleton
    exact simplyConnectedSpace_of_fundamentalGroup_subsingleton D.baseUPoint
  · intro h
    let : SimplyConnectedSpace D.U := h
    let : Subsingleton (FundamentalGroup X D.base) :=
      (inclusionU_bijective D).surjective.subsingleton
    exact simplyConnectedSpace_of_fundamentalGroup_subsingleton D.base

end Wikipedia.HopfProblem.DegreeCollapse.AttachmentConnectivity
