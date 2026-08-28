import Wikipedia.HopfProblem.FundamentalGroupVanKampenSurjectivity
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The exact nonabelian relations of an actual simply connected attachment

Apply the proved topological van Kampen universal property to the quotient
by the normal closure of the original overlap map. When the second chart
has trivial fundamental group, this is precisely the kernel of the actual
first-chart inclusion. No group presentation of the union is assumed.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.OpenCoverFundamentalGroup

open Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] (D : TwoOpenCover X)
  [Subsingleton D.VGroup]

theorem inclusion_surjective : Surjective D.inclusionHomU := by
  apply D.inclusionHomU_surjective_of_overlapHomV_surjective
  intro g
  exact ⟨1, Subsingleton.elim _ _⟩

theorem inclusion_kernel :
    D.inclusionHomU.ker = Subgroup.normalClosure (range D.overlapHomU) := by
  let N := Subgroup.normalClosure (range D.overlapHomU)
  change D.inclusionHomU.ker = N
  have hN : N ≤ D.inclusionHomU.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, rfl⟩
    change D.inclusionHomU (D.overlapHomU a) = 1
    have h := DFunLike.congr_fun D.inclusionHom_compatible a
    change D.inclusionHomU (D.overlapHomU a) = D.inclusionHomV (D.overlapHomV a) at h
    exact h.trans ((congrArg D.inclusionHomV (Subsingleton.elim (D.overlapHomV a) 1)).trans
      (map_one D.inclusionHomV))
  have hc : D.Compatible (QuotientGroup.mk' N) (1 : D.VGroup →* D.UGroup ⧸ N) := by
    apply MonoidHom.ext
    intro a
    change (D.overlapHomU a : D.UGroup ⧸ N) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (mem_range_self a))
  apply le_antisymm ?_ hN
  intro g hg
  have heq := DFunLike.congr_fun (D.lift_comp_inclusionU (QuotientGroup.mk' N) 1 hc) g
  have hg' : D.inclusionHomU g = 1 := hg
  apply (QuotientGroup.eq_one_iff g).mp
  exact heq.symm.trans
    ((congrArg (D.lift (QuotientGroup.mk' N) 1 hc) hg').trans (map_one _))

theorem inclusion_bijective_of_trivial_overlap [Subsingleton D.OverlapGroup] :
    Bijective D.inclusionHomU := by
  refine ⟨?_, inclusion_surjective D⟩
  apply (MonoidHom.ker_eq_bot_iff D.inclusionHomU).mp
  rw [inclusion_kernel D]
  apply le_antisymm ?_ bot_le
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨a, rfl⟩
  change D.overlapHomU a = 1
  exact (congrArg D.overlapHomU (Subsingleton.elim a 1)).trans (map_one _)

end Wikipedia.SmoothSixDPoincare.OpenCoverFundamentalGroup
