import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicDoubleCover

/-!
# Actual local cross products from double-cover equality

Equality on the native double cover forces the cross products of every
genuine local numerator and denominator to agree at any two original
period vectors over the same free base point.  The proof uses the actual
fraction-field pullbacks and evaluates a proved holomorphic germ
identity, so it remains valid at zeros of either denominator.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "ID" => modelWithCornersSelf ℂ DoubleModel

attribute [local instance] coverChartedSpace cover_isManifold
  doubleCoverChartedSpace doubleCover_isManifold

/-- Fibre-independent fraction germs give literal cross products for
every actual local presentation, even at its denominator zeros. -/
theorem local_fraction_cross_product
    (s : HolomorphicMeromorphic.Function IF Cover)
    (hs : leftPullback s = rightPullback s) (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, HolomorphicMeromorphic.holomorphicGerm IF Cover U x q ≠ 0)
    (hrep : ∀ x : U, s ⟨x.val, by trivial⟩ = HolomorphicMeromorphic.fraction IF Cover U p q x)
    (z : TriangleRegularPoint) (v w : ComplexPlane₂)
    (hv : (z, v) ∈ U) (hw : (z, w) ∈ U) :
    p ⟨(z, v), hv⟩ * q ⟨(z, w), hw⟩ = p ⟨(z, w), hw⟩ * q ⟨(z, v), hv⟩ := by
  let L := HolomorphicMeromorphic.pullbackOpen ID IF leftProjection U
  let R := HolomorphicMeromorphic.pullbackOpen ID IF rightProjection U
  let T : Opens DoubleCover := L ⊓ R
  have hTL : T ≤ L := inf_le_left
  have hTR : T ≤ R := inf_le_right
  let pL := HolomorphicMeromorphic.holomorphicPullback ID IF leftProjection U p
  let qL := HolomorphicMeromorphic.holomorphicPullback ID IF leftProjection U q
  let pR := HolomorphicMeromorphic.holomorphicPullback ID IF rightProjection U p
  let qR := HolomorphicMeromorphic.holomorphicPullback ID IF rightProjection U q
  let pLT := HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTL pL
  let qLT := HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTL qL
  let pRT := HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTR pR
  let qRT := HolomorphicFunctionSheaf.restrictionAlgHom ID DoubleCover hTR qR
  let x : DoubleCover := (z, (v, w))
  let t : T := ⟨x, ⟨hv, hw⟩⟩
  have hqLT : HolomorphicMeromorphic.holomorphicGerm ID DoubleCover T t qLT ≠ 0 := by
    rw [HolomorphicMeromorphic.holomorphicGerm_restrict ID DoubleCover hTL t qL]
    exact HolomorphicMeromorphic.holomorphicPullback_nonzero_germs ID IF
      leftProjection leftProjection_isOpenMap U q hq (Set.inclusion hTL t)
  have hqRT : HolomorphicMeromorphic.holomorphicGerm ID DoubleCover T t qRT ≠ 0 := by
    rw [HolomorphicMeromorphic.holomorphicGerm_restrict ID DoubleCover hTR t qR]
    exact HolomorphicMeromorphic.holomorphicPullback_nonzero_germs ID IF
      rightProjection rightProjection_isOpenMap U q hq (Set.inclusion hTR t)
  have hleft : leftPullback s ⟨x, by trivial⟩ =
      HolomorphicMeromorphic.fraction ID DoubleCover T pLT qLT t := by
    change HolomorphicMeromorphic.germPullback ID IF leftProjection
      leftProjection_isOpenMap x (s ⟨(z, v), by trivial⟩) = _
    rw [hrep ⟨(z, v), hv⟩]
    exact (HolomorphicMeromorphic.germPullback_fraction ID IF leftProjection
      leftProjection_isOpenMap U p q (Set.inclusion hTL t)).trans
        (HolomorphicMeromorphic.fraction_restrict ID DoubleCover hTL pL qL t).symm
  have hright : rightPullback s ⟨x, by trivial⟩ =
      HolomorphicMeromorphic.fraction ID DoubleCover T pRT qRT t := by
    change HolomorphicMeromorphic.germPullback ID IF rightProjection
      rightProjection_isOpenMap x (s ⟨(z, w), by trivial⟩) = _
    rw [hrep ⟨(z, w), hw⟩]
    exact (HolomorphicMeromorphic.germPullback_fraction ID IF rightProjection
      rightProjection_isOpenMap U p q (Set.inclusion hTR t)).trans
        (HolomorphicMeromorphic.fraction_restrict ID DoubleCover hTR pR qR t).symm
  have hfrac : HolomorphicMeromorphic.fraction ID DoubleCover T pLT qLT t =
      HolomorphicMeromorphic.fraction ID DoubleCover T pRT qRT t :=
    hleft.symm.trans ((congrArg (fun a : HolomorphicMeromorphic.Function ID DoubleCover =>
      a ⟨x, by trivial⟩) hs).trans hright)
  have hcross := (HolomorphicMeromorphic.fraction_eq_iff ID DoubleCover T
    pLT qLT pRT qRT t hqLT hqRT).mp hfrac
  have heval := congrArg (HolomorphicFunctionSheaf.stalkEval ID DoubleCover x) hcross
  exact (HolomorphicFunctionSheaf.stalkEval_germ ID DoubleCover T x t.property
    (pLT * qRT)).symm.trans (heval.trans
      (HolomorphicFunctionSheaf.stalkEval_germ ID DoubleCover T x t.property (pRT * qLT)))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
