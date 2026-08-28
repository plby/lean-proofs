import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainAppend
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainRetarget
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainLength
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainDimension
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyStandardCap

/-!
# Retaining native standard sphere components in a full handle chain

This additional property does not change the underlying attachment chain.
It records native smooth sphere coordinates for every capped component and
is preserved by initial and terminal coordinate changes and concatenation.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {dimension : ℕ}
  {U V W : SmoothBoundaryBody J} {k : ℕ}

def HasStandardCaps (c : FullSmoothHandleChain J dimension U V k) : Prop := by
  induction c with
  | nil _ => exact True
  | birth _ _ _ _ ih => exact ih
  | interior _ _ _ _ _ ih => exact ih
  | @cap U V W k N _ _ _ j hj hopen hdim r tail ih =>
      exact U.HasStandardCapSphere j hopen ∧ ih

theorem hasStandardCaps_retarget (c : FullSmoothHandleChain J dimension U V k)
    (e : SmoothBoundaryBody.Equiv V W) (hc : c.HasStandardCaps) :
    (c.retarget e).HasStandardCaps := by
  induction c with
  | nil _ => trivial
  | birth D hdim r tail ih => exact ih e hc
  | interior A P hdim r tail ih => exact ih e hc
  | cap j hj hopen hdim r tail ih => exact ⟨hc.1, ih e hc.2⟩

theorem hasStandardCaps_castLength (c : FullSmoothHandleChain J dimension U V k)
    {l : ℕ} (h : k = l) (hc : c.HasStandardCaps) : (c.castLength h).HasStandardCaps := by
  subst l
  exact hc

theorem hasStandardCaps_castDimension (c : FullSmoothHandleChain J dimension U V k)
    {dimension' : ℕ} (h : dimension = dimension') (hc : c.HasStandardCaps) :
    (c.castDimension h).HasStandardCaps := by
  subst dimension'
  exact hc

variable [FiniteDimensional ℝ G] [J.Boundaryless]

theorem hasStandardCaps_rebase (c : FullSmoothHandleChain J dimension U W k)
    (e : SmoothBoundaryBody.Equiv U V) (hc : c.HasStandardCaps) :
    (c.rebase e).HasStandardCaps := by
  cases c with
  | nil _ => trivial
  | birth D hdim r tail => exact hc
  | interior A P hdim r tail => exact hc
  | cap j hj hopen hdim r tail =>
      exact ⟨SmoothBoundaryBody.hasStandardCapSphere_postcompose j hopen e hc.1, hc.2⟩

theorem hasStandardCaps_append (c : FullSmoothHandleChain J dimension U V k)
    {l : ℕ} (tail : FullSmoothHandleChain J dimension V W l)
    (hc : c.HasStandardCaps) (ht : tail.HasStandardCaps) :
    (c.append tail).HasStandardCaps := by
  induction c with
  | nil r => exact tail.hasStandardCaps_rebase r.symm ht
  | birth D hdim r c ih => exact ih tail hc ht
  | interior A P hdim r c ih => exact ih tail hc ht
  | cap j hj hopen hdim r c ih => exact ⟨hc.1, ih tail hc.2 ht⟩

end Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
