import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeExtensionBasic
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationOpenRestriction

/-!
# Smooth extension by the identity across an actual closed support

A common closed support contained in an open subset makes the literal
extension smooth: in that open subset we use its original smooth local
inverse, and outside the support the extension is locally the identity.
This is a proof for the given maps, not an application of an extension
existence theorem or a change of atlas.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge.Extension

open CuspCircleNormalTrivialization.OpenRestriction

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  (I : ModelWithCorners ℝ E H) (U : Opens X)

local notation "IT" => ModelWithCorners.prod (modelWithCornersSelf ℝ ℝ) I

/-- Joint smoothness is checked in the original ambient and open-subtype atlases. -/
theorem extend_joint_contMDiff (F : ℝ → U → U)
    (hF : ContMDiff IT I ∞ (fun p : ℝ × U => F p.1 p.2))
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ s (y : U), y.val ∉ K → F s y = y) :
    ContMDiff IT I ∞ (fun p : ℝ × X => extend U (F p.1) p.2) := by
  intro p
  by_cases hp : p.2 ∈ U
  · let e := opensInclusionPartialDiffeomorph I (n := ∞) U ⟨⟨p.2, hp⟩⟩
    have ht : e.target = (U : Set X) := by
      change (U.openPartialHomeomorphSubtypeCoe ⟨⟨p.2, hp⟩⟩).target = (U : Set X)
      simp
    have hpe : p.2 ∈ e.target := ht ▸ hp
    have he : ContMDiffAt I I ∞ e.symm p.2 :=
      e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hpe)
    have hs : ContMDiffAt IT (modelWithCornersSelf ℝ ℝ) ∞
        (Prod.fst : ℝ × X → ℝ) p := contMDiffAt_fst
    have hx : ContMDiffAt IT I ∞ (Prod.snd : ℝ × X → X) p := contMDiffAt_snd
    have hin : ContMDiffAt IT IT ∞
        (fun q : ℝ × X => (q.1, e.symm q.2)) p := hs.prodMk (he.comp p hx)
    have hout : ContMDiff IT I ∞
        (fun q : ℝ × U => (F q.1 q.2).val) := contMDiff_subtype_val.comp hF
    have hlocal : ContMDiffAt IT I ∞
        (fun q : ℝ × X => (F q.1 (e.symm q.2)).val) p :=
      hout.contMDiffAt.comp p hin
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(U.isOpen.preimage continuous_snd).mem_nhds hp] with q hq
    rw [extend_of_mem U (F q.1) hq]
    have hqe : q.2 ∈ e.target := ht ▸ hq
    have hv : (e.symm q.2).val = q.2 := e.right_inv hqe
    have hi : e.symm q.2 = (⟨q.2, hq⟩ : U) := Subtype.ext hv
    rw [hi]
  · have hpK : p.2 ∉ K := fun hk => hp (hKU hk)
    have hs : ContMDiffAt IT I ∞ (Prod.snd : ℝ × X → X) p := contMDiffAt_snd
    apply hs.congr_of_eventuallyEq
    filter_upwards [(hK.isOpen_compl.preimage continuous_snd).mem_nhds hpK] with q hq
    exact extend_eq_self_of_notMem U (F q.1) (hfix q.1) hq

theorem extend_contMDiff (F : ℝ → U → U)
    (hF : ContMDiff IT I ∞ (fun p : ℝ × U => F p.1 p.2))
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ s (y : U), y.val ∉ K → F s y = y) (s : ℝ) :
    ContMDiff I I ∞ (extend U (F s)) := by
  have hi : ContMDiff I IT ∞ (fun x : X => (s, x)) :=
    contMDiff_const.prodMk contMDiff_id
  exact (extend_joint_contMDiff I U F hF K hK hKU hfix).comp hi

/-- A supported additive family has a genuine global diffeomorphism,
with inverse at negative time. -/
def extendDiffeomorph (F : ℝ → U → U)
    (hzero : ∀ y, F 0 y = y)
    (hadd : ∀ s t y, F (s + t) y = F s (F t y))
    (hF : ContMDiff IT I ∞ (fun p : ℝ × U => F p.1 p.2))
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ s (y : U), y.val ∉ K → F s y = y) (s : ℝ) :
    Diffeomorph I I X X ∞ where
  toEquiv := {
    toFun := extend U (F s)
    invFun := extend U (F (-s))
    left_inv x := by
      rw [← extend_family_add U F hadd, neg_add_cancel, extend_family_zero U F hzero]
    right_inv x := by
      rw [← extend_family_add U F hadd, add_neg_cancel, extend_family_zero U F hzero] }
  contMDiff_toFun := extend_contMDiff I U F hF K hK hKU hfix s
  contMDiff_invFun := extend_contMDiff I U F hF K hK hKU hfix (-s)

@[simp] theorem extendDiffeomorph_apply (F : ℝ → U → U)
    (hzero : ∀ y, F 0 y = y)
    (hadd : ∀ s t y, F (s + t) y = F s (F t y))
    (hF : ContMDiff IT I ∞ (fun p : ℝ × U => F p.1 p.2))
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ s (y : U), y.val ∉ K → F s y = y) (s : ℝ) (x : X) :
    extendDiffeomorph I U F hzero hadd hF K hK hKU hfix s x = extend U (F s) x := rfl

@[simp] theorem extendDiffeomorph_symm_apply (F : ℝ → U → U)
    (hzero : ∀ y, F 0 y = y)
    (hadd : ∀ s t y, F (s + t) y = F s (F t y))
    (hF : ContMDiff IT I ∞ (fun p : ℝ × U => F p.1 p.2))
    (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ s (y : U), y.val ∉ K → F s y = y) (s : ℝ) (x : X) :
    (extendDiffeomorph I U F hzero hadd hF K hK hKU hfix s).symm x =
      extend U (F (-s)) x := rfl

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge.Extension
