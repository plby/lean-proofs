import Wikipedia.SmoothSixDPoincare.SmoothFlowEquation
import Wikipedia.SmoothSixDPoincare.SmoothLocalInverseNeighborhood

/-!
# Smooth solutions of the rescaled flow equation

The implicit function takes initial point and elapsed time to an entire
continuous curve. It is smooth on one open parameter neighborhood. Its
uniqueness statement retains the original local graph chart, so a genuine
integral curve in that chart can be identified with the implicit solution.
-/

noncomputable section

open Set ContinuousMap Filter Topology
open scoped unitInterval ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def flowImplicitData (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ImplicitFunctionData ℝ ((E × ℝ) × C(I, E)) C(I, E) (E × ℝ) :=
  HasStrictFDerivAt.implicitFunctionDataOfProdDomain
    ((contDiff_flowEquation v hv).contDiffAt.hasStrictFDerivAt (by simp))
    (flowEquation_partial_invertible v hv x)

def flowGraphChart (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    OpenPartialHomeomorph ((E × ℝ) × C(I, E)) (C(I, E) × (E × ℝ)) :=
  (flowImplicitData v hv x).toOpenPartialHomeomorph

theorem flowGraphChart_apply (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    (q : (E × ℝ) × C(I, E)) : flowGraphChart v hv x q = (flowEquation v q, q.1) := rfl

theorem flowGraphChart_base_source (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ((x, 0), ContinuousMap.const I x) ∈ (flowGraphChart v hv x).source :=
  (flowImplicitData v hv x).pt_mem_toOpenPartialHomeomorph_source

theorem flowGraphChart_base (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    flowGraphChart v hv x ((x, 0), ContinuousMap.const I x) = (0, (x, 0)) := by
  rw [flowGraphChart_apply, flowEquation_base]

def implicitFlowCurve (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    (p : E × ℝ) : C(I, E) :=
  ((flowGraphChart v hv x).symm (0, p)).2

theorem implicitFlowCurve_base (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    implicitFlowCurve v hv x (x, 0) = ContinuousMap.const I x := by
  have h := (flowGraphChart v hv x).left_inv (flowGraphChart_base_source v hv x)
  rw [flowGraphChart_base] at h
  exact congrArg Prod.snd h

theorem implicitFlowCurve_of_source (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E)
    {p : E × ℝ} {a : C(I, E)} (ha : (p, a) ∈ (flowGraphChart v hv x).source)
    (hF : flowEquation v (p, a) = 0) : implicitFlowCurve v hv x p = a := by
  have h := (flowGraphChart v hv x).left_inv ha
  rw [flowGraphChart_apply, hF] at h
  exact congrArg Prod.snd h

theorem exists_smooth_implicitFlowCurve_neighborhood (v : C(E, E))
    (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ U : Set (E × ℝ), IsOpen U ∧ (x, 0) ∈ U ∧
      ContDiffOn ℝ ∞ (implicitFlowCurve v hv x) U ∧
      ∀ p ∈ U, flowEquation v (p, implicitFlowCurve v hv x p) = 0 := by
  let g := flowGraphChart v hv x
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_flowEquation v hv).prodMk contDiff_fst
  have hd : (fderiv ℝ g ((x, 0), ContinuousMap.const I x)).IsInvertible :=
    (flowImplicitData v hv x).isInvertible_fderiv_prodFun
  obtain ⟨V, hV, hxV, hVtarget, hsmooth⟩ := exists_smooth_inverse_neighborhood g hg
    (flowGraphChart_base_source v hv x) hd
  have hzero : g ((x, 0), ContinuousMap.const I x) = (0, (x, 0)) :=
    flowGraphChart_base v hv x
  rw [hzero] at hxV
  refine ⟨(fun p : E × ℝ => ((0 : C(I, E)), p)) ⁻¹' V,
    hV.preimage (continuous_const.prodMk continuous_id), hxV, ?_, ?_⟩
  · exact (hsmooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hp => hp)).snd
  · intro p hp
    have h := g.right_inv (hVtarget hp)
    have hfst : (g.symm (0, p)).1 = p := congrArg Prod.snd h
    have hval : flowEquation v (g.symm (0, p)) = 0 := congrArg Prod.fst h
    change flowEquation v (p, (g.symm (0, p)).2) = 0
    nth_rw 1 [← hfst]
    exact hval

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
