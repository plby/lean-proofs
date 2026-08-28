import Wikipedia.HopfProblem.OrbitPairClockFlowEquation
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# Native quotient diffeomorphisms induced by the ambient cylinder flow

The flow sends the whole time-zero slice to the chosen time slice. Its
negative-time inverse sends that whole slice back to time zero. Taking
the spatial coordinates therefore gives an actual native diffeomorphism,
with both inverse identities and smoothness proved. Smooth transition of
the time parameter produces a globally defined ambient isotopy from the
identity to the time-one map.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {G N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

attribute [local instance] cylinderChartedSpace cylinder_isManifold

variable (v : SupportedFlow.Field (E := ℝ × G) (M := ℝ × N))

theorem supportedField_native_flow :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) ∞ (uncurry v.flow) := by
  simpa +instances only [modelWithCornersSelf_prod, cylinderChartedSpace] using v.smooth_flow

theorem smooth_spatial_flow_slice (t a : ℝ) :
    ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, G) ∞ (fun x : N => (v.flow t (a, x)).2) :=
  contMDiff_snd.comp ((supportedField_native_flow v).comp
    (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id)))

variable (hclock : ∀ p : ℝ × N, (v.vector p).1 = clockCutoff p.1)

def clockSliceEquiv (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : N ≃ N where
  toFun := fun x => (v.flow t (0, x)).2
  invFun := fun y => (v.flow (-t) (t, y)).2
  left_inv := by
    intro x
    have hc : (v.flow t (0, x)).1 = t := by
      simpa only [zero_add] using flow_clock_eq_add v hclock (a := 0) (s := t)
        (by norm_num) (by simpa only [zero_add] using ht) x
    have hp : (t, (v.flow t (0, x)).2) = v.flow t (0, x) := Prod.ext hc.symm rfl
    change (v.flow (-t) (t, (v.flow t (0, x)).2)).2 = x
    rw [hp, ← v.flow_add, neg_add_cancel, v.flow_zero]
  right_inv := by
    intro y
    have hc : (v.flow (-t) (t, y)).1 = 0 := by
      simpa only [add_neg_cancel] using flow_clock_eq_add v hclock (a := t) (s := -t)
        ht (by simp) y
    have hp : (0, (v.flow (-t) (t, y)).2) = v.flow (-t) (t, y) := Prod.ext hc.symm rfl
    change (v.flow t (0, (v.flow (-t) (t, y)).2)).2 = y
    rw [hp, ← v.flow_add, add_neg_cancel, v.flow_zero]

def clockSliceDiffeomorph (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Diffeomorph 𝓘(ℝ, G) 𝓘(ℝ, G) N N ∞ where
  toEquiv := clockSliceEquiv v hclock t ht
  contMDiff_toFun := smooth_spatial_flow_slice v t 0
  contMDiff_invFun := smooth_spatial_flow_slice v (-t) t

theorem clockSliceDiffeomorph_apply (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) (x : N) :
    clockSliceDiffeomorph v hclock t ht x = (v.flow t (0, x)).2 := rfl

theorem clockSliceDiffeomorph_symm_apply (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) (y : N) :
    (clockSliceDiffeomorph v hclock t ht).symm y = (v.flow (-t) (t, y)).2 := rfl

theorem clockSlice_one_isotopic :
    Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph.IsotopicToIdentity
      (clockSliceDiffeomorph v hclock 1 (by norm_num)) := by
  let A : ℝ × N → N := fun p => (v.flow (Real.smoothTransition p.1) (0, p.2)).2
  have hs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × N => Real.smoothTransition p.1) :=
    Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, G)) 𝓘(ℝ, G) ∞ A :=
    contMDiff_snd.comp ((supportedField_native_flow v).comp
      (hs.prodMk (contMDiff_const.prodMk contMDiff_snd)))
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro x
    change (v.flow (Real.smoothTransition 0) (0, x)).2 = x
    rw [Real.smoothTransition.zero, v.flow_zero]
  · intro x
    change (v.flow (Real.smoothTransition 1) (0, x)).2 = (v.flow 1 (0, x)).2
    rw [Real.smoothTransition.one]
  · intro s
    have hsT : Real.smoothTransition s ∈ Ioo (-2 : ℝ) 2 :=
      ⟨by linarith [Real.smoothTransition.nonneg s], by linarith [Real.smoothTransition.le_one s]⟩
    exact ⟨clockSliceDiffeomorph v hclock (Real.smoothTransition s) hsT, fun _ => rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
