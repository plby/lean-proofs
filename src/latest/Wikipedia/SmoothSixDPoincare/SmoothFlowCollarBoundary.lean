import Wikipedia.SmoothSixDPoincare.FlowCollarBoundaryTime
import Wikipedia.SmoothSixDPoincare.SmoothFlowHittingTime

/-!
# Smoothness of the actual flow-collar boundary maps on transverse level pieces

Both directions use their original point maps and the original continuous
entry times. On a smoothly parametrized boundary piece whose image is a
transverse level, the corresponding boundary map is smooth. No smoothness
of an arbitrary homeomorphism or of the entire cornered collar is assumed.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [TopologicalSpace X] [ChartedSpace D X] [IsManifold 𝓘(ℝ, D) ∞ X]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
  {F : Flow ℝ M} (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v)
  {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  {A B : Set M} [CompactSpace B] (d : FlowCollarData F A B)

include hv hcurve hf

theorem contMDiffOn_forwardBoundary {i : X → B} {S : Set X} {b : ℝ}
    (hi : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun x => (i x).val))
    (hfront : ∀ x ∈ S, (i x).val ∈ frontier B)
    (hlevel : ∀ x ∈ S, f (d.homeomorph (i x)).val = b)
    (htrans : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (d.homeomorph (i x)).val
      (v (d.homeomorph (i x)).val) ≠ 0) :
    ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun x => (d.homeomorph (i x)).val) S := by
  have htime : ContinuousOn (entryTime F A) B :=
    continuousOn_entryTime F d.closed_inner d.forward_inner d.strict_inner
      (fun _ hx => d.hits_inner hx)
  have hτ : Continuous (fun x => entryTime F A (i x).val) :=
    htime.comp_continuous hi.continuous (fun x => (i x).property)
  have horbit (x : X) (hx : x ∈ S) :
      F (entryTime F A (i x).val) (i x).val = (d.homeomorph (i x)).val :=
    (d.homeomorph_eq_flow_entryTime (i x) (hfront x hx)).symm
  have hroot : ∀ x ∈ S, f (F (entryTime F A (i x).val) (i x).val) = b := by
    intro x hx
    rw [horbit x hx]
    exact hlevel x hx
  have hder : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (F (entryTime F A (i x).val) (i x).val)
      (v (F (entryTime F A (i x).val) (i x).val)) ≠ 0 := by
    intro x hx
    rw [horbit x hx]
    exact htrans x hx
  exact (contMDiffOn_flowHittingPoint hv F hcurve hf hi hτ.continuousOn hroot hder).congr
    (fun x hx => (horbit x hx).symm)

theorem contMDiffOn_inverseBoundary {i : X → A} {S : Set X} {b : ℝ}
    (hi : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun x => (i x).val))
    (hfront : ∀ x ∈ S, (i x).val ∈ frontier A)
    (hlevel : ∀ x ∈ S, f (d.homeomorph.symm (i x)).val = b)
    (htrans : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (d.homeomorph.symm (i x)).val
      (v (d.homeomorph.symm (i x)).val) ≠ 0) :
    ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun x => (d.homeomorph.symm (i x)).val) S := by
  have hic : Continuous i := hi.continuous.subtype_mk (fun x => (i x).property)
  have hτ : Continuous (fun x => d.inverseBoundaryTime (i x)) :=
    d.continuous_inverseBoundaryTime.comp hic
  have horbit (x : X) (hx : x ∈ S) :
      F (d.inverseBoundaryTime (i x)) (i x).val = (d.homeomorph.symm (i x)).val :=
    d.inverseBoundaryTime_orbit (i x) (hfront x hx)
  have hroot : ∀ x ∈ S, f (F (d.inverseBoundaryTime (i x)) (i x).val) = b := by
    intro x hx
    rw [horbit x hx]
    exact hlevel x hx
  have hder : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (F (d.inverseBoundaryTime (i x)) (i x).val)
      (v (F (d.inverseBoundaryTime (i x)) (i x).val)) ≠ 0 := by
    intro x hx
    rw [horbit x hx]
    exact htrans x hx
  exact (contMDiffOn_flowHittingPoint hv F hcurve hf hi hτ.continuousOn hroot hder).congr
    (fun x hx => (horbit x hx).symm)

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
