import Wikipedia.HopfProblem.DegreeCollapseCancellationBasinCharts
import Wikipedia.HopfProblem.DegreeCollapseNativePlaneFactorization

/-!
# Actual smooth basin sheets factor through the cancellation sheets

The exact native basin-plane charts and their explicit coordinate
retractions construct smooth factor germs. Thus any smooth sheet lying
in the relevant actual endpoint basin has tangent image contained in
the corresponding cancellation sheet's tangent image.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}
  {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
  {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]

open Classical in
theorem NativeConnectionCancellationData.outgoing_basin_factorization
    (D : NativeConnectionCancellationData (E := E) f p q m)
    {F : X → M} {x : X} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Tendsto (fun t => D.flow t (F y)) atBot (𝓝 q)) :
    ∃ u : X → ℝ × MorseHandle.NegativeSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.NegativeSpace D.σ) u x ∧ u x = 0 ∧
      F =ᶠ[𝓝 x] (D.outgoingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.outgoing_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × A) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inl ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ A)).prod
      (ContinuousLinearMap.fst ℝ ℝ A)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × A) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × A) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
      (hb : Tendsto (fun t => D.flow t (P w)) atBot (𝓝 q)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.1), ?_⟩
    exact Prod.ext (Prod.ext rfl hz) rfl
  exact TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
    (hx.trans hzero.symm) (fun y => Tendsto (fun t => D.flow t y) atBot (𝓝 q))
    hp hbasin hmodel

open Classical in
theorem NativeConnectionCancellationData.incoming_basin_factorization
    (D : NativeConnectionCancellationData (E := E) f p q m)
    {F : X → M} {x : X} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Tendsto (fun t => D.flow t (F y)) atTop (𝓝 p)) :
    ∃ u : X → ℝ × MorseHandle.PositiveSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × MorseHandle.PositiveSpace D.σ) u x ∧ u x = 0 ∧
      F =ᶠ[𝓝 x] (D.incomingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.incoming_basin_chart
  let A := MorseHandle.NegativeSpace D.σ
  let B := MorseHandle.PositiveSpace D.σ
  let L : (ℝ × B) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inr ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ B)).prod
      (ContinuousLinearMap.fst ℝ ℝ B)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × B) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × B) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
      (hb : Tendsto (fun t => D.flow t (P w)) atTop (𝓝 p)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.2), ?_⟩
    exact Prod.ext (Prod.ext hz rfl) rfl
  exact TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
    (hx.trans hzero.symm) (fun y => Tendsto (fun t => D.flow t y) atTop (𝓝 p))
    hp hbasin hmodel

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
