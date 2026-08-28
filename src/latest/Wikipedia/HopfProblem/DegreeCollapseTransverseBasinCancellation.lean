import Wikipedia.HopfProblem.DegreeCollapseCancellationBasinFactorizations

/-!
# Exact native cancellation from transverse actual basin sheets

Any smooth transverse sheets through the reference point, lying locally
in the two actual endpoint basins, force the cancellation sheets to be
transverse. The checked native construction then removes exactly the
chosen critical pair and preserves all exterior function germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}
  {U V H H' X Y : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]

theorem NativeConnectionCancellationData.transverse_of_native_basin_sheets
    (D : NativeConnectionCancellationData (E := E) f p q m)
    {F : X → M} {G : Y → M} {x : X} {y : Y}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Tendsto (fun t => D.flow t (F z)) atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Tendsto (fun t => D.flow t (G z)) atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y) : D.Transverse := by
  obtain ⟨u, hu, hu0, hFu⟩ := D.outgoing_basin_factorization hF hx hFbasin
  obtain ⟨v, hv, hv0, hGv⟩ := D.incoming_basin_factorization hG hy hGbasin
  apply D.transverse_of_native_sheets
  exact TransverseGerms.native_transversality_of_sheet_factorizations
    (D.outgoingSheet_properties.1.mdifferentiableAt (by simp))
    (D.incomingSheet_properties.1.mdifferentiableAt (by simp))
    hu hv hu0 hv0 hFu hGv (hy.trans hx.symm) htrans

theorem NativeConnectionCancellationData.cancel_of_transverse_basin_sheets
    (D : NativeConnectionCancellationData (E := E) f p q m)
    {F : X → M} {G : Y → M} {x : X} {y : Y}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Tendsto (fun t => D.flow t (F z)) atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Tendsto (fun t => D.flow t (G z)) atTop (𝓝 p))
    (htrans : NativeTransversality.At I I' 𝓘(ℝ, E) F G x y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f))
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f)
    (hpq : f p < f q) {c d : ℝ} (hc : c < f p) (hd : f q < d)
    (hpair : ∀ z ∈ criticalPoints E f, f z ∈ Icc c d → z = p ∨ z = q) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
      ∀ z, f z ∉ Ioo c d → g =ᶠ[𝓝 z] f :=
  D.cancel (D.transverse_of_native_basin_sheets hF hG hx hy hFbasin hGbasin htrans)
    hf hm hinj hp hq hpq hc hd hpair

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
