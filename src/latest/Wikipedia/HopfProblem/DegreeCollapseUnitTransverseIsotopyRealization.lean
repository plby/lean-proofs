import Wikipedia.HopfProblem.DegreeCollapseUnitLevelIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelBasinSheets

/-!
# Complete unique connection with actual transverse ambient basin tubes

The native holonomy realization retains both whole-level basin formulas.
These transfer the supplied transverse level germs to the realized flow.
Its actual flow cylinder then constructs transverse ambient basin tubes
through the same unique connection. These maps do not depend on later
changes to the Morse function's critical values.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem AdaptedSurgeryWindows.realize_unit_transverse_level_isotopy
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) {a : ℝ} (hpa : a < f p) (hqa : f q < a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) :
    let _ := RegularLevel.chartedSpace hf ha
    ∀ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = a} {y : M // f y = a} ∞,
      IsotopicToIdentity P →
      {x : {y : M // f y = a} | Tendsto (fun t => S.flow t x.val) atBot (𝓝 p.val) ∧
        Tendsto (fun t => S.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 →
      ∀ (α : X → {y : M // f y = a}) (β : Y → {y : M // f y = a}) (x : X) (y : Y),
        MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
        MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y → β y = α x →
        NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
        (∀ᶠ u in 𝓝 x, Tendsto (fun t => S.flow t (α u).val) atBot (𝓝 p.val)) →
        (∀ᶠ u in 𝓝 y, Tendsto (fun t => S.flow t (P (β u)).val) atTop (𝓝 q.val)) →
        ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
            (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
          (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ criticalPoints E f, V z = 0) ∧
          (∀ z, z ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
          (∀ z ∈ criticalPoints E f, ∀ᶠ w in 𝓝 z, V w = S.field w) ∧
          Tendsto (fun t => G t (α x).val) atBot (𝓝 p.val) ∧
          Tendsto (fun t => G t (α x).val) atTop (𝓝 q.val) ∧
          (∀ z, Tendsto (fun t => G t z) atBot (𝓝 p.val) →
            Tendsto (fun t => G t z) atTop (𝓝 q.val) → ∃ t, G t (α x).val = z) ∧
          (∀ (z : {w : M // f w = a}) w,
            Tendsto (fun t => G t z.val) atBot (𝓝 w) ↔
              Tendsto (fun t => S.flow t z.val) atBot (𝓝 w)) ∧
          (∀ (z : {w : M // f w = a}) w,
            Tendsto (fun t => G t z.val) atTop (𝓝 w) ↔
              Tendsto (fun t => S.flow t (P z).val) atTop (𝓝 w)) ∧
          let C : X × ℝ → M := fun u => G u.2 (α u.1).val
          let D : Y × ℝ → M := fun u => G u.2 (β u.1).val
          MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) C (x, 0) ∧
          MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) D (y, 0) ∧
          C (x, 0) = (α x).val ∧ D (y, 0) = (α x).val ∧
          (∀ᶠ u in 𝓝 (x, (0 : ℝ)), Tendsto (fun t => G t (C u)) atBot (𝓝 p.val)) ∧
          (∀ᶠ u in 𝓝 (y, (0 : ℝ)), Tendsto (fun t => G t (D u)) atTop (𝓝 q.val)) ∧
          NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ))
            𝓘(ℝ, E) C D (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf ha
  change ∀ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      {y : M // f y = a} {y : M // f y = a} ∞,
    IsotopicToIdentity P →
    {x : {y : M // f y = a} | Tendsto (fun t => S.flow t x.val) atBot (𝓝 p.val) ∧
      Tendsto (fun t => S.flow t (P x).val) atTop (𝓝 q.val)}.ncard = 1 → _
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, z, hV, hG, hzero, hdesc, hgerms, -, -, hunique, hback, hforward⟩ :=
    S.realize_unit_level_isotopy hf p q hpa hqa ha P hP hcount
  have hαG : ∀ᶠ u in 𝓝 x, Tendsto (fun t => G t (α u).val) atBot (𝓝 p.val) := by
    filter_upwards [hαbasin] with u hu
    exact (hback (α u) p.val).mpr hu
  have hβG : ∀ᶠ u in 𝓝 y, Tendsto (fun t => G t (β u).val) atTop (𝓝 q.val) := by
    filter_upwards [hβbasin] with u hu
    exact (hforward (β u) q.val).mpr hu
  have hxforward : Tendsto (fun t => G t (α x).val) atTop (𝓝 q.val) := by
    have hh := hβG.self_of_nhds
    rwa [hcross] at hh
  obtain ⟨s, hs⟩ := hunique (α x).val hαG.self_of_nhds hxforward
  have huniq (w : M) (hwb : Tendsto (fun t => G t w) atBot (𝓝 p.val))
      (hwf : Tendsto (fun t => G t w) atTop (𝓝 q.val)) : ∃ t, G t (α x).val = w := by
    obtain ⟨t, ht⟩ := hunique w hwb hwf
    refine ⟨t - s, ?_⟩
    rw [← hs, ← G.map_add, sub_add_cancel, ht]
  refine ⟨V, G, hV, hG, hzero, hdesc, hgerms, hαG.self_of_nhds, hxforward,
    huniq, hback, hforward, ?_⟩
  exact FlowSuspension.native_transverse_basin_tubes_of_level_maps hf ha hV G hG
    (fun w hw => hdesc w (ha w hw)) α β x y hα hβ hcross htrans hαG hβG

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
