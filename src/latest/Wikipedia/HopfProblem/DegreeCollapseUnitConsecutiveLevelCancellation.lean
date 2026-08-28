import Wikipedia.HopfProblem.DegreeCollapseConsecutiveTransversePairCancellation
import Wikipedia.HopfProblem.DegreeCollapseUnitTransverseIsotopyRealization

/-!
# A unit transverse native level isotopy cancels a consecutive pair relatively

Construct the complete flow and actual transverse ambient basin tubes from
the level data. The retained critical germs supply all native Morse models.
The original consecutive values permit cancellation without restrictions on
other lower endpoints. The original upper cut and all surviving indices stay
fixed. Constructing the unit intersection remains a separate geometric step.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ} {m : ℕ}
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem AdaptedSurgeryWindows.cancel_unit_consecutive_level_isotopy_below_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (p q : criticalPoints E f) {a b : ℝ} (hpa : f p < a) (haq : a < f q) (hqb : f q < b)
    (hconsecutive : ∀ s : criticalPoints E f, ¬ (f p < f s ∧ f s < f q))
    (hindex : nativeMorseIndex E f q = nativeMorseIndex E f p + 1)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) :
    letI := RegularLevel.chartedSpace hf ha
    ∀ P : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = a} {y : M // f y = a} ∞,
      IsotopicToIdentity P →
      {z : {y : M // f y = a} | Tendsto (fun t => S.flow t z.val) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t (P z).val) atTop (𝓝 p.val)}.ncard = 1 →
      ∀ (α : X → {y : M // f y = a}) (β : Y → {y : M // f y = a}) (x : X) (y : Y),
        MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
        MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y → β y = α x →
        NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
        (∀ᶠ u in 𝓝 x, Tendsto (fun t => S.flow t (α u).val) atBot (𝓝 q.val)) →
        (∀ᶠ u in 𝓝 y, Tendsto (fun t => S.flow t (P (β u)).val) atTop (𝓝 p.val)) →
        ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
          InjOn g (criticalPoints E g) ∧
          (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
          (∀ w, w ∈ criticalPoints E g ↔ w ∈ criticalPoints E f ∧ w ≠ p.val ∧ w ≠ q.val) ∧
          (∀ w ∈ criticalPoints E g, nativeMorseIndex E g w = nativeMorseIndex E f w) ∧
          (∀ w, b ≤ f w → g =ᶠ[𝓝 w] f) ∧ ∀ w, g w < b ↔ f w < b := by
  let _ := RegularLevel.chartedSpace hf ha
  intro P hP hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨V, G, hV, hG, hzero, hdesc, hgerms, hzq, hzp, hunique, _, _,
      hC, hD, hC0, hD0, hCbasin, hDbasin, htubes⟩ :=
    S.realize_unit_transverse_level_isotopy hf q p haq hpa ha P hP hcount
      α β x y hα hβ hcross htrans hαbasin hβbasin
  have hmodels (z : M) (hz : z ∈ criticalPoints E f) :
      ∃ c : SignedMorseChart (E := E) f z, ∀ᶠ w in 𝓝 z, V w = c.descentField w := by
    refine ⟨(S.data ⟨z, hz⟩).chart, ?_⟩
    filter_upwards [hgerms z hz, S.critical_model_germ ⟨z, hz⟩] with w hw hw'
    exact hw.trans hw'
  exact cancel_consecutive_transverse_pair_below_cut hf hm S.distinct hdim
    hV G hG hzero hdesc hmodels p q (hpa.trans haq) hconsecutive hindex hqb
      hzp hzq hunique hC hD hC0 hD0 hCbasin hDbasin htubes

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
