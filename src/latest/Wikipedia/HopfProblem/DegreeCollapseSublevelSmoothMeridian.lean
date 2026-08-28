import Wikipedia.HopfProblem.DegreeCollapseSublevelFirstTwoHandle
import Wikipedia.HopfProblem.DegreeCollapseSmoothCappedMeridian
import Wikipedia.HopfProblem.DegreeCollapseFirstOneHandleBranches

/-!
# A capped smooth meridian below a cut with a unique minimum

The actual first minimum belt gives a native standard sphere below the
first two-handle. Its simple connectivity supplies the cap. Smoothing
retains the entire pole disk and its unique whole-belt intersection.
Every upper-level forward endpoint is either the minimum or this handle.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_smooth_first_two_meridian_below_cut
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) {b : ℝ} (m q : criticalPoints E f)
    (hq : nativeMorseIndex E f q = 2) (hqb : f q < b)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m)
    (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace hf (A.data q).upper_regular
    ∃ (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (A.data q).chart.NegativeCoordinates)
      (γ : C(Hemisphere.Sphere 2, (A.data q).UpperLevel)),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ γ ∧
      (∀ x ∈ BeltMeridianSphere.fixedPoleCap,
        γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) ∧
      ∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
        γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w := by
  let _ := RegularLevel.chartedSpace hf (A.data q).upper_regular
  let _ := RegularLevel.isManifold hf (A.data q).upper_regular
  have hn : Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 2 :=
    (nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hq
  let _ : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 1 + 1) := ⟨hn⟩
  let _ : SimplyConnectedSpace (A.data q).LowerLevel :=
    A.lower_level_simplyConnected_of_first_two hf hdim m q hq hqb hbefore hminimum
  let L := StandardDiskCoordinates.coordinates hn
  obtain ⟨F, hformula, hF, hcount⟩ :=
    BeltMeridianSphere.exists_capped_meridian_sphere A hf q (by omega) L v s hs hs0
  obtain ⟨γ, hγ, hrel, heq⟩ := BeltMeridianSphere.exists_smooth_preserving_belt
    F hF (A.data q).surgery.beltSphere (fun x w h => ((hcount x w).mp h).1)
  refine ⟨L, γ, hγ, ?_, fun x w => (heq x w).trans (hcount x w)⟩
  intro x hx
  exact (hrel.fst_eq_snd hx).symm.trans
    (hformula x (BeltMeridianSphere.fixedPoleCap_subset_negative hx).le)

theorem AdaptedSurgeryWindows.upper_level_forward_minimum_or_self_below_cut
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (m q : criticalPoints E f) (hqb : f q < b)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (hminimum : ∀ p : criticalPoints E f, f p < b → nativeMorseIndex E f p = 0 → p = m)
    (x : (A.data q).UpperLevel) :
    Tendsto (fun t => A.flow t x.val) atTop (𝓝 m.val) ∨
      Tendsto (fun t => A.flow t x.val) atTop (𝓝 q.val) := by
  by_cases hx : x ∈ range (A.data q).surgery.beltSphere
  · exact Or.inr ((A.belt_basin_iff hf q x).mpr hx)
  · obtain ⟨t, ht⟩ := (A.upper_reaches_lower_iff_not_belt hf q x).mpr hx
    let y : (A.data q).LowerLevel := ⟨A.flow t x.val, ht⟩
    obtain ⟨r, hrzero, hrlow, hlim⟩ := A.lower_level_forward_minimum hf q hbefore y
    have hrm : r = m := hminimum r
      ((hrlow.trans (A.toSurgeryWindows.lower_lt_value q)).trans hqb) hrzero
    rw [hrm] at hlim
    exact Or.inl ((flow_time_atTop_limit_iff A.flow t x.val m.val).mp hlim)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
