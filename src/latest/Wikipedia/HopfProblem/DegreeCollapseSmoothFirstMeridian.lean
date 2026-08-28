import Wikipedia.HopfProblem.DegreeCollapseMeridianSphereDerivative
import Wikipedia.HopfProblem.DegreeCollapseFirstHandleBasinControl

/-!
# A smooth transverse sphere at the first positive two-handle

The original boundary supplies the lower cap. The glued and relatively
smoothed sphere retains the exact meridian germ, one transverse whole-belt
intersection, and crossing of the original zero level at every other
source point. Global embedding and transport to the higher cut remain
separate constructions.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_first_positive_two_handle_windows
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hlower : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      2 ≤ nativeMorseIndex (Vector 7) P.function p)
    (q₀ : criticalPoints (Vector 7) P.function) (hq₀ : 0 < P.function q₀)
    (hi₀ : nativeMorseIndex (Vector 7) P.function q₀ = 2) :
    ∃ (A : AdaptedSurgeryWindows (Vector 7) P.function)
      (q : criticalPoints (Vector 7) P.function),
      nativeMorseIndex (Vector 7) P.function q = 2 ∧
      0 < A.toSurgeryWindows.lower q ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        P.function q ≤ P.function p := by
  obtain ⟨q, hq, hi, hfirst⟩ :=
    P.exists_first_positive_of_index_lower_bound horder hlower q₀ hq₀ hi₀
  obtain ⟨A₀⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨A, _, _, _, _, hlow⟩ := A₀.exists_same_flow_windows_avoiding_level P.smooth P.morse
    (RegularTimeMorse.regular_zero_not_critical P.regular)
  exact ⟨A, q, hi, hlow q hq, hfirst⟩

variable [SimplyConnectedSpace B]

theorem exists_smooth_transverse_first_meridian
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (q : criticalPoints (Vector 7) P.function)
    (hi : nativeMorseIndex (Vector 7) P.function q = 2)
    [Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 4 + 1)]
    (hfirst : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function q ≤ P.function p)
    (hlower : 0 ≤ A.toSurgeryWindows.lower q)
    (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) (hs0 : 0 < (s : ℝ)) :
    let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
    ∃ (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (A.data q).chart.NegativeCoordinates)
      (γ : C(Hemisphere.Sphere 2, (A.data q).UpperLevel)),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ ∧
      (∀ x ∈ BeltMeridianSphere.fixedPoleCap,
        γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) ∧
      (∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
        γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w) ∧
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ BeltMeridianSphere.pole) ∧
      Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ
        BeltMeridianSphere.pole).coprod
          (mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (A.data q).surgery.beltSphere v)) ∧
      (∀ x, Tendsto (fun t => A.flow t (γ x).val) atTop (𝓝 q.val) ↔
        x = BeltMeridianSphere.pole) ∧
      ∀ x, (γ x).val ∈ FlowCancellation.levelBasin A.flow P.function 0 ↔
        x ≠ BeltMeridianSphere.pole := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  obtain ⟨L, γ, hγ, hformula, hcount⟩ :=
    P.exists_smooth_two_sphere_at_first_positive_handle A q hi hfirst hlower v s hs hs0
  have hgerm : (γ : Hemisphere.Sphere 2 → (A.data q).UpperLevel) =ᶠ[
      𝓝 BeltMeridianSphere.pole]
      (fun x => nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) := by
    filter_upwards [BeltMeridianSphere.fixedPoleCap_mem_nhds] with x hx
    exact hformula x hx
  obtain ⟨himm, htrans⟩ :=
    BeltMeridianSphere.retained_meridian_germ_transverse A P.smooth q 4 L v s hs hs0 γ hgerm
  have hmem (x : Hemisphere.Sphere 2) :
      γ x ∈ range (A.data q).surgery.beltSphere ↔ x = BeltMeridianSphere.pole := by
    constructor
    · rintro ⟨w, hw⟩
      exact ((hcount x w).mp hw.symm).1
    · intro hx
      exact ⟨v, ((hcount x v).mpr ⟨hx, rfl⟩).symm⟩
  refine ⟨L, γ, hγ, hformula, hcount, himm, htrans,
    fun x => (A.belt_basin_iff P.smooth q (γ x)).trans (hmem x), ?_⟩
  intro x
  exact (A.first_above_cut_upper_point_crosses_iff P.smooth
    (RegularTimeMorse.regular_zero_not_critical P.regular) q
      (hlower.trans_lt (A.toSurgeryWindows.lower_lt_value q)) hfirst (γ x)).trans
        (not_congr (hmem x))

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
