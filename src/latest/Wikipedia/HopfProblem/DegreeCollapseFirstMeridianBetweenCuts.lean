import Wikipedia.HopfProblem.DegreeCollapseTwoSphereHigherCutAvoidance
import Wikipedia.HopfProblem.DegreeCollapseMeridianEmbeddingInOpen
import Wikipedia.HopfProblem.DegreeCollapseMeridianDiskNeighborhood
import Wikipedia.HopfProblem.DegreeCollapsePositiveBeltPointCrossing

/-!
# An actual embedded transverse first meridian whose whole sphere reaches the higher cut

Choose a belt point with an actual higher-level crossing and shrink the
whole native meridian disk into that open crossing basin. The original
boundary constructs the cap. Relative avoidance removes all low backward
endpoints, and relative embedding retains the entire crossing condition.
The original pole germ, full belt relation, and forward endpoints remain.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_embedded_transverse_first_meridian_between_cuts
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (q : criticalPoints (Vector 7) P.function)
    (hi : nativeMorseIndex (Vector 7) P.function q = 2)
    [Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 4 + 1)]
    (hfirst : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function q ≤ P.function p)
    (hlower : 0 ≤ A.toSurgeryWindows.lower q)
    {a : ℝ} (hupper : A.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function p ≤ a → nativeMorseIndex (Vector 7) P.function p ≤ 3) :
    let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
    ∃ (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
      (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 2), 0 < (s : ℝ) ∧
      ∃ (L : Hemisphere.Ambient 2 ≃ₗᵢ[ℝ] (A.data q).chart.NegativeCoordinates)
        (γ : C(Hemisphere.Sphere 2, (A.data q).UpperLevel)),
        ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ γ ∧
        IsClosedEmbedding γ ∧
        (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ x)) ∧
        (∀ x, BeltMeridianSphere.poleCutoff x = 0 →
          γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) ∧
        (∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
          γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w) ∧
        Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ
          BeltMeridianSphere.pole).coprod
            (mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (A.data q).surgery.beltSphere v)) ∧
        (∀ x, (γ x).val ∈ FlowCancellation.levelBasin A.flow P.function a) ∧
        (∀ x, Tendsto (fun t => A.flow t (γ x).val) atTop (𝓝 q.val) ↔
          x = BeltMeridianSphere.pole) ∧
        ∀ x, (γ x).val ∈ FlowCancellation.levelBasin A.flow P.function 0 ↔
          x ≠ BeltMeridianSphere.pole := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  let _ := RegularLevel.isManifold P.smooth (A.data q).upper_regular
  let : CompactSpace (A.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq P.function.continuous continuous_const).isCompact
  have hq : 0 < P.function q := hlower.trans_lt (A.toSurgeryWindows.lower_lt_value q)
  have hqa : P.function q < a := (A.toSurgeryWindows.value_lt_upper q).trans_le hupper
  obtain ⟨v, hv⟩ := A.exists_belt_point_reaching_level_above_cut P.smooth q 4 hq hqa
    hlow (by norm_num)
  have hO : IsOpen (FlowCancellation.levelBasin A.flow P.function a) :=
    (FlowCancellation.smooth_signed_level_time P.smooth A.smooth A.flow A.integral
      (fun y hy => A.descent y (ha y hy))).1
  obtain ⟨s, hs, hs0, hdisk⟩ := exists_native_meridian_disk_in_open A q v hO hv
  obtain ⟨L, f, hf, hformula, hcount⟩ :=
    P.exists_smooth_two_sphere_at_first_positive_handle A q hi hfirst hlower v s hs hs0
  have hfixed (x : Hemisphere.Sphere 2) (hx : x ∈ BeltMeridianSphere.fixedPoleCap) :
      (f x).val ∈ FlowCancellation.levelBasin A.flow P.function a := by
    rw [hformula x hx]
    exact hdisk _
  have hcoincidence (x : Hemisphere.Sphere 2)
      (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
      (hxw : f x = (A.data q).surgery.beltSphere w) : x ∈ BeltMeridianSphere.fixedPoleCap := by
    rw [((hcount x w).mp hxw).1]
    exact BeltMeridianSphere.innerPoleCap_subset_fixed BeltMeridianSphere.pole_mem_inner
  obtain ⟨σ, hσ, hrel₀, hσreach, hσeq⟩ :=
    A.exists_two_sphere_reaching_higher_cut_preserving_belt P.smooth
      (hq.trans (A.toSurgeryWindows.value_lt_upper q)) hupper (A.data q).upper_regular ha
      hlow (by simp [RegularLevel.Model]) f (A.data q).surgery.beltSphere
      BeltMeridianSphere.fixedPoleCap_closed hfixed hcoincidence hf
  have hσformula (x : Hemisphere.Sphere 2) (hx : x ∈ BeltMeridianSphere.fixedPoleCap) :
      σ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x)) :=
    (hrel₀.fst_eq_snd hx).symm.trans (hformula x hx)
  let e := P.nativeLevelEmbedding (A.data q).upper_regular
  obtain ⟨r⟩ := P.nonempty_nativeLevelRetraction A (A.data q).upper_regular
    (σ BeltMeridianSphere.pole)
  obtain ⟨γ, hγ, hγi, hγd, hrel, heq, hγreach⟩ :=
    BeltMeridianSphere.exists_embedded_preserving_belt_in_open e r (by simp) σ hσ
      (BeltMeridianSphere.retained_meridian_injective_on_protected_cap A q L v s hs hs0
        σ hσformula)
      (BeltMeridianSphere.retained_meridian_immersive_on_protected_cap A P.smooth q L v s
        hs hs0 σ hσformula)
      (A.data q).surgery.beltSphere
      (fun x w h => ((hcount x w).mp ((hσeq x w).mp h)).1)
      (hO.preimage continuous_subtype_val) hσreach
  have hretained (x : Hemisphere.Sphere 2) (hx : BeltMeridianSphere.poleCutoff x = 0) :
      γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x)) := by
    have hcap : x ∈ BeltMeridianSphere.fixedPoleCap := by
      have hh := (BeltMeridianSphere.poleCutoff_zero_iff x).mp hx
      change x.val 0 ≤ -(1 / 2 : ℝ)
      linarith
    exact (hrel.fst_eq_snd hx).symm.trans (hσformula x hcap)
  have hgerm : (γ : Hemisphere.Sphere 2 → (A.data q).UpperLevel) =ᶠ[
      𝓝 BeltMeridianSphere.pole]
      (fun x => nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) := by
    filter_upwards [BeltMeridianSphere.poleCutoff_zero_mem_nhds] with x hx
    exact hretained x hx
  have hγcount (x : Hemisphere.Sphere 2)
      (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1) :
      γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w :=
    (heq x w).trans ((hσeq x w).trans (hcount x w))
  have hmem (x : Hemisphere.Sphere 2) :
      γ x ∈ range (A.data q).surgery.beltSphere ↔ x = BeltMeridianSphere.pole := by
    constructor
    · rintro ⟨w, hw⟩
      exact ((hγcount x w).mp hw.symm).1
    · intro hx
      exact ⟨v, ((hγcount x v).mpr ⟨hx, rfl⟩).symm⟩
  have htrans := (BeltMeridianSphere.retained_meridian_germ_transverse A P.smooth q 4
    L v s hs hs0 γ hgerm).2
  refine ⟨v, s, hs, hs0, L, γ, hγ, hγi, hγd, hretained, hγcount, htrans, hγreach,
    fun x => (A.belt_basin_iff P.smooth q (γ x)).trans (hmem x), ?_⟩
  intro x
  exact (A.first_above_cut_upper_point_crosses_iff P.smooth
    (RegularTimeMorse.regular_zero_not_critical P.regular) q hq hfirst (γ x)).trans
      (not_congr (hmem x))

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
