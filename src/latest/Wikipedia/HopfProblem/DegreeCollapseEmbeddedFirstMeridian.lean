import Wikipedia.HopfProblem.DegreeCollapseMeridianProtectedCap
import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereEmbedding
import Wikipedia.HopfProblem.DegreeCollapseSmoothFirstMeridian
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelRetraction

/-!
# An actual embedded transverse meridian at the first positive two-handle

Relative affine perturbation embeds the whole sphere while fixing an
actual pole neighborhood. On the compact region where it can move the
sphere, its entire homotopy avoids the full belt image. The original
native meridian germ, transverse intersection, forward endpoint, and
crossing of the original zero level are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

theorem exists_embedded_preserving_belt
    {n : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Vector n) N]
    [IsManifold (𝓡 n) ∞ N] [T2Space N] [CompactSpace N]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (e : EuclideanEmbedding n N) (r : TubularRetraction e) (hdim : 5 < n)
    (f : C(Hemisphere.Sphere 2, N)) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hinj : InjOn f {x | poleCutoff x = 0})
    (hderiv : ∀ x, poleCutoff x = 0 → Injective (mfderiv (𝓡 2) (𝓡 n) f x))
    (β : C(Y, N)) (honly : ∀ x y, f x = β y → x = pole) :
    ∃ g : C(Hemisphere.Sphere 2, N), ContMDiff (𝓡 2) (𝓡 n) ∞ g ∧
      IsClosedEmbedding g ∧ (∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) g x)) ∧
      f.HomotopicRel g {x | poleCutoff x = 0} ∧ ∀ x y, g x = β y ↔ f x = β y := by
  let U : Set N := (range β)ᶜ
  have hU : IsOpen U := (isCompact_range β.continuous).isClosed.isOpen_compl
  have hfU : MapsTo f awayPoleCap U := by
    rintro x hx ⟨y, hy⟩
    exact pole_not_mem_awayPoleCap ((honly x y hy.symm) ▸ hx)
  obtain ⟨g, hg, hgi, hgd, H, hHU⟩ :=
    RelativeTwoSphere.exists_relative_embedding_in_open_on_compact e r hdim f hf
      poleCutoff poleCutoff_smooth poleCutoff_nonneg poleCutoff_norm_le_one hinj hderiv
      awayPoleCap awayPoleCap_compact U hU hfU
  have hrel : f.HomotopicRel g {x | poleCutoff x = 0} := ⟨H⟩
  have hgU : MapsTo g awayPoleCap U := by
    intro x hx
    exact (H.map_one_left x) ▸ hHU 1 x hx
  refine ⟨g, hg, hgi, hgd, hrel, ?_⟩
  intro x y
  by_cases hx : x ∈ awayPoleCap
  · constructor
    · intro hxy
      exact (hgU hx ⟨y, hxy.symm⟩).elim
    · intro hxy
      exact (hfU hx ⟨y, hxy.symm⟩).elim
  · rw [← hrel.fst_eq_snd (poleCutoff_zero_outside x hx)]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_embedded_transverse_first_meridian
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
      IsClosedEmbedding γ ∧
      (∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ x)) ∧
      (∀ x, BeltMeridianSphere.poleCutoff x = 0 →
        γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) ∧
      (∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
        γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w) ∧
      Surjective ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) γ
        BeltMeridianSphere.pole).coprod
          (mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (A.data q).surgery.beltSphere v)) ∧
      (∀ x, Tendsto (fun t => A.flow t (γ x).val) atTop (𝓝 q.val) ↔
        x = BeltMeridianSphere.pole) ∧
      ∀ x, (γ x).val ∈ FlowCancellation.levelBasin A.flow P.function 0 ↔
        x ≠ BeltMeridianSphere.pole := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  let _ := RegularLevel.isManifold P.smooth (A.data q).upper_regular
  let : CompactSpace (A.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq P.function.continuous continuous_const).isCompact
  obtain ⟨L, f, hf, hformula, hcount⟩ :=
    P.exists_smooth_two_sphere_at_first_positive_handle A q hi hfirst hlower v s hs hs0
  let e := P.nativeLevelEmbedding (A.data q).upper_regular
  obtain ⟨r⟩ := P.nonempty_nativeLevelRetraction A (A.data q).upper_regular
    (f BeltMeridianSphere.pole)
  obtain ⟨γ, hγ, hγi, hγd, hrel, heq⟩ := BeltMeridianSphere.exists_embedded_preserving_belt
    e r (by simp) f hf
    (BeltMeridianSphere.retained_meridian_injective_on_protected_cap A q L v s hs hs0 f hformula)
    (BeltMeridianSphere.retained_meridian_immersive_on_protected_cap A P.smooth q L v s hs hs0
      f hformula)
    (A.data q).surgery.beltSphere (fun x w h => ((hcount x w).mp h).1)
  have hretained (x : Hemisphere.Sphere 2) (hx : BeltMeridianSphere.poleCutoff x = 0) :
      γ x = nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x)) := by
    have hfixed : x ∈ BeltMeridianSphere.fixedPoleCap := by
      have hh := (BeltMeridianSphere.poleCutoff_zero_iff x).mp hx
      change x.val 0 ≤ -(1 / 2 : ℝ)
      linarith
    exact (hrel.fst_eq_snd hx).symm.trans (hformula x hfixed)
  have hgerm : (γ : Hemisphere.Sphere 2 → (A.data q).UpperLevel) =ᶠ[
      𝓝 BeltMeridianSphere.pole]
      (fun x => nativeBeltMeridianDisk A q v s hs (L (Hemisphere.tail x))) := by
    filter_upwards [BeltMeridianSphere.poleCutoff_zero_mem_nhds] with x hx
    exact hretained x hx
  have hγcount (x : Hemisphere.Sphere 2)
      (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1) :
      γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w :=
    (heq x w).trans (hcount x w)
  have hmem (x : Hemisphere.Sphere 2) :
      γ x ∈ range (A.data q).surgery.beltSphere ↔ x = BeltMeridianSphere.pole := by
    constructor
    · rintro ⟨w, hw⟩
      exact ((hγcount x w).mp hw.symm).1
    · intro hx
      exact ⟨v, ((hγcount x v).mpr ⟨hx, rfl⟩).symm⟩
  have htrans := (BeltMeridianSphere.retained_meridian_germ_transverse A P.smooth q 4
    L v s hs hs0 γ hgerm).2
  refine ⟨L, γ, hγ, hγi, hγd, hretained, hγcount, htrans,
    fun x => (A.belt_basin_iff P.smooth q (γ x)).trans (hmem x), ?_⟩
  intro x
  exact (A.first_above_cut_upper_point_crosses_iff P.smooth
    (RegularTimeMorse.regular_zero_not_critical P.regular) q
      (hlower.trans_lt (A.toSurgeryWindows.lower_lt_value q)) hfirst (γ x)).trans
        (not_congr (hmem x))

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
