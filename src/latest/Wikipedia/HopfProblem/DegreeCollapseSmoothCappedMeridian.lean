import Wikipedia.HopfProblem.DegreeCollapseFirstPositiveTwoHandle
import Wikipedia.HopfProblem.DegreeCollapseRelativeAvoidingSmoothing

/-!
# Smooth the capped meridian while retaining its entire belt coincidence

The original disk formula is fixed on a closed neighborhood of the pole.
Elsewhere smoothing takes place in the complement of the full compact
belt image. Thus neither the unique coincidence nor its local smooth germ
changes. Global embedding is not asserted here.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

def fixedPoleCap : Set (Hemisphere.Sphere 2) := {x | x.val 0 ≤ -(1 / 2 : ℝ)}

def innerPoleCap : Set (Hemisphere.Sphere 2) := {x | x.val 0 < -(3 / 4 : ℝ)}

theorem fixedPoleCap_closed : IsClosed fixedPoleCap :=
  isClosed_le ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) continuous_const

theorem innerPoleCap_open : IsOpen innerPoleCap :=
  isOpen_lt ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) continuous_const

theorem innerPoleCap_subset_fixed : innerPoleCap ⊆ fixedPoleCap := by
  intro x hx
  change x.val 0 < -(3 / 4 : ℝ) at hx
  change x.val 0 ≤ -(1 / 2 : ℝ)
  linarith

theorem fixedPoleCap_subset_negative : fixedPoleCap ⊆ negativeHemisphere := by
  intro x hx
  change x.val 0 ≤ -(1 / 2 : ℝ) at hx
  change x.val 0 < 0
  linarith

theorem pole_mem_inner : pole ∈ innerPoleCap := by
  change -Hemisphere.radius (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 2) <
    -(3 / 4 : ℝ)
  norm_num [Hemisphere.radius]

theorem fixedPoleCap_mem_nhds : fixedPoleCap ∈ 𝓝 pole :=
  mem_of_superset (innerPoleCap_open.mem_nhds pole_mem_inner) innerPoleCap_subset_fixed

theorem exists_smooth_preserving_belt
    {G N Y : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N]
    [TopologicalSpace Y] [CompactSpace Y]
    (f : C(Hemisphere.Sphere 2, N))
    (hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, G) ∞ f negativeHemisphere)
    (β : C(Y, N)) (honly : ∀ x y, f x = β y → x = pole) :
    ∃ g : C(Hemisphere.Sphere 2, N), ContMDiff (𝓡 2) 𝓘(ℝ, G) ∞ g ∧
      f.HomotopicRel g fixedPoleCap ∧ ∀ x y, g x = β y ↔ f x = β y := by
  let V : Set N := (range β)ᶜ
  have hV : IsOpen V := (isCompact_range β.continuous).isClosed.isOpen_compl
  have hfV : MapsTo f innerPoleCapᶜ V := by
    rintro x hx ⟨y, hy⟩
    exact hx ((honly x y hy.symm) ▸ pole_mem_inner)
  have hfK : ContMDiffOn (𝓡 2) 𝓘(ℝ, G) ∞ f (innerPoleCapᶜ)ᶜ := by
    rw [compl_compl]
    exact hf.mono (innerPoleCap_subset_fixed.trans fixedPoleCap_subset_negative)
  obtain ⟨g, hg, hhom, hav⟩ := RelativeAvoidingSmoothing.exists_smooth_avoiding_on_compact
    (I := 𝓡 2) (J := 𝓘(ℝ, G)) f innerPoleCap_open.isClosed_compl.isCompact
      fixedPoleCap_closed negativeHemisphere_open fixedPoleCap_subset_negative hf hfK hV hfV
  refine ⟨g, hg, hhom, ?_⟩
  intro x y
  constructor
  · intro hxy
    by_cases hx : x ∈ innerPoleCap
    · exact (hhom.fst_eq_snd (innerPoleCap_subset_fixed hx)).trans hxy
    · exact (hav hx ⟨y, hxy.symm⟩).elim
  · intro hxy
    have hfixed : x ∈ fixedPoleCap :=
      (honly x y hxy) ▸ innerPoleCap_subset_fixed pole_mem_inner
    exact (hhom.fst_eq_snd hfixed).symm.trans hxy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.BeltMeridianSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_smooth_two_sphere_at_first_positive_handle
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (q : criticalPoints (Vector 7) P.function)
    (hi : nativeMorseIndex (Vector 7) P.function q = 2)
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
      ∀ x (w : sphere (0 : (A.data q).chart.PositiveCoordinates) 1),
        γ x = (A.data q).surgery.beltSphere w ↔ x = BeltMeridianSphere.pole ∧ v = w := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  let _ := RegularLevel.isManifold P.smooth (A.data q).upper_regular
  obtain ⟨L, f, hformula, hf, hcount⟩ :=
    P.exists_capped_two_sphere_at_first_positive_handle A q hi hfirst hlower v s hs hs0
  obtain ⟨γ, hγ, hhom, heq⟩ := BeltMeridianSphere.exists_smooth_preserving_belt
    f hf (A.data q).surgery.beltSphere (fun x w h => ((hcount x w).mp h).1)
  refine ⟨L, γ, hγ, ?_, fun x w => (heq x w).trans (hcount x w)⟩
  intro x hx
  exact (hhom.fst_eq_snd hx).symm.trans
    (hformula x (BeltMeridianSphere.fixedPoleCap_subset_negative hx).le)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
