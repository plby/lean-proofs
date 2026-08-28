import Wikipedia.HopfProblem.DegreeCollapseMiddleSphereGerms
import Wikipedia.HopfProblem.DegreeCollapseRelativeAvoidingSmoothing

/-!
# Relative smoothing that preserves every opposite sphere coincidence

Keep a fixed closed neighborhood of the negative pole. Outside a smaller
open neighborhood, smooth in the complement of the entire finite opposite
family. Thus every original coincidence is preserved, and no new one is
introduced. The original maps remain homotopic relative to the closed cap.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

def fixedPoleCap : Set (Hemisphere.Sphere 3) := {x | x.val 0 ≤ -(1 / 2 : ℝ)}

def innerPoleCap : Set (Hemisphere.Sphere 3) := {x | x.val 0 < -(3 / 4 : ℝ)}

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

theorem middlePole_mem_inner : middlePole ∈ innerPoleCap := by
  change -Hemisphere.radius (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 3) <
    -(3 / 4 : ℝ)
  norm_num [Hemisphere.radius]

theorem fixedPoleCap_mem_nhds : fixedPoleCap ∈ 𝓝 middlePole :=
  mem_of_superset (innerPoleCap_open.mem_nhds middlePole_mem_inner) innerPoleCap_subset_fixed

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem exists_smooth_preserving_opposite_family {ι : Type*} [Finite ι]
    (f : C(Hemisphere.Sphere 3, M))
    (hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ f negativeHemisphere)
    (g : ι → C(Hemisphere.Sphere 3, M))
    (honly : ∀ i x y, f x = g i y → x = middlePole) :
    ∃ f' : C(Hemisphere.Sphere 3, M), ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ f' ∧
      f.HomotopicRel f' fixedPoleCap ∧
      ∀ i x y, f' x = g i y ↔ f x = g i y := by
  let V : Set M := (⋃ i, range (g i))ᶜ
  have hV : IsOpen V :=
    (isClosed_iUnion_of_finite (fun i => (isCompact_range (g i).continuous).isClosed)).isOpen_compl
  have hfV : MapsTo f innerPoleCapᶜ V := by
    intro x hx hbad
    obtain ⟨i, y, hy⟩ := mem_iUnion.mp hbad
    have he := honly i x y hy.symm
    exact hx (he ▸ middlePole_mem_inner)
  have hfK : ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ f (innerPoleCapᶜ)ᶜ := by
    rw [compl_compl]
    exact hf.mono (innerPoleCap_subset_fixed.trans fixedPoleCap_subset_negative)
  obtain ⟨f', hs, hhom, hav⟩ := RelativeAvoidingSmoothing.exists_smooth_avoiding_on_compact
    (I := 𝓡 3) (J := 𝓘(ℝ, E)) f innerPoleCap_open.isClosed_compl.isCompact
      fixedPoleCap_closed negativeHemisphere_open fixedPoleCap_subset_negative hf hfK hV hfV
  refine ⟨f', hs, hhom, ?_⟩
  intro i x y
  constructor
  · intro hxy
    by_cases hx : x ∈ innerPoleCap
    · exact (hhom.fst_eq_snd (innerPoleCap_subset_fixed hx)).trans hxy
    · exact (hav hx (mem_iUnion.mpr ⟨i, ⟨y, hxy.symm⟩⟩)).elim
  · intro hxy
    have hx := honly i x y hxy
    have hfixed : x ∈ fixedPoleCap := hx ▸ innerPoleCap_subset_fixed middlePole_mem_inner
    exact (hhom.fst_eq_snd hfixed).symm.trans hxy

theorem exists_smooth_opposite_families {ι κ : Type*} [Finite ι] [Finite κ]
    (f : ι → C(Hemisphere.Sphere 3, M)) (g : κ → C(Hemisphere.Sphere 3, M))
    (hf : ∀ i, ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ (f i) negativeHemisphere)
    (hg : ∀ j, ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ (g j) negativeHemisphere)
    (honly : ∀ i j x y, f i x = g j y → x = middlePole ∧ y = middlePole) :
    ∃ (f' : ι → C(Hemisphere.Sphere 3, M)) (g' : κ → C(Hemisphere.Sphere 3, M)),
      (∀ i, ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ (f' i)) ∧
      (∀ j, ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ (g' j)) ∧
      (∀ i, (f i).HomotopicRel (f' i) fixedPoleCap) ∧
      (∀ j, (g j).HomotopicRel (g' j) fixedPoleCap) ∧
      ∀ i j x y, f' i x = g' j y ↔ f i x = g j y := by
  classical
  have hfirst (i : ι) := exists_smooth_preserving_opposite_family (f i) (hf i) g
    (fun j x y h => (honly i j x y h).1)
  choose f' hf' hrelf heqf using hfirst
  have hsecond (j : κ) := exists_smooth_preserving_opposite_family (g j) (hg j) f'
    (fun i y x h => (honly i j x y ((heqf i j x y).mp h.symm)).2)
  choose g' hg' hrelg heqg using hsecond
  refine ⟨f', g', hf', hg', hrelf, hrelg, ?_⟩
  intro i j x y
  exact eq_comm.trans ((heqg j i y x).trans (eq_comm.trans (heqf i j x y)))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
