import Wikipedia.SmoothSixDPoincare.HomotopyTimeFlattening
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Smooth homotopies with fixed endpoint collars

A continuous homotopy between smooth maps is first flattened in time.
Relative smoothing preserves closed endpoint collars, giving a genuinely
smooth cylinder map that is stationary near both ends.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [J.Boundaryless] [IsManifold I ∞ X] [T2Space X]
  [CompactSpace X] [IsManifold J ∞ N] in
/-- A flattened homotopy between smooth maps is smooth on an open endpoint neighborhood. -/
theorem contMDiffOn_flattenedHomotopyMap {f g : C(X, N)}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) (H : f.Homotopy g) :
    ContMDiffOn ((𝓡∂ 1).prod I) J ∞ (flattenedHomotopyMap H)
      (homotopyCollarNeighborhood X) := by
  rintro q (hl | hu)
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => f r.2) :=
      hf.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => f r.2) := by
      have hn : {r : unitInterval × X | (r.1 : ℝ) < 1 / 3} ∈ 𝓝 q :=
        (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds hl
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_lower H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have hs : ContMDiff ((𝓡∂ 1).prod I) J ∞ (fun r : unitInterval × X => g r.2) :=
      hg.comp contMDiff_snd
    have heq : flattenedHomotopyMap H =ᶠ[𝓝 q] (fun r => g r.2) := by
      have hn : {r : unitInterval × X | 2 / 3 < (r.1 : ℝ)} ∈ 𝓝 q :=
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds hu
      filter_upwards [hn] with r hr
      exact flattenedHomotopyMap_upper H r.1 r.2 (le_of_lt hr)
    exact (hs.contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt

/-- Construct a smooth cylinder homotopy, stationary on actual endpoint collars. -/
theorem exists_smooth_homotopy_with_collars {f g : C(X, N)}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) (H : f.Homotopy g) :
    ∃ H' : f.Homotopy g, ContMDiff ((𝓡∂ 1).prod I) J ∞ H' ∧
      (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H' (t, x) = f x) ∧
      (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H' (t, x) = g x) := by
  obtain ⟨F, hF, ⟨K⟩⟩ := exists_smooth_map_homotopicRel (flattenedHomotopyMap H)
    isClosed_homotopyCollars isOpen_homotopyCollarNeighborhood homotopyCollars_subset
    (contMDiffOn_flattenedHomotopyMap hf hg H)
  have hlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : F (t, x) = f x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inl ht)
    rw [← heq]
    exact flattenedHomotopyMap_lower H t x (by linarith)
  have hhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : F (t, x) = g x := by
    have heq := K.fst_eq_snd (show (t, x) ∈ homotopyCollars X from Or.inr ht)
    rw [← heq]
    exact flattenedHomotopyMap_upper H t x (by linarith)
  let H' : f.Homotopy g := {
    toContinuousMap := F
    map_zero_left := fun x => hlo 0 x (by norm_num)
    map_one_left := fun x => hhi 1 x (by norm_num) }
  exact ⟨H', hF, hlo, hhi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing
