import Wikipedia.SmoothSixDPoincare.FinitePointPathAvoidance
import Wikipedia.SmoothSixDPoincare.OpenObstacleRestriction

/-!
# Paths avoiding an entire closed smooth image inside an open manifold

Relative smooth general position fixes both endpoints. The obstacle source
may be noncompact and countable; only its full image must be closed. Native
open-submanifold restriction retains the entire path in the prescribed open
set, without replacing the original obstacle by a compact subset.
-/

noncomputable section

open Set Function ContinuousMap TopologicalSpace
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E G H H' N Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem exists_smooth_path_avoiding_closed_image {x y : N} (γ : Path x y)
    (g : C(Y, N)) (hg : ContMDiff I J ∞ g) (hclosed : IsClosed (range g))
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hx : x ∉ range g) (hy : y ∉ range g) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, η t ∉ range g := by
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_connecting_curve (J := J) γ
  let fI : C(unitInterval, N) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
  have hfI : ContMDiff (𝓡∂ 1) J ∞ fI := hf.comp contMDiff_subtypeVal_Icc
  have hdim' : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) + Module.finrank ℝ E <
      Module.finrank ℝ G := by simpa only [finrank_euclideanSpace_fin] using hdim
  have hfixed : ∀ t ∈ ({0, 1} : Set unitInterval), fI t ∉ range g := by
    intro t ht
    rcases ht with rfl | ht
    · change f 0 ∉ range g
      rwa [hf0]
    · have ht1 : t = 1 := ht
      subst t
      change f 1 ∉ range g
      rwa [hf1]
  obtain ⟨f', hf', hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel_of_isClosed_range fI g hfI hg
      hclosed hdim' ((finite_singleton (1 : unitInterval)).insert 0).isClosed hfixed
  have h0 : f' 0 = x := (hrel.fst_eq_snd (by simp)).symm.trans hf0
  have h1 : f' 1 = y := (hrel.fst_eq_snd (by simp)).symm.trans hf1
  let η : Path x y := { toContinuousMap := f', source' := h0, target' := h1 }
  exact ⟨η, hf', fun t ht => Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ht⟩

theorem exists_smooth_path_avoiding_closed_image_in_open
    (U : Opens N) {x y : U} (γ : Path x y)
    (g : C(Y, N)) (hg : ContMDiff I J ∞ g) (hclosed : IsClosed (range g))
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hx : x.val ∉ range g) (hy : y.val ∉ range g) :
    ∃ η : Path x y, ContMDiff (𝓡∂ 1) J ∞ η ∧ ∀ t, (η t).val ∉ range g := by
  obtain ⟨η, hη, havoid⟩ := exists_smooth_path_avoiding_closed_image γ
    (OpenObstacle.restrict g U) (OpenObstacle.contMDiff_restrict g U hg)
    (OpenObstacle.isClosed_range_restrict g U hclosed) hdim
    (fun h => hx ((OpenObstacle.mem_range_restrict_iff g U x).mp h))
    (fun h => hy ((OpenObstacle.mem_range_restrict_iff g U y).mp h))
  exact ⟨η, hη, fun t ht => havoid t
    ((OpenObstacle.mem_range_restrict_iff g U (η t)).mpr ht)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
