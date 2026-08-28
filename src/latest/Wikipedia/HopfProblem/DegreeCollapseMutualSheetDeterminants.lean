import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerOrientation

/-!
# Native determinant comparison for two different sheets

The two source maps and their source manifolds remain independent. The
actual original tangent sum factors through the retained strip source
coordinates and the forward tubular chart, with the same fixed coordinate
factor at both corners. No branch exchange changes the ordered sheets.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource ImmersedCorner

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace D P]
  (J : Sheet ≃L[ℝ] D) (K : (D × D) ≃L[ℝ] E)

def jointFrame (F : N → M) (G : P → M) (x : N) (y : P) :
    (D × D) →L[ℝ] (D × D) :=
  K.symm.toContinuousLinearMap.comp
    ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y).coprod (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))

theorem jointFrame_det_ne_zero {F : N → M} {G : P → M} {x : N} {y : P}
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y).coprod
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))) : (jointFrame K F G x y).det ≠ 0 := by
  have hs : Surjective (jointFrame K F G x y) := K.symm.surjective.comp ht
  have hi : Injective (jointFrame K F G x y) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hs
  exact fun hz => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hi)

theorem full_range_derivative_factor {F : N → M} {k : (ℝ × ℝ) → M}
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) NormalSpace M ∞)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : N}
    (hx : F x = k (t, 0)) (hT : F x ∈ Ψ.target) :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x =
      (mfderiv 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) Ψ (Ψ.symm (F x))).comp
        ((d.sheetDifferential Ψ t).comp
          (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, Sheet) (patchSourceCoordinates d.chart F) x)) := by
  let d' : StripNormalData Plane (EuclideanSpace ℝ (Fin 3))
      (E := E) (F '' (univ : Set N)) k := {
    d with sheet := by simpa only [image_univ] using d.sheet }
  exact original_derivative_eq_forward_sheetDifferential d' Ψ hF ht Filter.univ_mem hx hT

theorem actual_corner_determinant_factor
    {F : N → M} {G : P → M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := E) (range F) (range G) a b k l h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) l)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x : N} {y : P}
    (hx : F x = a t) (hy : G y = b t) :
    tube.sheetPairDet d e t * (forwardTubeFrame J K tube.chart ((2 * t - 1, 0), 0)).det *
        coordinateScale J K * (sourceFrame J e.chart G y).det *
        (sourceFrame J d.chart F x).det = (jointFrame K F G x y).det := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hpB : (2 * t - 1, 0) ∈ bigon h := by
    have hfront := (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, htI, Or.inl rfl⟩
    exact ((mem_frontier_bigon_iff h _).mp hfront).1
  have hp : ((2 * t - 1, 0), (0 : EuclideanSpace ℝ (Fin 4))) ∈ tube.chart.source :=
    tube.source_contains ⟨hpB, Metric.mem_closedBall_self tube.radius_pos.le⟩
  have hpF : tube.chart ((2 * t - 1, 0), 0) = F x :=
    (tube.zero_section _).trans ((tube.lower t htI).trans hx.symm)
  have hyx : G y = F x := by
    calc
      G y = tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) :=
        hy.trans (tube.upper t htI).symm
      _ = tube.map (2 * t - 1, 0) := by rw [hheight]
      _ = F x := (tube.lower t htI).trans hx.symm
  have hxk : F x = k (t, 0) := by
    have heq := (tube.lower_germ t htI).eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [lowerStripCoordinates_lower] at heq
    exact hx.trans ((tube.lower t htI).symm.trans heq)
  have hyl : G y = l (t, 0) := by
    have heq := (tube.upper_germ t htI).eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [upperStripCoordinates_upper] at heq
    exact hy.trans ((tube.upper t htI).symm.trans heq)
  have hxT : F x ∈ tube.chart.target := hpF ▸ tube.chart.map_source' hp
  have hyT : G y ∈ tube.chart.target := hyx.symm ▸ hxT
  have hxinv : tube.chart.symm (F x) = ((2 * t - 1, 0), 0) := by
    rw [← hpF]
    exact tube.chart.left_inv' hp
  have hyinv : tube.chart.symm (G y) = ((2 * t - 1, 0), 0) := by rw [hyx, hxinv]
  have hfirst := full_range_derivative_factor d tube.chart hF htI hxk hxT
  have hsecond := full_range_derivative_factor e tube.chart hG htI hyl hyT
  rw [hxinv] at hfirst
  rw [hyinv] at hsecond
  exact det_original_sheet_comparison J K
    (mfderiv 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) tube.chart ((2 * t - 1, 0), 0))
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
    (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, Sheet) (patchSourceCoordinates e.chart G) y)
    (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, Sheet) (patchSourceCoordinates d.chart F) x)
    (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y) (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x)
    hsecond.symm hfirst.symm

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
