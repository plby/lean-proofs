import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerDeterminant
import Wikipedia.HopfProblem.DegreeCollapsePatchSheetDifferential
import Wikipedia.HopfProblem.DegreeCollapseStripSourceOrientation

/-!
# The actual native determinant identity at either immersed bigon corner

Apply the exact comparison square to the two original immersion derivatives.
The actual tubular chart is based at the same point for both branches.
The retained source-coordinate factors and forward tubular determinant
give the precise factorization of the original ordered crossing determinant.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource

variable {G E M N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)

def sourceFrame
    (Φ : PartialDiffeomorph 𝓘(ℝ, Sheet × EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, E)
      (Sheet × EuclideanSpace ℝ (Fin 3)) M ∞) (F : N → M) (x : N) : G →L[ℝ] G :=
  NativeMapOrientation.nativeFrame (I := 𝓘(ℝ, G)) (patchSourceCoordinates Φ F) J x

def forwardTubeFrame
    (Ψ : PartialDiffeomorph 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) NormalSpace M ∞)
    (p : NormalSpace) : E →L[ℝ] E :=
  (mfderiv 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) Ψ p).comp (tubeCoordinates J K).toContinuousLinearMap

/-- The upper branch is first, consistently with the tubular bigon Jacobian. -/
def originalJointFrame (F : N → M) (x y : N) : (G × G) →L[ℝ] (G × G) :=
  K.symm.toContinuousLinearMap.comp
    ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y).coprod (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))

theorem actual_corner_determinant_factor
    {F : N → M} {U V : Set N} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := E) (F '' U) (F '' V) a b k l h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' U) k)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' V) l)
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x y : N} (hU : U ∈ 𝓝 x) (hV : V ∈ 𝓝 y)
    (hx : F x = a t) (hy : F y = b t) :
    tube.sheetPairDet d e t * (forwardTubeFrame J K tube.chart ((2 * t - 1, 0), 0)).det *
        coordinateScale J K * (sourceFrame J e.chart F y).det * (sourceFrame J d.chart F x).det =
      (originalJointFrame K F x y).det := by
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
  have hyx : F y = F x := by
    calc
      F y = tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) :=
        hy.trans (tube.upper t htI).symm
      _ = tube.map (2 * t - 1, 0) := by rw [hheight]
      _ = F x := (tube.lower t htI).trans hx.symm
  have hxk : F x = k (t, 0) := by
    have heq := (tube.lower_germ t htI).eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [lowerStripCoordinates_lower] at heq
    exact hx.trans ((tube.lower t htI).symm.trans heq)
  have hyl : F y = l (t, 0) := by
    have heq := (tube.upper_germ t htI).eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [upperStripCoordinates_upper] at heq
    exact hy.trans ((tube.upper t htI).symm.trans heq)
  have hxT : F x ∈ tube.chart.target := hpF ▸ tube.chart.map_source' hp
  have hyT : F y ∈ tube.chart.target := hyx.symm ▸ hxT
  have hxinv : tube.chart.symm (F x) = ((2 * t - 1, 0), 0) := by
    rw [← hpF]
    exact tube.chart.left_inv' hp
  have hyinv : tube.chart.symm (F y) = ((2 * t - 1, 0), 0) := by rw [hyx, hxinv]
  have hfirst := original_derivative_eq_forward_sheetDifferential d tube.chart hF htI hU hxk hxT
  have hsecond := original_derivative_eq_forward_sheetDifferential e tube.chart hF htI hV hyl hyT
  rw [hxinv] at hfirst
  rw [hyinv] at hsecond
  exact det_original_sheet_comparison J K
    (mfderiv 𝓘(ℝ, NormalSpace) 𝓘(ℝ, E) tube.chart ((2 * t - 1, 0), 0))
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
    (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, Sheet) (patchSourceCoordinates e.chart F) y)
    (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, Sheet) (patchSourceCoordinates d.chart F) x)
    (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y) (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x)
    hsecond.symm hfirst.symm

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
