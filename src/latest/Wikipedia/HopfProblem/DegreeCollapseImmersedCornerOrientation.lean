import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerNativeFactor

/-!
# Intrinsic crossing signs and coherent tubular orientation factors

Normalize the original ordered tangent determinant by the two source
orientation bits and the ambient orientation bit. The forward tubular
frame has a constant normalized sign along the disk boundary. The actual
corner determinant identity retains the corresponding scalar weights.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

variable {G E M N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, G) N))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)

def intersectionBit (F : N → M) (x y : N) : Bool :=
  Bool.xor (Bool.xor (oN.rawSign y) (oN.rawSign x)) (oM.rawSign (F x))

def intersectionSign (F : N → M) (x y : N) : Bool :=
  action (originalJointFrame K F x y).det (intersectionBit oN oM F x y)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, G) ∞ N] in
theorem originalJointFrame_det_ne_zero {F : N → M} {x y : N}
    (ht : Surjective ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y).coprod
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))) : (originalJointFrame K F x y).det ≠ 0 := by
  have hs : Surjective (originalJointFrame K F x y) := K.symm.surjective.comp ht
  have hi : Injective (originalJointFrame K F x y) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hs
  exact fun hz => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hi)

omit [FiniteDimensional ℝ G] in
theorem weighted_tube_determinants_pos
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := E) S T a b k l h) :
    0 < (weight (oM.rawSign (a 0)) *
        (forwardTubeFrame J K tube.chart ((2 * 0 - 1, 0), 0)).det) *
      (weight (oM.rawSign (a 1)) *
        (forwardTubeFrame J K tube.chart ((2 * 1 - 1, 0), 0)).det) := by
  let p : ℝ → NormalSpace := fun t => ((2 * t - 1, 0), 0)
  have hp : MapsTo p (Icc (0 : ℝ) 1) tube.chart.source := by
    intro t ht
    have hfront := (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr
      ⟨t, ht, Or.inl rfl⟩
    exact tube.source_contains
      ⟨((mem_frontier_bigon_iff h _).mp hfront).1, Metric.mem_closedBall_self tube.radius_pos.le⟩
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : tube.chart (p t) = a t :=
    (tube.zero_section _).trans (tube.lower t ht)
  have hsign := OrbitPair.NativeChartOrientation.sign_eq_on_preconnected oM tube.chart
    (tubeCoordinates J K) (convex_Icc (0 : ℝ) 1).isPreconnected
    (show ContinuousOn p (Icc (0 : ℝ) 1) from (by fun_prop : Continuous p).continuousOn)
    hp (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  have hdet (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (forwardTubeFrame J K tube.chart (p t)).det ≠ 0 :=
    OrbitPair.NativeChartOrientation.nativeFrame_det_ne_zero tube.chart
      (tubeCoordinates J K) (hp ht)
  change action (forwardTubeFrame J K tube.chart (p 0)).det (oM.rawSign (tube.chart (p 0))) =
    action (forwardTubeFrame J K tube.chart (p 1)).det (oM.rawSign (tube.chart (p 1))) at hsign
  rw [hpoint 0 (by simp), hpoint 1 (by simp)] at hsign
  exact (action_eq_iff_product_pos _ _ (hdet 0 (by simp)) (hdet 1 (by simp)) _ _).mp hsign

omit [FiniteDimensional ℝ E] in
theorem weighted_actual_corner_determinant_factor
    {F : N → M} {U V : Set N} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := E) (F '' U) (F '' V) a b k l h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' U) k)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' V) l)
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x y : N} (hU : U ∈ 𝓝 x) (hV : V ∈ 𝓝 y)
    (hx : F x = a t) (hy : F y = b t) :
    tube.sheetPairDet d e t *
        (weight (oM.rawSign (F x)) * (forwardTubeFrame J K tube.chart ((2 * t - 1, 0), 0)).det) *
        (weight (oN.rawSign y) * (sourceFrame J e.chart F y).det) *
        (weight (oN.rawSign x) * (sourceFrame J d.chart F x).det) * coordinateScale J K =
      weight (intersectionBit oN oM F x y) * (originalJointFrame K F x y).det :=
  normalize_source_comparison (oN.rawSign y) (oN.rawSign x) (oM.rawSign (F x))
    (actual_corner_determinant_factor J K tube d e hF ht hU hV hx hy)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
