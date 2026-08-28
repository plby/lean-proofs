import Wikipedia.SmoothSixDPoincare.ImageComplementNullhomotopy
import Wikipedia.HopfProblem.OrbitPairCircleNullhomotopy
import Wikipedia.HopfProblem.SphereHomologyCircleGeometry
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Connectivity of actual high-codimension image complements

The zero-dimensional instance of the proved homotopy-avoidance theorem
moves paths into the actual complement. Circle nullhomotopies are converted
to based loop nullhomotopies using the literal circle homeomorphism, so
the simple-connectivity conclusion concerns the original topology.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open Wikipedia.SmoothSixDPoincare
open TrianglePeriodFamily.BoundaryLoopSquares

/-- Unbased nullhomotopies of all round-circle maps imply the based loop condition. -/
theorem simplyConnected_of_roundCircle_nullhomotopies {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X]
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    SimplyConnectedSpace X := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x p
  let e : LoopCircle ≃ₜ Hemisphere.Sphere 1 :=
    (AddCircle.homeomorphCircle (by norm_num)).trans SphereHomology.sphereCircleHomeomorph.symm
  let a : C(LoopCircle, Hemisphere.Sphere 1) := ⟨e, e.continuous⟩
  let b : C(Hemisphere.Sphere 1, LoopCircle) := ⟨e.symm, e.symm.continuous⟩
  obtain ⟨c, hc⟩ := hnull ((loopOnCircle p).comp b)
  have hh := hc.comp (Homotopic.refl a)
  have he : ((loopOnCircle p).comp b).comp a = loopOnCircle p := by
    apply ContinuousMap.ext
    intro z
    exact congrArg (loopOnCircle p) (e.symm_apply_apply z)
  rw [he] at hh
  exact path_nullhomotopic_of_loopOnCircle_nullhomotopic p hh

namespace ImageComplementConnectivity

variable {E G H K Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
  (g : C(Y, N))

/-- Path avoidance gives path connectedness of the original nonempty image complement. -/
theorem pathConnected [PathConnectedSpace N] [Nonempty (ImageComplement.domain g)]
    (hg : ContMDiff I J ∞ g) (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G) :
    PathConnectedSpace (ImageComplement.domain g) := by
  refine { nonempty := inferInstance, joined := ?_ }
  intro a b
  let Z := EuclideanSpace ℝ (Fin 0)
  let f₀ : C(Z, ImageComplement.domain g) := ContinuousMap.const Z a
  let f₁ : C(Z, ImageComplement.domain g) := ContinuousMap.const Z b
  have ha : ((ImageComplement.inclusion g).comp f₀).Homotopic
      ((ImageComplement.inclusion g).comp f₁) :=
    ⟨(PathConnectedSpace.somePath a.val b.val).toHomotopyConst⟩
  have hd : Module.finrank ℝ Z + 1 + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [Z, finrank_euclideanSpace_fin, zero_add] using hdim
  obtain ⟨H⟩ := ImageComplement.homotopic_of_ambient_homotopic
    (I := 𝓡 0) g hg hd f₀ f₁ ha
  exact ⟨{
    toFun := fun t => H (t, 0)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := H.map_zero_left 0
    target' := H.map_one_left 0 }⟩

/-- Removing a compact smooth image of codimension at least three preserves simple connectivity. -/
theorem simplyConnected [PathConnectedSpace N] [Nonempty (ImageComplement.domain g)]
    (hg : ContMDiff I J ∞ g) (hdim : 2 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, N), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    SimplyConnectedSpace (ImageComplement.domain g) := by
  let := pathConnected g hg (by omega)
  exact simplyConnected_of_roundCircle_nullhomotopies
    (ImageComplement.circle_nullhomotopies g hg hdim hnull)

end ImageComplementConnectivity

end Wikipedia.HopfProblem.OrbitPair
