import Wikipedia.NoExoticSixSphere.StabilizedEmbedding
import Wikipedia.NoExoticSixSphere.GLDeformation
import Wikipedia.NoExoticSixSphere.OrthogonalStabilization

/-!
# The precise general-linear homotopy input needed for normal framing

This reduction uses actual high-codimension embeddings and their concrete
clutching maps. It records the remaining dimension-specific topological input
as a visible hypothesis. The homotopy-group vanishing and the final smooth
classification are not proved or assumed as axioms in this development.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

/-- Vanishing of all five-sphere maps into real general linear spaces of rank at least seven
would supply a genuine smoothly normal-framed Euclidean embedding of every candidate six-sphere. -/
theorem exists_framedEmbedding_of_fiveSphereGLvanishing
    (hGL : ∀ (r : ℕ), 7 ≤ r →
      ∀ f : C(Sphere 5, InvertibleOperators (EuclideanSpace ℝ (Fin r))),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  obtain ⟨e, he⟩ := exists_highCodimensionEmbedding h 7
  let v : Sphere 6 := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  obtain ⟨c, ⟨H⟩⟩ := hGL (e.ambientDimension - 6) he (e.normalSixClutchingMap h v)
  exact ⟨e, e.nonempty_smoothNormalFrame_of_clutchingNullhomotopy h v c H⟩

/-- The remaining normal-framing input can be restricted to genuine orthogonal operators. -/
theorem exists_framedEmbedding_of_fiveSphereOrthogonalVanishing
    (hO : ∀ (r : ℕ), 7 ≤ r →
      ∀ f : C(Sphere 5, GLOrthonormalization.OrthogonalOperators r),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) :=
  exists_framedEmbedding_of_fiveSphereGLvanishing
    (fun r hr ↦ GLOrthonormalization.nullhomotopic_of_orthogonal_nullhomotopic r (hO r hr)) h

/-- The proved rank reduction leaves a single rank-seven nullhomotopy theorem as the framing
input. That dimension-specific input is still a hypothesis, not a proved computation. -/
theorem exists_framedEmbedding_of_rankSevenVanishing
    (h7 : ∀ f : C(Sphere 5, GLOrthonormalization.OrthogonalOperators 7),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) :=
  exists_framedEmbedding_of_fiveSphereOrthogonalVanishing
    (sphereOrthogonalVanishing_of_rank (by decide : 5 < 7) h7) h

/-- Equivalently, the framing input is that every rank-six five-sphere family becomes
nullhomotopic after one genuine orthogonal stabilization. This remains unproved here. -/
theorem exists_framedEmbedding_of_stabilizedRankSixVanishing (v : Sphere 6)
    (h6 : ∀ f : C(Sphere 5, GLOrthonormalization.OrthogonalOperators 6),
      ∃ c, (OrthogonalStabilization.stabilizeMap v f).Homotopic (ContinuousMap.const _ c))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) :=
  exists_framedEmbedding_of_rankSevenVanishing
    ((OrthogonalStabilization.vanishing_iff_stabilizedVanishing v (by decide : 5 < 6)).mpr h6) h

end NoExoticSixSphere
