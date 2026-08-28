import Wikipedia.NoExoticSixSphere.CompactifiedCollapseArfTransport
import Wikipedia.NoExoticSixSphere.RegularFiberStableArfObstruction
import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue

/-!
# Nonzero prescribed Arf obstructs stable nullity of the original framed collapse

Choose the actual fiber-preserving smooth representative and its native
fiber diffeomorphism. The proved compactification comparison retains the
original prescribed Arf invariant. The regular-fiber obstruction then
applies to every finite suspension of the original collapse map itself.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open GLOrthonormalization SphereMapSuspension

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a) (hn : 0 < e.ambientDimension - 6)
  (r : e.TubularRetraction) (m : M) [Subsingleton (π_ 2 M m)]

include hn in
theorem geometricArf_eq_zero_of_finite_suspension_nullhomotopic
    (j : ℕ) (hnull : (iterate d.sphereMap j).Nullhomotopic) :
    GeometricArf.invariant e a r m = 0 := by
  have hdim := e.dimension_le_ambient m
  have hN : e.ambientDimension = (e.ambientDimension - 6) + 6 := by omega
  obtain ⟨g, hg, H, hfiber, hreg, hgerm⟩ := d.exists_smoothSphereMap_regular
  let := regularFiberAtlas g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := regularFiber_isManifold g hg (sphereZero (e.ambientDimension - 6)) hreg 6
    (by simpa using hN)
  let := RegularSphereFiber.fiber_compact g (sphereZero (e.ambientDimension - 6))
  let D := e.diffeomorphToCompactifiedFiber g hg hreg hN hfiber
  let : SimplyConnectedSpace
      {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)} :=
    D.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (π_ 2
      {y : Sphere e.ambientDimension // g y = sphereZero (e.ambientDimension - 6)} (D m)) :=
    piTwo_subsingleton_of_homeomorph D.toHomeomorph m (D m)
  let eg := RegularSphereFiber.embedding g hg (sphereZero (e.ambientDimension - 6)) hreg 6 hN
  let ag := RegularSphereFiber.frame g hg (sphereZero (e.ambientDimension - 6)) hreg 6 hN
    (spherePole e.ambientDimension)
  obtain ⟨rg⟩ := eg.nonempty_tubularRetraction ag
  have he := d.geometricArf_compactified g hg hreg hN hfiber hgerm
    (spherePole e.ambientDimension) r m (D m) rg
  have hgnull : (iterate g j).Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnull
    exact ⟨c, (iterate_homotopic H j).symm.trans hc⟩
  have hz := RegularSphereFiber.geometricArf_eq_zero_of_finite_suspension_nullhomotopic
    g hg (sphereZero (e.ambientDimension - 6)) hreg hN hn
    (spherePole e.ambientDimension) (D m) j hgnull rg
  exact he.symm.trans hz

include hn in
theorem not_finitely_stably_nullhomotopic_of_geometricArf_ne_zero
    (hArf : GeometricArf.invariant e a r m ≠ 0) :
    ¬ ∃ j : ℕ, (iterate d.sphereMap j).Nullhomotopic := by
  rintro ⟨j, hnull⟩
  exact hArf (d.geometricArf_eq_zero_of_finite_suspension_nullhomotopic hn r m j hnull)

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
