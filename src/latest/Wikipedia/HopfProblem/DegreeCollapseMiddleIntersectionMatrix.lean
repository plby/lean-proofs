import Wikipedia.HopfProblem.DegreeCollapseMiddleSphereTransversality
import Wikipedia.NoExoticSixSphere.GeometricIntersectionFundamentalClass

/-!
# The actual mod-two intersection matrix of the constructed middle families

The exact singleton-or-empty source-pair sets compute the genuine geometric
intersection number. The standard sphere classes then give the identity
matrix for the original mod-two homology pairing. This is not an integer
intersection or unit-detector assertion.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Classical
open Wikipedia.SmoothSixDPoincare
open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
  {D : SeparatedSystem (Vector 6) M} (F : D.SmoothMiddleFamilies)

namespace SmoothMiddleFamilies

theorem pairs_same (p : D.MiddleLabel) :
    MapIntersections.pairs (F.descending p) (F.ascending p) = {(middlePole, middlePole)} := by
  ext z
  change (F.descending p z.1 = F.ascending p z.2) ↔ z = (middlePole, middlePole)
  rw [F.pair_iff]
  constructor
  · rintro ⟨hx, hy, -⟩
    exact Prod.ext hx hy
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

theorem pairs_distinct (p q : D.MiddleLabel) (hpq : p ≠ q) :
    MapIntersections.pairs (F.descending p) (F.ascending q) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hpq ((F.pair_iff p q z.1 z.2).mp hz).2.2

theorem intersectionParity (p q : D.MiddleLabel) :
    MapIntersections.parity (F.descending p) (F.ascending q) =
      if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [MapIntersections.parity, F.pairs_same]
  · simp only [MapIntersections.parity, F.pairs_distinct p q hpq, Set.ncard_empty,
      Nat.cast_zero, if_neg hpq]

theorem intersectionNumber (e : EuclideanEmbedding 6 M) (r : e.TubularRetraction)
    (p q : D.MiddleLabel) :
    e.sphereIntersectionNumber r (F.descending p) (F.ascending q) =
      if p = q then 1 else 0 := by
  rw [e.sphereIntersectionNumber_eq_parity r (F.descending p) (F.ascending q)
    (F.descending_smooth p) (F.ascending_smooth q)
      (fun x y h => F.native_transverse p q x y h.symm)]
  exact F.intersectionParity p q

attribute [local instance] modHomologyModule

variable [SimplyConnectedSpace M] (e : EuclideanEmbedding 6 M) (r : e.TubularRetraction)
  (m : M) [Subsingleton (π_ 2 M m)]

theorem homologyIntersectionMatrix (p q : D.MiddleLabel) :
    e.modTwoHomologyIntersection r m
      (SixSphereMiddleParity.sphereClass (F.descending p))
      (SixSphereMiddleParity.sphereClass (F.ascending q)) =
      if p = q then 1 else 0 := by
  rw [e.modTwoHomologyIntersection_standardSphereClass r m]
  exact F.intersectionNumber e r p q

end SmoothMiddleFamilies
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
