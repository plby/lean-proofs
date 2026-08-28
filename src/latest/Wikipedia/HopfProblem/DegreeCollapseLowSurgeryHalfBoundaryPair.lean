import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryRegularTime
import Wikipedia.HopfProblem.DegreeCollapseNonnegativeSurgeryPair

/-!

# The actual low-surgery pair on the two nonnegative halves

The original closed tube has strictly positive time and the new cap has
time one. The constructed time preserves nonnegativity on their common
exterior. Restricting the proved closed pair therefore gives the actual
pair on the original and native nonnegative halves, without H2 or
simple-connectivity assumptions on either half.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair
open Wikipedia.SmoothSixDPoincare

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

abbrev OldPositiveHalf := {m : M // 0 ≤ T.time m}

omit [IsManifold (𝓡 7) ∞ M] in
theorem compactSpace_oldPositiveHalf : CompactSpace (OldPositiveHalf A T) :=
  isCompact_iff_compactSpace.mp (isClosed_le continuous_const T.smooth.continuous).isCompact

omit [IsManifold (𝓡 7) ∞ M] in
theorem oldPiece_time_pos (p : OldDomain d) : 0 < T.time (oldPiece A p) :=
  T.margin_pos.trans_le (T.tube_time p.1 (oldRadius A • p.2.val)
    (ball_subset_closedBall (oldPiece_vector_mem A p)))

abbrev HalfExterior := NonnegativeSurgeryPair.Exterior (boundaryPair A hR) T.time

def halfBoundaryPair :
    SurgeryBoundaryPair (Vector (d + 1)) (Vector (7 - d)) (HalfExterior A hR T)
      (OldPositiveHalf A T) (PositiveHalf A hR T) :=
  NonnegativeSurgeryPair.pair (boundaryPair A hR) T.time (timeFunction A hR T)
    T.smooth.continuous (fun p ↦ (oldPiece_time_pos A T p).le)
    (fun p ↦ by
      change 0 ≤ timeFunction A hR T (nativeCapPoint A hR p)
      rw [timeFunction_cap]
      exact zero_le_one)
    (fun r ↦ (timeFunction_exterior_nonneg_iff A hR T r).symm)

theorem halfBoundaryPair_attaching (s : NoExoticSixSphere.Sphere d) :
    ((halfBoundaryPair A hR T).attachingSphere s).val = f s := by
  change (boundaryPair A hR).attachingSphere s = f s
  exact boundaryPair_attaching A hR s

theorem halfBoundaryPair_belt_ambient (w : sphere (0 : Vector (7 - d)) 1) :
    ((halfBoundaryPair A hR T).beltSphere w).val.val.val.val = A.map (0, w.val) := by
  change ((boundaryPair A hR).beltSphere w).val.val.val = _
  exact boundaryPair_belt_ambient A hR w

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
