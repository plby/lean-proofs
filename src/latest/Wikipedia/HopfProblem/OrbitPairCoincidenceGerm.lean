import Wikipedia.HopfProblem.OrbitPairCoincidenceDifferential

/-! # Coincidence transversality depends only on the two native map germs -/

noncomputable section

open Function Filter
open scoped Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.Coincidence

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

theorem differential_congr {u v u' v' : X → N} {x : X}
    (hu : u =ᶠ[𝓝 x] u') (hv : v =ᶠ[𝓝 x] v') :
    differential (I := I) (J := J) u v x = differential (I := I) (J := J) u' v' x := by
  let A : E →L[ℝ] G := mfderiv I J u x
  let B : E →L[ℝ] G := mfderiv I J v x
  let A' : E →L[ℝ] G := mfderiv I J u' x
  let B' : E →L[ℝ] G := mfderiv I J v' x
  have hA : A = A' := hu.mfderiv_eq
  have hB : B = B' := hv.mfderiv_eq
  change B - A = B' - A'
  rw [hA, hB]

theorem transverseAt_congr {u v u' v' : X → N} {x : X}
    (hu : u =ᶠ[𝓝 x] u') (hv : v =ᶠ[𝓝 x] v') :
    TransverseAt (I := I) (J := J) u v x ↔ TransverseAt (I := I) (J := J) u' v' x := by
  unfold TransverseAt
  rw [differential_congr hu hv]

end Wikipedia.HopfProblem.OrbitPair.Coincidence
