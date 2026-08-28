import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryBoundaryPair
import Wikipedia.HopfProblem.DegreeCollapseSurgeryTimeProfile
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps

/-!

# A continuous defining time on the actual native low-surgery end

Flatten the original time above a positive tube margin. On the common
closed exterior use that profile, and on the actual closed cap use one.
The proved native cover and exact incidence give the descended continuous
function without replacing the native end by a canonical surgery quotient.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair
open Wikipedia.SmoothSixDPoincare

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

structure TimeData where
  time : M → ℝ
  smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ time
  regular : ∀ p, time p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) time p)
  margin : ℝ
  margin_pos : 0 < margin
  tube_time : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius,
    margin ≤ time (A.tube (s, v))

def oldProfile (T : TimeData A) (m : M) : ℝ :=
  SurgeryTimeProfile.profile T.margin (T.time m)

theorem contMDiff_oldProfile (T : TimeData A) : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ (oldProfile A T) :=
  (SurgeryTimeProfile.contDiff_profile T.margin).contMDiff.comp T.smooth

theorem oldProfile_tube (T : TimeData A) (s : NoExoticSixSphere.Sphere d)
    (v : Vector (7 - d)) (hv : v ∈ closedBall (0 : Vector (7 - d)) A.radius) :
    oldProfile A T (A.tube (s, v)) = 1 :=
  SurgeryTimeProfile.profile_eq_one T.margin_pos (T.tube_time s v hv)

variable [CompactSpace M] [IsManifold (𝓡 7) ∞ M] (hR : A.radius = 2) (T : TimeData A)

def exteriorTime : C(closedExterior A, ℝ) :=
  ⟨fun r ↦ oldProfile A T r.val,
    (contMDiff_oldProfile A T).continuous.comp continuous_subtype_val⟩

theorem timePieces_agree (r : closedExterior A) (p : CapDomain d)
    (h : newExterior A r = nativeCapPoint A hR p) : exteriorTime A T r = 1 := by
  obtain ⟨q, rfl, _⟩ := (new_overlap A hR r p).mp h
  apply oldProfile_tube
  rw [mem_closedBall, dist_zero_right, commonFace_vector_norm]
  exact (oldRadius_lt A).le

def timeFunction : C(otherBoundaryPart A, ℝ) :=
  ClosedCover.mapOfClosedPieces (newExterior A) (nativeCapPoint A hR)
    (isClosedEmbedding_newExterior A) (isClosedEmbedding_nativeCapPoint A hR)
    (new_cover A hR) (exteriorTime A T) (ContinuousMap.const _ 1)
    (timePieces_agree A hR T)

theorem timeFunction_exterior (r : closedExterior A) :
    timeFunction A hR T (newExterior A r) = oldProfile A T r.val :=
  ClosedCover.mapOfClosedPieces_left (newExterior A) (nativeCapPoint A hR)
    (isClosedEmbedding_newExterior A) (isClosedEmbedding_nativeCapPoint A hR)
    (new_cover A hR) (exteriorTime A T) (ContinuousMap.const _ 1)
    (timePieces_agree A hR T) r

theorem timeFunction_cap (p : CapDomain d) :
    timeFunction A hR T (nativeCapPoint A hR p) = 1 :=
  ClosedCover.mapOfClosedPieces_right (newExterior A) (nativeCapPoint A hR)
    (isClosedEmbedding_newExterior A) (isClosedEmbedding_nativeCapPoint A hR)
    (new_cover A hR) (exteriorTime A T) (ContinuousMap.const _ 1)
    (timePieces_agree A hR T) p

theorem timeFunction_zero_iff (y : otherBoundaryPart A) :
    timeFunction A hR T y = 0 ↔
      ∃ r : closedExterior A, T.time r.val = 0 ∧ newExterior A r = y := by
  constructor
  · intro hy
    have hc : y ∈ range (newExterior A) ∪ range (nativeCapPoint A hR) := by
      rw [new_cover A hR]
      trivial
    rcases hc with ⟨r, rfl⟩ | ⟨p, rfl⟩
    · rw [timeFunction_exterior] at hy
      exact ⟨r, (SurgeryTimeProfile.profile_eq_zero_iff T.margin_pos _).mp hy, rfl⟩
    · rw [timeFunction_cap] at hy
      exact (one_ne_zero hy).elim
  · rintro ⟨r, hr, rfl⟩
    rw [timeFunction_exterior]
    exact (SurgeryTimeProfile.profile_eq_zero_iff T.margin_pos _).mpr hr

theorem timeFunction_exterior_nonneg_iff (r : closedExterior A) :
    0 ≤ timeFunction A hR T (newExterior A r) ↔ 0 ≤ T.time r.val := by
  rw [timeFunction_exterior]
  exact SurgeryTimeProfile.profile_nonneg_iff T.margin_pos _

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
