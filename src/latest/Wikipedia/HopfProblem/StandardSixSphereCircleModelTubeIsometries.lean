import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeBoundary
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeSmooth
import Wikipedia.HopfProblem.StandardSixSphereCircleModelIsometries

/-!
# Equivariance of the actual standard tube

Every genuine orthogonal action on the four normal coordinates preserves
the tube maps and their boundary restriction.  In particular these formulas
apply directly to the previously constructed real circle rotations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

@[simp] theorem baseFactor_isometry (L : Normal ≃ₗᵢ[ℝ] Normal) (y : Normal) :
    baseFactor (L y) = baseFactor y := by
  simp only [baseFactor, L.norm_map]

theorem ambient_isometry (L : Normal ≃ₗᵢ[ℝ] Normal) (b : BaseSphere) (y : Normal) :
    Isometries.ambientIsometry L (ambient b y) = ambient b (L y) := by
  rw [ambient, Isometries.ambientIsometry_join, ambient, baseFactor_isometry]

def normalBallMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (y : ↥(normalBall r)) :
    ↥(normalBall r) :=
  ⟨L y.val, (mem_normalBall r _).mpr (by rw [L.norm_map]; exact normalBall_norm_lt r y)⟩

def closedBallMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (y : ↥(Metric.closedBall (0 : Normal) r)) : ↥(Metric.closedBall (0 : Normal) r) :=
  ⟨L y.val, by
    rw [Metric.mem_closedBall, dist_zero_right, L.norm_map]
    exact closedBall_norm_le r y⟩

def openDomainMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (q : OpenDomain r) : OpenDomain r :=
  (q.1, normalBallMap r L q.2)

def closedDomainMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (q : ClosedDomain r) : ClosedDomain r :=
  (q.1, closedBallMap r L q.2)

def openTubeMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (p : ↥(openTube r)) : ↥(openTube r) :=
  ⟨Isometries.sphereMap L p.val, by
    change ‖normal (Isometries.ambientIsometry L p.val.val)‖ < r
    rw [Isometries.normal_ambientIsometry, L.norm_map]
    exact p.property⟩

def closedTubeMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (p : ↥(closedTube r)) :
    ↥(closedTube r) :=
  ⟨Isometries.sphereMap L p.val, by
    change ‖normal (Isometries.ambientIsometry L p.val.val)‖ ≤ r
    rw [Isometries.normal_ambientIsometry, L.norm_map]
    exact p.property⟩

@[simp] theorem normalBallMap_val (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (y : ↥(normalBall r)) : (normalBallMap r L y).val = L y.val := rfl

@[simp] theorem closedBallMap_val (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (y : ↥(Metric.closedBall (0 : Normal) r)) : (closedBallMap r L y).val = L y.val := rfl

@[simp] theorem openTubeMap_val (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (p : ↥(openTube r)) : (openTubeMap r L p).val = Isometries.sphereMap L p.val := rfl

@[simp] theorem closedTubeMap_val (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (p : ↥(closedTube r)) : (closedTubeMap r L p).val = Isometries.sphereMap L p.val := rfl

theorem openForward_equivariant (r : ℝ) (hr1 : r ≤ 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (q : OpenDomain r) :
    openTubeMap r L (openForward r hr1 q) = openForward r hr1 (openDomainMap r L q) := by
  apply Subtype.ext
  apply Subtype.ext
  exact ambient_isometry L q.1 q.2.val

theorem closedForward_equivariant (r : ℝ) (hr1 : r < 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (q : ClosedDomain r) :
    closedTubeMap r L (closedForward r hr1 q) = closedForward r hr1 (closedDomainMap r L q) := by
  apply Subtype.ext
  apply Subtype.ext
  exact ambient_isometry L q.1 q.2.val

theorem openInverse_equivariant (r : ℝ) (hr1 : r ≤ 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (p : ↥(openTube r)) :
    openInverse r hr1 (openTubeMap r L p) = openDomainMap r L (openInverse r hr1 p) := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖base (Isometries.ambientIsometry L p.val.val)‖⁻¹ •
        base (Isometries.ambientIsometry L p.val.val) = ‖base p.val.val‖⁻¹ • base p.val.val
    rw [Isometries.base_ambientIsometry]
  · apply Subtype.ext
    exact Isometries.normal_ambientIsometry L p.val.val

theorem closedInverse_equivariant (r : ℝ) (hr1 : r < 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (p : ↥(closedTube r)) :
    closedInverse r hr1 (closedTubeMap r L p) = closedDomainMap r L (closedInverse r hr1 p) := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖base (Isometries.ambientIsometry L p.val.val)‖⁻¹ •
        base (Isometries.ambientIsometry L p.val.val) = ‖base p.val.val‖⁻¹ • base p.val.val
    rw [Isometries.base_ambientIsometry]
  · apply Subtype.ext
    exact Isometries.normal_ambientIsometry L p.val.val

theorem openDiffeomorph_equivariant (r : ℝ) (hr1 : r ≤ 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (q : OpenDomain r) :
    openTubeMap r L (openDiffeomorph r hr1 q) =
      openDiffeomorph r hr1 (openDomainMap r L q) := openForward_equivariant r hr1 L q

theorem closedHomeomorph_equivariant (r : ℝ) (hr1 : r < 1) (L : Normal ≃ₗᵢ[ℝ] Normal)
    (q : ClosedDomain r) :
    closedTubeMap r L (closedHomeomorph r hr1 q) =
      closedHomeomorph r hr1 (closedDomainMap r L q) := closedForward_equivariant r hr1 L q

def boundaryDomainMap (L : Normal ≃ₗᵢ[ℝ] Normal) (q : BaseSphere × NormalSphere) :
    BaseSphere × NormalSphere := (q.1, Isometries.normalSphereMap L q.2)

def boundaryLevelMap (r : ℝ) (L : Normal ≃ₗᵢ[ℝ] Normal) (p : ↥(radiusLevel r)) :
    ↥(radiusLevel r) :=
  ⟨Isometries.sphereMap L p.val, by
    change ‖normal (Isometries.ambientIsometry L p.val.val)‖ = r
    rw [Isometries.normal_ambientIsometry, L.norm_map]
    exact p.property⟩

theorem boundaryHomeomorph_equivariant (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (L : Normal ≃ₗᵢ[ℝ] Normal) (q : BaseSphere × NormalSphere) :
    boundaryLevelMap r L (boundaryHomeomorph r hr hr1 q) =
      boundaryHomeomorph r hr hr1 (boundaryDomainMap L q) := by
  apply Subtype.ext
  exact congrArg (fun p : Complement => p.val)
    (Isometries.complementMap_boundaryPoint L r hr hr1 q)

theorem boundaryIntoClosed_equivariant (r : ℝ) (hr : 0 < r)
    (L : Normal ≃ₗᵢ[ℝ] Normal) (q : BaseSphere × NormalSphere) :
    closedDomainMap r L (boundaryIntoClosed r hr q) =
      boundaryIntoClosed r hr (boundaryDomainMap L q) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact L.map_smul r q.2.val

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
