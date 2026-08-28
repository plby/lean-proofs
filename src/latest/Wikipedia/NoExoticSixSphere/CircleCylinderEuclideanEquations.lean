import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanEmbedding

/-!
# The same regular equations in the fixed Euclidean ambient coordinates

The actual equations are precomposed with the inverse block isometry.
They still vanish on the original embedding and have a smooth surjective
differential there. No independently chosen normal frame is substituted.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def euclideanEquations (a : Sphere 1 × Sphere m) :
    EuclideanSpace ℝ (Fin (2 + (m + 1))) → NormalModel n :=
  ambientEquations d a ∘ (ambientCoordinates m).symm.toContinuousLinearEquiv

theorem euclideanEquations_zero (a : Sphere 1 × Sphere m) (p : Fiber d) :
    euclideanEquations d a (euclideanInclusion d p) = 0 := by
  change ambientEquations d a
    ((ambientCoordinates m).symm (ambientCoordinates m (ambientInclusion d p))) = 0
  rw [(ambientCoordinates m).symm_apply_apply]
  exact ambientEquations_zero d a p

theorem contDiffAt_euclideanEquations (a : Sphere 1 × Sphere m) (p : Fiber d) :
    ContDiffAt ℝ ∞ (euclideanEquations d a) (euclideanInclusion d p) := by
  have hg : ContDiffAt ℝ ∞ (ambientEquations d a)
      ((ambientCoordinates m).symm (euclideanInclusion d p)) := by
    rw [euclideanInclusion, (ambientCoordinates m).symm_apply_apply]
    exact contDiffAt_ambientEquations d a p
  exact hg.comp (euclideanInclusion d p)
    (ambientCoordinates m).symm.toContinuousLinearEquiv.contDiff.contDiffAt

theorem fderiv_euclideanEquations (a : Sphere 1 × Sphere m) (p : Fiber d) :
    fderiv ℝ (euclideanEquations d a) (euclideanInclusion d p) =
      (fderiv ℝ (ambientEquations d a) (ambientInclusion d p)).comp
        (ambientCoordinates m).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hg : DifferentiableAt ℝ (ambientEquations d a)
      ((ambientCoordinates m).symm.toContinuousLinearEquiv (euclideanInclusion d p)) := by
    change DifferentiableAt ℝ (ambientEquations d a)
      ((ambientCoordinates m).symm (ambientCoordinates m (ambientInclusion d p)))
    rw [(ambientCoordinates m).symm_apply_apply]
    exact (contDiffAt_ambientEquations d a p).differentiableAt (by simp)
  rw [euclideanEquations, fderiv_comp (euclideanInclusion d p) hg
    (ambientCoordinates m).symm.toContinuousLinearEquiv.differentiableAt,
    ContinuousLinearEquiv.fderiv]
  congr 2
  exact (ambientCoordinates m).symm_apply_apply (ambientInclusion d p)

theorem surjective_fderiv_euclideanEquations (a : Sphere 1 × Sphere m) (p : Fiber d) :
    Surjective (fderiv ℝ (euclideanEquations d a) (euclideanInclusion d p)) := by
  rw [fderiv_euclideanEquations]
  exact (surjective_fderiv_ambientEquations d a p).comp (ambientCoordinates m).symm.surjective

end NoExoticSixSphere.CircleCylinder
