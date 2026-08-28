import Wikipedia.NoExoticSixSphere.SkewExponentialConjugation
import Wikipedia.NoExoticSixSphere.OrthogonalIndexForm

/-!
# Rotating a skew field to complete the energy index square

The half-speed backwards conjugation solves `C' = -[K,C]/2` and preserves
both the Hilbert--Schmidt norm and the commutator norm. This cancels the
connection term in the completed-square index form.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalIndexTransport

open GLOrthonormalization CayleyTransform OrthogonalExponential SkewConjugation
  OrthogonalCommutator HilbertSchmidt

variable {n : ℕ}

noncomputable def transport (K A : SkewOperators n) (t : ℝ) : SkewOperators n :=
  conjugate (exp (t • ((-1 / 2 : ℝ) • K))) A

theorem contDiff_transport (K A : SkewOperators n) : ContDiff ℝ ∞ (transport K A) :=
  contDiff_conjugate_exp ((-1 / 2 : ℝ) • K) A

theorem hasDerivAt_transport (K A : SkewOperators n) (t : ℝ) :
    HasDerivAt (fun r ↦ (transport K A r : Vector n →L[ℝ] Vector n))
      ((-1 / 2 : ℝ) • commutator (K : Vector n →L[ℝ] Vector n)
        (transport K A t : Vector n →L[ℝ] Vector n)) t := by
  simpa only [Submodule.coe_smul, commutator_smul_left] using!
    hasDerivAt_conjugate_exp ((-1 / 2 : ℝ) • K) A t

theorem squareNorm_transport (K A : SkewOperators n) (t : ℝ) :
    squareNorm (transport K A t : Vector n →L[ℝ] Vector n) =
      squareNorm (A : Vector n →L[ℝ] Vector n) := squareNorm_conjugate _ A

theorem squareNorm_commutator_transport (K A : SkewOperators n) (t : ℝ) :
    squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
      (transport K A t : Vector n →L[ℝ] Vector n)) =
        squareNorm (commutator (K : Vector n →L[ℝ] Vector n)
          (A : Vector n →L[ℝ] Vector n)) := by
  have he : (exp (t • ((-1 / 2 : ℝ) • K))).1.1.comp (K : Vector n →L[ℝ] Vector n) =
      (K : Vector n →L[ℝ] Vector n).comp (exp (t • ((-1 / 2 : ℝ) • K))).1.1 := by
    simpa only [smul_smul] using exp_smul_commute K (t * (-1 / 2))
  rw [transport, commutator_conjugate _ _ _ he, squareNorm_left, squareNorm_right]

end NoExoticSixSphere.OrthogonalIndexTransport
