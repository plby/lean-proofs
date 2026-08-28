import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponentialPolygon
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumExponential

/-! # Sampling balanced rotations into the actual constrained minimum polygons -/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices

variable {n m : ℕ}

def rotationVertices (τ : Fin (m + 2) → ℝ) (J : BalancedRealInvolutions.Space n) :
    VertexSpace.Space (Index n) m := fun j ↦ rotation J (τ j.castSucc.succ * Real.pi)

theorem continuous_rotationVertices (n : ℕ) (τ : Fin (m + 2) → ℝ) :
    Continuous (rotationVertices (n := n) τ) := by
  apply continuous_pi
  intro j
  let phase : C(BalancedRealInvolutions.Space n, ℝ × BalancedRealInvolutions.Space n) :=
    ⟨fun J ↦ (τ j.castSucc.succ * Real.pi, J), continuous_const.prodMk continuous_id⟩
  let rot : C(ℝ × BalancedRealInvolutions.Space n, SpecialSpace (Index n)) :=
    ⟨fun p ↦ rotation p.2 p.1, continuous_rotation n⟩
  exact (rot.comp phase).continuous

theorem rotationVertices_eq_exponentialVertices (τ : Fin (m + 2) → ℝ)
    (J : BalancedRealInvolutions.Space n) :
    rotationVertices τ J = exponentialVertices τ (minimumGenerator J) :=
  funext (fun j ↦ (exponentialCurve_minimumGenerator J (τ j.castSucc.succ)).symm)

theorem minimumGenerator_endpoint (J : BalancedRealInvolutions.Space n) :
    QuaternionicSymmetricMatrices.exponential (minimumGenerator J) = antipode n := by
  have h := exponentialCurve_minimumGenerator J 1
  simpa only [exponentialCurve, one_smul, one_mul, rotation_pi] using h

variable (τ : Fin (m + 2) → ℝ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (J : BalancedRealInvolutions.Space n)
    (hsmall : ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))

include hzero hone hsmall

theorem rotationVertices_admissible :
    rotationVertices τ J ∈ admissible specialIdentity (antipode n) m := by
  rw [rotationVertices_eq_exponentialVertices]
  exact exponentialVertices_admissible (antipode n) τ hzero hone (minimumGenerator J)
    (minimumGenerator_endpoint J) hsmall

theorem generator_rotationVertices (i : Fin (m + 1)) :
    generator specialIdentity (antipode n) (rotationVertices τ J) i =
      (τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J) := by
  rw [rotationVertices_eq_exponentialVertices]
  exact generator_exponentialVertices (antipode n) τ hzero hone (minimumGenerator J)
    (minimumGenerator_endpoint J) hsmall i

theorem path_rotationVertices (hτ : StrictMono τ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    path specialIdentity (antipode n) τ hτ (rotationVertices τ J)
      (rotationVertices_admissible τ hzero hone J hsmall) t = rotation J (t * Real.pi) := by
  have h := path_exponentialVertices (antipode n) τ hzero hone (minimumGenerator J)
    (minimumGenerator_endpoint J) hsmall hτ ht
  simpa only [← rotationVertices_eq_exponentialVertices, exponentialCurve_minimumGenerator] using h

theorem energy_rotationVertices (hτ : StrictMono τ) :
    energy specialIdentity (antipode n) τ (rotationVertices τ J) = (4 * n : ℝ) * Real.pi ^ 2 := by
  rw [rotationVertices_eq_exponentialVertices,
    energy_exponentialVertices (antipode n) τ hzero hone (minimumGenerator J)
      (minimumGenerator_endpoint J) hsmall hτ, minimumGenerator_squareNorm]
  ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
