import Wikipedia.HopfProblem.OrbitPairSubdivisionFaceNaturality
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Uniform face means and diameter bounds

These estimates take place in a real normed space, so they apply to the
affine images of subdivided simplices, not only to the initial standard
simplex. Uniform means remain in convex balls and split exactly over
disjoint unions of faces.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def faceMean (v : V → E) (A : Finset V) : E :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, v i

theorem faceMean_eq_centerMass (v : V → E) (A : Finset V) :
    faceMean v A = A.centerMass (fun _ ↦ (1 : ℝ)) v := by
  simp [faceMean, Finset.centerMass]

theorem faceMean_mem_convex (v : V → E) (A : Finset V) (hA : A.Nonempty)
    (C : Set E) (hC : Convex ℝ C) (hv : ∀ i ∈ A, v i ∈ C) : faceMean v A ∈ C := by
  rw [faceMean_eq_centerMass]
  exact hC.centerMass_mem (fun _ _ ↦ zero_le_one)
    (by simpa using (Nat.cast_pos.mpr hA.card_pos : (0 : ℝ) < A.card)) hv

theorem faceMean_dist_le (v : V → E) (A : Finset V) (hA : A.Nonempty)
    (x : E) (D : ℝ) (hv : ∀ i ∈ A, dist (v i) x ≤ D) : dist (faceMean v A) x ≤ D :=
  faceMean_mem_convex v A hA (Metric.closedBall x D) (convex_closedBall x D) hv

theorem faceMeans_dist_le (v : V → E) (A C B : Finset V)
    (hA : A.Nonempty) (hC : C.Nonempty) (hAB : A ⊆ B) (hCB : C ⊆ B)
    (D : ℝ) (hv : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (faceMean v A) (faceMean v C) ≤ D := by
  apply faceMean_dist_le v A hA
  intro i hi
  have h := faceMean_dist_le v C hC (v i) D (fun j hj ↦ hv j (hCB hj) i (hAB hi))
  simpa only [dist_comm] using h

theorem faceMean_union (v : V → E) (A C : Finset V) [DecidableEq V]
    (hAC : Disjoint A C) (hA : A.Nonempty) (hC : C.Nonempty) :
    faceMean v (A ∪ C) =
      ((A.card : ℝ) / (A.card + C.card)) • faceMean v A +
        ((C.card : ℝ) / (A.card + C.card)) • faceMean v C := by
  have ha : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.card_ne_zero
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.card_ne_zero
  unfold faceMean
  rw [Finset.card_union_of_disjoint hAC, Finset.sum_union hAC, Nat.cast_add,
    smul_add, smul_smul, smul_smul]
  congr 1
  · apply congrArg (fun r : ℝ ↦ r • ∑ i ∈ A, v i)
    field_simp
  · apply congrArg (fun r : ℝ ↦ r • ∑ i ∈ C, v i)
    field_simp

end Wikipedia.HopfProblem.OrbitPair.Subdivision
