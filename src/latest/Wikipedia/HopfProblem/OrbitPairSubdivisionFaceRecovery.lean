import Wikipedia.HopfProblem.OrbitPairSubdivisionBarycentricCoordinates

/-!
# Recovering a nested face from a barycentric coordinate threshold

For positive weights on a nested chain, the sum of the remaining normalized
weights is a threshold which distinguishes the vertices of that face from
all other vertices. Strict positivity is essential for the reverse direction.
-/

noncomputable section

universe u

open PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz

variable {n k : ℕ}
variable (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
variable (t : Simplex k)

def tailWeight (j : Fin (k + 1)) : ℝ :=
  ∑ l, if j ≤ l then chainWeight A t l else 0

theorem tailWeight_pos (ht : ∀ j, 0 < t j) (j : Fin (k + 1)) :
    0 < tailWeight A t j := by
  classical
  unfold tailWeight
  apply (Finset.sum_pos_iff_of_nonneg (fun l _ ↦ ?_)).mpr
  · exact ⟨j, Finset.mem_univ j, by simpa using chainWeight_pos A t ht j⟩
  · split_ifs
    · exact chainWeight_nonneg A t l
    · exact le_rfl

theorem tailWeight_strictAnti (ht : ∀ j, 0 < t j) : StrictAnti (tailWeight A t) := by
  classical
  intro i j hij
  unfold tailWeight
  apply Finset.sum_lt_sum
  · intro l hl
    by_cases hjl : j ≤ l
    · simp only [hjl, (hij.le.trans hjl), ite_true]
      exact le_rfl
    · simp only [hjl, ite_false]
      split_ifs
      · exact chainWeight_nonneg A t l
      · exact le_rfl
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa only [not_le_of_gt hij, ite_false, le_refl, ite_true] using
      chainWeight_pos A t ht i

theorem tailWeight_le_coordinate_of_mem (hA : Monotone A)
    (j : Fin (k + 1)) (i : Fin (n + 1)) (hi : ULift.up i ∈ (A j).finset) :
    tailWeight A t j ≤ chainCoordinate A t i := by
  classical
  unfold tailWeight chainCoordinate
  apply Finset.sum_le_sum
  intro l hl
  by_cases hjl : j ≤ l
  · have hil : ULift.up i ∈ (A l).finset :=
      (hA hjl : (A j).finset ⊆ (A l).finset) hi
    simp only [hjl, hil, ite_true]
    exact le_rfl
  · simp only [hjl, ite_false]
    split_ifs
    · exact chainWeight_nonneg A t l
    · exact le_rfl

theorem coordinate_lt_tailWeight_of_not_mem (hA : Monotone A)
    (ht : ∀ j, 0 < t j) (j : Fin (k + 1)) (i : Fin (n + 1))
    (hi : ULift.up i ∉ (A j).finset) :
    chainCoordinate A t i < tailWeight A t j := by
  classical
  unfold chainCoordinate tailWeight
  apply Finset.sum_lt_sum
  · intro l hl
    by_cases hjl : j ≤ l
    · simp only [hjl, ite_true]
      split_ifs
      · exact le_rfl
      · exact chainWeight_nonneg A t l
    · have hil : ULift.up i ∉ (A l).finset := fun h ↦
        hi ((hA (le_of_not_ge hjl) : (A l).finset ⊆ (A j).finset) h)
      simp only [hil, hjl, ite_false]
      exact le_rfl
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    simpa only [hi, ite_false, le_refl, ite_true] using chainWeight_pos A t ht j

theorem mem_face_iff_threshold (hA : Monotone A) (ht : ∀ j, 0 < t j)
    (j : Fin (k + 1)) (i : Fin (n + 1)) :
    ULift.up i ∈ (A j).finset ↔ tailWeight A t j ≤ chainCoordinate A t i := by
  constructor
  · exact tailWeight_le_coordinate_of_mem A t hA j i
  · intro h
    by_contra hi
    exact (not_lt_of_ge h) (coordinate_lt_tailWeight_of_not_mem A t hA ht j i hi)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
