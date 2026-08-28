import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyPartitionTopology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyPartitionSum

/-!
# Actual singular homology of a three-piece open partition

Three pairwise disjoint open subsets covering a space give an actual
homeomorphism with their topological sum. The proved singular homology
equivalence of that sum supplies the three component coordinates in every
degree. Inclusion maps and maps out of the space retain their literal
singular-homology meanings throughout.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)
  (hdisj : Pairwise fun i j : Fin 3 => Disjoint (U i : Set X) (U j : Set X))
  (hcover : (⋃ i, (U i : Set X)) = Set.univ)

/-- The inverse partition homeomorphism is the actual summed subtype-inclusion map. -/
theorem openPartitionHomeomorph_symm_toContinuousMap :
    ((openPartitionHomeomorph U hdisj hcover).symm : C(openPartitionSum U, X)) =
      openPartitionSumMap U := by
  apply ContinuousMap.ext
  exact openPartitionHomeomorph_symm_apply U hdisj hcover

/-- Actual integral homology of a three-piece open partition, with order `0,(1,2)`. -/
def openPartitionHomologyEquiv (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ]
      (SingularHomology (U 0) n ×
        (SingularHomology (U 1) n × SingularHomology (U 2) n)) :=
  (homeomorphHomologyEquiv (openPartitionHomeomorph U hdisj hcover) n).trans
    (tripleSumHomologyEquiv (U 0) (U 1) (U 2) n)

@[simp] theorem openPartitionHomologyEquiv_apply (n : ℕ) (a : SingularHomology X n) :
    openPartitionHomologyEquiv U hdisj hcover n a =
      tripleSumHomologyEquiv (U 0) (U 1) (U 2) n
        (singularHomologyMap (openPartitionHomeomorph U hdisj hcover) n a) := rfl

/-- The inverse sums the three actual induced subtype-inclusion maps. -/
theorem openPartitionHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology (U 0) n ×
      (SingularHomology (U 1) n × SingularHomology (U 2) n)) :
    (openPartitionHomologyEquiv U hdisj hcover n).symm a =
      singularHomologyMap (openPartitionInclusion U 0) n a.1 +
        (singularHomologyMap (openPartitionInclusion U 1) n a.2.1 +
          singularHomologyMap (openPartitionInclusion U 2) n a.2.2) := by
  change singularHomologyMap
    ((openPartitionHomeomorph U hdisj hcover).symm : C(openPartitionSum U, X)) n
    ((tripleSumHomologyEquiv (U 0) (U 1) (U 2) n).symm a) = _
  rw [openPartitionHomeomorph_symm_toContinuousMap]
  exact tripleSumHomologyEquiv_sumElim_symm
    (openPartitionInclusion U 0) (openPartitionInclusion U 1)
    (openPartitionInclusion U 2) n a

@[simp] theorem openPartitionHomologyEquiv_inclusion_zero (n : ℕ)
    (a : SingularHomology (U 0) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (singularHomologyMap (openPartitionInclusion U 0) n a) = (a, (0, 0)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, add_zero]

@[simp] theorem openPartitionHomologyEquiv_inclusion_one (n : ℕ)
    (a : SingularHomology (U 1) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (singularHomologyMap (openPartitionInclusion U 1) n a) = (0, (a, 0)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add, add_zero]

@[simp] theorem openPartitionHomologyEquiv_inclusion_two (n : ℕ)
    (a : SingularHomology (U 2) n) :
    openPartitionHomologyEquiv U hdisj hcover n
        (singularHomologyMap (openPartitionInclusion U 2) n a) = (0, (0, a)) := by
  apply (openPartitionHomologyEquiv U hdisj hcover n).symm.injective
  rw [LinearEquiv.symm_apply_apply, openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add]

@[simp] theorem openPartitionHomologyEquiv_symm_zero (n : ℕ)
    (a : SingularHomology (U 0) n) :
    (openPartitionHomologyEquiv U hdisj hcover n).symm (a, (0, 0)) =
      singularHomologyMap (openPartitionInclusion U 0) n a := by
  rw [openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, add_zero]

@[simp] theorem openPartitionHomologyEquiv_symm_one (n : ℕ)
    (a : SingularHomology (U 1) n) :
    (openPartitionHomologyEquiv U hdisj hcover n).symm (0, (a, 0)) =
      singularHomologyMap (openPartitionInclusion U 1) n a := by
  rw [openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add, add_zero]

@[simp] theorem openPartitionHomologyEquiv_symm_two (n : ℕ)
    (a : SingularHomology (U 2) n) :
    (openPartitionHomologyEquiv U hdisj hcover n).symm (0, (0, a)) =
      singularHomologyMap (openPartitionInclusion U 2) n a := by
  rw [openPartitionHomologyEquiv_symm_apply]
  simp only [map_zero, zero_add]

variable {Y : Type} [TopologicalSpace Y]

/-- A continuous map out of the partition acts by its three actual restrictions. -/
theorem openPartitionHomologyEquiv_map_out_symm (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (U 0) n ×
      (SingularHomology (U 1) n × SingularHomology (U 2) n)) :
    singularHomologyMap f n ((openPartitionHomologyEquiv U hdisj hcover n).symm a) =
      singularHomologyMap (f.comp (openPartitionInclusion U 0)) n a.1 +
        (singularHomologyMap (f.comp (openPartitionInclusion U 1)) n a.2.1 +
          singularHomologyMap (f.comp (openPartitionInclusion U 2)) n a.2.2) := by
  rw [openPartitionHomologyEquiv_symm_apply, map_add, map_add,
    singularHomologyMap_comp, singularHomologyMap_comp, singularHomologyMap_comp]
  rfl

/-- The map-out formula on any actual ambient singular homology class. -/
theorem openPartitionHomologyEquiv_map_out (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology X n) :
    singularHomologyMap f n a =
      singularHomologyMap (f.comp (openPartitionInclusion U 0)) n
          (openPartitionHomologyEquiv U hdisj hcover n a).1 +
        (singularHomologyMap (f.comp (openPartitionInclusion U 1)) n
            (openPartitionHomologyEquiv U hdisj hcover n a).2.1 +
          singularHomologyMap (f.comp (openPartitionInclusion U 2)) n
            (openPartitionHomologyEquiv U hdisj hcover n a).2.2) := by
  have h := openPartitionHomologyEquiv_map_out_symm U hdisj hcover f n
    (openPartitionHomologyEquiv U hdisj hcover n a)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- Normalize a map-out formula by specified actual continuous restrictions. -/
theorem openPartitionHomologyEquiv_map_out_of_restrictions (f : C(X, Y))
    (g : ∀ i : Fin 3, C(U i, Y))
    (hg : ∀ i, f.comp (openPartitionInclusion U i) = g i) (n : ℕ)
    (a : SingularHomology X n) :
    singularHomologyMap f n a =
      singularHomologyMap (g 0) n (openPartitionHomologyEquiv U hdisj hcover n a).1 +
        (singularHomologyMap (g 1) n (openPartitionHomologyEquiv U hdisj hcover n a).2.1 +
          singularHomologyMap (g 2) n (openPartitionHomologyEquiv U hdisj hcover n a).2.2) := by
  rw [openPartitionHomologyEquiv_map_out U hdisj hcover f n a, hg 0, hg 1, hg 2]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
