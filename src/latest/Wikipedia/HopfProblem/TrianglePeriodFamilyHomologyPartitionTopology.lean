import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Mathlib.Topology.Sets.Opens

/-!
# A topological decomposition into three disjoint open sets

Three pairwise disjoint open subsets covering a space give a homeomorphism
with their nested topological sum. Its inverse is the sum of the actual
subtype inclusions, including when some of the open sets are empty.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] (U : Fin 3 → TopologicalSpace.Opens X)

/-- The nested topological sum of the three open subsets. -/
abbrev openPartitionSum := U 0 ⊕ (U 1 ⊕ U 2)

/-- The actual subtype inclusion of one member of the open partition. -/
def openPartitionInclusion (i : Fin 3) : C(U i, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem openPartitionInclusion_apply (i : Fin 3) (x : U i) :
    openPartitionInclusion U i x = (x : X) := rfl

/-- The continuous map from the nested sum given by the three inclusions. -/
def openPartitionSumMap : C(openPartitionSum U, X) :=
  sumElimMap (openPartitionInclusion U 0)
    (sumElimMap (openPartitionInclusion U 1) (openPartitionInclusion U 2))

@[simp] theorem openPartitionSumMap_inl (x : U 0) :
    openPartitionSumMap U (Sum.inl x) = (x : X) := rfl

@[simp] theorem openPartitionSumMap_inr_inl (x : U 1) :
    openPartitionSumMap U (Sum.inr (Sum.inl x)) = (x : X) := rfl

@[simp] theorem openPartitionSumMap_inr_inr (x : U 2) :
    openPartitionSumMap U (Sum.inr (Sum.inr x)) = (x : X) := rfl

/-- The sum of inclusions of open subspaces is an open map. -/
theorem openPartitionSumMap_isOpenMap : IsOpenMap (openPartitionSumMap U) :=
  (U 0).isOpen.isOpenMap_subtype_val.sumElim
    ((U 1).isOpen.isOpenMap_subtype_val.sumElim (U 2).isOpen.isOpenMap_subtype_val)

variable (hdisj : Pairwise fun i j : Fin 3 =>
  Disjoint (U i : Set X) (U j : Set X))

include hdisj in
private theorem openPartitionInclusion_ne {i j : Fin 3} (hij : i ≠ j)
    (x : U i) (y : U j) : (x : X) ≠ (y : X) := by
  intro h
  exact Set.disjoint_left.mp (hdisj hij) x.property (h.symm ▸ y.property)

include hdisj in
/-- Disjointness makes the sum of the actual inclusions injective. -/
theorem openPartitionSumMap_injective : Function.Injective (openPartitionSumMap U) := by
  rintro (x | (x | x)) (y | (y | y)) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (0 : Fin 3) ≠ 1) x y h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (0 : Fin 3) ≠ 2) x y h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (1 : Fin 3) ≠ 0) x y h)
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (1 : Fin 3) ≠ 2) x y h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (2 : Fin 3) ≠ 0) x y h)
  · exact False.elim (openPartitionInclusion_ne U hdisj (by decide : (2 : Fin 3) ≠ 1) x y h)
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext h)

variable (hcover : (⋃ i, (U i : Set X)) = Set.univ)

include hcover in
/-- The cover property makes the sum of the actual inclusions surjective. -/
theorem openPartitionSumMap_surjective : Function.Surjective (openPartitionSumMap U) := by
  intro x
  have hx : x ∈ ⋃ i, (U i : Set X) := by rw [hcover]; exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  fin_cases i
  · exact ⟨Sum.inl ⟨x, hi⟩, rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨x, hi⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨x, hi⟩), rfl⟩

/-- A space partitioned into three open subspaces is their topological sum. -/
def openPartitionHomeomorph : X ≃ₜ openPartitionSum U :=
  ((Equiv.ofBijective (openPartitionSumMap U)
      ⟨openPartitionSumMap_injective U hdisj,
        openPartitionSumMap_surjective U hcover⟩).toHomeomorphOfContinuousOpen
    (openPartitionSumMap U).continuous (openPartitionSumMap_isOpenMap U)).symm

/-- The inverse is literally the sum of the three subtype inclusions. -/
@[simp] theorem openPartitionHomeomorph_symm_apply (a : openPartitionSum U) :
    (openPartitionHomeomorph U hdisj hcover).symm a = openPartitionSumMap U a := rfl

@[simp] theorem openPartitionHomeomorph_apply_zero (x : U 0) :
    openPartitionHomeomorph U hdisj hcover (x : X) =
      Sum.inl x :=
  (openPartitionHomeomorph U hdisj hcover).apply_symm_apply (Sum.inl x)

@[simp] theorem openPartitionHomeomorph_apply_one (x : U 1) :
    openPartitionHomeomorph U hdisj hcover (x : X) =
      Sum.inr (Sum.inl x) :=
  (openPartitionHomeomorph U hdisj hcover).apply_symm_apply (Sum.inr (Sum.inl x))

@[simp] theorem openPartitionHomeomorph_apply_two (x : U 2) :
    openPartitionHomeomorph U hdisj hcover (x : X) =
      Sum.inr (Sum.inr x) :=
  (openPartitionHomeomorph U hdisj hcover).apply_symm_apply (Sum.inr (Sum.inr x))

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
