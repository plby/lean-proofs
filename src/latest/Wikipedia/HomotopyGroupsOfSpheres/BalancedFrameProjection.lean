import Wikipedia.HomotopyGroupsOfSpheres.BalancedProjectionModel
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates
import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame

/-!
# The actual orthonormal-frame projection to the balanced real orbit

An orthonormal frame maps to the orthogonal projection onto its range, and
then to the corresponding balanced involution. The map is continuous and
surjective. Equal projection values are exactly equal frame ranges.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

theorem projection_eq_of_range {n : ℕ} (P Q : ProjectionSpace n)
    (hr : P.val.range = Q.val.range) : P = Q := by
  have hPQ : P.val * Q.val = Q.val := by
    apply ContinuousLinearMap.ext
    intro x
    exact projection_apply_range P.val P.property.1
      ⟨Q.val x, by rw [hr]; exact ⟨x, rfl⟩⟩
  have hQP : Q.val * P.val = P.val := by
    apply ContinuousLinearMap.ext
    intro x
    exact projection_apply_range Q.val Q.property.1
      ⟨P.val x, by rw [← hr]; exact ⟨x, rfl⟩⟩
  have hs := congrArg star hPQ
  rw [star_mul, P.property.2.1, Q.property.2.1] at hs
  exact Subtype.ext (hQP.symm.trans hs)

namespace FrameProjection

variable {N r : ℕ}

def operator (A : Stiefel.Space N r) : Vector N →L[ℝ] Vector N := A.val.comp A.val.adjoint

theorem operator_idempotent (A : Stiefel.Space N r) : IsIdempotentElem (operator A) := by
  have hA := (A.val.norm_map_iff_adjoint_comp_self).mp A.property
  change (A.val.comp A.val.adjoint).comp (A.val.comp A.val.adjoint) = A.val.comp A.val.adjoint
  calc
    (A.val.comp A.val.adjoint).comp (A.val.comp A.val.adjoint) =
        A.val.comp ((A.val.adjoint.comp A.val).comp A.val.adjoint) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = A.val.comp A.val.adjoint := by
      rw [hA, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem operator_selfAdjoint (A : Stiefel.Space N r) : IsSelfAdjoint (operator A) := by
  change (A.val.comp A.val.adjoint).adjoint = A.val.comp A.val.adjoint
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem operator_range (A : Stiefel.Space N r) : (operator A).range = A.val.range := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨A.val.adjoint x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨A.val x, ?_⟩
    change A.val (A.val.adjoint (A.val x)) = A.val x
    rw [Stiefel.RangeCoordinates.adjoint_self]

theorem operator_rank (A : Stiefel.Space N r) : Module.finrank ℝ (operator A).range = r := by
  rw [operator_range, LinearMap.finrank_range_of_inj (Stiefel.injective A)]
  exact finrank_euclideanSpace_fin

theorem continuous_operator : Continuous (operator (N := N) (r := r)) :=
  continuous_subtype_val.clm_comp
    (ContinuousLinearMap.adjoint.continuous.comp continuous_subtype_val)

def projection {n : ℕ} (A : Stiefel.Space (n + n) n) : ProjectionSpace n :=
  ⟨operator A, operator_idempotent A, operator_selfAdjoint A, operator_rank A⟩

def toBalanced {n : ℕ} (A : Stiefel.Space (n + n) n) : Space n := ofProjection (projection A)

theorem continuous_toBalanced (n : ℕ) : Continuous (toBalanced (n := n)) :=
  (continuous_ofProjection n).comp (continuous_operator.subtype_mk _)

theorem positiveProjection_toBalanced {n : ℕ} (A : Stiefel.Space (n + n) n) :
    positiveProjection (toBalanced A) = operator A :=
  congrArg Subtype.val (toProjection_ofProjection (projection A))

theorem toBalanced_eq_iff_range {n : ℕ} (A B : Stiefel.Space (n + n) n) :
    toBalanced A = toBalanced B ↔ A.val.range = B.val.range := by
  constructor
  · intro h
    have he := congrArg (fun J : Space n ↦ (positiveProjection J).range) h
    simpa only [positiveProjection_toBalanced, operator_range] using he
  · intro hr
    exact congrArg ofProjection (projection_eq_of_range (projection A) (projection B)
      ((operator_range A).trans (hr.trans (operator_range B).symm)))

theorem toBalanced_surjective (n : ℕ) : Function.Surjective (toBalanced (n := n)) := by
  intro J
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector n) = Module.finrank ℝ (positiveProjection J).range by
      rw [finrank_euclideanSpace_fin, positiveProjection_rank])
  let F : ContinuousRangeFrame (fun _ : Unit ↦ positiveProjection J) (Vector n) :=
    { equiv := fun _ ↦ q
      continuous := continuous_const }
  obtain ⟨t, ht⟩ := Stiefel.ProjectionDisk.exists_frame_of_rangeFrame _ F
  refine ⟨t (), ?_⟩
  have he : projection (t ()) = toProjection J :=
    projection_eq_of_range _ _ ((operator_range _).trans (ht ()))
  change ofProjection (projection (t ())) = J
  rw [he, ofProjection_toProjection]

def map (n : ℕ) : C(Stiefel.Space (n + n) n, Space n) :=
  ⟨toBalanced, continuous_toBalanced n⟩

end FrameProjection
end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
