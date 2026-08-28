import Wikipedia.NoExoticSixSphere.OrthogonalGroupOperations

/-!
# Compactness of the orthogonal operators

The actual operator inclusion identifies the orthogonal operators with the
closed, bounded locus of norm-preserving endomorphisms. Invertibility follows
from finite dimension and is not an additional closure condition.
-/

open Set

namespace NoExoticSixSphere.OrthogonalCompactness

open GLOrthonormalization

variable {n : ℕ}

def normPreservingLocus (n : ℕ) : Set (Vector n →L[ℝ] Vector n) :=
  {A | ∀ x, ‖A x‖ = ‖x‖}

theorem normPreserving_isInvertible (A : Vector n →L[ℝ] Vector n)
    (hA : A ∈ normPreservingLocus n) : A.IsInvertible := by
  let L : Vector n →ₗᵢ[ℝ] Vector n := { A.toLinearMap with norm_map' := hA }
  let e := (LinearEquiv.ofInjectiveEndo A.toLinearMap L.injective).toContinuousLinearEquiv
  exact ⟨e, by apply ContinuousLinearMap.ext; intro x; rfl⟩

theorem isClosed_normPreservingLocus (n : ℕ) : IsClosed (normPreservingLocus n) := by
  change IsClosed {A : Vector n →L[ℝ] Vector n | ∀ x, ‖A x‖ = ‖x‖}
  rw [ofPred_forall]
  exact isClosed_iInter (fun x ↦
    isClosed_eq (continuous_id.clm_apply continuous_const).norm continuous_const)

theorem norm_le_one (A : Vector n →L[ℝ] Vector n) (hA : A ∈ normPreservingLocus n) :
    ‖A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound A zero_le_one
  intro x
  rw [hA x, one_mul]

theorem isCompact_normPreservingLocus (n : ℕ) : IsCompact (normPreservingLocus n) := by
  apply (isCompact_closedBall (0 : Vector n →L[ℝ] Vector n) 1).of_isClosed_subset
    (isClosed_normPreservingLocus n)
  intro A hA
  simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_one A hA

/-- Forgetting the invertibility witness gives a homeomorphism to the closed locus. -/
noncomputable def homeomorph (n : ℕ) :
    OrthogonalOperators n ≃ₜ normPreservingLocus n where
  toFun a := ⟨a.1.1, a.2⟩
  invFun a := ⟨⟨a.1, normPreserving_isInvertible a.1 a.2⟩, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance compactSpace (n : ℕ) : CompactSpace (OrthogonalOperators n) := by
  have : CompactSpace (normPreservingLocus n) :=
    isCompact_iff_compactSpace.mp (isCompact_normPreservingLocus n)
  exact (homeomorph n).symm.compactSpace

theorem isClosedEmbedding_operator (n : ℕ) :
    Topology.IsClosedEmbedding (fun a : OrthogonalOperators n ↦ a.1.1) :=
  (continuous_subtype_val.comp continuous_subtype_val).isClosedEmbedding
    (fun _ _ h ↦ Subtype.ext (Subtype.ext h))

end NoExoticSixSphere.OrthogonalCompactness
