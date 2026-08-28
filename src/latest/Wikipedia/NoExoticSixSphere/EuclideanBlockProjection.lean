import Wikipedia.NoExoticSixSphere.EuclideanBlockInner

/-!
# Removing the added Euclidean coordinates

The coordinate projection is an actual continuous linear left inverse of
zero-coordinate stabilization. On the old ambient range, its reverse
composition is also the identity. Stabilization preserves the Euclidean norm.
-/

noncomputable section

namespace NoExoticSixSphere

open GLOrthonormalization

def oldProjection (N k : ℕ) : Vector (N + k) →L[ℝ] Vector N :=
  (ContinuousLinearMap.fst ℝ (Vector N) (Vector k)).comp
    (EuclideanSpace.finAddEquivProd (n := N) (m := k)).toContinuousLinearMap

theorem oldProjection_appendZeroMap (N k : ℕ) (v : Vector N) :
    oldProjection N k (appendZeroMap N k v) = v := by
  change (EuclideanSpace.finAddEquivProd
    ((EuclideanSpace.finAddEquivProd (n := N) (m := k)).symm (v, 0))).1 = v
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem appendZeroMap_oldProjection {N k : ℕ} {v : Vector (N + k)}
    (hv : v ∈ (appendZeroMap N k).range) : appendZeroMap N k (oldProjection N k v) = v := by
  obtain ⟨w, rfl⟩ := hv
  change appendZeroMap N k (oldProjection N k (appendZeroMap N k w)) = appendZeroMap N k w
  rw [oldProjection_appendZeroMap]

theorem norm_appendZeroMap (N k : ℕ) (v : Vector N) : ‖appendZeroMap N k v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_appendZeroMap N k v v

end NoExoticSixSphere
