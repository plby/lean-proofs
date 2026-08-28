import Wikipedia.NoExoticSixSphere.ColumnCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Extracting the block of a fixed-column orthogonal operator

An orthogonal operator on the Euclidean product `ℝ ⊕ F` that fixes `(1, 0)`
is exactly the identity on the first factor plus an orthogonal operator on
`F`. Both extraction and extension are continuous in the operator norm.
-/

namespace NoExoticSixSphere.FixedColumnBlock

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev Space (F : Type*) := WithLp 2 (ℝ × F)

def firstVector : Space F := WithLp.toLp 2 ((1 : ℝ), (0 : F))

noncomputable def tailInclusion : F →L[ℝ] Space F :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ F).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ ℝ F)

theorem norm_tailInclusion (w : F) : ‖tailInclusion w‖ = ‖w‖ :=
  WithLp.norm_toLp_snd 2 ℝ F w

theorem inner_firstVector (z : Space F) : inner ℝ firstVector z = z.fst := by
  simp [firstVector, WithLp.prod_inner_apply]

theorem decompose (z : Space F) : z = z.fst • firstVector + tailInclusion z.snd := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [firstVector, tailInclusion]

variable (e : Space F ≃ₗᵢ[ℝ] Space F) (he : e firstVector = firstVector)

include he in
theorem fst_apply (z : Space F) : (e z).fst = z.fst := by
  have h := e.inner_map_map firstVector z
  rw [he] at h
  simpa only [inner_firstVector] using h

noncomputable def tailMap : F →L[ℝ] F :=
  (WithLp.sndL 2 ℝ ℝ F).comp (e.toContinuousLinearEquiv.toContinuousLinearMap.comp tailInclusion)

include he in
theorem apply_tailInclusion (w : F) : e (tailInclusion w) = tailInclusion (tailMap e w) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact fst_apply e he (tailInclusion w)
  · rfl

include he in
theorem tailMap_norm (w : F) : ‖tailMap e w‖ = ‖w‖ := by
  have h := e.norm_map (tailInclusion w)
  rw [apply_tailInclusion e he, norm_tailInclusion, norm_tailInclusion] at h
  exact h

noncomputable def tailIsometry : F →ₗᵢ[ℝ] F where
  toLinearMap := (tailMap e).toLinearMap
  norm_map' := tailMap_norm e he

noncomputable def tailEquiv [FiniteDimensional ℝ F] : F ≃ₗᵢ[ℝ] F :=
  LinearIsometryEquiv.ofSurjective (tailIsometry e he)
    (LinearMap.surjective_of_injective (tailIsometry e he).injective)

theorem tailEquiv_apply [FiniteDimensional ℝ F] (w : F) :
    tailEquiv e he w = tailMap e w := rfl

noncomputable def block (q : F ≃ₗᵢ[ℝ] F) : Space F ≃ₗᵢ[ℝ] Space F :=
  LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ) q

theorem block_apply (q : F ≃ₗᵢ[ℝ] F) (z : Space F) :
    block q z = WithLp.toLp 2 (z.fst, q z.snd) := rfl

theorem block_firstVector (q : F ≃ₗᵢ[ℝ] F) : block q firstVector = firstVector := by
  rw [block_apply]
  simp [firstVector]

theorem tailMap_block (q : F ≃ₗᵢ[ℝ] F) :
    tailMap (block q) = q.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem equiv_eq_block [FiniteDimensional ℝ F] : e = block (tailEquiv e he) := by
  apply LinearIsometryEquiv.ext
  intro z
  calc
    e z = e (z.fst • firstVector + tailInclusion z.snd) := congrArg e (decompose z)
    _ = z.fst • firstVector + tailInclusion (tailMap e z.snd) := by
      rw [map_add, map_smul, he, apply_tailInclusion e he]
    _ = block (tailEquiv e he) z := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp [firstVector, tailInclusion, block_apply, tailEquiv_apply]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_tailMap (a : X → Space F ≃ₗᵢ[ℝ] Space F)
    (ha : Continuous (fun x ↦ (a x).toContinuousLinearEquiv.toContinuousLinearMap)) :
    Continuous (fun x ↦ tailMap (a x)) :=
  continuous_const.clm_comp (ha.clm_comp continuous_const)

theorem continuous_block [FiniteDimensional ℝ F] (a : X → F ≃ₗᵢ[ℝ] F)
    (ha : Continuous (fun x ↦ (a x).toContinuousLinearEquiv.toContinuousLinearMap)) :
    Continuous (fun x ↦ (block (a x)).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro z
  have heq : (fun x ↦ (block (a x)).toContinuousLinearEquiv.toContinuousLinearMap z) =
      fun x ↦ WithLp.toLp 2 (z.fst, a x z.snd) := funext (fun x ↦ block_apply (a x) z)
  rw [heq]
  exact (WithLp.prod_continuous_toLp 2 ℝ F).comp
    (continuous_const.prodMk (ha.clm_apply continuous_const))

end NoExoticSixSphere.FixedColumnBlock
