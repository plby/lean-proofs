import Wikipedia.NoExoticSixSphere.FixedColumnBlock

/-!
# Splitting a fixed column of a rectangular linear isometry

A linear isometry `ℝ ⊕ E → ℝ ⊕ F` fixing the first unit vector is precisely
the identity on that line plus a linear isometry `E → F`. No surjectivity is
assumed. These explicit operator maps will identify fibers of partial-frame
column projections.
-/

noncomputable section

namespace NoExoticSixSphere.RectangularColumnBlock

open FixedColumnBlock

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (a : Space E →ₗᵢ[ℝ] Space F) (ha : a firstVector = firstVector)

include ha in
theorem fst_apply (z : Space E) : (a z).fst = z.fst := by
  have h := a.inner_map_map firstVector z
  rw [ha] at h
  simpa only [inner_firstVector] using h

def tailMap : E →L[ℝ] F :=
  (WithLp.sndL 2 ℝ ℝ F).comp (a.toContinuousLinearMap.comp tailInclusion)

include ha in
theorem apply_tailInclusion (x : E) :
    a (tailInclusion x) = tailInclusion (tailMap a x) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact fst_apply a ha (tailInclusion x)
  · rfl

include ha in
theorem tailMap_norm (x : E) : ‖tailMap a x‖ = ‖x‖ := by
  have h := a.norm_map (tailInclusion x)
  rw [apply_tailInclusion a ha, norm_tailInclusion, norm_tailInclusion] at h
  exact h

def tailIsometry : E →ₗᵢ[ℝ] F where
  toLinearMap := (tailMap a).toLinearMap
  norm_map' := tailMap_norm a ha

def block (q : E →ₗᵢ[ℝ] F) : Space E →ₗᵢ[ℝ] Space F :=
  (LinearIsometryEquiv.refl ℝ ℝ).toLinearIsometry.withLpProdMap 2 q

@[simp] theorem block_apply (q : E →ₗᵢ[ℝ] F) (z : Space E) :
    block q z = WithLp.toLp 2 (z.fst, q z.snd) := rfl

@[simp] theorem block_firstVector (q : E →ₗᵢ[ℝ] F) :
    block q firstVector = firstVector := by
  rw [block_apply]
  simp [firstVector]

theorem tailMap_block (q : E →ₗᵢ[ℝ] F) : tailMap (block q) = q.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem isometry_eq_block : a = block (tailIsometry a ha) := by
  apply LinearIsometry.ext
  intro z
  calc
    a z = a (z.fst • firstVector + tailInclusion z.snd) := congrArg a (decompose z)
    _ = z.fst • firstVector + tailInclusion (tailMap a z.snd) := by
      rw [map_add, map_smul, ha, apply_tailInclusion a ha]
    _ = block (tailIsometry a ha) z := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> simp [firstVector, tailInclusion, tailIsometry]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_tailMap (a : X → Space E →ₗᵢ[ℝ] Space F)
    (ha : Continuous (fun x ↦ (a x).toContinuousLinearMap)) :
    Continuous (fun x ↦ tailMap (a x)) :=
  continuous_const.clm_comp (ha.clm_comp continuous_const)

theorem continuous_block [FiniteDimensional ℝ E] (a : X → E →ₗᵢ[ℝ] F)
    (ha : Continuous (fun x ↦ (a x).toContinuousLinearMap)) :
    Continuous (fun x ↦ (block (a x)).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro z
  have he : (fun x ↦ (block (a x)).toContinuousLinearMap z) =
      fun x ↦ WithLp.toLp 2 (z.fst, a x z.snd) := rfl
  rw [he]
  exact (WithLp.prod_continuous_toLp 2 ℝ F).comp
    (continuous_const.prodMk (ha.clm_apply continuous_const))

end NoExoticSixSphere.RectangularColumnBlock
