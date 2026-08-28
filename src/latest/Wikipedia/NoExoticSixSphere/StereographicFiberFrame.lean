import Wikipedia.NoExoticSixSphere.StereographicFiberEquations

/-!
# The induced normal frame retains the original defining differential

The orthogonal right inverse of the actual stereographic equations gives
a smooth frame of the actual embedding's normal projection. Applying the
original equation differential to that frame is the explicit normal-model
coordinate equivalence. Its inverse gives the identity in the collapse data.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

def normalCoordinates (n k : ℕ) :
    EuclideanSpace ℝ (Fin (n + k - k)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
  rw [Nat.add_sub_cancel_right]

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n))
  (hf : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x))
  (a : Sphere (n + k)) (ha : f a = -b)

def equationFrame :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    SmoothRangeFrame (𝓡 k) (embedding f hf b hreg a ha).normalProjection
      (EuclideanSpace ℝ (Fin n)) := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  exact NormalFrameOfEquations.inducedFrame (contMDiff_inclusion f hf b hreg a ha)
    (fun x ↦ (contDiffOn_coordinates f hf b a).contDiffAt
      ((isOpen_neighborhood f hf b a).mem_nhds (inclusion_mem_neighborhood f b hreg a ha x)))
    (coordinates_inclusion f b a ha)
    (fun x ↦ surjective_fderiv_coordinates f hf b a
      (inclusion_mem_neighborhood f b hreg a ha x))
    (inclusion_differential_injective f hf b hreg a ha)
    (by
      simp only [finrank_euclideanSpace_fin]
      rfl)

def frame :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    SmoothRangeFrame (𝓡 k) (embedding f hf b hreg a ha).normalProjection
      (embedding f hf b hreg a ha).NormalModel := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  let A := equationFrame f hf b hreg a ha
  let Q : (embedding f hf b hreg a ha).NormalModel ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) := normalCoordinates n k
  refine ⟨fun x ↦ Q.trans (A.equiv x), ?_⟩
  change ContMDiff (𝓡 k) 𝓘(ℝ, (embedding f hf b hreg a ha).NormalModel →L[ℝ]
    EuclideanSpace ℝ (Fin (embedding f hf b hreg a ha).ambientDimension)) ∞
      (fun x ↦ (A.ambient x).comp Q.toContinuousLinearMap)
  exact A.contMDiff_ambient.clm_comp contMDiff_const

theorem frame_ambient (x : {x : Sphere (n + k) // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (frame f hf b hreg a ha).ambient x =
      (orthogonalRightInverse (fderiv ℝ (coordinates f b a) (inclusion f b a x))).comp
        (normalCoordinates n k).toContinuousLinearMap := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem fderiv_coordinates_frame (x : {x : Sphere (n + k) // f x = b})
    (v : EuclideanSpace ℝ (Fin (n + k - k))) :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    fderiv ℝ (coordinates f b a) (inclusion f b a x)
      ((frame f hf b hreg a ha).ambient x v) = normalCoordinates n k v := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  rw [frame_ambient]
  exact apply_orthogonalRightInverse _ (surjective_fderiv_coordinates f hf b a
    (inclusion_mem_neighborhood f b hreg a ha x)) (normalCoordinates n k v)

end NoExoticSixSphere.StereographicFiber
