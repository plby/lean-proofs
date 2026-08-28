import Wikipedia.NoExoticSixSphere.HilbertSchmidtCalculus

/-!
# The actual skew-adjoint velocity of an orthogonal curve

Differentiating preservation of the inner product shows that `a⁻¹ a'` is
skew-adjoint. Multiplication by `a` recovers the ambient derivative, and the
Hilbert--Schmidt squared speed is unchanged.
-/

namespace NoExoticSixSphere.OrthogonalVelocity

open GLOrthonormalization OrthogonalPaths CayleyTransform HilbertSchmidt

variable {n : ℕ} (a : ℝ → OrthogonalOperators n) (A : Vector n →L[ℝ] Vector n) (t : ℝ)
  (h : HasDerivAt (fun r ↦ (a r).1.1) A t)

include h in
theorem derivative_inner_identity (u v : Vector n) :
    inner ℝ ((a t).1.1 u) (A v) + inner ℝ (A u) ((a t).1.1 v) = 0 := by
  have hd := (hasDerivAt_apply h u).inner ℝ (hasDerivAt_apply h v)
  have heq : (fun r : ℝ ↦ inner ℝ ((a r).1.1 u) ((a r).1.1 v)) =
      (fun _ : ℝ ↦ inner ℝ u v) := by
    funext r
    exact (toEquiv (a r)).inner_map_map u v
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const t (inner ℝ u v))

theorem reconstruct_apply (x : Vector n) :
    (a t).1.1 (((inverse (a t)).1.1.comp A) x) = A x :=
  self_apply_inverse (a t) (A x)

include h in
theorem velocity_inner_identity (u v : Vector n) :
    inner ℝ (((inverse (a t)).1.1.comp A) u) v +
      inner ℝ u (((inverse (a t)).1.1.comp A) v) = 0 := by
  have hleft : inner ℝ (((inverse (a t)).1.1.comp A) u) v =
      inner ℝ (A u) ((a t).1.1 v) := by
    rw [← (toEquiv (a t)).inner_map_map (((inverse (a t)).1.1.comp A) u) v]
    rw [toEquiv_apply, toEquiv_apply, reconstruct_apply]
  have hright : inner ℝ u (((inverse (a t)).1.1.comp A) v) =
      inner ℝ ((a t).1.1 u) (A v) := by
    rw [← (toEquiv (a t)).inner_map_map u (((inverse (a t)).1.1.comp A) v)]
    rw [toEquiv_apply, toEquiv_apply, reconstruct_apply]
  rw [hleft, hright, add_comm]
  exact derivative_inner_identity a A t h u v

include h in
theorem adjoint_velocity : ((inverse (a t)).1.1.comp A).adjoint =
    -((inverse (a t)).1.1.comp A) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (((inverse (a t)).1.1.comp A) u) v =
    inner ℝ u (-(((inverse (a t)).1.1.comp A) v))
  rw [inner_neg_right]
  linarith [velocity_inner_identity a A t h u v]

/-- The velocity is an element of the actual skew-adjoint model, not a formal symbol. -/
noncomputable def bodyVelocity : SkewOperators n :=
  ⟨(inverse (a t)).1.1.comp A, adjoint_velocity a A t h⟩

theorem bodyVelocity_reconstruct : (a t).1.1.comp
    (bodyVelocity a A t h : Vector n →L[ℝ] Vector n) = A := by
  apply ContinuousLinearMap.ext
  intro x
  exact reconstruct_apply a A t x

theorem squareNorm_bodyVelocity :
    squareNorm (bodyVelocity a A t h : Vector n →L[ℝ] Vector n) = squareNorm A :=
  squareNorm_left (inverse (a t)) A

end NoExoticSixSphere.OrthogonalVelocity
