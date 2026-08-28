import Wikipedia.NoExoticSixSphere.SkewPolarNormalization

/-! # Local polar normalization of a self-adjoint element is an involution -/

noncomputable section

open scoped Ring

namespace Wikipedia.HomotopyGroupsOfSpheres.SelfAdjointPolarNormalization

open NoExoticSixSphere.NearIdentitySquare

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [NormedStarGroup A]

omit [CompleteSpace A] [NormedStarGroup A] in
theorem root_gram_commute (R : RootData A) {k : A}
    (hk : star k = k) (hdom : star k * k ∈ R.domain) :
    Commute (R.root (star k * k)) k := by
  apply R.commute hdom
  change (star k * k) * k = k * (star k * k)
  rw [hk, mul_assoc]

theorem normalize_selfAdjoint (R : RootData A) {k : A}
    (hk : star k = k) (hdom : star k * k ∈ R.domain) :
    star (normalize R k) = normalize R k := by
  have hs : IsSelfAdjoint (R.root (star k * k)) :=
    R.selfAdjoint hdom (IsSelfAdjoint.star_mul_self k)
  let s := R.root (star k * k)
  have hc : Commute s⁻¹ʳ k :=
    commute_ringInverse_of_isUnit (R.isUnit_root hdom) (root_gram_commute R hk hdom)
  change star (k * s⁻¹ʳ) = k * s⁻¹ʳ
  change IsSelfAdjoint s at hs
  rw [star_mul, hs.ringInverse.star_eq, hk, hc.eq]

omit [NormedStarGroup A] in
theorem normalize_square (R : RootData A) {k : A}
    (hk : star k = k) (hdom : star k * k ∈ R.domain) :
    normalize R k * normalize R k = 1 := by
  let s := R.root (star k * k)
  have hs : IsUnit s := R.isUnit_root hdom
  have hc : Commute s⁻¹ʳ k :=
    commute_ringInverse_of_isUnit hs (root_gram_commute R hk hdom)
  have hksq : k * k = s * s := by
    dsimp only [s]
    rw [R.square _ hdom, hk]
  have hcancel : (s * s) * (s⁻¹ʳ * s⁻¹ʳ) = 1 := by
    calc
      _ = s * (s * s⁻¹ʳ) * s⁻¹ʳ := by simp only [mul_assoc]
      _ = 1 := by rw [Ring.mul_inverse_cancel s hs, mul_one, Ring.mul_inverse_cancel s hs]
  change (k * s⁻¹ʳ) * (k * s⁻¹ʳ) = 1
  calc
    _ = k * (s⁻¹ʳ * k) * s⁻¹ʳ := by simp only [mul_assoc]
    _ = k * (k * s⁻¹ʳ) * s⁻¹ʳ := by rw [hc.eq]
    _ = (k * k) * (s⁻¹ʳ * s⁻¹ʳ) := by simp only [mul_assoc]
    _ = 1 := by rw [hksq, hcancel]

end Wikipedia.HomotopyGroupsOfSpheres.SelfAdjointPolarNormalization
