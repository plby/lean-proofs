import Wikipedia.NoExoticSixSphere.LocalSquareRoot
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Normalization of a skew element by its local Gram square root

The inverse square root commutes with the skew element. Consequently their
product is still skew and its square is minus the identity.
-/

open scoped Ring

namespace NoExoticSixSphere.NearIdentitySquare

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem RootData.isUnit_root (R : RootData A) {a : A} (ha : a ∈ R.domain) :
    IsUnit (R.root a) := by
  have hn : ‖1 - R.root a‖ < 1 := by rw [norm_sub_rev]; exact R.near_one a ha
  simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn

omit [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem commute_ringInverse_of_isUnit {A : Type*} [MonoidWithZero A] {s k : A}
    (hs : IsUnit s) (h : Commute s k) : Commute s⁻¹ʳ k := by
  change s⁻¹ʳ * k = k * s⁻¹ʳ
  apply (Ring.inverse_mul_eq_iff_eq_mul s k (k * s⁻¹ʳ) hs).mpr
  rw [← mul_assoc, h.eq, Ring.mul_inverse_cancel_right s k hs]

variable [StarRing A] [NormedStarGroup A]

noncomputable def normalize (R : RootData A) (k : A) : A :=
  k * (R.root (star k * k))⁻¹ʳ

omit [CompleteSpace A] [NormedStarGroup A] in
theorem root_gram_commute (R : RootData A) {k : A}
    (hk : star k = -k) (hdom : star k * k ∈ R.domain) :
    Commute (R.root (star k * k)) k := by
  apply R.commute hdom
  change (star k * k) * k = k * (star k * k)
  rw [hk]
  noncomm_ring

theorem normalize_skew (R : RootData A) {k : A}
    (hk : star k = -k) (hdom : star k * k ∈ R.domain) :
    star (normalize R k) = -normalize R k := by
  have hs : IsSelfAdjoint (R.root (star k * k)) :=
    R.selfAdjoint hdom (IsSelfAdjoint.star_mul_self k)
  let s := R.root (star k * k)
  have hc : Commute s⁻¹ʳ k :=
    commute_ringInverse_of_isUnit (R.isUnit_root hdom) (root_gram_commute R hk hdom)
  change star (k * s⁻¹ʳ) = -(k * s⁻¹ʳ)
  change IsSelfAdjoint s at hs
  rw [star_mul, hs.ringInverse.star_eq, hk, mul_neg, hc.eq]

omit [NormedStarGroup A] in
theorem normalize_square (R : RootData A) {k : A}
    (hk : star k = -k) (hdom : star k * k ∈ R.domain) :
    normalize R k * normalize R k = -1 := by
  let s := R.root (star k * k)
  have hs : IsUnit s := R.isUnit_root hdom
  have hc : Commute s⁻¹ʳ k :=
    commute_ringInverse_of_isUnit hs (root_gram_commute R hk hdom)
  have hksq : k * k = -(s * s) := by
    dsimp only [s]
    rw [R.square _ hdom, hk, neg_mul, neg_neg]
  have hcancel : (s * s) * (s⁻¹ʳ * s⁻¹ʳ) = 1 := by
    calc
      _ = s * (s * s⁻¹ʳ) * s⁻¹ʳ := by simp only [mul_assoc]
      _ = 1 := by rw [Ring.mul_inverse_cancel s hs, mul_one, Ring.mul_inverse_cancel s hs]
  change (k * s⁻¹ʳ) * (k * s⁻¹ʳ) = -1
  calc
    _ = k * (s⁻¹ʳ * k) * s⁻¹ʳ := by simp only [mul_assoc]
    _ = k * (k * s⁻¹ʳ) * s⁻¹ʳ := by rw [hc.eq]
    _ = (k * k) * (s⁻¹ʳ * s⁻¹ʳ) := by simp only [mul_assoc]
    _ = -1 := by rw [hksq, neg_mul, hcancel]

omit [CompleteSpace A] [NormedStarGroup A] in
theorem normalize_of_gram_eq_one (R : RootData A) {k : A} (hk : star k * k = 1) :
    normalize R k = k := by
  rw [normalize, hk, R.root_one, Ring.inverse_one, mul_one]

end NoExoticSixSphere.NearIdentitySquare
