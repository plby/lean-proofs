import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- The determinant formed by two gap starts and the positions at which two
moduli witness them. -/
def shiftedPairDet
    (n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ : ℕ) : ℤ :=
  ((n₁ + u₁₁ : ℕ) : ℤ) * ((n₂ + u₂₂ : ℕ) : ℤ) -
    ((n₁ + u₁₂ : ℕ) : ℤ) * ((n₂ + u₂₁ : ℕ) : ℤ)

/-- If modulus `a` divides the first covered number in both gaps and modulus
`b` divides the second covered number in both gaps, then `a*b` divides the
corresponding two-by-two determinant. -/
theorem int_mul_dvd_shiftedPairDet
    (a b n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ : ℕ)
    (ha₁ : a ∣ n₁ + u₁₁) (ha₂ : a ∣ n₂ + u₂₁)
    (hb₁ : b ∣ n₁ + u₁₂) (hb₂ : b ∣ n₂ + u₂₂) :
    ((a * b : ℕ) : ℤ) ∣ shiftedPairDet n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ := by
  rcases ha₁ with ⟨ka₁, hka₁⟩
  rcases ha₂ with ⟨ka₂, hka₂⟩
  rcases hb₁ with ⟨kb₁, hkb₁⟩
  rcases hb₂ with ⟨kb₂, hkb₂⟩
  refine ⟨(ka₁ : ℤ) * (kb₂ : ℤ) - (kb₁ : ℤ) * (ka₂ : ℤ), ?_⟩
  have hka₁z : (n₁ : ℤ) + (u₁₁ : ℤ) = (a : ℤ) * (ka₁ : ℤ) := by
    exact_mod_cast hka₁
  have hka₂z : (n₂ : ℤ) + (u₂₁ : ℤ) = (a : ℤ) * (ka₂ : ℤ) := by
    exact_mod_cast hka₂
  have hkb₁z : (n₁ : ℤ) + (u₁₂ : ℤ) = (b : ℤ) * (kb₁ : ℤ) := by
    exact_mod_cast hkb₁
  have hkb₂z : (n₂ : ℤ) + (u₂₂ : ℤ) = (b : ℤ) * (kb₂ : ℤ) := by
    exact_mod_cast hkb₂
  dsimp [shiftedPairDet]
  push_cast
  rw [hka₁z, hka₂z, hkb₁z, hkb₂z]
  push_cast
  ring

/-- Subtracting the first column cancels the two large gap starts.  Thus a
shifted two-by-two determinant is only `O(XG)`, not `O(X²)`. -/
theorem abs_shifted_det_le
    (n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ X G : ℝ)
    (hn₁0 : 0 ≤ n₁) (hn₂0 : 0 ≤ n₂)
    (hu₁₁0 : 0 ≤ u₁₁) (hu₁₂0 : 0 ≤ u₁₂)
    (hu₂₁0 : 0 ≤ u₂₁) (hu₂₂0 : 0 ≤ u₂₂)
    (hn₁X : n₁ ≤ X) (hn₂X : n₂ ≤ X)
    (hu₁₁G : u₁₁ ≤ G) (hu₁₂G : u₁₂ ≤ G)
    (hu₂₁G : u₂₁ ≤ G) (hu₂₂G : u₂₂ ≤ G) :
    |(n₁ + u₁₁) * (n₂ + u₂₂) -
      (n₁ + u₁₂) * (n₂ + u₂₁)| ≤ 2 * X * G + G ^ 2 := by
  have hX0 : 0 ≤ X := le_trans hn₁0 hn₁X
  have hG0 : 0 ≤ G := le_trans hu₁₁0 hu₁₁G
  have h11 : n₁ * u₂₂ ≤ X * G :=
    mul_le_mul hn₁X hu₂₂G hu₂₂0 hX0
  have h12 : n₁ * u₂₁ ≤ X * G :=
    mul_le_mul hn₁X hu₂₁G hu₂₁0 hX0
  have h21 : n₂ * u₁₁ ≤ X * G :=
    mul_le_mul hn₂X hu₁₁G hu₁₁0 hX0
  have h22 : n₂ * u₁₂ ≤ X * G :=
    mul_le_mul hn₂X hu₁₂G hu₁₂0 hX0
  have huA : u₁₁ * u₂₂ ≤ G ^ 2 := by
    nlinarith [mul_le_mul hu₁₁G hu₂₂G hu₂₂0 hG0]
  have huB : u₁₂ * u₂₁ ≤ G ^ 2 := by
    nlinarith [mul_le_mul hu₁₂G hu₂₁G hu₂₁0 hG0]
  rw [abs_le]
  constructor <;> nlinarith

/-- Consequently, if `a*b` exceeds `2XG+G²`, two repeated compatible witness
columns must be exactly proportional: their determinant vanishes. -/
theorem shiftedPairDet_eq_zero_of_product_large
    (a b n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ X G : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hn₁X : n₁ ≤ X) (hn₂X : n₂ ≤ X)
    (hu₁₁G : u₁₁ ≤ G) (hu₁₂G : u₁₂ ≤ G)
    (hu₂₁G : u₂₁ ≤ G) (hu₂₂G : u₂₂ ≤ G)
    (ha₁ : a ∣ n₁ + u₁₁) (ha₂ : a ∣ n₂ + u₂₁)
    (hb₁ : b ∣ n₁ + u₁₂) (hb₂ : b ∣ n₂ + u₂₂)
    (hlarge : 2 * X * G + G ^ 2 < a * b) :
    shiftedPairDet n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂ = 0 := by
  let d := shiftedPairDet n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂
  have hdvd : ((a * b : ℕ) : ℤ) ∣ d :=
    int_mul_dvd_shiftedPairDet a b n₁ n₂ u₁₁ u₁₂ u₂₁ u₂₂
      ha₁ ha₂ hb₁ hb₂
  have hbound : |(d : ℝ)| ≤ (2 * X * G + G ^ 2 : ℕ) := by
    dsimp [d, shiftedPairDet]
    push_cast
    exact abs_shifted_det_le
      (n₁ : ℝ) (n₂ : ℝ) (u₁₁ : ℝ) (u₁₂ : ℝ)
      (u₂₁ : ℝ) (u₂₂ : ℝ) (X : ℝ) (G : ℝ)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity)
      (by exact_mod_cast hn₁X) (by exact_mod_cast hn₂X)
      (by exact_mod_cast hu₁₁G) (by exact_mod_cast hu₁₂G)
      (by exact_mod_cast hu₂₁G) (by exact_mod_cast hu₂₂G)
  by_contra hd0
  have hnatpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
  have hnatdvd : a * b ∣ d.natAbs := by
    rw [← Int.natAbs_cast (a * b), Int.natAbs_dvd_natAbs]
    exact hdvd
  have hab_le : a * b ≤ d.natAbs := Nat.le_of_dvd hnatpos hnatdvd
  have hab_real : ((a * b : ℕ) : ℝ) ≤ |(d : ℝ)| := by
    calc
      ((a * b : ℕ) : ℝ) ≤ (d.natAbs : ℝ) := by exact_mod_cast hab_le
      _ = |(d : ℝ)| := by norm_num
  have hlarge_real : ((2 * X * G + G ^ 2 : ℕ) : ℝ) < (a * b : ℕ) := by
    exact_mod_cast hlarge
  linarith

end Erdos489
