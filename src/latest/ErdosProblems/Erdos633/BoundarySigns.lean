import ErdosProblems.Erdos633.DirectionSigns
import ErdosProblems.Erdos633.OneTwentyRationality
import ErdosProblems.Erdos633.GroupOneRationality

/-!
# Boundary-sign equations and their six rationality consequences

`IntegerBoundarySigns` states the algebraic boundary identity. Its integer
coefficients are proved from finite signed tile sums below. It is not built
into the definition of `CongruentTiling`. The geometric extraction from actual
tilings, including arbitrary partial edge contacts, is proved in
`CharacterBoundary.lean`.
-/

namespace Erdos633

open scoped BigOperators

/-- Start with side AB in direction zero; turn at B and then at C. -/
noncomputable def signedTriangleBoundary (u v : ℤ) (πc B C : ℤ × ℤ)
    (X Y Z : ℝ) : ℝ :=
  Z + X * directionSign u v (πc - B) +
    Y * directionSign u v ((πc - B) + (πc - C))

/-- The algebraic boundary conclusion, kept separate from geometric tilings. -/
def IntegerBoundarySigns (a b c X Y Z : ℝ) (πc B C : ℤ × ℤ) : Prop :=
  ∀ u v : ℤ, directionSign u v πc = -1 → ∃ m : ℤ,
    signedTriangleBoundary u v πc B C X Y Z =
      m * (c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b)

/-- The integer-boundary property follows from finite tile contributions. -/
theorem integerBoundarySigns_of_tile_sum {ι : Type*} [Fintype ι]
    (a b c X Y Z : ℝ) (πc B C : ℤ × ℤ) (z : ι → ℤ × ℤ)
    (h : ∀ u v : ℤ, directionSign u v πc = -1 →
      signedTriangleBoundary u v πc B C X Y Z = ∑ i, directionSign u v (z i) *
        (c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b)) :
    IntegerBoundarySigns a b c X Y Z πc B C := by
  intro u v hπ
  exact directionSign_boundary_integer u v z _ _ (h u v hπ)

theorem oneTwenty_boundary_factors_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1) :
    0 < 1 + a - b ∧ 0 < 1 - a + b := by
  have hab := mul_pos ha hb
  have ha1 : a < 1 := by nlinarith only [hconic, hab, sq_nonneg b, ha]
  have hb1 : b < 1 := by nlinarith only [hconic, hab, sq_nonneg a, hb]
  constructor <;> linarith

theorem oneTwenty_W_boundary_counts (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * a) ℓ (ℓ * (a + b)) (3, 3) (1, 1) (1, 2)) :
    ∃ m n : ℤ, (m : ℝ) = ℓ * (1 - a) / b ∧ (n : ℝ) = ℓ * (1 + a) / b := by
  obtain ⟨m, hm⟩ := h 0 1 (by norm_num [directionSign])
  obtain ⟨n, hn⟩ := h 1 0 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm hn
  obtain ⟨hF, hG⟩ := oneTwenty_boundary_factors_pos a b ha hb hconic
  refine ⟨m, n, ?_, ?_⟩
  · apply (eq_div_iff (ne_of_gt hb)).mpr
    apply mul_right_cancel₀ (ne_of_gt hF)
    linear_combination -b * hm + ℓ * hconic
  · apply (eq_div_iff (ne_of_gt hb)).mpr
    apply mul_right_cancel₀ (ne_of_gt hG)
    linear_combination -b * hn + ℓ * hconic

theorem oneTwenty_Y_boundary_counts (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * a) (ℓ * (b * (2 * a + b)))
      (ℓ * (a + b)) (3, 3) (0, 2) (2, 1)) :
    ∃ m n : ℤ, (m : ℝ) = -ℓ * (1 - a) ∧ (n : ℝ) = ℓ * (1 + a) := by
  obtain ⟨m, hm⟩ := h 0 1 (by norm_num [directionSign])
  obtain ⟨n, hn⟩ := h 1 0 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm hn
  obtain ⟨hF, hG⟩ := oneTwenty_boundary_factors_pos a b ha hb hconic
  refine ⟨m, n, ?_, ?_⟩
  · apply mul_right_cancel₀ (ne_of_gt hF)
    linear_combination -hm - ℓ * hconic
  · apply mul_right_cancel₀ (ne_of_gt hG)
    linear_combination -hn + ℓ * hconic

theorem oneTwenty_Z_boundary_counts (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * (a * (a + 2 * b)))
      (ℓ * (b * (2 * a + b))) ℓ (3, 3) (0, 2) (1, 1)) :
    ∃ m n : ℤ, (m : ℝ) = -ℓ * (1 - a + b) ∧ (n : ℝ) = -ℓ * (1 + a - b) := by
  obtain ⟨m, hm⟩ := h 0 1 (by norm_num [directionSign])
  obtain ⟨n, hn⟩ := h 1 0 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm hn
  obtain ⟨hF, hG⟩ := oneTwenty_boundary_factors_pos a b ha hb hconic
  refine ⟨m, n, ?_, ?_⟩
  · apply mul_right_cancel₀ (ne_of_gt hF)
    linear_combination -hm - 2 * ℓ * hconic
  · apply mul_right_cancel₀ (ne_of_gt hG)
    linear_combination -hn - 2 * ℓ * hconic

theorem oneTwenty_U_two_boundary_counts (a b ℓ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 ℓ (ℓ * (a + 2 * b))
      (ℓ * (3 * b * (a + b))) (3, 3) (2, 0) (0, 3)) :
    ∃ m n : ℤ, (m : ℝ) = -ℓ * (2 * a + b - 1) ∧
      (n : ℝ) = ℓ * (2 * a + b + 1) := by
  obtain ⟨m, hm⟩ := h 0 1 (by norm_num [directionSign])
  obtain ⟨n, hn⟩ := h 1 0 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm hn
  obtain ⟨hF, hG⟩ := oneTwenty_boundary_factors_pos a b ha hb hconic
  refine ⟨m, n, ?_, ?_⟩
  · apply mul_right_cancel₀ (ne_of_gt hF)
    linear_combination -hm + 2 * ℓ * hconic
  · apply mul_right_cancel₀ (ne_of_gt hG)
    linear_combination -hn + 2 * ℓ * hconic

theorem groupOne_boundary_factors_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < 2 - s - s ^ 2 ∧ 0 < 2 + s - s ^ 2 := by
  have hg : 2 - s - s ^ 2 = (1 - s) * (2 + s) := by ring
  have hh : 2 + s - s ^ 2 = (1 + s) * (2 - s) := by ring
  rw [hg, hh]
  constructor <;> apply mul_pos <;> linarith

theorem groupOne_U_boundary_counts (s L : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (h : IntegerBoundarySigns s (1 - s ^ 2) 1 L (L * (2 - s ^ 2))
      (L * ((1 - s ^ 2) * (3 - s ^ 2))) (3, 2) (2, 0) (0, 2)) :
    ∃ m n : ℤ, (m : ℝ) = L * (2 + s - s ^ 2) ∧
      (n : ℝ) = L * (2 - s - s ^ 2) := by
  obtain ⟨m, hm⟩ := h 1 0 (by norm_num [directionSign])
  obtain ⟨n, hn⟩ := h 1 1 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm hn
  obtain ⟨hg, hh⟩ := groupOne_boundary_factors_pos s hs0 hs1
  refine ⟨m, n, ?_, ?_⟩
  · apply mul_right_cancel₀ (ne_of_gt hg)
    linear_combination -hm
  · apply mul_right_cancel₀ (ne_of_gt hh)
    linear_combination -hn

theorem groupOne_V_boundary_count (s L : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (h : IntegerBoundarySigns s (1 - s ^ 2) 1 (L * (s * (2 - s ^ 2)))
      (L * (1 - s ^ 2)) L (3, 2) (0, 1) (1, 1)) :
    ∃ m : ℤ, (m : ℝ) = L * s := by
  obtain ⟨m, hm⟩ := h 1 1 (by norm_num [directionSign])
  norm_num [signedTriangleBoundary, directionSign] at hm
  have hh := (groupOne_boundary_factors_pos s hs0 hs1).2
  refine ⟨m, ?_⟩
  apply mul_right_cancel₀ (ne_of_gt hh)
  linear_combination -hm

/-- The complete U algebraic argument, starting with boundary signs. -/
theorem groupOne_U_rational_of_boundary_signs (s L : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (h : IntegerBoundarySigns s (1 - s ^ 2) 1 L (L * (2 - s ^ 2))
      (L * ((1 - s ^ 2) * (3 - s ^ 2))) (3, 2) (2, 0) (0, 2))
    (N : ℕ) (harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) :
    s ∈ rationalReals ∧ L ∈ rationalReals := by
  obtain ⟨m, n, hm, hn⟩ := groupOne_U_boundary_counts s L hs0 hs1 h
  exact groupOne_U_rational s L hs0 hs1 hL m n hm hn N harea

theorem groupOne_V_rational_of_boundary_signs (s L : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (h : IntegerBoundarySigns s (1 - s ^ 2) 1 (L * (s * (2 - s ^ 2)))
      (L * (1 - s ^ 2)) L (3, 2) (0, 1) (1, 1))
    (N : ℕ) (harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2))
    (p q r : ℕ) (hr : 0 < r) (hedge : L = p * s + q * (1 - s ^ 2) + r) :
    s ∈ rationalReals ∧ L ∈ rationalReals := by
  obtain ⟨m, hm⟩ := groupOne_V_boundary_count s L hs0 hs1 h
  exact groupOne_V_rational s L hs0 hs1 hL m hm N harea p q r hr hedge

theorem oneTwenty_W_rational_of_boundary_signs (a b ℓ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * a) ℓ (ℓ * (a + b)) (3, 3) (1, 1) (1, 2))
    (p q r : ℕ) (hr : 0 < r) (hedge : ℓ * a = p * a + q * b + r) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨m, n, hm, hn⟩ := oneTwenty_W_boundary_counts a b ℓ ha hb hconic h
  exact oneTwenty_W_rational a b ℓ ha hb hℓ m n hm hn p q r hr hedge

theorem oneTwenty_Y_rational_of_boundary_signs (a b ℓ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * a) (ℓ * (b * (2 * a + b)))
      (ℓ * (a + b)) (3, 3) (0, 2) (2, 1))
    (N : ℕ) (harea : (N : ℝ) = ℓ ^ 2 * (a + b) * (2 * a + b)) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨m, n, hm, hn⟩ := oneTwenty_Y_boundary_counts a b ℓ ha hb hconic h
  exact oneTwenty_Y_rational a b ℓ ha hℓ hconic m n hm hn N harea

theorem oneTwenty_Z_rational_of_boundary_signs (a b ℓ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ) (hab : a ≠ b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 (ℓ * (a * (a + 2 * b)))
      (ℓ * (b * (2 * a + b))) ℓ (3, 3) (0, 2) (1, 1))
    (p q r u v w : ℕ)
    (hX : ℓ * a * (a + 2 * b) = p * a + q * b + r)
    (hY : ℓ * b * (2 * a + b) = u * a + v * b + w) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨m, n, hm, hn⟩ := oneTwenty_Z_boundary_counts a b ℓ ha hb hconic h
  exact oneTwenty_Z_rational a b ℓ hℓ hab hconic m n hm hn p q r u v w hX hY

theorem oneTwenty_U_two_rational_of_boundary_signs (a b ℓ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hℓ : 0 < ℓ)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (h : IntegerBoundarySigns a b 1 ℓ (ℓ * (a + 2 * b))
      (ℓ * (3 * b * (a + b))) (3, 3) (2, 0) (0, 3))
    (N : ℕ) (harea : (N : ℝ) = 3 * ℓ ^ 2 * (a + b) * (a + 2 * b)) :
    a ∈ rationalReals ∧ b ∈ rationalReals := by
  obtain ⟨m, n, hm, hn⟩ := oneTwenty_U_two_boundary_counts a b ℓ ha hb hconic h
  exact oneTwenty_U_two_rational a b ℓ ha hb hℓ hconic m n hm hn N harea

/-- A reptile boundary identity with nonzero factor forces a square count.
The boundary identity remains an explicit hypothesis of this finite lemma. -/
theorem square_count_of_signed_boundary {ι : Type*} [Fintype ι]
    (u v : ℤ) (z : ι → ℤ × ℤ) (L D : ℝ) (hL : 0 < L) (hD : D ≠ 0)
    (N : ℕ) (hN : L ^ 2 = N)
    (hboundary : L * D = ∑ i, directionSign u v (z i) * D) : IsSquare N := by
  obtain ⟨m, hm⟩ := directionSign_boundary_integer u v z (L * D) D hboundary
  have hLm : L = (m : ℝ) := mul_right_cancel₀ hD hm
  have hm0 : 0 ≤ m := by
    have h : (0 : ℝ) ≤ m := by rw [← hLm]; exact hL.le
    exact_mod_cast h
  have habs : (m.natAbs : ℝ) = (m : ℝ) := by
    have hz : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm0
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℝ)) hz
  refine ⟨m.natAbs, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [habs, ← hLm, ← pow_two, hN]

end Erdos633
