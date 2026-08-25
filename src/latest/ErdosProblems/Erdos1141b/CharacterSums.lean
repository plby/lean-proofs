import Mathlib
import HasseWeil.HasseBound

/-!
# Quadratic character sums for Erdős 1141

The fourth moment in the `r = 2` Burgess argument reduces to character sums
of cubic and quartic polynomials. This file derives the cubic estimate from
the existing unconditional Hasse bound.
-/

open scoped BigOperators
open WeierstrassCurve

namespace Erdos1141b.CharacterSums

variable {F : Type*} [Field F]

/-- A monic cubic presented as a Weierstrass equation. -/
def cubicCurve (a b c : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := a, a₃ := 0, a₄ := b, a₆ := c }

lemma cubicCurve_equation (a b c x y : F) :
    (cubicCurve a b c).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c := by
  simp [Affine.equation_iff, cubicCurve]

variable [Fintype F] [DecidableEq F]

open Classical in
lemma card_cubic_fiber (hF : ringChar F ≠ 2) (a b c x : F) :
    (Fintype.card {y : F // (cubicCurve a b c).toAffine.Equation x y} : ℤ) =
      quadraticChar F (x ^ 3 + a * x ^ 2 + b * x + c) + 1 := by
  simpa [Fintype.card_subtype, cubicCurve_equation] using
    quadraticChar_card_sqrts hF (x ^ 3 + a * x ^ 2 + b * x + c)

/-- Hasse's bound in the character-sum form needed for Burgess's fourth moment. -/
theorem abs_sum_quadraticChar_cubic_le (hF : ringChar F ≠ 2) (a b c : F)
    [(cubicCurve a b c).IsElliptic] :
    |((∑ x : F, quadraticChar F (x ^ 3 + a * x ^ 2 + b * x + c) : ℤ) : ℝ)| ≤
      (2 * Real.sqrt (Fintype.card F : ℝ)) := by
  classical
  let W := cubicCurve a b c
  let e : W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Equation xy.1 xy.2} :=
    W.toAffine.pointEquiv
  let : Fintype W.toAffine.Point :=
    Fintype.ofEquiv (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}) e.symm
  have hcard : Fintype.card W.toAffine.Point =
      (∑ x : F, Fintype.card {y : F // W.toAffine.Equation x y}) + 1 := by
    rw [Fintype.card_congr e, Fintype.card_option]
    congr 1
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype W.toAffine.Equation),
      Fintype.card_sigma]
  have hcount : (HasseWeil.pointCount W.toAffine : ℤ) =
      (∑ x : F, quadraticChar F (x ^ 3 + a * x ^ 2 + b * x + c)) +
        Fintype.card F + 1 := by
    simp only [HasseWeil.pointCount, hcard, Nat.cast_add, Nat.cast_sum, Nat.cast_one]
    simp only [W, card_cubic_fiber hF, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hhasse := HasseWeil.WeilPairing.hasse_bound W
  have hcountR := congrArg (fun z : ℤ ↦ (z : ℝ)) hcount
  push_cast at hcountR
  rw [hcountR] at hhasse
  push_cast
  convert hhasse using 1
  congr 1
  ring

omit [Fintype F] [DecidableEq F] in
lemma cubicCurve_roots_discriminant (a b c : F) :
    (cubicCurve (-(a + b + c)) (a * b + a * c + b * c) (-(a * b * c))).Δ =
      16 * (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, cubicCurve]
  ring

/-- The cubic estimate for three distinct roots. -/
theorem abs_sum_quadraticChar_prod_three_of_distinct_le (hF : ringChar F ≠ 2)
    (a b c : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    |((∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  let W := cubicCurve (-(a + b + c)) (a * b + a * c + b * c) (-(a * b * c))
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h16 : (16 : F) ≠ 0 := by
    have heq : (16 : F) = 2 ^ 4 := by norm_num
    rw [heq]
    exact pow_ne_zero _ h2
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by
    rw [show W.Δ = _ from cubicCurve_roots_discriminant a b c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ (sub_ne_zero.mpr hab)))
      (pow_ne_zero _ (sub_ne_zero.mpr hac))) (pow_ne_zero _ (sub_ne_zero.mpr hbc)))⟩
  have h := abs_sum_quadraticChar_cubic_le hF (-(a + b + c))
    (a * b + a * c + b * c) (-(a * b * c))
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

lemma abs_quadraticChar_le_one (x : F) : |(quadraticChar F x : ℝ)| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  rcases quadraticChar_dichotomy hx with h | h <;> simp [h]

lemma sum_quadraticChar_sq_mul (a : F) (f : F → F) :
    (∑ x : F, quadraticChar F ((x - a) ^ 2 * f x)) =
      (∑ x : F, quadraticChar F (f x)) - quadraticChar F (f a) := by
  have h : ∀ x : F, quadraticChar F ((x - a) ^ 2 * f x) =
      quadraticChar F (f x) - if x = a then quadraticChar F (f a) else 0 := by
    intro x
    by_cases hx : x = a
    · simp [hx]
    rw [map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr hx)]
    simp [hx]
  simp_rw [h]
  simp [Finset.sum_sub_distrib]

lemma sum_quadraticChar_sub (hF : ringChar F ≠ 2) (a : F) :
    (∑ x : F, quadraticChar F (x - a)) = 0 := by
  exact ((Equiv.subRight a).sum_comp (quadraticChar F)).trans (quadraticChar_sum_zero hF)

lemma abs_sum_quadraticChar_sq_mul_sub_le (hF : ringChar F ≠ 2) (a b : F) :
    |((∑ x : F, quadraticChar F ((x - a) ^ 2 * (x - b)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  rw [sum_quadraticChar_sq_mul, sum_quadraticChar_sub hF]
  simp only [zero_sub, Int.cast_neg, abs_neg]
  have hcard : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) :=
    (Real.one_le_sqrt).mpr hcard
  exact (abs_quadraticChar_le_one (a - b)).trans (by linarith)

/-- The same cubic estimate also holds when roots coincide. -/
theorem abs_sum_quadraticChar_prod_three_le (hF : ringChar F ≠ 2) (a b c : F) :
    |((∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  by_cases hab : a = b
  · subst b
    simpa only [pow_two] using abs_sum_quadraticChar_sq_mul_sub_le hF a c
  by_cases hac : a = c
  · subst c
    have hpoly : ∀ x : F, (x - a) * (x - b) * (x - a) = (x - a) ^ 2 * (x - b) := by
      intro x; ring
    simp_rw [hpoly]
    exact abs_sum_quadraticChar_sq_mul_sub_le hF a b
  by_cases hbc : b = c
  · subst c
    have hpoly : ∀ x : F, (x - a) * (x - b) * (x - b) = (x - b) ^ 2 * (x - a) := by
      intro x; ring
    simp_rw [hpoly]
    exact abs_sum_quadraticChar_sq_mul_sub_le hF b a
  exact abs_sum_quadraticChar_prod_three_of_distinct_le hF a b c hab hac hbc

/-- Multiplying a split cubic by a nonzero constant leaves the estimate unchanged. -/
lemma abs_sum_quadraticChar_mul_prod_three_le (hF : ringChar F ≠ 2)
    (v a b c : F) (hv : v ≠ 0) :
    |((∑ x : F, quadraticChar F (v * ((x - a) * (x - b) * (x - c))) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  simp only [map_mul (quadraticChar F) v, ← Finset.mul_sum]
  rcases quadraticChar_dichotomy hv with h | h <;>
    simpa [h] using abs_sum_quadraticChar_prod_three_le hF a b c

lemma abs_sum_quadraticChar_three_linear_le (hF : ringChar F ≠ 2)
    (u v w : F) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    |((∑ x : F, quadraticChar F ((1 + u * x) * (1 + v * x) * (1 + w * x)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  have h := abs_sum_quadraticChar_mul_prod_three_le hF (u * v * w)
    (-u⁻¹) (-v⁻¹) (-w⁻¹) (mul_ne_zero (mul_ne_zero hu hv) hw)
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  field_simp
  ring

lemma quadraticChar_quartic_inv (a b c d t : F) :
    quadraticChar F (((a + t⁻¹) - a) * ((a + t⁻¹) - b) *
      ((a + t⁻¹) - c) * ((a + t⁻¹) - d)) =
    quadraticChar F ((1 + (a - b) * t) * (1 + (a - c) * t) * (1 + (a - d) * t)) -
      if t = 0 then 1 else 0 := by
  by_cases ht : t = 0
  · simp [ht]
  have hfac : ((a + t⁻¹) - a) * ((a + t⁻¹) - b) *
      ((a + t⁻¹) - c) * ((a + t⁻¹) - d) =
      (t⁻¹ ^ 2) ^ 2 *
        ((1 + (a - b) * t) * (1 + (a - c) * t) * (1 + (a - d) * t)) := by
    field_simp
    ring
  rw [hfac, map_mul, quadraticChar_sq_one' (pow_ne_zero _ (inv_ne_zero ht))]
  simp [ht]

/-- A quartic with a simple root; inversion accounts for the extra `1`. -/
theorem abs_sum_quadraticChar_prod_four_le (hF : ringChar F ≠ 2)
    (a b c d : F) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    |((∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) + 1 := by
  let f : F → ℤ := fun x ↦ quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d))
  let g : F → ℤ := fun t ↦
    quadraticChar F ((1 + (a - b) * t) * (1 + (a - c) * t) * (1 + (a - d) * t))
  have he : Function.Bijective (fun t : F ↦ a + t⁻¹) :=
    (Equiv.addLeft a).bijective.comp inv_bijective
  have hsum : ∑ x : F, f x = (∑ t : F, g t) - 1 := by
    rw [← he.sum_comp f]
    simp only [f, quadraticChar_quartic_inv, Finset.sum_sub_distrib]
    simp [g]
  have hg := abs_sum_quadraticChar_three_linear_le hF (a - b) (a - c) (a - d)
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac) (sub_ne_zero.mpr had)
  change |((∑ x : F, f x : ℤ) : ℝ)| ≤ _
  rw [hsum, Int.cast_sub, Int.cast_one]
  exact (abs_sub _ _).trans (by simpa [g] using add_le_add_right hg 1)

lemma four_has_simple_entry {α : Type*} (a b c d : α)
    (h : ¬ ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    (a ≠ b ∧ a ≠ c ∧ a ≠ d) ∨ (b ≠ a ∧ b ≠ c ∧ b ≠ d) ∨
      (c ≠ a ∧ c ≠ b ∧ c ≠ d) ∨ (d ≠ a ∧ d ≠ b ∧ d ≠ c) := by
  grind

theorem abs_sum_quadraticChar_prod_four_of_unpaired_le (hF : ringChar F ≠ 2)
    (a b c d : F)
    (h : ¬ ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    |((∑ x : F, quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) + 1 := by
  rcases four_has_simple_entry a b c d h with ha | hb | hc | hd
  · exact abs_sum_quadraticChar_prod_four_le hF a b c d ha.1 ha.2.1 ha.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_quadraticChar_prod_four_le hF b a c d hb.1 hb.2.1 hb.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_quadraticChar_prod_four_le hF c a b d hc.1 hc.2.1 hc.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_quadraticChar_prod_four_le hF d a b c hd.1 hd.2.1 hd.2.2

lemma sum_quadraticChar_prod_four_le_indicators (hF : ringChar F ≠ 2) (a b c d : F) :
    (∑ x : F, (quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)) ≤
      (if a = b ∧ c = d then (Fintype.card F : ℝ) else 0) +
      (if a = c ∧ b = d then (Fintype.card F : ℝ) else 0) +
      (if a = d ∧ b = c then (Fintype.card F : ℝ) else 0) +
      (2 * Real.sqrt (Fintype.card F : ℝ) + 1) := by
  have htriv :
      (∑ x : F, (quadraticChar F ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)) ≤
        Fintype.card F := by
    calc
      _ ≤ ∑ _x : F, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦
        (le_abs_self _).trans (abs_quadraticChar_le_one _)
      _ = _ := by simp
  have hC : 0 ≤ 2 * Real.sqrt (Fintype.card F : ℝ) + 1 := by positivity
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  split_ifs with h₁ h₂ h₃
  all_goals first
    | linarith
    | have hgood := abs_sum_quadraticChar_prod_four_of_unpaired_le hF a b c d (by tauto)
      push_cast at hgood
      simpa using (le_abs_self _).trans hgood

/-- A fourth-moment bound for distinct shifts over a finite field of odd characteristic. -/
theorem quadraticChar_fourth_moment_le {ι : Type*} [Fintype ι]
    (hF : ringChar F ≠ 2) (f : ι → F) (hf : Function.Injective f) :
    (∑ x : F, (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) ^ 4) ≤
      3 * (Fintype.card ι : ℝ) ^ 2 * Fintype.card F +
        (Fintype.card ι : ℝ) ^ 4 * (2 * Real.sqrt (Fintype.card F : ℝ) + 1) := by
  classical
  have hexpand : ∀ x : F,
      (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) ^ 4 =
        ∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι,
          (quadraticChar F ((x - f a) * (x - f b) * (x - f c) * (x - f d)) : ℝ) := by
    intro x
    rw [show (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) ^ 4 =
      (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) *
      (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) *
      (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) *
      (∑ i : ι, (quadraticChar F (x - f i) : ℝ)) by ring]
    simp only [Finset.mul_sum, map_mul, Int.cast_mul, mul_comm, mul_assoc]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι,
        ((if f a = f b ∧ f c = f d then (Fintype.card F : ℝ) else 0) +
         (if f a = f c ∧ f b = f d then (Fintype.card F : ℝ) else 0) +
         (if f a = f d ∧ f b = f c then (Fintype.card F : ℝ) else 0) +
         (2 * Real.sqrt (Fintype.card F : ℝ) + 1)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro d _
      exact sum_quadraticChar_prod_four_le_indicators hF (f a) (f b) (f c) (f d)
    _ = _ := by
      simp only [hf.eq_iff, ite_and, Finset.sum_add_distrib]
      simp [Finset.sum_ite_irrel, Finset.sum_const, nsmul_eq_mul]
      ring

end Erdos1141b.CharacterSums
