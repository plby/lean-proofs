import Mathlib

/-!
# A two-coordinate bound for rational linear forms on a Boolean cube

If two coefficients of a rational linear form are nonzero, then after all
other Boolean coordinates are fixed at least one of the four assignments to
these two coordinates makes the value different from both `0` and `1`.
Consequently at most three quarters of the Boolean cube can be mapped into
`{0, 1}`.  This file isolates the elementary counting argument.
-/

namespace Erdos543

/-- The rational value of a Boolean digit. -/
def boolRat (b : Bool) : ℚ := if b then 1 else 0

@[simp] theorem boolRat_false : boolRat false = 0 := rfl

@[simp] theorem boolRat_true : boolRat true = 1 := rfl

/-- Membership in the two-point target `{0, 1}`. -/
def IsZeroOrOne (x : ℚ) : Prop := x = 0 ∨ x = 1

instance (x : ℚ) : Decidable (IsZeroOrOne x) := by
  unfold IsZeroOrOne
  infer_instance

/-- Four values forming a nondegenerate affine parallelogram cannot all lie
in the two-point set `{0, 1}`. -/
theorem exists_rejected_boolean_pair (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ p : Bool × Bool,
      ¬ IsZeroOrOne (c + a * boolRat p.1 + b * boolRat p.2) := by
  by_contra h
  push Not at h
  have h00 := h (false, false)
  have h10 := h (true, false)
  have h01 := h (false, true)
  have h11 := h (true, true)
  simp only [IsZeroOrOne, boolRat_false, boolRat_true, mul_zero, mul_one,
    add_zero] at h00 h10 h01 h11
  rcases h00 with hc | hc
  · have ha1 : a = 1 := by
      rcases h10 with h10 | h10
      · exfalso
        apply ha
        linarith
      · linarith
    have hb1 : b = 1 := by
      rcases h01 with h01 | h01
      · exfalso
        apply hb
        linarith
      · linarith
    rcases h11 with h11 | h11 <;> linarith
  · have haNeg : a = -1 := by
      rcases h10 with h10 | h10
      · linarith
      · exfalso
        apply ha
        linarith
    have hbNeg : b = -1 := by
      rcases h01 with h01 | h01
      · linarith
      · exfalso
        apply hb
        linarith
    rcases h11 with h11 | h11 <;> linarith

/-- In one fiber, at most three of the four Boolean pairs are accepted by a
rational affine form having two nonzero coefficients. -/
theorem card_accepted_boolean_pairs_le_three (a b c : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fintype.card {p : Bool × Bool //
      IsZeroOrOne (c + a * boolRat p.1 + b * boolRat p.2)} ≤ 3 := by
  classical
  obtain ⟨p, hp⟩ := exists_rejected_boolean_pair a b c ha hb
  have hlt :
      Fintype.card {q : Bool × Bool //
        IsZeroOrOne (c + a * boolRat q.1 + b * boolRat q.2)} <
        Fintype.card (Bool × Bool) :=
    Fintype.card_subtype_lt hp
  norm_num [Fintype.card_prod, Fintype.card_bool] at hlt ⊢
  omega

/-- Fiberwise form of the three-quarters bound.  The type `γ` records all
Boolean coordinates other than the two distinguished ones. -/
theorem card_two_bit_affine_accepted_le [Fintype γ]
    (a b : ℚ) (offset : γ → ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fintype.card {x : γ × (Bool × Bool) //
      IsZeroOrOne (offset x.1 + a * boolRat x.2.1 + b * boolRat x.2.2)} ≤
      3 * Fintype.card γ := by
  classical
  let P : γ → Bool × Bool → Prop := fun r p ↦
    IsZeroOrOne (offset r + a * boolRat p.1 + b * boolRat p.2)
  calc
    Fintype.card {x : γ × (Bool × Bool) // P x.1 x.2} =
        Fintype.card (Σ r : γ, {p : Bool × Bool // P r p}) :=
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype P)
    _ = ∑ r : γ, Fintype.card {p : Bool × Bool // P r p} :=
      Fintype.card_sigma
    _ ≤ ∑ _r : γ, 3 := by
      exact Finset.sum_le_sum fun r _ ↦
        card_accepted_boolean_pairs_le_three a b (offset r) ha hb
    _ = 3 * Fintype.card γ := by simp [Nat.mul_comm]

/-- The normalized `(n + 2)`-dimensional Boolean-cube form of the bound. -/
theorem card_normalized_linear_form_le_three_mul_pow (n : ℕ)
    (a b : ℚ) (offset : (Fin n → Bool) → ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fintype.card {x : (Fin n → Bool) × (Bool × Bool) //
      IsZeroOrOne (offset x.1 + a * boolRat x.2.1 + b * boolRat x.2.2)} ≤
      3 * 2 ^ n := by
  simpa [Fintype.card_fun, Fintype.card_bool] using
    card_two_bit_affine_accepted_le a b offset ha hb

/-- The three-quarters bound transported across an arbitrary equivalence that
splits a finite sample space into the remaining coordinates and two bits.
This is the convenient form for reindexing columns of an incidence matrix. -/
theorem card_accepted_of_equiv_two_bits [Fintype Ω] [Fintype γ]
    (e : Ω ≃ γ × (Bool × Bool)) (L : Ω → ℚ) (offset : γ → ℚ)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hL : ∀ x, L x =
      offset (e x).1 + a * boolRat (e x).2.1 + b * boolRat (e x).2.2) :
    Fintype.card {x : Ω // IsZeroOrOne (L x)} ≤ 3 * Fintype.card γ := by
  classical
  calc
    Fintype.card {x : Ω // IsZeroOrOne (L x)} =
        Fintype.card {y : γ × (Bool × Bool) //
          IsZeroOrOne (offset y.1 + a * boolRat y.2.1 + b * boolRat y.2.2)} := by
      apply Fintype.card_congr
      exact e.subtypeEquiv fun x ↦ by rw [hL x]
    _ ≤ 3 * Fintype.card γ :=
      card_two_bit_affine_accepted_le a b offset ha hb

/-- Any finite intersection contained in one accepted affine constraint has
the same three-quarters upper bound.  In applications, `S` can be the
intersection of the Boolean cube with a rational affine subspace. -/
theorem card_constraint_intersection_le [Fintype Ω] [Fintype γ]
    (e : Ω ≃ γ × (Bool × Bool)) (L : Ω → ℚ) (offset : γ → ℚ)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hL : ∀ x, L x =
      offset (e x).1 + a * boolRat (e x).2.1 + b * boolRat (e x).2.2)
    (S : Ω → Prop) [DecidablePred S]
    (hS : ∀ x, S x → IsZeroOrOne (L x)) :
    Fintype.card {x : Ω // S x} ≤ 3 * Fintype.card γ := by
  let inclusion : {x : Ω // S x} ↪ {x : Ω // IsZeroOrOne (L x)} :=
    ⟨fun x ↦ ⟨x, hS x x.property⟩, fun x y h ↦ Subtype.ext <|
      congrArg (fun z : {x : Ω // IsZeroOrOne (L x)} ↦ (z : Ω)) h⟩
  exact (Fintype.card_le_of_embedding inclusion).trans
    (card_accepted_of_equiv_two_bits e L offset a b ha hb hL)

/-- The normalized rational linear form with two distinguished coefficients. -/
def normalizedLinearForm {n : ℕ} (coeff : Fin n → ℚ) (a b : ℚ)
    (x : (Fin n → Bool) × (Bool × Bool)) : ℚ :=
  (∑ i, coeff i * boolRat (x.1 i)) +
    a * boolRat x.2.1 + b * boolRat x.2.2

/-- A rational linear form with two nonzero distinguished coefficients takes
values in `{0, 1}` on at most `3 * 2^n` points of the `(n + 2)`-cube. -/
theorem card_normalized_linear_form_zero_or_one_le (n : ℕ)
    (coeff : Fin n → ℚ) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fintype.card {x : (Fin n → Bool) × (Bool × Bool) //
      IsZeroOrOne (normalizedLinearForm coeff a b x)} ≤ 3 * 2 ^ n := by
  apply card_normalized_linear_form_le_three_mul_pow n a b
    (fun r ↦ ∑ i, coeff i * boolRat (r i)) ha hb

end Erdos543
