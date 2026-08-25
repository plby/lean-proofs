import ErdosProblems.Erdos157.PolynomialCharacters
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Finite character orthogonality and a uniform fiber-count estimate. -/

namespace Erdos157.Elementary.PolynomialCharacters

variable {R : Type*} [CommMonoid R] [Finite R]

noncomputable instance complexCharacterFintype : Fintype (MulChar R ℂ) :=
  Fintype.ofFinite _

instance complexExponentCastNeZero :
    NeZero ((Monoid.exponent Rˣ : ℕ) : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩

theorem complexCharacter_card : Fintype.card (MulChar R ℂ) = Nat.card Rˣ := by
  rw [← Nat.card_eq_fintype_card]
  exact MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

theorem sum_characters_eq_zero {x : R} (hx : x ≠ 1) :
    ∑ χ : MulChar R ℂ, χ x = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ hx
  refine eq_zero_of_mul_eq_self_left hχ₀ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ₀) _ _ (fun _ => rfl)

theorem sum_characters [DecidableEq R] (x : R) :
    ∑ χ : MulChar R ℂ, χ x = if x = 1 then (Nat.card Rˣ : ℂ) else 0 := by
  classical
  split_ifs with hx
  · subst x
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      complexCharacter_card]
  · exact sum_characters_eq_zero hx

omit [Finite R] in
theorem unit_ratio_eq_one_iff (x : R) (u : Rˣ) :
    (↑u⁻¹ : R) * x = 1 ↔ x = ↑u := by
  constructor
  · intro h
    have hm := congrArg (fun y : R => (u : R) * y) h
    simpa only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      mul_one] using hm
  · rintro rfl
    exact u.inv_mul

/-- Fourier inversion for the fiber of any finite family over a unit. -/
theorem character_fiber_identity {A : Type*} [Fintype A] (x : A → R) (u : Rˣ) :
    ∑ χ : MulChar R ℂ, χ (↑u⁻¹ : R) * ∑ a, χ (x a) =
      (Nat.card Rˣ : ℂ) * (Nat.card {a // x a = ↑u} : ℂ) := by
  classical
  simp_rw [Finset.mul_sum, ← map_mul]
  rw [Finset.sum_comm]
  simp_rw [sum_characters, unit_ratio_eq_one_iff]
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun a => x a = ↑u) _ (by simp)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [mul_comm]

/-- A bound for all nonprincipal character sums controls every unit fiber. -/
theorem character_fiber_error_le {A : Type*} [Fintype A] (x : A → R)
    (hx : ∀ a, IsUnit (x a)) (u : Rˣ) (c E : ℝ) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (hbound : ∀ χ : MulChar R ℂ, χ ≠ 1 → c * ‖∑ a, χ (x a)‖ ≤ E) :
    |c * ((Nat.card Rˣ : ℝ) * Nat.card {a // x a = ↑u} - Fintype.card A)| ≤
      (Nat.card Rˣ : ℝ) * E := by
  classical
  let F : MulChar R ℂ → ℂ := fun χ => χ (↑u⁻¹ : R) * ∑ a, χ (x a)
  let S : Finset (MulChar R ℂ) := Finset.univ.erase 1
  have hprincipal : F 1 = Fintype.card A := by
    simp only [F, MulChar.one_apply_coe, one_mul]
    simp only [MulChar.one_apply (hx _), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hsum : (∑ χ ∈ S, F χ) =
      (Nat.card Rˣ : ℂ) * Nat.card {a // x a = ↑u} - Fintype.card A := by
    have h := Finset.sum_erase_add Finset.univ F (Finset.mem_univ (1 : MulChar R ℂ))
    rw [hprincipal, character_fiber_identity x u] at h
    exact eq_sub_of_add_eq h
  have hterm : ∀ χ ∈ S, c * ‖F χ‖ ≤ E := by
    intro χ hχ
    have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    calc
      _ = c * (‖χ (↑u⁻¹ : R)‖ * ‖∑ a, χ (x a)‖) := by
        change c * ‖χ (↑u⁻¹ : R) * ∑ a, χ (x a)‖ = _
        rw [norm_mul]
      _ ≤ c * ‖∑ a, χ (x a)‖ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (character_norm_le_one χ _)) hc
      _ ≤ E := hbound χ hne
  have hnorm : c * ‖∑ χ ∈ S, F χ‖ ≤ (Nat.card Rˣ : ℝ) * E := by
    calc
      _ ≤ c * ∑ χ ∈ S, ‖F χ‖ := mul_le_mul_of_nonneg_left (norm_sum_le S F) hc
      _ = ∑ χ ∈ S, c * ‖F χ‖ := Finset.mul_sum ..
      _ ≤ ∑ _χ ∈ S, E := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * E := by simp
      _ ≤ (Fintype.card (MulChar R ℂ) : ℝ) * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        exact_mod_cast Finset.card_le_card (Finset.erase_subset (1 : MulChar R ℂ) Finset.univ)
      _ = _ := by rw [complexCharacter_card]
  rw [hsum] at hnorm
  have hcast : (Nat.card Rˣ : ℂ) * Nat.card {a // x a = ↑u} - Fintype.card A =
      (((Nat.card Rˣ : ℝ) * Nat.card {a // x a = ↑u} - Fintype.card A : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  simpa only [abs_mul, abs_of_nonneg hc] using hnorm

end Erdos157.Elementary.PolynomialCharacters
