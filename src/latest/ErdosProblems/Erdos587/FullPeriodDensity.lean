import ErdosProblems.Erdos587.SmoothedCounts

/-!
# Complete-period density for a smoothed quadratic count

Unit quadratic coefficients can be inverted before applying the uniform
affine root-density theorem.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_range_natCast_zmod {α : Type*} [AddCommMonoid α]
    (q : ℕ) [NeZero q] (f : ZMod q → α) :
    (∑ j ∈ Finset.range q, f (j : ZMod q)) = ∑ z : ZMod q, f z := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg f (Fin.cast_val_eq_self j)

lemma sum_range_shifted_natCast_zmod {α : Type*} [AddCommMonoid α]
    (q Z : ℕ) [NeZero q] (f : ZMod q → α) :
    (∑ j ∈ Finset.range q, f ((Z + j : ℕ) : ZMod q)) = ∑ z : ZMod q, f z := by
  simp only [Nat.cast_add]
  rw [sum_range_natCast_zmod q (fun z => f ((Z : ZMod q) + z))]
  exact Equiv.sum_comp (Equiv.addLeft (Z : ZMod q)) f

lemma squareRootCount_eq_of_natCast_eq {q m n : ℕ} [NeZero q]
    (h : (m : ZMod q) = (n : ZMod q)) : squareRootCount q m = squareRootCount q n := by
  simp only [squareRootCount_eq_card, h]

lemma unit_mul_square_eq_iff {q : ℕ} (u : (ZMod q)ˣ) (b z : ZMod q) :
    (u : ZMod q) * z ^ 2 = b ↔ z ^ 2 = (u⁻¹ : (ZMod q)ˣ) * b := by
  constructor
  · intro h
    have hh := congrArg (fun w : ZMod q => (u⁻¹ : (ZMod q)ˣ) * w) h
    simpa [← mul_assoc] using hh
  · intro h
    rw [h, ← mul_assoc, ← Units.val_mul]
    simp

lemma card_shifted_unit_quadratic_period (q Z : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (b : ZMod q) :
    ((Finset.range q).filter fun j =>
      (u : ZMod q) * (((Z + j : ℕ) : ZMod q) ^ 2) = b).card =
      squareRootCount q (((u⁻¹ : (ZMod q)ˣ) * b : ZMod q).val) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [sum_range_shifted_natCast_zmod q Z
    (fun z => if (u : ZMod q) * z ^ 2 = b then (1 : ℕ) else 0)]
  rw [squareRootCount_eq_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [ZMod.natCast_zmod_val, unit_mul_square_eq_iff]

lemma card_shifted_unit_quadratic_period_affine (q Z x : ℕ) [NeZero q]
    (u : (ZMod q)ˣ) (b : ZMod q) :
    ((Finset.range q).filter fun j =>
      (u : ZMod q) * (((Z + j : ℕ) : ZMod q) ^ 2) = b + x).card =
      squareRootCount q
        ((((u⁻¹ : (ZMod q)ˣ) * b : ZMod q).val) + ((u⁻¹ : (ZMod q)ˣ) : ZMod q).val * x) := by
  rw [card_shifted_unit_quadratic_period]
  apply squareRootCount_eq_of_natCast_eq
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  ring

lemma inverse_unit_val_coprime (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    (((u⁻¹ : (ZMod q)ˣ) : ZMod q).val).Coprime q := by
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rw [ZMod.natCast_zmod_val]
  exact Units.isUnit _

theorem exists_complete_unit_quadratic_interval_density :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q Z U : ℕ) [NeZero q], ∀ (u : (ZMod q)ˣ) (b : ZMod q),
        A * Real.sqrt q ≤ U →
        (U : ℝ) / (C * (1 + Real.log q) ^ O) ≤
          ∑ x ∈ Finset.range U,
            (((Finset.range q).filter fun j =>
              (u : ZMod q) * (((Z + j : ℕ) : ZMod q) ^ 2) = b + x).card : ℝ) := by
  obtain ⟨A, hA, C, hC, O, hO, hmean⟩ := exists_complete_root_density_bound
  refine ⟨A, hA, C, hC, O, hO, ?_⟩
  intro q Z U hq u b hU
  simp only [card_shifted_unit_quadratic_period_affine]
  exact hmean q _ _ U (Nat.pos_of_ne_zero (NeZero.ne q)) (inverse_unit_val_coprime q u) hU

lemma nvSmoothedRectangleCount_succ
    (q A B C X Z L U k : ℕ) [NeZero q] :
    nvSmoothedRectangleCount q A B C X Z L U (k + 1) =
      ∑ v : Fin k → Fin U, ∑ x : Fin U,
        ((Finset.range L).filter fun j =>
          ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
            (((X + ∑ i, (v i : ℕ)) + (x : ℕ) : ℕ) : ZMod q)).card := by
  classical
  let F : (Fin (k + 1) → Fin U) → ℕ := fun v =>
    ((Finset.range L).filter fun j =>
      ((A * (Z + j) ^ 2 + B * (Z + j) + C : ℕ) : ZMod q) =
        ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q)).card
  change (∑ v, F v) = _
  calc
    _ = ∑ w : Fin U × (Fin k → Fin U), F (Fin.cons w.1 w.2) :=
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Fin U)) F).symm
    _ = ∑ v : Fin k → Fin U, ∑ x : Fin U, F (Fin.cons x v) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro x hx
      have htarget : X + (∑ i : Fin (k + 1),
          ((Fin.cons (α := fun _ : Fin (k + 1) => Fin U) x v i : Fin U) : ℕ)) =
          (X + ∑ i : Fin k, (v i : ℕ)) + (x : ℕ) := by
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        omega
      dsimp only [F]
      rw [htarget]

lemma complete_unit_quadratic_count_tail_lower
    {A₀ C₀ : ℝ} {O q a C X Z U k : ℕ} [NeZero q]
    (hmean : ∀ (u : (ZMod q)ˣ) (b : ZMod q), A₀ * Real.sqrt q ≤ U →
      (U : ℝ) / (C₀ * (1 + Real.log q) ^ O) ≤
        ∑ x ∈ Finset.range U,
          (((Finset.range q).filter fun j =>
            (u : ZMod q) * (((Z + j : ℕ) : ZMod q) ^ 2) = b + x).card : ℝ))
    (ha : a.Coprime q) (hU : A₀ * Real.sqrt q ≤ U) (v : Fin k → Fin U) :
    (U : ℝ) / (C₀ * (1 + Real.log q) ^ O) ≤
      ∑ x : Fin U,
        (((Finset.range q).filter fun j =>
          ((a * (Z + j) ^ 2 + 0 * (Z + j) + C : ℕ) : ZMod q) =
            (((X + ∑ i, (v i : ℕ)) + (x : ℕ) : ℕ) : ZMod q)).card : ℝ) := by
  classical
  let u := ZMod.unitOfCoprime a ha
  let b : ZMod q := ((X + ∑ i, (v i : ℕ) : ℕ) : ZMod q) - C
  have hraw := hmean u b hU
  rw [← Fin.sum_univ_eq_sum_range] at hraw
  apply hraw.trans_eq
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  apply Finset.filter_congr
  intro j hj
  have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a ha
  dsimp only [b]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_zero, zero_mul, add_zero, hu]
  constructor <;> intro h <;> linear_combination h

theorem exists_smoothed_complete_period_density :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q a C X Z U k : ℕ) [NeZero q], a.Coprime q → A₀ * Real.sqrt q ≤ U →
        (U : ℝ) ^ (k + 1) / (C₀ * (1 + Real.log q) ^ O) ≤
          (nvSmoothedRectangleCount q a 0 C X Z q U (k + 1) : ℝ) := by
  obtain ⟨A₀, hA₀, C₀, hC₀, O, hO, hmean⟩ := exists_complete_unit_quadratic_interval_density
  refine ⟨A₀, hA₀, C₀, hC₀, O, hO, ?_⟩
  intro q a C X Z U k hq ha hU
  have hcount := congrArg (fun n : ℕ => (n : ℝ))
    (nvSmoothedRectangleCount_succ q a 0 C X Z q U k)
  simp only [Nat.cast_sum] at hcount
  calc
    _ = (U : ℝ) ^ k * ((U : ℝ) / (C₀ * (1 + Real.log q) ^ O)) := by
      rw [pow_succ]
      ring
    _ = ∑ _v : Fin k → Fin U, (U : ℝ) / (C₀ * (1 + Real.log q) ^ O) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
    _ ≤ ∑ v : Fin k → Fin U, ∑ x : Fin U,
        (((Finset.range q).filter fun j =>
          ((a * (Z + j) ^ 2 + 0 * (Z + j) + C : ℕ) : ZMod q) =
            (((X + ∑ i, (v i : ℕ)) + (x : ℕ) : ℕ) : ZMod q)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact complete_unit_quadratic_count_tail_lower (hmean q Z U) ha hU v
    _ = _ := hcount.symm

end Erdos587
