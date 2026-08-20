import Mathlib

/-!
# A finite simultaneous Dirichlet approximation lemma

This file contains the pigeonhole argument used in the proof of Erdős
Problem 485.  The strict inequality comes from using half-open boxes: two
fractional parts in the same box differ by *strictly* less than its width.
-/

namespace Erdos485

open scoped BigOperators

noncomputable section

private def dirichletBox {E : Type*} (alpha : E → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (r : ℕ) (e : E) : Fin Q :=
  ⟨⌊Int.fract ((r : ℝ) * alpha e) * Q⌋₊, by
    rw [Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _))]
    have hfract := Int.fract_lt_one ((r : ℝ) * alpha e)
    have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    nlinarith⟩

private lemma abs_fract_sub_lt_inv_of_box_eq {E : Type*} (alpha : E → ℝ)
    (Q : ℕ) (hQ : 0 < Q) {a b : ℕ} {e : E}
    (hbox : dirichletBox alpha Q hQ a e = dirichletBox alpha Q hQ b e) :
    |Int.fract ((b : ℝ) * alpha e) - Int.fract ((a : ℝ) * alpha e)| < (1 : ℝ) / Q := by
  have hfloor :
      ⌊Int.fract ((a : ℝ) * alpha e) * Q⌋₊ =
        ⌊Int.fract ((b : ℝ) * alpha e) * Q⌋₊ :=
    congrArg Fin.val hbox
  have ha0 : 0 ≤ Int.fract ((a : ℝ) * alpha e) * (Q : ℝ) :=
    mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _)
  have hb0 : 0 ≤ Int.fract ((b : ℝ) * alpha e) * (Q : ℝ) :=
    mul_nonneg (Int.fract_nonneg _) (Nat.cast_nonneg _)
  have haL :
      (⌊Int.fract ((a : ℝ) * alpha e) * Q⌋₊ : ℝ) ≤
        Int.fract ((a : ℝ) * alpha e) * Q :=
    Nat.floor_le ha0
  have hbL :
      (⌊Int.fract ((b : ℝ) * alpha e) * Q⌋₊ : ℝ) ≤
        Int.fract ((b : ℝ) * alpha e) * Q :=
    Nat.floor_le hb0
  have haU :
      Int.fract ((a : ℝ) * alpha e) * Q <
        (⌊Int.fract ((a : ℝ) * alpha e) * Q⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((a : ℝ) * alpha e) * Q)
  have hbU :
      Int.fract ((b : ℝ) * alpha e) * Q <
        (⌊Int.fract ((b : ℝ) * alpha e) * Q⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((b : ℝ) * alpha e) * Q)
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hab :
      Int.fract ((a : ℝ) * alpha e) - Int.fract ((b : ℝ) * alpha e) <
        (1 : ℝ) / Q := by
    apply (lt_div_iff₀ hQr).2
    rw [← hfloor] at hbL hbU
    nlinarith
  have hba :
      Int.fract ((b : ℝ) * alpha e) - Int.fract ((a : ℝ) * alpha e) <
        (1 : ℝ) / Q := by
    apply (lt_div_iff₀ hQr).2
    rw [hfloor] at haL haU
    nlinarith
  exact abs_lt.mpr ⟨by linarith, hba⟩

/-- The multiplicative-error form of simultaneous Dirichlet approximation.

For a positive integer `Q` and a finite family `alpha`, there is a positive
integer `q ≤ Q ^ |E|` such that every `q * alpha e` is strictly within
`1 / Q` of an integer. -/
theorem simultaneous_dirichlet_mul {E : Type*} [Fintype E] (alpha : E → ℝ)
    (Q : ℕ) (hQ : 0 < Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ Fintype.card E ∧
      ∀ e, ∃ z : ℤ, |(q : ℝ) * alpha e - z| < (1 : ℝ) / Q := by
  classical
  let f : Fin (Q ^ Fintype.card E + 1) → (E → Fin Q) :=
    fun r e ↦ dirichletBox alpha Q hQ r e
  have hcard :
      Fintype.card (E → Fin Q) < Fintype.card (Fin (Q ^ Fintype.card E + 1)) := by
    simp [Fintype.card_pi, Finset.prod_const]
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · refine ⟨y - x, Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hxy_lt), ?_, ?_⟩
    · exact (Nat.sub_le y x).trans (Nat.le_of_lt_succ y.isLt)
    · intro e
      let z : ℤ := ⌊(y : ℝ) * alpha e⌋ - ⌊(x : ℝ) * alpha e⌋
      refine ⟨z, ?_⟩
      have hbox : dirichletBox alpha Q hQ x e = dirichletBox alpha Q hQ y e :=
        congrFun hf e
      have hfract := abs_fract_sub_lt_inv_of_box_eq alpha Q hQ hbox
      have hxdecomp := Int.fract_add_floor ((x : ℝ) * alpha e)
      have hydecomp := Int.fract_add_floor ((y : ℝ) * alpha e)
      dsimp [z]
      have heq :
          ((y - x : ℕ) : ℝ) * alpha e -
              (↑(⌊(y : ℝ) * alpha e⌋ - ⌊(x : ℝ) * alpha e⌋) : ℝ) =
            Int.fract ((y : ℝ) * alpha e) - Int.fract ((x : ℝ) * alpha e) := by
        rw [Nat.cast_sub hxy_lt.le]
        push_cast
        linarith
      rw [heq]
      exact hfract
  · refine ⟨x - y, Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hyx_lt), ?_, ?_⟩
    · exact (Nat.sub_le x y).trans (Nat.le_of_lt_succ x.isLt)
    · intro e
      let z : ℤ := ⌊(x : ℝ) * alpha e⌋ - ⌊(y : ℝ) * alpha e⌋
      refine ⟨z, ?_⟩
      have hbox : dirichletBox alpha Q hQ y e = dirichletBox alpha Q hQ x e :=
        (congrFun hf e).symm
      have hfract := abs_fract_sub_lt_inv_of_box_eq alpha Q hQ hbox
      have hxdecomp := Int.fract_add_floor ((x : ℝ) * alpha e)
      have hydecomp := Int.fract_add_floor ((y : ℝ) * alpha e)
      dsimp [z]
      have heq :
          ((x - y : ℕ) : ℝ) * alpha e -
              (↑(⌊(x : ℝ) * alpha e⌋ - ⌊(y : ℝ) * alpha e⌋) : ℝ) =
            Int.fract ((x : ℝ) * alpha e) - Int.fract ((y : ℝ) * alpha e) := by
        rw [Nat.cast_sub hyx_lt.le]
        push_cast
        linarith
      rw [heq]
      exact hfract

/-- **Finite simultaneous Dirichlet box lemma.**

If `m ≥ 1`, all coordinates of `alpha` lie strictly between zero and one,
and `Q ≥ 2`, then there is a denominator `1 ≤ q ≤ Q ^ m` and integer
numerators in `[0,q]` which approximate every coordinate with error strictly
less than `1 / (Q*q)`. -/
theorem finite_simultaneous_dirichlet {m Q : ℕ} (_hm : 1 ≤ m) (hQ : 2 ≤ Q)
    (alpha : Fin m → ℝ) (halpha : ∀ j, 0 < alpha j ∧ alpha j < 1) :
    ∃ q : ℕ, ∃ p : Fin m → ℤ,
      1 ≤ q ∧ q ≤ Q ^ m ∧
        (∀ j, |alpha j - (p j : ℝ) / q| < 1 / ((Q : ℝ) * q)) ∧
        ∀ j, (0 : ℤ) ≤ p j ∧ p j ≤ q := by
  obtain ⟨q, hqpos, hqQ, hp⟩ :=
    simultaneous_dirichlet_mul alpha Q (lt_of_lt_of_le Nat.zero_lt_two hQ)
  choose p hp using hp
  simp only [Fintype.card_fin] at hqQ
  refine ⟨q, p, hqpos, hqQ, ?_, ?_⟩
  · intro j
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have heq :
        alpha j - (p j : ℝ) / q = ((q : ℝ) * alpha j - p j) / q := by
      field_simp
    have hrhs :
        (1 : ℝ) / ((Q : ℝ) * q) = ((1 : ℝ) / Q) / q := by
      ring
    rw [heq, abs_div, abs_of_pos hqR, hrhs, div_lt_div_iff_of_pos_right hqR]
    exact hp j
  · intro j
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hQR : (0 : ℝ) < Q := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two hQ
    have hInvLtOne : (1 : ℝ) / Q < 1 := by
      rw [div_lt_one hQR]
      exact_mod_cast hQ
    have h := hp j
    rw [abs_lt] at h
    constructor
    · have hp_nonneg : 0 ≤ (p j : ℝ) := by
        by_contra hn
        have hp_neg : p j < 0 := by exact_mod_cast (lt_of_not_ge hn)
        have hp_le : (p j : ℝ) ≤ -1 := by
          exact_mod_cast (Int.lt_add_one_iff.mp hp_neg)
        nlinarith [halpha j]
      exact_mod_cast hp_nonneg
    · have hp_le_q : (p j : ℝ) ≤ q := by
        by_contra hn
        have hq_lt : (q : ℤ) < p j := by exact_mod_cast (lt_of_not_ge hn)
        have hq_add_one : (q : ℝ) + 1 ≤ p j := by
          exact_mod_cast (Int.add_one_le_iff.mpr hq_lt)
        nlinarith [halpha j]
      exact_mod_cast hp_le_q

end

end Erdos485
