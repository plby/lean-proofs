import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith

/-! # An exact Dirichlet hyperbola identity for finite convolution sums -/

namespace Erdos1148.DukeArithmetic

open Finset

lemma sum_hyperbola_strip {R : Type*} [Semiring R] (f g : ℕ → R) (A X : ℕ) :
    ∑ p ∈ (Ioc 0 A ×ˢ Ioc 0 X).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X),
        f p.1 * g p.2 =
      ∑ m ∈ Ioc 0 A, f m * ∑ n ∈ Ioc 0 (X / m), g n := by
  rw [sum_filter, sum_product]
  refine sum_congr rfl (fun m hm => ?_)
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr 1
  have hm0 : 0 < m := (mem_Ioc.mp hm).1
  ext n
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hn0, hnX⟩, hmn⟩
    exact ⟨hn0, (Nat.le_div_iff_mul_le hm0).mpr (by simpa only [mul_comm] using hmn)⟩
  · rintro ⟨hn0, hdiv⟩
    exact ⟨⟨hn0, hdiv.trans (Nat.div_le_self X m)⟩,
      by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hdiv⟩

theorem sum_convolution_hyperbola {R : Type*} [CommRing R]
    (f g : ArithmeticFunction R) {A B X : ℕ}
    (hAX : A ≤ X) (hBX : B ≤ X) (hAB : A * B ≤ X) (hX : X < (A + 1) * (B + 1)) :
    ∑ n ∈ Ioc 0 X, (f * g) n =
      (∑ m ∈ Ioc 0 A, f m * ∑ n ∈ Ioc 0 (X / m), g n) +
      (∑ n ∈ Ioc 0 B, g n * ∑ m ∈ Ioc 0 (X / n), f m) -
      (∑ m ∈ Ioc 0 A, f m) * (∑ n ∈ Ioc 0 B, g n) := by
  classical
  let H := (Ioc 0 X ×ˢ Ioc 0 X).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X)
  let U := H.filter (fun p => p.1 ≤ A)
  let V := H.filter (fun p => p.2 ≤ B)
  have hUnion : U ∪ V = H := by
    ext p
    simp only [U, V, H, mem_union, mem_filter, mem_product, mem_Ioc]
    constructor
    · tauto
    · intro hp
      by_cases ha : p.1 ≤ A
      · exact Or.inl ⟨hp, ha⟩
      · right
        refine ⟨hp, ?_⟩
        by_contra hb
        have hle : (A + 1) * (B + 1) ≤ p.1 * p.2 :=
          Nat.mul_le_mul (by omega) (by omega)
        exact (not_le_of_gt hX) (hle.trans hp.2)
  have hInter : U ∩ V = Ioc 0 A ×ˢ Ioc 0 B := by
    ext p
    simp only [U, V, H, mem_inter, mem_filter, mem_product, mem_Ioc]
    constructor
    · tauto
    · rintro ⟨⟨hp0, hpA⟩, ⟨hq0, hqB⟩⟩
      have hH : ((0 < p.1 ∧ p.1 ≤ X) ∧ 0 < p.2 ∧ p.2 ≤ X) ∧ p.1 * p.2 ≤ X :=
        ⟨⟨⟨hp0, hpA.trans hAX⟩, hq0, hqB.trans hBX⟩,
          (Nat.mul_le_mul hpA hqB).trans hAB⟩
      exact ⟨⟨hH, hpA⟩, hH, hqB⟩
  have hU : U = (Ioc 0 A ×ˢ Ioc 0 X).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X) := by
    ext p
    simp only [U, H, mem_filter, mem_product, mem_Ioc]
    constructor
    · tauto
    · rintro ⟨⟨⟨hp0, hpA⟩, hq⟩, hmul⟩
      exact ⟨⟨⟨⟨hp0, hpA.trans hAX⟩, hq⟩, hmul⟩, hpA⟩
  have hV : V = (Ioc 0 X ×ˢ Ioc 0 B).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X) := by
    ext p
    simp only [V, H, mem_filter, mem_product, mem_Ioc]
    constructor
    · tauto
    · rintro ⟨⟨hp, ⟨hq0, hqB⟩⟩, hmul⟩
      exact ⟨⟨⟨hp, hq0, hqB.trans hBX⟩, hmul⟩, hqB⟩
  have hVsum : ∑ p ∈ V, f p.1 * g p.2 =
      ∑ n ∈ Ioc 0 B, g n * ∑ m ∈ Ioc 0 (X / n), f m := by
    rw [hV]
    calc
      _ = ∑ p ∈ (Ioc 0 B ×ˢ Ioc 0 X).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X),
          g p.1 * f p.2 := by
        rw [sum_filter, sum_product, sum_comm, sum_filter, sum_product]
        simp only [mul_comm]
      _ = _ := sum_hyperbola_strip g f B X
  have h := sum_union_inter (s₁ := U) (s₂ := V) (f := fun p => f p.1 * g p.2)
  rw [hUnion, hInter, hVsum, hU, sum_hyperbola_strip f g A X] at h
  have hrect : (∑ p ∈ Ioc 0 A ×ˢ Ioc 0 B, f p.1 * g p.2) =
      (∑ m ∈ Ioc 0 A, f m) * (∑ n ∈ Ioc 0 B, g n) := by
    rw [sum_product, sum_mul]
    simp only [mul_sum]
  rw [hrect] at h
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
  change (∑ p ∈ H, f p.1 * g p.2) = _
  exact eq_sub_of_add_eq h

end Erdos1148.DukeArithmetic
