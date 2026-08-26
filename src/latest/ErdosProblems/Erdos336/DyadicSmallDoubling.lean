import Mathlib
import ErdosProblems.Erdos336.DenseHighPower

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A dyadic scale with doubling below 9/4
-/

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- Exact list powers agree with Mathlib's pointwise set powers. -/
theorem exactPower_eq_nsmul (A : Set G) (k : ℕ) :
    ExactPower A k = k • A := by
  ext y
  constructor
  · rintro ⟨xs, hlen, hxmem, hxsum⟩
    subst k
    rw [Set.mem_nsmul]
    let f : Fin xs.length → A := fun i =>
      ⟨xs.get i, hxmem (xs.get i) (List.get_mem xs i)⟩
    refine ⟨f, ?_⟩
    change (List.ofFn (fun i : Fin xs.length => xs.get i)).sum = y
    rw [List.ofFn_get]
    exact hxsum
  · intro hy
    rw [Set.mem_nsmul] at hy
    obtain ⟨f, hf⟩ := hy
    let xs : List G := List.ofFn fun i : Fin k => (f i : G)
    refine ⟨xs, by simp [xs], ?_, hf⟩
    intro x hx
    simp only [xs, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (f i).2

/-- Exact powers add exactly. -/
theorem exactPower_add (A : Set G) (k l : ℕ) :
    ExactPower A k + ExactPower A l = ExactPower A (k + l) := by
  simp only [exactPower_eq_nsmul, add_nsmul]

/-- Multiplicative growth at every one of the first `m` dyadic scales forces
the corresponding power growth. -/
lemma nine_pow_mul_le_four_pow_of_growth
    (f : ℕ → ℕ) (m : ℕ)
    (hgrowth : ∀ i : ℕ, i < m → 9 * f i ≤ 4 * f (i + 1)) :
    9 ^ m * f 0 ≤ 4 ^ m * f m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ih' : 9 ^ m * f 0 ≤ 4 ^ m * f m :=
        ih (fun i hi => hgrowth i (by omega))
      have hm := hgrowth m (by omega)
      calc
        9 ^ (m + 1) * f 0 = 9 * (9 ^ m * f 0) := by ring
        _ ≤ 9 * (4 ^ m * f m) := Nat.mul_le_mul_left 9 ih'
        _ ≤ 4 ^ m * (4 * f (m + 1)) := by
          nlinarith [Nat.zero_le (4 ^ m)]
        _ = 4 ^ (m + 1) * f (m + 1) := by ring

/-- Starting from a weak order-`h` cover, every sufficiently long dyadic
range contains a scale whose doubling constant is strictly below `9/4`.
The set at scale `i` is the exact `(2^i h)`-power of the normalized set. -/
theorem exists_dyadic_small_doubling_of_weakCover
    [Fintype G] {B : Set G} {b : G} {h m : ℕ}
    (hb : b ∈ B) (hweak : ∀ y : G, GroupRepAtMost B h y)
    (hscale : 4 ^ m * (h + 1) < 9 ^ m) :
    ∃ i : ℕ, i < m ∧
      4 * (ExactPower (ShiftToZero B b) (2 ^ (i + 1) * h)).ncard <
        9 * (ExactPower (ShiftToZero B b) (2 ^ i * h)).ncard := by
  let C : Set G := ShiftToZero B b
  let f : ℕ → ℕ := fun i => (ExactPower C (2 ^ i * h)).ncard
  have hdense : Fintype.card G ≤ (h + 1) * f 0 := by
    simpa [f, C] using
      card_le_mul_ncard_highPower_of_weakCover hb hweak
  have htop : f m ≤ Fintype.card G := by
    calc
      f m ≤ (Set.univ : Set G).ncard :=
        Set.ncard_le_ncard (fun _ _ => Set.mem_univ _)
      _ = Fintype.card G := by simp
  by_contra hnot
  push_neg at hnot
  have hgrowth : ∀ i : ℕ, i < m → 9 * f i ≤ 4 * f (i + 1) := by
    intro i hi
    simpa [f, C] using hnot i hi
  have hpowers := nine_pow_mul_le_four_pow_of_growth f m hgrowth
  have hpositive : 0 < Fintype.card G := Fintype.card_pos
  have hbad : 9 ^ m * Fintype.card G ≤
      4 ^ m * (h + 1) * Fintype.card G := by
    calc
      9 ^ m * Fintype.card G ≤ 9 ^ m * ((h + 1) * f 0) :=
        Nat.mul_le_mul_left _ hdense
      _ = (h + 1) * (9 ^ m * f 0) := by ring
      _ ≤ (h + 1) * (4 ^ m * f m) :=
        Nat.mul_le_mul_left _ hpowers
      _ = 4 ^ m * (h + 1) * f m := by ring
      _ ≤ 4 ^ m * (h + 1) * Fintype.card G :=
        Nat.mul_le_mul_left _ htop
  nlinarith

end Erdos336
