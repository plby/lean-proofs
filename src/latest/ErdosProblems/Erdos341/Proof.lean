import ErdosProblems.Erdos341.Shield

set_option linter.style.header false

/-!
# Erdős Problem 341: a fixed aperiodic greedy extension

-/

set_option autoImplicit false

namespace Erdos341

abbrev Pow8 (k : ℕ) : ℕ := 8 ^ k

/-- The first state of the scale-eight controller. -/
def Y0 (n : ℕ) : Prop :=
  n = 0 ∨ ∃ k : ℕ, 4 * Pow8 k ≤ n ∧ n < 8 * Pow8 k

/-- The second state of the scale-eight controller. -/
def Y1 (n : ℕ) : Prop :=
  (1 ≤ n ∧ n ≤ 3) ∨
    ∃ k : ℕ, 16 * Pow8 k ≤ n + 1 ∧ n < 32 * Pow8 k

/-- The third state of the scale-eight controller. -/
def Y2 (n : ℕ) : Prop :=
  n ≤ 1 ∨ (7 ≤ n ∧ n ≤ 15) ∨
    ∃ k : ℕ, 64 * Pow8 k ≤ n + 1 ∧ n < 128 * Pow8 k

/-- Ordered pair-sum membership; equal summands are allowed. -/
def PairSum (X : ℕ → Prop) (n : ℕ) : Prop :=
  ∃ a b : ℕ, X a ∧ X b ∧ a + b = n

def F0 (n : ℕ) : Prop :=
  n = 0 ∨ ∃ k : ℕ, 4 * Pow8 k ≤ n ∧ n + 2 ≤ 16 * Pow8 k

def F1 (n : ℕ) : Prop :=
  (2 ≤ n ∧ n ≤ 6) ∨
    ∃ k : ℕ, 16 * Pow8 k ≤ n ∧ n + 2 ≤ 64 * Pow8 k

def F2 (n : ℕ) : Prop :=
  n ≤ 2 ∨ (7 ≤ n ∧ n ≤ 30) ∨
    ∃ k : ℕ, 64 * Pow8 k ≤ n + 1 ∧ n + 2 ≤ 256 * Pow8 k

lemma pow8_pos (k : ℕ) : 0 < Pow8 k := by
  positivity

lemma pow8_mono {i j : ℕ} (hij : i ≤ j) : Pow8 i ≤ Pow8 j := by
  exact Nat.pow_le_pow_right (by omega) hij

lemma eight_mul_pow8_le {i j : ℕ} (hij : i < j) : 8 * Pow8 i ≤ Pow8 j := by
  have h := pow8_mono (Nat.succ_le_iff.mpr hij)
  simpa [Pow8, Nat.pow_succ, mul_comm] using h

lemma y0_zero : Y0 0 := by simp [Y0]
lemma y1_one : Y1 1 := by simp [Y1]
lemma y2_zero : Y2 0 := by simp [Y2]
lemma y2_one : Y2 1 := by simp [Y2]

lemma not_y0_one : ¬ Y0 1 := by
  intro h
  rcases h with h | ⟨k, hk, _⟩
  · omega
  · have hp := pow8_pos k
    omega

lemma not_y1_zero : ¬ Y1 0 := by
  intro h
  rcases h with h | ⟨k, hk, _⟩
  · omega
  · have hp := pow8_pos k
    omega

lemma exists_scale4 {n : ℕ} (hn : 4 ≤ n) :
    ∃ k : ℕ, 4 * Pow8 k ≤ n ∧ n < 32 * Pow8 k := by
  let z := n / 4
  have hz : z ≠ 0 := by
    dsimp [z]
    omega
  refine ⟨Nat.log 8 z, ?_, ?_⟩
  · have hlo := Nat.pow_log_le_self 8 hz
    have hfloor : 4 * z ≤ n := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 4 hlo
    simpa [Pow8] using hm.trans hfloor
  · have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 8) z
    simp only [Nat.pow_succ] at hhi
    have hz8 : z + 1 ≤ 8 * 8 ^ Nat.log 8 z := by
      rw [mul_comm]
      omega
    have hnlt : n < 4 * (z + 1) := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 4 hz8
    calc
      n < 4 * (z + 1) := hnlt
      _ ≤ 4 * (8 * 8 ^ Nat.log 8 z) := hm
      _ = 32 * Pow8 (Nat.log 8 z) := by simp [Pow8]; ring

lemma exists_scale16 {n : ℕ} (hn : 16 ≤ n) :
    ∃ k : ℕ, 16 * Pow8 k ≤ n ∧ n < 128 * Pow8 k := by
  let z := n / 16
  have hz : z ≠ 0 := by
    dsimp [z]
    omega
  refine ⟨Nat.log 8 z, ?_, ?_⟩
  · have hlo := Nat.pow_log_le_self 8 hz
    have hfloor : 16 * z ≤ n := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 16 hlo
    simpa [Pow8] using hm.trans hfloor
  · have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 8) z
    simp only [Nat.pow_succ] at hhi
    have hz8 : z + 1 ≤ 8 * 8 ^ Nat.log 8 z := by
      rw [mul_comm]
      omega
    have hnlt : n < 16 * (z + 1) := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 16 hz8
    calc
      n < 16 * (z + 1) := hnlt
      _ ≤ 16 * (8 * 8 ^ Nat.log 8 z) := hm
      _ = 128 * Pow8 (Nat.log 8 z) := by simp [Pow8]; ring

lemma exists_scale64 {n : ℕ} (hn : 64 ≤ n) :
    ∃ k : ℕ, 64 * Pow8 k ≤ n ∧ n < 512 * Pow8 k := by
  let z := n / 64
  have hz : z ≠ 0 := by
    dsimp [z]
    omega
  refine ⟨Nat.log 8 z, ?_, ?_⟩
  · have hlo := Nat.pow_log_le_self 8 hz
    have hfloor : 64 * z ≤ n := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 64 hlo
    simpa [Pow8] using hm.trans hfloor
  · have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < 8) z
    simp only [Nat.pow_succ] at hhi
    have hz8 : z + 1 ≤ 8 * 8 ^ Nat.log 8 z := by
      rw [mul_comm]
      omega
    have hnlt : n < 64 * (z + 1) := by
      dsimp [z]
      omega
    have hm := Nat.mul_le_mul_left 64 hz8
    calc
      n < 64 * (z + 1) := hnlt
      _ ≤ 64 * (8 * 8 ^ Nat.log 8 z) := hm
      _ = 512 * Pow8 (Nat.log 8 z) := by simp [Pow8]; ring

/-! ## Exact controller sumsets -/

theorem pairSum_y0_iff (n : ℕ) : PairSum Y0 n ↔ F0 n := by
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    rcases hx with hx0 | ⟨i, hxi0, hxi1⟩
    · subst x
      rcases hy with hy0 | ⟨j, hyj0, hyj1⟩
      · subst y
        exact Or.inl rfl
      · right
        refine ⟨j, ?_, ?_⟩
        · simpa using hyj0
        · have hj := pow8_pos j
          omega
    · rcases hy with hy0 | ⟨j, hyj0, hyj1⟩
      · subst y
        right
        refine ⟨i, ?_, ?_⟩
        · simpa using hxi0
        · have hi := pow8_pos i
          omega
      · right
        rcases le_total i j with hij | hji
        · refine ⟨j, ?_, ?_⟩
          · omega
          · have hp := pow8_mono hij
            omega
        · refine ⟨i, ?_, ?_⟩
          · omega
          · have hp := pow8_mono hji
            omega
  · intro hn
    rcases hn with hn0 | ⟨k, hk0, hk1⟩
    · subst n
      exact ⟨0, 0, y0_zero, y0_zero, rfl⟩
    · have hk := pow8_pos k
      by_cases h8 : n < 8 * Pow8 k
      · exact ⟨0, n, y0_zero, Or.inr ⟨k, hk0, h8⟩, by omega⟩
      · by_cases h12 : n < 12 * Pow8 k
        · refine ⟨4 * Pow8 k, n - 4 * Pow8 k, ?_, ?_, ?_⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega
        · refine ⟨8 * Pow8 k - 1, n - (8 * Pow8 k - 1), ?_, ?_, ?_⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega

theorem pairSum_y1_iff (n : ℕ) : PairSum Y1 n ↔ F1 n := by
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    rcases hx with hxsmall | ⟨i, hxi0, hxi1⟩
    · rcases hy with hysmall | ⟨j, hyj0, hyj1⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · right
        refine ⟨j, ?_, ?_⟩
        · omega
        · have hj := pow8_pos j
          omega
    · rcases hy with hysmall | ⟨j, hyj0, hyj1⟩
      · right
        refine ⟨i, ?_, ?_⟩
        · omega
        · have hi := pow8_pos i
          omega
      · right
        rcases le_total i j with hij | hji
        · refine ⟨j, ?_, ?_⟩
          · have hi := pow8_pos i
            omega
          · have hp := pow8_mono hij
            omega
        · refine ⟨i, ?_, ?_⟩
          · have hj := pow8_pos j
            omega
          · have hp := pow8_mono hji
            omega
  · intro hn
    rcases hn with hsmall | ⟨k, hk0, hk1⟩
    · by_cases h4 : n ≤ 4
      · refine ⟨1, n - 1, ?_, ?_, ?_⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · omega
      · refine ⟨n - 3, 3, ?_, ?_, ?_⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · omega
    · have hk := pow8_pos k
      by_cases htop : n ≤ 32 * Pow8 k + 2
      · by_cases hmid : n < 32 * Pow8 k + 1
        · refine ⟨1, n - 1, ?_, ?_, ?_⟩
          · exact Or.inl ⟨by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega
        · refine ⟨n - (32 * Pow8 k - 1), 32 * Pow8 k - 1, ?_, ?_, ?_⟩
          · exact Or.inl ⟨by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega
      · by_cases h48 : n < 48 * Pow8 k - 1
        · refine ⟨16 * Pow8 k - 1, n - (16 * Pow8 k - 1), ?_, ?_, ?_⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega
        · refine ⟨32 * Pow8 k - 1, n - (32 * Pow8 k - 1), ?_, ?_, ?_⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · exact Or.inr ⟨k, by omega, by omega⟩
          · omega

theorem pairSum_y2_iff (n : ℕ) : PairSum Y2 n ↔ F2 n := by
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    rcases hx with hx01 | hx7 | ⟨i, hxi0, hxi1⟩
    · rcases hy with hy01 | hy7 | ⟨j, hyj0, hyj1⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, by have hj := pow8_pos j; omega⟩)
    · rcases hy with hy01 | hy7 | ⟨j, hyj0, hyj1⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, by have hj := pow8_pos j; omega⟩)
    · rcases hy with hy01 | hy7 | ⟨j, hyj0, hyj1⟩
      · exact Or.inr (Or.inr ⟨i, by omega, by have hi := pow8_pos i; omega⟩)
      · exact Or.inr (Or.inr ⟨i, by omega, by have hi := pow8_pos i; omega⟩)
      · right
        right
        rcases le_total i j with hij | hji
        · refine ⟨j, ?_, ?_⟩
          · have hi := pow8_pos i
            omega
          · have hp := pow8_mono hij
            omega
        · refine ⟨i, ?_, ?_⟩
          · have hj := pow8_pos j
            omega
          · have hp := pow8_mono hji
            omega
  · intro hn
    rcases hn with h02 | h730 | ⟨k, hk0, hk1⟩
    · by_cases h1 : n ≤ 1
      · exact ⟨0, n, Or.inl (by omega), Or.inl h1, by omega⟩
      · exact ⟨1, 1, Or.inl (by omega), Or.inl (by omega), by omega⟩
    · by_cases h15 : n ≤ 15
      · exact ⟨0, n, Or.inl (by omega), Or.inr (Or.inl ⟨by omega, h15⟩), by omega⟩
      · by_cases h16 : n ≤ 16
        · exact ⟨1, 15, Or.inl (by omega), Or.inr (Or.inl ⟨by omega, by omega⟩), by omega⟩
        · by_cases h22 : n ≤ 22
          · refine ⟨7, n - 7, ?_, ?_, ?_⟩
            · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            · omega
          · refine ⟨15, n - 15, ?_, ?_, ?_⟩
            · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            · omega
    · have hk := pow8_pos k
      by_cases h128 : n < 128 * Pow8 k
      · exact ⟨0, n, Or.inl (by omega), Or.inr (Or.inr ⟨k, hk0, h128⟩), by omega⟩
      · by_cases h128eq : n ≤ 128 * Pow8 k
        · refine ⟨1, 128 * Pow8 k - 1, Or.inl (by omega), ?_, by omega⟩
          exact Or.inr (Or.inr ⟨k, by omega, by omega⟩)
        · by_cases h192 : n < 192 * Pow8 k - 1
          · refine ⟨64 * Pow8 k - 1, n - (64 * Pow8 k - 1), ?_, ?_, ?_⟩
            · exact Or.inr (Or.inr ⟨k, by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨k, by omega, by omega⟩)
            · omega
          · refine ⟨128 * Pow8 k - 1, n - (128 * Pow8 k - 1), ?_, ?_, ?_⟩
            · exact Or.inr (Or.inr ⟨k, by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨k, by omega, by omega⟩)
            · omega

theorem y1_iff_not_f0 (n : ℕ) : Y1 n ↔ ¬ F0 n := by
  constructor
  · intro hy hf
    rcases hy with hsmall | ⟨i, hi0, hi1⟩
    · rcases hf with rfl | ⟨j, hj0, hj1⟩
      · omega
      · have hj := pow8_pos j
        omega
    · rcases hf with hf0 | ⟨j, hj0, hj1⟩
      · subst n
        have hi := pow8_pos i
        omega
      · rcases lt_trichotomy i j with hij | hij | hij
        · have hp := eight_mul_pow8_le hij
          omega
        · subst j
          omega
        · have hp := eight_mul_pow8_le hij
          omega
  · intro hnf
    by_cases h4 : n < 4
    · left
      have hn0 : n ≠ 0 := by
        intro hn
        apply hnf
        exact Or.inl hn
      constructor <;> omega
    · obtain ⟨k, hk0, hk1⟩ := exists_scale4 (by omega : 4 ≤ n)
      right
      refine ⟨k, ?_, hk1⟩
      by_contra hbad
      apply hnf
      right
      exact ⟨k, hk0, by omega⟩

theorem y2_iff_not_f1 (n : ℕ) : Y2 n ↔ ¬ F1 n := by
  constructor
  · intro hy hf
    rcases hy with h01 | h715 | ⟨i, hi0, hi1⟩
    · rcases hf with h26 | ⟨j, hj0, hj1⟩
      · omega
      · have hj := pow8_pos j
        omega
    · rcases hf with h26 | ⟨j, hj0, hj1⟩
      · omega
      · have hj := pow8_pos j
        omega
    · rcases hf with h26 | ⟨j, hj0, hj1⟩
      · have hi := pow8_pos i
        omega
      · rcases lt_trichotomy i j with hij | hij | hij
        · have hp := eight_mul_pow8_le hij
          omega
        · subst j
          omega
        · have hp := eight_mul_pow8_le hij
          omega
  · intro hnf
    by_cases h16 : n < 16
    · by_cases h2 : n ≤ 1
      · exact Or.inl h2
      · right
        left
        have hn7 : 7 ≤ n := by
          by_contra hn
          apply hnf
          exact Or.inl ⟨by omega, by omega⟩
        exact ⟨hn7, by omega⟩
    · obtain ⟨k, hk0, hk1⟩ := exists_scale16 (by omega : 16 ≤ n)
      right
      right
      refine ⟨k, ?_, hk1⟩
      by_contra hbad
      apply hnf
      right
      exact ⟨k, hk0, by omega⟩

theorem y0_succ_iff_not_f2 (n : ℕ) : Y0 (n + 1) ↔ ¬ F2 n := by
  constructor
  · intro hy hf
    rcases hy with hzero | ⟨k, hk0, hk1⟩
    · omega
    · rcases k with _ | k
      · have hq0 : 4 ≤ n + 1 ∧ n + 1 < 8 := by
          simpa [Pow8] using And.intro hk0 hk1
        rcases hf with h02 | h730 | ⟨j, hj0, hj1⟩
        · omega
        · omega
        · have hj := pow8_pos j
          omega
      · rcases k with _ | j
        · have hq1 : 32 ≤ n + 1 ∧ n + 1 < 64 := by
            simpa [Pow8] using And.intro hk0 hk1
          rcases hf with h02 | h730 | ⟨j, hj0, hj1⟩
          · omega
          · omega
          · have hj := pow8_pos j
            omega
        · have hp : Pow8 (Nat.succ (Nat.succ j)) = 64 * Pow8 j := by
            simp [Pow8, Nat.pow_succ]
            ring
          rw [hp] at hk0 hk1
          rcases hf with h02 | h730 | ⟨i, hi0, hi1⟩
          · have hj := pow8_pos j
            omega
          · have hj := pow8_pos j
            omega
          · rcases le_or_gt i j with hij | hji
            · have hpij := pow8_mono hij
              omega
            · have hpij := eight_mul_pow8_le hji
              omega
  · intro hnf
    by_cases h63 : n < 63
    · by_cases h2 : n ≤ 2
      · exact (hnf (Or.inl h2)).elim
      · by_cases h6 : n ≤ 6
        · right
          refine ⟨0, ?_, ?_⟩ <;> norm_num [Pow8] <;> omega
        · by_cases h30 : n ≤ 30
          · exact (hnf (Or.inr (Or.inl ⟨by omega, h30⟩))).elim
          · right
            refine ⟨1, ?_, ?_⟩ <;> norm_num [Pow8] <;> omega
    · obtain ⟨k, hk0, hk1⟩ := exists_scale64 (by omega : 64 ≤ n + 1)
      have hk256 : 256 * Pow8 k ≤ n + 1 := by
        by_contra hbad
        apply hnf
        right
        right
        exact ⟨k, hk0, by omega⟩
      right
      refine ⟨k + 2, ?_, ?_⟩
      · have hp : Pow8 (k + 2) = 64 * Pow8 k := by
          simp [Pow8, pow_add]
          ring
        rw [hp]
        omega
      · have hp : Pow8 (k + 2) = 64 * Pow8 k := by
          simp [Pow8, pow_add]
          ring
        rw [hp]
        omega

theorem controller_01 (n : ℕ) : Y1 n ↔ ¬ PairSum Y0 n := by
  rw [pairSum_y0_iff, y1_iff_not_f0]

theorem controller_12 (n : ℕ) : Y2 n ↔ ¬ PairSum Y1 n := by
  rw [pairSum_y1_iff, y2_iff_not_f1]

theorem controller_20 (n : ℕ) : Y0 (n + 1) ↔ ¬ PairSum Y2 n := by
  rw [pairSum_y2_iff, y0_succ_iff_not_f2]

/-! ## The modulus-49 shield and the infinite selected set -/

def P (r : Fin 49) : Prop := r.1 = 7 ∨ r.1 = 14 ∨ r.1 = 28
def B (r : Fin 49) : Prop :=
  r.1 = 3 ∨ r.1 = 22 ∨ r.1 = 32 ∨ r.1 = 40 ∨ r.1 = 48
def DResidue (r : Fin 49) : Prop :=
  r.1 = 1 ∨ r.1 = 2 ∨ r.1 = 5 ∨ r.1 = 13 ∨ r.1 = 27 ∨ r.1 = 36 ∨ r.1 = 47
def Q (r : Fin 49) : Prop := B r ∨ P r

def D (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 13 ∨ n = 27 ∨ n = 36 ∨ n = 47

def Seed (n : ℕ) : Prop :=
  n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 13 ∨
  n = 22 ∨ n = 27 ∨ n = 28 ∨ n = 32 ∨ n = 36 ∨ n = 40 ∨
  n = 47 ∨ n = 48 ∨ n = 52 ∨ n = 63 ∨ n = 71 ∨ n = 77 ∨
  n = 81 ∨ n = 89 ∨ n = 97

def residue (n : ℕ) : Fin 49 := ⟨n % 49, Nat.mod_lt _ (by omega)⟩

def S (n : ℕ) : Prop :=
  D n ∨ B (residue n) ∨
    (n % 49 = 7 ∧ Y0 (n / 49)) ∨
    (n % 49 = 14 ∧ Y1 (n / 49)) ∨
    (n % 49 = 28 ∧ Y2 (n / 49))

def EventuallyPeriodic {α : Type} (f : ℕ → α) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → f (n + p) = f n

def GreedyExtension (A X : ℕ → Prop) (N : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ N → (X n ↔ A n)) ∧
  (∀ n : ℕ, N < n → (X n ↔ ¬ PairSum X n))

theorem seed_prefix : ∀ n : ℕ, n ≤ 97 → (S n ↔ Seed n) := by
  intro n hn
  interval_cases n <;>
    norm_num [S, D, B, residue, Seed, y0_zero, y1_one, y2_zero, y2_one,
      not_y0_one, not_y1_zero]

def shieldController : Erdos341Shield.Controller where
  y0 := Y0
  y1 := Y1
  y2 := Y2
  gate01 := controller_01
  gate12 := controller_12
  gate20 := controller_20
  y0_zero := y0_zero
  y0_one_false := not_y0_one
  y1_zero_false := not_y1_zero
  y1_one := y1_one
  y2_zero := y2_zero
  y2_one := y2_one

lemma S_iff_shieldSelected (n : ℕ) :
    S n ↔ Erdos341Shield.Selected shieldController n := by
  simp [S, Erdos341Shield.Selected, D, Erdos341Shield.dNat, B,
    Erdos341Shield.bResidues, residue, Erdos341Shield.residue,
    shieldController, Fin.ext_iff]

theorem exact_recurrence : ∀ n : ℕ, 97 < n → (S n ↔ ¬ PairSum S n) := by
  intro n hn
  simpa [PairSum, Erdos341Shield.PairSum, S_iff_shieldSelected] using
    (Erdos341Shield.exact_recurrence shieldController n hn)

theorem S_is_greedy : GreedyExtension Seed S 97 := by
  exact ⟨seed_prefix, exact_recurrence⟩

lemma rail_three_mem (q : ℕ) : S (49 * q + 3) := by
  right
  left
  simp [B, residue]

theorem S_infinite : {n : ℕ | S n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun q : ℕ ↦ 49 * q + 3)
  · intro q r h
    dsimp at h
    omega
  · exact rail_three_mem

theorem not_eventuallyPeriodic_Y0 : ¬ EventuallyPeriodic Y0 := by
  rintro ⟨N, p, hp, hperiod⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (N + p) (by norm_num : (1 : ℕ) < 8)
  let a : ℕ := Pow8 k
  let n : ℕ := 4 * a - p
  have ha : 0 < a := pow8_pos k
  have hlarge : N + p < a := by simpa [a] using hk
  have hp_a : p < a := by omega
  have hp_four_a : p ≤ 4 * a := by omega
  have hn_add : n + p = 4 * a := by
    dsimp [n]
    exact Nat.sub_add_cancel hp_four_a
  have hn_lower : a ≤ n := by
    dsimp [n]
    omega
  have hn_upper : n < 4 * a := by
    dsimp [n]
    omega
  have hnN : N ≤ n := by omega
  have hy_at_endpoint : Y0 (4 * a) := by
    right
    refine ⟨k, ?_, ?_⟩
    · simp [a]
    · dsimp [a]
      omega
  have hy_before : ¬ Y0 n := by
    rintro (hn0 | ⟨j, hj0, hj1⟩)
    · omega
    · by_cases hkj : k ≤ j
      · have hpowers : Pow8 k ≤ Pow8 j := pow8_mono hkj
        omega
      · have hjk' : j + 1 ≤ k := by omega
        have hpowers : Pow8 (j + 1) ≤ Pow8 k := pow8_mono hjk'
        have hrewrite : Pow8 (j + 1) = 8 * Pow8 j := by
          simp [Pow8, pow_succ, Nat.mul_comm]
        rw [hrewrite] at hpowers
        omega
  apply hy_before
  rw [← hperiod n hnN, hn_add]
  exact hy_at_endpoint

lemma S_rail_seven (q : ℕ) : S (49 * q + 7) ↔ Y0 q := by
  have hform : 49 * q + 7 = 7 + 49 * q := by omega
  have hmod : (49 * q + 7) % 49 = 7 := by
    rw [hform, Nat.add_mul_mod_self_left]
  have hdiv : (49 * q + 7) / 49 = q := by
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hD : ¬ D (49 * q + 7) := by
    simp only [D]
    omega
  have hres : residue (49 * q + 7) = (⟨7, by omega⟩ : Fin 49) := by
    apply Fin.ext
    exact hmod
  simp [S, hD, hres, hmod, hdiv, B]

lemma iterate_eventual_period {α : Type} {f : ℕ → α} {N p : ℕ}
    (h : ∀ n : ℕ, N ≤ n → f (n + p) = f n) :
    ∀ k n : ℕ, N ≤ n → f (n + k * p) = f n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro n hn
      calc
        f (n + (k + 1) * p) = f ((n + k * p) + p) := by
          congr 1
          simp [Nat.succ_mul, Nat.add_assoc]
        _ = f (n + k * p) := h _ (by omega)
        _ = f n := ih n hn

theorem not_eventuallyPeriodic_S : ¬ EventuallyPeriodic S := by
  intro hS
  apply not_eventuallyPeriodic_Y0
  rcases hS with ⟨N, p, hp, hperiod⟩
  refine ⟨N, p, hp, ?_⟩
  intro q hq
  rw [← S_rail_seven (q + p), ← S_rail_seven q]
  have hiter := iterate_eventual_period hperiod 49 (49 * q + 7) (by omega)
  have harg : 49 * (q + p) + 7 = (49 * q + 7) + 49 * p := by omega
  rw [harg]
  exact hiter

noncomputable def enumOf (X : ℕ → Prop) (n : ℕ) : ℕ := Nat.nth X n
noncomputable def gapOf (X : ℕ → Prop) (n : ℕ) : ℕ :=
  enumOf X (n + 1) - enumOf X n

noncomputable def enumeration (n : ℕ) : ℕ := enumOf S n
noncomputable def gap (n : ℕ) : ℕ := gapOf S n

theorem enumeration_strictMono : StrictMono enumeration := by
  exact Nat.nth_strictMono S_infinite

theorem enumeration_range : Set.range enumeration = {n : ℕ | S n} := by
  exact Nat.range_nth_of_infinite S_infinite

/-- A candidate is obstructed by two terms already present in the indicated
finite enumeration prefix.  Equal indices are deliberately allowed. -/
def PrefixPairSum (a : ℕ → ℕ) (i t : ℕ) : Prop :=
  ∃ j : ℕ, j ≤ i ∧ ∃ k : ℕ, k ≤ i ∧ a j + a k = t

/-- The next enumerated term is exactly the least admissible integer above the
current one, in the original statement of the problem. -/
def LeastGreedyStep (a : ℕ → ℕ) (i : ℕ) : Prop :=
  a i < a (i + 1) ∧
  ¬ PrefixPairSum a i (a (i + 1)) ∧
  ∀ t : ℕ, a i < t → t < a (i + 1) → PrefixPairSum a i t

lemma S_positive {n : ℕ} (hn : S n) : 0 < n := by
  exact Erdos341Shield.selected_positive shieldController
    ((S_iff_shieldSelected n).mp hn)

theorem enumeration_least_greedy_step (i : ℕ) (hi : 97 ≤ enumeration i) :
    LeastGreedyStep enumeration i := by
  have hstrict := enumeration_strictMono
  have hnext : enumeration i < enumeration (i + 1) :=
    hstrict (by omega)
  refine ⟨hnext, ?_, ?_⟩
  · intro hprefix
    rcases hprefix with ⟨j, hj, k, hk, hsum⟩
    have hSj : S (enumeration j) := by
      simpa [enumeration, enumOf] using Nat.nth_mem_of_infinite S_infinite j
    have hSk : S (enumeration k) := by
      simpa [enumeration, enumOf] using Nat.nth_mem_of_infinite S_infinite k
    have hSnext : S (enumeration (i + 1)) := by
      simpa [enumeration, enumOf] using Nat.nth_mem_of_infinite S_infinite (i + 1)
    have hpair : PairSum S (enumeration (i + 1)) :=
      ⟨enumeration j, enumeration k, hSj, hSk, hsum⟩
    exact ((exact_recurrence _ (by omega)).mp hSnext) hpair
  · intro t hit hti
    have hnotS : ¬ S t := by
      intro hSt
      have htRange : t ∈ Set.range enumeration := by
        rw [enumeration_range]
        exact hSt
      rcases htRange with ⟨j, hj⟩
      have hij : i < j := by
        apply (hstrict.lt_iff_lt).mp
        simpa [hj] using hit
      have hji : j < i + 1 := by
        apply (hstrict.lt_iff_lt).mp
        simpa [hj] using hti
      omega
    have hpair : PairSum S t := by
      by_contra hnotPair
      exact hnotS ((exact_recurrence t (by omega)).mpr hnotPair)
    rcases hpair with ⟨u, v, huS, hvS, huv⟩
    have huPos := S_positive huS
    have hvPos := S_positive hvS
    have huRange : u ∈ Set.range enumeration := by
      rw [enumeration_range]
      exact huS
    have hvRange : v ∈ Set.range enumeration := by
      rw [enumeration_range]
      exact hvS
    rcases huRange with ⟨j, hj⟩
    rcases hvRange with ⟨k, hk⟩
    have hju : j ≤ i := by
      have : enumeration j < enumeration (i + 1) := by
        rw [hj]
        omega
      exact Nat.lt_succ_iff.mp ((hstrict.lt_iff_lt).mp this)
    have hkv : k ≤ i := by
      have : enumeration k < enumeration (i + 1) := by
        rw [hk]
        omega
      exact Nat.lt_succ_iff.mp ((hstrict.lt_iff_lt).mp this)
    exact ⟨j, hju, k, hkv, by simpa [hj, hk] using huv⟩

theorem enumeration_hits_seed_max : ∃ i : ℕ, enumeration i = 97 := by
  have hSeed97 : Seed 97 := by simp [Seed]
  have hS97 : S 97 := (seed_prefix 97 (by omega)).mpr hSeed97
  have : 97 ∈ Set.range enumeration := by
    rw [enumeration_range]
    exact hS97
  simpa using this

theorem least_next_rule_after_fixed_seed :
    ∃ i : ℕ, enumeration i = 97 ∧
      ∀ j : ℕ, i ≤ j → LeastGreedyStep enumeration j := by
  rcases enumeration_hits_seed_max with ⟨i, hi⟩
  refine ⟨i, hi, ?_⟩
  intro j hij
  apply enumeration_least_greedy_step
  have hmono := enumeration_strictMono.monotone hij
  simpa [hi] using hmono

lemma enumOf_step (X : ℕ → Prop) (hX : {n : ℕ | X n}.Infinite) (n : ℕ) :
    enumOf X (n + 1) = enumOf X n + gapOf X n := by
  have hmono : enumOf X n ≤ enumOf X (n + 1) :=
    (Nat.nth_strictMono hX).monotone (Nat.le_succ n)
  dsimp [gapOf]
  omega

theorem eventual_gap_periodicity_implies_membership_periodicity
    (X : ℕ → Prop) (hX : {n : ℕ | X n}.Infinite)
    (hg : EventuallyPeriodic (gapOf X)) : EventuallyPeriodic X := by
  rcases hg with ⟨M, p, hp, hgap⟩
  let a : ℕ → ℕ := enumOf X
  let t : ℕ := a (M + p) - a M
  have ha_strict : StrictMono a := by
    change StrictMono (Nat.nth X)
    exact Nat.nth_strictMono hX
  have ht : 0 < t := by
    have hlt : a M < a (M + p) := ha_strict (by omega)
    dsimp [t]
    omega
  have hshift : ∀ n : ℕ, M ≤ n → a (n + p) = a n + t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        have hle : a M ≤ a (M + p) := (ha_strict (by omega)).le
        dsimp [t]
        omega
    | succ n hn ih =>
        have hstep_n : a (n + 1) = a n + gapOf X n := by
          simpa [a] using enumOf_step X hX n
        have hstep_np : a (n + p + 1) = a (n + p) + gapOf X (n + p) := by
          simpa [a, Nat.add_assoc] using enumOf_step X hX (n + p)
        have hgp : gapOf X (n + p) = gapOf X n := hgap n hn
        calc
          a (n + 1 + p) = a (n + p + 1) := by congr 1; omega
          _ = a (n + p) + gapOf X (n + p) := hstep_np
          _ = (a n + t) + gapOf X n := by rw [ih, hgp]
          _ = a (n + 1) + t := by omega
  refine ⟨a M, t, ht, ?_⟩
  intro x hx
  apply propext
  constructor
  · intro hxt
    have hrange : Set.range a = {n : ℕ | X n} := by
      change Set.range (Nat.nth X) = {n : ℕ | X n}
      exact Nat.range_nth_of_infinite hX
    have hxr : x + t ∈ Set.range a := by
      rw [hrange]
      exact hxt
    rcases hxr with ⟨j, hj⟩
    have hbase : a (M + p) = a M + t := hshift M (by omega)
    have hindex : M + p ≤ j := by
      apply (ha_strict.le_iff_le).mp
      rw [hj, hbase]
      omega
    let i : ℕ := j - p
    have hi : M ≤ i := by
      dsimp [i]
      omega
    have hip : i + p = j := by
      dsimp [i]
      omega
    have hxi : a i = x := by
      have hs := hshift i hi
      rw [hip, hj] at hs
      omega
    have hmem : X (a i) := by
      simpa [a, enumOf] using Nat.nth_mem_of_infinite hX i
    simpa [hxi] using hmem
  · intro hxx
    have hrange : Set.range a = {n : ℕ | X n} := by
      change Set.range (Nat.nth X) = {n : ℕ | X n}
      exact Nat.range_nth_of_infinite hX
    have hxr : x ∈ Set.range a := by
      rw [hrange]
      exact hxx
    rcases hxr with ⟨i, hi⟩
    have hindex : M ≤ i := by
      apply (ha_strict.le_iff_le).mp
      rw [hi]
      exact hx
    have hmem : X (a (i + p)) := by
      simpa [a, enumOf] using Nat.nth_mem_of_infinite hX (i + p)
    have hs := hshift i hindex
    rw [hi] at hs
    simpa [hs] using hmem

theorem gap_not_eventuallyPeriodic : ¬ EventuallyPeriodic gap := by
  intro hg
  exact not_eventuallyPeriodic_S
    (eventual_gap_periodicity_implies_membership_periodicity S S_infinite hg)

/-- Final kernel-checked negative resolution of Erdős Problem 341. -/
theorem erdos_341_negative :
    GreedyExtension Seed S 97 ∧
    (∃ i : ℕ, enumeration i = 97 ∧
      ∀ j : ℕ, i ≤ j → LeastGreedyStep enumeration j) ∧
    ¬ EventuallyPeriodic gap := by
  exact ⟨S_is_greedy, least_next_rule_after_fixed_seed,
    gap_not_eventuallyPeriodic⟩

#print axioms erdos_341_negative

end Erdos341
