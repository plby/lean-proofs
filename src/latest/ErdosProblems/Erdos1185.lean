/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1185.
https://www.erdosproblems.com/forum/thread/1185

Informal authors:
- Hillel Furstenberg

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1185.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 1185

The proposed uniform statement is false already for three-term arithmetic
progressions.  We give a finite periodic form of Furstenberg's quadratic
skew-shift counterexample.  The detailed mathematical proof and the
Leanization map are in `tex/1185.tex`.
-/

namespace Erdos1185

open scoped BigOperators

/-- `A` contains a nonconstant `k`-term arithmetic progression whose
positive common difference is a difference of two elements of `B`. -/
def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → a + j * d ∈ A) ∧
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = b₁ - b₂

/-- The literal universal affirmative assertion in Erdős Problem 1185. -/
def Erdos1185Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        δ * (N : ℝ) ≤ (A.card : ℝ) → m ≤ B.card →
        HasAPWithStepInDiff k A B

/-! ## The rapidly divisible sequence -/

/-- The rapidly growing sequence used to make all pairwise quadratic
phases lie in one fixed arc. -/
def rapidB : ℕ → ℕ
  | 0 => 27
  | n + 1 => 27 * (rapidB n) ^ 2

@[simp] lemma rapidB_zero : rapidB 0 = 27 := rfl

@[simp] lemma rapidB_succ (n : ℕ) : rapidB (n + 1) = 27 * (rapidB n) ^ 2 := rfl

lemma rapidB_pos (n : ℕ) : 0 < rapidB n := by
  induction n with
  | zero => norm_num
  | succ n ih => simp only [rapidB_succ]; positivity

lemma rapidB_one_le (n : ℕ) : 1 ≤ rapidB n := rapidB_pos n

lemma rapidB_lt_succ (n : ℕ) : rapidB n < rapidB (n + 1) := by
  rw [rapidB_succ]
  have h := rapidB_one_le n
  nlinarith [sq_nonneg (rapidB n)]

lemma rapidB_strictMono : StrictMono rapidB :=
  strictMono_nat_of_lt_succ rapidB_lt_succ

lemma rapidB_dvd_succ (n : ℕ) : rapidB n ∣ rapidB (n + 1) := by
  rw [rapidB_succ]
  exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _

lemma rapidB_dvd {i j : ℕ} (hij : i ≤ j) : rapidB i ∣ rapidB j := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact dvd_rfl
  | succ j ih =>
      rcases Nat.lt_or_eq_of_le hij with h | rfl
      · exact (ih (by omega)).trans (rapidB_dvd_succ j)
      · exact dvd_rfl

lemma three_mul_rapidB_sq_dvd {i j : ℕ} (hij : i < j) :
    3 * (rapidB i) ^ 2 ∣ rapidB j := by
  have hs : 3 * (rapidB i) ^ 2 ∣ rapidB (i + 1) := by
    rw [rapidB_succ]
    exact ⟨9, by ring⟩
  exact hs.trans (rapidB_dvd (Nat.succ_le_iff.mpr hij))

lemma twenty_seven_mul_rapidB_le_succ (n : ℕ) :
    27 * rapidB n ≤ rapidB (n + 1) := by
  rw [rapidB_succ]
  apply Nat.mul_le_mul_left
  nlinarith [rapidB_one_le n]

lemma rapidB_ge_twenty_seven (n : ℕ) : 27 ≤ rapidB n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [rapidB_succ]
      nlinarith [rapidB_pos n]

lemma twenty_seven_mul_rapidB_le_of_lt {i j : ℕ} (hij : i < j) :
    27 * rapidB i ≤ rapidB j := by
  exact (twenty_seven_mul_rapidB_le_succ i).trans
    (rapidB_strictMono.monotone (by omega : i + 1 ≤ j))

/-! ## The exact finite quadratic phase estimate -/

lemma finite_geometric_tail_invariant (f : ℕ → ℚ)
    (hdec : ∀ n, 27 * f (n + 1) ≤ f n) {i h : ℕ} (hih : i ≤ h) :
    26 * (∑ r ∈ Finset.Ioc i h, f r) + f h ≤ f i := by
  induction h, hih using Nat.le_induction with
  | base => simp
  | succ h hih ih =>
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hih, Finset.sum_insert]
      · have hd := hdec h
        linarith
      · simp

/-- The square tail after the `i`th summand of the finite phase. -/
def squareTail (i h : ℕ) : ℚ :=
  ∑ r ∈ Finset.Ioc i h, (rapidB i : ℚ) ^ 2 / (3 * (rapidB r : ℚ) ^ 2)

private lemma squareTerm_decay (i n : ℕ) :
    27 * ((rapidB i : ℚ) ^ 2 / (3 * (rapidB (n + 1) : ℚ) ^ 2)) ≤
      (rapidB i : ℚ) ^ 2 / (3 * (rapidB n : ℚ) ^ 2) := by
  have hn : (0 : ℚ) < rapidB n := by exact_mod_cast rapidB_pos n
  have hns : (0 : ℚ) < rapidB (n + 1) := by exact_mod_cast rapidB_pos (n + 1)
  have hg : (27 : ℚ) * rapidB n ≤ rapidB (n + 1) := by
    exact_mod_cast twenty_seven_mul_rapidB_le_succ n
  have hden : (27 : ℚ) * (3 * rapidB n ^ 2) ≤ 3 * rapidB (n + 1) ^ 2 := by
    nlinarith [sq_nonneg ((rapidB (n + 1) : ℚ) - 27 * rapidB n)]
  rw [show 27 * ((rapidB i : ℚ) ^ 2 / (3 * rapidB (n + 1) ^ 2)) =
      (27 * (rapidB i : ℚ) ^ 2) / (3 * rapidB (n + 1) ^ 2) by ring]
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 3 * rapidB (n + 1) ^ 2)
    (by positivity : (0 : ℚ) < 3 * rapidB n ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg (rapidB i : ℚ))
  nlinarith

lemma squareTail_bound {i h : ℕ} (hih : i ≤ h) : squareTail i h ≤ 1 / 78 := by
  let f : ℕ → ℚ := fun r =>
    (rapidB i : ℚ) ^ 2 / (3 * (rapidB r : ℚ) ^ 2)
  have hinv := finite_geometric_tail_invariant f (squareTerm_decay i) hih
  have hfh : 0 ≤ f h := by dsimp [f]; positivity
  have hfi : f i = 1 / 3 := by
    dsimp [f]
    have hi : (rapidB i : ℚ) ≠ 0 := by exact_mod_cast (rapidB_pos i).ne'
    field_simp
  change (∑ r ∈ Finset.Ioc i h, f r) ≤ 1 / 78
  rw [hfi] at hinv
  linarith

/-- The linear tail starting at the `j`th summand of the finite phase. -/
def linearTail (j h : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc j h, (rapidB j : ℚ) / (3 * (rapidB r : ℚ) ^ 2)

private lemma linearTerm_decay (j n : ℕ) :
    27 * ((rapidB j : ℚ) / (3 * (rapidB (n + 1) : ℚ) ^ 2)) ≤
      (rapidB j : ℚ) / (3 * (rapidB n : ℚ) ^ 2) := by
  have hn : (0 : ℚ) < rapidB n := by exact_mod_cast rapidB_pos n
  have hns : (0 : ℚ) < rapidB (n + 1) := by exact_mod_cast rapidB_pos (n + 1)
  have hg : (27 : ℚ) * rapidB n ≤ rapidB (n + 1) := by
    exact_mod_cast twenty_seven_mul_rapidB_le_succ n
  have hden : (27 : ℚ) * (3 * rapidB n ^ 2) ≤ 3 * rapidB (n + 1) ^ 2 := by
    nlinarith [sq_nonneg ((rapidB (n + 1) : ℚ) - 27 * rapidB n)]
  rw [show 27 * ((rapidB j : ℚ) / (3 * rapidB (n + 1) ^ 2)) =
      (27 * (rapidB j : ℚ)) / (3 * rapidB (n + 1) ^ 2) by ring]
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < 3 * rapidB (n + 1) ^ 2)
    (by positivity : (0 : ℚ) < 3 * rapidB n ^ 2)]
  have hmul := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℚ) ≤ rapidB j)
  nlinarith

lemma linearTail_bound {j h : ℕ} (hjh : j ≤ h) :
    linearTail j h ≤ 9 / (26 * (rapidB j : ℚ)) := by
  let f : ℕ → ℚ := fun r =>
    (rapidB j : ℚ) / (3 * (rapidB r : ℚ) ^ 2)
  have hinv := finite_geometric_tail_invariant f (linearTerm_decay j) hjh
  have hfh : 0 ≤ f h := by dsimp [f]; positivity
  have hfj : f j = 1 / (3 * (rapidB j : ℚ)) := by
    dsimp [f]
    have hj : (rapidB j : ℚ) ≠ 0 := by exact_mod_cast (rapidB_pos j).ne'
    field_simp
  have hdecomp : linearTail j h = f j + ∑ r ∈ Finset.Ioc j h, f r := by
    rw [linearTail, ← Finset.Ioc_insert_left hjh]
    simp [f]
  rw [hdecomp, hfj]
  rw [hfj] at hinv
  have hjpos : (0 : ℚ) < rapidB j := by exact_mod_cast rapidB_pos j
  have htail : (∑ r ∈ Finset.Ioc j h, f r) ≤ 1 / (78 * (rapidB j : ℚ)) := by
    have hid : 26 * (1 / (78 * (rapidB j : ℚ))) = 1 / (3 * rapidB j) := by
      field_simp
      norm_num
    nlinarith
  calc
    1 / (3 * (rapidB j : ℚ)) + ∑ r ∈ Finset.Ioc j h, f r
        ≤ 1 / (3 * (rapidB j : ℚ)) + 1 / (78 * (rapidB j : ℚ)) := by gcongr
    _ = 9 / (26 * (rapidB j : ℚ)) := by field_simp; ring

lemma crossTail_bound {i j h : ℕ} (hij : i < j) (hjh : j ≤ h) :
    2 * (rapidB i : ℚ) * linearTail j h ≤ 1 / 39 := by
  have hS := linearTail_bound hjh
  have hgrowth : (27 : ℚ) * rapidB i ≤ rapidB j := by
    exact_mod_cast twenty_seven_mul_rapidB_le_of_lt hij
  have hi : (0 : ℚ) < rapidB i := by exact_mod_cast rapidB_pos i
  have hj : (0 : ℚ) < rapidB j := by exact_mod_cast rapidB_pos j
  have hS0 : 0 ≤ linearTail j h := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  calc
    2 * (rapidB i : ℚ) * linearTail j h
        ≤ 2 * (rapidB i : ℚ) * (9 / (26 * (rapidB j : ℚ))) := by gcongr
    _ ≤ 1 / 39 := by
      rw [show 2 * (rapidB i : ℚ) * (9 / (26 * rapidB j)) =
        (18 * rapidB i) / (26 * rapidB j) by field_simp; ring]
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < 26 * rapidB j)).2
      rw [show (1 / 39 : ℚ) * (26 * rapidB j) = (2 / 3) * rapidB j by ring]
      have hmul := mul_le_mul_of_nonneg_left hgrowth (by norm_num : (0 : ℚ) ≤ 2 / 3)
      norm_num at hmul
      nlinarith

/-- The finite denominator `Q`. -/
def phaseModulus (h : ℕ) : ℕ := 3 * rapidB h ^ 2

/-- The numerator `p` of the rational phase `p / Q`. -/
def phaseNumerator (h : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (h + 1), phaseModulus h / (3 * rapidB r ^ 2)

def phaseAlpha (h : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (h + 1), 1 / (3 * (rapidB r : ℚ) ^ 2)

lemma phaseModulus_pos (h : ℕ) : 0 < phaseModulus h := by
  exact Nat.mul_pos (by norm_num) (pow_pos (rapidB_pos h) _)

lemma rapidB_odd (n : ℕ) : Odd (rapidB n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [rapidB_succ]
      exact (by norm_num : Odd 27).mul ih.pow

lemma phaseModulus_odd (h : ℕ) : Odd (phaseModulus h) := by
  rw [phaseModulus]
  exact (by norm_num : Odd 3).mul (rapidB_odd h).pow

lemma phase_den_dvd_modulus {r h : ℕ} (hrh : r ≤ h) :
    3 * rapidB r ^ 2 ∣ phaseModulus h := by
  rcases rapidB_dvd hrh with ⟨c, hc⟩
  refine ⟨c ^ 2, ?_⟩
  simp only [phaseModulus]
  rw [hc]
  ring

lemma cast_nat_exact_div {a b : ℕ} (hb : 0 < b) (hba : b ∣ a) :
    ((a / b : ℕ) : ℚ) = (a : ℚ) / b := by
  apply (eq_div_iff (by exact_mod_cast hb.ne')).2
  exact_mod_cast Nat.div_mul_cancel hba

lemma phaseNumerator_div_modulus (h : ℕ) :
    (phaseNumerator h : ℚ) / phaseModulus h = phaseAlpha h := by
  rw [phaseNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hrh : r ≤ h := by simpa using Finset.mem_range.mp hr
  have hdpos : 0 < 3 * rapidB r ^ 2 :=
    Nat.mul_pos (by norm_num) (pow_pos (rapidB_pos r) _)
  have hQpos := phaseModulus_pos h
  rw [cast_nat_exact_div hdpos (phase_den_dvd_modulus hrh)]
  have hQ : (phaseModulus h : ℚ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hd : ((3 * rapidB r ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  field_simp
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hbr : (rapidB r : ℚ) ≠ 0 := by exact_mod_cast (rapidB_pos r).ne'
  field_simp

lemma phaseAlpha_split {i h : ℕ} (hih : i ≤ h) :
    phaseAlpha h =
      (∑ r ∈ Finset.range i, 1 / (3 * (rapidB r : ℚ) ^ 2)) +
        1 / (3 * (rapidB i : ℚ) ^ 2) +
          ∑ r ∈ Finset.Ioc i h, 1 / (3 * (rapidB r : ℚ) ^ 2) := by
  rw [phaseAlpha, ← Finset.sum_range_add_sum_Ico _ (by omega : i ≤ h + 1)]
  have hinterval : Finset.Ico i (h + 1) = Finset.Icc i h := by
    ext r
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hinterval, Finset.Icc_eq_cons_Ioc hih, Finset.sum_cons]
  ring

def squarePrefix (i : ℕ) : ℕ :=
  ∑ r ∈ Finset.range i, rapidB i ^ 2 / (3 * rapidB r ^ 2)

def linearPrefix (j : ℕ) : ℕ :=
  ∑ r ∈ Finset.range j, rapidB j / (3 * rapidB r ^ 2)

lemma cast_squarePrefix (i : ℕ) :
    (squarePrefix i : ℚ) =
      ∑ r ∈ Finset.range i, (1 / (3 * (rapidB r : ℚ) ^ 2)) * rapidB i ^ 2 := by
  rw [squarePrefix, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hri : r < i := Finset.mem_range.mp hr
  have hdpos : 0 < 3 * rapidB r ^ 2 :=
    Nat.mul_pos (by norm_num) (pow_pos (rapidB_pos r) _)
  have hdSq : 3 * rapidB r ^ 2 ∣ rapidB i ^ 2 := by
    simpa [pow_two] using
      dvd_mul_of_dvd_left (three_mul_rapidB_sq_dvd hri) (rapidB i)
  rw [cast_nat_exact_div (a := rapidB i ^ 2) (b := 3 * rapidB r ^ 2)
    hdpos hdSq]
  norm_num
  ring

lemma cast_linearPrefix (j : ℕ) :
    (linearPrefix j : ℚ) =
      ∑ r ∈ Finset.range j, (1 / (3 * (rapidB r : ℚ) ^ 2)) * rapidB j := by
  rw [linearPrefix, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrj : r < j := Finset.mem_range.mp hr
  have hdpos : 0 < 3 * rapidB r ^ 2 :=
    Nat.mul_pos (by norm_num) (pow_pos (rapidB_pos r) _)
  rw [cast_nat_exact_div (a := rapidB j) (b := 3 * rapidB r ^ 2)
    hdpos (three_mul_rapidB_sq_dvd hrj)]
  norm_num
  ring

lemma phaseAlpha_mul_square {i h : ℕ} (hih : i ≤ h) :
    phaseAlpha h * (rapidB i : ℚ) ^ 2 =
      squarePrefix i + 1 / 3 + squareTail i h := by
  rw [phaseAlpha_split hih]
  have hi : (rapidB i : ℚ) ≠ 0 := by exact_mod_cast (rapidB_pos i).ne'
  have hp := cast_squarePrefix i
  have ht :
      (∑ r ∈ Finset.Ioc i h, 1 / (3 * (rapidB r : ℚ) ^ 2)) * rapidB i ^ 2 =
        squareTail i h := by
    rw [Finset.sum_mul, squareTail]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [add_mul, add_mul, Finset.sum_mul, ← hp, ht]
  field_simp

lemma phaseAlpha_mul_linear {j h : ℕ} (hjh : j ≤ h) :
    phaseAlpha h * (rapidB j : ℚ) = linearPrefix j + linearTail j h := by
  rw [phaseAlpha_split hjh]
  have hp := cast_linearPrefix j
  have hrest :
      (1 / (3 * (rapidB j : ℚ) ^ 2) +
        ∑ r ∈ Finset.Ioc j h, 1 / (3 * (rapidB r : ℚ) ^ 2)) * rapidB j =
          linearTail j h := by
    rw [add_mul, Finset.sum_mul, linearTail, ← Finset.Ioc_insert_left hjh]
    simp only [Finset.sum_insert, Finset.left_notMem_Ioc, not_false_eq_true]
    have hj : (rapidB j : ℚ) ≠ 0 := by exact_mod_cast (rapidB_pos j).ne'
    apply congrArg₂ (· + ·)
    · field_simp
    · apply Finset.sum_congr rfl
      intro r hr
      ring
  rw [add_mul, add_mul, Finset.sum_mul, ← hp]
  rw [add_assoc, ← add_mul, hrest]

def phaseError (i j h : ℕ) : ℚ :=
  squareTail i h + squareTail j h -
    2 * (rapidB i : ℚ) * linearTail j h

lemma phaseError_abs_le {i j h : ℕ} (hij : i < j) (hjh : j ≤ h) :
    |phaseError i j h| ≤ 1 / 39 := by
  have hih : i ≤ h := (Nat.le_of_lt hij).trans hjh
  have hTi := squareTail_bound hih
  have hTj := squareTail_bound hjh
  have hC := crossTail_bound hij hjh
  have hTi0 : 0 ≤ squareTail i h := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  have hTj0 : 0 ≤ squareTail j h := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  have hS0 : 0 ≤ linearTail j h := by
    apply Finset.sum_nonneg
    intro r hr
    positivity
  rw [abs_le]
  dsimp only [phaseError]
  constructor <;> nlinarith

lemma phase_middle_decomposition {i j h : ℕ} (hij : i < j) (hjh : j ≤ h) :
    ∃ z : ℤ,
      phaseAlpha h * ((rapidB j - rapidB i : ℕ) : ℚ) ^ 2 =
        (z : ℚ) + 2 / 3 + phaseError i j h := by
  have hih : i ≤ h := (Nat.le_of_lt hij).trans hjh
  have hbij : rapidB i ≤ rapidB j := (rapidB_strictMono hij).le
  have hsub : ((rapidB j - rapidB i : ℕ) : ℚ) =
      (rapidB j : ℚ) - rapidB i := by exact Nat.cast_sub hbij
  have hsi := phaseAlpha_mul_square hih
  have hsj := phaseAlpha_mul_square hjh
  have hlj := phaseAlpha_mul_linear hjh
  refine ⟨(squarePrefix i : ℤ) + squarePrefix j -
    2 * (rapidB i : ℤ) * linearPrefix j, ?_⟩
  rw [hsub]
  rw [show phaseAlpha h * ((rapidB j : ℚ) - rapidB i) ^ 2 =
      phaseAlpha h * (rapidB j : ℚ) ^ 2 +
        phaseAlpha h * (rapidB i : ℚ) ^ 2 -
          2 * (rapidB i : ℚ) * (phaseAlpha h * rapidB j) by ring]
  rw [hsi, hsj, hlj]
  push_cast
  dsimp only [phaseError]
  ring

lemma phaseError_middle {i j h : ℕ} (hij : i < j) (hjh : j ≤ h) :
    3 / 5 < (2 / 3 : ℚ) + phaseError i j h ∧
      (2 / 3 : ℚ) + phaseError i j h < 3 / 4 := by
  have herr := phaseError_abs_le hij hjh
  rw [abs_le] at herr
  constructor <;> nlinarith

lemma residue_middle_of_decomposition {x Q : ℕ} (hQ : 0 < Q) (z : ℤ) (u : ℚ)
    (hphase : (x : ℚ) / Q = (z : ℚ) + u)
    (hulo : 3 / 5 < u) (huhi : u < 3 / 4) :
    3 * Q < 5 * (x % Q) ∧ 4 * (x % Q) < 3 * Q := by
  let rho := x % Q
  let q := x / Q
  have hdecompN : rho + Q * q = x := by
    simpa [rho, q] using Nat.mod_add_div x Q
  have hdecompQ : (x : ℚ) / Q = (q : ℚ) + (rho : ℚ) / Q := by
    have hc : (rho : ℚ) + (Q : ℚ) * q = x := by exact_mod_cast hdecompN
    have hQc : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp
    nlinarith
  have hrho0 : (0 : ℚ) ≤ (rho : ℚ) / Q := by positivity
  have hrhoLt : (rho : ℚ) / Q < 1 := by
    apply (div_lt_one (by exact_mod_cast hQ)).2
    exact_mod_cast Nat.mod_lt x hQ
  let n : ℤ := z - (q : ℤ)
  have hrhoEq : (rho : ℚ) / Q = (n : ℚ) + u := by
    dsimp only [n]
    push_cast
    linarith
  have hnloQ : (-1 : ℚ) < (n : ℚ) := by nlinarith
  have hnhiQ : (n : ℚ) < 1 := by nlinarith
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast hnloQ
  have hnhi : n < (1 : ℤ) := by exact_mod_cast hnhiQ
  have hn : n = 0 := by omega
  have hrhoU : (rho : ℚ) / Q = u := by rw [hrhoEq, hn]; norm_num
  have hloFrac : (3 / 5 : ℚ) < (rho : ℚ) / Q := by simpa [hrhoU] using hulo
  have hhiFrac : (rho : ℚ) / Q < (3 / 4 : ℚ) := by simpa [hrhoU] using huhi
  have hloQ : (3 : ℚ) * Q < 5 * rho := by
    have := (div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 5)
      (by exact_mod_cast hQ : (0 : ℚ) < Q)).mp hloFrac
    nlinarith
  have hhiQ : (4 : ℚ) * rho < 3 * Q := by
    have := (div_lt_div_iff₀ (by exact_mod_cast hQ : (0 : ℚ) < Q)
      (by norm_num : (0 : ℚ) < 4)).mp hhiFrac
    nlinarith
  constructor
  · change 3 * Q < 5 * rho
    exact_mod_cast hloQ
  · change 4 * rho < 3 * Q
    exact_mod_cast hhiQ

/-- Every pair difference has its phase residue in the fixed interval `(3/5, 3/4)`. -/
lemma middlePhase_mod {i j h : ℕ} (hij : i < j) (hjh : j ≤ h) :
    let Q := phaseModulus h
    let p := phaseNumerator h
    let d := rapidB j - rapidB i
    let rho := (p * d ^ 2) % Q
    3 * Q < 5 * rho ∧ 4 * rho < 3 * Q := by
  dsimp only
  obtain ⟨z, hz⟩ := phase_middle_decomposition hij hjh
  have hu := phaseError_middle hij hjh
  let u : ℚ := 2 / 3 + phaseError i j h
  apply residue_middle_of_decomposition (phaseModulus_pos h) z u
  · dsimp only [u]
    calc
      ((phaseNumerator h * (rapidB j - rapidB i) ^ 2 : ℕ) : ℚ) / phaseModulus h =
          ((phaseNumerator h : ℚ) / phaseModulus h) *
            ((rapidB j - rapidB i : ℕ) : ℚ) ^ 2 := by
              norm_num [Nat.cast_mul, Nat.cast_pow]
              ring
      _ = phaseAlpha h * ((rapidB j - rapidB i : ℕ) : ℚ) ^ 2 := by
        rw [phaseNumerator_div_modulus]
      _ = (z : ℚ) + (2 / 3 + phaseError i j h) := by rw [hz]; ring
  · exact hu.1
  · exact hu.2

/-! ## A nilpotent quadratic shear over `ZMod` -/

section Shear

variable {R : Type*} [CommRing R]

/-- The quadratic shear `x ↦ x + c x (x - 1)`. -/
def shear (c x : R) : R := x + c * x * (x - 1)

/-- The inverse shear when `c² = 0`. -/
def unshear (c x : R) : R := x - c * x * (x - 1)

lemma shear_unshear (c x : R) (hc : c ^ 2 = 0) :
    shear c (unshear c x) = x := by
  have hc3 : c ^ 3 = 0 := by
    calc
      c ^ 3 = c ^ 2 * c := by ring
      _ = 0 := by rw [hc, zero_mul]
  simp only [shear, unshear]
  ring_nf
  simp [hc, hc3]

lemma unshear_shear (c x : R) (hc : c ^ 2 = 0) :
    unshear c (shear c x) = x := by
  have hc3 : c ^ 3 = 0 := by
    calc
      c ^ 3 = c ^ 2 * c := by ring
      _ = 0 := by rw [hc, zero_mul]
  simp only [shear, unshear]
  ring_nf
  simp [hc, hc3]

lemma shear_secondDifference (c x d : R) :
    shear c (x + 2 * d) - 2 * shear c (x + d) + shear c x = 2 * c * d ^ 2 := by
  simp only [shear]
  ring

/-- The shear as an equivalence when its coefficient is square-zero. -/
def shearEquiv (c : R) (hc : c ^ 2 = 0) : R ≃ R where
  toFun := shear c
  invFun := unshear c
  left_inv := fun x ↦ unshear_shear c x hc
  right_inv := fun x ↦ shear_unshear c x hc

end Shear

section ZModShear

/-- The modulus used for the finite skew shift. -/
abbrev phasePeriod (Q : ℕ) : ℕ := Q ^ 2

/-- A square-zero coefficient whose double is `Q * p` modulo `Q²`. -/
def phaseCoeff (Q p : ℕ) : ZMod (phasePeriod Q) :=
  (Q : ZMod (phasePeriod Q)) * (p : ZMod (phasePeriod Q)) *
    (2 : ZMod (phasePeriod Q))⁻¹

lemma Q_sq_eq_zero (Q : ℕ) : (Q : ZMod (phasePeriod Q)) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  simp [phasePeriod]

lemma phaseCoeff_sq_eq_zero (Q p : ℕ) : (phaseCoeff Q p) ^ 2 = 0 := by
  rw [phaseCoeff, mul_pow, mul_pow, Q_sq_eq_zero]
  simp

lemma two_mul_phaseCoeff (Q p : ℕ) (hQ : Odd Q) :
    2 * phaseCoeff Q p = (Q * p : ℕ) := by
  have hP : Odd (phasePeriod Q) := by
    simpa [phasePeriod] using hQ.pow
  have hu : IsUnit (2 : ZMod (phasePeriod Q)) :=
    (ZMod.isUnit_iff_coprime 2 (phasePeriod Q)).2
      (Nat.coprime_two_left.mpr hP)
  rw [phaseCoeff]
  calc
    2 * ((Q : ZMod (phasePeriod Q)) * (p : ZMod (phasePeriod Q)) *
        (2 : ZMod (phasePeriod Q))⁻¹) =
        (Q : ZMod (phasePeriod Q)) * (p : ZMod (phasePeriod Q)) *
          ((2 : ZMod (phasePeriod Q)) * (2 : ZMod (phasePeriod Q))⁻¹) := by ring
    _ = (Q : ZMod (phasePeriod Q)) * (p : ZMod (phasePeriod Q)) := by
      rw [ZMod.mul_inv_of_unit _ hu, mul_one]
    _ = (Q * p : ℕ) := by simp

/-- The finite quadratic shear permutation. -/
def phaseEquiv (Q p : ℕ) : ZMod (phasePeriod Q) ≃ ZMod (phasePeriod Q) :=
  shearEquiv (phaseCoeff Q p) (phaseCoeff_sq_eq_zero Q p)

@[simp] lemma phaseEquiv_apply (Q p : ℕ) (x : ZMod (phasePeriod Q)) :
    phaseEquiv Q p x = shear (phaseCoeff Q p) x := rfl

@[simp] lemma phaseEquiv_symm_apply (Q p : ℕ) (x : ZMod (phasePeriod Q)) :
    (phaseEquiv Q p).symm x = unshear (phaseCoeff Q p) x := rfl

lemma phaseEquiv_secondDifference (Q p : ℕ) (hQ : Odd Q)
    (x d : ZMod (phasePeriod Q)) :
    phaseEquiv Q p (x + 2 * d) - 2 * phaseEquiv Q p (x + d) +
        phaseEquiv Q p x = (Q * p : ℕ) * d ^ 2 := by
  rw [phaseEquiv_apply, phaseEquiv_apply, phaseEquiv_apply,
    shear_secondDifference, two_mul_phaseCoeff Q p hQ]

end ZModShear

/-! ## Dense finite blocks selected by a permutation -/

/-- The integer in block `u` selected by the residue labelled `y`. -/
def blockPoint (P : ℕ) (e : ZMod P ≃ ZMod P) (uy : ℕ × ℕ) : ℕ :=
  uy.1 * P + (e.symm (uy.2 : ZMod P)).val + 1

/-- `t` complete blocks, taking labels `0, ..., L - 1` in every block. -/
def blockFinset (P t L : ℕ) (e : ZMod P ≃ ZMod P) : Finset ℕ :=
  ((Finset.range t).product (Finset.range L)).image (blockPoint P e)

lemma blockPoint_injOn (P t L : ℕ) (e : ZMod P ≃ ZMod P)
    (hP : 0 < P) (hLP : L ≤ P) :
    Set.InjOn (blockPoint P e)
      (((Finset.range t).product (Finset.range L) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  let _ : NeZero P := ⟨Nat.ne_of_gt hP⟩
  intro a ha b hb hab
  have ha' : a.1 < t ∧ a.2 < L := by simpa using ha
  have hb' : b.1 < t ∧ b.2 < L := by simpa using hb
  have hraw :
      a.1 * P + (e.symm (a.2 : ZMod P)).val =
        b.1 * P + (e.symm (b.2 : ZMod P)).val := by
    simpa [blockPoint] using hab
  have hcore :
      (e.symm (a.2 : ZMod P)).val + P * a.1 =
        (e.symm (b.2 : ZMod P)).val + P * b.1 := by
    simpa [Nat.add_comm, Nat.mul_comm] using hraw
  have hfirst : a.1 = b.1 := by
    have hdiv := congrArg (fun n : ℕ ↦ n / P) hcore
    simpa [Nat.add_mul_div_left, hP, Nat.div_eq_of_lt (ZMod.val_lt _)] using hdiv
  have hres :
      (e.symm (a.2 : ZMod P)).val = (e.symm (b.2 : ZMod P)).val := by
    rw [hfirst] at hcore
    exact Nat.add_right_cancel hcore
  have hcast : (a.2 : ZMod P) = (b.2 : ZMod P) := by
    apply e.symm.injective
    exact (ZMod.val_injective P) hres
  have hsecond : a.2 = b.2 := by
    have hvals := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le ha'.2 hLP),
      Nat.mod_eq_of_lt (lt_of_lt_of_le hb'.2 hLP)] using hvals
  exact Prod.ext hfirst hsecond

lemma card_blockFinset (P t L : ℕ) (e : ZMod P ≃ ZMod P)
    (hP : 0 < P) (hLP : L ≤ P) :
    (blockFinset P t L e).card = t * L := by
  rw [blockFinset, Finset.card_image_iff.mpr (blockPoint_injOn P t L e hP hLP)]
  simp

lemma blockFinset_subset_Icc (P t L : ℕ) (e : ZMod P ≃ ZMod P)
    (hP : 0 < P) :
    blockFinset P t L e ⊆ Finset.Icc 1 (t * P) := by
  let _ : NeZero P := ⟨Nat.ne_of_gt hP⟩
  intro x hx
  rw [blockFinset, Finset.mem_image] at hx
  obtain ⟨uy, huy, rfl⟩ := hx
  have huy' : uy.1 < t ∧ uy.2 < L := by simpa using huy
  have hu : uy.1 < t := huy'.1
  have hr : (e.symm (uy.2 : ZMod P)).val < P := ZMod.val_lt _
  rw [Finset.mem_Icc]
  constructor
  · simp [blockPoint]
  · calc
      blockPoint P e uy ≤ uy.1 * P + P := by
        simp only [blockPoint]
        exact Nat.add_le_add_left (Nat.succ_le_iff.mpr hr) _
      _ = (uy.1 + 1) * P := by simp [Nat.add_mul]
      _ ≤ t * P := Nat.mul_le_mul_right P (Nat.succ_le_iff.mpr hu)

lemma mem_blockFinset_iff (P t L : ℕ) (e : ZMod P ≃ ZMod P) (x : ℕ) :
    x ∈ blockFinset P t L e ↔
      ∃ u < t, ∃ y < L, x = u * P + (e.symm (y : ZMod P)).val + 1 := by
  rw [blockFinset, Finset.mem_image]
  constructor
  · rintro ⟨uy, huy, rfl⟩
    have huy' : uy.1 < t ∧ uy.2 < L := by simpa using huy
    rcases huy' with ⟨hu, hy⟩
    exact ⟨uy.1, hu, uy.2, hy, rfl⟩
  · rintro ⟨u, hu, y, hy, rfl⟩
    exact ⟨(u, y), by simp [hu, hy], rfl⟩

/-- The first `m` shifted values of `rapidB`. -/
def differenceSet (m : ℕ) : Finset ℕ :=
  (Finset.range m).image fun i ↦ rapidB i + 1

lemma card_differenceSet (m : ℕ) : (differenceSet m).card = m := by
  rw [differenceSet, Finset.card_image_iff.mpr]
  · simp
  · exact (rapidB_strictMono.add_const 1).injective.injOn

lemma mem_differenceSet_iff (m x : ℕ) :
    x ∈ differenceSet m ↔ ∃ i < m, rapidB i + 1 = x := by
  simp [differenceSet]

/-! ## The modular obstruction to a three-term progression -/

lemma block_member_phase_label {P t L : ℕ} [NeZero P]
    (e : ZMod P ≃ ZMod P) {x : ℕ}
    (hx : x ∈ blockFinset P t L e) :
    ∃ y < L, e ((x : ZMod P) - 1) = (y : ZMod P) := by
  rw [mem_blockFinset_iff] at hx
  obtain ⟨u, hu, y, hy, rfl⟩ := hx
  refine ⟨y, hy, ?_⟩
  have hres :
      (((u * P + (e.symm (y : ZMod P)).val + 1 : ℕ) : ZMod P) - 1) =
        e.symm (y : ZMod P) := by
    simp [Nat.cast_add, Nat.cast_mul]
  rw [hres]
  simp

/-- Three selected block points cannot form a progression when the
quadratic phase of its difference lies in the middle arc. -/
lemma no_three_ap_of_middlePhase
    (Q p t x d : ℕ) (hQ : Odd Q)
    (hx₀ : x ∈ blockFinset (phasePeriod Q) t
      (phasePeriod Q / 100) (phaseEquiv Q p))
    (hx₁ : x + d ∈ blockFinset (phasePeriod Q) t
      (phasePeriod Q / 100) (phaseEquiv Q p))
    (hx₂ : x + 2 * d ∈ blockFinset (phasePeriod Q) t
      (phasePeriod Q / 100) (phaseEquiv Q p))
    (hlo : 3 * Q < 5 * ((p * d ^ 2) % Q))
    (hhi : 4 * ((p * d ^ 2) % Q) < 3 * Q) : False := by
  let P := phasePeriod Q
  let L := P / 100
  let rho := (p * d ^ 2) % Q
  have hQpos : 0 < Q := hQ.pos
  have hPpos : 0 < P := by
    dsimp only [P, phasePeriod]
    positivity
  let _ : NeZero P := ⟨hPpos.ne'⟩
  change x ∈ blockFinset P t L (phaseEquiv Q p) at hx₀
  change x + d ∈ blockFinset P t L (phaseEquiv Q p) at hx₁
  change x + 2 * d ∈ blockFinset P t L (phaseEquiv Q p) at hx₂
  obtain ⟨y₀, hy₀, hlabel₀⟩ := block_member_phase_label (phaseEquiv Q p) hx₀
  obtain ⟨y₁, hy₁, hlabel₁⟩ := block_member_phase_label (phaseEquiv Q p) hx₁
  obtain ⟨y₂, hy₂, hlabel₂⟩ := block_member_phase_label (phaseEquiv Q p) hx₂
  let X : ZMod P := (x : ZMod P) - 1
  have hX₁ : X + (d : ZMod P) = ((x + d : ℕ) : ZMod P) - 1 := by
    dsimp only [X]
    push_cast
    ring
  have hX₂ : X + 2 * (d : ZMod P) = ((x + 2 * d : ℕ) : ZMod P) - 1 := by
    dsimp only [X]
    push_cast
    ring
  have hshear := phaseEquiv_secondDifference Q p hQ X (d : ZMod P)
  rw [hX₂, hX₁, hlabel₂, hlabel₁] at hshear
  change phaseEquiv Q p X = (y₀ : ZMod P) at hlabel₀
  rw [hlabel₀] at hshear
  have hmod : Q * (p * d ^ 2) ≡ Q * rho [MOD P] := by
    convert ((Nat.mod_modEq (p * d ^ 2) Q).symm.mul_left' Q) using 1
    simp [P, pow_two]
  have hcast :
      ((Q * (p * d ^ 2) : ℕ) : ZMod P) = ((Q * rho : ℕ) : ZMod P) :=
    (ZMod.natCast_eq_natCast_iff _ _ P).2 hmod
  let z : ℤ := (y₂ : ℤ) - 2 * y₁ + y₀
  have hzmod : ((Q * rho : ℕ) : ZMod P) = (z : ZMod P) := by
    calc
      ((Q * rho : ℕ) : ZMod P) = ((Q * (p * d ^ 2) : ℕ) : ZMod P) := hcast.symm
      _ = ((Q * p : ℕ) : ZMod P) * (d : ZMod P) ^ 2 := by
        push_cast
        ring
      _ = (y₂ : ZMod P) - 2 * (y₁ : ZMod P) + (y₀ : ZMod P) := hshear.symm
      _ = (z : ZMod P) := by
        dsimp only [z]
        push_cast
        ring
  have hdiv₀ : (P : ℤ) ∣ z - (Q * rho : ℕ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((Q * rho : ℕ) : ℤ) z P).mp
    simpa using hzmod
  have hdiv : (P : ℤ) ∣ (Q * rho : ℕ) - z := by
    have hn := dvd_neg.mpr hdiv₀
    simpa [neg_sub] using hn
  have hzlo : (-2 : ℤ) * L < z := by
    dsimp only [z]
    omega
  have hzhi : z < 2 * (L : ℤ) := by
    dsimp only [z]
    omega
  have hLP : 100 * L ≤ P := by
    dsimp only [L]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self P 100
  have hlo' : 3 * P < 5 * (Q * rho) := by
    dsimp only [P, rho, phasePeriod] at ⊢
    nlinarith [hlo]
  have hhi' : 4 * (Q * rho) < 3 * P := by
    dsimp only [P, rho, phasePeriod] at ⊢
    nlinarith [hhi]
  have hwpos : (0 : ℤ) < (Q * rho : ℕ) - z := by
    have hLPz : (100 : ℤ) * L ≤ P := by exact_mod_cast hLP
    have hloz : (3 : ℤ) * P < 5 * (Q * rho) := by exact_mod_cast hlo'
    norm_num [Nat.cast_mul] at ⊢
    nlinarith
  have hwlt : ((Q * rho : ℕ) : ℤ) - z < P := by
    have hLPz : (100 : ℤ) * L ≤ P := by exact_mod_cast hLP
    have hhiz : (4 : ℤ) * (Q * rho) < 3 * P := by exact_mod_cast hhi'
    norm_num [Nat.cast_mul] at ⊢
    nlinarith
  have hwzero : ((Q * rho : ℕ) : ℤ) - z = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt hwpos.le hwlt hdiv
  nlinarith

lemma phasePeriod_ge_two_hundred (h : ℕ) :
    200 ≤ phasePeriod (phaseModulus h) := by
  have hb := rapidB_ge_twenty_seven h
  have hb2 : 27 ^ 2 ≤ rapidB h ^ 2 := Nat.pow_le_pow_left hb 2
  have hQ : 3 * 27 ^ 2 ≤ 3 * rapidB h ^ 2 := Nat.mul_le_mul_left 3 hb2
  have hP : (3 * 27 ^ 2) ^ 2 ≤ (3 * rapidB h ^ 2) ^ 2 :=
    Nat.pow_le_pow_left hQ 2
  change 200 ≤ (3 * rapidB h ^ 2) ^ 2
  exact (show 200 ≤ (3 * 27 ^ 2) ^ 2 by norm_num).trans hP

lemma phaseModulus_ge_ten (h : ℕ) : 10 ≤ phaseModulus h := by
  have hb := rapidB_ge_twenty_seven h
  have hb2 : 27 ^ 2 ≤ rapidB h ^ 2 := Nat.pow_le_pow_left hb 2
  have hQ : 3 * 27 ^ 2 ≤ 3 * rapidB h ^ 2 := Nat.mul_le_mul_left 3 hb2
  change 10 ≤ 3 * rapidB h ^ 2
  exact (show 10 ≤ 3 * 27 ^ 2 by norm_num).trans hQ

lemma block_density_bound_real {P t : ℕ} (hP : 200 ≤ P) :
    ((t * P : ℕ) : ℝ) / 200 ≤ (t * (P / 100) : ℕ) := by
  have hbase : P ≤ 200 * (P / 100) := by omega
  have hmul : t * P ≤ 200 * (t * (P / 100)) := by
    calc
      t * P ≤ t * (200 * (P / 100)) := Nat.mul_le_mul_left t hbase
      _ = 200 * (t * (P / 100)) := by ring
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200)).2
  have hmul' : t * P ≤ t * (P / 100) * 200 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact_mod_cast hmul'

lemma differenceSet_subset_Icc (m N : ℕ) (hN : rapidB m + 1 ≤ N) :
    differenceSet m ⊆ Finset.Icc 1 N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := (mem_differenceSet_iff m x).mp hx
  rw [Finset.mem_Icc]
  constructor
  · omega
  · exact Nat.add_le_add_right
      (rapidB_strictMono.monotone (Nat.le_of_lt hi)) 1 |>.trans hN

/-! ## The finite counterexamples and the negative answer -/

/-- For every proposed threshold and cutoff, the explicit periodic
construction supplies a counterexample at `k = 3` and density `1/200`. -/
theorem finite_counterexample (m N₀ : ℕ) (hm : 1 ≤ m) :
    ∃ N A B, N₀ ≤ N ∧
      A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
      (1 / 200 : ℝ) * N ≤ (A.card : ℝ) ∧ m ≤ B.card ∧
      ¬ HasAPWithStepInDiff 3 A B := by
  let h := m - 1
  let Q := phaseModulus h
  let p := phaseNumerator h
  let P := phasePeriod Q
  let L := P / 100
  let t := N₀ + 1
  let N := t * P
  let A := blockFinset P t L (phaseEquiv Q p)
  let B := differenceSet m
  have hQpos : 0 < Q := by simpa [Q] using phaseModulus_pos h
  have hQodd : Odd Q := by simpa [Q] using phaseModulus_odd h
  have hPpos : 0 < P := by dsimp only [P, phasePeriod]; positivity
  have hP200 : 200 ≤ P := by simpa [P, Q] using phasePeriod_ge_two_hundred h
  have htpos : 0 < t := by simp [t]
  refine ⟨N, A, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [N]
    have hPle : 1 ≤ P := hPpos
    calc
      N₀ ≤ t := by simp [t]
      _ = t * 1 := by simp
      _ ≤ t * P := Nat.mul_le_mul_left t hPle
  · exact blockFinset_subset_Icc P t L (phaseEquiv Q p) hPpos
  · apply differenceSet_subset_Icc m N
    have hmh : m = h + 1 := by simp [h, Nat.sub_add_cancel hm]
    have hbQ : rapidB m = 9 * Q := by
      rw [hmh, rapidB_succ]
      simp only [Q, phaseModulus]
      ring
    have hQN : Q ≤ N := by
      dsimp only [N, P, phasePeriod]
      nlinarith
    have hBmP : rapidB m + 1 ≤ P := by
      rw [hbQ]
      dsimp only [P, phasePeriod]
      have hQlarge : 10 ≤ Q := by
        simpa [Q] using phaseModulus_ge_ten h
      nlinarith
    exact hBmP.trans (by
      dsimp only [N]
      exact Nat.le_mul_of_pos_left P htpos)
  · have hcard : A.card = t * L := by
      exact card_blockFinset P t L (phaseEquiv Q p) hPpos (Nat.div_le_self P 100)
    rw [hcard]
    change (1 / 200 : ℝ) * (t * P : ℕ) ≤ (t * L : ℕ)
    have hdens := block_density_bound_real (t := t) hP200
    norm_num at hdens ⊢
    nlinarith
  · simp [B, card_differenceSet]
  · intro hap
    rcases hap with ⟨a, d, hd, hA, b₁, hb₁, b₂, hb₂, hdB⟩
    have ha₀ : a ∈ A := by
      simpa only [zero_mul, Nat.add_zero] using hA 0 (by omega)
    have ha₁ : a + d ∈ A := by simpa using hA 1 (by omega)
    have ha₂ : a + 2 * d ∈ A := by simpa using hA 2 (by omega)
    obtain ⟨i, hi, hiB⟩ := (mem_differenceSet_iff m b₁).mp (by simpa [B] using hb₁)
    obtain ⟨j, hj, hjB⟩ := (mem_differenceSet_iff m b₂).mp (by simpa [B] using hb₂)
    have hdij : d = rapidB i - rapidB j := by omega
    have hji : j < i := by
      by_contra hnot
      have hle : rapidB i ≤ rapidB j :=
        rapidB_strictMono.monotone (Nat.le_of_not_gt hnot)
      omega
    have hih : i ≤ h := by dsimp only [h]; omega
    have hphase := middlePhase_mod hji hih
    dsimp only at hphase
    rw [← hdij] at hphase
    exact no_three_ap_of_middlePhase Q p t a d hQodd
      (by simpa [A, P, L, Q, p] using ha₀)
      (by simpa [A, P, L, Q, p] using ha₁)
      (by simpa [A, P, L, Q, p] using ha₂)
      (by simpa [Q, p, h] using hphase.1)
      (by simpa [Q, p, h] using hphase.2)

/-- Erdős Problem 1185 has a negative answer. -/
theorem not_erdos_1185 : ¬ (∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
  ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A B : Finset ℕ,
      A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
      δ * (N : ℝ) ≤ (A.card : ℝ) → m ≤ B.card →
  Erdos1185.HasAPWithStepInDiff k A B) := by
  intro hstatement
  · rcases hstatement (1 / 200) (by norm_num) 3 (by omega) with
      ⟨m, hm, N₀, hall⟩
    obtain ⟨N, A, B, hN, hA, hB, hcardA, hcardB, hno⟩ :=
      finite_counterexample m N₀ hm
    exact hno (hall N hN A B hA hB hcardA hcardB)

end Erdos1185

alias _root_.Erdos1185.erdos_1185 := _root_.Erdos1185.not_erdos_1185
