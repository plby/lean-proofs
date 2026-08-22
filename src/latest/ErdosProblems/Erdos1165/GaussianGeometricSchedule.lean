/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianMultiBlockProfile

/-!
# A genuine fixed-cutoff geometric schedule for HLOZ (A.12)

Starting at a fixed scale `K`, successive complete blocks occupy
`[K,2K-1]`, `[2K,4K-1]`, and so on.  The last block is truncated at the
requested terminal scale `n`.  Hence the centered prefix stops at the fixed
cutoff `K`; every later Gaussian normalizer is recovered by summing paths.
-/

namespace Erdos1165.GaussianGeometricSchedule

noncomputable section

open GaussianBlockFactorization GaussianMultiBlockProfile

/-- Radius used at a geometric block beginning at `s`, specialized to the
HLOZ exponent `1+delta=6/5`. -/
def geometricRadius (s : ℕ) : ℕ :=
  ⌊(s : ℝ) ^ (6 / 5 : ℝ) / 16⌋₊

/-- A complete geometric block from `s` through `2s-1`. -/
def completeGeometricBlock (s : ℕ) : GaussianBlock where
  start := s
  steps := s - 1
  radius := geometricRadius s

/-- The terminal block from `s` through `n`. -/
def terminalGeometricBlock (s n : ℕ) : GaussianBlock where
  start := s
  steps := n - s
  radius := geometricRadius s

/-- `J` complete doublings followed by the block truncated at `n`. -/
def geometricSchedule : ℕ → ℕ → ℕ → List GaussianBlock
  | s, 0, n => [terminalGeometricBlock s n]
  | s, J + 1, n => completeGeometricBlock s :: geometricSchedule (2 * s) J n

@[simp] lemma geometricSchedule_zero (s n : ℕ) :
    geometricSchedule s 0 n = [terminalGeometricBlock s n] := rfl

@[simp] lemma geometricSchedule_succ (s J n : ℕ) :
    geometricSchedule s (J + 1) n =
      completeGeometricBlock s :: geometricSchedule (2 * s) J n := rfl

@[simp] lemma completeGeometricBlock_start (s : ℕ) :
    (completeGeometricBlock s).start = s := rfl

@[simp] lemma completeGeometricBlock_steps (s : ℕ) :
    (completeGeometricBlock s).steps = s - 1 := rfl

@[simp] lemma completeGeometricBlock_end {s : ℕ} (hs : 1 ≤ s) :
    (completeGeometricBlock s).start + (completeGeometricBlock s).steps =
      2 * s - 1 := by
  simp only [completeGeometricBlock]
  omega

@[simp] lemma terminalGeometricBlock_start (s n : ℕ) :
    (terminalGeometricBlock s n).start = s := rfl

@[simp] lemma terminalGeometricBlock_steps (s n : ℕ) :
    (terminalGeometricBlock s n).steps = n - s := rfl

@[simp] lemma terminalGeometricBlock_end {s n : ℕ} (hsn : s ≤ n) :
    (terminalGeometricBlock s n).start + (terminalGeometricBlock s n).steps = n := by
  simp only [terminalGeometricBlock]
  exact Nat.add_sub_of_le hsn

lemma geometricSchedule_head_start (s J n : ℕ) :
    (geometricSchedule s J n).head?.map GaussianBlock.start = some s := by
  cases J <;> rfl

lemma geometricSchedule_ne_nil (s J n : ℕ) :
    geometricSchedule s J n ≠ [] := by
  cases J <;> simp

/-- The dyadic list is genuinely consecutive. -/
theorem geometricSchedule_consecutive {s J n : ℕ}
    (hs : 1 ≤ s) (hterminal : 2 ^ J * s ≤ n) :
    ConsecutiveBlocks (geometricSchedule s J n) := by
  induction J generalizing s with
  | zero => simp [geometricSchedule, ConsecutiveBlocks]
  | succ J ih =>
      rw [geometricSchedule_succ]
      cases J with
      | zero =>
          simp only [geometricSchedule_zero, ConsecutiveBlocks,
            terminalGeometricBlock_start, completeGeometricBlock_start,
            completeGeometricBlock_steps]
          refine ⟨?_, trivial⟩
          clear hterminal
          omega
      | succ j =>
          simp only [geometricSchedule_succ, ConsecutiveBlocks,
            completeGeometricBlock_start]
          constructor
          · simp only [completeGeometricBlock_steps]
            omega
          · apply ih (by omega)
            simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hterminal

/-- The geometric schedule ends exactly at `n`. -/
theorem geometricSchedule_end {s J n : ℕ}
    (hterminal : 2 ^ J * s ≤ n) :
    gaussianBlocksEnd (geometricSchedule s J n) = n := by
  induction J generalizing s with
  | zero =>
      simp only [geometricSchedule_zero, gaussianBlocksEnd]
      apply terminalGeometricBlock_end
      simpa using hterminal
  | succ J ih =>
      rw [geometricSchedule_succ]
      cases J with
      | zero =>
          simp only [geometricSchedule_zero, gaussianBlocksEnd]
          apply terminalGeometricBlock_end
          simpa [pow_succ] using hterminal
      | succ j =>
          simp only [geometricSchedule_succ, gaussianBlocksEnd]
          apply ih
          simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hterminal

/-- Every start in the schedule is at least its fixed cutoff. -/
lemma geometricSchedule_start_ge {s J n : ℕ} (hs : 1 ≤ s) :
    ∀ b ∈ geometricSchedule s J n, s ≤ b.start := by
  induction J generalizing s with
  | zero =>
      intro b hb
      simp only [geometricSchedule_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      subst b
      simp
  | succ J ih =>
      intro b hb
      rw [geometricSchedule_succ] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp
      · exact (show s ≤ 2 * s by omega).trans (ih (by omega) b hb)

/-- If the terminal start is at most `n`, every block starts at most `n`. -/
lemma geometricSchedule_start_le_terminal {s J n : ℕ}
    (hterminal : 2 ^ J * s ≤ n) :
    ∀ b ∈ geometricSchedule s J n, b.start ≤ n := by
  induction J generalizing s with
  | zero =>
      intro b hb
      simp only [geometricSchedule_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      subst b
      simpa using hterminal
  | succ J ih =>
      intro b hb
      rw [geometricSchedule_succ] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp only [completeGeometricBlock_start]
        have : s ≤ 2 ^ (J + 1) * s := by
          have : 1 ≤ 2 ^ (J + 1) := Nat.one_le_pow _ _ (by omega)
          nlinarith
        exact this.trans hterminal
      · apply ih (b := b) ?_ hb
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hterminal

/-- Under the usual truncation condition, every block has length at most
its start and endpoint at most twice its start. -/
lemma geometricSchedule_steps_le_start {s J n : ℕ}
    (hupper : n < 2 * (2 ^ J * s)) :
    ∀ b ∈ geometricSchedule s J n, b.steps ≤ b.start := by
  induction J generalizing s with
  | zero =>
      intro b hb
      simp only [geometricSchedule_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      subst b
      simp only [terminalGeometricBlock_steps, terminalGeometricBlock_start]
      omega
  | succ J ih =>
      intro b hb
      rw [geometricSchedule_succ] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · simp only [completeGeometricBlock_steps, completeGeometricBlock_start]
        omega
      · apply ih (b := b) ?_ hb
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hupper

/-- Consequently every block endpoint is at most twice its start. -/
lemma geometricSchedule_end_le_two_start {s J n : ℕ}
    (hupper : n < 2 * (2 ^ J * s)) :
    ∀ b ∈ geometricSchedule s J n,
      b.start + b.steps ≤ 2 * b.start := by
  intro b hb
  have := geometricSchedule_steps_le_start hupper b hb
  omega

/-- Number of blocks in the explicit schedule. -/
@[simp] lemma geometricSchedule_length (s J n : ℕ) :
    (geometricSchedule s J n).length = J + 1 := by
  induction J generalizing s with
  | zero => simp [geometricSchedule]
  | succ J ih => simp [geometricSchedule, ih]

/-! ## Radius, envelope, and spectral estimates -/

lemma geometricRadius_lower {s : ℕ} (hs : 32 ≤ s) :
    (s : ℝ) ^ (6 / 5 : ℝ) / 32 ≤ geometricRadius s := by
  let y : ℝ := (s : ℝ) ^ (6 / 5 : ℝ) / 16
  have hsOne : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hpow : (s : ℝ) ≤ (s : ℝ) ^ (6 / 5 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hsOne (by norm_num : (1 : ℝ) ≤ 6 / 5)
  have hyTwo : 2 ≤ y := by
    dsimp only [y]
    have hsReal : (32 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hfloor := Nat.lt_floor_add_one y
  have hfloorOneNat : 1 ≤ ⌊y⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloorOne : (1 : ℝ) ≤ (⌊y⌋₊ : ℕ) := by exact_mod_cast hfloorOneNat
  have hy : y / 2 ≤ (⌊y⌋₊ : ℕ) := by linarith
  change (s : ℝ) ^ (6 / 5 : ℝ) / 32 ≤
    (⌊(s : ℝ) ^ (6 / 5 : ℝ) / 16⌋₊ : ℕ)
  convert hy using 1 <;> simp only [y] <;> ring

lemma geometricRadius_le {s : ℕ} :
    (geometricRadius s : ℝ) ≤ (s : ℝ) ^ (6 / 5 : ℝ) / 16 := by
  exact Nat.floor_le (by positivity)

private lemma rpow_six_fifths_sq {x : ℝ} (hx : 0 < x) :
    (x ^ (6 / 5 : ℝ)) ^ 2 = x ^ 2 * x ^ (2 / 5 : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le,
    show (6 / 5 : ℝ) * 2 = 2 + 2 / 5 by norm_num,
    Real.rpow_add hx, Real.rpow_two]

lemma geometricRadius_le_envelope {s l : ℕ}
    (hsl : s ≤ l) :
    (geometricRadius s : ℝ) ≤ (l : ℝ) ^ (6 / 5 : ℝ) := by
  calc
    (geometricRadius s : ℝ) ≤ (s : ℝ) ^ (6 / 5 : ℝ) / 16 :=
      geometricRadius_le
    _ ≤ (s : ℝ) ^ (6 / 5 : ℝ) := by
      have hp : 0 ≤ (s : ℝ) ^ (6 / 5 : ℝ) := by positivity
      nlinarith
    _ ≤ (l : ℝ) ^ (6 / 5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsl) (by norm_num)

lemma geometricRadius_le_center {s l : ℕ}
    (hs : 1 ≤ s) (hsl : s ≤ l) :
    geometricRadius s ≤ AppendixFirstMoment.profileCenter l := by
  have hw := geometricRadius_le_envelope hsl
  have hlOne : (1 : ℝ) ≤ l := by exact_mod_cast hs.trans hsl
  have hp : (l : ℝ) ^ (6 / 5 : ℝ) ≤ (l : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlOne (by norm_num)
  rw [Real.rpow_two] at hp
  have hr : (geometricRadius s : ℝ) ≤
      (AppendixFirstMoment.profileCenter l : ℕ) := by
    simp only [AppendixFirstMoment.profileCenter]
    push_cast
    nlinarith [sq_nonneg (l : ℝ)]
  exact_mod_cast hr

lemma geometricBlock_scale {b : GaussianBlock}
    (hstart : 32 ≤ b.start)
    (hend : b.start + b.steps ≤ 2 * b.start)
    (hradius : b.radius = geometricRadius b.start)
    (hlarge : (2560 * 4096 : ℝ) ≤
      (b.start : ℝ) ^ (2 / 5 : ℝ)) :
    (2560 : ℝ) * (b.start + b.steps : ℕ) ^ 2 ≤
      (b.radius : ℝ) ^ 2 := by
  have hspos : (0 : ℝ) < b.start := by positivity
  have hR := geometricRadius_lower hstart
  rw [hradius]
  have hRsq : ((b.start : ℝ) ^ (6 / 5 : ℝ) / 32) ^ 2 ≤
      (geometricRadius b.start : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR 2
  have hpow : ((b.start : ℝ) ^ (6 / 5 : ℝ) / 32) ^ 2 =
      (b.start : ℝ) ^ 2 * (b.start : ℝ) ^ (2 / 5 : ℝ) / 1024 := by
    rw [div_pow, rpow_six_fifths_sq hspos]
    norm_num
  rw [hpow] at hRsq
  have hendReal : ((b.start + b.steps : ℕ) : ℝ) ≤ 2 * b.start := by
    exact_mod_cast hend
  have hendSq : (((b.start + b.steps : ℕ) : ℝ)) ^ 2 ≤
      (2 * (b.start : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hendReal 2
  calc
    (2560 : ℝ) * (((b.start + b.steps : ℕ) : ℝ)) ^ 2 ≤
        2560 * (2 * (b.start : ℝ)) ^ 2 := by gcongr
    _ ≤ (b.start : ℝ) ^ 2 * (b.start : ℝ) ^ (2 / 5 : ℝ) / 1024 := by
      nlinarith [sq_nonneg (b.start : ℝ)]
    _ ≤ (geometricRadius b.start : ℝ) ^ 2 := hRsq

lemma geometricSchedule_radius_eq {s J n : ℕ} :
    ∀ b ∈ geometricSchedule s J n,
      b.radius = geometricRadius b.start := by
  induction J generalizing s with
  | zero =>
      intro b hb
      simp only [geometricSchedule_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      subst b
      rfl
  | succ J ih =>
      intro b hb
      rw [geometricSchedule_succ] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rfl
      · exact ih b hb

theorem geometricSchedule_scale {s J n : ℕ}
    (hs : 32 ≤ s)
    (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s))
    (hlarge : (2560 * 4096 : ℝ) ≤ (s : ℝ) ^ (2 / 5 : ℝ)) :
    ∀ b ∈ geometricSchedule s J n,
      (2560 : ℝ) * (b.start + b.steps : ℕ) ^ 2 ≤ (b.radius : ℝ) ^ 2 := by
  intro b hb
  have hsb := geometricSchedule_start_ge (show 1 ≤ s by omega) b hb
  have hlargeB : (2560 * 4096 : ℝ) ≤
      (b.start : ℝ) ^ (2 / 5 : ℝ) := hlarge.trans
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hsb) (by norm_num))
  exact geometricBlock_scale (hs.trans hsb)
    (geometricSchedule_end_le_two_start hupper b hb)
    (geometricSchedule_radius_eq b hb) hlargeB

theorem geometricSchedule_width_center {s J n : ℕ} (hs : 1 ≤ s) :
    (∀ b ∈ geometricSchedule s J n, ∀ l,
      BlockContains b l → b.radius ≤ AppendixFirstMoment.profileCenter l) ∧
    (∀ b ∈ geometricSchedule s J n, ∀ l,
      BlockContains b l → (b.radius : ℝ) ≤ (l : ℝ) ^ (6 / 5 : ℝ)) := by
  constructor
  · intro b hb l hl
    rw [geometricSchedule_radius_eq b hb]
    exact geometricRadius_le_center (hs.trans
      (geometricSchedule_start_ge hs b hb)) hl.1
  · intro b hb l hl
    rw [geometricSchedule_radius_eq b hb]
    exact geometricRadius_le_envelope hl.1

/-- Finite A.12 instantiated on the genuine fixed-cutoff geometric schedule. -/
theorem geometricSchedule_A12
    {s J n : ℕ} (hs : 32 ≤ s)
    (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s))
    (hlarge : (2560 * 4096 : ℝ) ≤ (s : ℝ) ^ (2 / 5 : ℝ)) :
    gaussianCenteredPrefixProduct s *
        Real.exp (-gaussianBlockTotalCost (geometricSchedule s J n)) ≤
      constrainedGaussianDeviationWeight n (1 / 5 : ℝ) := by
  have hconsecutive := geometricSchedule_consecutive (show 1 ≤ s by omega) hterminal
  have hend := geometricSchedule_end hterminal
  have hscale := geometricSchedule_scale hs hterminal hupper hlarge
  have hcw := geometricSchedule_width_center (J := J) (n := n) (show 1 ≤ s by omega)
  have hstart : ∀ c ∈ geometricSchedule s J n, 0 < c.start := by
    intro c hc
    exact lt_of_lt_of_le (by omega) (geometricSchedule_start_ge (show 1 ≤ s by omega) c hc)
  have hpowOne : 1 ≤ 2 ^ J := Nat.one_le_pow _ _ (by omega)
  have hsn : s ≤ n := by
    simpa using (Nat.mul_le_mul_right s hpowOne).trans hterminal
  have hn2 : 2 ≤ n := (show 2 ≤ s by omega).trans hsn
  cases J with
  | zero =>
      change gaussianCenteredPrefixProduct (terminalGeometricBlock s n).start *
          Real.exp (-gaussianBlockTotalCost ([terminalGeometricBlock s n])) ≤ _
      apply prefix_mul_exp_neg_totalCost_le_constrainedGaussianDeviationWeight
        hn2 (show 2 ≤ (terminalGeometricBlock s n).start by simpa using (show 2 ≤ s by omega))
        hconsecutive hend hstart hscale
      · exact hcw.1
      · intro c hc l hl
        have := hcw.2 c hc l hl
        convert this using 1 <;> norm_num
  | succ j =>
      change gaussianCenteredPrefixProduct (completeGeometricBlock s).start *
          Real.exp (-gaussianBlockTotalCost
            (completeGeometricBlock s :: geometricSchedule (2 * s) j n)) ≤ _
      apply prefix_mul_exp_neg_totalCost_le_constrainedGaussianDeviationWeight
        hn2 (show 2 ≤ (completeGeometricBlock s).start by simpa using (show 2 ≤ s by omega))
        hconsecutive hend hstart hscale
      · exact hcw.1
      · intro c hc l hl
        have := hcw.2 c hc l hl
        convert this using 1 <;> norm_num

private lemma spectral_reference_identity {x : ℝ} (hx : 0 < x) :
    1280 * x * (2 * x) ^ 2 / (x ^ (6 / 5 : ℝ) / 32) ^ 2 =
      5242880 * x ^ (3 / 5 : ℝ) := by
  rw [div_pow, rpow_six_fifths_sq hx]
  have hden : 0 < x ^ 2 * x ^ (2 / 5 : ℝ) := by positivity
  rw [div_eq_iff (div_pos hden (by norm_num : (0 : ℝ) < 32 ^ 2)).ne']
  field_simp
  have hsmall : x ^ (3 / 5 : ℝ) * x ^ (2 / 5 : ℝ) = x := by
    rw [← Real.rpow_add hx,
      show (3 / 5 : ℝ) + 2 / 5 = 1 by norm_num, Real.rpow_one]
  calc
    1280 * x * 2 ^ 2 * 32 ^ 2 = 5242880 * x := by ring
    _ = 5242880 * (x ^ (3 / 5 : ℝ) * x ^ (2 / 5 : ℝ)) := by rw [hsmall]
    _ = 5242880 * x ^ (3 / 5 : ℝ) * x ^ (2 / 5 : ℝ) := by ring

lemma gaussianBlockSpectralCost_le_start {b : GaussianBlock}
    (hstart : 32 ≤ b.start)
    (hsteps : b.steps ≤ b.start)
    (hend : b.start + b.steps ≤ 2 * b.start)
    (hradius : b.radius = geometricRadius b.start) :
    gaussianBlockSpectralCost b ≤
      5242880 * (b.start : ℝ) ^ (3 / 5 : ℝ) := by
  unfold gaussianBlockSpectralCost
  rw [hradius]
  have hspos : (0 : ℝ) < b.start := by positivity
  have hR := geometricRadius_lower hstart
  have hnum : 1280 * (b.steps : ℝ) * ((b.start + b.steps : ℕ) : ℝ) ^ 2 ≤
      1280 * (b.start : ℝ) * (2 * b.start : ℝ) ^ 2 := by
    have hstepsReal : (b.steps : ℝ) ≤ b.start := by exact_mod_cast hsteps
    have hendReal : ((b.start + b.steps : ℕ) : ℝ) ≤ 2 * b.start := by
      exact_mod_cast hend
    gcongr
  have hden : ((b.start : ℝ) ^ (6 / 5 : ℝ) / 32) ^ 2 ≤
      (geometricRadius b.start : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR 2
  calc
    1280 * (b.steps : ℝ) * ((b.start + b.steps : ℕ) : ℝ) ^ 2 /
        (geometricRadius b.start : ℝ) ^ 2 ≤
      1280 * (b.start : ℝ) * (2 * b.start : ℝ) ^ 2 /
        ((b.start : ℝ) ^ (6 / 5 : ℝ) / 32) ^ 2 := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := spectral_reference_identity hspos

lemma geometricSchedule_spectralCost_le {s J n : ℕ}
    (hs : 32 ≤ s) (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s)) :
    ∀ b ∈ geometricSchedule s J n,
      gaussianBlockSpectralCost b ≤
        5242880 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  intro b hb
  have hsb := geometricSchedule_start_ge (show 1 ≤ s by omega) b hb
  have hbn := geometricSchedule_start_le_terminal hterminal b hb
  calc
    gaussianBlockSpectralCost b ≤
        5242880 * (b.start : ℝ) ^ (3 / 5 : ℝ) :=
      gaussianBlockSpectralCost_le_start (hs.trans hsb)
        (geometricSchedule_steps_le_start hupper b hb)
        (geometricSchedule_end_le_two_start hupper b hb)
        (geometricSchedule_radius_eq b hb)
    _ ≤ 5242880 * (n : ℝ) ^ (3 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbn) (by norm_num))
        (by norm_num)

/-- Generic length bound for the recursively defined block cost. -/
lemma gaussianBlockTotalCost_le_length_mul {blocks : List GaussianBlock}
    {S C : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hspectral : ∀ b ∈ blocks, gaussianBlockSpectralCost b ≤ S)
    (hconnector : ∀ b ∈ blocks,
      gaussianConnectorCost (b.start + b.steps) b.radius ≤ C) :
    gaussianBlockTotalCost blocks ≤ (blocks.length : ℕ) * (S + C) := by
  induction blocks with
  | nil => simp [gaussianBlockTotalCost]
  | cons b blocks ih =>
      cases blocks with
      | nil =>
          simp only [gaussianBlockTotalCost, List.length_cons, List.length_nil,
            Nat.zero_add, Nat.cast_one, one_mul]
          exact (hspectral b (by simp)).trans (by linarith)
      | cons c blocks =>
          rw [gaussianBlockTotalCost]
          have hbS := hspectral b (by simp)
          have hbC := hconnector b (by simp)
          have htail := ih
            (fun d hd ↦ hspectral d (by simp [hd]))
            (fun d hd ↦ hconnector d (by simp [hd]))
          calc
            gaussianBlockSpectralCost b +
                gaussianConnectorCost (b.start + b.steps) b.radius +
                gaussianBlockTotalCost (c :: blocks) ≤
              S + C + ((c :: blocks).length : ℕ) * (S + C) := by
                linarith
            _ = (((b :: c :: blocks).length : ℕ) : ℝ) * (S + C) := by
              push_cast
              simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
              ring

private lemma sqrt_two_pi_le_three : Real.sqrt (2 * Real.pi) ≤ 3 := by
  have hsq : (2 : ℝ) * Real.pi ≤ 3 ^ 2 := by
    nlinarith [Real.pi_le_four]
  have h := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h
  exact h

private lemma connector_ratio_reference {x : ℝ} (hx : 0 < x) :
    (x ^ (6 / 5 : ℝ) / 16) ^ 2 / (8 * x ^ 2) =
      x ^ (2 / 5 : ℝ) / 2048 := by
  rw [div_pow, rpow_six_fifths_sq hx]
  field_simp
  ring

lemma gaussianConnectorCost_le_start {b : GaussianBlock}
    (hstart : 32 ≤ b.start)
    (hendLower : b.start ≤ b.start + b.steps)
    (hendUpper : b.start + b.steps ≤ 2 * b.start)
    (hradius : b.radius = geometricRadius b.start) :
    gaussianConnectorCost (b.start + b.steps) b.radius ≤
      21 * (b.start : ℝ) ^ (3 / 5 : ℝ) := by
  let e : ℕ := b.start + b.steps
  have hspos : (0 : ℝ) < b.start := by positivity
  have hepos : (0 : ℝ) < e := by
    exact_mod_cast (show 0 < e by exact (show 0 < b.start by omega).trans_le hendLower)
  have hsOne : (1 : ℝ) ≤ b.start := by exact_mod_cast (show 1 ≤ b.start by omega)
  have hR := geometricRadius_le (s := b.start)
  rw [hradius]
  have hRsq : (geometricRadius b.start : ℝ) ^ 2 ≤
      ((b.start : ℝ) ^ (6 / 5 : ℝ) / 16) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR 2
  have heLowerReal : (b.start : ℝ) ≤ e := by exact_mod_cast hendLower
  have heUpperReal : (e : ℝ) ≤ 2 * b.start := by exact_mod_cast hendUpper
  have heSq : (b.start : ℝ) ^ 2 ≤ (e : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) heLowerReal 2
  have hratio : (geometricRadius b.start : ℝ) ^ 2 /
        (8 * (e : ℝ) ^ 2) ≤ (b.start : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      (geometricRadius b.start : ℝ) ^ 2 / (8 * (e : ℝ) ^ 2) ≤
          ((b.start : ℝ) ^ (6 / 5 : ℝ) / 16) ^ 2 /
            (8 * (b.start : ℝ) ^ 2) := by
        exact div_le_div₀ (by positivity) hRsq (by positivity) (by gcongr)
      _ = (b.start : ℝ) ^ (2 / 5 : ℝ) / 2048 :=
        connector_ratio_reference hspos
      _ ≤ (b.start : ℝ) ^ (2 / 5 : ℝ) := by
        have hp : 0 ≤ (b.start : ℝ) ^ (2 / 5 : ℝ) := by positivity
        nlinarith
      _ ≤ (b.start : ℝ) ^ (3 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hsOne (by norm_num)
  let z : ℝ := 2 * Real.sqrt (2 * Real.pi) * (e : ℝ)
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hz : z ≤ 12 * (b.start : ℝ) := by
    dsimp only [z]
    calc
      2 * Real.sqrt (2 * Real.pi) * (e : ℝ) ≤
          2 * 3 * (e : ℝ) := by
        gcongr
        exact sqrt_two_pi_le_three
      _ ≤ 2 * 3 * (2 * (b.start : ℝ)) := by gcongr
      _ = 12 * (b.start : ℝ) := by ring
  have hlog : Real.log z ≤ 20 * (b.start : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      Real.log z ≤ z ^ (3 / 5 : ℝ) / (3 / 5 : ℝ) :=
        Real.log_le_rpow_div hz0 (by norm_num)
      _ ≤ (12 * (b.start : ℝ)) ^ (3 / 5 : ℝ) / (3 / 5 : ℝ) := by
        gcongr
      _ = (12 : ℝ) ^ (3 / 5 : ℝ) *
          (b.start : ℝ) ^ (3 / 5 : ℝ) / (3 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) (by positivity)]
      _ ≤ 20 * (b.start : ℝ) ^ (3 / 5 : ℝ) := by
        have h12 : (12 : ℝ) ^ (3 / 5 : ℝ) ≤ 12 := by
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12)
              (by norm_num : (3 / 5 : ℝ) ≤ 1)
        have hp : 0 ≤ (b.start : ℝ) ^ (3 / 5 : ℝ) := by positivity
        nlinarith
  unfold gaussianConnectorCost
  change (geometricRadius b.start : ℝ) ^ 2 / (8 * (e : ℝ) ^ 2) +
      Real.log z ≤ _
  linarith

lemma geometricSchedule_connectorCost_le {s J n : ℕ}
    (hs : 32 ≤ s) (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s)) :
    ∀ b ∈ geometricSchedule s J n,
      gaussianConnectorCost (b.start + b.steps) b.radius ≤
        21 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  intro b hb
  have hsb := geometricSchedule_start_ge (show 1 ≤ s by omega) b hb
  have hbn := geometricSchedule_start_le_terminal hterminal b hb
  calc
    gaussianConnectorCost (b.start + b.steps) b.radius ≤
        21 * (b.start : ℝ) ^ (3 / 5 : ℝ) :=
      gaussianConnectorCost_le_start (hs.trans hsb)
        (Nat.le_add_right _ _) (geometricSchedule_end_le_two_start hupper b hb)
        (geometricSchedule_radius_eq b hb)
    _ ≤ 21 * (n : ℝ) ^ (3 / 5 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbn) (by norm_num))
        (by norm_num)

/-- Polynomial/rpow bound for the complete geometric A.12 cost.  The
harmless factor `J+1` is the exact number of dyadic blocks and is absorbed by
the positive slack in `Proposition13Scales.costExponent`. -/
theorem geometricSchedule_totalCost_le {s J n : ℕ}
    (hs : 32 ≤ s) (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s)) :
    gaussianBlockTotalCost (geometricSchedule s J n) ≤
      5242901 * (J + 1 : ℕ) * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have h := gaussianBlockTotalCost_le_length_mul
    (blocks := geometricSchedule s J n)
    (S := 5242880 * (n : ℝ) ^ (3 / 5 : ℝ))
    (C := 21 * (n : ℝ) ^ (3 / 5 : ℝ))
    (by positivity) (by positivity)
    (geometricSchedule_spectralCost_le hs hterminal hupper)
    (geometricSchedule_connectorCost_le hs hterminal hupper)
  rw [geometricSchedule_length] at h
  calc
    gaussianBlockTotalCost (geometricSchedule s J n) ≤
        ((J + 1 : ℕ) : ℝ) *
          (5242880 * (n : ℝ) ^ (3 / 5 : ℝ) +
            21 * (n : ℝ) ^ (3 / 5 : ℝ)) := h
    _ = 5242901 * (J + 1 : ℕ) * (n : ℝ) ^ (3 / 5 : ℝ) := by
      push_cast
      ring

/-! ## Sharp geometric-series cost estimate -/

/-- Sum of the `3/5` powers of all block starts in a geometric schedule. -/
def geometricStartPowerSum : ℕ → ℕ → ℝ
  | s, 0 => (s : ℝ) ^ (3 / 5 : ℝ)
  | s, J + 1 =>
      (s : ℝ) ^ (3 / 5 : ℝ) + geometricStartPowerSum (2 * s) J

private lemma five_le_four_mul_two_rpow :
    (5 : ℝ) ≤ 4 * (2 : ℝ) ^ (3 / 5 : ℝ) := by
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hsqrt0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hhalf : (2 : ℝ) ^ (1 / 2 : ℝ) ≤
      (2 : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hhalf
  linarith

private lemma five_mul_rpow_le_four_mul_double_rpow (s : ℕ) :
    5 * (s : ℝ) ^ (3 / 5 : ℝ) ≤
      4 * (2 * s : ℕ) ^ (3 / 5 : ℝ) := by
  have hp : 0 ≤ (s : ℝ) ^ (3 / 5 : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right five_le_four_mul_two_rpow hp
  rw [show ((2 * s : ℕ) : ℝ) = (2 : ℝ) * s by norm_num,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
  nlinarith

/-- A geometric series with ratio `2^(3/5)` is bounded by five times its
last term.  The slightly generous constant keeps the proof entirely
algebraic: `2^(3/5) ≥ sqrt 2 ≥ 5/4`. -/
lemma geometricStartPowerSum_le (s J : ℕ) :
    geometricStartPowerSum s J ≤
      5 * (2 ^ J * s : ℕ) ^ (3 / 5 : ℝ) -
        4 * (s : ℝ) ^ (3 / 5 : ℝ) := by
  induction J generalizing s with
  | zero =>
      simp only [geometricStartPowerSum, pow_zero, one_mul]
      ring_nf
      exact le_rfl
  | succ J ih =>
      rw [geometricStartPowerSum]
      have htail := ih (2 * s)
      have hratio := five_mul_rpow_le_four_mul_double_rpow s
      have hterminal : 2 ^ J * (2 * s) = 2 ^ (J + 1) * s := by
        simp only [pow_succ]
        ring
      rw [hterminal] at htail
      linarith

private lemma gaussianBlockTotalCost_cons_of_ne_nil
    (b : GaussianBlock) {bs : List GaussianBlock} (hbs : bs ≠ []) :
    gaussianBlockTotalCost (b :: bs) =
      gaussianBlockSpectralCost b +
        gaussianConnectorCost (b.start + b.steps) b.radius +
        gaussianBlockTotalCost bs := by
  cases bs with
  | nil => contradiction
  | cons c bs => rfl

/-- The total spectral and connector loss is bounded by the weighted
geometric sum of block starts. -/
lemma geometricSchedule_totalCost_le_powerSum {s J n : ℕ}
    (hs : 32 ≤ s) (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s)) :
    gaussianBlockTotalCost (geometricSchedule s J n) ≤
      5242901 * geometricStartPowerSum s J := by
  induction J generalizing s with
  | zero =>
      have hsn : s ≤ n := by simpa using hterminal
      have hspec : gaussianBlockSpectralCost (terminalGeometricBlock s n) ≤
          5242880 * (s : ℝ) ^ (3 / 5 : ℝ) := by
        apply gaussianBlockSpectralCost_le_start hs
        · simp only [terminalGeometricBlock_steps, terminalGeometricBlock_start]
          omega
        · simp only [terminalGeometricBlock_steps, terminalGeometricBlock_start]
          omega
        · rfl
      simp only [geometricSchedule_zero, gaussianBlockTotalCost,
        geometricStartPowerSum]
      have hp : 0 ≤ (s : ℝ) ^ (3 / 5 : ℝ) := by positivity
      linarith
  | succ J ih =>
      have hterminalTail : 2 ^ J * (2 * s) ≤ n := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hterminal
      have hupperTail : n < 2 * (2 ^ J * (2 * s)) := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hupper
      have htail := ih (show 32 ≤ 2 * s by omega) hterminalTail hupperTail
      have hspec : gaussianBlockSpectralCost (completeGeometricBlock s) ≤
          5242880 * (s : ℝ) ^ (3 / 5 : ℝ) := by
        apply gaussianBlockSpectralCost_le_start hs
        · simp only [completeGeometricBlock_steps, completeGeometricBlock_start]
          omega
        · simp only [completeGeometricBlock_steps, completeGeometricBlock_start]
          omega
        · rfl
      have hconn : gaussianConnectorCost
          ((completeGeometricBlock s).start + (completeGeometricBlock s).steps)
          (completeGeometricBlock s).radius ≤
          21 * (s : ℝ) ^ (3 / 5 : ℝ) := by
        apply gaussianConnectorCost_le_start hs
        · exact Nat.le_add_right _ _
        · simp only [completeGeometricBlock_steps, completeGeometricBlock_start]
          omega
        · rfl
      rw [geometricSchedule_succ,
        gaussianBlockTotalCost_cons_of_ne_nil _ (geometricSchedule_ne_nil _ _ _),
        geometricStartPowerSum]
      linarith

/-- Sharp A.12 cost: despite having logarithmically many blocks, the
geometric growth of their starts makes the complete loss `O(n^(3/5))`,
with no logarithmic factor. -/
theorem geometricSchedule_totalCost_le_sharp {s J n : ℕ}
    (hs : 32 ≤ s) (hterminal : 2 ^ J * s ≤ n)
    (hupper : n < 2 * (2 ^ J * s)) :
    gaussianBlockTotalCost (geometricSchedule s J n) ≤
      26214505 * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have hcost := geometricSchedule_totalCost_le_powerSum hs hterminal hupper
  have hsum := geometricStartPowerSum_le s J
  have hterminalRpow : ((2 ^ J * s : ℕ) : ℝ) ^ (3 / 5 : ℝ) ≤
      (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hterminal) (by norm_num)
  have hsnonneg : 0 ≤ (s : ℝ) ^ (3 / 5 : ℝ) := by positivity
  calc
    gaussianBlockTotalCost (geometricSchedule s J n) ≤
        5242901 * geometricStartPowerSum s J := hcost
    _ ≤ 5242901 *
        (5 * ((2 ^ J * s : ℕ) : ℝ) ^ (3 / 5 : ℝ) -
          4 * (s : ℝ) ^ (3 / 5 : ℝ)) := by gcongr
    _ ≤ 26214505 * ((2 ^ J * s : ℕ) : ℝ) ^ (3 / 5 : ℝ) := by
      nlinarith
    _ ≤ 26214505 * (n : ℝ) ^ (3 / 5 : ℝ) := by gcongr

/-! ## Canonical depth -/

/-- Number of complete doublings needed to reach the terminal scale. -/
def geometricDepth (s n : ℕ) : ℕ := Nat.log 2 (n / s)

lemma geometricDepth_terminal_lower {s n : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    2 ^ geometricDepth s n * s ≤ n := by
  have hdiv0 : n / s ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos hsn hs)
  apply (Nat.le_div_iff_mul_le hs).1
  exact Nat.pow_log_le_self 2 hdiv0

lemma geometricDepth_terminal_upper {s n : ℕ}
    (hs : 0 < s) (hsn : s ≤ n) :
    n < 2 * (2 ^ geometricDepth s n * s) := by
  have hdiv := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n / s)
  have hmul : (n / s + 1) * s ≤ 2 ^ (geometricDepth s n + 1) * s := by
    exact Nat.mul_le_mul_right s (Nat.succ_le_of_lt hdiv)
  have hn : n < (n / s + 1) * s := by
    have hdecomp : (n / s) * s + n % s = n := by
      simpa [Nat.mul_comm] using Nat.div_add_mod n s
    have hmod : n % s < s := Nat.mod_lt n hs
    calc
      n = (n / s) * s + n % s := hdecomp.symm
      _ < (n / s) * s + s := Nat.add_lt_add_left hmod _
      _ = (n / s + 1) * s := by rw [Nat.add_mul, one_mul]
  calc
    n < (n / s + 1) * s := hn
    _ ≤ 2 ^ (geometricDepth s n + 1) * s := hmul
    _ = 2 * (2 ^ geometricDepth s n * s) := by
      simp [pow_succ]
      ring

/-- Cost bound for the canonical schedule, with its exact logarithmic block
count displayed. -/
theorem canonicalGeometricSchedule_totalCost_le {s n : ℕ}
    (hs : 32 ≤ s) (hsn : s ≤ n) :
    gaussianBlockTotalCost (geometricSchedule s (geometricDepth s n) n) ≤
      5242901 * (geometricDepth s n + 1 : ℕ) *
        (n : ℝ) ^ (3 / 5 : ℝ) :=
  geometricSchedule_totalCost_le hs
    (geometricDepth_terminal_lower (by omega) hsn)
    (geometricDepth_terminal_upper (by omega) hsn)

/-- Canonical fixed-cutoff constrained Gaussian lower bound. -/
theorem canonicalGeometricSchedule_A12
    {s n : ℕ} (hs : 32 ≤ s) (hsn : s ≤ n)
    (hlarge : (2560 * 4096 : ℝ) ≤ (s : ℝ) ^ (2 / 5 : ℝ)) :
    gaussianCenteredPrefixProduct s *
        Real.exp (-gaussianBlockTotalCost
          (geometricSchedule s (geometricDepth s n) n)) ≤
      constrainedGaussianDeviationWeight n (1 / 5 : ℝ) :=
  geometricSchedule_A12 hs
    (geometricDepth_terminal_lower (by omega) hsn)
    (geometricDepth_terminal_upper (by omega) hsn) hlarge

end

end Erdos1165.GaussianGeometricSchedule
