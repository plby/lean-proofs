/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib

/-!
# Finite-dimensional cores of the PZ affine-approximation argument

Pham--Zakharov's Lemma 2 finds, among a prescribed family of small cubes, one
cube on which a bounded convex function is uniformly close to an affine
function.  The published proof has two logically separate finite-dimensional
parts:

* coordinate errors add along a path which changes one coordinate at a time;
* a coordinate, a transverse fibre, and a residue class can be pigeonholed,
  after which separated one-dimensional slope jumps telescope.

This file proves both parts in arbitrary finite dimension and with exact
constants.  The results are deliberately independent of differentiability;
they can be applied either to derivatives of a smooth approximation, as in the
paper, or to finite secant slopes in a nonsmooth proof.

The remaining analytic input for the full multidimensional Lemma 2 is the
existence, at every bad cell, of a compatible affine support whose failure
forces one of the coordinate jumps below.  Mathlib currently has no packaged
finite-dimensional subgradient theorem on an open box, so that input is not
asserted here.
-/

open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity.ConvexApproxND

set_option autoImplicit false

noncomputable section

/-! ## Coordinate paths and exact affine error accumulation -/

/-- The path from `v` to `x` which has changed precisely the coordinates with
index strictly below `k`.  Values of `k` above the dimension are harmless. -/
def coordinatePath {n : ℕ} (v x : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i ↦ if i.val < k then x i else v i

@[simp]
theorem coordinatePath_zero {n : ℕ} (v x : Fin n → ℝ) :
    coordinatePath v x 0 = v := by
  funext i
  simp [coordinatePath]

@[simp]
theorem coordinatePath_dim {n : ℕ} (v x : Fin n → ℝ) :
    coordinatePath v x n = x := by
  funext i
  simp [coordinatePath, i.isLt]

/-- Between two consecutive stages, only the newly selected coordinate can
change. -/
theorem coordinatePath_succ_apply {n k : ℕ} (v x : Fin n → ℝ)
    (hk : k < n) (i : Fin n) :
    coordinatePath v x (k + 1) i =
      if i = ⟨k, hk⟩ then x i else coordinatePath v x k i := by
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp [coordinatePath]
  · have hne : i.val ≠ k := by
      intro hval
      apply hi
      exact Fin.ext hval
    by_cases hil : i.val < k
    · have his : i.val < k + 1 := by omega
      simp [coordinatePath, hil, his, hi]
    · have hki : k < i.val := by omega
      have hnis : ¬i.val < k + 1 := by omega
      simp [coordinatePath, hil, hnis, hi]

/-- An affine function written relative to a base point. -/
def tangentAffine {n : ℕ} (f : (Fin n → ℝ) → ℝ) (v p : Fin n → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x ↦ f v + ∑ i, p i * (x i - v i)

@[simp]
theorem tangentAffine_apply_base {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (v p : Fin n → ℝ) : tangentAffine f v p v = f v := by
  simp [tangentAffine]

/-- The increment of the affine model at one coordinate-path step is exactly
the corresponding coordinate increment. -/
theorem tangentAffine_coordinatePath_succ_sub {n k : ℕ}
    (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ) (hk : k < n) :
    tangentAffine f v p (coordinatePath v x (k + 1)) -
        tangentAffine f v p (coordinatePath v x k) =
      p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩) := by
  simp only [tangentAffine, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · rw [coordinatePath_succ_apply v x hk]
    simp [coordinatePath]
  · intro i _ hi
    rw [coordinatePath_succ_apply v x hk]
    simp [hi]
  · simp

/-- Consecutive coordinate-path increments telescope exactly. -/
theorem sum_coordinatePath_increments {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) :
    ∑ k ∈ Finset.range n,
        (g (coordinatePath v x (k + 1)) - g (coordinatePath v x k)) =
      g x - g v := by
  simpa only [coordinatePath_zero, coordinatePath_dim] using
    (Finset.sum_range_sub (fun k ↦ g (coordinatePath v x k)) n)

/-- **Multidimensional affine error from coordinate directional errors.**

If the error made at each coordinate-path step is at most `epsilon k`, then
the error of the resulting affine model is at most the sum of those errors.
No sign condition on `epsilon` is needed: the hypotheses themselves force the
relevant terms to be nonnegative. -/
theorem tangentAffine_error_le_sum_coordinate_errors {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ) (epsilon : ℕ → ℝ)
    (hstep : ∀ (k : ℕ) (hk : k < n),
      |(f (coordinatePath v x (k + 1)) - f (coordinatePath v x k)) -
        p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩)| ≤ epsilon k) :
    |f x - tangentAffine f v p x| ≤
      ∑ k ∈ Finset.range n, epsilon k := by
  let L := tangentAffine f v p
  let g : (Fin n → ℝ) → ℝ := fun y ↦ f y - L y
  have hgbase : g v = 0 := by simp [g, L]
  have htel :
      ∑ k ∈ Finset.range n,
          (g (coordinatePath v x (k + 1)) - g (coordinatePath v x k)) =
        g x := by
    rw [sum_coordinatePath_increments]
    simp [hgbase]
  rw [show f x - tangentAffine f v p x = g x by rfl, ← htel]
  calc
    |∑ k ∈ Finset.range n,
        (g (coordinatePath v x (k + 1)) - g (coordinatePath v x k))| ≤
        ∑ k ∈ Finset.range n,
          |g (coordinatePath v x (k + 1)) - g (coordinatePath v x k)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, epsilon k := by
      apply Finset.sum_le_sum
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      rw [show
          g (coordinatePath v x (k + 1)) - g (coordinatePath v x k) =
            (f (coordinatePath v x (k + 1)) - f (coordinatePath v x k)) -
              p ⟨k, hklt⟩ * (x ⟨k, hklt⟩ - v ⟨k, hklt⟩) by
        dsimp [g, L]
        calc
          f (coordinatePath v x (k + 1)) -
                tangentAffine f v p (coordinatePath v x (k + 1)) -
              (f (coordinatePath v x k) -
                tangentAffine f v p (coordinatePath v x k)) =
              (f (coordinatePath v x (k + 1)) - f (coordinatePath v x k)) -
                (tangentAffine f v p (coordinatePath v x (k + 1)) -
                  tangentAffine f v p (coordinatePath v x k)) := by ring
          _ = (f (coordinatePath v x (k + 1)) - f (coordinatePath v x k)) -
                p ⟨k, hklt⟩ * (x ⟨k, hklt⟩ - v ⟨k, hklt⟩) := by
              rw [tangentAffine_coordinatePath_succ_sub f v x p hklt]]
      exact hstep k hklt

/-- Uniform-error specialization: `n` coordinate errors of size at most
`epsilon` produce total error at most `n * epsilon`. -/
theorem tangentAffine_error_le_dim_mul {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ) (epsilon : ℝ)
    (hstep : ∀ (k : ℕ) (hk : k < n),
      |(f (coordinatePath v x (k + 1)) - f (coordinatePath v x k)) -
        p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩)| ≤ epsilon) :
    |f x - tangentAffine f v p x| ≤ (n : ℝ) * epsilon := by
  simpa using tangentAffine_error_le_sum_coordinate_errors
    f v x p (fun _ ↦ epsilon) hstep

/-! ## Exact finite pigeonhole statements -/

/-- A finite map has a fibre of at least the average size, in a
division-free exact form. -/
theorem exists_large_fiber {α β : Type*} [DecidableEq α]
    [Fintype β] [DecidableEq β] (I : Finset α) (hI : I.Nonempty)
    (key : α → β) :
    ∃ b : β, I.card ≤ Fintype.card β * (I.filter fun a ↦ key a = b).card := by
  have : Nonempty β := ⟨key hI.choose⟩
  have hcardβ : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast Fintype.card_pos
  have hsum_nat :
      ∑ b : β, (I.filter fun a ↦ key a = b).card = I.card := by
    classical
    simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := I) (t := (Finset.univ : Finset β))
        (g := key) (f := fun _ ↦ (1 : ℕ)) (by simp))
  have hsum_real :
      ∑ b : β, ((I.filter fun a ↦ key a = b).card : ℝ) = I.card := by
    exact_mod_cast hsum_nat
  have haverage :
      ∑ _b : β, (I.card : ℝ) / Fintype.card β ≤
        ∑ b : β, ((I.filter fun a ↦ key a = b).card : ℝ) := by
    rw [hsum_real]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hcardβ.ne']
  obtain ⟨b, _hb, hb⟩ :=
    Finset.exists_le_of_sum_le (s := (Finset.univ : Finset β))
      (Finset.univ_nonempty : (Finset.univ : Finset β).Nonempty) haverage
  refine ⟨b, ?_⟩
  have hreal : (I.card : ℝ) ≤
      Fintype.card β * (I.filter fun a ↦ key a = b).card := by
    rw [div_le_iff₀ hcardβ] at hb
    simpa [mul_comm] using hb
  exact_mod_cast hreal

/-- Pigeonhole a coordinate label and an arbitrary finite transverse key at
once.  This is the abstract form used before adding the residue class which
separates selected grid positions. -/
theorem exists_large_coordinate_fiber {α κ β : Type*} [DecidableEq α]
    [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
    (I : Finset α) (hI : I.Nonempty) (axis : α → κ) (fiber : α → β) :
    ∃ i : κ, ∃ b : β,
      I.card ≤ Fintype.card κ * Fintype.card β *
        (I.filter fun a ↦ axis a = i ∧ fiber a = b).card := by
  obtain ⟨key, hkey⟩ := exists_large_fiber I hI (fun a ↦ (axis a, fiber a))
  obtain ⟨i, b⟩ := key
  refine ⟨i, b, ?_⟩
  simpa [Fintype.card_prod, Nat.mul_assoc] using hkey

/-- Adding a residue class costs exactly a factor `q`. -/
theorem exists_large_coordinate_fiber_residue {α κ β : Type*}
    [DecidableEq α] [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β]
    (I : Finset α) (hI : I.Nonempty) (q : ℕ)
    (axis : α → κ) (fiber : α → β) (residue : α → Fin q) :
    ∃ i : κ, ∃ b : β, ∃ r : Fin q,
      I.card ≤ Fintype.card κ * Fintype.card β * q *
        (I.filter fun a ↦
          axis a = i ∧ fiber a = b ∧ residue a = r).card := by
  obtain ⟨key, hkey⟩ := exists_large_fiber I hI
    (fun a ↦ (axis a, fiber a, residue a))
  obtain ⟨i, b, r⟩ := key
  refine ⟨i, b, r, ?_⟩
  simpa [Fintype.card_prod, Nat.mul_assoc] using hkey

/-! ## Residue separation and telescoping jumps -/

/-- Distinct increasing natural numbers in one residue class modulo `q` are
separated by at least `q`. -/
theorem add_modulus_le_of_lt_of_mod_eq {a b q : ℕ}
    (hab : a < b) (hmod : a % q = b % q) : a + q ≤ b := by
  have hdvd : q ∣ b - a :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hab)).mp hmod
  have hqle : q ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdvd
  omega

/-- If successive selected locations are separated by `q`, monotonicity lets
each local jump feed into the next one.  All `ell + 1` jumps, including the
last jump beyond `a ell`, are retained exactly. -/
theorem separated_jump_telescope {q ell : ℕ} (a : ℕ → ℕ) (g : ℕ → ℝ)
    (Delta : ℝ)
    (hsep : ∀ j, j < ell → a j + q ≤ a (j + 1))
    (hmono : Monotone g)
    (hjump : ∀ j, j ≤ ell → g (a j) + Delta ≤ g (a j + q)) :
    g (a 0) + (ell + 1 : ℕ) * Delta ≤ g (a ell + q) := by
  induction ell with
  | zero =>
      simpa using hjump 0 (by omega)
  | succ ell ih =>
      have hprev := ih
        (fun j hj ↦ hsep j (by omega))
        (fun j hj ↦ hjump j (by omega))
      have hbridge : g (a ell + q) ≤ g (a (ell + 1)) :=
        hmono (hsep ell (by omega))
      have hlast := hjump (ell + 1) (by omega)
      push_cast at hprev ⊢
      linarith

/-- Version whose separation is obtained directly from strict ordering in a
common nonzero residue class. -/
theorem residue_class_jump_telescope {q ell : ℕ} (_hq : 0 < q)
    (a : ℕ → ℕ) (g : ℕ → ℝ) (Delta : ℝ)
    (hstrict : ∀ j, j < ell → a j < a (j + 1))
    (hresidue : ∀ j, j < ell → a j % q = a (j + 1) % q)
    (hmono : Monotone g)
    (hjump : ∀ j, j ≤ ell → g (a j) + Delta ≤ g (a j + q)) :
    g (a 0) + (ell + 1 : ℕ) * Delta ≤ g (a ell + q) := by
  apply separated_jump_telescope a g Delta
  · intro j hj
    exact add_modulus_le_of_lt_of_mod_eq (hstrict j hj) (hresidue j hj)
  · exact hmono
  · exact hjump

/-- A bounded monotone slope function cannot sustain more total separated
jump than its available oscillation.  This is the final contradiction step
in PZ Lemma 2. -/
theorem separated_jumps_le_oscillation {q ell : ℕ}
    (a : ℕ → ℕ) (g : ℕ → ℝ) (Delta lower upper : ℝ)
    (hsep : ∀ j, j < ell → a j + q ≤ a (j + 1))
    (hmono : Monotone g)
    (hjump : ∀ j, j ≤ ell → g (a j) + Delta ≤ g (a j + q))
    (hlower : lower ≤ g (a 0)) (hupper : g (a ell + q) ≤ upper) :
    (ell + 1 : ℕ) * Delta ≤ upper - lower := by
  have htel := separated_jump_telescope a g Delta hsep hmono hjump
  push_cast at htel ⊢
  linarith

end

end Erdos186.PZ.ConvexDensity.ConvexApproxND
