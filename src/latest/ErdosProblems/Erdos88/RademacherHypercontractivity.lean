/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos88.Fourier

/-!
# Rademacher hypercontractivity for Erdős Problem 88

This file proves the finite-cube Bonami inequality needed for the Taylor
remainder in KSSS Lemma 7.2.  The proof is entirely finite and axiom-free:
it recursively splits a multilinear polynomial into its constant and
Rademacher-coordinate parts, proves the real 2-to-4 estimate, and iterates
it to dyadic moments.  A public wrapper applies the result to arbitrary
finite quadratic forms.
-/

open scoped BigOperators

namespace Erdos88
namespace RademacherHypercontractivity

inductive CubePoly : (n : ℕ) → Type
  | const (x : ℝ) : CubePoly 0
  | split {n : ℕ} (g h : CubePoly n) : CubePoly (n + 1)

namespace CubePoly

def eval : {n : ℕ} → CubePoly n → (Fin n → Bool) → ℝ
  | 0, const x, _ => x
  | _ + 1, split g h, ξ =>
      eval g (fun i ↦ ξ i.succ) +
        Erdos88.Fourier.rademacherSign (ξ 0) * eval h (fun i ↦ ξ i.succ)

def zero : (n : ℕ) → CubePoly n
  | 0 => const 0
  | n + 1 => split (zero n) (zero n)

def add : {n : ℕ} → CubePoly n → CubePoly n → CubePoly n
  | 0, const x, const y => const (x + y)
  | _ + 1, split g h, split g' h' => split (add g g') (add h h')

def neg : {n : ℕ} → CubePoly n → CubePoly n
  | 0, const x => const (-x)
  | _ + 1, split g h => split (neg g) (neg h)

def sub {n : ℕ} (p q : CubePoly n) : CubePoly n := add p (neg q)

def mul : {n : ℕ} → CubePoly n → CubePoly n → CubePoly n
  | 0, const x, const y => const (x * y)
  | _ + 1, split g h, split g' h' =>
      split (add (mul g g') (mul h h')) (add (mul g h') (mul h g'))

def smul : {n : ℕ} → ℝ → CubePoly n → CubePoly n
  | 0, a, const x => const (a * x)
  | _ + 1, a, split g h => split (smul a g) (smul a h)

def constPoly : (n : ℕ) → ℝ → CubePoly n
  | 0, x => const x
  | n + 1, x => split (constPoly n x) (zero n)

def affinePoly : {n : ℕ} → ℝ → (Fin n → ℝ) → CubePoly n
  | 0, c, _ => const c
  | n + 1, c, a =>
      split (affinePoly c (fun i ↦ a i.succ)) (constPoly n (a 0))

def quadraticPoly : {n : ℕ} → ℝ → (Fin n → ℝ) →
    (Fin n → Fin n → ℝ) → CubePoly n
  | 0, c, _, _ => const c
  | n + 1, c, a, A =>
      split
        (quadraticPoly (c + A 0 0) (fun i ↦ a i.succ)
          (fun i j ↦ A i.succ j.succ))
        (affinePoly (a 0) (fun i ↦ A 0 i.succ + A i.succ 0))

def powPoly {n : ℕ} (p : CubePoly n) : ℕ → CubePoly n
  | 0 => constPoly n 1
  | k + 1 => mul p (powPoly p k)

@[simp] theorem eval_zero {n : ℕ} (ξ : Fin n → Bool) : eval (zero n) ξ = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zero, eval, ih]

@[simp] theorem eval_add {n : ℕ} (p q : CubePoly n) (ξ : Fin n → Bool) :
    eval (add p q) ξ = eval p ξ + eval q ξ := by
  induction n with
  | zero => cases p; cases q; rfl
  | succ n ih =>
      cases p with
      | split g h =>
        cases q with
        | split g' h' => simp [add, eval, ih]; ring

@[simp] theorem eval_neg {n : ℕ} (p : CubePoly n) (ξ : Fin n → Bool) :
    eval (neg p) ξ = -eval p ξ := by
  induction n with
  | zero => cases p; rfl
  | succ n ih => cases p with | split g h => simp [neg, eval, ih]; ring

@[simp] theorem eval_sub {n : ℕ} (p q : CubePoly n) (ξ : Fin n → Bool) :
    eval (sub p q) ξ = eval p ξ - eval q ξ := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem eval_mul {n : ℕ} (p q : CubePoly n) (ξ : Fin n → Bool) :
    eval (mul p q) ξ = eval p ξ * eval q ξ := by
  induction n with
  | zero => cases p; cases q; rfl
  | succ n ih =>
      cases p with
      | split g h =>
        cases q with
        | split g' h' =>
          simp only [mul, eval, eval_add, ih]
          cases hξ : ξ 0 <;> simp [hξ] <;> ring

@[simp] theorem eval_smul {n : ℕ} (a : ℝ) (p : CubePoly n) (ξ : Fin n → Bool) :
    eval (smul a p) ξ = a * eval p ξ := by
  induction n with
  | zero => cases p; rfl
  | succ n ih => cases p with | split g h => simp [smul, eval, ih]; ring

@[simp] theorem eval_constPoly {n : ℕ} (x : ℝ) (ξ : Fin n → Bool) :
    eval (constPoly n x) ξ = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [constPoly, eval, ih]

theorem eval_affinePoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (ξ : Fin n → Bool) :
    eval (affinePoly c a) ξ =
      c + ∑ i, a i * Erdos88.Fourier.rademacherSign (ξ i) := by
  induction n with
  | zero => simp [affinePoly, eval]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [affinePoly, eval, ih, eval_constPoly]
      ring

theorem eval_quadraticPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (A : Fin n → Fin n → ℝ) (ξ : Fin n → Bool) :
    eval (quadraticPoly c a A) ξ =
      c + ∑ i, a i * Erdos88.Fourier.rademacherSign (ξ i) +
        ∑ i, ∑ j, A i j * Erdos88.Fourier.rademacherSign (ξ i) *
          Erdos88.Fourier.rademacherSign (ξ j) := by
  induction n generalizing c with
  | zero => simp [quadraticPoly, eval]
  | succ n ih =>
      simp_rw [Fin.sum_univ_succ]
      simp only [quadraticPoly, eval, ih, eval_affinePoly]
      simp only [Finset.sum_add_distrib]
      rw [mul_add]
      rw [Finset.mul_sum]
      simp_rw [add_mul, mul_add]
      rw [Finset.sum_add_distrib]
      have hs := Erdos88.Fourier.rademacherSign_sq (ξ 0)
      have hdiag : A 0 0 * Erdos88.Fourier.rademacherSign (ξ 0) *
          Erdos88.Fourier.rademacherSign (ξ 0) = A 0 0 := by
        calc
          _ = A 0 0 * Erdos88.Fourier.rademacherSign (ξ 0) ^ 2 := by ring
          _ = A 0 0 := by rw [hs]; ring
      rw [hdiag]
      ring_nf

@[simp] theorem eval_powPoly {n k : ℕ} (p : CubePoly n) (ξ : Fin n → Bool) :
    eval (powPoly p k) ξ = eval p ξ ^ k := by
  induction k with
  | zero => simp [powPoly]
  | succ k ih => simp [powPoly, ih, pow_succ]; ring

def IsZero {n : ℕ} (p : CubePoly n) : Prop := ∀ ξ, eval p ξ = 0

def DegreeLE : {n : ℕ} → ℕ → CubePoly n → Prop
  | 0, _, _ => True
  | _ + 1, 0, split g h => DegreeLE 0 g ∧ IsZero h
  | _ + 1, d + 1, split g h => DegreeLE (d + 1) g ∧ DegreeLE d h

noncomputable def mean {n : ℕ} (p : CubePoly n) (k : ℕ) : ℝ :=
  (∑ ξ : Fin n → Bool, eval p ξ ^ k) / Fintype.card (Fin n → Bool)

lemma mean_nonneg {n k : ℕ} (p : CubePoly n) (hk : Even k) : 0 ≤ mean p k := by
  rw [mean]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro ξ hξ
    exact Even.pow_nonneg hk _
  · positivity

lemma mean_split {n k : ℕ} (g h : CubePoly n) :
    mean (split g h) k = (mean (add g h) k + mean (sub g h) k) / 2 := by
  rw [mean, mean, mean]
  let e : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) :=
    (Equiv.piCongrLeft (fun _ ↦ Bool) (finSuccEquiv n)).trans Equiv.piOptionEquivProd
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  simp_rw [show ∀ ξ : Fin n → Bool,
      eval (split g h) (e.symm (true, ξ)) = eval (add g h) ξ by
        intro ξ
        simp [e, eval, add]]
  simp_rw [show ∀ ξ : Fin n → Bool,
      eval (split g h) (e.symm (false, ξ)) = eval (sub g h) ξ by
        intro ξ
        simp [e, eval, sub, neg]]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.reducePow]
  push_cast
  ring

lemma mean_congr {n k : ℕ} {p q : CubePoly n}
    (h : ∀ ξ, eval p ξ = eval q ξ) : mean p k = mean q k := by
  unfold mean
  congr 2
  funext ξ
  rw [h]

lemma mean_split_two {n : ℕ} (g h : CubePoly n) :
    mean (split g h) 2 = mean g 2 + mean h 2 := by
  rw [mean_split]
  unfold mean
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by positivity
  field_simp
  rw [← Finset.sum_add_distrib]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ hξ
  simp only [eval_add, eval_sub]
  ring

lemma mean_split_four {n : ℕ} (g h : CubePoly n) :
    mean (split g h) 4 =
      mean g 4 + 6 * mean (mul g h) 2 + mean h 4 := by
  rw [mean_split]
  unfold mean
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by positivity
  field_simp
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ hξ
  simp only [eval_add, eval_sub, eval_mul]
  ring

lemma mean_mul_two_sq_le {n : ℕ} (g h : CubePoly n) :
    mean (mul g h) 2 ^ 2 ≤ mean g 4 * mean h 4 := by
  unfold mean
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → Bool))
    (fun ξ ↦ eval g ξ ^ 2) (fun ξ ↦ eval h ξ ^ 2)
  simp only [eval_mul, mul_pow]
  have hcard : (0 : ℝ) < Fintype.card (Fin n → Bool) := by positivity
  rw [div_pow]
  calc
    (∑ ξ, eval g ξ ^ 2 * eval h ξ ^ 2) ^ 2 /
          (Fintype.card (Fin n → Bool) : ℝ) ^ 2 ≤
        ((∑ ξ, eval g ξ ^ 4) * ∑ ξ, eval h ξ ^ 4) /
          (Fintype.card (Fin n → Bool) : ℝ) ^ 2 := by
            apply div_le_div_of_nonneg_right
            · calc
                (∑ ξ, eval g ξ ^ 2 * eval h ξ ^ 2) ^ 2 ≤
                    (∑ ξ, (eval g ξ ^ 2) ^ 2) *
                      ∑ ξ, (eval h ξ ^ 2) ^ 2 := hc
                _ = (∑ ξ, eval g ξ ^ 4) * ∑ ξ, eval h ξ ^ 4 := by
                  congr 1 <;> apply Finset.sum_congr rfl <;> intro ξ hξ <;> ring
            · positivity
    _ = ((∑ ξ, eval g ξ ^ 4) /
          (Fintype.card (Fin n → Bool) : ℝ)) *
        ((∑ ξ, eval h ξ ^ 4) /
          (Fintype.card (Fin n → Bool) : ℝ)) := by field_simp

lemma isZero_degreeLE {n d : ℕ} {p : CubePoly n} (hp : IsZero p) :
    DegreeLE d p := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases p with
      | split g h =>
        have hg : IsZero g := by
          intro ξ
          have hp1 := hp (Fin.cons true ξ)
          have hp0 := hp (Fin.cons false ξ)
          simp only [eval, Fin.cons_succ, Fin.cons_zero,
            Erdos88.Fourier.rademacherSign_true,
            Erdos88.Fourier.rademacherSign_false] at hp1 hp0
          linarith
        have hh : IsZero h := by
          intro ξ
          have hp1 := hp (Fin.cons true ξ)
          have hp0 := hp (Fin.cons false ξ)
          simp only [eval, Fin.cons_succ, Fin.cons_zero,
            Erdos88.Fourier.rademacherSign_true,
            Erdos88.Fourier.rademacherSign_false] at hp1 hp0
          linarith
        cases d with
        | zero => exact ⟨ih hg, hh⟩
        | succ d => exact ⟨ih hg, ih hh⟩

lemma isZero_zero (n : ℕ) : IsZero (zero n) := by
  intro ξ
  exact eval_zero ξ

lemma degreeLE_constPoly (n d : ℕ) (x : ℝ) : DegreeLE d (constPoly n x) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases d with
      | zero => exact ⟨ih 0, isZero_zero n⟩
      | succ d => exact ⟨ih (d + 1), isZero_degreeLE (isZero_zero n)⟩

lemma degreeLE_affinePoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    DegreeLE 1 (affinePoly c a) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      exact ⟨ih (fun i ↦ a i.succ), degreeLE_constPoly n 0 (a 0)⟩

lemma degreeLE_quadraticPoly {n : ℕ} (c : ℝ) (a : Fin n → ℝ)
    (A : Fin n → Fin n → ℝ) : DegreeLE 2 (quadraticPoly c a A) := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
      exact ⟨ih (c + A 0 0) (fun i ↦ a i.succ) (fun i j ↦ A i.succ j.succ),
        degreeLE_affinePoly (a 0) (fun i ↦ A 0 i.succ + A i.succ 0)⟩

lemma degreeLE_mono {n d e : ℕ} {p : CubePoly n}
    (hde : d ≤ e) (hp : DegreeLE d p) : DegreeLE e p := by
  induction n generalizing d e with
  | zero => trivial
  | succ n ih =>
      cases p with
      | split g h =>
        cases d with
        | zero =>
          rcases hp with ⟨hg, hh⟩
          cases e with
          | zero => exact ⟨hg, hh⟩
          | succ e =>
            refine ⟨ih (Nat.zero_le _) hg, ?_⟩
            exact isZero_degreeLE hh
        | succ d =>
          cases e with
          | zero => omega
          | succ e =>
            exact ⟨ih hde hp.1,
              ih (Nat.le_of_succ_le_succ hde) hp.2⟩

lemma isZero_add {n : ℕ} {p q : CubePoly n}
    (hp : IsZero p) (hq : IsZero q) : IsZero (add p q) := by
  intro ξ
  rw [eval_add, hp ξ, hq ξ, zero_add]

lemma isZero_neg {n : ℕ} {p : CubePoly n} (hp : IsZero p) : IsZero (neg p) := by
  intro ξ
  rw [eval_neg, hp ξ, neg_zero]

lemma isZero_mul_left {n : ℕ} {p q : CubePoly n}
    (hp : IsZero p) : IsZero (mul p q) := by
  intro ξ
  rw [eval_mul, hp ξ, zero_mul]

lemma isZero_mul_right {n : ℕ} {p q : CubePoly n}
    (hq : IsZero q) : IsZero (mul p q) := by
  intro ξ
  rw [eval_mul, hq ξ, mul_zero]

lemma degreeLE_add {n d : ℕ} {p q : CubePoly n}
    (hp : DegreeLE d p) (hq : DegreeLE d q) : DegreeLE d (add p q) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases p with
      | split g h =>
        cases q with
        | split g' h' =>
          cases d with
          | zero => exact ⟨ih hp.1 hq.1, isZero_add hp.2 hq.2⟩
          | succ d => exact ⟨ih hp.1 hq.1, ih hp.2 hq.2⟩

lemma degreeLE_smul {n d : ℕ} (a : ℝ) {p : CubePoly n}
    (hp : DegreeLE d p) : DegreeLE d (smul a p) := by
  induction n generalizing d with
  | zero => trivial
  | succ n ih =>
      cases p with
      | split g h =>
        cases d with
        | zero =>
          refine ⟨ih hp.1, ?_⟩
          intro ξ
          rw [eval_smul, hp.2 ξ, mul_zero]
        | succ d => exact ⟨ih hp.1, ih hp.2⟩

lemma degreeLE_mul {n d e : ℕ} {p q : CubePoly n}
    (hp : DegreeLE d p) (hq : DegreeLE e q) : DegreeLE (d + e) (mul p q) := by
  induction n generalizing d e with
  | zero => trivial
  | succ n ih =>
      cases p with
      | split g h =>
        cases q with
        | split g' h' =>
          cases d with
          | zero =>
            cases e with
            | zero =>
              refine ⟨degreeLE_add (ih (d := 0) (e := 0) hp.1 hq.1)
                  (isZero_degreeLE (isZero_mul_left hp.2)), ?_⟩
              exact isZero_add (isZero_mul_right hq.2) (isZero_mul_left hp.2)
            | succ e =>
              refine ⟨degreeLE_add (ih (d := 0) (e := e + 1) hp.1 hq.1)
                  (isZero_degreeLE (isZero_mul_left hp.2)), ?_⟩
              exact degreeLE_add (ih (d := 0) (e := e) hp.1 hq.2)
                (isZero_degreeLE (isZero_mul_left hp.2))
          | succ d =>
            cases e with
            | zero =>
              refine ⟨degreeLE_add (ih (d := d + 1) (e := 0) hp.1 hq.1)
                  (isZero_degreeLE (isZero_mul_right hq.2)), ?_⟩
              exact degreeLE_add (isZero_degreeLE (isZero_mul_right hq.2))
                (ih (d := d) (e := 0) hp.2 hq.1)
            | succ e =>
              refine ⟨degreeLE_add
                  (ih (d := d + 1) (e := e + 1) hp.1 hq.1)
                  (degreeLE_mono (d := d + e) (e := (d + 1) + (e + 1)) (by omega)
                    (ih (d := d) (e := e) hp.2 hq.2)), ?_⟩
              have hleft := ih (d := d + 1) (e := e) hp.1 hq.2
              have hright := ih (d := d) (e := e + 1) hp.2 hq.1
              apply degreeLE_add hleft
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hright

lemma degreeLE_powPoly {n d k : ℕ} {p : CubePoly n} (hp : DegreeLE d p) :
    DegreeLE (d * k) (powPoly p k) := by
  induction k with
  | zero =>
      change DegreeLE 0 (constPoly n 1)
      exact degreeLE_constPoly n 0 1
  | succ k ih =>
      change DegreeLE (d * (k + 1)) (mul p (powPoly p k))
      simpa [Nat.mul_succ, Nat.add_comm] using degreeLE_mul hp ih

lemma mean_eq_zero_of_isZero {n k : ℕ} {p : CubePoly n} (hp : IsZero p)
    (hk : 0 < k) : mean p k = 0 := by
  unfold mean
  have hsum : (∑ ξ : Fin n → Bool, eval p ξ ^ k) = 0 := by
    apply Finset.sum_eq_zero
    intro ξ hξ
    rw [hp ξ]
    exact zero_pow hk.ne'
  rw [hsum, zero_div]

lemma mean_powPoly {n m k : ℕ} (p : CubePoly n) :
    mean (powPoly p m) k = mean p (m * k) := by
  unfold mean
  congr 2
  funext ξ
  rw [eval_powPoly, pow_mul]

/-- The real `2 → 4` Bonami inequality on a finite Rademacher cube. -/
theorem mean_four_le_nine_pow_degree_mul_mean_two_sq
    {n d : ℕ} (p : CubePoly n) (hp : DegreeLE d p) :
    mean p 4 ≤ 9 ^ d * mean p 2 ^ 2 := by
  induction n generalizing d with
  | zero =>
      cases p with
      | const x =>
        simp only [mean]
        have heval : ∀ ξ : Fin 0 → Bool, eval (const x) ξ = x := by intro ξ; rfl
        simp_rw [heval]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_fun, Fintype.card_fin]
        norm_num
        have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
        have hx : 0 ≤ x ^ 4 := by positivity
        nlinarith [show x ^ 4 = (x ^ 2) ^ 2 by ring]
  | succ n ih =>
      cases p with
      | split g h =>
        cases d with
        | zero =>
          rcases hp with ⟨hg, hh⟩
          have hmean (k : ℕ) : mean (split g h) k = mean g k := by
            rw [mean_split]
            have hadd : ∀ ξ, eval (add g h) ξ = eval g ξ := by
              intro ξ
              rw [eval_add, hh ξ, add_zero]
            have hsub : ∀ ξ, eval (sub g h) ξ = eval g ξ := by
              intro ξ
              rw [eval_sub, hh ξ, sub_zero]
            rw [mean_congr hadd, mean_congr hsub]
            ring
          rw [hmean 4, hmean 2]
          exact ih g hg
        | succ d =>
          rcases hp with ⟨hg, hh⟩
          have ihg := ih g hg
          have ihh := ih h hh
          have ha : 0 ≤ mean g 2 := mean_nonneg g even_two
          have hb : 0 ≤ mean h 2 := mean_nonneg h even_two
          have hG : 0 ≤ mean g 4 := mean_nonneg g (even_two.mul_left 2)
          have hH : 0 ≤ mean h 4 := mean_nonneg h (even_two.mul_left 2)
          have hC : 0 ≤ mean (mul g h) 2 := mean_nonneg (mul g h) even_two
          have hcrossSq := mean_mul_two_sq_le g h
          have hprod : mean g 4 * mean h 4 ≤
              (9 ^ (d + 1) * mean g 2 ^ 2) *
                (9 ^ d * mean h 2 ^ 2) :=
            mul_le_mul ihg ihh hH (by positivity)
          have hcrossSq' : mean (mul g h) 2 ^ 2 ≤
              (3 * 9 ^ d * mean g 2 * mean h 2) ^ 2 := by
            calc
              mean (mul g h) 2 ^ 2 ≤ mean g 4 * mean h 4 := hcrossSq
              _ ≤ (9 ^ (d + 1) * mean g 2 ^ 2) *
                    (9 ^ d * mean h 2 ^ 2) := hprod
              _ = (3 * 9 ^ d * mean g 2 * mean h 2) ^ 2 := by
                norm_num [pow_succ]
                ring
          have hcross : mean (mul g h) 2 ≤
              3 * 9 ^ d * mean g 2 * mean h 2 := by
            apply (sq_le_sq₀ hC (by positivity)).mp
            exact hcrossSq'
          rw [mean_split_four, mean_split_two]
          norm_num [pow_succ] at ihg ihh ⊢
          nlinarith [sq_nonneg (mean g 2 - mean h 2)]

def bonamiExponent (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => d * 2 ^ r + 2 * bonamiExponent d r

/-- Dyadic high moments obtained by iterating the `2 → 4` Bonami inequality. -/
theorem mean_two_pow_succ_le
    {n d : ℕ} (p : CubePoly n) (hp : DegreeLE d p) (r : ℕ) :
    mean p (2 ^ (r + 1)) ≤
      9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r) := by
  induction r with
  | zero => simp [bonamiExponent]
  | succ r ihr =>
      let q : CubePoly n := powPoly p (2 ^ r)
      have hqdeg : DegreeLE (d * 2 ^ r) q := degreeLE_powPoly hp
      have hbonami := mean_four_le_nine_pow_degree_mul_mean_two_sq q hqdeg
      have hq4 : mean q 4 = mean p (2 ^ (r + 2)) := by
        simp only [q, mean_powPoly]
        congr 1
        simp [pow_succ]
        ring
      have hq2 : mean q 2 = mean p (2 ^ (r + 1)) := by
        simp only [q, mean_powPoly]
        congr 1
      rw [hq4, hq2] at hbonami
      have hmoment : 0 ≤ mean p (2 ^ (r + 1)) :=
        mean_nonneg p (by rw [pow_succ]; exact even_two.mul_left _)
      have hbase : 0 ≤ mean p 2 := mean_nonneg p even_two
      have hrhs : 0 ≤
          9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r) := by positivity
      have hsq : mean p (2 ^ (r + 1)) ^ 2 ≤
          (9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r)) ^ 2 :=
        (sq_le_sq₀ hmoment hrhs).2 ihr
      calc
        mean p (2 ^ ((r + 1) + 1)) = mean p (2 ^ (r + 2)) := by congr 2
        _ ≤ 9 ^ (d * 2 ^ r) * mean p (2 ^ (r + 1)) ^ 2 := hbonami
        _ ≤ 9 ^ (d * 2 ^ r) *
            (9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r)) ^ 2 := by
              exact mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 9 ^ bonamiExponent d (r + 1) * mean p 2 ^ (2 ^ (r + 1)) := by
          simp only [bonamiExponent]
          rw [pow_add]
          rw [show 2 * bonamiExponent d r = bonamiExponent d r * 2 by omega]
          rw [pow_mul]
          rw [pow_succ]
          ring

/-- Finite Markov corollary of the dyadic Bonami bound.  This is the
source-usable high-moment tail estimate: no measure-theoretic probability
space is hidden in the statement. -/
theorem finProbability_abs_eval_mul_pow_le
    {n d : ℕ} (p : CubePoly n) (hp : DegreeLE d p) (r : ℕ)
    {T : ℝ} (hT : 0 < T) :
    Erdos88.Fourier.finProbability (Fin n → Bool)
        (fun xi ↦ T ≤ |eval p xi|) * T ^ (2 ^ (r + 1)) ≤
      9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r) := by
  classical
  let k : ℕ := 2 ^ (r + 1)
  have hkEven : Even k := by
    dsimp only [k]
    rw [pow_succ]
    exact even_two.mul_left _
  have hmarkov :
      ((Finset.univ.filter fun xi : Fin n → Bool ↦
          T ≤ |eval p xi|).card : ℝ) * T ^ k ≤
        ∑ xi : Fin n → Bool, |eval p xi| ^ k := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun xi (_hxi : xi ∈ (Finset.univ : Finset (Fin n → Bool))) ↦
        show (if T ≤ |eval p xi| then T ^ k else 0) ≤
            |eval p xi| ^ k by
          split_ifs with h
          · exact pow_le_pow_left₀ hT.le h k
          · exact (Even.pow_nonneg hkEven _))
    simpa only [Finset.sum_ite, Finset.sum_const_zero,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat, mul_one, add_zero] using hsum
  have hcard : (0 : ℝ) < Fintype.card (Fin n → Bool) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin n → Bool))
  calc
    Erdos88.Fourier.finProbability (Fin n → Bool)
          (fun xi ↦ T ≤ |eval p xi|) * T ^ (2 ^ (r + 1)) =
        (((Finset.univ.filter fun xi : Fin n → Bool ↦
            T ≤ |eval p xi|).card : ℝ) * T ^ k) /
          Fintype.card (Fin n → Bool) := by
      rw [Erdos88.Fourier.finProbability]
      dsimp only [k]
      ring
    _ ≤ (∑ xi : Fin n → Bool, |eval p xi| ^ k) /
          Fintype.card (Fin n → Bool) :=
      div_le_div_of_nonneg_right hmarkov hcard.le
    _ = mean p k := by
      rw [mean]
      congr 1
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [← abs_pow, abs_of_nonneg (hkEven.pow_nonneg (eval p xi))]
    _ ≤ 9 ^ bonamiExponent d r * mean p 2 ^ (2 ^ r) := by
      simpa only [k] using mean_two_pow_succ_le p hp r

noncomputable def quadraticCubeMean {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℝ) (k : ℕ) : ℝ :=
  (∑ ξ : I → Bool,
      (∑ i, ∑ j, A i j * Erdos88.Fourier.rademacherSign (ξ i) *
        Erdos88.Fourier.rademacherSign (ξ j)) ^ k) /
    Fintype.card (I → Bool)

/-- A source-usable dyadic high-moment bound for a real quadratic form on
an arbitrary finite Rademacher cube. -/
theorem quadraticCubeMean_two_pow_succ_le
    {I : Type*} [Fintype I] [DecidableEq I] (A : I → I → ℝ) (r : ℕ) :
    quadraticCubeMean A (2 ^ (r + 1)) ≤
      9 ^ bonamiExponent 2 r * quadraticCubeMean A 2 ^ (2 ^ r) := by
  classical
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let se : (I → Bool) ≃ (Fin (Fintype.card I) → Bool) :=
    Equiv.piCongrLeft (fun _ ↦ Bool) e
  let A' : Fin (Fintype.card I) → Fin (Fintype.card I) → ℝ :=
    fun i j ↦ A (e.symm i) (e.symm j)
  let p : CubePoly (Fintype.card I) :=
    quadraticPoly 0 (fun _ ↦ 0) A'
  have hp : DegreeLE 2 p := degreeLE_quadraticPoly 0 (fun _ ↦ 0) A'
  have h := mean_two_pow_succ_le p hp r
  have hpoint (k : ℕ) : mean p k = quadraticCubeMean A k := by
    unfold mean quadraticCubeMean
    have hs := se.sum_comp (fun ξ ↦ eval p ξ ^ k)
    rw [← hs]
    rw [Fintype.card_congr se]
    congr 2
    funext ξ
    rw [show eval p (se ξ) =
        ∑ i, ∑ j, A i j * Erdos88.Fourier.rademacherSign (ξ i) *
          Erdos88.Fourier.rademacherSign (ξ j) by
      simp only [p, eval_quadraticPoly]
      simp only [zero_mul, Finset.sum_const_zero, zero_add]
      dsimp only [A']
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro j hj
      simp [se, e]]
  simpa only [hpoint] using h

lemma abs_pow_eq_pow_of_even (x : ℝ) {k : ℕ} (hk : Even k) :
    |x| ^ k = x ^ k := by
  rw [← abs_pow, abs_of_nonneg (hk.pow_nonneg x)]

/-- Absolute-moment form of the dyadic quadratic Bonami bound, matching
the Taylor remainder in KSSS (7.4). -/
theorem quadraticCubeAbsMean_two_pow_succ_le
    {I : Type*} [Fintype I] [DecidableEq I] (A : I → I → ℝ) (r : ℕ) :
    (∑ ξ : I → Bool,
        |∑ i, ∑ j, A i j * Erdos88.Fourier.rademacherSign (ξ i) *
          Erdos88.Fourier.rademacherSign (ξ j)| ^ (2 ^ (r + 1))) /
        Fintype.card (I → Bool) ≤
      9 ^ bonamiExponent 2 r *
        ((∑ ξ : I → Bool,
            (∑ i, ∑ j, A i j * Erdos88.Fourier.rademacherSign (ξ i) *
              Erdos88.Fourier.rademacherSign (ξ j)) ^ 2) /
          Fintype.card (I → Bool)) ^ (2 ^ r) := by
  have heven : Even (2 ^ (r + 1)) := by
    rw [pow_succ]
    exact even_two.mul_left _
  simpa only [quadraticCubeMean, abs_pow_eq_pow_of_even _ heven] using
    quadraticCubeMean_two_pow_succ_le A r

end CubePoly
end RademacherHypercontractivity
end Erdos88
