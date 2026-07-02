/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 24.
https://www.erdosproblems.com/forum/thread/24

Informal authors:
- Andrzej Grzesik

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/24#post-5732
- https://gist.githubusercontent.com/madeve-unipi/683739094ab7a5079a2bc2647c47743b/raw/6164255a2f1ed85df3f01b75d2f8b35a1330aacb/Erdos24.lean
-/
/-
Released under Apache 2.0 license.
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/
import Mathlib

/-!
# Erdős Pentagon Conjecture

We prove that every triangle-free graph on `5n` vertices contains at most `n⁵` copies
of the 5-cycle `C₅`, settling the Erdős pentagon conjecture in the affirmative.

## Main results

- `erdos_pentagon_conjecture`: Every triangle-free graph on `5n` vertices has ≤ `n⁵`
  copies of `C₅`.

## Proof outline

Following Grzesik (2012), the proof proceeds in two steps:

1. **Flag algebra bound** (`flag_algebra_c5_turan_density`):
   The Turán density of `C₅` in `K₃`-free graphs satisfies `π_{C₅}(K₃) ≤ 24/625`,
   proved via Razborov's flag algebra method with explicit semidefinite certificates.

2. **Blow-up argument** (`erdos_pentagon_conjecture`):
   Given a triangle-free graph `G` on `5n` vertices with `c = numC5Copies G` copies of
   `C₅`, its balanced blow-up `G.blowup N` is triangle-free with at least `c · N⁵` copies.
   Applying the Turán density bound with `ε = 12/(625·n⁵)` to the blow-up (for `N` large
   enough) yields `c ≤ n⁵ + 1/2`, hence `c ≤ n⁵`.

## References

* A. Grzesik, *On the maximum number of five-cycles in a triangle-free graph*,
  J. Combin. Theory Ser. B, 102(5):1061–1066, 2012.
* A. Razborov, *Flag algebras*, J. Symbolic Logic, 72(4):1239–1282, 2007.
* H. Hatami, J. Hladký, D. Král', S. Norine, A. Razborov,
  *On the number of pentagons in triangle-free graphs*, J. Combin. Theory Ser. A,
  120(3):722–732, 2013.
-/

namespace Erdos24

noncomputable section

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.maxHeartbeats false
set_option linter.style.show false
set_option maxHeartbeats 50000000
-- Several generated pentagon-density arguments time out at the default heartbeat limit.

open Finset Function SimpleGraph Fintype Nat Matrix

attribute [local instance] Classical.propDecidable

/-!
## § 1. Certificate Matrices and PSD Verification

Three certificate matrices P (8×8), Q (6×6), R (5×5) from the flag algebra proof,
verified positive semidefinite via explicit LDLᵀ decompositions checked by rational arithmetic.
-/

/-- Certificate matrix P (8×8) for type σ₀, scaled by 625. -/
def P_cert : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 24 | 0, 1 => -36 | 0, 2 => -36 | 0, 3 => 24
  | 0, 4 => -36 | 0, 5 => 24 | 0, 6 => 24 | 0, 7 => -36
  | 1, 0 => -36 | 1, 1 => 277 | 1, 2 => 97 | 1, 3 => -79
  | 1, 4 => 97 | 1, 5 => -79 | 1, 6 => -259 | 1, 7 => 54
  | 2, 0 => -36 | 2, 1 => 97 | 2, 2 => 277 | 2, 3 => -79
  | 2, 4 => 97 | 2, 5 => -259 | 2, 6 => -79 | 2, 7 => 54
  | 3, 0 => 24 | 3, 1 => -79 | 3, 2 => -79 | 3, 3 => 247
  | 3, 4 => -259 | 3, 5 => 67 | 3, 6 => 67 | 3, 7 => -36
  | 4, 0 => -36 | 4, 1 => 97 | 4, 2 => 97 | 4, 3 => -259
  | 4, 4 => 277 | 4, 5 => -79 | 4, 6 => -79 | 4, 7 => 54
  | 5, 0 => 24 | 5, 1 => -79 | 5, 2 => -259 | 5, 3 => 67
  | 5, 4 => -79 | 5, 5 => 247 | 5, 6 => 67 | 5, 7 => -36
  | 6, 0 => 24 | 6, 1 => -259 | 6, 2 => -79 | 6, 3 => 67
  | 6, 4 => -79 | 6, 5 => 67 | 6, 6 => 247 | 6, 7 => -36
  | 7, 0 => -36 | 7, 1 => 54 | 7, 2 => 54 | 7, 3 => -36
  | 7, 4 => 54 | 7, 5 => -36 | 7, 6 => -36 | 7, 7 => 54
  | _, _ => 0

/-- Certificate matrix Q (6×6) for type σ₁, scaled by 2500. -/
def Q_cert : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1728 | 0, 1 => -1551 | 0, 2 => -1551 | 0, 3 => -1308
  | 0, 4 => 687 | 0, 5 => 687
  | 1, 0 => -1551 | 1, 1 => 2336 | 1, 2 => 742 | 1, 3 => 908
  | 1, 4 => 2557 | 1, 5 => -4084
  | 2, 0 => -1551 | 2, 1 => 742 | 2, 2 => 2336 | 2, 3 => 908
  | 2, 4 => -4084 | 2, 5 => 2557
  | 3, 0 => -1308 | 3, 1 => 908 | 3, 2 => 908 | 3, 3 => 1728
  | 3, 4 => -254 | 3, 5 => -254
  | 4, 0 => 687 | 4, 1 => 2557 | 4, 2 => -4084 | 4, 3 => -254
  | 4, 4 => 15264 | 4, 5 => -14424
  | 5, 0 => 687 | 5, 1 => -4084 | 5, 2 => 2557 | 5, 3 => -254
  | 5, 4 => -14424 | 5, 5 => 15264
  | _, _ => 0

/-- Certificate matrix R (5×5) for type σ₂, scaled by 625. -/
def R_cert : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1512 | 0, 1 => 568 | 0, 2 => -380 | 0, 3 => 568 | 0, 4 => -376
  | 1, 0 => 568 | 1, 1 => 475 | 1, 2 => -191 | 1, 3 => 0 | 1, 4 => -93
  | 2, 0 => -380 | 2, 1 => -191 | 2, 2 => 192 | 2, 3 => -191 | 2, 4 => -2
  | 3, 0 => 568 | 3, 1 => 0 | 3, 2 => -191 | 3, 3 => 475 | 3, 4 => -93
  | 4, 0 => -376 | 4, 1 => -93 | 4, 2 => -2 | 4, 3 => -93 | 4, 4 => 190
  | _, _ => 0

private def L_P : Matrix (Fin 8) (Fin 8) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => -3 / 2
  | 1, 1 => 1
  | 2, 0 => -3 / 2
  | 2, 1 => 43 / 223
  | 2, 2 => 1
  | 3, 0 => 1
  | 3, 1 => -43 / 223
  | 3, 2 => -43 / 266
  | 3, 3 => 1
  | 4, 0 => -3 / 2
  | 4, 1 => 43 / 223
  | 4, 2 => 43 / 266
  | 4, 3 => -1
  | 4, 4 => 1
  | 5, 0 => 1
  | 5, 1 => -43 / 223
  | 5, 2 => -1
  | 5, 5 => 1
  | 6, 0 => 1
  | 6, 1 => -1
  | 6, 6 => 1
  | 7, 0 => -3 / 2
  | 7, 7 => 1
  | _, _ => 0

private def D_P_vec : Fin 8 → ℚ := fun i =>
  match i.val with
  | 0 => 24
  | 1 => 223
  | 2 => 47880 / 223
  | 3 => 27810 / 133
  | _ => 0

private def L_Q : Matrix (Fin 6) (Fin 6) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => -517 / 576
  | 1, 1 => 1
  | 2, 0 => -517 / 576
  | 2, 1 => -124825 / 181223
  | 2, 2 => 1
  | 3, 0 => -109 / 144
  | 3, 1 => -51076 / 181223
  | 3, 2 => -25538 / 28199
  | 3, 3 => 1
  | 4, 0 => 229 / 576
  | 4, 1 => 609337 / 181223
  | 4, 2 => -8235 / 3188
  | 4, 4 => 1
  | 5, 0 => 229 / 576
  | 5, 1 => -95105 / 25889
  | 5, 2 => 5047 / 3188
  | 5, 4 => -1
  | 5, 5 => 1
  | _, _ => 0

private def D_Q_vec : Fin 6 → ℚ := fun i =>
  match i.val with
  | 0 => 1728
  | 1 => 181223 / 192
  | 2 => 89898412 / 181223
  | 3 => 7221232 / 28199
  | 4 => 3219791 / 3188
  | 5 => 0
  | _ => 0

private def L_R : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 71 / 189
  | 1, 1 => 1
  | 2, 0 => -95 / 378
  | 2, 1 => -9119 / 49447
  | 2, 2 => 1
  | 3, 0 => 71 / 189
  | 3, 1 => -40328 / 49447
  | 3, 2 => -1
  | 3, 3 => 1
  | 4, 0 => -47 / 189
  | 4, 1 => 9119 / 49447
  | 4, 2 => -1
  | 4, 4 => 1
  | _, _ => 0

private def D_R_vec : Fin 5 → ℚ := fun i =>
  match i.val with
  | 0 => 1512
  | 1 => 49447 / 189
  | 2 => 4331525 / 49447
  | 3 => 0
  | 4 => 0
  | _ => 0

private lemma P_ldlt : P_cert = L_P * Matrix.diagonal D_P_vec * L_P.transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [P_cert, L_P, D_P_vec, Fin.sum_univ_eight]

private lemma Q_ldlt : Q_cert = L_Q * Matrix.diagonal D_Q_vec * L_Q.transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Q_cert, L_Q, D_Q_vec, Fin.sum_univ_six]

private lemma R_ldlt : R_cert = L_R * Matrix.diagonal D_R_vec * L_R.transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [R_cert, L_R, D_R_vec, Fin.sum_univ_five]

private lemma D_P_nonneg : ∀ i : Fin 8, 0 ≤ D_P_vec i := by
  intro i
  fin_cases i <;> norm_num [D_P_vec]

private lemma D_Q_nonneg : ∀ i : Fin 6, 0 ≤ D_Q_vec i := by
  intro i
  fin_cases i <;> norm_num [D_Q_vec]

private lemma D_R_nonneg : ∀ i : Fin 5, 0 ≤ D_R_vec i := by
  intro i
  fin_cases i <;> norm_num [D_R_vec]

/-- If `M = L * diag(d) * Lᵀ` with `d ≥ 0`, then `M` is positive semidefinite. -/
lemma psd_of_ldlt {n : ℕ} (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hM : M = L * Matrix.diagonal d * L.transpose) :
    ∀ v : Fin n → ℚ, 0 ≤ dotProduct v (M.mulVec v) := by
  intro v
  have : v ⬝ᵥ (M *ᵥ v) =
      (Lᵀ *ᵥ v) ⬝ᵥ (Matrix.diagonal d *ᵥ (Lᵀ *ᵥ v)) := by
    simp [hM, Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  simp_all [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_nonneg fun i _ => by nlinarith [hd i, mul_self_nonneg ((Lᵀ *ᵥ v) i)]

lemma P_cert_psd : ∀ v : Fin 8 → ℚ, 0 ≤ dotProduct v (P_cert.mulVec v) :=
  psd_of_ldlt P_cert L_P D_P_vec D_P_nonneg P_ldlt

lemma Q_cert_psd : ∀ v : Fin 6 → ℚ, 0 ≤ dotProduct v (Q_cert.mulVec v) :=
  psd_of_ldlt Q_cert L_Q D_Q_vec D_Q_nonneg Q_ldlt

lemma R_cert_psd : ∀ v : Fin 5 → ℚ, 0 ≤ dotProduct v (R_cert.mulVec v) :=
  psd_of_ldlt R_cert L_R D_R_vec D_R_nonneg R_ldlt

/-!
## § 2. Flag Indices and Contributions
-/

/-- Flag index for type σ₀ (no edges among labeled triple). -/
def σ₀FlagIdx (adjDA adjDB adjDC : Bool) : Fin 8 :=
  ⟨(if adjDA then 1 else 0) + (if adjDB then 2 else 0) + (if adjDC then 4 else 0),
   by cases adjDA <;> cases adjDB <;> cases adjDC <;> simp⟩

/-- Flag index for type σ₁ (edge between first two labeled vertices). -/
def σ₁FlagIdx (adjDA adjDB adjDC : Bool) : Option (Fin 6) :=
  match adjDA, adjDB, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | false, true, true => some 5
  | _, _, _ => none

/-- Flag index for type σ₂ (path through center vertex). -/
def σ₂FlagIdx (adjDA adjDCenter adjDC : Bool) : Option (Fin 5) :=
  match adjDA, adjDCenter, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | _, _, _ => none

/-- Contribution of one ordered quintuple to the flag algebra sum. -/
def quintContribOf (adj : Fin 5 → Fin 5 → Bool) (a b c d e : Fin 5) : ℚ :=
  let ab := adj a b
  let ac := adj a c
  let bc := adj b c
  if !ab && !ac && !bc then
    P_cert (σ₀FlagIdx (adj d a) (adj d b) (adj d c))
           (σ₀FlagIdx (adj e a) (adj e b) (adj e c)) / 625
  else if ab && !ac && !bc then
    match σ₁FlagIdx (adj d a) (adj d b) (adj d c),
          σ₁FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => Q_cert fi fj / 2500
    | _, _ => 0
  else if ab && bc && !ac then
    match σ₂FlagIdx (adj d a) (adj d b) (adj d c),
          σ₂FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => R_cert fi fj / 625
    | _, _ => 0
  else 0

/-- Contribution of one ordered quintuple to the flag algebra sum. -/
def quintContrib (adj : Fin 5 → Fin 5 → Bool) (p : Equiv.Perm (Fin 5)) : ℚ :=
  quintContribOf adj (p 0) (p 1) (p 2) (p 3) (p 4)

private def totalFlagPermTuples : List (List (Fin 5)) :=
  [
    [0, 1, 2, 3, 4],
    [0, 1, 2, 4, 3],
    [0, 1, 3, 2, 4],
    [0, 1, 3, 4, 2],
    [0, 1, 4, 2, 3],
    [0, 1, 4, 3, 2],
    [0, 2, 1, 3, 4],
    [0, 2, 1, 4, 3],
    [0, 2, 3, 1, 4],
    [0, 2, 3, 4, 1],
    [0, 2, 4, 1, 3],
    [0, 2, 4, 3, 1],
    [0, 3, 1, 2, 4],
    [0, 3, 1, 4, 2],
    [0, 3, 2, 1, 4],
    [0, 3, 2, 4, 1],
    [0, 3, 4, 1, 2],
    [0, 3, 4, 2, 1],
    [0, 4, 1, 2, 3],
    [0, 4, 1, 3, 2],
    [0, 4, 2, 1, 3],
    [0, 4, 2, 3, 1],
    [0, 4, 3, 1, 2],
    [0, 4, 3, 2, 1],
    [1, 0, 2, 3, 4],
    [1, 0, 2, 4, 3],
    [1, 0, 3, 2, 4],
    [1, 0, 3, 4, 2],
    [1, 0, 4, 2, 3],
    [1, 0, 4, 3, 2],
    [1, 2, 0, 3, 4],
    [1, 2, 0, 4, 3],
    [1, 2, 3, 0, 4],
    [1, 2, 3, 4, 0],
    [1, 2, 4, 0, 3],
    [1, 2, 4, 3, 0],
    [1, 3, 0, 2, 4],
    [1, 3, 0, 4, 2],
    [1, 3, 2, 0, 4],
    [1, 3, 2, 4, 0],
    [1, 3, 4, 0, 2],
    [1, 3, 4, 2, 0],
    [1, 4, 0, 2, 3],
    [1, 4, 0, 3, 2],
    [1, 4, 2, 0, 3],
    [1, 4, 2, 3, 0],
    [1, 4, 3, 0, 2],
    [1, 4, 3, 2, 0],
    [2, 0, 1, 3, 4],
    [2, 0, 1, 4, 3],
    [2, 0, 3, 1, 4],
    [2, 0, 3, 4, 1],
    [2, 0, 4, 1, 3],
    [2, 0, 4, 3, 1],
    [2, 1, 0, 3, 4],
    [2, 1, 0, 4, 3],
    [2, 1, 3, 0, 4],
    [2, 1, 3, 4, 0],
    [2, 1, 4, 0, 3],
    [2, 1, 4, 3, 0],
    [2, 3, 0, 1, 4],
    [2, 3, 0, 4, 1],
    [2, 3, 1, 0, 4],
    [2, 3, 1, 4, 0],
    [2, 3, 4, 0, 1],
    [2, 3, 4, 1, 0],
    [2, 4, 0, 1, 3],
    [2, 4, 0, 3, 1],
    [2, 4, 1, 0, 3],
    [2, 4, 1, 3, 0],
    [2, 4, 3, 0, 1],
    [2, 4, 3, 1, 0],
    [3, 0, 1, 2, 4],
    [3, 0, 1, 4, 2],
    [3, 0, 2, 1, 4],
    [3, 0, 2, 4, 1],
    [3, 0, 4, 1, 2],
    [3, 0, 4, 2, 1],
    [3, 1, 0, 2, 4],
    [3, 1, 0, 4, 2],
    [3, 1, 2, 0, 4],
    [3, 1, 2, 4, 0],
    [3, 1, 4, 0, 2],
    [3, 1, 4, 2, 0],
    [3, 2, 0, 1, 4],
    [3, 2, 0, 4, 1],
    [3, 2, 1, 0, 4],
    [3, 2, 1, 4, 0],
    [3, 2, 4, 0, 1],
    [3, 2, 4, 1, 0],
    [3, 4, 0, 1, 2],
    [3, 4, 0, 2, 1],
    [3, 4, 1, 0, 2],
    [3, 4, 1, 2, 0],
    [3, 4, 2, 0, 1],
    [3, 4, 2, 1, 0],
    [4, 0, 1, 2, 3],
    [4, 0, 1, 3, 2],
    [4, 0, 2, 1, 3],
    [4, 0, 2, 3, 1],
    [4, 0, 3, 1, 2],
    [4, 0, 3, 2, 1],
    [4, 1, 0, 2, 3],
    [4, 1, 0, 3, 2],
    [4, 1, 2, 0, 3],
    [4, 1, 2, 3, 0],
    [4, 1, 3, 0, 2],
    [4, 1, 3, 2, 0],
    [4, 2, 0, 1, 3],
    [4, 2, 0, 3, 1],
    [4, 2, 1, 0, 3],
    [4, 2, 1, 3, 0],
    [4, 2, 3, 0, 1],
    [4, 2, 3, 1, 0],
    [4, 3, 0, 1, 2],
    [4, 3, 0, 2, 1],
    [4, 3, 1, 0, 2],
    [4, 3, 1, 2, 0],
    [4, 3, 2, 0, 1],
    [4, 3, 2, 1, 0]
  ]

private lemma totalFlagPermTuples_nodup : totalFlagPermTuples.Nodup := by
  decide

set_option maxRecDepth 100000 in
-- The generated permutation table proof needs a deeper recursion budget.
private lemma totalFlagPermTuples_toFinset_eq_image :
    totalFlagPermTuples.toFinset =
      Finset.image (fun p : Equiv.Perm (Fin 5) => [p 0, p 1, p 2, p 3, p 4]) Finset.univ := by
  decide

private lemma totalFlagPermTuple_injective :
    Function.Injective (fun p : Equiv.Perm (Fin 5) => [p 0, p 1, p 2, p 3, p 4]) := by
  intro σ τ h
  have h' : σ 0 = τ 0 ∧ σ 1 = τ 1 ∧ σ 2 = τ 2 ∧ σ 3 = τ 3 ∧ σ 4 = τ 4 := by
    simpa using h
  ext i
  fin_cases i
  · exact congrArg Fin.val h'.1
  · exact congrArg Fin.val h'.2.1
  · exact congrArg Fin.val h'.2.2.1
  · exact congrArg Fin.val h'.2.2.2.1
  · exact congrArg Fin.val h'.2.2.2.2

private def totalFlagTupleContrib (adj : Fin 5 → Fin 5 → Bool) : List (Fin 5) → ℚ
  | [a, b, c, d, e] => quintContribOf adj a b c d e
  | _ => 0

private def totalFlagContribPermSum (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  (totalFlagPermTuples.map (totalFlagTupleContrib adj)).sum

private lemma totalFlagContribPermSum_eq_sum_univ (adj : Fin 5 → Fin 5 → Bool) :
    totalFlagContribPermSum adj =
      (Finset.univ : Finset (Equiv.Perm (Fin 5))).sum (quintContrib adj) := by
  unfold totalFlagContribPermSum
  calc
    (totalFlagPermTuples.map (totalFlagTupleContrib adj)).sum =
        totalFlagPermTuples.toFinset.sum (totalFlagTupleContrib adj) := by
      symm
      exact List.sum_toFinset _ totalFlagPermTuples_nodup
    _ = (Finset.univ : Finset (Equiv.Perm (Fin 5))).sum (quintContrib adj) := by
      rw [totalFlagPermTuples_toFinset_eq_image]
      simpa [totalFlagTupleContrib, quintContrib] using
        (Finset.sum_image (s := (Finset.univ : Finset (Equiv.Perm (Fin 5))))
          (g := fun p : Equiv.Perm (Fin 5) => [p 0, p 1, p 2, p 3, p 4])
          (f := totalFlagTupleContrib adj) (by
            intro p _ q _ hpq
            exact totalFlagPermTuple_injective hpq))

/-- Total flag contribution for a graph on `Fin 5`. -/
def totalFlagContribBits (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) : ℚ :=
  match b01, b02, b03, b04, b12, b13, b14, b23, b24, b34 with
  | false, false, false, false, false, false, false, false, false, false => 576 / 125
  | false, false, false, false, false, false, false, false, false, true => 576 / 125
  | false, false, false, false, false, false, false, false, true, false => 576 / 125
  | false, false, false, false, false, false, false, false, true, true => 576 / 125
  | false, false, false, false, false, false, false, true, false, false => 576 / 125
  | false, false, false, false, false, false, false, true, false, true => 576 / 125
  | false, false, false, false, false, false, false, true, true, false => 576 / 125
  | false, false, false, false, false, false, false, true, true, true => 9972 / 625
  | false, false, false, false, false, false, true, false, false, false => 576 / 125
  | false, false, false, false, false, false, true, false, false, true => 576 / 125
  | false, false, false, false, false, false, true, false, true, false => 576 / 125
  | false, false, false, false, false, false, true, false, true, true => 576 / 125
  | false, false, false, false, false, false, true, true, false, false => 576 / 125
  | false, false, false, false, false, false, true, true, false, true => 2826 / 625
  | false, false, false, false, false, false, true, true, true, false => 2826 / 625
  | false, false, false, false, false, false, true, true, true, true => 88 / 125
  | false, false, false, false, false, true, false, false, false, false => 576 / 125
  | false, false, false, false, false, true, false, false, false, true => 576 / 125
  | false, false, false, false, false, true, false, false, true, false => 576 / 125
  | false, false, false, false, false, true, false, false, true, true => 2826 / 625
  | false, false, false, false, false, true, false, true, false, false => 576 / 125
  | false, false, false, false, false, true, false, true, false, true => 576 / 125
  | false, false, false, false, false, true, false, true, true, false => 2826 / 625
  | false, false, false, false, false, true, false, true, true, true => 88 / 125
  | false, false, false, false, false, true, true, false, false, false => 576 / 125
  | false, false, false, false, false, true, true, false, false, true => 9972 / 625
  | false, false, false, false, false, true, true, false, true, false => 2826 / 625
  | false, false, false, false, false, true, true, false, true, true => 88 / 125
  | false, false, false, false, false, true, true, true, false, false => 2826 / 625
  | false, false, false, false, false, true, true, true, false, true => 88 / 125
  | false, false, false, false, false, true, true, true, true, false => 576 / 125
  | false, false, false, false, false, true, true, true, true, true => 2964 / 625
  | false, false, false, false, true, false, false, false, false, false => 576 / 125
  | false, false, false, false, true, false, false, false, false, true => 576 / 125
  | false, false, false, false, true, false, false, false, true, false => 576 / 125
  | false, false, false, false, true, false, false, false, true, true => 2826 / 625
  | false, false, false, false, true, false, false, true, false, false => 576 / 125
  | false, false, false, false, true, false, false, true, false, true => 2826 / 625
  | false, false, false, false, true, false, false, true, true, false => 576 / 125
  | false, false, false, false, true, false, false, true, true, true => 88 / 125
  | false, false, false, false, true, false, true, false, false, false => 576 / 125
  | false, false, false, false, true, false, true, false, false, true => 2826 / 625
  | false, false, false, false, true, false, true, false, true, false => 9972 / 625
  | false, false, false, false, true, false, true, false, true, true => 88 / 125
  | false, false, false, false, true, false, true, true, false, false => 2826 / 625
  | false, false, false, false, true, false, true, true, false, true => 576 / 125
  | false, false, false, false, true, false, true, true, true, false => 88 / 125
  | false, false, false, false, true, false, true, true, true, true => 2964 / 625
  | false, false, false, false, true, true, false, false, false, false => 576 / 125
  | false, false, false, false, true, true, false, false, false, true => 2826 / 625
  | false, false, false, false, true, true, false, false, true, false => 2826 / 625
  | false, false, false, false, true, true, false, false, true, true => 576 / 125
  | false, false, false, false, true, true, false, true, false, false => 9972 / 625
  | false, false, false, false, true, true, false, true, false, true => 88 / 125
  | false, false, false, false, true, true, false, true, true, false => 88 / 125
  | false, false, false, false, true, true, false, true, true, true => 2964 / 625
  | false, false, false, false, true, true, true, false, false, false => 576 / 125
  | false, false, false, false, true, true, true, false, false, true => 88 / 125
  | false, false, false, false, true, true, true, false, true, false => 88 / 125
  | false, false, false, false, true, true, true, false, true, true => 2964 / 625
  | false, false, false, false, true, true, true, true, false, false => 88 / 125
  | false, false, false, false, true, true, true, true, false, true => 2964 / 625
  | false, false, false, false, true, true, true, true, true, false => 2964 / 625
  | false, false, false, false, true, true, true, true, true, true => 0
  | false, false, false, true, false, false, false, false, false, false => 576 / 125
  | false, false, false, true, false, false, false, false, false, true => 576 / 125
  | false, false, false, true, false, false, false, false, true, false => 576 / 125
  | false, false, false, true, false, false, false, false, true, true => 576 / 125
  | false, false, false, true, false, false, false, true, false, false => 576 / 125
  | false, false, false, true, false, false, false, true, false, true => 2826 / 625
  | false, false, false, true, false, false, false, true, true, false => 2826 / 625
  | false, false, false, true, false, false, false, true, true, true => 88 / 125
  | false, false, false, true, false, false, true, false, false, false => 576 / 125
  | false, false, false, true, false, false, true, false, false, true => 576 / 125
  | false, false, false, true, false, false, true, false, true, false => 576 / 125
  | false, false, false, true, false, false, true, false, true, true => 576 / 125
  | false, false, false, true, false, false, true, true, false, false => 2576 / 625
  | false, false, false, true, false, false, true, true, false, true => 576 / 125
  | false, false, false, true, false, false, true, true, true, false => 576 / 125
  | false, false, false, true, false, false, true, true, true, true => 2064 / 625
  | false, false, false, true, false, true, false, false, false, false => 576 / 125
  | false, false, false, true, false, true, false, false, false, true => 2826 / 625
  | false, false, false, true, false, true, false, false, true, false => 2576 / 625
  | false, false, false, true, false, true, false, false, true, true => 576 / 125
  | false, false, false, true, false, true, false, true, false, false => 2576 / 625
  | false, false, false, true, false, true, false, true, false, true => 576 / 125
  | false, false, false, true, false, true, false, true, true, false => -1512 / 625
  | false, false, false, true, false, true, false, true, true, true => 5918 / 625
  | false, false, false, true, false, true, true, false, false, false => 2826 / 625
  | false, false, false, true, false, true, true, false, false, true => 88 / 125
  | false, false, false, true, false, true, true, false, true, false => 576 / 125
  | false, false, false, true, false, true, true, false, true, true => 2064 / 625
  | false, false, false, true, false, true, true, true, false, false => -1512 / 625
  | false, false, false, true, false, true, true, true, false, true => 5918 / 625
  | false, false, false, true, false, true, true, true, true, false => 576 / 125
  | false, false, false, true, false, true, true, true, true, true => -432 / 625
  | false, false, false, true, true, false, false, false, false, false => 576 / 125
  | false, false, false, true, true, false, false, false, false, true => 2576 / 625
  | false, false, false, true, true, false, false, false, true, false => 2826 / 625
  | false, false, false, true, true, false, false, false, true, true => 576 / 125
  | false, false, false, true, true, false, false, true, false, false => 2576 / 625
  | false, false, false, true, true, false, false, true, false, true => -1512 / 625
  | false, false, false, true, true, false, false, true, true, false => 576 / 125
  | false, false, false, true, true, false, false, true, true, true => 5918 / 625
  | false, false, false, true, true, false, true, false, false, false => 2826 / 625
  | false, false, false, true, true, false, true, false, false, true => 576 / 125
  | false, false, false, true, true, false, true, false, true, false => 88 / 125
  | false, false, false, true, true, false, true, false, true, true => 2064 / 625
  | false, false, false, true, true, false, true, true, false, false => -1512 / 625
  | false, false, false, true, true, false, true, true, false, true => 576 / 125
  | false, false, false, true, true, false, true, true, true, false => 5918 / 625
  | false, false, false, true, true, false, true, true, true, true => -432 / 625
  | false, false, false, true, true, true, false, false, false, false => 2576 / 625
  | false, false, false, true, true, true, false, false, false, true => -1512 / 625
  | false, false, false, true, true, true, false, false, true, false => -1512 / 625
  | false, false, false, true, true, true, false, false, true, true => 576 / 125
  | false, false, false, true, true, true, false, true, false, false => 5184 / 625
  | false, false, false, true, true, true, false, true, false, true => 1392 / 625
  | false, false, false, true, true, true, false, true, true, false => 1392 / 625
  | false, false, false, true, true, true, false, true, true, true => 15264 / 625
  | false, false, false, true, true, true, true, false, false, false => 576 / 125
  | false, false, false, true, true, true, true, false, false, true => 5918 / 625
  | false, false, false, true, true, true, true, false, true, false => 5918 / 625
  | false, false, false, true, true, true, true, false, true, true => -432 / 625
  | false, false, false, true, true, true, true, true, false, false => 1392 / 625
  | false, false, false, true, true, true, true, true, false, true => 15264 / 625
  | false, false, false, true, true, true, true, true, true, false => 15264 / 625
  | false, false, false, true, true, true, true, true, true, true => 0
  | false, false, true, false, false, false, false, false, false, false => 576 / 125
  | false, false, true, false, false, false, false, false, false, true => 576 / 125
  | false, false, true, false, false, false, false, false, true, false => 576 / 125
  | false, false, true, false, false, false, false, false, true, true => 2826 / 625
  | false, false, true, false, false, false, false, true, false, false => 576 / 125
  | false, false, true, false, false, false, false, true, false, true => 576 / 125
  | false, false, true, false, false, false, false, true, true, false => 2826 / 625
  | false, false, true, false, false, false, false, true, true, true => 88 / 125
  | false, false, true, false, false, false, true, false, false, false => 576 / 125
  | false, false, true, false, false, false, true, false, false, true => 2826 / 625
  | false, false, true, false, false, false, true, false, true, false => 2576 / 625
  | false, false, true, false, false, false, true, false, true, true => 576 / 125
  | false, false, true, false, false, false, true, true, false, false => 2576 / 625
  | false, false, true, false, false, false, true, true, false, true => 576 / 125
  | false, false, true, false, false, false, true, true, true, false => -1512 / 625
  | false, false, true, false, false, false, true, true, true, true => 5918 / 625
  | false, false, true, false, false, true, false, false, false, false => 576 / 125
  | false, false, true, false, false, true, false, false, false, true => 576 / 125
  | false, false, true, false, false, true, false, false, true, false => 2576 / 625
  | false, false, true, false, false, true, false, false, true, true => 576 / 125
  | false, false, true, false, false, true, false, true, false, false => 576 / 125
  | false, false, true, false, false, true, false, true, false, true => 576 / 125
  | false, false, true, false, false, true, false, true, true, false => 576 / 125
  | false, false, true, false, false, true, false, true, true, true => 2064 / 625
  | false, false, true, false, false, true, true, false, false, false => 2826 / 625
  | false, false, true, false, false, true, true, false, false, true => 88 / 125
  | false, false, true, false, false, true, true, false, true, false => -1512 / 625
  | false, false, true, false, false, true, true, false, true, true => 5918 / 625
  | false, false, true, false, false, true, true, true, false, false => 576 / 125
  | false, false, true, false, false, true, true, true, false, true => 2064 / 625
  | false, false, true, false, false, true, true, true, true, false => 576 / 125
  | false, false, true, false, false, true, true, true, true, true => -432 / 625
  | false, false, true, false, true, false, false, false, false, false => 576 / 125
  | false, false, true, false, true, false, false, false, false, true => 2576 / 625
  | false, false, true, false, true, false, false, false, true, false => 2576 / 625
  | false, false, true, false, true, false, false, false, true, true => -1512 / 625
  | false, false, true, false, true, false, false, true, false, false => 2826 / 625
  | false, false, true, false, true, false, false, true, false, true => 576 / 125
  | false, false, true, false, true, false, false, true, true, false => 576 / 125
  | false, false, true, false, true, false, false, true, true, true => 5918 / 625
  | false, false, true, false, true, false, true, false, false, false => 2576 / 625
  | false, false, true, false, true, false, true, false, false, true => -1512 / 625
  | false, false, true, false, true, false, true, false, true, false => 5184 / 625
  | false, false, true, false, true, false, true, false, true, true => 1392 / 625
  | false, false, true, false, true, false, true, true, false, false => -1512 / 625
  | false, false, true, false, true, false, true, true, false, true => 576 / 125
  | false, false, true, false, true, false, true, true, true, false => 1392 / 625
  | false, false, true, false, true, false, true, true, true, true => 15264 / 625
  | false, false, true, false, true, true, false, false, false, false => 2826 / 625
  | false, false, true, false, true, true, false, false, false, true => 576 / 125
  | false, false, true, false, true, true, false, false, true, false => -1512 / 625
  | false, false, true, false, true, true, false, false, true, true => 576 / 125
  | false, false, true, false, true, true, false, true, false, false => 88 / 125
  | false, false, true, false, true, true, false, true, false, true => 2064 / 625
  | false, false, true, false, true, true, false, true, true, false => 5918 / 625
  | false, false, true, false, true, true, false, true, true, true => -432 / 625
  | false, false, true, false, true, true, true, false, false, false => 576 / 125
  | false, false, true, false, true, true, true, false, false, true => 5918 / 625
  | false, false, true, false, true, true, true, false, true, false => 1392 / 625
  | false, false, true, false, true, true, true, false, true, true => 15264 / 625
  | false, false, true, false, true, true, true, true, false, false => 5918 / 625
  | false, false, true, false, true, true, true, true, false, true => -432 / 625
  | false, false, true, false, true, true, true, true, true, false => 15264 / 625
  | false, false, true, false, true, true, true, true, true, true => 0
  | false, false, true, true, false, false, false, false, false, false => 576 / 125
  | false, false, true, true, false, false, false, false, false, true => 9972 / 625
  | false, false, true, true, false, false, false, false, true, false => 2826 / 625
  | false, false, true, true, false, false, false, false, true, true => 88 / 125
  | false, false, true, true, false, false, false, true, false, false => 2826 / 625
  | false, false, true, true, false, false, false, true, false, true => 88 / 125
  | false, false, true, true, false, false, false, true, true, false => 576 / 125
  | false, false, true, true, false, false, false, true, true, true => 2964 / 625
  | false, false, true, true, false, false, true, false, false, false => 2826 / 625
  | false, false, true, true, false, false, true, false, false, true => 88 / 125
  | false, false, true, true, false, false, true, false, true, false => 576 / 125
  | false, false, true, true, false, false, true, false, true, true => 2064 / 625
  | false, false, true, true, false, false, true, true, false, false => -1512 / 625
  | false, false, true, true, false, false, true, true, false, true => 5918 / 625
  | false, false, true, true, false, false, true, true, true, false => 576 / 125
  | false, false, true, true, false, false, true, true, true, true => -432 / 625
  | false, false, true, true, false, true, false, false, false, false => 2826 / 625
  | false, false, true, true, false, true, false, false, false, true => 88 / 125
  | false, false, true, true, false, true, false, false, true, false => -1512 / 625
  | false, false, true, true, false, true, false, false, true, true => 5918 / 625
  | false, false, true, true, false, true, false, true, false, false => 576 / 125
  | false, false, true, true, false, true, false, true, false, true => 2064 / 625
  | false, false, true, true, false, true, false, true, true, false => 576 / 125
  | false, false, true, true, false, true, false, true, true, true => -432 / 625
  | false, false, true, true, false, true, true, false, false, false => 576 / 125
  | false, false, true, true, false, true, true, false, false, true => 2964 / 625
  | false, false, true, true, false, true, true, false, true, false => 576 / 125
  | false, false, true, true, false, true, true, false, true, true => -432 / 625
  | false, false, true, true, false, true, true, true, false, false => 576 / 125
  | false, false, true, true, false, true, true, true, false, true => -432 / 625
  | false, false, true, true, false, true, true, true, true, false => 576 / 125
  | false, false, true, true, false, true, true, true, true, true => 648 / 625
  | false, false, true, true, true, false, false, false, false, false => 2576 / 625
  | false, false, true, true, true, false, false, false, false, true => 5184 / 625
  | false, false, true, true, true, false, false, false, true, false => -1512 / 625
  | false, false, true, true, true, false, false, false, true, true => 1392 / 625
  | false, false, true, true, true, false, false, true, false, false => -1512 / 625
  | false, false, true, true, true, false, false, true, false, true => 1392 / 625
  | false, false, true, true, true, false, false, true, true, false => 576 / 125
  | false, false, true, true, true, false, false, true, true, true => 15264 / 625
  | false, false, true, true, true, false, true, false, false, false => -1512 / 625
  | false, false, true, true, true, false, true, false, false, true => 1392 / 625
  | false, false, true, true, true, false, true, false, true, false => 1392 / 625
  | false, false, true, true, true, false, true, false, true, true => 0
  | false, false, true, true, true, false, true, true, false, false => -14424 / 125
  | false, false, true, true, true, false, true, true, false, true => -15168 / 625
  | false, false, true, true, true, false, true, true, true, false => -15168 / 625
  | false, false, true, true, true, false, true, true, true, true => 0
  | false, false, true, true, true, true, false, false, false, false => -1512 / 625
  | false, false, true, true, true, true, false, false, false, true => 1392 / 625
  | false, false, true, true, true, true, false, false, true, false => -14424 / 125
  | false, false, true, true, true, true, false, false, true, true => -15168 / 625
  | false, false, true, true, true, true, false, true, false, false => 1392 / 625
  | false, false, true, true, true, true, false, true, false, true => 0
  | false, false, true, true, true, true, false, true, true, false => -15168 / 625
  | false, false, true, true, true, true, false, true, true, true => 0
  | false, false, true, true, true, true, true, false, false, false => 576 / 125
  | false, false, true, true, true, true, true, false, false, true => 15264 / 625
  | false, false, true, true, true, true, true, false, true, false => -15168 / 625
  | false, false, true, true, true, true, true, false, true, true => 0
  | false, false, true, true, true, true, true, true, false, false => -15168 / 625
  | false, false, true, true, true, true, true, true, false, true => 0
  | false, false, true, true, true, true, true, true, true, false => 152 / 125
  | false, false, true, true, true, true, true, true, true, true => 0
  | false, true, false, false, false, false, false, false, false, false => 576 / 125
  | false, true, false, false, false, false, false, false, false, true => 576 / 125
  | false, true, false, false, false, false, false, false, true, false => 576 / 125
  | false, true, false, false, false, false, false, false, true, true => 2826 / 625
  | false, true, false, false, false, false, false, true, false, false => 576 / 125
  | false, true, false, false, false, false, false, true, false, true => 2826 / 625
  | false, true, false, false, false, false, false, true, true, false => 576 / 125
  | false, true, false, false, false, false, false, true, true, true => 88 / 125
  | false, true, false, false, false, false, true, false, false, false => 576 / 125
  | false, true, false, false, false, false, true, false, false, true => 2576 / 625
  | false, true, false, false, false, false, true, false, true, false => 2826 / 625
  | false, true, false, false, false, false, true, false, true, true => 576 / 125
  | false, true, false, false, false, false, true, true, false, false => 2576 / 625
  | false, true, false, false, false, false, true, true, false, true => -1512 / 625
  | false, true, false, false, false, false, true, true, true, false => 576 / 125
  | false, true, false, false, false, false, true, true, true, true => 5918 / 625
  | false, true, false, false, false, true, false, false, false, false => 576 / 125
  | false, true, false, false, false, true, false, false, false, true => 2576 / 625
  | false, true, false, false, false, true, false, false, true, false => 2576 / 625
  | false, true, false, false, false, true, false, false, true, true => -1512 / 625
  | false, true, false, false, false, true, false, true, false, false => 2826 / 625
  | false, true, false, false, false, true, false, true, false, true => 576 / 125
  | false, true, false, false, false, true, false, true, true, false => 576 / 125
  | false, true, false, false, false, true, false, true, true, true => 5918 / 625
  | false, true, false, false, false, true, true, false, false, false => 2576 / 625
  | false, true, false, false, false, true, true, false, false, true => 5184 / 625
  | false, true, false, false, false, true, true, false, true, false => -1512 / 625
  | false, true, false, false, false, true, true, false, true, true => 1392 / 625
  | false, true, false, false, false, true, true, true, false, false => -1512 / 625
  | false, true, false, false, false, true, true, true, false, true => 1392 / 625
  | false, true, false, false, false, true, true, true, true, false => 576 / 125
  | false, true, false, false, false, true, true, true, true, true => 15264 / 625
  | false, true, false, false, true, false, false, false, false, false => 576 / 125
  | false, true, false, false, true, false, false, false, false, true => 2576 / 625
  | false, true, false, false, true, false, false, false, true, false => 576 / 125
  | false, true, false, false, true, false, false, false, true, true => 576 / 125
  | false, true, false, false, true, false, false, true, false, false => 576 / 125
  | false, true, false, false, true, false, false, true, false, true => 576 / 125
  | false, true, false, false, true, false, false, true, true, false => 576 / 125
  | false, true, false, false, true, false, false, true, true, true => 2064 / 625
  | false, true, false, false, true, false, true, false, false, false => 2826 / 625
  | false, true, false, false, true, false, true, false, false, true => -1512 / 625
  | false, true, false, false, true, false, true, false, true, false => 88 / 125
  | false, true, false, false, true, false, true, false, true, true => 5918 / 625
  | false, true, false, false, true, false, true, true, false, false => 576 / 125
  | false, true, false, false, true, false, true, true, false, true => 576 / 125
  | false, true, false, false, true, false, true, true, true, false => 2064 / 625
  | false, true, false, false, true, false, true, true, true, true => -432 / 625
  | false, true, false, false, true, true, false, false, false, false => 2826 / 625
  | false, true, false, false, true, true, false, false, false, true => -1512 / 625
  | false, true, false, false, true, true, false, false, true, false => 576 / 125
  | false, true, false, false, true, true, false, false, true, true => 576 / 125
  | false, true, false, false, true, true, false, true, false, false => 88 / 125
  | false, true, false, false, true, true, false, true, false, true => 5918 / 625
  | false, true, false, false, true, true, false, true, true, false => 2064 / 625
  | false, true, false, false, true, true, false, true, true, true => -432 / 625
  | false, true, false, false, true, true, true, false, false, false => 576 / 125
  | false, true, false, false, true, true, true, false, false, true => 1392 / 625
  | false, true, false, false, true, true, true, false, true, false => 5918 / 625
  | false, true, false, false, true, true, true, false, true, true => 15264 / 625
  | false, true, false, false, true, true, true, true, false, false => 5918 / 625
  | false, true, false, false, true, true, true, true, false, true => 15264 / 625
  | false, true, false, false, true, true, true, true, true, false => -432 / 625
  | false, true, false, false, true, true, true, true, true, true => 0
  | false, true, false, true, false, false, false, false, false, false => 576 / 125
  | false, true, false, true, false, false, false, false, false, true => 2826 / 625
  | false, true, false, true, false, false, false, false, true, false => 9972 / 625
  | false, true, false, true, false, false, false, false, true, true => 88 / 125
  | false, true, false, true, false, false, false, true, false, false => 2826 / 625
  | false, true, false, true, false, false, false, true, false, true => 576 / 125
  | false, true, false, true, false, false, false, true, true, false => 88 / 125
  | false, true, false, true, false, false, false, true, true, true => 2964 / 625
  | false, true, false, true, false, false, true, false, false, false => 2826 / 625
  | false, true, false, true, false, false, true, false, false, true => 576 / 125
  | false, true, false, true, false, false, true, false, true, false => 88 / 125
  | false, true, false, true, false, false, true, false, true, true => 2064 / 625
  | false, true, false, true, false, false, true, true, false, false => -1512 / 625
  | false, true, false, true, false, false, true, true, false, true => 576 / 125
  | false, true, false, true, false, false, true, true, true, false => 5918 / 625
  | false, true, false, true, false, false, true, true, true, true => -432 / 625
  | false, true, false, true, false, true, false, false, false, false => 2576 / 625
  | false, true, false, true, false, true, false, false, false, true => -1512 / 625
  | false, true, false, true, false, true, false, false, true, false => 5184 / 625
  | false, true, false, true, false, true, false, false, true, true => 1392 / 625
  | false, true, false, true, false, true, false, true, false, false => -1512 / 625
  | false, true, false, true, false, true, false, true, false, true => 576 / 125
  | false, true, false, true, false, true, false, true, true, false => 1392 / 625
  | false, true, false, true, false, true, false, true, true, true => 15264 / 625
  | false, true, false, true, false, true, true, false, false, false => -1512 / 625
  | false, true, false, true, false, true, true, false, false, true => 1392 / 625
  | false, true, false, true, false, true, true, false, true, false => 1392 / 625
  | false, true, false, true, false, true, true, false, true, true => 0
  | false, true, false, true, false, true, true, true, false, false => -14424 / 125
  | false, true, false, true, false, true, true, true, false, true => -15168 / 625
  | false, true, false, true, false, true, true, true, true, false => -15168 / 625
  | false, true, false, true, false, true, true, true, true, true => 0
  | false, true, false, true, true, false, false, false, false, false => 2826 / 625
  | false, true, false, true, true, false, false, false, false, true => -1512 / 625
  | false, true, false, true, true, false, false, false, true, false => 88 / 125
  | false, true, false, true, true, false, false, false, true, true => 5918 / 625
  | false, true, false, true, true, false, false, true, false, false => 576 / 125
  | false, true, false, true, true, false, false, true, false, true => 576 / 125
  | false, true, false, true, true, false, false, true, true, false => 2064 / 625
  | false, true, false, true, true, false, false, true, true, true => -432 / 625
  | false, true, false, true, true, false, true, false, false, false => 576 / 125
  | false, true, false, true, true, false, true, false, false, true => 576 / 125
  | false, true, false, true, true, false, true, false, true, false => 2964 / 625
  | false, true, false, true, true, false, true, false, true, true => -432 / 625
  | false, true, false, true, true, false, true, true, false, false => 576 / 125
  | false, true, false, true, true, false, true, true, false, true => 576 / 125
  | false, true, false, true, true, false, true, true, true, false => -432 / 625
  | false, true, false, true, true, false, true, true, true, true => 648 / 625
  | false, true, false, true, true, true, false, false, false, false => -1512 / 625
  | false, true, false, true, true, true, false, false, false, true => -14424 / 125
  | false, true, false, true, true, true, false, false, true, false => 1392 / 625
  | false, true, false, true, true, true, false, false, true, true => -15168 / 625
  | false, true, false, true, true, true, false, true, false, false => 1392 / 625
  | false, true, false, true, true, true, false, true, false, true => -15168 / 625
  | false, true, false, true, true, true, false, true, true, false => 0
  | false, true, false, true, true, true, false, true, true, true => 0
  | false, true, false, true, true, true, true, false, false, false => 576 / 125
  | false, true, false, true, true, true, true, false, false, true => -15168 / 625
  | false, true, false, true, true, true, true, false, true, false => 15264 / 625
  | false, true, false, true, true, true, true, false, true, true => 0
  | false, true, false, true, true, true, true, true, false, false => -15168 / 625
  | false, true, false, true, true, true, true, true, false, true => 152 / 125
  | false, true, false, true, true, true, true, true, true, false => 0
  | false, true, false, true, true, true, true, true, true, true => 0
  | false, true, true, false, false, false, false, false, false, false => 576 / 125
  | false, true, true, false, false, false, false, false, false, true => 2826 / 625
  | false, true, true, false, false, false, false, false, true, false => 2826 / 625
  | false, true, true, false, false, false, false, false, true, true => 576 / 125
  | false, true, true, false, false, false, false, true, false, false => 9972 / 625
  | false, true, true, false, false, false, false, true, false, true => 88 / 125
  | false, true, true, false, false, false, false, true, true, false => 88 / 125
  | false, true, true, false, false, false, false, true, true, true => 2964 / 625
  | false, true, true, false, false, false, true, false, false, false => 2576 / 625
  | false, true, true, false, false, false, true, false, false, true => -1512 / 625
  | false, true, true, false, false, false, true, false, true, false => -1512 / 625
  | false, true, true, false, false, false, true, false, true, true => 576 / 125
  | false, true, true, false, false, false, true, true, false, false => 5184 / 625
  | false, true, true, false, false, false, true, true, false, true => 1392 / 625
  | false, true, true, false, false, false, true, true, true, false => 1392 / 625
  | false, true, true, false, false, false, true, true, true, true => 15264 / 625
  | false, true, true, false, false, true, false, false, false, false => 2826 / 625
  | false, true, true, false, false, true, false, false, false, true => 576 / 125
  | false, true, true, false, false, true, false, false, true, false => -1512 / 625
  | false, true, true, false, false, true, false, false, true, true => 576 / 125
  | false, true, true, false, false, true, false, true, false, false => 88 / 125
  | false, true, true, false, false, true, false, true, false, true => 2064 / 625
  | false, true, true, false, false, true, false, true, true, false => 5918 / 625
  | false, true, true, false, false, true, false, true, true, true => -432 / 625
  | false, true, true, false, false, true, true, false, false, false => -1512 / 625
  | false, true, true, false, false, true, true, false, false, true => 1392 / 625
  | false, true, true, false, false, true, true, false, true, false => -14424 / 125
  | false, true, true, false, false, true, true, false, true, true => -15168 / 625
  | false, true, true, false, false, true, true, true, false, false => 1392 / 625
  | false, true, true, false, false, true, true, true, false, true => 0
  | false, true, true, false, false, true, true, true, true, false => -15168 / 625
  | false, true, true, false, false, true, true, true, true, true => 0
  | false, true, true, false, true, false, false, false, false, false => 2826 / 625
  | false, true, true, false, true, false, false, false, false, true => -1512 / 625
  | false, true, true, false, true, false, false, false, true, false => 576 / 125
  | false, true, true, false, true, false, false, false, true, true => 576 / 125
  | false, true, true, false, true, false, false, true, false, false => 88 / 125
  | false, true, true, false, true, false, false, true, false, true => 5918 / 625
  | false, true, true, false, true, false, false, true, true, false => 2064 / 625
  | false, true, true, false, true, false, false, true, true, true => -432 / 625
  | false, true, true, false, true, false, true, false, false, false => -1512 / 625
  | false, true, true, false, true, false, true, false, false, true => -14424 / 125
  | false, true, true, false, true, false, true, false, true, false => 1392 / 625
  | false, true, true, false, true, false, true, false, true, true => -15168 / 625
  | false, true, true, false, true, false, true, true, false, false => 1392 / 625
  | false, true, true, false, true, false, true, true, false, true => -15168 / 625
  | false, true, true, false, true, false, true, true, true, false => 0
  | false, true, true, false, true, false, true, true, true, true => 0
  | false, true, true, false, true, true, false, false, false, false => 576 / 125
  | false, true, true, false, true, true, false, false, false, true => 576 / 125
  | false, true, true, false, true, true, false, false, true, false => 576 / 125
  | false, true, true, false, true, true, false, false, true, true => 576 / 125
  | false, true, true, false, true, true, false, true, false, false => 2964 / 625
  | false, true, true, false, true, true, false, true, false, true => -432 / 625
  | false, true, true, false, true, true, false, true, true, false => -432 / 625
  | false, true, true, false, true, true, false, true, true, true => 648 / 625
  | false, true, true, false, true, true, true, false, false, false => 576 / 125
  | false, true, true, false, true, true, true, false, false, true => -15168 / 625
  | false, true, true, false, true, true, true, false, true, false => -15168 / 625
  | false, true, true, false, true, true, true, false, true, true => 152 / 125
  | false, true, true, false, true, true, true, true, false, false => 15264 / 625
  | false, true, true, false, true, true, true, true, false, true => 0
  | false, true, true, false, true, true, true, true, true, false => 0
  | false, true, true, false, true, true, true, true, true, true => 0
  | false, true, true, true, false, false, false, false, false, false => 576 / 125
  | false, true, true, true, false, false, false, false, false, true => 88 / 125
  | false, true, true, true, false, false, false, false, true, false => 88 / 125
  | false, true, true, true, false, false, false, false, true, true => 2964 / 625
  | false, true, true, true, false, false, false, true, false, false => 88 / 125
  | false, true, true, true, false, false, false, true, false, true => 2964 / 625
  | false, true, true, true, false, false, false, true, true, false => 2964 / 625
  | false, true, true, true, false, false, false, true, true, true => 0
  | false, true, true, true, false, false, true, false, false, false => 576 / 125
  | false, true, true, true, false, false, true, false, false, true => 5918 / 625
  | false, true, true, true, false, false, true, false, true, false => 5918 / 625
  | false, true, true, true, false, false, true, false, true, true => -432 / 625
  | false, true, true, true, false, false, true, true, false, false => 1392 / 625
  | false, true, true, true, false, false, true, true, false, true => 15264 / 625
  | false, true, true, true, false, false, true, true, true, false => 15264 / 625
  | false, true, true, true, false, false, true, true, true, true => 0
  | false, true, true, true, false, true, false, false, false, false => 576 / 125
  | false, true, true, true, false, true, false, false, false, true => 5918 / 625
  | false, true, true, true, false, true, false, false, true, false => 1392 / 625
  | false, true, true, true, false, true, false, false, true, true => 15264 / 625
  | false, true, true, true, false, true, false, true, false, false => 5918 / 625
  | false, true, true, true, false, true, false, true, false, true => -432 / 625
  | false, true, true, true, false, true, false, true, true, false => 15264 / 625
  | false, true, true, true, false, true, false, true, true, true => 0
  | false, true, true, true, false, true, true, false, false, false => 576 / 125
  | false, true, true, true, false, true, true, false, false, true => 15264 / 625
  | false, true, true, true, false, true, true, false, true, false => -15168 / 625
  | false, true, true, true, false, true, true, false, true, true => 0
  | false, true, true, true, false, true, true, true, false, false => -15168 / 625
  | false, true, true, true, false, true, true, true, false, true => 0
  | false, true, true, true, false, true, true, true, true, false => 152 / 125
  | false, true, true, true, false, true, true, true, true, true => 0
  | false, true, true, true, true, false, false, false, false, false => 576 / 125
  | false, true, true, true, true, false, false, false, false, true => 1392 / 625
  | false, true, true, true, true, false, false, false, true, false => 5918 / 625
  | false, true, true, true, true, false, false, false, true, true => 15264 / 625
  | false, true, true, true, true, false, false, true, false, false => 5918 / 625
  | false, true, true, true, true, false, false, true, false, true => 15264 / 625
  | false, true, true, true, true, false, false, true, true, false => -432 / 625
  | false, true, true, true, true, false, false, true, true, true => 0
  | false, true, true, true, true, false, true, false, false, false => 576 / 125
  | false, true, true, true, true, false, true, false, false, true => -15168 / 625
  | false, true, true, true, true, false, true, false, true, false => 15264 / 625
  | false, true, true, true, true, false, true, false, true, true => 0
  | false, true, true, true, true, false, true, true, false, false => -15168 / 625
  | false, true, true, true, true, false, true, true, false, true => 152 / 125
  | false, true, true, true, true, false, true, true, true, false => 0
  | false, true, true, true, true, false, true, true, true, true => 0
  | false, true, true, true, true, true, false, false, false, false => 576 / 125
  | false, true, true, true, true, true, false, false, false, true => -15168 / 625
  | false, true, true, true, true, true, false, false, true, false => -15168 / 625
  | false, true, true, true, true, true, false, false, true, true => 152 / 125
  | false, true, true, true, true, true, false, true, false, false => 15264 / 625
  | false, true, true, true, true, true, false, true, false, true => 0
  | false, true, true, true, true, true, false, true, true, false => 0
  | false, true, true, true, true, true, false, true, true, true => 0
  | false, true, true, true, true, true, true, false, false, false => 576 / 125
  | false, true, true, true, true, true, true, false, false, true => 152 / 125
  | false, true, true, true, true, true, true, false, true, false => 152 / 125
  | false, true, true, true, true, true, true, false, true, true => 0
  | false, true, true, true, true, true, true, true, false, false => 152 / 125
  | false, true, true, true, true, true, true, true, false, true => 0
  | false, true, true, true, true, true, true, true, true, false => 0
  | false, true, true, true, true, true, true, true, true, true => 0
  | true, false, false, false, false, false, false, false, false, false => 576 / 125
  | true, false, false, false, false, false, false, false, false, true => 576 / 125
  | true, false, false, false, false, false, false, false, true, false => 576 / 125
  | true, false, false, false, false, false, false, false, true, true => 2576 / 625
  | true, false, false, false, false, false, false, true, false, false => 576 / 125
  | true, false, false, false, false, false, false, true, false, true => 2576 / 625
  | true, false, false, false, false, false, false, true, true, false => 2576 / 625
  | true, false, false, false, false, false, false, true, true, true => 5184 / 625
  | true, false, false, false, false, false, true, false, false, false => 576 / 125
  | true, false, false, false, false, false, true, false, false, true => 2826 / 625
  | true, false, false, false, false, false, true, false, true, false => 2826 / 625
  | true, false, false, false, false, false, true, false, true, true => 576 / 125
  | true, false, false, false, false, false, true, true, false, false => 2576 / 625
  | true, false, false, false, false, false, true, true, false, true => -1512 / 625
  | true, false, false, false, false, false, true, true, true, false => -1512 / 625
  | true, false, false, false, false, false, true, true, true, true => 1392 / 625
  | true, false, false, false, false, true, false, false, false, false => 576 / 125
  | true, false, false, false, false, true, false, false, false, true => 2826 / 625
  | true, false, false, false, false, true, false, false, true, false => 2576 / 625
  | true, false, false, false, false, true, false, false, true, true => -1512 / 625
  | true, false, false, false, false, true, false, true, false, false => 2826 / 625
  | true, false, false, false, false, true, false, true, false, true => 576 / 125
  | true, false, false, false, false, true, false, true, true, false => -1512 / 625
  | true, false, false, false, false, true, false, true, true, true => 1392 / 625
  | true, false, false, false, false, true, true, false, false, false => 576 / 125
  | true, false, false, false, false, true, true, false, false, true => 88 / 125
  | true, false, false, false, false, true, true, false, true, false => 576 / 125
  | true, false, false, false, false, true, true, false, true, true => 5918 / 625
  | true, false, false, false, false, true, true, true, false, false => 576 / 125
  | true, false, false, false, false, true, true, true, false, true => 5918 / 625
  | true, false, false, false, false, true, true, true, true, false => 576 / 125
  | true, false, false, false, false, true, true, true, true, true => 15264 / 625
  | true, false, false, false, true, false, false, false, false, false => 576 / 125
  | true, false, false, false, true, false, false, false, false, true => 2576 / 625
  | true, false, false, false, true, false, false, false, true, false => 2826 / 625
  | true, false, false, false, true, false, false, false, true, true => -1512 / 625
  | true, false, false, false, true, false, false, true, false, false => 2826 / 625
  | true, false, false, false, true, false, false, true, false, true => -1512 / 625
  | true, false, false, false, true, false, false, true, true, false => 576 / 125
  | true, false, false, false, true, false, false, true, true, true => 1392 / 625
  | true, false, false, false, true, false, true, false, false, false => 576 / 125
  | true, false, false, false, true, false, true, false, false, true => 576 / 125
  | true, false, false, false, true, false, true, false, true, false => 88 / 125
  | true, false, false, false, true, false, true, false, true, true => 5918 / 625
  | true, false, false, false, true, false, true, true, false, false => 576 / 125
  | true, false, false, false, true, false, true, true, false, true => 576 / 125
  | true, false, false, false, true, false, true, true, true, false => 5918 / 625
  | true, false, false, false, true, false, true, true, true, true => 15264 / 625
  | true, false, false, false, true, true, false, false, false, false => 576 / 125
  | true, false, false, false, true, true, false, false, false, true => 576 / 125
  | true, false, false, false, true, true, false, false, true, false => 576 / 125
  | true, false, false, false, true, true, false, false, true, true => 576 / 125
  | true, false, false, false, true, true, false, true, false, false => 88 / 125
  | true, false, false, false, true, true, false, true, false, true => 5918 / 625
  | true, false, false, false, true, true, false, true, true, false => 5918 / 625
  | true, false, false, false, true, true, false, true, true, true => 15264 / 625
  | true, false, false, false, true, true, true, false, false, false => 576 / 125
  | true, false, false, false, true, true, true, false, false, true => 2064 / 625
  | true, false, false, false, true, true, true, false, true, false => 2064 / 625
  | true, false, false, false, true, true, true, false, true, true => -432 / 625
  | true, false, false, false, true, true, true, true, false, false => 2064 / 625
  | true, false, false, false, true, true, true, true, false, true => -432 / 625
  | true, false, false, false, true, true, true, true, true, false => -432 / 625
  | true, false, false, false, true, true, true, true, true, true => 0
  | true, false, false, true, false, false, false, false, false, false => 576 / 125
  | true, false, false, true, false, false, false, false, false, true => 2826 / 625
  | true, false, false, true, false, false, false, false, true, false => 2826 / 625
  | true, false, false, true, false, false, false, false, true, true => 576 / 125
  | true, false, false, true, false, false, false, true, false, false => 2576 / 625
  | true, false, false, true, false, false, false, true, false, true => -1512 / 625
  | true, false, false, true, false, false, false, true, true, false => -1512 / 625
  | true, false, false, true, false, false, false, true, true, true => 1392 / 625
  | true, false, false, true, false, false, true, false, false, false => 9972 / 625
  | true, false, false, true, false, false, true, false, false, true => 88 / 125
  | true, false, false, true, false, false, true, false, true, false => 88 / 125
  | true, false, false, true, false, false, true, false, true, true => 2064 / 625
  | true, false, false, true, false, false, true, true, false, false => 5184 / 625
  | true, false, false, true, false, false, true, true, false, true => 1392 / 625
  | true, false, false, true, false, false, true, true, true, false => 1392 / 625
  | true, false, false, true, false, false, true, true, true, true => 0
  | true, false, false, true, false, true, false, false, false, false => 2826 / 625
  | true, false, false, true, false, true, false, false, false, true => 576 / 125
  | true, false, false, true, false, true, false, false, true, false => -1512 / 625
  | true, false, false, true, false, true, false, false, true, true => 576 / 125
  | true, false, false, true, false, true, false, true, false, false => -1512 / 625
  | true, false, false, true, false, true, false, true, false, true => 576 / 125
  | true, false, false, true, false, true, false, true, true, false => -14424 / 125
  | true, false, false, true, false, true, false, true, true, true => -15168 / 625
  | true, false, false, true, false, true, true, false, false, false => 88 / 125
  | true, false, false, true, false, true, true, false, false, true => 2964 / 625
  | true, false, false, true, false, true, true, false, true, false => 5918 / 625
  | true, false, false, true, false, true, true, false, true, true => -432 / 625
  | true, false, false, true, false, true, true, true, false, false => 1392 / 625
  | true, false, false, true, false, true, true, true, false, true => 15264 / 625
  | true, false, false, true, false, true, true, true, true, false => -15168 / 625
  | true, false, false, true, false, true, true, true, true, true => 0
  | true, false, false, true, true, false, false, false, false, false => 2826 / 625
  | true, false, false, true, true, false, false, false, false, true => -1512 / 625
  | true, false, false, true, true, false, false, false, true, false => 576 / 125
  | true, false, false, true, true, false, false, false, true, true => 576 / 125
  | true, false, false, true, true, false, false, true, false, false => -1512 / 625
  | true, false, false, true, true, false, false, true, false, true => -14424 / 125
  | true, false, false, true, true, false, false, true, true, false => 576 / 125
  | true, false, false, true, true, false, false, true, true, true => -15168 / 625
  | true, false, false, true, true, false, true, false, false, false => 88 / 125
  | true, false, false, true, true, false, true, false, false, true => 5918 / 625
  | true, false, false, true, true, false, true, false, true, false => 2964 / 625
  | true, false, false, true, true, false, true, false, true, true => -432 / 625
  | true, false, false, true, true, false, true, true, false, false => 1392 / 625
  | true, false, false, true, true, false, true, true, false, true => -15168 / 625
  | true, false, false, true, true, false, true, true, true, false => 15264 / 625
  | true, false, false, true, true, false, true, true, true, true => 0
  | true, false, false, true, true, true, false, false, false, false => 576 / 125
  | true, false, false, true, true, true, false, false, false, true => 576 / 125
  | true, false, false, true, true, true, false, false, true, false => 576 / 125
  | true, false, false, true, true, true, false, false, true, true => 576 / 125
  | true, false, false, true, true, true, false, true, false, false => 1392 / 625
  | true, false, false, true, true, true, false, true, false, true => -15168 / 625
  | true, false, false, true, true, true, false, true, true, false => -15168 / 625
  | true, false, false, true, true, true, false, true, true, true => 152 / 125
  | true, false, false, true, true, true, true, false, false, false => 2064 / 625
  | true, false, false, true, true, true, true, false, false, true => -432 / 625
  | true, false, false, true, true, true, true, false, true, false => -432 / 625
  | true, false, false, true, true, true, true, false, true, true => 648 / 625
  | true, false, false, true, true, true, true, true, false, false => 0
  | true, false, false, true, true, true, true, true, false, true => 0
  | true, false, false, true, true, true, true, true, true, false => 0
  | true, false, false, true, true, true, true, true, true, true => 0
  | true, false, true, false, false, false, false, false, false, false => 576 / 125
  | true, false, true, false, false, false, false, false, false, true => 2826 / 625
  | true, false, true, false, false, false, false, false, true, false => 2576 / 625
  | true, false, true, false, false, false, false, false, true, true => -1512 / 625
  | true, false, true, false, false, false, false, true, false, false => 2826 / 625
  | true, false, true, false, false, false, false, true, false, true => 576 / 125
  | true, false, true, false, false, false, false, true, true, false => -1512 / 625
  | true, false, true, false, false, false, false, true, true, true => 1392 / 625
  | true, false, true, false, false, false, true, false, false, false => 2826 / 625
  | true, false, true, false, false, false, true, false, false, true => 576 / 125
  | true, false, true, false, false, false, true, false, true, false => -1512 / 625
  | true, false, true, false, false, false, true, false, true, true => 576 / 125
  | true, false, true, false, false, false, true, true, false, false => -1512 / 625
  | true, false, true, false, false, false, true, true, false, true => 576 / 125
  | true, false, true, false, false, false, true, true, true, false => -14424 / 125
  | true, false, true, false, false, false, true, true, true, true => -15168 / 625
  | true, false, true, false, false, true, false, false, false, false => 9972 / 625
  | true, false, true, false, false, true, false, false, false, true => 88 / 125
  | true, false, true, false, false, true, false, false, true, false => 5184 / 625
  | true, false, true, false, false, true, false, false, true, true => 1392 / 625
  | true, false, true, false, false, true, false, true, false, false => 88 / 125
  | true, false, true, false, false, true, false, true, false, true => 2064 / 625
  | true, false, true, false, false, true, false, true, true, false => 1392 / 625
  | true, false, true, false, false, true, false, true, true, true => 0
  | true, false, true, false, false, true, true, false, false, false => 88 / 125
  | true, false, true, false, false, true, true, false, false, true => 2964 / 625
  | true, false, true, false, false, true, true, false, true, false => 1392 / 625
  | true, false, true, false, false, true, true, false, true, true => 15264 / 625
  | true, false, true, false, false, true, true, true, false, false => 5918 / 625
  | true, false, true, false, false, true, true, true, false, true => -432 / 625
  | true, false, true, false, false, true, true, true, true, false => -15168 / 625
  | true, false, true, false, false, true, true, true, true, true => 0
  | true, false, true, false, true, false, false, false, false, false => 2826 / 625
  | true, false, true, false, true, false, false, false, false, true => -1512 / 625
  | true, false, true, false, true, false, false, false, true, false => -1512 / 625
  | true, false, true, false, true, false, false, false, true, true => -14424 / 125
  | true, false, true, false, true, false, false, true, false, false => 576 / 125
  | true, false, true, false, true, false, false, true, false, true => 576 / 125
  | true, false, true, false, true, false, false, true, true, false => 576 / 125
  | true, false, true, false, true, false, false, true, true, true => -15168 / 625
  | true, false, true, false, true, false, true, false, false, false => 576 / 125
  | true, false, true, false, true, false, true, false, false, true => 576 / 125
  | true, false, true, false, true, false, true, false, true, false => 1392 / 625
  | true, false, true, false, true, false, true, false, true, true => -15168 / 625
  | true, false, true, false, true, false, true, true, false, false => 576 / 125
  | true, false, true, false, true, false, true, true, false, true => 576 / 125
  | true, false, true, false, true, false, true, true, true, false => -15168 / 625
  | true, false, true, false, true, false, true, true, true, true => 152 / 125
  | true, false, true, false, true, true, false, false, false, false => 88 / 125
  | true, false, true, false, true, true, false, false, false, true => 5918 / 625
  | true, false, true, false, true, true, false, false, true, false => 1392 / 625
  | true, false, true, false, true, true, false, false, true, true => -15168 / 625
  | true, false, true, false, true, true, false, true, false, false => 2964 / 625
  | true, false, true, false, true, true, false, true, false, true => -432 / 625
  | true, false, true, false, true, true, false, true, true, false => 15264 / 625
  | true, false, true, false, true, true, false, true, true, true => 0
  | true, false, true, false, true, true, true, false, false, false => 2064 / 625
  | true, false, true, false, true, true, true, false, false, true => -432 / 625
  | true, false, true, false, true, true, true, false, true, false => 0
  | true, false, true, false, true, true, true, false, true, true => 0
  | true, false, true, false, true, true, true, true, false, false => -432 / 625
  | true, false, true, false, true, true, true, true, false, true => 648 / 625
  | true, false, true, false, true, true, true, true, true, false => 0
  | true, false, true, false, true, true, true, true, true, true => 0
  | true, false, true, true, false, false, false, false, false, false => 576 / 125
  | true, false, true, true, false, false, false, false, false, true => 88 / 125
  | true, false, true, true, false, false, false, false, true, false => 576 / 125
  | true, false, true, true, false, false, false, false, true, true => 5918 / 625
  | true, false, true, true, false, false, false, true, false, false => 576 / 125
  | true, false, true, true, false, false, false, true, false, true => 5918 / 625
  | true, false, true, true, false, false, false, true, true, false => 576 / 125
  | true, false, true, true, false, false, false, true, true, true => 15264 / 625
  | true, false, true, true, false, false, true, false, false, false => 88 / 125
  | true, false, true, true, false, false, true, false, false, true => 2964 / 625
  | true, false, true, true, false, false, true, false, true, false => 5918 / 625
  | true, false, true, true, false, false, true, false, true, true => -432 / 625
  | true, false, true, true, false, false, true, true, false, false => 1392 / 625
  | true, false, true, true, false, false, true, true, false, true => 15264 / 625
  | true, false, true, true, false, false, true, true, true, false => -15168 / 625
  | true, false, true, true, false, false, true, true, true, true => 0
  | true, false, true, true, false, true, false, false, false, false => 88 / 125
  | true, false, true, true, false, true, false, false, false, true => 2964 / 625
  | true, false, true, true, false, true, false, false, true, false => 1392 / 625
  | true, false, true, true, false, true, false, false, true, true => 15264 / 625
  | true, false, true, true, false, true, false, true, false, false => 5918 / 625
  | true, false, true, true, false, true, false, true, false, true => -432 / 625
  | true, false, true, true, false, true, false, true, true, false => -15168 / 625
  | true, false, true, true, false, true, false, true, true, true => 0
  | true, false, true, true, false, true, true, false, false, false => 2964 / 625
  | true, false, true, true, false, true, true, false, false, true => 0
  | true, false, true, true, false, true, true, false, true, false => 15264 / 625
  | true, false, true, true, false, true, true, false, true, true => 0
  | true, false, true, true, false, true, true, true, false, false => 15264 / 625
  | true, false, true, true, false, true, true, true, false, true => 0
  | true, false, true, true, false, true, true, true, true, false => 152 / 125
  | true, false, true, true, false, true, true, true, true, true => 0
  | true, false, true, true, true, false, false, false, false, false => 576 / 125
  | true, false, true, true, true, false, false, false, false, true => 1392 / 625
  | true, false, true, true, true, false, false, false, true, false => 576 / 125
  | true, false, true, true, true, false, false, false, true, true => -15168 / 625
  | true, false, true, true, true, false, false, true, false, false => 576 / 125
  | true, false, true, true, true, false, false, true, false, true => -15168 / 625
  | true, false, true, true, true, false, false, true, true, false => 576 / 125
  | true, false, true, true, true, false, false, true, true, true => 152 / 125
  | true, false, true, true, true, false, true, false, false, false => 5918 / 625
  | true, false, true, true, true, false, true, false, false, true => 15264 / 625
  | true, false, true, true, true, false, true, false, true, false => 15264 / 625
  | true, false, true, true, true, false, true, false, true, true => 0
  | true, false, true, true, true, false, true, true, false, false => -15168 / 625
  | true, false, true, true, true, false, true, true, false, true => 152 / 125
  | true, false, true, true, true, false, true, true, true, false => 152 / 125
  | true, false, true, true, true, false, true, true, true, true => 0
  | true, false, true, true, true, true, false, false, false, false => 5918 / 625
  | true, false, true, true, true, true, false, false, false, true => 15264 / 625
  | true, false, true, true, true, true, false, false, true, false => -15168 / 625
  | true, false, true, true, true, true, false, false, true, true => 152 / 125
  | true, false, true, true, true, true, false, true, false, false => 15264 / 625
  | true, false, true, true, true, true, false, true, false, true => 0
  | true, false, true, true, true, true, false, true, true, false => 152 / 125
  | true, false, true, true, true, true, false, true, true, true => 0
  | true, false, true, true, true, true, true, false, false, false => -432 / 625
  | true, false, true, true, true, true, true, false, false, true => 0
  | true, false, true, true, true, true, true, false, true, false => 0
  | true, false, true, true, true, true, true, false, true, true => 0
  | true, false, true, true, true, true, true, true, false, false => 0
  | true, false, true, true, true, true, true, true, false, true => 0
  | true, false, true, true, true, true, true, true, true, false => 0
  | true, false, true, true, true, true, true, true, true, true => 0
  | true, true, false, false, false, false, false, false, false, false => 576 / 125
  | true, true, false, false, false, false, false, false, false, true => 2576 / 625
  | true, true, false, false, false, false, false, false, true, false => 2826 / 625
  | true, true, false, false, false, false, false, false, true, true => -1512 / 625
  | true, true, false, false, false, false, false, true, false, false => 2826 / 625
  | true, true, false, false, false, false, false, true, false, true => -1512 / 625
  | true, true, false, false, false, false, false, true, true, false => 576 / 125
  | true, true, false, false, false, false, false, true, true, true => 1392 / 625
  | true, true, false, false, false, false, true, false, false, false => 2826 / 625
  | true, true, false, false, false, false, true, false, false, true => -1512 / 625
  | true, true, false, false, false, false, true, false, true, false => 576 / 125
  | true, true, false, false, false, false, true, false, true, true => 576 / 125
  | true, true, false, false, false, false, true, true, false, false => -1512 / 625
  | true, true, false, false, false, false, true, true, false, true => -14424 / 125
  | true, true, false, false, false, false, true, true, true, false => 576 / 125
  | true, true, false, false, false, false, true, true, true, true => -15168 / 625
  | true, true, false, false, false, true, false, false, false, false => 2826 / 625
  | true, true, false, false, false, true, false, false, false, true => -1512 / 625
  | true, true, false, false, false, true, false, false, true, false => -1512 / 625
  | true, true, false, false, false, true, false, false, true, true => -14424 / 125
  | true, true, false, false, false, true, false, true, false, false => 576 / 125
  | true, true, false, false, false, true, false, true, false, true => 576 / 125
  | true, true, false, false, false, true, false, true, true, false => 576 / 125
  | true, true, false, false, false, true, false, true, true, true => -15168 / 625
  | true, true, false, false, false, true, true, false, false, false => 576 / 125
  | true, true, false, false, false, true, true, false, false, true => 1392 / 625
  | true, true, false, false, false, true, true, false, true, false => 576 / 125
  | true, true, false, false, false, true, true, false, true, true => -15168 / 625
  | true, true, false, false, false, true, true, true, false, false => 576 / 125
  | true, true, false, false, false, true, true, true, false, true => -15168 / 625
  | true, true, false, false, false, true, true, true, true, false => 576 / 125
  | true, true, false, false, false, true, true, true, true, true => 152 / 125
  | true, true, false, false, true, false, false, false, false, false => 9972 / 625
  | true, true, false, false, true, false, false, false, false, true => 5184 / 625
  | true, true, false, false, true, false, false, false, true, false => 88 / 125
  | true, true, false, false, true, false, false, false, true, true => 1392 / 625
  | true, true, false, false, true, false, false, true, false, false => 88 / 125
  | true, true, false, false, true, false, false, true, false, true => 1392 / 625
  | true, true, false, false, true, false, false, true, true, false => 2064 / 625
  | true, true, false, false, true, false, false, true, true, true => 0
  | true, true, false, false, true, false, true, false, false, false => 88 / 125
  | true, true, false, false, true, false, true, false, false, true => 1392 / 625
  | true, true, false, false, true, false, true, false, true, false => 2964 / 625
  | true, true, false, false, true, false, true, false, true, true => 15264 / 625
  | true, true, false, false, true, false, true, true, false, false => 5918 / 625
  | true, true, false, false, true, false, true, true, false, true => -15168 / 625
  | true, true, false, false, true, false, true, true, true, false => -432 / 625
  | true, true, false, false, true, false, true, true, true, true => 0
  | true, true, false, false, true, true, false, false, false, false => 88 / 125
  | true, true, false, false, true, true, false, false, false, true => 1392 / 625
  | true, true, false, false, true, true, false, false, true, false => 5918 / 625
  | true, true, false, false, true, true, false, false, true, true => -15168 / 625
  | true, true, false, false, true, true, false, true, false, false => 2964 / 625
  | true, true, false, false, true, true, false, true, false, true => 15264 / 625
  | true, true, false, false, true, true, false, true, true, false => -432 / 625
  | true, true, false, false, true, true, false, true, true, true => 0
  | true, true, false, false, true, true, true, false, false, false => 2064 / 625
  | true, true, false, false, true, true, true, false, false, true => 0
  | true, true, false, false, true, true, true, false, true, false => -432 / 625
  | true, true, false, false, true, true, true, false, true, true => 0
  | true, true, false, false, true, true, true, true, false, false => -432 / 625
  | true, true, false, false, true, true, true, true, false, true => 0
  | true, true, false, false, true, true, true, true, true, false => 648 / 625
  | true, true, false, false, true, true, true, true, true, true => 0
  | true, true, false, true, false, false, false, false, false, false => 576 / 125
  | true, true, false, true, false, false, false, false, false, true => 576 / 125
  | true, true, false, true, false, false, false, false, true, false => 88 / 125
  | true, true, false, true, false, false, false, false, true, true => 5918 / 625
  | true, true, false, true, false, false, false, true, false, false => 576 / 125
  | true, true, false, true, false, false, false, true, false, true => 576 / 125
  | true, true, false, true, false, false, false, true, true, false => 5918 / 625
  | true, true, false, true, false, false, false, true, true, true => 15264 / 625
  | true, true, false, true, false, false, true, false, false, false => 88 / 125
  | true, true, false, true, false, false, true, false, false, true => 5918 / 625
  | true, true, false, true, false, false, true, false, true, false => 2964 / 625
  | true, true, false, true, false, false, true, false, true, true => -432 / 625
  | true, true, false, true, false, false, true, true, false, false => 1392 / 625
  | true, true, false, true, false, false, true, true, false, true => -15168 / 625
  | true, true, false, true, false, false, true, true, true, false => 15264 / 625
  | true, true, false, true, false, false, true, true, true, true => 0
  | true, true, false, true, false, true, false, false, false, false => 576 / 125
  | true, true, false, true, false, true, false, false, false, true => 576 / 125
  | true, true, false, true, false, true, false, false, true, false => 1392 / 625
  | true, true, false, true, false, true, false, false, true, true => -15168 / 625
  | true, true, false, true, false, true, false, true, false, false => 576 / 125
  | true, true, false, true, false, true, false, true, false, true => 576 / 125
  | true, true, false, true, false, true, false, true, true, false => -15168 / 625
  | true, true, false, true, false, true, false, true, true, true => 152 / 125
  | true, true, false, true, false, true, true, false, false, false => 5918 / 625
  | true, true, false, true, false, true, true, false, false, true => 15264 / 625
  | true, true, false, true, false, true, true, false, true, false => 15264 / 625
  | true, true, false, true, false, true, true, false, true, true => 0
  | true, true, false, true, false, true, true, true, false, false => -15168 / 625
  | true, true, false, true, false, true, true, true, false, true => 152 / 125
  | true, true, false, true, false, true, true, true, true, false => 152 / 125
  | true, true, false, true, false, true, true, true, true, true => 0
  | true, true, false, true, true, false, false, false, false, false => 88 / 125
  | true, true, false, true, true, false, false, false, false, true => 1392 / 625
  | true, true, false, true, true, false, false, false, true, false => 2964 / 625
  | true, true, false, true, true, false, false, false, true, true => 15264 / 625
  | true, true, false, true, true, false, false, true, false, false => 5918 / 625
  | true, true, false, true, true, false, false, true, false, true => -15168 / 625
  | true, true, false, true, true, false, false, true, true, false => -432 / 625
  | true, true, false, true, true, false, false, true, true, true => 0
  | true, true, false, true, true, false, true, false, false, false => 2964 / 625
  | true, true, false, true, true, false, true, false, false, true => 15264 / 625
  | true, true, false, true, true, false, true, false, true, false => 0
  | true, true, false, true, true, false, true, false, true, true => 0
  | true, true, false, true, true, false, true, true, false, false => 15264 / 625
  | true, true, false, true, true, false, true, true, false, true => 152 / 125
  | true, true, false, true, true, false, true, true, true, false => 0
  | true, true, false, true, true, false, true, true, true, true => 0
  | true, true, false, true, true, true, false, false, false, false => 5918 / 625
  | true, true, false, true, true, true, false, false, false, true => -15168 / 625
  | true, true, false, true, true, true, false, false, true, false => 15264 / 625
  | true, true, false, true, true, true, false, false, true, true => 152 / 125
  | true, true, false, true, true, true, false, true, false, false => 15264 / 625
  | true, true, false, true, true, true, false, true, false, true => 152 / 125
  | true, true, false, true, true, true, false, true, true, false => 0
  | true, true, false, true, true, true, false, true, true, true => 0
  | true, true, false, true, true, true, true, false, false, false => -432 / 625
  | true, true, false, true, true, true, true, false, false, true => 0
  | true, true, false, true, true, true, true, false, true, false => 0
  | true, true, false, true, true, true, true, false, true, true => 0
  | true, true, false, true, true, true, true, true, false, false => 0
  | true, true, false, true, true, true, true, true, false, true => 0
  | true, true, false, true, true, true, true, true, true, false => 0
  | true, true, false, true, true, true, true, true, true, true => 0
  | true, true, true, false, false, false, false, false, false, false => 576 / 125
  | true, true, true, false, false, false, false, false, false, true => 576 / 125
  | true, true, true, false, false, false, false, false, true, false => 576 / 125
  | true, true, true, false, false, false, false, false, true, true => 576 / 125
  | true, true, true, false, false, false, false, true, false, false => 88 / 125
  | true, true, true, false, false, false, false, true, false, true => 5918 / 625
  | true, true, true, false, false, false, false, true, true, false => 5918 / 625
  | true, true, true, false, false, false, false, true, true, true => 15264 / 625
  | true, true, true, false, false, false, true, false, false, false => 576 / 125
  | true, true, true, false, false, false, true, false, false, true => 576 / 125
  | true, true, true, false, false, false, true, false, true, false => 576 / 125
  | true, true, true, false, false, false, true, false, true, true => 576 / 125
  | true, true, true, false, false, false, true, true, false, false => 1392 / 625
  | true, true, true, false, false, false, true, true, false, true => -15168 / 625
  | true, true, true, false, false, false, true, true, true, false => -15168 / 625
  | true, true, true, false, false, false, true, true, true, true => 152 / 125
  | true, true, true, false, false, true, false, false, false, false => 88 / 125
  | true, true, true, false, false, true, false, false, false, true => 5918 / 625
  | true, true, true, false, false, true, false, false, true, false => 1392 / 625
  | true, true, true, false, false, true, false, false, true, true => -15168 / 625
  | true, true, true, false, false, true, false, true, false, false => 2964 / 625
  | true, true, true, false, false, true, false, true, false, true => -432 / 625
  | true, true, true, false, false, true, false, true, true, false => 15264 / 625
  | true, true, true, false, false, true, false, true, true, true => 0
  | true, true, true, false, false, true, true, false, false, false => 5918 / 625
  | true, true, true, false, false, true, true, false, false, true => 15264 / 625
  | true, true, true, false, false, true, true, false, true, false => -15168 / 625
  | true, true, true, false, false, true, true, false, true, true => 152 / 125
  | true, true, true, false, false, true, true, true, false, false => 15264 / 625
  | true, true, true, false, false, true, true, true, false, true => 0
  | true, true, true, false, false, true, true, true, true, false => 152 / 125
  | true, true, true, false, false, true, true, true, true, true => 0
  | true, true, true, false, true, false, false, false, false, false => 88 / 125
  | true, true, true, false, true, false, false, false, false, true => 1392 / 625
  | true, true, true, false, true, false, false, false, true, false => 5918 / 625
  | true, true, true, false, true, false, false, false, true, true => -15168 / 625
  | true, true, true, false, true, false, false, true, false, false => 2964 / 625
  | true, true, true, false, true, false, false, true, false, true => 15264 / 625
  | true, true, true, false, true, false, false, true, true, false => -432 / 625
  | true, true, true, false, true, false, false, true, true, true => 0
  | true, true, true, false, true, false, true, false, false, false => 5918 / 625
  | true, true, true, false, true, false, true, false, false, true => -15168 / 625
  | true, true, true, false, true, false, true, false, true, false => 15264 / 625
  | true, true, true, false, true, false, true, false, true, true => 152 / 125
  | true, true, true, false, true, false, true, true, false, false => 15264 / 625
  | true, true, true, false, true, false, true, true, false, true => 152 / 125
  | true, true, true, false, true, false, true, true, true, false => 0
  | true, true, true, false, true, false, true, true, true, true => 0
  | true, true, true, false, true, true, false, false, false, false => 2964 / 625
  | true, true, true, false, true, true, false, false, false, true => 15264 / 625
  | true, true, true, false, true, true, false, false, true, false => 15264 / 625
  | true, true, true, false, true, true, false, false, true, true => 152 / 125
  | true, true, true, false, true, true, false, true, false, false => 0
  | true, true, true, false, true, true, false, true, false, true => 0
  | true, true, true, false, true, true, false, true, true, false => 0
  | true, true, true, false, true, true, false, true, true, true => 0
  | true, true, true, false, true, true, true, false, false, false => -432 / 625
  | true, true, true, false, true, true, true, false, false, true => 0
  | true, true, true, false, true, true, true, false, true, false => 0
  | true, true, true, false, true, true, true, false, true, true => 0
  | true, true, true, false, true, true, true, true, false, false => 0
  | true, true, true, false, true, true, true, true, false, true => 0
  | true, true, true, false, true, true, true, true, true, false => 0
  | true, true, true, false, true, true, true, true, true, true => 0
  | true, true, true, true, false, false, false, false, false, false => 576 / 125
  | true, true, true, true, false, false, false, false, false, true => 2064 / 625
  | true, true, true, true, false, false, false, false, true, false => 2064 / 625
  | true, true, true, true, false, false, false, false, true, true => -432 / 625
  | true, true, true, true, false, false, false, true, false, false => 2064 / 625
  | true, true, true, true, false, false, false, true, false, true => -432 / 625
  | true, true, true, true, false, false, false, true, true, false => -432 / 625
  | true, true, true, true, false, false, false, true, true, true => 0
  | true, true, true, true, false, false, true, false, false, false => 2064 / 625
  | true, true, true, true, false, false, true, false, false, true => -432 / 625
  | true, true, true, true, false, false, true, false, true, false => -432 / 625
  | true, true, true, true, false, false, true, false, true, true => 648 / 625
  | true, true, true, true, false, false, true, true, false, false => 0
  | true, true, true, true, false, false, true, true, false, true => 0
  | true, true, true, true, false, false, true, true, true, false => 0
  | true, true, true, true, false, false, true, true, true, true => 0
  | true, true, true, true, false, true, false, false, false, false => 2064 / 625
  | true, true, true, true, false, true, false, false, false, true => -432 / 625
  | true, true, true, true, false, true, false, false, true, false => 0
  | true, true, true, true, false, true, false, false, true, true => 0
  | true, true, true, true, false, true, false, true, false, false => -432 / 625
  | true, true, true, true, false, true, false, true, false, true => 648 / 625
  | true, true, true, true, false, true, false, true, true, false => 0
  | true, true, true, true, false, true, false, true, true, true => 0
  | true, true, true, true, false, true, true, false, false, false => -432 / 625
  | true, true, true, true, false, true, true, false, false, true => 0
  | true, true, true, true, false, true, true, false, true, false => 0
  | true, true, true, true, false, true, true, false, true, true => 0
  | true, true, true, true, false, true, true, true, false, false => 0
  | true, true, true, true, false, true, true, true, false, true => 0
  | true, true, true, true, false, true, true, true, true, false => 0
  | true, true, true, true, false, true, true, true, true, true => 0
  | true, true, true, true, true, false, false, false, false, false => 2064 / 625
  | true, true, true, true, true, false, false, false, false, true => 0
  | true, true, true, true, true, false, false, false, true, false => -432 / 625
  | true, true, true, true, true, false, false, false, true, true => 0
  | true, true, true, true, true, false, false, true, false, false => -432 / 625
  | true, true, true, true, true, false, false, true, false, true => 0
  | true, true, true, true, true, false, false, true, true, false => 648 / 625
  | true, true, true, true, true, false, false, true, true, true => 0
  | true, true, true, true, true, false, true, false, false, false => -432 / 625
  | true, true, true, true, true, false, true, false, false, true => 0
  | true, true, true, true, true, false, true, false, true, false => 0
  | true, true, true, true, true, false, true, false, true, true => 0
  | true, true, true, true, true, false, true, true, false, false => 0
  | true, true, true, true, true, false, true, true, false, true => 0
  | true, true, true, true, true, false, true, true, true, false => 0
  | true, true, true, true, true, false, true, true, true, true => 0
  | true, true, true, true, true, true, false, false, false, false => -432 / 625
  | true, true, true, true, true, true, false, false, false, true => 0
  | true, true, true, true, true, true, false, false, true, false => 0
  | true, true, true, true, true, true, false, false, true, true => 0
  | true, true, true, true, true, true, false, true, false, false => 0
  | true, true, true, true, true, true, false, true, false, true => 0
  | true, true, true, true, true, true, false, true, true, false => 0
  | true, true, true, true, true, true, false, true, true, true => 0
  | true, true, true, true, true, true, true, false, false, false => 648 / 625
  | true, true, true, true, true, true, true, false, false, true => 0
  | true, true, true, true, true, true, true, false, true, false => 0
  | true, true, true, true, true, true, true, false, true, true => 0
  | true, true, true, true, true, true, true, true, false, false => 0
  | true, true, true, true, true, true, true, true, false, true => 0
  | true, true, true, true, true, true, true, true, true, false => 0
  | true, true, true, true, true, true, true, true, true, true => 0


/-!
## § 3. Computational Bound Verification
-/

/-- Total flag contribution for a graph on `Fin 5`. -/
def totalFlagContrib (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  totalFlagContribBits (adj 0 1) (adj 0 2) (adj 0 3) (adj 0 4) (adj 1 2)
    (adj 1 3) (adj 1 4) (adj 2 3) (adj 2 4) (adj 3 4)

/-- Encode a graph on `Fin 5` as a function from edge indices to `Bool`. -/
def mkAdj5 (e : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 => e 0 | 0, 2 | 2, 0 => e 1 | 0, 3 | 3, 0 => e 2 | 0, 4 | 4, 0 => e 3
  | 1, 2 | 2, 1 => e 4 | 1, 3 | 3, 1 => e 5 | 1, 4 | 4, 1 => e 6
  | 2, 3 | 3, 2 => e 7 | 2, 4 | 4, 2 => e 8 | 3, 4 | 4, 3 => e 9
  | _, _ => false

def noTriangleBits (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) : Prop :=
  ¬(b01 = true ∧ b12 = true ∧ b02 = true) ∧
  ¬(b01 = true ∧ b13 = true ∧ b03 = true) ∧
  ¬(b01 = true ∧ b14 = true ∧ b04 = true) ∧
  ¬(b02 = true ∧ b23 = true ∧ b03 = true) ∧
  ¬(b02 = true ∧ b24 = true ∧ b04 = true) ∧
  ¬(b03 = true ∧ b34 = true ∧ b04 = true) ∧
  ¬(b12 = true ∧ b23 = true ∧ b13 = true) ∧
  ¬(b12 = true ∧ b24 = true ∧ b14 = true) ∧
  ¬(b13 = true ∧ b34 = true ∧ b14 = true) ∧
  ¬(b23 = true ∧ b34 = true ∧ b24 = true)

attribute [-instance] Classical.propDecidable

private instance noTriangleBits_decidable
    (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) :
    Decidable (noTriangleBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34) := by
  unfold noTriangleBits
  infer_instance

private lemma flag_bound_all_graphs_bits :
    ∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
      noTriangleBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 →
      totalFlagContribBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 ≤ 576 / 125 := by
  intro b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 h
  cases b01 <;> cases b02 <;> cases b03 <;> cases b04 <;> cases b12 <;>
    cases b13 <;> cases b14 <;> cases b23 <;> cases b24 <;> cases b34 <;>
    simp [noTriangleBits, totalFlagContribBits] at h ⊢ <;> norm_num at h ⊢

/-- For every triangle-free graph on `Fin 5`,
`totalFlagContrib ≤ 576/125 = 120 · (24/625)`.
Checked over all `2^10 = 1024` possible edge configurations by kernel reduction. -/
theorem flag_bound_all_graphs : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) ≤ 576 / 125 := by
  intro e h
  exact flag_bound_all_graphs_bits
    (mkAdj5 e 0 1) (mkAdj5 e 0 2) (mkAdj5 e 0 3) (mkAdj5 e 0 4)
    (mkAdj5 e 1 2) (mkAdj5 e 1 3) (mkAdj5 e 1 4) (mkAdj5 e 2 3)
    (mkAdj5 e 2 4) (mkAdj5 e 3 4) (by
      exact ⟨h 0 1 2, h 0 1 3, h 0 1 4, h 0 2 3, h 0 2 4,
        h 0 3 4, h 1 2 3, h 1 2 4, h 1 3 4, h 2 3 4⟩)

attribute [local instance] Classical.propDecidable

/-- Whether a graph on `Fin 5` is a 5-cycle. -/
def isC5_adj (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  decide (
      (adj 0 1 = true ∧ adj 0 2 = true ∧ adj 0 3 = false ∧
        adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = true ∧
        adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧
        adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = true ∧ adj 0 3 = false ∧
        adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = false ∧
        adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧
        adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = true ∧
        adj 0 4 = false ∧ adj 1 2 = true ∧ adj 1 3 = false ∧
        adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧
        adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = true ∧
        adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = false ∧
        adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = true ∧
        adj 3 4 = false) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = false ∧
        adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = false ∧
        adj 1 4 = false ∧ adj 2 3 = true ∧ adj 2 4 = false ∧
        adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = false ∧
        adj 0 4 = true ∧ adj 1 2 = false ∧ adj 1 3 = true ∧
        adj 1 4 = false ∧ adj 2 3 = true ∧ adj 2 4 = true ∧
        adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = true ∧
        adj 0 4 = false ∧ adj 1 2 = true ∧ adj 1 3 = false ∧
        adj 1 4 = true ∧ adj 2 3 = false ∧ adj 2 4 = false ∧
        adj 3 4 = true) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = true ∧
        adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = true ∧
        adj 1 4 = true ∧ adj 2 3 = false ∧ adj 2 4 = true ∧
        adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = false ∧
        adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = true ∧
        adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = false ∧
        adj 3 4 = true) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = false ∧
        adj 0 4 = true ∧ adj 1 2 = false ∧ adj 1 3 = true ∧
        adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧
        adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = false ∧ adj 0 3 = true ∧
        adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = true ∧
        adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧
        adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = false ∧ adj 0 3 = true ∧
        adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = false ∧
        adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧
        adj 3 4 = false))

private def isC5_adj_bool (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  (adj 0 1 && (adj 0 2 && (!adj 0 3 && (!adj 0 4 &&
    (!adj 1 2 && (adj 1 3 && (!adj 1 4 && (!adj 2 3 &&
    (adj 2 4 && adj 3 4))))))))) ||
    ((adj 0 1 && (adj 0 2 && (!adj 0 3 && (!adj 0 4 &&
      (!adj 1 2 && (!adj 1 3 && (adj 1 4 && (adj 2 3 &&
      (!adj 2 4 && adj 3 4))))))))) ||
      ((adj 0 1 && (!adj 0 2 && (adj 0 3 && (!adj 0 4 &&
        (adj 1 2 && (!adj 1 3 && (!adj 1 4 && (!adj 2 3 &&
        (adj 2 4 && adj 3 4))))))))) ||
        ((adj 0 1 && (!adj 0 2 && (adj 0 3 && (!adj 0 4 &&
          (!adj 1 2 && (!adj 1 3 && (adj 1 4 && (adj 2 3 &&
          (adj 2 4 && !adj 3 4))))))))) ||
          ((adj 0 1 && (!adj 0 2 && (!adj 0 3 && (adj 0 4 &&
            (adj 1 2 && (!adj 1 3 && (!adj 1 4 && (adj 2 3 &&
            (!adj 2 4 && adj 3 4))))))))) ||
            ((adj 0 1 && (!adj 0 2 && (!adj 0 3 && (adj 0 4 &&
              (!adj 1 2 && (adj 1 3 && (!adj 1 4 && (adj 2 3 &&
              (adj 2 4 && !adj 3 4))))))))) ||
              ((!adj 0 1 && (adj 0 2 && (adj 0 3 && (!adj 0 4 &&
                (adj 1 2 && (!adj 1 3 && (adj 1 4 && (!adj 2 3 &&
                (!adj 2 4 && adj 3 4))))))))) ||
                ((!adj 0 1 && (adj 0 2 && (adj 0 3 && (!adj 0 4 &&
                  (!adj 1 2 && (adj 1 3 && (adj 1 4 && (!adj 2 3 &&
                  (adj 2 4 && !adj 3 4))))))))) ||
                  ((!adj 0 1 && (adj 0 2 && (!adj 0 3 && (adj 0 4 &&
                    (adj 1 2 && (adj 1 3 && (!adj 1 4 && (!adj 2 3 &&
                    (!adj 2 4 && adj 3 4))))))))) ||
                    ((!adj 0 1 && (adj 0 2 && (!adj 0 3 && (adj 0 4 &&
                      (!adj 1 2 && (adj 1 3 && (adj 1 4 && (adj 2 3 &&
                      (!adj 2 4 && !adj 3 4))))))))) ||
                      ((!adj 0 1 && (!adj 0 2 && (adj 0 3 && (adj 0 4 &&
                        (adj 1 2 && (adj 1 3 && (!adj 1 4 && (!adj 2 3 &&
                        (adj 2 4 && !adj 3 4))))))))) ||
                        (!adj 0 1 && (!adj 0 2 && (adj 0 3 && (adj 0 4 &&
                          (adj 1 2 && (!adj 1 3 && (adj 1 4 &&
                          (adj 2 3 && (!adj 2 4 && !adj 3 4)))))))))))))))))))

private lemma isC5_adj_true_iff_bool (adj : Fin 5 → Fin 5 → Bool) :
    isC5_adj adj = true ↔ isC5_adj_bool adj = true := by
  simp [isC5_adj, isC5_adj_bool]

set_option maxRecDepth 1000000 in
-- The generated C5 adjacency permutation proof needs a deeper recursion budget.
private lemma isC5_adj_bool_perm :
    ∀ τ : Equiv.Perm (Fin 5),
      isC5_adj_bool (fun i j => decide (τ j = τ i + 1 ∨ τ i = τ j + 1)) = true := by
  decide

private lemma c5_no_chords {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {f : Fin 5 → V} (hf_inj : Function.Injective f)
    (hcycle : ∀ i : Fin 5, G.Adj (f i) (f (i + 1)))
    (i j : Fin 5) (hij : j ≠ i + 1) (hji : i ≠ j + 1) (hne : i ≠ j) :
    ¬ G.Adj (f i) (f j) := by
  intro hadj
  have h := hcycle
  have h01 : G.Adj (f 0) (f 1) := h 0
  have h12 : G.Adj (f 1) (f 2) := h 1
  have h23 : G.Adj (f 2) (f 3) := h 2
  have h34 : G.Adj (f 3) (f 4) := h 3
  have h40 : G.Adj (f 4) (f 0) := by
    have := h 4
    simp at this
    exact this
  have tri : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      G.Adj (f a) (f b) → G.Adj (f a) (f c) → G.Adj (f b) (f c) → False := by
    intro a b c hab hac hbc e1 e2 e3
    apply hG {f a, f b, f c}
    constructor
    · intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
    · simp [hf_inj.ne hab, hf_inj.ne hac, hf_inj.ne hbc]
  fin_cases i <;> fin_cases j <;> simp_all (config := { decide := true })
  · exact tri 0 2 1 (by decide) (by decide) (by decide) hadj h01 h12.symm
  · exact tri 0 3 4 (by decide) (by decide) (by decide) hadj h40.symm h34
  · exact tri 1 3 2 (by decide) (by decide) (by decide) hadj h12 h23.symm
  · exact tri 1 4 0 (by decide) (by decide) (by decide) hadj h01.symm h40
  · exact tri 2 0 1 (by decide) (by decide) (by decide) hadj h12.symm h01
  · exact tri 2 4 3 (by decide) (by decide) (by decide) hadj h23 h34.symm
  · exact tri 3 0 4 (by decide) (by decide) (by decide) hadj h34 h40.symm
  · exact tri 3 1 2 (by decide) (by decide) (by decide) hadj h23.symm h12
  · exact tri 4 1 0 (by decide) (by decide) (by decide) hadj h40 h01.symm
  · exact tri 4 2 3 (by decide) (by decide) (by decide) hadj h34.symm h23

private def edgeBits
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool := fun i =>
  match i.val with
  | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4
  | 5 => b5 | 6 => b6 | 7 => b7 | 8 => b8 | 9 => b9
  | _ => false

private lemma edgeBits_ext (e : Fin 10 → Bool) {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool}
    (h0 : e 0 = b0) (h1 : e 1 = b1) (h2 : e 2 = b2) (h3 : e 3 = b3)
    (h4 : e 4 = b4) (h5 : e 5 = b5) (h6 : e 6 = b6) (h7 : e 7 = b7)
    (h8 : e 8 = b8) (h9 : e 9 = b9) :
    e = edgeBits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 := by
  funext i
  fin_cases i <;> simp [edgeBits, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

private lemma c5_contrib_0 :
    totalFlagContrib (mkAdj5 (edgeBits true true false false false true false false true true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_1 :
    totalFlagContrib (mkAdj5 (edgeBits true true false false false false true true false true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_2 :
    totalFlagContrib (mkAdj5 (edgeBits true false true false true false false false true true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_3 :
    totalFlagContrib (mkAdj5 (edgeBits true false true false false false true true true false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_4 :
    totalFlagContrib (mkAdj5 (edgeBits true false false true true false false true false true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_5 :
    totalFlagContrib (mkAdj5 (edgeBits true false false true false true false true true false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_6 :
    totalFlagContrib (mkAdj5 (edgeBits false true true false true false true false false true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_7 :
    totalFlagContrib (mkAdj5 (edgeBits false true true false false true true false true false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_8 :
    totalFlagContrib (mkAdj5 (edgeBits false true false true true true false false false true)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_9 :
    totalFlagContrib (mkAdj5 (edgeBits false true false true false true true true false false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_10 :
    totalFlagContrib (mkAdj5 (edgeBits false false true true true true false false true false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

private lemma c5_contrib_11 :
    totalFlagContrib (mkAdj5 (edgeBits false false true true true false true true false false)) =
      -14424 / 125 := by
  change (-14424 / 125 : ℚ) = -14424 / 125
  rfl

/-- Strengthened computational bound including the C₅ indicator. -/
theorem flag_bound_with_c5 : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) +
      120 * (if isC5_adj (mkAdj5 e) then 1 else 0) ≤ 576 / 125 := by
  intro e htri
  by_cases hc : isC5_adj (mkAdj5 e) = true
  · have hc' := of_decide_eq_true (by simpa [isC5_adj] using hc)
    rw [hc]
    rcases hc' with
      hpat | hpat | hpat | hpat | hpat | hpat |
      hpat | hpat | hpat | hpat | hpat | hpat
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_0]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_1]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_2]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_3]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_4]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_5]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_6]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_7]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_8]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_9]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_10]
      norm_num
    · rcases hpat with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      simp [mkAdj5] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      have he := edgeBits_ext e h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [he, c5_contrib_11]
      norm_num
  · cases hfalse : isC5_adj (mkAdj5 e)
    · simp
      exact flag_bound_all_graphs e htri
    · exact False.elim (hc hfalse)

/-!
## § 4. Graph Adjacency from Injective Functions
-/

/-- The adjacency function of `G` pulled back along `f : Fin 5 → V`. -/
def graphAdj5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    Fin 5 → Fin 5 → Bool :=
  fun i j => decide (G.Adj (f i) (f j))

lemma graphAdj5_symm {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i j, graphAdj5 G f i j = graphAdj5 G f j i := by
  intro i j
  unfold graphAdj5
  simp [G.adj_comm]

lemma graphAdj5_irrefl {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i, graphAdj5 G f i i = false := by
  intro i
  unfold graphAdj5
  exact decide_eq_false_iff_not.mpr G.irrefl

set_option maxHeartbeats 800000 in
lemma graphAdj5_triangleFree {V : Type*}
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (f : Fin 5 → V) (_hf : f.Injective) :
    ∀ a b c : Fin 5,
      ¬(graphAdj5 G f a b = true ∧ graphAdj5 G f b c = true ∧
        graphAdj5 G f a c = true) := by
  intro a b c h
  rcases h with ⟨hab, hbc, hac⟩
  have hab' : G.Adj (f a) (f b) := of_decide_eq_true hab
  have hbc' : G.Adj (f b) (f c) := of_decide_eq_true hbc
  have hac' : G.Adj (f a) (f c) := of_decide_eq_true hac
  classical
  let s : Finset V := {f a, f b, f c}
  have hfab_ne_fb : f a ≠ f b := by
    intro hEq
    rw [hEq] at hab'
    exact G.irrefl hab'
  have hfb_ne_fc : f b ≠ f c := by
    intro hEq
    rw [hEq] at hbc'
    exact G.irrefl hbc'
  have hfa_ne_fc : f a ≠ f c := by
    intro hEq
    rw [hEq] at hac'
    exact G.irrefl hac'
  apply hG s
  constructor
  · rw [SimpleGraph.isClique_iff]
    rw [show (s : Set V) = ({f a, f b, f c} : Set V) by simp [s]]
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · contradiction
    · exact hab'
    · exact hac'
    · exact G.adj_symm hab'
    · contradiction
    · exact hbc'
    · exact G.adj_symm hac'
    · exact G.adj_symm hbc'
    · contradiction
  · simp [s, hfab_ne_fb, hfa_ne_fc, hfb_ne_fc]

/-!
## § 5. Connecting `graphAdj5` to `mkAdj5`
-/

/-- Extract edge bits from an adjacency function. -/
def toEdges5 (adj : Fin 5 → Fin 5 → Bool) : Fin 10 → Bool :=
  ![adj 0 1, adj 0 2, adj 0 3, adj 0 4, adj 1 2,
    adj 1 3, adj 1 4, adj 2 3, adj 2 4, adj 3 4]

lemma mkAdj5_toEdges5 (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false) :
    mkAdj5 (toEdges5 adj) = adj := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [*, mkAdj5, toEdges5]
  · exact hsym _ _
  · exact hsym _ _

lemma flag_bound_for_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj ≤ 576 / 125 := by
  rw [show adj = mkAdj5 (toEdges5 adj) from (mkAdj5_toEdges5 adj hsym hirr).symm]
  exact flag_bound_all_graphs (toEdges5 adj) (by rwa [mkAdj5_toEdges5 adj hsym hirr])

lemma flag_bound_with_c5_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj +
      120 * (if isC5_adj adj then 1 else 0) ≤ 576 / 125 := by
  rw [show adj = mkAdj5 (toEdges5 adj) from (mkAdj5_toEdges5 adj hsym hirr).symm]
  exact flag_bound_with_c5 (toEdges5 adj) (by rwa [mkAdj5_toEdges5 adj hsym hirr])

/-!
## § 6. Equivariance of `quintContrib`
-/

private lemma mkAdj5_toEdges5_of_ne (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i) {i j : Fin 5} (hij : i ≠ j) :
    mkAdj5 (toEdges5 adj) i j = adj i j := by
  fin_cases i <;> fin_cases j <;> simp [mkAdj5, toEdges5] at *
  all_goals first | contradiction | exact hsym _ _

private lemma totalFlagContrib_toEdges5_perm (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i) (τ : Equiv.Perm (Fin 5)) :
    totalFlagContrib (fun i j => adj (τ i) (τ j)) =
      totalFlagContrib (fun i j => mkAdj5 (toEdges5 adj) (τ i) (τ j)) := by
  have hne {i j : Fin 5} (hij : i ≠ j) : τ i ≠ τ j :=
    fun h => hij (τ.injective h)
  have h01 : mkAdj5 (toEdges5 adj) (τ 0) (τ 1) = adj (τ 0) (τ 1) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (0 : Fin 5) ≠ 1))
  have h02 : mkAdj5 (toEdges5 adj) (τ 0) (τ 2) = adj (τ 0) (τ 2) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (0 : Fin 5) ≠ 2))
  have h03 : mkAdj5 (toEdges5 adj) (τ 0) (τ 3) = adj (τ 0) (τ 3) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (0 : Fin 5) ≠ 3))
  have h04 : mkAdj5 (toEdges5 adj) (τ 0) (τ 4) = adj (τ 0) (τ 4) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (0 : Fin 5) ≠ 4))
  have h12 : mkAdj5 (toEdges5 adj) (τ 1) (τ 2) = adj (τ 1) (τ 2) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (1 : Fin 5) ≠ 2))
  have h13 : mkAdj5 (toEdges5 adj) (τ 1) (τ 3) = adj (τ 1) (τ 3) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (1 : Fin 5) ≠ 3))
  have h14 : mkAdj5 (toEdges5 adj) (τ 1) (τ 4) = adj (τ 1) (τ 4) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (1 : Fin 5) ≠ 4))
  have h23 : mkAdj5 (toEdges5 adj) (τ 2) (τ 3) = adj (τ 2) (τ 3) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (2 : Fin 5) ≠ 3))
  have h24 : mkAdj5 (toEdges5 adj) (τ 2) (τ 4) = adj (τ 2) (τ 4) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (2 : Fin 5) ≠ 4))
  have h34 : mkAdj5 (toEdges5 adj) (τ 3) (τ 4) = adj (τ 3) (τ 4) :=
    mkAdj5_toEdges5_of_ne adj hsym (hne (by decide : (3 : Fin 5) ≠ 4))
  simp [totalFlagContrib, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]

private lemma totalFlagContribBits_swap01
    (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) :
    totalFlagContribBits b01 b12 b13 b14 b02 b03 b04 b23 b24 b34 =
      totalFlagContribBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 := by
  cases b01 <;> cases b02 <;> cases b03 <;> cases b04 <;> cases b12 <;>
    cases b13 <;> cases b14 <;> cases b23 <;> cases b24 <;> cases b34 <;> rfl

private lemma totalFlagContribBits_swap12
    (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) :
    totalFlagContribBits b02 b01 b03 b04 b12 b23 b24 b13 b14 b34 =
      totalFlagContribBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 := by
  cases b01 <;> cases b02 <;> cases b03 <;> cases b04 <;> cases b12 <;>
    cases b13 <;> cases b14 <;> cases b23 <;> cases b24 <;> cases b34 <;> rfl

private lemma totalFlagContribBits_swap23
    (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) :
    totalFlagContribBits b01 b03 b02 b04 b13 b12 b14 b23 b34 b24 =
      totalFlagContribBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 := by
  cases b01 <;> cases b02 <;> cases b03 <;> cases b04 <;> cases b12 <;>
    cases b13 <;> cases b14 <;> cases b23 <;> cases b24 <;> cases b34 <;> rfl

private lemma totalFlagContribBits_swap34
    (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool) :
    totalFlagContribBits b01 b02 b04 b03 b12 b14 b13 b24 b23 b34 =
      totalFlagContribBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 := by
  cases b01 <;> cases b02 <;> cases b03 <;> cases b04 <;> cases b12 <;>
    cases b13 <;> cases b14 <;> cases b23 <;> cases b24 <;> cases b34 <;> rfl

private lemma totalFlagContrib_mkAdj5_adjacent_swap_inv (e : Fin 10 → Bool) (k : Fin 4) :
    totalFlagContrib
        (fun i j => mkAdj5 e (Equiv.swap k.castSucc k.succ i) (Equiv.swap k.castSucc k.succ j)) =
      totalFlagContrib (mkAdj5 e) := by
  fin_cases k
  · simpa [totalFlagContrib, mkAdj5, Equiv.swap_apply_def] using
      totalFlagContribBits_swap01 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5, Equiv.swap_apply_def] using
      totalFlagContribBits_swap12 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5, Equiv.swap_apply_def] using
      totalFlagContribBits_swap23 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5, Equiv.swap_apply_def] using
      totalFlagContribBits_swap34 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)

private lemma totalFlagContrib_adjacent_swap_inv (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i) (k : Fin 4) :
    totalFlagContrib
        (fun i j => adj (Equiv.swap k.castSucc k.succ i) (Equiv.swap k.castSucc k.succ j)) =
      totalFlagContrib adj := by
  calc
    totalFlagContrib
        (fun i j => adj (Equiv.swap k.castSucc k.succ i) (Equiv.swap k.castSucc k.succ j))
        = totalFlagContrib
            (fun i j =>
              mkAdj5 (toEdges5 adj) (Equiv.swap k.castSucc k.succ i)
                (Equiv.swap k.castSucc k.succ j)) :=
          totalFlagContrib_toEdges5_perm adj hsym (Equiv.swap k.castSucc k.succ)
    _ = totalFlagContrib (mkAdj5 (toEdges5 adj)) :=
          totalFlagContrib_mkAdj5_adjacent_swap_inv (toEdges5 adj) k
    _ = totalFlagContrib adj := by
          simp [totalFlagContrib, mkAdj5, toEdges5]

lemma totalFlagContrib_perm_inv (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (τ : Equiv.Perm (Fin 5)) :
    totalFlagContrib (fun i j => adj (τ i) (τ j)) = totalFlagContrib adj := by
  let S : Submonoid (Equiv.Perm (Fin 5)) :=
  {
    carrier :=
      {τ | ∀ adj : Fin 5 → Fin 5 → Bool, (∀ i j, adj i j = adj j i) →
        totalFlagContrib (fun i j => adj (τ i) (τ j)) = totalFlagContrib adj}
    one_mem' := by
      intro adj _hsym
      simp
    mul_mem' := by
      intro σ τ hσ hτ adj hsym
      let adjσ : Fin 5 → Fin 5 → Bool := fun i j => adj (σ i) (σ j)
      have hsymσ : ∀ i j, adjσ i j = adjσ j i := by
        intro i j
        exact hsym _ _
      calc
        totalFlagContrib (fun i j => adj ((σ * τ) i) ((σ * τ) j))
            = totalFlagContrib (fun i j => adjσ (τ i) (τ j)) := by
              simp [adjσ, Equiv.Perm.mul_apply]
        _ = totalFlagContrib adjσ := hτ adjσ hsymσ
        _ = totalFlagContrib adj := hσ adj hsym
  }
  have hgen : Set.range (fun k : Fin 4 => Equiv.swap k.castSucc k.succ) ⊆ S := by
    rintro σ ⟨k, rfl⟩ adj hsym
    exact totalFlagContrib_adjacent_swap_inv adj hsym k
  have htop : (⊤ : Submonoid (Equiv.Perm (Fin 5))) ≤ S := by
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ 4]
    exact Submonoid.closure_le.mpr hgen
  exact (htop (by simp : τ ∈ (⊤ : Submonoid (Equiv.Perm (Fin 5))))) adj hsym

/-!
## § 7. PSD Non-negativity of Quadratic Form
-/

/-- PSD double sum lemma: if `M` is PSD then `∑_{d,e} M(flag d, flag e) ≥ 0`. -/
lemma sum_sum_psd_nonneg {k : ℕ} {M : Matrix (Fin k) (Fin k) ℚ}
    (hM : ∀ v : Fin k → ℚ, 0 ≤ dotProduct v (M.mulVec v))
    {α : Type*} (S : Finset α) (flag : α → Fin k) :
    (0 : ℚ) ≤ S.sum fun d => S.sum fun e => M (flag d) (flag e) := by
  convert hM _
  swap
  · exact fun i => (S.filter fun x => flag x = i).card
  · simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have : ∑ d ∈ S, ∑ e ∈ S, M (flag d) (flag e) =
        ∑ i, ∑ d ∈ S.filter (fun x => flag x = i),
          ∑ j, ∑ e ∈ S.filter (fun x => flag x = j), M i j := by
      simp only [Finset.sum_sigma']
      exact Finset.sum_bij (fun x _ => ⟨flag x.fst, x.fst, flag x.snd, x.snd⟩)
        (by aesop) (by aesop) (by aesop) (by aesop)
    simp_all [mul_comm, mul_left_comm, Finset.mul_sum]

set_option maxHeartbeats 800000 in
lemma sum_sum_psd_option {k : ℕ} {M : Matrix (Fin k) (Fin k) ℚ}
    (hM : ∀ v : Fin k → ℚ, 0 ≤ dotProduct v (M.mulVec v))
    {α : Type*} (S : Finset α) (flag : α → Option (Fin k)) (scale : ℚ)
    (hscale : 0 < scale) :
    (0 : ℚ) ≤ S.sum fun d => S.sum fun e =>
      match flag d, flag e with
      | some fi, some fj => M fi fj / scale
      | _, _ => 0 := by
  have h_nonneg : 0 ≤ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
      M i j * (∑ d ∈ S, if flag d = some i then 1 else 0) *
        (∑ e ∈ S, if flag e = some j then 1 else 0) := by
    convert hM (fun i => ∑ d ∈ S, if flag d = some i then 1 else 0) using 1
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
  have h_sum : ∑ d ∈ S, ∑ e ∈ S,
      (match flag d, flag e with
      | some fi, some fj => M fi fj / scale
      | _, _ => 0) =
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        M i j / scale *
          (∑ d ∈ S, if flag d = some i then 1 else 0) *
          (∑ e ∈ S, if flag e = some j then 1 else 0) := by
    have : ∑ d ∈ S, ∑ e ∈ S,
        (match flag d, flag e with
        | some fi, some fj => M fi fj / scale
        | _, _ => 0) =
        ∑ d ∈ S, ∑ e ∈ S, ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          (if flag d = some i then M i j / scale else 0) *
          (if flag e = some j then 1 else 0) := by
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
      cases flag d <;> cases flag e <;> simp
    convert this using 1
    simp only [Finset.mul_sum, sum_mul, mul_assoc]
    simp only [Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ =>
        ⟨x.snd.snd.snd, x.snd.snd.fst, x.fst, x.snd.fst⟩) ?_ ?_ ?_ ?_
      <;> simp
    · exact fun a ha₁ ha₂ => ⟨ha₂, ha₁⟩
    · bound
    · exact fun b hb₁ hb₂ => ⟨_, _, _, _, ⟨hb₂, hb₁⟩, rfl⟩
  exact h_sum.symm ▸ by
    simpa only [div_mul_eq_mul_div, Finset.sum_div] using div_nonneg h_nonneg hscale.le

lemma quintContrib_type0 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = false) (h02 : adj 0 2 = false) (h12 : adj 1 2 = false) :
    quintContrib adj (Equiv.refl _) =
      P_cert (σ₀FlagIdx (adj 3 0) (adj 3 1) (adj 3 2))
             (σ₀FlagIdx (adj 4 0) (adj 4 1) (adj 4 2)) / 625 := by
  simp [quintContrib, quintContribOf, h01, h02, h12]

lemma quintContrib_type1 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = true) (h02 : adj 0 2 = false) (h12 : adj 1 2 = false) :
    quintContrib adj (Equiv.refl _) =
      match σ₁FlagIdx (adj 3 0) (adj 3 1) (adj 3 2),
            σ₁FlagIdx (adj 4 0) (adj 4 1) (adj 4 2) with
      | some fi, some fj => Q_cert fi fj / 2500
      | _, _ => 0 := by
  simp [quintContrib, quintContribOf, h01, h02, h12]

lemma quintContrib_type2 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = true) (h12 : adj 1 2 = true) (h02 : adj 0 2 = false) :
    quintContrib adj (Equiv.refl _) =
      match σ₂FlagIdx (adj 3 0) (adj 3 1) (adj 3 2),
            σ₂FlagIdx (adj 4 0) (adj 4 1) (adj 4 2) with
      | some fi, some fj => R_cert fi fj / 625
      | _, _ => 0 := by
  simp [quintContrib, quintContribOf, h01, h12, h02]

set_option maxHeartbeats 800000 in
/-- The quadratic form `∑_{d,e} quintContrib(![a,b,c,d,e])` is non-negative. -/
lemma quadForm_nonneg {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a b c : V) :
    (0 : ℚ) ≤ (Finset.univ : Finset V).sum fun d =>
      (Finset.univ : Finset V).sum fun e =>
        quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) := by
  by_cases h_ab : G.Adj a b
  · by_cases h_ac : G.Adj a c
    · unfold quintContrib quintContribOf graphAdj5
      simp [*]
    · by_cases h_bc : G.Adj b c
      · convert sum_sum_psd_option R_cert_psd (Finset.univ : Finset V)
            (fun d => σ₂FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2)) 625 (by norm_num) using 1
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [quintContrib_type2]
        · unfold graphAdj5
          simp
          congr! 1
          ext
          cases ‹Option (Fin 5)› <;> cases ‹Option (Fin 5)› <;> rfl
        · unfold graphAdj5
          aesop
        · unfold graphAdj5
          aesop
        · unfold graphAdj5
          aesop
      · convert sum_sum_psd_option Q_cert_psd (Finset.univ : Finset V)
            (fun d => σ₁FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2)) 2500 (by norm_num) using 1
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [quintContrib_type1]
        · unfold graphAdj5
          simp
          congr! 1
          ext
          cases ‹Option (Fin 6)› <;> cases ‹Option (Fin 6)› <;> rfl
        · unfold graphAdj5
          aesop
        · unfold graphAdj5
          aesop
        · unfold graphAdj5
          aesop
  · by_cases h_ac : G.Adj a c <;> by_cases h_bc : G.Adj b c
    · unfold quintContrib quintContribOf graphAdj5
      simp [*]
    · unfold quintContrib quintContribOf graphAdj5
      simp [*]
    · unfold quintContrib quintContribOf graphAdj5
      simp [*]
    · have h_eq : ∀ d e : V,
          quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) =
            P_cert (σ₀FlagIdx (graphAdj5 G ![a, b, c, d, e] 3 0)
                    (graphAdj5 G ![a, b, c, d, e] 3 1)
                    (graphAdj5 G ![a, b, c, d, e] 3 2))
                   (σ₀FlagIdx (graphAdj5 G ![a, b, c, d, e] 4 0)
                    (graphAdj5 G ![a, b, c, d, e] 4 1)
                    (graphAdj5 G ![a, b, c, d, e] 4 2)) / 625 := by
        intro d e
        apply quintContrib_type0 <;> unfold graphAdj5 <;> aesop
      simp_rw [h_eq]
      convert mul_nonneg (inv_nonneg.mpr (show (625 : ℚ) ≥ 0 by norm_num))
          (sum_sum_psd_nonneg P_cert_psd (Finset.univ : Finset V)
            (fun d => σ₀FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2))) using 1
      · rfl
      · unfold graphAdj5
        simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => rfl

/-!
## § 8. Bounds on `quintContrib` Values
-/

private lemma P_cert_div_le_seven (i j : Fin 8) : P_cert i j / 625 ≤ 7 := by
  fin_cases i <;> fin_cases j <;> norm_num [P_cert]

private lemma Q_cert_div_le_seven (i j : Fin 6) : Q_cert i j / 2500 ≤ 7 := by
  fin_cases i <;> fin_cases j <;> norm_num [Q_cert]

private lemma R_cert_div_le_seven (i j : Fin 5) : R_cert i j / 625 ≤ 7 := by
  fin_cases i <;> fin_cases j <;> norm_num [R_cert]

private lemma Q_cert_match_le_seven (oi oj : Option (Fin 6)) :
    (match oi, oj with
    | some fi, some fj => Q_cert fi fj / 2500
    | _, _ => 0) ≤ 7 := by
  cases oi <;> cases oj <;> simp [Q_cert_div_le_seven]

private lemma R_cert_match_le_seven (oi oj : Option (Fin 5)) :
    (match oi, oj with
    | some fi, some fj => R_cert fi fj / 625
    | _, _ => 0) ≤ 7 := by
  cases oi <;> cases oj <;> simp [R_cert_div_le_seven]

/-- Every `quintContrib` value is ≤ 7 (verified computationally). -/
theorem quintContrib_le_seven :
    ∀ (e : Fin 10 → Bool), quintContrib (mkAdj5 e) (Equiv.refl _) ≤ 7 := by
  intro e
  cases h01 : e 0 with
  | false =>
      cases h02 : e 1 with
      | false =>
          cases h12 : e 4 with
          | false =>
              simpa [quintContrib, quintContribOf, mkAdj5, h01, h02, h12] using
                (P_cert_div_le_seven
                  (σ₀FlagIdx (e 2) (e 5) (e 7))
                  (σ₀FlagIdx (e 3) (e 6) (e 8)))
          | true =>
              norm_num [quintContrib, quintContribOf, mkAdj5, h01, h02, h12]
      | true =>
          cases h12 : e 4 <;> norm_num [quintContrib, quintContribOf, mkAdj5, h01, h02, h12]
  | true =>
      cases h02 : e 1 with
      | false =>
          cases h12 : e 4 with
          | false =>
              simpa [quintContrib, quintContribOf, mkAdj5, h01, h02, h12] using
                (Q_cert_match_le_seven
                  (σ₁FlagIdx (e 2) (e 5) (e 7))
                  (σ₁FlagIdx (e 3) (e 6) (e 8)))
          | true =>
              simpa [quintContrib, quintContribOf, mkAdj5, h01, h02, h12] using
                (R_cert_match_le_seven
                  (σ₂FlagIdx (e 2) (e 5) (e 7))
                  (σ₂FlagIdx (e 3) (e 6) (e 8)))
      | true =>
          cases h12 : e 4 <;> norm_num [quintContrib, quintContribOf, mkAdj5, h01, h02, h12]

/-- `quintContrib` is bounded by 7 for any `graphAdj5`. -/
lemma quintContrib_le_for_graphAdj {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    quintContrib (graphAdj5 G f) (Equiv.refl _) ≤ 7 := by
  rw [show graphAdj5 G f = mkAdj5 (toEdges5 (graphAdj5 G f))
    from (mkAdj5_toEdges5 (graphAdj5 G f) (graphAdj5_symm G f) (graphAdj5_irrefl G f)).symm]
  exact quintContrib_le_seven _

/-!
## § 9. PSD Lower Bound on Injective Sum
-/

/-- The global sum over all functions `f : Fin 5 → V` is non-negative. -/
lemma allFuncSum_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (0 : ℚ) ≤ (Finset.univ : Finset (Fin 5 → V)).sum
      fun f => quintContrib (graphAdj5 G f) (Equiv.refl _) := by
  have h_decomp : ∑ f : Fin 5 → V,
      quintContrib (graphAdj5 G f) (Equiv.refl _) =
      ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, ∑ e : V,
        quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) := by
    simp only [← sum_product']
    refine Finset.sum_bij (fun f _ => (f 0, f 1, f 2, f 3, f 4)) ?_ ?_ ?_ ?_
    all_goals simp
    · exact fun a₁ a₂ h₀ h₁ h₂ h₃ h₄ =>
        funext fun i => by fin_cases i <;> assumption
    · exact fun a b c d e =>
        ⟨fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c
          else if i = 3 then d else e, rfl, rfl, rfl, rfl, rfl⟩
    · intro a
      congr
      ext i
      fin_cases i <;> rfl
  exact h_decomp.symm ▸
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun c _ => quadForm_nonneg G a b c


set_option maxHeartbeats 800000 in
/-- Number of non-injective functions `Fin 5 → V` is at most `10 * n^4`. -/
lemma non_injective_count_le {V : Type*} [Fintype V] :
    ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).card ≤
      10 * Fintype.card V ^ 4 := by
  suffices ∀ n : ℕ,
      ((Finset.univ : Finset (Fin 5 → Fin n)).filter fun f => ¬f.Injective).card ≤
        10 * n ^ 4 by
    obtain ⟨e⟩ : Nonempty (V ≃ Fin (Fintype.card V)) := ⟨Fintype.equivFin V⟩
    convert this (Fintype.card V) using 1
    refine Finset.card_bij (fun f _ i => e (f i)) ?_ ?_ ?_ <;>
      simp +decide [Function.Injective]
    · exact fun a₁ x y hxy hne a₂ u v huv hne' h =>
        funext fun i => e.injective <| congr_fun h i
    · exact fun b x y hxy hne =>
        ⟨fun i => e.symm (b i), ⟨x, y, by simpa using hxy, hne⟩, by simp +decide⟩
  intro n
  by_cases hn : n ≤ 4
  · calc
      ((Finset.univ : Finset (Fin 5 → Fin n)).filter fun f => ¬f.Injective).card
          ≤ (Finset.univ : Finset (Fin 5 → Fin n)).card := Finset.card_filter_le _ _
      _ = n ^ 5 := by simp
      _ ≤ 10 * n ^ 4 := by
        rw [pow_succ, mul_comm 10 (n ^ 4)]
        exact Nat.mul_le_mul_left (n ^ 4) (by omega : n ≤ 10)
  · have h_count :
        (Finset.univ.filter fun f : Fin 5 → Fin n => Injective f).card =
          Nat.descFactorial n 5 := by
      have h_eq : (Finset.univ.filter fun f : Fin 5 → Fin n => Injective f) =
          Finset.image (fun f : Fin 5 ↪ Fin n => f.toFun)
            (Finset.univ : Finset (Fin 5 ↪ Fin n)) := by
        ext f
        simp [Function.Injective]
        exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, by
          rintro ⟨a, rfl⟩
          exact a.injective⟩
      rw [h_eq, Finset.card_image_of_injective _
          (fun f g h => by simpa [Function.Injective] using h)]
      simp +decide [Finset.card_univ]
    rw [Finset.filter_not, Finset.card_sdiff]
    simp_all [Finset.card_univ]
    zify
    have h_pow2 := pow_pos (by linarith : 0 < n) 2
    have h_pow3 := pow_pos (by linarith : 0 < n) 3
    rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_sub, Nat.cast_sub] <;>
      (try push_cast) <;> nlinarith

/-- PSD lower bound: `∑_{f injective} quintContrib ≥ -70 * n^4`. -/
lemma psd_lower_bound_injective {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (-(70 : ℚ) * (Fintype.card V : ℚ) ^ 4) ≤
      ((Finset.univ : Finset (Fin 5 → V)).filter fun f => f.Injective).sum
        fun f => quintContrib (graphAdj5 G f) (Equiv.refl _) := by
  have h_split := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 5 → V)) (fun f => f.Injective)
    (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _))
  have h_all := allFuncSum_nonneg G
  have h_bound :
      ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
        (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _)) ≤
        70 * (Fintype.card V : ℚ) ^ 4 := by
    calc ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
            (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _))
        ≤ ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
            fun _ => (7 : ℚ) := by
          apply Finset.sum_le_sum
          intro f _
          exact_mod_cast quintContrib_le_for_graphAdj G f
      _ = 7 * ((Finset.univ : Finset (Fin 5 → V)).filter fun f =>
            ¬f.Injective).card := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ 7 * (10 * Fintype.card V ^ 4) := by
          exact_mod_cast Nat.mul_le_mul_left 7 (non_injective_count_le (V := V))
      _ = 70 * (Fintype.card V : ℚ) ^ 4 := by ring
  linarith

/-!
## § 10. Counting Identity
-/

set_option linter.style.nativeDecide false in
private lemma totalFlagContrib_mkAdj5_edgeBits_eq_permSum :
    ∀ b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool,
      totalFlagContrib (mkAdj5 (edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34)) =
        totalFlagContribPermSum (mkAdj5 (edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24 b34)) := by
  native_decide +revert

private lemma totalFlagContrib_mkAdj5_eq_permSum (e : Fin 10 → Bool) :
    totalFlagContrib (mkAdj5 e) = totalFlagContribPermSum (mkAdj5 e) := by
  rw [edgeBits_ext e rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
  exact totalFlagContrib_mkAdj5_edgeBits_eq_permSum
    (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)

private lemma totalFlagContrib_eq_permSum (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false) :
    totalFlagContrib adj = totalFlagContribPermSum adj := by
  rw [← mkAdj5_toEdges5 adj hsym hirr]
  exact totalFlagContrib_mkAdj5_eq_permSum (toEdges5 adj)

private lemma totalFlagContrib_eq_sum_univ (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false) :
    totalFlagContrib adj =
      (Finset.univ : Finset (Equiv.Perm (Fin 5))).sum (quintContrib adj) := by
  rw [totalFlagContrib_eq_permSum adj hsym hirr]
  exact totalFlagContribPermSum_eq_sum_univ adj

set_option maxHeartbeats 1600000 in
/-- The sum of `quintContrib` over injective functions equals the sum of
`totalFlagContrib` over 5-element subsets. -/
lemma counting_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (enum : ∀ (S : Finset V), S.card = 5 → (Fin 5 → V))
    (henum : ∀ S hS, Function.Injective (enum S hS) ∧
      Finset.image (enum S hS) Finset.univ = S) :
    ((Finset.univ : Finset (Fin 5 → V)).filter fun f => f.Injective).sum
      (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _)) =
    ((Finset.univ : Finset (Finset V)).filter fun S => S.card = 5).sum
      fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (enum S h))
        else 0 := by
  have h_partition :
      ∑ f ∈ Finset.filter (fun f : Fin 5 → V => f.Injective) Finset.univ,
        quintContrib (graphAdj5 G f) (Equiv.refl _) =
      ∑ S ∈ Finset.powersetCard 5 (Finset.univ : Finset V),
        ∑ f ∈ Finset.filter
          (fun f : Fin 5 → V => f.Injective ∧ Finset.image f Finset.univ = S)
          Finset.univ,
          quintContrib (graphAdj5 G f) (Equiv.refl _) := by
    rw [← Finset.sum_biUnion]
    · rcongr f
      simp
      exact fun hf => by rw [Finset.card_image_of_injective _ hf, Finset.card_fin]
    · exact fun S _ T _ hST =>
        Finset.disjoint_left.mpr fun f hfS hfT => hST <| by aesop
  rw [h_partition, Finset.powersetCard_eq_filter]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have hScard : S.card = 5 := by simpa using hS
  have h_bij :
      Finset.filter (fun f : Fin 5 → V =>
        f.Injective ∧ Finset.image f Finset.univ = S) Finset.univ =
      Finset.image (fun σ : Equiv.Perm (Fin 5) =>
        fun i => enum S hScard (σ i))
        (Finset.univ : Finset (Equiv.Perm (Fin 5))) := by
    ext f
    simp
    constructor
    · intro h
      have h_bij : ∀ i : Fin 5, ∃ j : Fin 5,
          enum S hScard j = f i := by
        intro i
        have : f i ∈ S :=
          h.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have := (henum S hScard).2
        rw [Finset.ext_iff] at this
        grind
      choose σ hσ using h_bij
      have hσ_inj : Function.Injective σ := fun i j hij =>
        h.1 <| by
          have := hσ i
          have := hσ j
          aesop
      exact ⟨Equiv.ofBijective σ ⟨hσ_inj,
        Finite.injective_iff_surjective.mp hσ_inj⟩, funext hσ⟩
    · rintro ⟨σ, rfl⟩
      specialize henum S hScard
      simp [Function.Injective, Finset.ext_iff] at henum ⊢
      exact ⟨fun a₁ a₂ h => σ.injective (henum.1 h),
        fun a => ⟨fun ⟨i, hi⟩ => henum.2 a |>.1 ⟨_, hi⟩,
          fun ha => by
            obtain ⟨i, hi⟩ := henum.2 a |>.2 ha
            exact ⟨σ.symm i, by simpa using hi⟩⟩⟩
  simp_all +decide [Function.Injective]
  rw [Finset.sum_image
    (fun σ _ τ _ h => Equiv.Perm.ext fun i =>
      (henum S hScard).1 (by simpa using congr_fun h i))]
  rw [totalFlagContrib_eq_sum_univ (graphAdj5 G (enum S hScard))
    (graphAdj5_symm G (enum S hScard)) (graphAdj5_irrefl G (enum S hScard))]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rfl

/-!
## § 11. C₅ Copy Detection

### Counting conventions

There are two natural ways to count 5-cycles in a graph:

1. **`numC5`** (correct in general): counts labeled 5-cycles modulo the dihedral
   symmetry group D₅ (rotations and reflections), i.e. the number of
   *subgraphs* isomorphic to C₅. Formally, `numC5 G` is the number of
   labeled 5-cycles `(Fin 5 → V)` divided by 10 (= |D₅|). For example,
   `numC5 K₅ = 12` and `numC5 C₅ = 1`.

2. **`numC5Copies`** (correct only for triangle-free graphs): counts *vertex sets*
   `S : Finset V` that support at least one 5-cycle. In a triangle-free graph
   each such vertex set supports a unique cycle (up to dihedral symmetry),
   so `numC5Copies = numC5`. In general graphs, a single 5-vertex set may
   support multiple distinct 5-cycles, so `numC5Copies` undercounts.
   For instance, `numC5Copies K₅ = 1` (there is only one 5-element subset),
   whereas `numC5 K₅ = 12`.

The main theorem (`erdos_pentagon_conjecture`) is stated using `numC5` (the
correct general definition); the proof goes through `numC5Copies` via the
equivalence `numC5_eq_numC5Copies_of_triangleFree`.
-/

/-- A function `f : Fin 5 → V` defines a **labeled 5-cycle** in `G` if it is injective
and maps consecutive vertices (cyclically) to adjacent vertices. -/
def _root_.SimpleGraph.IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + 1))

/-- The number of 5-cycles in `G`, counting each cycle once.

A **5-cycle** is a subgraph of `G` isomorphic to the cycle graph C₅. We
formalize this as the number of labeled 5-cycles (injective maps
`f : Fin 5 → V` with `G.Adj (f i) (f (i+1))` for all `i`) divided by 10,
the order of the dihedral group D₅ = ⟨rotation, reflection⟩ that acts
freely on such labelings.

This is the correct definition for arbitrary graphs. For example,
`numC5 C₅ = 1` and `numC5 K₅ = 12`.

See also `numC5Copies` for a simpler definition that agrees with `numC5`
when the graph is triangle-free (`numC5_eq_numC5Copies_of_triangleFree`). -/
noncomputable def _root_.SimpleGraph.numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => G.IsLabeledC5 f)).card / 10

/-- A `Finset V` is a **C₅ copy** in `G` if its elements can be cyclically ordered
so that consecutive elements are adjacent.

**Warning:** This counts *vertex sets*, not *cycles*. A single 5-vertex set
can support multiple distinct 5-cycles in a general graph, so this definition
undercounts. For example, `K₅` has `numC5Copies = 1` but `numC5 = 12`.

In a triangle-free graph, the cycle through any such vertex set is unique
(up to dihedral symmetry), so `numC5Copies = numC5`; see
`numC5_eq_numC5Copies_of_triangleFree`. -/
def _root_.SimpleGraph.IsC5Copy {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ f : Fin 5 → V, G.IsLabeledC5 f ∧ Finset.image f Finset.univ = s

/-- The number of 5-element vertex sets supporting a 5-cycle in `G`.

**Warning:** This is *not* the number of 5-cycles in general — it only counts
vertex sets, ignoring multiplicity when a vertex set supports several distinct
cycles. It equals the correct count `numC5` when `G` is triangle-free; see
`numC5_eq_numC5Copies_of_triangleFree`.

Used internally in the flag-algebra machinery where the triangle-free
hypothesis is always available. -/
noncomputable def _root_.SimpleGraph.numC5Copies {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter G.IsC5Copy).card

set_option maxHeartbeats 1600000 in
/-- If `S` is a C₅ copy in a triangle-free graph, then the induced adjacency
on any enumeration of `S` satisfies `isC5_adj`. -/
lemma isC5Copy_implies_isC5_adj {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (S : Finset V) (enumS : Fin 5 → V) (henumInj : Function.Injective enumS)
    (henumImg : Finset.image enumS Finset.univ = S)
    (hC5 : G.IsC5Copy S) :
    isC5_adj (graphAdj5 G enumS) = true := by
  obtain ⟨f, hf, hf_image⟩ := hC5
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 5), enumS = f ∘ τ := by
    have h_bij : ∀ (s : Finset V), s.card = 5 →
        ∀ g : Fin 5 → V, Function.Injective g →
        Finset.image g Finset.univ = s →
        ∀ h : Fin 5 → V, Function.Injective h →
        Finset.image h Finset.univ = s →
        ∃ τ : Equiv.Perm (Fin 5), g = h ∘ τ := by
      intro s _ g hg_inj hg_image h hh_inj hh_image
      have : ∀ x : Fin 5, ∃ y : Fin 5, h y = g x := by
        intro x
        have : g x ∈ s := hg_image ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact Finset.mem_image.mp (hh_image.symm ▸ this) |>.imp fun _ => And.right
      choose τ hτ using this
      have hτ_inj : Function.Injective τ := fun x y hxy =>
        hg_inj <| by
          have := hτ x
          have := hτ y
          aesop
      exact ⟨Equiv.ofBijective τ
        ⟨hτ_inj, Finite.injective_iff_surjective.mp hτ_inj⟩,
        funext fun x => hτ x ▸ rfl⟩
    have hcard : S.card = 5 := by
      rw [← henumImg]
      exact Finset.card_image_of_injective _ henumInj
    exact h_bij _ hcard _ henumInj henumImg _ hf.1 (by
      convert hf_image using 2)
  have hmodel :
      graphAdj5 G (f ∘ ⇑τ) = fun i j => decide (τ j = τ i + 1 ∨ τ i = τ j + 1) := by
    funext i j
    have hprop : G.Adj (f (τ i)) (f (τ j)) ↔ (τ j = τ i + 1 ∨ τ i = τ j + 1) := by
      constructor
      · intro hij
        by_cases hconsec : τ j = τ i + 1 ∨ τ i = τ j + 1
        · exact hconsec
        · have hne : τ i ≠ τ j := by
            intro hij'
            have : G.Adj (f (τ i)) (f (τ i)) := by simp [hij'] at hij
            exact (G.loopless).irrefl _ this
          have hji : τ j ≠ τ i + 1 := by
            intro hji
            exact hconsec (Or.inl hji)
          have hij' : τ i ≠ τ j + 1 := by
            intro hij'
            exact hconsec (Or.inr hij')
          exact False.elim <| (c5_no_chords hG hf.1 hf.2 (τ i) (τ j) hji hij' hne) hij
      · intro hconsec
        rcases hconsec with hconsec | hconsec
        · simpa [hconsec] using hf.2 (τ i)
        · have := hf.2 (τ j)
          simpa [SimpleGraph.adj_comm, hconsec] using this
    by_cases hadj : G.Adj (f (τ i)) (f (τ j))
    · have hconsec : τ j = τ i + 1 ∨ τ i = τ j + 1 := hprop.1 hadj
      simp [graphAdj5, hadj, hconsec]
    · have hconsec : ¬ (τ j = τ i + 1 ∨ τ i = τ j + 1) := by
        intro hconsec
        exact hadj (hprop.2 hconsec)
      simp [graphAdj5, hadj, hconsec]
  rw [hτ, hmodel]
  exact (isC5_adj_true_iff_bool _).2 (isC5_adj_bool_perm τ)

/-!
## § 12. Per-subset Bound and Assembly
-/

/-- Canonical enumeration of a 5-element set. -/
noncomputable def chooseEnum5 {V : Type*} (S : Finset V) (hS : S.card = 5) :
    Fin 5 → V :=
  fun i => ((Fintype.equivFin ↥S).symm (Fin.cast (by simp [Fintype.card_coe, hS]) i)).val

lemma chooseEnum5_injective {V : Type*} (S : Finset V) (hS : S.card = 5) :
    Function.Injective (chooseEnum5 S hS) := by
  intro i j h
  simp only [chooseEnum5] at h
  exact Fin.cast_injective _
    ((Fintype.equivFin ↥S).symm.injective (Subtype.val_injective h))

lemma chooseEnum5_image {V : Type*} [DecidableEq V] (S : Finset V)
    (hS : S.card = 5) :
    Finset.image (chooseEnum5 S hS) Finset.univ = S := by
  ext x
  simp only [chooseEnum5, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Fintype.equivFin ↥S).symm _).prop
  · intro hx
    exact ⟨Fin.cast (by simp [Fintype.card_coe, hS]) ((Fintype.equivFin ↥S) ⟨x, hx⟩),
           by simp [Equiv.symm_apply_apply]⟩

lemma chooseEnum5_spec {V : Type*} [DecidableEq V] (S : Finset V)
    (hS : S.card = 5) :
    Function.Injective (chooseEnum5 S hS) ∧
    Finset.image (chooseEnum5 S hS) Finset.univ = S :=
  ⟨chooseEnum5_injective S hS, chooseEnum5_image S hS⟩

lemma per_subset_c5_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (S : Finset V) (_hS : S.card = 5) (enumS : Fin 5 → V)
    (hinj : Function.Injective enumS) (himg : Finset.image enumS univ = S) :
    totalFlagContrib (graphAdj5 G enumS) +
      120 * (if G.IsC5Copy S then (1 : ℚ) else 0) ≤ 576 / 125 := by
  have hc5 := flag_bound_with_c5_adj (graphAdj5 G enumS)
    (graphAdj5_symm G enumS) (graphAdj5_irrefl G enumS)
    (graphAdj5_triangleFree G hG enumS hinj)
  by_cases hcopy : G.IsC5Copy S
  · simp [hcopy]
    have := isC5Copy_implies_isC5_adj G hG S enumS hinj himg hcopy
    simp [this] at hc5
    linarith
  · simp [hcopy]
    exact flag_bound_for_adj (graphAdj5 G enumS)
      (graphAdj5_symm G enumS) (graphAdj5_irrefl G enumS)
      (graphAdj5_triangleFree G hG enumS hinj)

lemma isC5Copy_card {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (h : G.IsC5Copy S) : S.card = 5 := by
  classical
  obtain ⟨f, ⟨hfinj, _⟩, himg⟩ := h
  conv_lhs => rw [show S = Finset.image f Finset.univ from
    himg.symm]
  exact Finset.card_image_of_injective _ hfinj

lemma c5_indicator_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ((univ : Finset (Finset V)).filter fun S => S.card = 5).sum
      (fun S => if G.IsC5Copy S then (1 : ℚ) else 0) = G.numC5Copies := by
  classical
  simp only [sum_boole, Nat.cast_inj]
  unfold SimpleGraph.numC5Copies
  congr 1
  ext S
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨isC5Copy_card G S h, h⟩⟩

set_option maxHeartbeats 800000 in
/-- **Key intermediate bound**:
`numC5Copies ≤ (24/625) * C(n,5) + 8 * n^4`. -/
theorem numC5Copies_le_turan_plus_error {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (G.numC5Copies : ℝ) ≤
      (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
      8 * (Fintype.card V : ℝ) ^ 4 := by
  classical
  set F := (univ : Finset (Finset V)).filter (fun S => S.card = 5) with hF_def
  have h_lb : -(70 : ℚ) * (Fintype.card V : ℚ) ^ 4 ≤
      F.sum fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (chooseEnum5 S h)) else 0 := by
    calc -(70 : ℚ) * _ ≤ _ := psd_lower_bound_injective G
      _ = _ := by convert counting_identity G chooseEnum5
                    fun S hS => chooseEnum5_spec S hS
  have h_step1 : F.sum (fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (chooseEnum5 S h)) else 0) ≤
      F.sum fun S => (576 / 125 : ℚ) - 120 * if G.IsC5Copy S then 1 else 0 := by
    apply Finset.sum_le_sum
    intro S hS
    have hScard : S.card = 5 := by
      simp [hF_def] at hS
      exact hS
    simp only [dif_pos hScard]
    linarith [per_subset_c5_bound G hG S hScard (chooseEnum5 S hScard)
      (chooseEnum5_injective S hScard) (chooseEnum5_image S hScard)]
  have hcard : F.card = (Fintype.card V).choose 5 := by
    rw [hF_def,
      show (Finset.univ : Finset (Finset V)).filter (fun S => S.card = 5) =
        (Finset.univ : Finset V).powersetCard 5 from by
          ext S
          simp [Finset.mem_powersetCard]]
    simp [Finset.card_powersetCard]
  have h_step2 :
      F.sum (fun S => (576 / 125 : ℚ) - 120 * if G.IsC5Copy S then 1 else 0) =
      (576 / 125 : ℚ) * (Fintype.card V).choose 5 - 120 * (G.numC5Copies : ℚ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, c5_indicator_sum G, hcard]
    ring
  have hq : (G.numC5Copies : ℚ) ≤
      (24 / 625 : ℚ) * (Fintype.card V).choose 5 +
        8 * (Fintype.card V : ℚ) ^ 4 := by
    have : (0 : ℚ) ≤ (Fintype.card V : ℚ) ^ 4 := by positivity
    linarith
  have h_cast := Rat.cast_le (K := ℝ) |>.mpr hq
  simp only [Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_div] at h_cast
  convert h_cast using 1

/-!
## § 13. Error Bound and Turán Density
-/

/-- For `n ≥ N₀`, the error term `8 · n⁴` is at most `ε · C(n,5)`. -/
lemma error_le_eps_choose {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (hn : n ≥ Nat.ceil (15360 * eps⁻¹ + 8)) :
    8 * (n : ℝ) ^ 4 ≤ eps * ((n.choose 5 : ℕ) : ℝ) := by
  have hn_ge_8 : 8 ≤ n :=
    le_trans (Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]
      push_cast
      linarith [Nat.le_ceil (15360 * eps⁻¹ + 8), inv_pos.2 heps]) hn
  have hepsn_ge_15360 : 15360 ≤ eps * n := by
    nlinarith [Nat.ceil_le.mp hn, mul_inv_cancel₀ heps.ne']
  have h_prod_ge_half_pow :
      (n - 1 : ℝ) * (n - 2) * (n - 3) * (n - 4) ≥ (n / 2) ^ 4 := by
    nlinarith only [show (n : ℝ) ≥ 8 by norm_cast, sq (n - 8 : ℝ)]
  have h_binom : (Nat.choose n 5 : ℝ) =
      n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
    rw [Nat.cast_choose] <;> try linarith
    rcases n with (_ | _ | _ | _ | _ | n) <;> norm_num [Nat.factorial] at *
    rw [div_eq_div_iff] <;> first | positivity | push_cast [Nat.factorial_succ]
    ring
  nlinarith [pow_pos (by positivity : 0 < (n : ℝ)) 2,
             pow_pos (by positivity : 0 < (n : ℝ)) 3,
             pow_pos (by positivity : 0 < (n : ℝ)) 4]

/-- **Turán density bound** (Theorem 1 of Grzesik, 2012).

For any `ε > 0`, all sufficiently large triangle-free graphs `G` satisfy
`numC5Copies G ≤ (24/625 + ε) · C(|V(G)|, 5)`. -/
theorem flag_algebra_c5_turan_density :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V],
      Fintype.card V ≥ N₀ → ∀ G : SimpleGraph V, G.CliqueFree 3 →
        (G.numC5Copies : ℝ) ≤ (24 / 625 + ε) * ((Fintype.card V).choose 5 : ℝ) := by
  intro ε hε
  use Nat.ceil (15360 * ε⁻¹ + 8)
  intro V _ hn G hG
  have h1 := numC5Copies_le_turan_plus_error G hG
  have h2 := error_le_eps_choose hε hn
  calc (G.numC5Copies : ℝ)
      ≤ (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
        8 * (Fintype.card V : ℝ) ^ 4 := h1
    _ ≤ (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
        ε * ((Fintype.card V).choose 5 : ℝ) := by linarith
    _ = (24 / 625 + ε) * ((Fintype.card V).choose 5 : ℝ) := by ring

/-!
## § 14. Blow-up Construction
-/

/-- **Balanced blow-up**: replace each vertex of `G` by `N` independent copies.
Two copies `(u, i)` and `(v, j)` are adjacent iff `G.Adj u v`. -/
def _root_.SimpleGraph.blowup {V : Type*} (G : SimpleGraph V) (N : ℕ) :
    SimpleGraph (V × Fin N) where
  Adj p q := G.Adj p.1 q.1
  symm := by
    constructor
    intro p q h
    exact G.adj_symm h
  loopless := ⟨fun _ h => G.irrefl h⟩

/-- A blow-up of a `K_k`-free graph is `K_k`-free. -/
lemma _root_.SimpleGraph.blowup_cliqueFree {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (hG : G.CliqueFree k) (N : ℕ) :
    (G.blowup N).CliqueFree k := by
  intro s ⟨hclique, hcard⟩
  apply hG (s.image Prod.fst)
  constructor
  · intro x hx y hy hne
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    simpa [SimpleGraph.blowup] using
      hclique hx' hy' (fun h => hne (by simpa using congr_arg Prod.fst h))
  · rw [Finset.card_image_of_injOn, hcard]
    intro x hx y hy hfst
    by_contra hne
    have hadj := hclique hx hy hne
    simp [SimpleGraph.blowup] at hadj
    rw [hfst] at hadj
    exact (G.loopless).irrefl _ hadj

/-- Each labeled C₅ and function `a : Fin 5 → Fin N` give rise to a C₅ copy
in `G.blowup N`. -/
lemma _root_.SimpleGraph.blowup_IsC5Copy_of_IsLabeledC5 {V : Type*} {G : SimpleGraph V}
    {N : ℕ} {f : Fin 5 → V} (hf : G.IsLabeledC5 f) (a : Fin 5 → Fin N) :
    (G.blowup N).IsC5Copy (Finset.image (fun i => (f i, a i)) Finset.univ) := by
  refine ⟨fun i => (f i, a i), ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · simp [Prod.mk.injEq] at hij
    exact hf.1 hij.1
  · simpa [SimpleGraph.blowup] using hf.2 i
  · ext x
    simp

/-- Canonical witness ordering for a C₅ copy. -/
noncomputable def _root_.SimpleGraph.IsC5Copy.witness {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsC5Copy s) : Fin 5 → V :=
  hs.choose

lemma _root_.SimpleGraph.IsC5Copy.witness_isLabeledC5 {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsC5Copy s) : G.IsLabeledC5 hs.witness :=
  hs.choose_spec.1

lemma _root_.SimpleGraph.IsC5Copy.witness_image {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsC5Copy s) :
    Finset.image hs.witness Finset.univ = s :=
  hs.choose_spec.2

/-- The blow-up map sends `(s, a)` to the corresponding C₅ copy in `G.blowup N`. -/
noncomputable def _root_.SimpleGraph.blowupC5Map {V : Type*} (G : SimpleGraph V)
    (N : ℕ) (p : Finset V × (Fin 5 → Fin N)) : Finset (V × Fin N) :=
  if h : G.IsC5Copy p.1 then
    Finset.image (fun i => (h.witness i, p.2 i)) Finset.univ
  else ∅

/-- The blow-up map sends C₅ copies in `G` to C₅ copies in `G.blowup N`. -/
lemma _root_.SimpleGraph.blowupC5Map_isC5Copy {V : Type*} {G : SimpleGraph V}
    {N : ℕ} {s : Finset V} {a : Fin 5 → Fin N} (hs : G.IsC5Copy s) :
    (G.blowup N).IsC5Copy (G.blowupC5Map N (s, a)) := by
  simp only [SimpleGraph.blowupC5Map, dif_pos hs]
  exact G.blowup_IsC5Copy_of_IsLabeledC5 hs.witness_isLabeledC5 a

set_option maxHeartbeats 800000 in
/-- The blow-up map is injective on C₅ copies. -/
lemma _root_.SimpleGraph.blowupC5Map_injective {V : Type*} {G : SimpleGraph V} {N : ℕ}
    {s₁ s₂ : Finset V} {a₁ a₂ : Fin 5 → Fin N}
    (hs₁ : G.IsC5Copy s₁) (hs₂ : G.IsC5Copy s₂)
    (h : G.blowupC5Map N (s₁, a₁) = G.blowupC5Map N (s₂, a₂)) :
    s₁ = s₂ ∧ a₁ = a₂ := by
  unfold SimpleGraph.blowupC5Map at h
  have hs : s₁ = s₂ := by
    rw [← hs₁.witness_image, ← hs₂.witness_image]
    ext x
    simp_all [Finset.ext_iff]
    exact ⟨fun ⟨i, hi⟩ => by
        obtain ⟨j, hj₁, hj₂⟩ := h _ (a₁ i) |>.1 ⟨i, hi, rfl⟩
        exact ⟨j, hj₁⟩,
      fun ⟨i, hi⟩ => by
        obtain ⟨j, hj₁, hj₂⟩ := h _ (a₂ i) |>.2 ⟨i, hi, rfl⟩
        exact ⟨j, hj₁⟩⟩
  simp_all [Finset.ext_iff]
  ext i
  specialize h (hs₂.witness i) (a₁ i)
  simp_all [Function.Injective.eq_iff
    (show Function.Injective hs₂.witness from hs₂.witness_isLabeledC5.1)]

/-- The blow-up `G.blowup N` contains at least `G.numC5Copies * N ^ 5` copies of C₅. -/
lemma _root_.SimpleGraph.blowup_numC5Copies_ge {V : Type*} [Fintype V]
    {G : SimpleGraph V} {N : ℕ} (_ : 0 < N) :
    G.numC5Copies * N ^ 5 ≤ (G.blowup N).numC5Copies := by
  trans
  · convert Set.ncard_le_ncard (show
        Set.image (fun p : Finset V × (Fin 5 → Fin N) => G.blowupC5Map N p)
          ({s : Finset V | G.IsC5Copy s} ×ˢ Set.univ) ⊆
            {s : Finset (V × Fin N) | (G.blowup N).IsC5Copy s}
        from Set.image_subset_iff.mpr fun p hp => ?_)
    · rw [Set.InjOn.ncard_image, Set.ncard_prod]
      · simp [Set.ncard_univ, SimpleGraph.numC5Copies]
        exact Or.inl (by
          rw [← Set.ncard_coe_finset]
          congr
          ext
          simp)
      · intro p hp q hq h_eq
        have := SimpleGraph.blowupC5Map_injective
          (show G.IsC5Copy p.1 from hp.1) (show G.IsC5Copy q.1 from hq.1) h_eq
        aesop
    · exact SimpleGraph.blowupC5Map_isC5Copy hp.1
  · rw [SimpleGraph.numC5Copies]
    exact le_of_eq (by
      rw [← Set.ncard_coe_finset
        ((Finset.univ : Finset (Finset (V × Fin N))).filter (G.blowup N).IsC5Copy)]
      apply congrArg Set.ncard
      ext s
      simp)

/-!
## § 15. Combinatorial Bounds
-/

/-- `120 * C(M, 5) ≤ M ^ 5` for all `M : ℕ`. -/
lemma Nat.mul_choose_five_le (M : ℕ) : 120 * M.choose 5 ≤ M ^ 5 := by
  have h1 : M.choose 5 = M.descFactorial 5 / Nat.factorial 5 :=
    Nat.choose_eq_descFactorial_div_factorial M 5
  have h2 : Nat.factorial 5 = 120 := by norm_num
  rw [h1, h2]
  have h3 : 120 ∣ M.descFactorial 5 := by
    rw [← h2]
    exact Nat.factorial_dvd_descFactorial M 5
  rw [Nat.mul_div_cancel' h3]
  exact Nat.descFactorial_le_pow M 5

/-- `C(M, 5) ≤ M⁵ / 120` over `ℝ`. -/
lemma Real.choose_five_le_div (M : ℕ) :
    (M.choose 5 : ℝ) ≤ (M : ℝ) ^ 5 / 120 := by
  rw [le_div_iff₀ (by norm_num : (120 : ℝ) > 0)]
  have h := Nat.mul_choose_five_le M
  have : (120 : ℝ) * (M.choose 5 : ℝ) ≤ (M : ℝ) ^ 5 := by exact_mod_cast h
  linarith

/-!
## § 16. Main Theorem
-/

/-- Arithmetic identity: `(24/625 + 12/(625 · n⁵)) · (5n)⁵ / 120 = n⁵ + 1/2`. -/
lemma erdos_key_arithmetic (n : ℕ) (hn : 0 < n) :
    (24 / 625 + 12 / (625 * (n : ℝ) ^ 5)) * ((5 * (n : ℝ)) ^ 5 / 120) =
    (n : ℝ) ^ 5 + 1 / 2 := by
  have : (n : ℝ) ^ 5 ≠ 0 :=
    pow_ne_zero 5 (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))
  field_simp
  ring

/-- A natural number `c ≤ n⁵ + 1/2` (over `ℝ`) implies `c ≤ n⁵` (over `ℕ`). -/
lemma nat_le_of_real_le_add_half (c n : ℕ) (h : (c : ℝ) ≤ (n : ℝ) ^ 5 + 1 / 2) :
    c ≤ n ^ 5 := by
  have : (c : ℝ) < (n ^ 5 + 1 : ℕ) := by
    push_cast
    linarith
  exact Nat.lt_add_one_iff.mp (Nat.cast_lt.mp this)

/-- **Erdős Pentagon Conjecture** (settled affirmatively by Grzesik, 2012).
  Statement in terms of `SimpleGraph.numC5Copies`. See `erdos_pentagon_conjecture` for
  a statement in terms of `SimpleGraph.numC5`. See Section §11 for a discussion on the
  differences between the two.

Every triangle-free graph on `5n` vertices contains at most `n⁵` copies of `C₅`.

The proof follows Grzesik's Theorem 2: assuming `c = numC5Copies G`, the balanced
blow-up `G.blowup N` is triangle-free with `≥ c · N⁵` copies of `C₅`. Choosing
`ε = 12/(625·n⁵)` and applying the Turán density bound to the blow-up gives
`c ≤ n⁵ + 1/2`, hence `c ≤ n⁵` since `c` is a natural number. -/
theorem erdos_pentagon_conjecture' (n : ℕ) (G : SimpleGraph (Fin (5 * n)))
    (hG : G.CliqueFree 3) :
    G.numC5Copies ≤ n ^ 5 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show G.numC5Copies ≤ 0
    simp only [Nat.le_zero]
    unfold SimpleGraph.numC5Copies
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _ ⟨f, _, _⟩
    exact Fin.elim0 (f 0)
  set c := G.numC5Copies with hc_def
  set ε : ℝ := 12 / (625 * (n : ℝ) ^ 5) with hε_def
  have hε_pos : ε > 0 := by positivity
  obtain ⟨N₀, hN₀⟩ := flag_algebra_c5_turan_density ε hε_pos
  set N := max 1 N₀ with hN_def
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 N₀)
  have hcf := G.blowup_cliqueFree hG N
  have hcount := @SimpleGraph.blowup_numC5Copies_ge _ _ G N hN_pos
  have hcard : Fintype.card (Fin (5 * n) × Fin N) = 5 * n * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hcard_ge : Fintype.card (Fin (5 * n) × Fin N) ≥ N₀ := by
    rw [hcard]
    calc N₀ ≤ N := le_max_right 1 N₀
      _ = 1 * N := (one_mul N).symm
      _ ≤ (5 * n) * N := Nat.mul_le_mul_right N (by omega)
  have hfa := hN₀ (Fin (5 * n) × Fin N) hcard_ge (G.blowup N) hcf
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hε' : (0 : ℝ) ≤ 24 / 625 + ε := by linarith
  have h1 : (c : ℝ) * (N : ℝ) ^ 5 ≤
      ((G.blowup N).numC5Copies : ℝ) := by exact_mod_cast hcount
  have h3 : ((Fintype.card (Fin (5 * n) × Fin N)).choose 5 : ℝ) ≤
      (Fintype.card (Fin (5 * n) × Fin N) : ℝ) ^ 5 / 120 :=
    Real.choose_five_le_div _
  have hchain : (c : ℝ) * (N : ℝ) ^ 5 ≤
      (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) * (N : ℝ) ^ 5 := by
    calc (c : ℝ) * (N : ℝ) ^ 5
        ≤ ((G.blowup N).numC5Copies : ℝ) := h1
      _ ≤ (24 / 625 + ε) *
            ((Fintype.card (Fin (5 * n) × Fin N)).choose 5 : ℝ) := hfa
      _ ≤ (24 / 625 + ε) *
            ((Fintype.card (Fin (5 * n) × Fin N) : ℝ) ^ 5 / 120) :=
          mul_le_mul_of_nonneg_left h3 hε'
      _ = (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) * (N : ℝ) ^ 5 := by
          rw [hcard]
          push_cast
          ring
  have hc_le : (c : ℝ) ≤ (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) :=
    le_of_mul_le_mul_right hchain hN5
  rw [erdos_key_arithmetic n hn] at hc_le
  exact nat_le_of_real_le_add_half c n hc_le

/-!
## § 17. Equivalence of `numC5` and `numC5Copies` for Triangle-Free Graphs

In a triangle-free graph, each 5-vertex set supporting a 5-cycle admits a
unique cycle structure (up to the dihedral symmetry D₅), so the 10 labeled
5-cycles on that vertex set form a single orbit.  This gives
`|{f | IsLabeledC5 f}| = 10 * numC5Copies`, hence `numC5 = numC5Copies`.
-/

/-- The rotation `i ↦ i + 1` on `Fin 5`. -/
def Fin5.rotate : Equiv.Perm (Fin 5) :=
  ⟨fun i => i + 1, fun i => i - 1,
   fun i => by simp,
   fun i => by simp⟩

/-- The reflection `i ↦ -i` (= `5 - i`) on `Fin 5`. -/
def Fin5.reflect : Equiv.Perm (Fin 5) :=
  ⟨fun i => -i, fun i => -i,
   fun i => by simp,
   fun i => by simp⟩

/-- Rotating a labeled 5-cycle gives a labeled 5-cycle. -/
lemma IsLabeledC5_rotate {V : Type*} {G : SimpleGraph V}
    {f : Fin 5 → V} (hf : G.IsLabeledC5 f) :
    G.IsLabeledC5 (f ∘ Fin5.rotate) := by
  constructor
  · exact hf.1.comp (Equiv.injective _)
  · intro i
    show G.Adj (f (i + 1)) (f (i + 1 + 1))
    exact hf.2 (i + 1)

/-- Reflecting a labeled 5-cycle gives a labeled 5-cycle. -/
lemma IsLabeledC5_reflect {V : Type*} {G : SimpleGraph V}
    {f : Fin 5 → V} (hf : G.IsLabeledC5 f) :
    G.IsLabeledC5 (f ∘ Fin5.reflect) := by
  constructor
  · exact hf.1.comp (Equiv.injective _)
  · intro i
    show G.Adj (f (-i)) (f (-(i + 1)))
    have : G.Adj (f (-(i+1))) (f (-(i+1) + 1)) := hf.2 (-(i+1))
    have h2 : -(i + 1) + 1 = -i := by fin_cases i <;> decide
    rw [h2] at this
    exact this.symm

set_option maxHeartbeats 6400000 in
/-- In a triangle-free graph, non-consecutive vertices of a labeled 5-cycle are
non-adjacent. Equivalently, the induced subgraph on the 5 vertices is exactly C₅
(no chords), because any chord in a 5-cycle creates a triangle. -/
lemma triangleFree_C5_no_chords {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 3)
    {f : Fin 5 → V} (hf : G.IsLabeledC5 f)
    (i j : Fin 5) (hij : j ≠ i + 1) (hji : i ≠ j + 1) (hne : i ≠ j) :
    ¬G.Adj (f i) (f j) := by
  intro hadj
  have h := hf.2
  have h01 : G.Adj (f 0) (f 1) := h 0
  have h12 : G.Adj (f 1) (f 2) := h 1
  have h23 : G.Adj (f 2) (f 3) := h 2
  have h34 : G.Adj (f 3) (f 4) := h 3
  have h40 : G.Adj (f 4) (f 0) := by
    have := h 4
    simp at this
    exact this
  have tri : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      G.Adj (f a) (f b) → G.Adj (f a) (f c) → G.Adj (f b) (f c) → False := by
    intro a b c hab hac hbc e1 e2 e3
    apply hG {f a, f b, f c}
    constructor
    · intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
    · simp [hf.1.ne hab, hf.1.ne hac, hf.1.ne hbc]
  fin_cases i <;> fin_cases j <;> simp_all (config := { decide := true })
  · exact tri 0 2 1 (by decide) (by decide) (by decide) hadj h01 h12.symm
  · exact tri 0 3 4 (by decide) (by decide) (by decide) hadj h40.symm h34
  · exact tri 1 3 2 (by decide) (by decide) (by decide) hadj h12 h23.symm
  · exact tri 1 4 0 (by decide) (by decide) (by decide) hadj h01.symm h40
  · exact tri 2 0 1 (by decide) (by decide) (by decide) hadj h12.symm h01
  · exact tri 2 4 3 (by decide) (by decide) (by decide) hadj h23 h34.symm
  · exact tri 3 0 4 (by decide) (by decide) (by decide) hadj h34 h40.symm
  · exact tri 3 1 2 (by decide) (by decide) (by decide) hadj h23.symm h12
  · exact tri 4 1 0 (by decide) (by decide) (by decide) hadj h40 h01.symm
  · exact tri 4 2 3 (by decide) (by decide) (by decide) hadj h34.symm h23

/-
In a triangle-free graph, the number of labeled 5-cycles on a given vertex set
is exactly 10 (the order of the dihedral group D₅).

The proof uses `triangleFree_C5_no_chords` to show that the only permutations
preserving the cycle structure are the 10 dihedral symmetries (5 rotations ×
2 orientations).
-/
lemma labeledC5_fiber_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.CliqueFree 3)
    {S : Finset V} (hS : G.IsC5Copy S) :
    ((Finset.univ : Finset (Fin 5 → V)).filter
      (fun f => G.IsLabeledC5 f ∧ Finset.image f Finset.univ = S)).card = 10 := by
        revert hS S
        intro S hS
        obtain ⟨f₀, hf₀⟩ := hS
        have h_adj : ∀ i j : Fin 5, G.Adj (f₀ i) (f₀ j) ↔ (j = i + 1 ∨ i = j + 1) := by
          intro i j
          constructor
          · intro hij
            by_contra h_contra
            exact triangleFree_C5_no_chords hG hf₀.1 i j
              (by tauto) (by tauto) (by aesop) hij
          · rintro (rfl | rfl) <;> simp_all +decide [SimpleGraph.IsLabeledC5]
            simpa [SimpleGraph.adj_comm] using hf₀.1.2 j
        -- We need to show that the set of labeled 5-cycles on $S$ is in bijection with the set
        -- of dihedral permutations of $\{0, 1, 2, 3, 4\}$.
        have h_bij :
            {f : Fin 5 → V | G.IsLabeledC5 f ∧ Finset.image f Finset.univ = S} =
              Finset.image
                (fun σ : Equiv.Perm (Fin 5) => fun i => f₀ (σ i))
                (Finset.filter
                  (fun σ : Equiv.Perm (Fin 5) =>
                    ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1)
                  (Finset.univ : Finset (Equiv.Perm (Fin 5)))) := by
          ext f
          simp
          constructor
          · intro hf
            obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), ∀ i, f i = f₀ (σ i) := by
              have h_bij : ∀ i, ∃ j, f i = f₀ j := by
                intro i
                have h_mem : f i ∈ S := by
                  exact hf.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
                grind +qlia
              choose σ hσ using h_bij
              have hσ_inj : Function.Injective σ := by
                intro i j hij
                have := hf.1.1
                have := hf₀.1.1
                aesop
              exact ⟨
                Equiv.ofBijective σ
                  ⟨hσ_inj, Finite.injective_iff_surjective.mp hσ_inj⟩,
                hσ⟩
            use σ
            simp_all +decide [funext_iff, SimpleGraph.IsLabeledC5]
          · rintro ⟨σ, hσ, rfl⟩
            simp_all +decide [SimpleGraph.IsLabeledC5]
            simp_all +decide [Finset.ext_iff, Function.Injective]
            exact ⟨
              fun i j hij => σ.injective (hf₀.1 hij),
              fun a => by
                rw [← hf₀.2 a]
                exact ⟨
                  fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
                  fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩⟩⟩
        rw [Set.ext_iff] at h_bij
        convert Finset.card_image_of_injective _
          (show Function.Injective
              (fun σ : Equiv.Perm (Fin 5) => fun i => f₀ (σ i)) from ?_) using 1
        any_goals
          exact Finset.filter
            (fun σ : Equiv.Perm (Fin 5) =>
              ∀ i : Fin 5, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1)
            Finset.univ
        · exact congr_arg Finset.card (Finset.ext fun x => by simpa using h_bij x)
        · decide
        · intro σ τ hστ
          have := hf₀.1.1
          simp_all +decide [funext_iff, Fin.forall_fin_succ]
          exact Equiv.Perm.ext fun x => this <| by fin_cases x <;> tauto

/-
In a triangle-free graph, `numC5 = numC5Copies`.

Each 5-element vertex set supporting a cycle gives rise to exactly 10
labeled 5-cycles (one orbit under D₅), so
`|{f | IsLabeledC5 f}| = 10 * numC5Copies` and dividing by 10 recovers
`numC5Copies`.
-/
theorem numC5_eq_numC5Copies_of_triangleFree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    G.numC5 = G.numC5Copies := by
      classical
      have := @labeledC5_fiber_card
      rw [eq_comm, SimpleGraph.numC5, SimpleGraph.numC5Copies]
      rw [Nat.div_eq_of_eq_mul_left]
      focus decide +revert
      rw [← Finset.sum_const_nat]
      focus nontriviality
      focus convert Finset.card_biUnion _
      rotate_left
      focus infer_instance
      rotate_left
      focus
        intro S hS
        convert this hG (Finset.mem_filter.mp hS |>.2)
      · ext f
        simp [SimpleGraph.IsC5Copy]
        grind +qlia
      · exact fun x hx y hy hxy =>
          Finset.disjoint_left.mpr fun f hf₁ hf₂ => hxy <| by aesop

/-- **Erdős Pentagon Conjecture** (settled affirmatively by Grzesik, 2012).

Every triangle-free graph on `5n` vertices contains at most `n⁵` copies of `C₅`,
where copies are counted as subgraphs isomorphic to the cycle graph `C₅`
(see `SimpleGraph.numC5` and Section §11). -/
theorem erdos_pentagon_conjecture (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (hG : G.CliqueFree 3) :
    G.numC5 ≤ n ^ 5 := by
  rw [numC5_eq_numC5Copies_of_triangleFree G hG]
  exact erdos_pentagon_conjecture' n G hG

#print axioms erdos_pentagon_conjecture
-- 'Erdos24.erdos_pentagon_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos24
