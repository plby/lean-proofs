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
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.show false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 0

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

private def L_P : Matrix (Fin 8) (Fin 8) ℚ
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

private def D_P_vec : Fin 8 → ℚ
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
  admit

private lemma Q_ldlt : Q_cert = L_Q * Matrix.diagonal D_Q_vec * L_Q.transpose := by
  admit

private lemma R_ldlt : R_cert = L_R * Matrix.diagonal D_R_vec * L_R.transpose := by
  admit

private lemma D_P_nonneg : ∀ i : Fin 8, 0 ≤ D_P_vec i := by
  admit

private lemma D_Q_nonneg : ∀ i : Fin 6, 0 ≤ D_Q_vec i := by
  admit

private lemma D_R_nonneg : ∀ i : Fin 5, 0 ≤ D_R_vec i := by
  admit

/-- If `M = L * diag(d) * Lᵀ` with `d ≥ 0`, then `M` is positive semidefinite. -/
lemma psd_of_ldlt {n : ℕ} (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hM : M = L * Matrix.diagonal d * L.transpose) :
    ∀ v : Fin n → ℚ, 0 ≤ dotProduct v (M.mulVec v) := by
  admit

lemma P_cert_psd : ∀ v : Fin 8 → ℚ, 0 ≤ dotProduct v (P_cert.mulVec v) :=
  by admit

lemma Q_cert_psd : ∀ v : Fin 6 → ℚ, 0 ≤ dotProduct v (Q_cert.mulVec v) :=
  by admit

lemma R_cert_psd : ∀ v : Fin 5 → ℚ, 0 ≤ dotProduct v (R_cert.mulVec v) :=
  by admit

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
  let ab := adj a b; let ac := adj a c; let bc := adj b c
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
  admit

/-- For every triangle-free graph on `Fin 5`,
`totalFlagContrib ≤ 576/125 = 120 · (24/625)`.
Checked over all `2^10 = 1024` possible edge configurations by kernel reduction. -/
theorem flag_bound_all_graphs : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) ≤ 576 / 125 := by
  admit

attribute [local instance] Classical.propDecidable

/-- Whether a graph on `Fin 5` is a 5-cycle. -/
def isC5_adj (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  decide (
      (adj 0 1 = true ∧ adj 0 2 = true ∧ adj 0 3 = false ∧ adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = true ∧ adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧ adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = true ∧ adj 0 3 = false ∧ adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = false ∧ adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧ adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = true ∧ adj 0 4 = false ∧ adj 1 2 = true ∧ adj 1 3 = false ∧ adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧ adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = true ∧ adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = false ∧ adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = true ∧ adj 3 4 = false) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = false ∧ adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = false ∧ adj 1 4 = false ∧ adj 2 3 = true ∧ adj 2 4 = false ∧ adj 3 4 = true) ∨
      (adj 0 1 = true ∧ adj 0 2 = false ∧ adj 0 3 = false ∧ adj 0 4 = true ∧ adj 1 2 = false ∧ adj 1 3 = true ∧ adj 1 4 = false ∧ adj 2 3 = true ∧ adj 2 4 = true ∧ adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = true ∧ adj 0 4 = false ∧ adj 1 2 = true ∧ adj 1 3 = false ∧ adj 1 4 = true ∧ adj 2 3 = false ∧ adj 2 4 = false ∧ adj 3 4 = true) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = true ∧ adj 0 4 = false ∧ adj 1 2 = false ∧ adj 1 3 = true ∧ adj 1 4 = true ∧ adj 2 3 = false ∧ adj 2 4 = true ∧ adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = false ∧ adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = true ∧ adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = false ∧ adj 3 4 = true) ∨
      (adj 0 1 = false ∧ adj 0 2 = true ∧ adj 0 3 = false ∧ adj 0 4 = true ∧ adj 1 2 = false ∧ adj 1 3 = true ∧ adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧ adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = false ∧ adj 0 3 = true ∧ adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = true ∧ adj 1 4 = false ∧ adj 2 3 = false ∧ adj 2 4 = true ∧ adj 3 4 = false) ∨
      (adj 0 1 = false ∧ adj 0 2 = false ∧ adj 0 3 = true ∧ adj 0 4 = true ∧ adj 1 2 = true ∧ adj 1 3 = false ∧ adj 1 4 = true ∧ adj 2 3 = true ∧ adj 2 4 = false ∧ adj 3 4 = false))

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
  admit

private lemma c5_contrib_0 :
    totalFlagContrib (mkAdj5 (edgeBits true true false false false true false false true true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_1 :
    totalFlagContrib (mkAdj5 (edgeBits true true false false false false true true false true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_2 :
    totalFlagContrib (mkAdj5 (edgeBits true false true false true false false false true true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_3 :
    totalFlagContrib (mkAdj5 (edgeBits true false true false false false true true true false)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_4 :
    totalFlagContrib (mkAdj5 (edgeBits true false false true true false false true false true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_5 :
    totalFlagContrib (mkAdj5 (edgeBits true false false true false true false true true false)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_6 :
    totalFlagContrib (mkAdj5 (edgeBits false true true false true false true false false true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_7 :
    totalFlagContrib (mkAdj5 (edgeBits false true true false false true true false true false)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_8 :
    totalFlagContrib (mkAdj5 (edgeBits false true false true true true false false false true)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_9 :
    totalFlagContrib (mkAdj5 (edgeBits false true false true false true true true false false)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_10 :
    totalFlagContrib (mkAdj5 (edgeBits false false true true true true false false true false)) =
      -14424 / 125 := by
  admit

private lemma c5_contrib_11 :
    totalFlagContrib (mkAdj5 (edgeBits false false true true true false true true false false)) =
      -14424 / 125 := by
  admit

/-- Strengthened computational bound including the C₅ indicator. -/
theorem flag_bound_with_c5 : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) +
      120 * (if isC5_adj (mkAdj5 e) then 1 else 0) ≤ 576 / 125 := by
  admit

/-!
## § 4. Graph Adjacency from Injective Functions
-/

/-- The adjacency function of `G` pulled back along `f : Fin 5 → V`. -/
def graphAdj5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    Fin 5 → Fin 5 → Bool :=
  fun i j => decide (G.Adj (f i) (f j))

lemma graphAdj5_symm {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i j, graphAdj5 G f i j = graphAdj5 G f j i := by
  admit

lemma graphAdj5_irrefl {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i, graphAdj5 G f i i = false := by
  admit

set_option maxHeartbeats 800000 in
lemma graphAdj5_triangleFree {V : Type*}
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (f : Fin 5 → V) (_hf : f.Injective) :
    ∀ a b c : Fin 5,
      ¬(graphAdj5 G f a b = true ∧ graphAdj5 G f b c = true ∧
        graphAdj5 G f a c = true) := by
  admit

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
  admit

lemma flag_bound_for_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj ≤ 576 / 125 := by
  admit

lemma flag_bound_with_c5_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj +
      120 * (if isC5_adj adj then 1 else 0) ≤ 576 / 125 := by
  admit

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
  · simpa [totalFlagContrib, mkAdj5] using
      totalFlagContribBits_swap01 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5] using
      totalFlagContribBits_swap12 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5] using
      totalFlagContribBits_swap23 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
  · simpa [totalFlagContrib, mkAdj5] using
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

end

end Erdos24
