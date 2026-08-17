/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import Mathlib

/-!
# Finite linear fibers and rank stability modulo a prime

This file contains two elementary pieces of linear algebra used in the
Ma--Tang argument for Erdős Problem 543.

* Every nonempty fiber of a homomorphism from a finite additive group has the
  same cardinality as its kernel.  For a linear map over a finite division
  ring this gives the usual power-of-the-field formula.
* A nonzero integral minor remains nonzero modulo every prime larger than its
  absolute determinant.  For a matrix with entries of absolute value at most
  one, the Leibniz formula gives the convenient coarse bound `r!`.

The second statement is formulated for an explicitly supplied minor.  This is
the form needed after choosing linearly independent rows and columns: it does
not require a separate library theorem extracting a maximal minor.
-/

open scoped BigOperators

namespace Erdos543

/-! ## Uniform fibers -/

section Fibers

variable {K V W : Type*} [DivisionRing K]
variable [AddCommGroup V] [Module K V] [Fintype V]
variable [AddCommGroup W] [Module K W] [DecidableEq W]

/-- The finite fiber of a linear map over a specified target. -/
noncomputable def linearFiber (f : V →ₗ[K] W) (y : W) : Finset V := by
  classical
  exact Finset.univ.filter fun x ↦ f x = y

@[simp] theorem mem_linearFiber (f : V →ₗ[K] W) (y : W) (x : V) :
    x ∈ linearFiber f y ↔ f x = y := by
  classical
  simp [linearFiber]

/-- Translation by any point in a nonempty fiber identifies that fiber with
the kernel; at the cardinality level this says all nonempty fibers are
uniform. -/
theorem card_linearFiber_eq_card_ker (f : V →ₗ[K] W) {y : W}
    (hy : y ∈ Set.range f) :
    (linearFiber f y).card = Nat.card f.ker := by
  classical
  let _ : Fintype f.ker := Fintype.ofFinite f.ker
  calc
    (linearFiber f y).card = (Finset.univ.filter fun x : V ↦ f x = 0).card := by
      exact AddMonoidHom.card_fiber_eq_of_mem_range f hy ⟨0, by simp⟩
    _ = Fintype.card f.ker := by
      simpa [LinearMap.mem_ker] using
        (Fintype.card_subtype (fun x : V ↦ f x = 0)).symm
    _ = Nat.card f.ker := Fintype.card_eq_nat_card

/-- Cardinality of a nonempty fiber of a linear map over a finite division
ring. -/
theorem card_linearFiber_eq_pow_finrank_ker [Fintype K] [FiniteDimensional K V]
    (f : V →ₗ[K] W) {y : W}
    (hy : y ∈ Set.range f) :
    (linearFiber f y).card = Fintype.card K ^ Module.finrank K f.ker := by
  have hcard : Nat.card f.ker = Nat.card K ^ Module.finrank K f.ker :=
    Module.natCard_eq_pow_finrank (K := K) (V := f.ker)
  rw [card_linearFiber_eq_card_ker f hy, hcard, Nat.card_eq_fintype_card]

/-- Rank-nullity form of the finite-fiber formula. -/
theorem card_linearFiber_eq_pow_finrank_sub [Fintype K] [FiniteDimensional K V]
    (f : V →ₗ[K] W) {y : W} (hy : y ∈ Set.range f) :
    (linearFiber f y).card =
      Fintype.card K ^ (Module.finrank K V - Module.finrank K f.range) := by
  rw [card_linearFiber_eq_pow_finrank_ker f hy]
  congr 1
  exact Nat.eq_sub_of_add_eq <| by
    rw [add_comm]
    exact f.finrank_range_add_finrank_ker

end Fibers

/-! ## Matrix fibers over `ZMod p` -/

section MatrixFibers

variable {p : ℕ} [Fact p.Prime]
variable {m n : Type*} [Fintype n] [Fintype m]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-- The solutions of `M x = y` over the prime field `ZMod p`. -/
noncomputable def matrixFiber (M : Matrix m n (ZMod p)) (y : m → ZMod p) :
    Finset (n → ZMod p) := by
  classical
  let _ : Fintype (n → ZMod p) := Fintype.ofFinite (n → ZMod p)
  exact linearFiber M.mulVecLin y

@[simp] theorem mem_matrixFiber (M : Matrix m n (ZMod p)) (y : m → ZMod p)
    (x : n → ZMod p) : x ∈ matrixFiber M y ↔ M.mulVec x = y := by
  classical
  let _ : Fintype (n → ZMod p) := Fintype.ofFinite (n → ZMod p)
  simp [matrixFiber]

/-- An attainable right-hand side of a rank-`d` matrix over `ZMod p` has
exactly `p ^ (n - d)` preimages. -/
theorem card_matrixFiber (M : Matrix m n (ZMod p)) {y : m → ZMod p}
    (hy : y ∈ Set.range M.mulVecLin) :
    (matrixFiber M y).card = p ^ (Fintype.card n - M.rank) := by
  classical
  let _ : Fintype (n → ZMod p) := Fintype.ofFinite (n → ZMod p)
  rw [matrixFiber, card_linearFiber_eq_pow_finrank_sub M.mulVecLin hy, ZMod.card,
    Module.finrank_fintype_fun_eq_card]
  congr 1

end MatrixFibers

/-! ## Extracting a nonsingular minor -/

section MinorExtraction

/-- If `s` is at most the rank of a matrix over a field, then `s` of its
actual columns can be selected to form a linearly independent family.  The
proof first chooses a basis from the finite set of all columns and then takes
the first `s` members of that basis. -/
theorem exists_cols_linearIndependent_of_le_rank
    {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (M : Matrix m n K) {s : ℕ} (hs : s ≤ M.rank) :
    ∃ cols : Fin s → n, LinearIndependent K (fun j ↦ M.col (cols j)) := by
  classical
  obtain ⟨f, hf_mem, _hf_span, hf_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.col)
  have hrank : Module.finrank K (Submodule.span K (Set.range M.col)) = M.rank :=
    M.rank_eq_finrank_span_cols.symm
  let e : Fin s → Fin (Module.finrank K (Submodule.span K (Set.range M.col))) :=
    fun i ↦ ⟨i, lt_of_lt_of_le i.isLt (hrank.symm ▸ hs)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg (fun x : Fin (Module.finrank K
      (Submodule.span K (Set.range M.col))) ↦ x.val) hij
  have hli : LinearIndependent K (fun i ↦ f (e i)) := hf_li.comp e he
  have hmem : ∀ i, ∃ j, M.col j = f (e i) := fun i ↦ hf_mem (e i)
  choose cols hcols using hmem
  refine ⟨cols, ?_⟩
  simpa only [hcols] using hli

/-- The minor characterization of matrix rank, in the direction used for
extraction: every size at most the rank is witnessed by a nonsingular square
minor of that size. -/
theorem exists_minor_det_ne_zero_of_le_rank
    {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (M : Matrix m n K) {s : ℕ} (hs : s ≤ M.rank) :
    ∃ rows : Fin s → m, ∃ cols : Fin s → n,
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨cols, hcols⟩ := exists_cols_linearIndependent_of_le_rank M hs
  let B : Matrix m (Fin s) K := M.submatrix id cols
  have hBcols : LinearIndependent K B.col := by
    convert hcols using 1
    ext j i
    rfl
  have hBrank : B.rank = s := by
    rw [B.rank_eq_finrank_span_cols, finrank_span_eq_card hBcols,
      Fintype.card_fin]
  have hBtRank : B.transpose.rank = s := by simpa using hBrank
  obtain ⟨rows, hrows⟩ :=
    exists_cols_linearIndependent_of_le_rank B.transpose (le_of_eq hBtRank.symm)
  refine ⟨rows, cols, ?_⟩
  let C : Matrix (Fin s) (Fin s) K := M.submatrix rows cols
  have hCrows : LinearIndependent K C.row := by
    convert hrows using 1
    ext i j
    rfl
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row hCrows)

/-- Conversely, a nonsingular `s × s` minor certifies rank at least `s`. -/
theorem rank_ge_of_minor_det_ne_zero
    {K m n : Type*} [Field K] [Fintype n]
    (M : Matrix m n K) {s : ℕ} (rows : Fin s → m) (cols : Fin s → n)
    (hdet : (M.submatrix rows cols).det ≠ 0) : s ≤ M.rank := by
  have hfull : (M.submatrix rows cols).rank = s := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  exact hfull ▸ Matrix.rank_submatrix_le M rows cols

end MinorExtraction

/-! ## Determinant bounds for integral matrices -/

section DeterminantBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coarse Leibniz bound: if every integral entry has absolute value at most
one, the determinant has absolute value at most the factorial of the size. -/
theorem natAbs_det_le_factorial_of_entry_le_one (A : Matrix ι ι ℤ)
    (hA : ∀ i j, Int.natAbs (A i j) ≤ 1) :
    Int.natAbs A.det ≤ (Fintype.card ι).factorial := by
  have h := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := (1 : ℤ))
    (fun i j ↦ by
      rw [AbsoluteValue.abs_apply, Int.abs_eq_natAbs]
      exact_mod_cast hA i j)
  simp only [AbsoluteValue.abs_apply, one_pow, nsmul_eq_mul, mul_one] at h
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

/-- In particular, the same factorial bound holds for a zero-one matrix. -/
theorem natAbs_det_le_factorial_of_zero_one (A : Matrix ι ι ℤ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    Int.natAbs A.det ≤ (Fintype.card ι).factorial := by
  apply natAbs_det_le_factorial_of_entry_le_one A
  intro i j
  rcases hA i j with h | h <;> simp [h]

end DeterminantBound

/-! ## Stability of an integral minor modulo a prime -/

section RankStability

variable {p r : ℕ} [Fact p.Prime]
variable {m n : Type*} [Fintype n]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-- An integer whose nonzero absolute value is smaller than `p` remains
nonzero in `ZMod p`.  Primality is not needed for this elementary step. -/
theorem intCast_zmod_ne_zero_of_natAbs_lt (z : ℤ) (hz : z ≠ 0)
    (hsmall : Int.natAbs z < p) : (z : ZMod p) ≠ 0 := by
  intro hzmod
  have hpdiv : (p : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzmod
  have hle : p ≤ Int.natAbs z := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpdiv hz
  omega

/-- A supplied nonzero `r × r` integral minor whose determinant is smaller
than `p` certifies rank at least `r` after reduction modulo `p`. -/
theorem rank_map_zmod_ge_of_minor_det (A : Matrix m n ℤ)
    (rows : Fin r → m) (cols : Fin r → n)
    (hdet : (A.submatrix rows cols).det ≠ 0)
    (hsmall : Int.natAbs (A.submatrix rows cols).det < p) :
    r ≤ (A.map (Int.castRingHom (ZMod p))).rank := by
  let B : Matrix (Fin r) (Fin r) ℤ := A.submatrix rows cols
  let Bp : Matrix (Fin r) (Fin r) (ZMod p) :=
    (Int.castRingHom (ZMod p)).mapMatrix B
  have hBpdet : Bp.det ≠ 0 := by
    rw [← (Int.castRingHom (ZMod p)).map_det B]
    exact intCast_zmod_ne_zero_of_natAbs_lt B.det hdet hsmall
  have hfull : Bp.rank = r := by
    simpa [Bp] using Matrix.rank_of_det_ne_zero hBpdet
  have hsub : Bp.rank ≤ (A.map (Int.castRingHom (ZMod p))).rank := by
    have hle := Matrix.rank_submatrix_le
      (A.map (Int.castRingHom (ZMod p))) rows cols
    simpa [Bp, B, RingHom.mapMatrix_apply, Matrix.submatrix_map] using hle
  omega

/-- Factorial-sized prime version for a zero-one minor. -/
theorem rank_map_zmod_ge_of_zero_one_minor (A : Matrix m n ℤ)
    (rows : Fin r → m) (cols : Fin r → n)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdet : (A.submatrix rows cols).det ≠ 0)
    (hprime : r.factorial < p) :
    r ≤ (A.map (Int.castRingHom (ZMod p))).rank := by
  apply rank_map_zmod_ge_of_minor_det A rows cols hdet
  exact lt_of_le_of_lt
    (natAbs_det_le_factorial_of_zero_one (A.submatrix rows cols)
      (fun i j ↦ hzeroOne (rows i) (cols j))) (by simpa using hprime)

/-- Square specialization: a nonsingular zero-one integral matrix has full
rank modulo every prime larger than `r!`. -/
theorem rank_map_zmod_eq_of_zero_one_det_ne_zero (A : Matrix (Fin r) (Fin r) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdet : A.det ≠ 0) (hprime : r.factorial < p) :
    (A.map (Int.castRingHom (ZMod p))).rank = r := by
  apply le_antisymm
  · simpa using Matrix.rank_le_card_height (A.map (Int.castRingHom (ZMod p)))
  · simpa using rank_map_zmod_ge_of_zero_one_minor A id id hzeroOne hdet hprime

end RankStability

/-! ## Rectangular rank stability -/

section RectangularRankStability

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-- Reduction modulo a prime cannot increase the rank of an integral matrix.
Indeed, any nonsingular minor modulo `p` comes from a nonzero integral minor,
which is also nonzero over `ℚ`. -/
theorem rank_map_zmod_le_rank_map_rat
    {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℤ) :
    (A.map (Int.castRingHom (ZMod p))).rank ≤
      (A.map (Int.castRingHom ℚ)).rank := by
  let Ap : Matrix (Fin rows) (Fin cols) (ZMod p) :=
    A.map (Int.castRingHom (ZMod p))
  let Aq : Matrix (Fin rows) (Fin cols) ℚ := A.map (Int.castRingHom ℚ)
  by_contra hle
  have hsucc : Aq.rank + 1 ≤ Ap.rank :=
    Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  obtain ⟨rs, cs, hdetp⟩ := exists_minor_det_ne_zero_of_le_rank Ap hsucc
  have hdetZ : (A.submatrix rs cs).det ≠ 0 := by
    intro hzero
    apply hdetp
    rw [show Ap.submatrix rs cs =
        (Int.castRingHom (ZMod p)).mapMatrix (A.submatrix rs cs) by
      ext i j
      rfl]
    rw [← (Int.castRingHom (ZMod p)).map_det, hzero, map_zero]
  have hdetq : (Aq.submatrix rs cs).det ≠ 0 := by
    rw [show Aq.submatrix rs cs =
        (Int.castRingHom ℚ).mapMatrix (A.submatrix rs cs) by
      ext i j
      rfl]
    rw [← (Int.castRingHom ℚ).map_det]
    exact Int.cast_ne_zero.mpr hdetZ
  have hge := rank_ge_of_minor_det_ne_zero Aq rs cs hdetq
  omega

/-- Complete rectangular zero-one rank stability.  If `d` is the rational
rank, every nonzero `d × d` integral minor has absolute determinant at most
`d!`; hence it survives modulo any prime larger than `d!`.  The reverse rank
inequality holds for every integral matrix by
`rank_map_zmod_le_rank_map_rat`. -/
theorem rank_map_zmod_eq_rank_map_rat_of_zero_one
    {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℤ)
    (hzeroOne : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hprime : (A.map (Int.castRingHom ℚ)).rank.factorial < p) :
    (A.map (Int.castRingHom (ZMod p))).rank =
      (A.map (Int.castRingHom ℚ)).rank := by
  apply le_antisymm (rank_map_zmod_le_rank_map_rat A)
  let Aq : Matrix (Fin rows) (Fin cols) ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨rs, cs, hdetq⟩ :=
    exists_minor_det_ne_zero_of_le_rank Aq (le_refl Aq.rank)
  have hdetZ : (A.submatrix rs cs).det ≠ 0 := by
    intro hzero
    apply hdetq
    rw [show Aq.submatrix rs cs =
        (Int.castRingHom ℚ).mapMatrix (A.submatrix rs cs) by
      ext i j
      rfl]
    rw [← (Int.castRingHom ℚ).map_det, hzero, map_zero]
  exact rank_map_zmod_ge_of_zero_one_minor A rs cs hzeroOne hdetZ hprime

end RectangularRankStability

end Erdos543
