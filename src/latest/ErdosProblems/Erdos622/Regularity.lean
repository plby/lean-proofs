/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 622: finite weak cut regularity

This file develops the finite energy-increment lemma used in the bi-dense
case.  It is stated for a real matrix on a finite type.  A `CutPiece` is a
constant multiple of the indicator of a rectangle.  Repeatedly subtracting a
rectangle on which the residual has large cut sum decreases the squared
`L²` energy by a definite amount.
-/

namespace Erdos622

open Finset

attribute [local instance] Classical.propDecidable

section MatrixCuts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The sum of a real matrix over an ordered rectangle `S × T`. -/
noncomputable def matrixCutSum (A : V → V → ℝ) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, A i j

/-- A constant matrix supported on the ordered rectangle `S × T`. -/
noncomputable def cutPiece (S T : Finset V) (c : ℝ) : V → V → ℝ :=
  fun i j ↦ if i ∈ S ∧ j ∈ T then c else 0

/-- The squared Euclidean energy of a finite real matrix. -/
noncomputable def matrixEnergy (A : V → V → ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- A finite list of weighted rectangles and the matrix obtained by summing
their indicator matrices. -/
abbrev CutDecomposition (V : Type*) := List (Finset V × Finset V × ℝ)

noncomputable def cutDecompositionMatrix (L : CutDecomposition V) : V → V → ℝ :=
  fun i j ↦ (L.map fun q ↦ cutPiece q.1 q.2.1 q.2.2 i j).sum

@[simp] lemma matrixCutSum_empty_left (A : V → V → ℝ) (T : Finset V) :
    matrixCutSum A ∅ T = 0 := by
  simp [matrixCutSum]

@[simp] lemma matrixCutSum_empty_right (A : V → V → ℝ) (S : Finset V) :
    matrixCutSum A S ∅ = 0 := by
  simp [matrixCutSum]

lemma matrixCutSum_sub (A B : V → V → ℝ) (S T : Finset V) :
    matrixCutSum (A - B) S T = matrixCutSum A S T - matrixCutSum B S T := by
  simp [matrixCutSum, Finset.sum_sub_distrib]

lemma matrixCutSum_add (A B : V → V → ℝ) (S T : Finset V) :
    matrixCutSum (A + B) S T = matrixCutSum A S T + matrixCutSum B S T := by
  simp [matrixCutSum, Finset.sum_add_distrib]

lemma sum_ite_rectangle (f : V → V → ℝ) (S T : Finset V) :
    (∑ i, ∑ j, if i ∈ S ∧ j ∈ T then f i j else 0) = matrixCutSum f S T := by
  unfold matrixCutSum
  calc
    (∑ i, ∑ j, if i ∈ S ∧ j ∈ T then f i j else 0) =
        ∑ i ∈ S, ∑ j, if i ∈ S ∧ j ∈ T then f i j else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      simp [hi]
    _ = ∑ i ∈ S, ∑ j ∈ T, f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      calc
        (∑ j ∈ T, f i j) =
            ∑ j ∈ T, if i ∈ S ∧ j ∈ T then f i j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [hi, hj]
        _ = ∑ j, if i ∈ S ∧ j ∈ T then f i j else 0 := by
          apply Finset.sum_subset (Finset.subset_univ T)
          intro j _ hj
          simp [hj]

lemma matrixCutSum_mul_const (A : V → V → ℝ) (S T : Finset V) (c : ℝ) :
    matrixCutSum (fun i j ↦ A i j * c) S T = matrixCutSum A S T * c := by
  simp [matrixCutSum, Finset.sum_mul]

lemma matrixCutSum_const_mul (A : V → V → ℝ) (S T : Finset V) (c : ℝ) :
    matrixCutSum (fun i j ↦ c * A i j) S T = c * matrixCutSum A S T := by
  simp [matrixCutSum, Finset.mul_sum]

lemma matrixCutSum_cutPiece (S T : Finset V) (c : ℝ) :
    matrixCutSum (cutPiece S T c) S T = S.card * T.card * c := by
  unfold matrixCutSum
  calc
    (∑ i ∈ S, ∑ j ∈ T, cutPiece S T c i j) =
        ∑ _i ∈ S, ∑ _j ∈ T, c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [cutPiece, hi, hj]
    _ = S.card * T.card * c := by
      simp
      ring

private lemma sum_indicator_inter (X S : Finset V) (c : ℝ) :
    (∑ i ∈ X, if i ∈ S then c else 0) = (X ∩ S).card * c := by
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter]

/-- Rectangle cut sums depend only on the two intersection cardinalities. -/
lemma matrixCutSum_cutPiece_general (S T X Y : Finset V) (c : ℝ) :
    matrixCutSum (cutPiece S T c) X Y =
      (X ∩ S).card * (Y ∩ T).card * c := by
  unfold matrixCutSum
  calc
    (∑ i ∈ X, ∑ j ∈ Y, cutPiece S T c i j) =
        ∑ i ∈ X, if i ∈ S then ((Y ∩ T).card : ℝ) * c else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiS : i ∈ S
      · rw [if_pos hiS]
        simpa only [cutPiece, hiS, true_and] using
          sum_indicator_inter Y T c
      · simp [cutPiece, hiS]
    _ = (X ∩ S).card * (((Y ∩ T).card : ℝ) * c) :=
      sum_indicator_inter X S _
    _ = (X ∩ S).card * (Y ∩ T).card * c := by ring

lemma matrixEnergy_nonneg (A : V → V → ℝ) : 0 ≤ matrixEnergy A := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma matrixEnergy_eq_zero_iff (A : V → V → ℝ) :
    matrixEnergy A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext i j
    have houter : ∀ k ∈ (Finset.univ : Finset V),
        (∑ l, (A k l) ^ 2) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).mp h
    have hinner : ∀ l ∈ (Finset.univ : Finset V), (A i l) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp
        (houter i (Finset.mem_univ i))
    have hsquare : (A i j) ^ 2 = 0 := hinner j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hsquare
  · rintro rfl
    simp [matrixEnergy]

lemma sum_mul_cutPiece (A : V → V → ℝ) (S T : Finset V) (c : ℝ) :
    (∑ i, ∑ j, A i j * cutPiece S T c i j) =
      c * matrixCutSum A S T := by
  rw [show (∑ i, ∑ j, A i j * cutPiece S T c i j) =
      ∑ i, ∑ j, if i ∈ S ∧ j ∈ T then A i j * c else 0 by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [cutPiece]]
  rw [sum_ite_rectangle]
  rw [matrixCutSum_mul_const]
  ring

lemma sum_sq_cutPiece (S T : Finset V) (c : ℝ) :
    (∑ i, ∑ j, (cutPiece S T c i j) ^ 2) =
      (S.card * T.card : ℝ) * c ^ 2 := by
  rw [show (∑ i, ∑ j, (cutPiece S T c i j) ^ 2) =
      ∑ i, ∑ j, if i ∈ S ∧ j ∈ T then c ^ 2 else 0 by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [cutPiece]]
  rw [sum_ite_rectangle]
  simp [matrixCutSum]
  ring

lemma matrixEnergy_sub_cutPiece (A : V → V → ℝ) (S T : Finset V) (c : ℝ) :
    matrixEnergy (A - cutPiece S T c) =
      matrixEnergy A - 2 * c * matrixCutSum A S T +
        (S.card * T.card : ℝ) * c ^ 2 := by
  unfold matrixEnergy
  simp only [Pi.sub_apply]
  simp_rw [sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_mul_cutPiece, sum_sq_cutPiece]
  rw [matrixCutSum_const_mul]
  ring

lemma matrixEnergy_average_cut (A : V → V → ℝ) (S T : Finset V)
    (hST : 0 < S.card * T.card) :
    let x := matrixCutSum A S T
    let c := x / (S.card * T.card : ℝ)
    matrixEnergy (A - cutPiece S T c) =
      matrixEnergy A - x ^ 2 / (S.card * T.card : ℝ) := by
  dsimp
  rw [matrixEnergy_sub_cutPiece]
  have hp : (S.card * T.card : ℝ) ≠ 0 := by exact_mod_cast hST.ne'
  field_simp
  ring

/-- A residual matrix is cut-regular at scale `ε` when every ordered
rectangle has discrepancy at most `ε |V|²`. -/
def IsCutRegular (ε : ℝ) (A : V → V → ℝ) : Prop :=
  ∀ S T : Finset V,
    |matrixCutSum A S T| ≤ ε * (Fintype.card V : ℝ) ^ 2

@[simp] lemma cutDecompositionMatrix_nil :
    cutDecompositionMatrix ([] : CutDecomposition V) = 0 := by
  funext i j
  simp [cutDecompositionMatrix]

@[simp] lemma cutDecompositionMatrix_cons (S T : Finset V) (c : ℝ)
    (L : CutDecomposition V) :
    cutDecompositionMatrix ((S, T, c) :: L) =
      cutPiece S T c + cutDecompositionMatrix L := by
  funext i j
  simp [cutDecompositionMatrix]

/-- The explicit profile formula for a rectangle decomposition.  This is the
form used with simultaneous concentration of the finitely many intersection
cardinalities. -/
lemma matrixCutSum_cutDecompositionMatrix (L : CutDecomposition V)
    (X Y : Finset V) :
    matrixCutSum (cutDecompositionMatrix L) X Y =
      (L.map fun q ↦
        ((X ∩ q.1).card : ℝ) * ((Y ∩ q.2.1).card : ℝ) * q.2.2).sum := by
  induction L with
  | nil => simp [cutDecompositionMatrix, matrixCutSum]
  | cons q L ih =>
      obtain ⟨S, T, c⟩ := q
      rw [cutDecompositionMatrix_cons, matrixCutSum_add,
        matrixCutSum_cutPiece_general, ih]
      simp

lemma matrixEnergy_le_card_sq (A : V → V → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    matrixEnergy A ≤ (Fintype.card V : ℝ) ^ 2 := by
  unfold matrixEnergy
  calc
    (∑ i, ∑ j, A i j ^ 2) ≤ ∑ _i : V, ∑ _j : V, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [← sq_abs]
      simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 (hA i j)
    _ = (Fintype.card V : ℝ) ^ 2 := by
      simp
      ring

lemma abs_matrixCutSum_le (A : V → V → ℝ) (S T : Finset V) (M : ℝ)
    (hA : ∀ i ∈ S, ∀ j ∈ T, |A i j| ≤ M) :
    |matrixCutSum A S T| ≤ (S.card * T.card : ℝ) * M := by
  unfold matrixCutSum
  calc
    |∑ i ∈ S, ∑ j ∈ T, A i j| ≤
        ∑ i ∈ S, |∑ j ∈ T, A i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, |A i j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, ∑ _j ∈ T, M := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hA i hi j hj
    _ = (S.card * T.card : ℝ) * M := by
      simp
      ring

/-- The bounded form of the energy-increment lemma.  In addition to cut
regularity, it records a uniform bound on every coefficient.  The factor
`2^k` comes from the elementary pointwise estimate
`|R - c 1_{S×T}| ≤ 2M` when `|R| ≤ M` and `c` is a rectangle average. -/
theorem exists_bounded_cutDecomposition_of_energy_le (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (A : V → V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M)
    (henergy : matrixEnergy A ≤
      (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧
      IsCutRegular ε (A - cutDecompositionMatrix L) ∧
      ∀ q ∈ L, |q.2.2| ≤ (2 : ℝ) ^ k * M := by
  induction k generalizing A M with
  | zero =>
      have hzero : matrixEnergy A = 0 := by
        apply le_antisymm
        · simpa using henergy
        · exact matrixEnergy_nonneg A
      have hAzero : A = 0 := (matrixEnergy_eq_zero_iff A).mp hzero
      refine ⟨[], by simp, ?_, by simp⟩
      subst A
      intro S T
      simp only [cutDecompositionMatrix_nil, sub_self]
      simpa [matrixCutSum] using mul_nonneg hε.le (sq_nonneg (Fintype.card V : ℝ))
  | succ k ih =>
      by_cases hregular : IsCutRegular ε A
      · exact ⟨[], by simp, by simpa using hregular, by simp⟩
      · rw [IsCutRegular] at hregular
        push Not at hregular
        obtain ⟨S, T, hbad⟩ := hregular
        let x : ℝ := matrixCutSum A S T
        let p : ℕ := S.card * T.card
        let c : ℝ := x / (p : ℝ)
        have hthreshold : 0 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
          mul_nonneg hε.le (sq_nonneg _)
        have hxRaw : matrixCutSum A S T ≠ 0 := by
          intro hxzero
          rw [hxzero, abs_zero] at hbad
          exact (not_lt_of_ge hthreshold) hbad
        have hx : x ≠ 0 := by simpa [x] using hxRaw
        have hS : S.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hSempty
          apply hx
          simp [x, hSempty, matrixCutSum]
        have hT : T.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hTempty
          apply hx
          simp [x, hTempty, matrixCutSum]
        have hpNat : 0 < p := Nat.mul_pos hS.card_pos hT.card_pos
        have hp : 0 < (p : ℝ) := by exact_mod_cast hpNat
        have hp_le : (p : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
          have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
          have hTle : T.card ≤ Fintype.card V := Finset.card_le_univ T
          have hSle' : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hSle
          have hTle' : (T.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hTle
          simpa [p, Nat.cast_mul, pow_two] using
            (mul_le_mul hSle' hTle' (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        have hsq : (ε * (Fintype.card V : ℝ) ^ 2) ^ 2 < x ^ 2 := by
          rw [← sq_abs x]
          exact (sq_lt_sq₀ hthreshold (abs_nonneg x)).2 hbad
        have hdrop : ε ^ 2 * (Fintype.card V : ℝ) ^ 2 < x ^ 2 / (p : ℝ) := by
          rw [lt_div_iff₀ hp]
          have hmul : ε ^ 2 * (Fintype.card V : ℝ) ^ 2 * (p : ℝ) ≤
              ε ^ 2 * (Fintype.card V : ℝ) ^ 2 *
                (Fintype.card V : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hp_le
              (mul_nonneg (sq_nonneg ε) (sq_nonneg _))
          nlinarith
        have hc : |c| ≤ M := by
          have hcut : |x| ≤ (p : ℝ) * M := by
            simpa [x, p, Nat.cast_mul] using
              abs_matrixCutSum_le A S T M (fun i _ j _ ↦ hA i j)
          dsimp [c]
          rw [abs_div, abs_of_pos hp]
          exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hcut)
        let A' : V → V → ℝ := A - cutPiece S T c
        have hA' : ∀ i j, |A' i j| ≤ 2 * M := by
          intro i j
          by_cases hij : i ∈ S ∧ j ∈ T
          · simp only [A', Pi.sub_apply, cutPiece, hij]
            calc
              |A i j - c| ≤ |A i j| + |c| := abs_sub _ _
              _ ≤ M + M := add_le_add (hA i j) hc
              _ = 2 * M := by ring
          · simp only [A', Pi.sub_apply, cutPiece, hij, if_false, sub_zero]
            exact (hA i j).trans (by nlinarith)
        have henergy' : matrixEnergy A' ≤
            (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
          have hidentity : matrixEnergy A' =
              matrixEnergy A - x ^ 2 / (p : ℝ) := by
            simpa [A', c, x, p] using matrixEnergy_average_cut A S T hpNat
          rw [hidentity]
          norm_num [Nat.cast_succ] at henergy
          nlinarith
        obtain ⟨L, hLlength, hLregular, hLcoeff⟩ :=
          ih A' (2 * M) (mul_nonneg (by norm_num) hM) hA' henergy'
        refine ⟨(S, T, c) :: L, by simp [hLlength], ?_, ?_⟩
        · have hresidual : A - cutDecompositionMatrix ((S, T, c) :: L) =
              A' - cutDecompositionMatrix L := by
            funext i j
            simp [A', cutDecompositionMatrix]
            ring
          rw [hresidual]
          exact hLregular
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · calc
              |c| ≤ M := hc
              _ ≤ (2 : ℝ) ^ (k + 1) * M := by
                rw [pow_succ]
                have hpow : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
                nlinarith
          · have hqbound := hLcoeff q hq
            calc
              |q.2.2| ≤ (2 : ℝ) ^ k * (2 * M) := hqbound
              _ = (2 : ℝ) ^ (k + 1) * M := by rw [pow_succ]; ring

/-- The energy-increment heart of finite weak regularity.  If the starting
energy has room for `k` increments of size `ε² |V|²`, at most `k` rectangle
pieces suffice to make every residual cut sum small. -/
theorem exists_cutDecomposition_of_energy_le (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (A : V → V → ℝ)
    (henergy : matrixEnergy A ≤
      (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧ IsCutRegular ε (A - cutDecompositionMatrix L) := by
  induction k generalizing A with
  | zero =>
      have hzero : matrixEnergy A = 0 := by
        apply le_antisymm
        · simpa using henergy
        · exact matrixEnergy_nonneg A
      have hA : A = 0 := (matrixEnergy_eq_zero_iff A).mp hzero
      refine ⟨[], by simp, ?_⟩
      subst A
      intro S T
      simp only [cutDecompositionMatrix_nil, sub_self]
      simpa [matrixCutSum] using mul_nonneg hε.le (sq_nonneg (Fintype.card V : ℝ))
  | succ k ih =>
      by_cases hregular : IsCutRegular ε A
      · exact ⟨[], by simp, by simpa using hregular⟩
      · rw [IsCutRegular] at hregular
        push Not at hregular
        obtain ⟨S, T, hbad⟩ := hregular
        let x : ℝ := matrixCutSum A S T
        let p : ℕ := S.card * T.card
        let c : ℝ := x / (p : ℝ)
        have hthreshold : 0 ≤ ε * (Fintype.card V : ℝ) ^ 2 :=
          mul_nonneg hε.le (sq_nonneg _)
        have hxRaw : matrixCutSum A S T ≠ 0 := by
          intro hxzero
          rw [hxzero, abs_zero] at hbad
          exact (not_lt_of_ge hthreshold) hbad
        have hx : x ≠ 0 := by simpa [x] using hxRaw
        have hS : S.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hSempty
          apply hx
          simp [x, hSempty, matrixCutSum]
        have hT : T.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hTempty
          apply hx
          simp [x, hTempty, matrixCutSum]
        have hpNat : 0 < p := by
          exact Nat.mul_pos hS.card_pos hT.card_pos
        have hp : 0 < (p : ℝ) := by exact_mod_cast hpNat
        have hN : 0 < (Fintype.card V : ℝ) := by
          exact_mod_cast (Fintype.card_pos_iff.mpr ⟨hS.choose⟩)
        have hp_le : (p : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
          have hSle : S.card ≤ Fintype.card V := Finset.card_le_univ S
          have hTle : T.card ≤ Fintype.card V := Finset.card_le_univ T
          have hSle' : (S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hSle
          have hTle' : (T.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hTle
          simpa [p, Nat.cast_mul, pow_two] using
            (mul_le_mul hSle' hTle' (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        have hsq : (ε * (Fintype.card V : ℝ) ^ 2) ^ 2 < x ^ 2 := by
          rw [← sq_abs x]
          exact (sq_lt_sq₀ hthreshold (abs_nonneg x)).2 hbad
        have hdrop : ε ^ 2 * (Fintype.card V : ℝ) ^ 2 < x ^ 2 / (p : ℝ) := by
          rw [lt_div_iff₀ hp]
          have hmul : ε ^ 2 * (Fintype.card V : ℝ) ^ 2 * (p : ℝ) ≤
              ε ^ 2 * (Fintype.card V : ℝ) ^ 2 *
                (Fintype.card V : ℝ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hp_le
              (mul_nonneg (sq_nonneg ε) (sq_nonneg _))
          nlinarith
        let A' : V → V → ℝ := A - cutPiece S T c
        have henergy' : matrixEnergy A' ≤
            (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
          have hidentity : matrixEnergy A' =
              matrixEnergy A - x ^ 2 / (p : ℝ) := by
            simpa [A', c, x, p] using matrixEnergy_average_cut A S T hpNat
          rw [hidentity]
          norm_num [Nat.cast_succ] at henergy
          nlinarith
        obtain ⟨L, hLlength, hLregular⟩ := ih A' henergy'
        refine ⟨(S, T, c) :: L, by simp [hLlength], ?_⟩
        have hresidual : A - cutDecompositionMatrix ((S, T, c) :: L) =
            A' - cutDecompositionMatrix L := by
          funext i j
          simp [A', cutDecompositionMatrix]
          ring
        rw [hresidual]
        exact hLregular

/-- Explicit finite Frieze--Kannan weak regularity in rectangle-decomposition
form.  The number of pieces depends only on `ε`: any natural `k` satisfying
`1 ≤ k ε²` works. -/
theorem finite_weak_regularity (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hk : 1 ≤ (k : ℝ) * ε ^ 2) (A : V → V → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧ IsCutRegular ε (A - cutDecompositionMatrix L) := by
  apply exists_cutDecomposition_of_energy_le ε hε k A
  calc
    matrixEnergy A ≤ (Fintype.card V : ℝ) ^ 2 := matrixEnergy_le_card_sq A hA
    _ ≤ (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hk
        (sq_nonneg (Fintype.card V : ℝ))

/-- The total absolute coefficient mass of a rectangle decomposition. -/
noncomputable def cutCoefficientMass (L : CutDecomposition V) : ℝ :=
  (L.map fun q ↦ |q.2.2|).sum

/-- Evaluate a rectangle decomposition on two arbitrary real profiles. -/
noncomputable def cutProfileValue (L : CutDecomposition V)
    (a b : (Finset V × Finset V × ℝ) → ℝ) : ℝ :=
  (L.map fun q ↦ q.2.2 * a q * b q).sum

lemma matrixCutSum_cutDecompositionMatrix_eq_profile
    (L : CutDecomposition V) (X Y : Finset V) :
    matrixCutSum (cutDecompositionMatrix L) X Y =
      cutProfileValue L
        (fun q ↦ ((X ∩ q.1).card : ℝ))
        (fun q ↦ ((Y ∩ q.2.1).card : ℝ)) := by
  rw [matrixCutSum_cutDecompositionMatrix]
  unfold cutProfileValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  ring

lemma cutProfileValue_sub_le (L : CutDecomposition V)
    (a b a' b' : (Finset V × Finset V × ℝ) → ℝ) (E : ℝ) (_hE : 0 ≤ E)
    (hterm : ∀ q ∈ L, |a q * b q - a' q * b' q| ≤ E) :
    |cutProfileValue L a b - cutProfileValue L a' b'| ≤
      cutCoefficientMass L * E := by
  induction L with
  | nil => simp [cutProfileValue, cutCoefficientMass]
  | cons q L ih =>
      have hq := hterm q (by simp)
      have htail : ∀ r ∈ L, |a r * b r - a' r * b' r| ≤ E := by
        intro r hr
        exact hterm r (by simp [hr])
      have hih := ih htail
      calc
        |cutProfileValue (q :: L) a b - cutProfileValue (q :: L) a' b'| =
            |q.2.2 * (a q * b q - a' q * b' q) +
              (cutProfileValue L a b - cutProfileValue L a' b')| := by
                simp [cutProfileValue]
                congr 1
                ring
        _ ≤ |q.2.2 * (a q * b q - a' q * b' q)| +
              |cutProfileValue L a b - cutProfileValue L a' b'| :=
            abs_add_le _ _
        _ = |q.2.2| * |a q * b q - a' q * b' q| +
              |cutProfileValue L a b - cutProfileValue L a' b'| := by
            rw [abs_mul]
        _ ≤ |q.2.2| * E + cutCoefficientMass L * E :=
            add_le_add (mul_le_mul_of_nonneg_left hq (abs_nonneg _)) hih
        _ = cutCoefficientMass (q :: L) * E := by
            simp [cutCoefficientMass]
            ring

/-- A bilinear profile changes by at most `2Nδ` when each of its two factors
changes by at most `δ` and the relevant factors are bounded by `N`. -/
lemma abs_mul_sub_mul_le {a b a' b' N δ : ℝ} (hN : 0 ≤ N) (_hδ : 0 ≤ δ)
    (ha : |a| ≤ N) (hb' : |b'| ≤ N)
    (haa' : |a - a'| ≤ δ) (hbb' : |b - b'| ≤ δ) :
    |a * b - a' * b'| ≤ 2 * N * δ := by
  calc
    |a * b - a' * b'| = |a * (b - b') + b' * (a - a')| := by
      congr 1
      ring
    _ ≤ |a * (b - b')| + |b' * (a - a')| := abs_add_le _ _
    _ = |a| * |b - b'| + |b'| * |a - a'| := by
      rw [abs_mul, abs_mul]
    _ ≤ N * δ + N * δ := by
      exact add_le_add
        (mul_le_mul ha hbb' (abs_nonneg _) hN)
        (mul_le_mul hb' haa' (abs_nonneg _) hN)
    _ = 2 * N * δ := by ring

/-- Profile-density transfer estimate.  The exact cut value of a rectangle
decomposition is within `mass · E` of any profile whose two-factor products
are termwise within `E` of the exact intersection-cardinality products. -/
lemma matrixCutSum_cutDecompositionMatrix_sub_profile_le
    (L : CutDecomposition V) (X Y : Finset V)
    (a b : (Finset V × Finset V × ℝ) → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hterm : ∀ q ∈ L,
      |((X ∩ q.1).card : ℝ) * ((Y ∩ q.2.1).card : ℝ) - a q * b q| ≤ E) :
    |matrixCutSum (cutDecompositionMatrix L) X Y - cutProfileValue L a b| ≤
      cutCoefficientMass L * E := by
  rw [matrixCutSum_cutDecompositionMatrix_eq_profile]
  exact cutProfileValue_sub_le L _ _ a b E hE hterm

/-- Uniform profile-density transfer in the form used after simultaneous
concentration.  The exact intersection factors and the comparison profile
are within `δ`; their relevant magnitudes are at most `N`; and the total
coefficient mass is at most `C`.  The resulting cut-value error is at most
`2 C N δ`. -/
lemma profile_density_transfer_estimate
    (L : CutDecomposition V) (X Y : Finset V)
    (a b : (Finset V × Finset V × ℝ) → ℝ)
    (C N δ : ℝ) (hC : cutCoefficientMass L ≤ C)
    (hN : 0 ≤ N) (hδ : 0 ≤ δ)
    (hXbound : ∀ q ∈ L, |((X ∩ q.1).card : ℝ)| ≤ N)
    (hBbound : ∀ q ∈ L, |b q| ≤ N)
    (hXclose : ∀ q ∈ L, |((X ∩ q.1).card : ℝ) - a q| ≤ δ)
    (hYclose : ∀ q ∈ L, |((Y ∩ q.2.1).card : ℝ) - b q| ≤ δ) :
    |matrixCutSum (cutDecompositionMatrix L) X Y - cutProfileValue L a b| ≤
      C * (2 * N * δ) := by
  have hterm : ∀ q ∈ L,
      |((X ∩ q.1).card : ℝ) * ((Y ∩ q.2.1).card : ℝ) - a q * b q| ≤
        2 * N * δ := by
    intro q hq
    exact abs_mul_sub_mul_le hN hδ
      (hXbound q hq) (hBbound q hq) (hXclose q hq) (hYclose q hq)
  calc
    |matrixCutSum (cutDecompositionMatrix L) X Y - cutProfileValue L a b| ≤
        cutCoefficientMass L * (2 * N * δ) :=
      matrixCutSum_cutDecompositionMatrix_sub_profile_le
        L X Y a b (2 * N * δ) (mul_nonneg (mul_nonneg (by norm_num) hN) hδ) hterm
    _ ≤ C * (2 * N * δ) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg (mul_nonneg (by norm_num) hN) hδ)

lemma cutCoefficientMass_le (L : CutDecomposition V) (B : ℝ)
    (hB : ∀ q ∈ L, |q.2.2| ≤ B) :
    cutCoefficientMass L ≤ (L.length : ℝ) * B := by
  unfold cutCoefficientMass
  calc
    (L.map fun q ↦ |q.2.2|).sum ≤ (L.map fun _q ↦ B).sum := by
      exact List.sum_le_sum hB
    _ = (L.length : ℝ) * B := by simp

/-- Weak regularity with all quantitative data needed for a uniform random
sampling argument.  Both the individual coefficients and their total mass
depend only on `k`, hence only on the chosen regularity tolerance. -/
theorem finite_weak_regularity_bounded (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hk : 1 ≤ (k : ℝ) * ε ^ 2) (A : V → V → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧
      IsCutRegular ε (A - cutDecompositionMatrix L) ∧
      (∀ q ∈ L, |q.2.2| ≤ (2 : ℝ) ^ k) ∧
      cutCoefficientMass L ≤ (k : ℝ) * (2 : ℝ) ^ k := by
  have henergy : matrixEnergy A ≤
      (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
    calc
      matrixEnergy A ≤ (Fintype.card V : ℝ) ^ 2 :=
        matrixEnergy_le_card_sq A hA
      _ ≤ (k : ℝ) * ε ^ 2 * (Fintype.card V : ℝ) ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hk
          (sq_nonneg (Fintype.card V : ℝ))
  obtain ⟨L, hlength, hregular, hcoeff⟩ :=
    exists_bounded_cutDecomposition_of_energy_le ε hε k A 1 (by norm_num) hA henergy
  have hcoeff' : ∀ q ∈ L, |q.2.2| ≤ (2 : ℝ) ^ k := by
    intro q hq
    simpa using hcoeff q hq
  refine ⟨L, hlength, hregular, hcoeff', ?_⟩
  calc
    cutCoefficientMass L ≤ (L.length : ℝ) * (2 : ℝ) ^ k :=
      cutCoefficientMass_le L _ hcoeff'
    _ ≤ (k : ℝ) * (2 : ℝ) ^ k := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlength) (pow_nonneg (by norm_num) _)

/-- Cut-regularity of a difference is exactly the uniform additive estimate
needed to transfer lower bounds between the original and approximating
matrices. -/
lemma cutSum_sub_le_of_isCutRegular {ε : ℝ} {A B : V → V → ℝ}
    (h : IsCutRegular ε (A - B)) (S T : Finset V) :
    matrixCutSum A S T - ε * (Fintype.card V : ℝ) ^ 2 ≤
      matrixCutSum B S T := by
  have habs := h S T
  rw [matrixCutSum_sub] at habs
  have hupper : matrixCutSum A S T - matrixCutSum B S T ≤
      ε * (Fintype.card V : ℝ) ^ 2 := (abs_le.mp habs).2
  linarith

/-- The `0`--`1` adjacency matrix of a finite simple graph.  It is ordered,
so a crossing edge is counted once when the two input sets are disjoint and
an internal edge is counted twice when both inputs are the same set. -/
noncomputable def graphAdjacencyMatrix (G : SimpleGraph V) : V → V → ℝ :=
  fun i j ↦ if G.Adj i j then 1 else 0

lemma abs_graphAdjacencyMatrix_le_one (G : SimpleGraph V) (i j : V) :
    |graphAdjacencyMatrix G i j| ≤ 1 := by
  by_cases h : G.Adj i j <;> simp [graphAdjacencyMatrix, h]

lemma matrixCutSum_graphAdjacencyMatrix (G : SimpleGraph V) (S T : Finset V) :
    matrixCutSum (graphAdjacencyMatrix G) S T =
      ∑ i ∈ S, ∑ j ∈ T, if G.Adj i j then 1 else 0 := by
  rfl

/-- Finite Frieze--Kannan weak regularity specialized to graph adjacency
matrices.  This is the bounded-complexity deterministic input for the
bi-density inheritance argument. -/
theorem finite_graph_weak_regularity (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 1 ≤ (k : ℝ) * ε ^ 2) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧
        IsCutRegular ε
          (graphAdjacencyMatrix G - cutDecompositionMatrix L) := by
  exact finite_weak_regularity ε hε k hk (graphAdjacencyMatrix G)
    (abs_graphAdjacencyMatrix_le_one G)

/-- Graph weak regularity with graph-independent bounds on every coefficient
and on their total absolute mass. -/
theorem finite_graph_weak_regularity_bounded
    (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 1 ≤ (k : ℝ) * ε ^ 2) :
    ∃ L : CutDecomposition V,
      L.length ≤ k ∧
      IsCutRegular ε
        (graphAdjacencyMatrix G - cutDecompositionMatrix L) ∧
      (∀ q ∈ L, |q.2.2| ≤ (2 : ℝ) ^ k) ∧
      cutCoefficientMass L ≤ (k : ℝ) * (2 : ℝ) ^ k := by
  exact finite_weak_regularity_bounded ε hε k hk (graphAdjacencyMatrix G)
    (abs_graphAdjacencyMatrix_le_one G)

end MatrixCuts

end Erdos622
