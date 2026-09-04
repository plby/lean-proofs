/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TypicalChosenLinkCover

/-!
# Uniform scalar sufficient conditions for robust Hall mixing

The normalized second-moment premise is quantified over two arbitrary
subsets.  This file removes the second subset from the numerical work.  If
`M` is the common side size, `s` is the first subset size, and

`M * (D + codegree*s) < s * (d-density)^2`,

then the required strict second-moment inequality follows for every second
subset.  The proof is entirely in natural numbers and explicitly controls
the truncated subtraction in the normalized lower bound.
-/

namespace Erdos207

open Finset

/-- A uniform degree/codegree inequality implies the normalized
second-moment scalar for arbitrary finite subsets of two `M`-element types. -/
theorem normalizedSecondMomentScalar_of_uniform
    (M d D codegree density cutoff : ℕ)
    (hM : 0 < M) (hdensity : density ≤ d)
    (huniform : ∀ s : ℕ, cutoff < s → s ≤ M →
      M * (D + codegree * s) < s * (d - density) ^ 2) :
    ∀ s u : ℕ, s ≤ M → u ≤ M → cutoff < s →
      M ^ 2 * (M - u) *
          (D * s + codegree * s * (s - 1)) <
        (M * d * s - density * s * u) ^ 2 := by
  intro s u hsM huM hcuts
  have hs : 0 < s := by omega
  have hsubterm : D * s + codegree * s * (s - 1) ≤
      s * (D + codegree * s) := by
    have hpred : s - 1 ≤ s := Nat.sub_le s 1
    calc
      D * s + codegree * s * (s - 1) ≤
          D * s + codegree * s * s := by
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_left (codegree * s) hpred) (D * s)
      _ = s * (D + codegree * s) := by ring
  have hleft :
      M ^ 2 * (M - u) * (D * s + codegree * s * (s - 1)) ≤
        M ^ 2 * M * (s * (D + codegree * s)) := by
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left (M ^ 2) (Nat.sub_le M u)) hsubterm
  have huniform' := huniform s hcuts hsM
  have hscalePos : 0 < M ^ 2 * s := by positivity
  have hmiddle : M ^ 2 * M * (s * (D + codegree * s)) <
      (M * (d - density) * s) ^ 2 := by
    have hmul := Nat.mul_lt_mul_of_pos_left huniform' hscalePos
    nlinarith
  have hdu : density * s * u ≤ density * s * M :=
    Nat.mul_le_mul_left (density * s) huM
  have hsubLower : M * (d - density) * s ≤
      M * d * s - density * s * u := by
    calc
      M * (d - density) * s = M * s * (d - density) := by ring
      _ = M * s * d - M * s * density := by
        rw [Nat.mul_sub_left_distrib]
      _ = M * d * s - density * s * M := by ring_nf
      _ ≤ M * d * s - density * s * u :=
        Nat.sub_le_sub_left hdu (M * d * s)
  exact hleft.trans_lt (hmiddle.trans_le (Nat.pow_le_pow_left hsubLower 2))

/-- The preceding scalar simultaneously supplies both oriented subset
inequalities for a balanced bipartite link. -/
theorem balancedLink_secondMomentScalars_of_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : BipartiteLink V) (d D codegree density cutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card)
    (hdensity : density ≤ d)
    (huniform : ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
      K.right.card * (D + codegree * s) <
        s * (d - density) ^ 2) :
    (∀ S : Finset ↥K.left, ∀ U : Finset ↥K.right, cutoff < S.card →
      K.right.card ^ 2 * (K.right.card - U.card) *
          (D * S.card + codegree * S.card * (S.card - 1)) <
        (K.right.card * d * S.card -
          density * S.card * U.card) ^ 2) ∧
    (∀ S : Finset ↥K.right, ∀ U : Finset ↥K.left, cutoff < S.card →
      K.left.card ^ 2 * (K.left.card - U.card) *
          (D * S.card + codegree * S.card * (S.card - 1)) <
        (K.left.card * d * S.card -
          density * S.card * U.card) ^ 2) := by
  have hbase := normalizedSecondMomentScalar_of_uniform K.right.card d D
    codegree density cutoff hpositive hdensity huniform
  constructor
  · intro S U hcut
    exact hbase S.card U.card (by
      simpa [hbalanced] using S.card_le_univ) (by
        simpa using U.card_le_univ) hcut
  · intro S U hcut
    have hbase' := normalizedSecondMomentScalar_of_uniform K.left.card d D
      codegree density cutoff (by simpa [hbalanced] using hpositive)
      hdensity (by
        intro s hs hle
        simpa [hbalanced] using huniform s hs (by simpa [hbalanced] using hle))
    exact hbase' S.card U.card (by
      simpa [hbalanced] using S.card_le_univ) (by
        simpa using U.card_le_univ) hcut

end Erdos207
