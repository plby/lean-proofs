/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 231, finite disproof.
Informal authors: Nicolaas Govert de Bruijn, Paul Erdős (as credited by EPC).
Formal author: AxiomProver. Published by Axiom Math.
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos231/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos231

/-! # Erdős Problem 231 (Disproof)

The conjecture asserts: for every positive integer `k` and every word `S` of
length `2^k - 1` over an alphabet of size `k`, the word `S` contains an
abelian square. We disprove this by exhibiting an abelian-square-free word of
length 15 over `Fin 4`. -/

def IsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ u v : List α, u ≠ [] ∧ v ≠ [] ∧ u.length = v.length ∧ u.Perm v ∧ w = u ++ v

def isAbelianSquare {α : Type*} [DecidableEq α] (w : List α) : Bool :=
  w.length % 2 == 0 ∧ w.length / 2 ≥ 1 ∧ (w.take (w.length / 2)).Perm (w.drop (w.length / 2))

def ContainsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ i len : ℕ, 2 ≤ len ∧ i + len ≤ w.length ∧
    IsAbelianSquare ((w.drop i).take len)

def containsAbelianSquare {α : Type*} [DecidableEq α] (w : List α) : Bool :=
  (List.range w.length).any fun i =>
    (List.range ((w.length - i) / 2)).any fun m =>
      isAbelianSquare ((w.drop i).take (2 * (m + 1)))

def IsAbelianSquareFree {α : Type*} (w : List α) : Prop :=
  ¬ContainsAbelianSquare w

/-- `isAbelianSquare` correctly decides `IsAbelianSquare`. -/
theorem isAbelianSquare_iff {α : Type*} [DecidableEq α] (w : List α) :
    isAbelianSquare w = true ↔ IsAbelianSquare w := by
  refine ⟨fun h => ?_, fun ⟨u, v, hu, _, hlen, hperm, hw⟩ => ?_⟩
  · simp only [isAbelianSquare, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hmod, hge, hperm⟩ := h
    refine ⟨w.take (w.length / 2), w.drop (w.length / 2), ?_, ?_, ?_, hperm,
      (List.take_append_drop (w.length / 2) w).symm⟩
    · simp [← List.length_eq_zero_iff, List.length_take]
      omega
    · simp [← List.length_eq_zero_iff, List.length_drop]
      omega
    · simp [List.length_take, List.length_drop]
      omega
  · subst hw
    have h_len : (u ++ v).length = 2 * u.length := by
      rw [List.length_append, ← hlen, two_mul]
    have h_pos : 1 ≤ u.length := List.length_pos_iff.mpr hu
    simp [isAbelianSquare, h_len, h_pos, hperm]

/-- `containsAbelianSquare` correctly decides `ContainsAbelianSquare`. -/
theorem containsAbelianSquare_iff {α : Type*} [DecidableEq α] (w : List α) :
    containsAbelianSquare w = true ↔ ContainsAbelianSquare w := by
  unfold containsAbelianSquare
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨fun ⟨i, hi, m, hm, hsq⟩ => ⟨i, 2 * (m + 1), by omega, by omega,
    (isAbelianSquare_iff _).mp hsq⟩, fun ⟨i, len, hlen, hbound, hsq⟩ => ?_⟩
  have hbool : isAbelianSquare ((w.drop i).take len) = true := (isAbelianSquare_iff _).mpr hsq
  have hlen_eq : ((w.drop i).take len).length = len := by
    rw [List.length_take, List.length_drop]
    omega
  have heven : len % 2 = 0 := by
    simp only [isAbelianSquare, beq_iff_eq, decide_eq_true_eq, hlen_eq] at hbool
    exact hbool.1
  refine ⟨i, by omega, len / 2 - 1, by omega, ?_⟩
  rw [show 2 * (len / 2 - 1 + 1) = len by omega]
  exact hbool

/-- **Explicit witness for k = 4.** The word
`[0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]` over `Fin 4` has length 15
and is abelian-square-free. -/
theorem erdos_problem_231_k4 :
    let S : List (Fin 4) := [0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 1, 0, 1]
    S.length = 2 ^ 4 - 1 ∧ IsAbelianSquareFree S :=
  ⟨rfl, fun hcontra => absurd ((containsAbelianSquare_iff _).mpr hcontra) (by decide)⟩

/-- **Erdős Problem 231 (Disproof).** -/
theorem erdos_problem_231_disproof :
    ∃ k : ℕ, 0 < k ∧ ∃ S : List (Fin k),
      S.length = 2 ^ k - 1 ∧ IsAbelianSquareFree S :=
  ⟨4, by norm_num, _, erdos_problem_231_k4.1, erdos_problem_231_k4.2⟩

end Erdos231
