/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import UnitFractions.Definitions

/-!
# Exact statement infrastructure for Erdős Problem 294

This file records the literal increasing-sequence formulation, an equivalent
finite-set formulation, the least forbidden denominator, and the fully
quantified Liu--Sawhney asymptotic statement.
-/

open Filter Real
open scoped BigOperators Topology

namespace Erdos294

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `t` is representable at cutoff `N`: a finite set of distinct positive
denominators has minimum `t`, maximum at most `N`, and reciprocal sum one. -/
def Represents (N t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ A : Finset ℕ, t ∈ A ∧
    (∀ n ∈ A, t ≤ n ∧ n ≤ N) ∧ UnitFractions.rec_sum A = 1

/-- The literal increasing-sequence formulation from the problem.  The index
`k` records the number of denominators after the first one. -/
def SequenceRepresents (N t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ (k : ℕ) (n : Fin (k + 1) → ℕ),
    StrictMono n ∧ n 0 = t ∧ (∀ i, n i ≤ N) ∧
      ∑ i, (1 : ℚ) / n i = 1

lemma sequenceRepresents_imp_represents {N t : ℕ} :
    SequenceRepresents N t → Represents N t := by
  rintro ⟨ht, k, n, hn, hn0, hnN, hsum⟩
  let A : Finset ℕ := Finset.univ.image n
  refine ⟨ht, A, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hn0⟩
  · intro m hm
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
    refine ⟨?_, hnN i⟩
    rw [← hn0]
    exact hn.monotone (Fin.zero_le i)
  · rw [UnitFractions.rec_sum]
    dsimp [A]
    rw [Finset.sum_image hn.injective.injOn]
    simpa using hsum

/-- The finset and increasing-sequence formulations are equivalent. -/
lemma represents_imp_sequenceRepresents {N t : ℕ} :
    Represents N t → SequenceRepresents N t := by
  rintro ⟨ht, A, htA, hbounds, hsum⟩
  have hAne : A.Nonempty := ⟨t, htA⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A.card = k + 1 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hAne)
    exact ⟨k, by omega⟩
  let e : Fin (k + 1) ≃o A := A.orderIsoOfFin hk
  let n : Fin (k + 1) → ℕ := fun i => (e i : ℕ)
  refine ⟨ht, k, n, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact_mod_cast e.strictMono hij
  · apply Nat.le_antisymm
    · let a : A := ⟨t, htA⟩
      have hzero : (0 : Fin (k + 1)) ≤ e.symm a := Fin.zero_le _
      have hmono := e.monotone hzero
      have hmono' : (e 0 : ℕ) ≤ (e (e.symm a) : ℕ) := hmono
      change (e 0 : ℕ) ≤ t
      simpa [a] using hmono'
    · exact (hbounds (n 0) (e 0).property).1
  · intro i
    exact (hbounds (n i) (e i).property).2
  · calc
      ∑ i, (1 : ℚ) / n i = ∑ a : A, (1 : ℚ) / (a : ℕ) := by
        exact Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
      _ = UnitFractions.rec_sum A := by
        rw [UnitFractions.rec_sum]
        simpa using
          (Finset.sum_attach A (fun a : ℕ => (1 : ℚ) / a))
      _ = 1 := hsum

theorem sequenceRepresents_iff_represents {N t : ℕ} :
    SequenceRepresents N t ↔ Represents N t :=
  ⟨sequenceRepresents_imp_represents, represents_imp_sequenceRepresents⟩

lemma exists_positive_not_represents (N : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧ ¬ Represents N t := by
  refine ⟨N + 1, Nat.succ_le_succ (Nat.zero_le N), ?_⟩
  rintro ⟨-, A, htA, hbounds, -⟩
  exact (Nat.not_succ_le_self N) (hbounds (N + 1) htA).2

/-- The least positive integer which is not representable at cutoff `N`. -/
def firstForbidden (N : ℕ) : ℕ :=
  Nat.find (exists_positive_not_represents N)

lemma firstForbidden_spec (N : ℕ) :
    1 ≤ firstForbidden N ∧ ¬ Represents N (firstForbidden N) :=
  Nat.find_spec (exists_positive_not_represents N)

lemma firstForbidden_pos (N : ℕ) : 0 < firstForbidden N :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (firstForbidden_spec N).1

lemma not_represents_firstForbidden (N : ℕ) :
    ¬ Represents N (firstForbidden N) :=
  (firstForbidden_spec N).2

lemma represents_of_pos_of_lt_firstForbidden {N t : ℕ}
    (ht : 1 ≤ t) (hlt : t < firstForbidden N) : Represents N t := by
  by_contra hrep
  have hleast : firstForbidden N ≤ t :=
    Nat.find_min' (exists_positive_not_represents N) ⟨ht, hrep⟩
  omega

/-- The real lower comparison profile, with an explicit exponent replacing
the source's `(log log log N)^O(1)`. -/
def lowerProfile (k : ℕ) (N : ℕ) : ℝ :=
  (N : ℝ) /
    (log (N : ℝ) * (log (log (N : ℝ))) ^ 3 *
      (log (log (log (N : ℝ)))) ^ k)

/-- The real upper comparison profile `N / log N`. -/
def upperProfile (N : ℕ) : ℝ :=
  (N : ℝ) / log (N : ℝ)

/-- Fully quantified form of the Liu--Sawhney resolution. -/
def Resolution : Prop :=
  ∃ (k : ℕ) (c C : ℝ), 0 < c ∧ 0 < C ∧
    ∀ᶠ N : ℕ in atTop,
      c * lowerProfile k N ≤ firstForbidden N ∧
        (firstForbidden N : ℝ) ≤ C * upperProfile N

end

end Erdos294
