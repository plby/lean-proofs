/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

open scoped BigOperators Topology

variable {α : Type*} [AddCommMonoid α]

/-- A set is an arithmetic progression of length `l`, first term `a`, and
difference `d`. Cardinality is included so repeated terms are not nontrivial. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length `l`. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

theorem card {s : Set α} {l : ℕ∞} (h : s.IsAPOfLength l) : ENat.card s = l :=
  h.choose_spec.choose_spec.1

end Set.IsAPOfLength

/-- A set is free of nontrivial arithmetic progressions of length `l`. -/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

namespace Set.IsAPOfLengthFree

/-- The largest cardinality of a `k`-AP-free subset of `{1, ..., N}`. -/
noncomputable def maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}

end Set.IsAPOfLengthFree

namespace SzemeredisTheorem

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

private def candidateCards (k N : ℕ) : Set ℕ :=
  {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}

private lemma empty_isAPOfLengthFree (k : ℕ) :
    (∅ : Set ℕ).IsAPOfLengthFree k := by
  intro t ht hAP
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht
  subst t
  have hk0 : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  have hk0' : k = 0 := by exact_mod_cast hk0
  subst k
  simp

private lemma candidateCards_nonempty (k N : ℕ) :
    (candidateCards k N).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨∅, by simp, by simpa using empty_isAPOfLengthFree k, rfl⟩

private lemma candidateCards_bddAbove (k N : ℕ) :
    BddAbove (candidateCards k N) := by
  refine ⟨N, ?_⟩
  rintro n ⟨S, hS, -, rfl⟩
  exact (Finset.card_mono hS).trans_eq (by simp)

/-- The supremum in `maxCard` is attained by an AP-free subset. -/
theorem exists_maxCard_witness (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      (S : Set ℕ).IsAPOfLengthFree k ∧ S.card = r k N := by
  have hm := Nat.sSup_mem (candidateCards_nonempty k N)
    (candidateCards_bddAbove k N)
  change r k N ∈ candidateCards k N at hm
  rcases hm with ⟨S, hS, hfree, hcard⟩
  exact ⟨S, hS, hfree, hcard⟩

/-- The finitary density form of Szemerédi's theorem. -/
def FinitarySzemeredi (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → δ * (N : ℝ) ≤ (A.card : ℝ) →
        ¬(A : Set ℕ).IsAPOfLengthFree k

private lemma arithmeticProgressionSet_card
    (a d k : ℕ) (hd : 0 < d) :
    ENat.card {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} = k := by
  let f : ℕ → ℕ := fun i ↦ a + i * d
  have hf : Function.Injective f := by
    apply StrictMono.injective
    apply strictMono_nat_of_lt_succ
    intro i
    dsimp [f]
    nlinarith
  have hset : {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} =
      f '' {i : ℕ | i < k} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [hset]
  simp only [ENat.card_coe_set_eq, hf.encard_image, Set.Nat.encard_range]

/-- A positive-difference parameter progression has the exact set/cardinality
form used by the Formal Conjectures specification. -/
theorem arithmeticProgressionSet_isAP
    (a d k : ℕ) (hd : 0 < d) :
    Set.IsAPOfLength
      {x : ℕ | ∃ i : ℕ, i < k ∧ x = a + i * d} (k : ℕ∞) := by
  refine ⟨a, d, arithmeticProgressionSet_card a d k hd, ?_⟩
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by exact_mod_cast hi, by simp⟩

/-- A parameterized positive-step progression witnesses non-freeness. -/
theorem not_isAPOfLengthFree_of_parameters {A : Set ℕ} {k a d : ℕ}
    (hk : 1 < k) (hd : 0 < d)
    (hmem : ∀ i < k, a + i * d ∈ A) :
    ¬A.IsAPOfLengthFree k := by
  intro hfree
  let t : Set ℕ := {x | ∃ i : ℕ, i < k ∧ x = a + i * d}
  have ht : t ⊆ A := by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact hmem i hi
  have hAP : t.IsAPOfLength k := arithmeticProgressionSet_isAP a d k hd
  have hle := hfree t ht hAP
  have hnle : ¬(k : ℕ∞) ≤ 1 := by exact_mod_cast (not_le.mpr hk)
  exact hnle hle

/-- A finitary density theorem implies the Formal Conjectures extremal limit. -/
theorem tendsto_maxCard_div_of_finitarySzemeredi {k : ℕ}
    (hSz : FinitarySzemeredi k) :
    Filter.Tendsto (fun N => (r k N / N : ℝ)) Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀, hSz⟩ := hSz ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hNpos : 0 < N := hN₀.trans_le hN
  obtain ⟨S, hS, hfree, hcard⟩ := exists_maxCard_witness k N
  have hlt : (S.card : ℝ) < ε * (N : ℝ) := by
    rw [lt_iff_not_ge]
    intro hdense
    exact (hSz N hN S hS hdense) hfree
  have hratio : (r k N : ℝ) / (N : ℝ) < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < N), ← hcard]
    exact hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg]
  · exact hratio
  · positivity

end SzemeredisTheorem
