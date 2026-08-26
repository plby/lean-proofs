/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Refinement along a dense ω-closed subset of a complete Boolean algebra: deciding countably many
Boolean values / choices simultaneously on a nonzero piece.
-/
import ErdosProblems.Erdos501.Flypitch4.ForcingCH
import ErdosProblems.Erdos501.Flypitch4.Erdos501.Semantics

set_option relaxedAutoImplicit true

/-!
# ω-closed refinement

Let `D ⊆ 𝔹` be a dense ω-closed subset of a nontrivial complete Boolean algebra
(`Flypitch.DenseOmegaClosed`), e.g. the principal opens of the collapse algebra `𝔹_collapse`
(`Flypitch.principalOpens_denseOmegaClosed`).  Then countably many "choices" can be made
simultaneously below any nonzero `Γ`: given, for every `n`, a family `φ n : ι n → 𝔹` such that
every nonzero `Γ' ≤ Γ` is compatible with some `φ n i`, there are a nonzero `Γ' ≤ Γ` and choices
`c n` with `Γ' ≤ φ n (c n)` for **all** `n` (`exists_forall_of_denseOmegaClosed`).  This is the
external form of the (ω, ∞)-distributivity of `𝔹_collapse` ("no new ω-sequences"), and it is the
only property of the collapse algebra used in `CheckReals.lean` and `Hechler.lean`.

Special cases: deciding a sequence of Boolean values (`exists_decide_of_denseOmegaClosed`), and
choosing witnesses of a sequence of suprema (`exists_witness_of_denseOmegaClosed`).
-/

open Flypitch

namespace Flypitch.Erdos501

universe u

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

/-- Density: below every nonzero element there is a nonzero element of `D`. -/
lemma exists_mem_D_le {D : Set 𝔹} (hD : DenseOmegaClosed D) {b : 𝔹} (hb : ⊥ < b) :
    ∃ d ∈ D, d ≤ b ∧ ⊥ < d := by
  obtain ⟨d, hdD, hdb⟩ := hD.1.2 b hb
  exact ⟨d, hdD, hdb, nonzero_of_mem_DenseOmegaClosed hD hdD⟩

/-- Every nonzero element compatible with a supremum is compatible with one of its terms. -/
lemma exists_bot_lt_inf_of_le_iSup {ι : Type*} {s : ι → 𝔹} {Γ : 𝔹} (hΓ : ⊥ < Γ)
    (h : Γ ≤ ⨆ i, s i) : ∃ i, ⊥ < Γ ⊓ s i :=
  nonzero_inf_of_nonzero_le_supr hΓ h

section Chain

/-- The state of the recursion: a nonzero element of `D` below `Γ`. -/
private abbrev State (D : Set 𝔹) (Γ : 𝔹) : Type u := {x : 𝔹 // x ∈ D ∧ ⊥ < x ∧ x ≤ Γ}

variable {D : Set 𝔹} {Γ : 𝔹} {ι : ℕ → Type*}

private lemma exists_next (hD : DenseOmegaClosed D) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) (p : State D Γ) :
    ∃ q : ι n × State D Γ, q.2.1 ≤ p.1 ⊓ φ n q.1 := by
  obtain ⟨i, hi⟩ := hφ n p.1 p.2.2.1 p.2.2.2
  obtain ⟨d, hdD, hdle, hdpos⟩ := exists_mem_D_le hD hi
  exact ⟨(i, ⟨d, hdD, hdpos, hdle.trans (inf_le_left.trans p.2.2.2)⟩), hdle⟩

private lemma exists_start (hD : DenseOmegaClosed D) (hΓ : ⊥ < Γ) :
    ∃ _p : State D Γ, True := by
  obtain ⟨d, hdD, hdle, hdpos⟩ := exists_mem_D_le hD hΓ
  exact ⟨⟨d, hdD, hdpos, hdle⟩, trivial⟩

/-- One step of the recursion. -/
private noncomputable def step (hD : DenseOmegaClosed D) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) (p : State D Γ) :
    ι n × State D Γ :=
  Classical.choose (exists_next hD φ hφ n p)

private lemma step_spec (hD : DenseOmegaClosed D) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) (p : State D Γ) :
    (step hD φ hφ n p).2.1 ≤ p.1 ⊓ φ n (step hD φ hφ n p).1 :=
  Classical.choose_spec (exists_next hD φ hφ n p)

/-- The chain of pieces. -/
private noncomputable def chain (hD : DenseOmegaClosed D) (hΓ : ⊥ < Γ) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) : State D Γ :=
  Nat.rec (Classical.choose (exists_start hD hΓ)) (fun n p => (step hD φ hφ n p).2) n

/-- The `n`-th choice. -/
private noncomputable def choice (hD : DenseOmegaClosed D) (hΓ : ⊥ < Γ) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) : ι n :=
  (step hD φ hφ n (chain hD hΓ φ hφ n)).1

private lemma chain_succ_le (hD : DenseOmegaClosed D) (hΓ : ⊥ < Γ) (φ : ∀ n, ι n → 𝔹)
    (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) (n : ℕ) :
    (chain hD hΓ φ hφ (n + 1)).1 ≤ (chain hD hΓ φ hφ n).1 ⊓ φ n (choice hD hΓ φ hφ n) :=
  step_spec hD φ hφ n (chain hD hΓ φ hφ n)

/-- **ω-closed refinement.**  Countably many choices can be made simultaneously below `Γ`. -/
theorem exists_forall_of_denseOmegaClosed (hD : DenseOmegaClosed D) (hΓ : ⊥ < Γ)
    (φ : ∀ n, ι n → 𝔹) (hφ : ∀ n (Γ' : 𝔹), ⊥ < Γ' → Γ' ≤ Γ → ∃ i, ⊥ < Γ' ⊓ φ n i) :
    ∃ (Γ' : 𝔹) (c : ∀ n, ι n), ⊥ < Γ' ∧ Γ' ≤ Γ ∧ ∀ n, Γ' ≤ φ n (c n) := by
  let s : ℕ → 𝔹 := fun n => (chain hD hΓ φ hφ n).1
  have hmem : ∀ n, s n ∈ D := fun n => (chain hD hΓ φ hφ n).2.1
  have hchain : ∀ n, s (n + 1) ≤ s n := fun n =>
    (chain_succ_le hD hΓ φ hφ n).trans inf_le_left
  have hpos : ⊥ < ⨅ n, s n := nonzero_iInf_of_mem_DenseOmegaClosed hD hchain hmem
  refine ⟨⨅ n, s n, choice hD hΓ φ hφ, hpos, ?_, ?_⟩
  · exact (iInf_le s 0).trans (chain hD hΓ φ hφ 0).2.2.2
  · intro n
    exact (iInf_le s (n + 1)).trans ((chain_succ_le hD hΓ φ hφ n).trans inf_le_right)

end Chain

/-- Deciding a sequence of Boolean values on a nonzero piece. -/
theorem exists_decide_of_denseOmegaClosed {D : Set 𝔹} (hD : DenseOmegaClosed D) {Γ : 𝔹}
    (hΓ : ⊥ < Γ) (b : ℕ → 𝔹) :
    ∃ (Γ' : 𝔹) (c : ℕ → Bool), ⊥ < Γ' ∧ Γ' ≤ Γ ∧
      ∀ n, (c n = true → Γ' ≤ b n) ∧ (c n = false → Γ' ≤ (b n)ᶜ) := by
  obtain ⟨Γ', c, hΓ', hle, hc⟩ := exists_forall_of_denseOmegaClosed hD hΓ
    (ι := fun _ => Bool) (fun n i => if i then b n else (b n)ᶜ) (by
      intro n Γ'' hΓ'' _
      by_cases h : ⊥ < Γ'' ⊓ b n
      · exact ⟨true, by simpa using h⟩
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [bot_lt_iff_ne_bot] at hΓ'' ⊢
        intro h'
        apply hΓ''
        rw [bot_lt_iff_ne_bot, not_not] at h
        have := sup_le (le_of_eq h) (le_of_eq h')
        rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq] at this
        exact le_bot_iff.1 this)
  refine ⟨Γ', c, hΓ', hle, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := hc n; rw [h] at this; simpa using this
  · have := hc n; rw [h] at this; simpa using this

/-- Choosing witnesses for a sequence of suprema on a nonzero piece. -/
theorem exists_witness_of_denseOmegaClosed {D : Set 𝔹} (hD : DenseOmegaClosed D) {Γ : 𝔹}
    (hΓ : ⊥ < Γ) {ι : ℕ → Type*} (φ : ∀ n, ι n → 𝔹) (h : ∀ n, Γ ≤ ⨆ i, φ n i) :
    ∃ (Γ' : 𝔹) (c : ∀ n, ι n), ⊥ < Γ' ∧ Γ' ≤ Γ ∧ ∀ n, Γ' ≤ φ n (c n) :=
  exists_forall_of_denseOmegaClosed hD hΓ φ fun n _ hΓ' hle =>
    exists_bot_lt_inf_of_le_iSup hΓ' (hle.trans (h n))

/-! ### The collapse algebra -/

namespace Collapse

open collapse_algebra

/-- The dense ω-closed subset of `𝔹_collapse`: the principal opens of the collapse poset. -/
noncomputable def D_col : Set (𝔹_collapse : Type) :=
  Set.range (@collapseInclusion (pSet_aleph1 : PSet.{0}).Type
    (PSet.powerset PSet.omega : PSet.{0}).Type)

theorem denseOmegaClosed_D_col : DenseOmegaClosed (D_col : Set 𝔹_collapse) :=
  principalOpens_denseOmegaClosed

end Collapse

end Flypitch.Erdos501
