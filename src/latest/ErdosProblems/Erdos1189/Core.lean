/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Erdős Problem 1189: foundational definitions and elementary lemmas.

Informal sources:
- Erdős Problem 1189, https://www.erdosproblems.com/1189
- Jeff Pickhardt and Omniscience Research Agent, "Irreducible Covering Sets:
  A Solution of Erdős Problem 1189" (the selected proof claim).

Formal author: OpenAI Codex.
This file does not claim the asymptotic or extremal results in that writeup.
-/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Order.Minimal
import Mathlib.Tactic

namespace Erdos1189

open Finset

/-- A fixed choice of one congruence class for each modulus covers all integers. -/
def Covers (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ z : ℤ, ∃ d ∈ D, z ≡ a d [ZMOD d]

/-- A set of distinct, nontrivial moduli admitting some covering assignment. -/
def IsCoveringSet (D : Finset ℕ) : Prop :=
  (∀ d ∈ D, 1 < d) ∧ ∃ a : ℕ → ℤ, Covers D a

/-- No proper subset admits any covering assignment, including a new assignment. -/
def IsIrreducibleCoveringSet (D : Finset ℕ) : Prop :=
  IsCoveringSet D ∧ ∀ E ⊂ D, ¬ IsCoveringSet E

/-- Minimality of one fixed assignment, a weaker notion than irreducibility. -/
def IsMinimalCoveringSystem (D : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ d ∈ D, 1 < d) ∧ Covers D a ∧ ∀ E ⊂ D, ¬ Covers E a

/-- All divisors except 1, including the number itself. -/
def nontrivialDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (1 < ·)

lemma Covers.mono {D E : Finset ℕ} {a : ℕ → ℤ}
    (h : Covers D a) (hDE : D ⊆ E) : Covers E a := by
  intro z
  obtain ⟨d, hd, hz⟩ := h z
  exact ⟨d, hDE hd, hz⟩

lemma IsCoveringSet.mono {D E : Finset ℕ} (h : IsCoveringSet D)
    (hDE : D ⊆ E) (hE : ∀ d ∈ E, 1 < d) : IsCoveringSet E := by
  obtain ⟨a, ha⟩ := h.2
  exact ⟨hE, a, ha.mono hDE⟩

lemma not_covers_empty (a : ℕ → ℤ) : ¬ Covers ∅ a := by
  intro h
  simpa using h 0

lemma not_isCoveringSet_empty : ¬ IsCoveringSet ∅ := by
  rintro ⟨_, a, ha⟩
  exact not_covers_empty a ha

lemma IsCoveringSet.nonempty {D : Finset ℕ} (h : IsCoveringSet D) : D.Nonempty := by
  obtain ⟨a, ha⟩ := h.2
  obtain ⟨d, hd, _⟩ := ha 0
  exact ⟨d, hd⟩

/-- The immediate lower bound for the largest of `k` distinct nontrivial moduli. -/
lemma IsCoveringSet.card_add_one_le_largest {D : Finset ℕ} (h : IsCoveringSet D) :
    D.card + 1 ≤ D.sup id := by
  have hsub : D ⊆ Icc 2 (D.sup id) := by
    intro d hd
    exact mem_Icc.mpr ⟨h.1 d hd, le_sup (f := id) hd⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  obtain ⟨d, hd⟩ := h.nonempty
  have hmin := h.1 d hd
  have hmax : d ≤ D.sup id := le_sup (f := id) hd
  omega

lemma isIrreducibleCoveringSet_iff_erase (D : Finset ℕ) :
    IsIrreducibleCoveringSet D ↔
      IsCoveringSet D ∧ ∀ d ∈ D, ¬ IsCoveringSet (D.erase d) := by
  constructor
  · rintro ⟨hD, hmin⟩
    exact ⟨hD, fun d hd => hmin _ (erase_ssubset hd)⟩
  · rintro ⟨hD, hmin⟩
    refine ⟨hD, ?_⟩
    intro E hE hcover
    obtain ⟨d, hdD, hdE⟩ := exists_of_ssubset hE
    apply hmin d hdD
    exact hcover.mono (subset_erase.mpr ⟨hE.subset, hdE⟩)
      (fun n hn => hD.1 n (mem_of_mem_erase hn))

lemma IsIrreducibleCoveringSet.minimal_system {D : Finset ℕ}
    (hD : IsIrreducibleCoveringSet D) {a : ℕ → ℤ} (ha : Covers D a) :
    IsMinimalCoveringSystem D a := by
  refine ⟨hD.1.1, ha, ?_⟩
  intro E hE hcover
  exact hD.2 E hE ⟨fun d hd => hD.1.1 d (hE.subset hd), a, hcover⟩

lemma IsCoveringSet.exists_irreducible_subset {D : Finset ℕ} (hD : IsCoveringSet D) :
    ∃ E ⊆ D, IsIrreducibleCoveringSet E := by
  classical
  obtain ⟨E, hED, hE⟩ := exists_minimal_le_of_wellFoundedLT IsCoveringSet D hD
  refine ⟨E, hED, hE.1, ?_⟩
  intro F hF hcover
  exact hF.not_ge (hE.2 hcover hF.subset)

/-- A positive common multiple reduces coverage of all integers to a finite check. -/
lemma covers_iff_finite_period {D : Finset ℕ} {a : ℕ → ℤ} {N : ℕ}
    (hN : 0 < N) (hdiv : ∀ d ∈ D, d ∣ N) :
    Covers D a ↔ ∀ x : Fin N, ∃ d ∈ D, (x : ℕ) ≡ a d [ZMOD d] := by
  refine ⟨fun h x => h x, ?_⟩
  intro h z
  have hpos : (0 : ℤ) < N := by exact_mod_cast hN
  have hnonneg : 0 ≤ z % (N : ℤ) := Int.emod_nonneg _ (ne_of_gt hpos)
  have hlt : (z % (N : ℤ)).toNat < N := by
    have := Int.emod_lt_of_pos z hpos
    omega
  obtain ⟨d, hd, hx⟩ := h ⟨(z % (N : ℤ)).toNat, hlt⟩
  refine ⟨d, hd, ?_⟩
  have hz : z ≡ ((z % (N : ℤ)).toNat : ℤ) [ZMOD N] := by
    rw [Int.toNat_of_nonneg hnonneg]
    exact (Int.mod_modEq z N).symm
  exact (hz.of_dvd (by exact_mod_cast hdiv d hd)).trans hx

/-- The same assignment, with every residue replaced by its canonical representative. -/
lemma covers_normalize_iff (D : Finset ℕ) (a : ℕ → ℤ) :
    Covers D (fun d => a d % (d : ℤ)) ↔ Covers D a := by
  simp only [Covers, Int.ModEq, Int.emod_emod]

end Erdos1189
