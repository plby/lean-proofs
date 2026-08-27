/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformExtensionWeight

/-!
# Weighted bounds for exact absorber-bank classes

Filtering an exact class by a further outside root is the same counting
problem with that root adjoined.  This observation lets the bounded-span
estimate control every rooted uniform extension weight, including the
distinguished-triangle classes in the nonlocal branch of A2.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- Adding a further root to an exact class only shrinks it into the exact
class with the enlarged prescribed outside root. -/
theorem familyExtensions_exactBankOutsideExtensions_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K A : TripleSystemOn V) :
    familyExtensions (exactBankOutsideExtensions r j B R K) A ⊆
      exactBankOutsideExtensions r j B (R ∪ A) K := by
  intro S hS
  obtain ⟨hSexact, hAS⟩ := mem_familyExtensions_iff.mp hS
  obtain ⟨hcard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hSexact
  apply mem_exactBankOutsideExtensions_iff.mpr
  exact ⟨hcard, union_subset hRS hAS, E, hE, hEout, hEin⟩

/-- In a nonempty exact extension class the enlarged outside root is
disjoint from the fixed bank part, whose size is exactly `r-j`. -/
theorem exactBank_enlarged_root_union_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 2 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty) :
    ((R ∪ A) ∪ K).card = (R ∪ A).card + (r - j) := by
  obtain ⟨S, hS⟩ := hne
  have hSenlarged :
      S ∈ exactBankOutsideExtensions r j B (R ∪ A) K :=
    familyExtensions_exactBankOutsideExtensions_subset r j B R K A hS
  rw [exactBankOutsideExtensions_root_union_card hSenlarged,
    exactBankOutsideExtensions_bank_card hr hj hjr hSenlarged]

/-- If the old and newly prescribed outside roots are disjoint, the exact
root size separates into the three expected summands. -/
theorem exactBank_enlarged_root_union_card_of_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 2 ≤ r) (hj : 2 ≤ j) (hjr : j ≤ r)
    (hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty)
    (hRA : Disjoint R A) :
    ((R ∪ A) ∪ K).card = R.card + A.card + (r - j) := by
  rw [exactBank_enlarged_root_union_card hr hj hjr hne,
    card_union_of_disjoint hRA]

/-- Cardinal form of the enlarged-root bounded-span estimate. -/
theorem card_familyExtensions_exactBankOutsideExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V} (hr : 5 ≤ r) :
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
      2 ^ (r ^ 3) *
        ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
          (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn ((R ∪ A) ∪ K)).card))) := by
  calc
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
        (exactBankOutsideExtensions r j B (R ∪ A) K).card :=
      card_le_card
        (familyExtensions_exactBankOutsideExtensions_subset r j B R K A)
    _ ≤ _ := card_exactBankOutsideExtensions_le hr

/-- Minimality simplifies the enlarged-root count to the strong polynomial
degree `r - (|root|+3)` whenever the root is in the interior range. -/
theorem card_familyExtensions_exactBankOutsideExtensions_le_strong
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r)
    (hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty)
    (hroot2 : 2 ≤ ((R ∪ A) ∪ K).card)
    (hrootsmall : ((R ∪ A) ∪ K).card ≤ r - 3) :
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
      (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^ (r - (((R ∪ A) ∪ K).card + 3)) := by
  obtain ⟨S, hS⟩ := hne
  have hSenlarged :
      S ∈ exactBankOutsideExtensions r j B (R ∪ A) K :=
    familyExtensions_exactBankOutsideExtensions_subset r j B R K A hS
  have hspan : ((R ∪ A) ∪ K).card + 3 ≤
      (verticesOn ((R ∪ A) ∪ K)).card :=
    exactBankOutsideExtensions_root_span hroot2 hrootsmall hSenlarged
  have hbase :
      (univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1 ≤
        Fintype.card V + 1 := by
    simpa using Nat.add_le_add_right
      (card_le_card (sdiff_subset :
        (univ \ verticesOn ((R ∪ A) ∪ K) : Finset V) ⊆ univ)) 1
  have hexp :
      r - (verticesOn ((R ∪ A) ∪ K)).card ≤
        r - (((R ∪ A) ∪ K).card + 3) := by omega
  have hpow :
      ((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
          (r - (verticesOn ((R ∪ A) ∪ K)).card) ≤
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 3)) := by
    calc
      ((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
          (r - (verticesOn ((R ∪ A) ∪ K)).card) ≤
          (Fintype.card V + 1) ^
            (r - (verticesOn ((R ∪ A) ∪ K)).card) :=
        pow_le_pow_left₀ zero_le hbase _
      _ ≤ (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 3)) :=
        pow_le_pow_right₀ (by omega) hexp
  calc
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
        2 ^ (r ^ 3) *
          ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
            (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
              (r - (verticesOn ((R ∪ A) ∪ K)).card))) :=
      card_familyExtensions_exactBankOutsideExtensions_le hr
    _ ≤ 2 ^ (r ^ 3) * ((r + 1) *
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 3))) := by
      gcongr
      omega
    _ = (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 3)) := by
      simp only [mul_assoc]

/-- Endpoint version of the preceding estimate, using the universal weak
minimality exponent `|root|+2`. -/
theorem card_familyExtensions_exactBankOutsideExtensions_le_weak
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V}
    (hr : 5 ≤ r)
    (hne : (familyExtensions
      (exactBankOutsideExtensions r j B R K) A).Nonempty)
    (hroot : 1 ≤ ((R ∪ A) ∪ K).card) :
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
      (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^ (r - (((R ∪ A) ∪ K).card + 2)) := by
  obtain ⟨S, hS⟩ := hne
  have hSenlarged :
      S ∈ exactBankOutsideExtensions r j B (R ∪ A) K :=
    familyExtensions_exactBankOutsideExtensions_subset r j B R K A hS
  have hspan : ((R ∪ A) ∪ K).card + 2 ≤
      (verticesOn ((R ∪ A) ∪ K)).card :=
    exactBankOutsideExtensions_root_span_weak hr hroot hSenlarged
  have hbase :
      (univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1 ≤
        Fintype.card V + 1 := by
    simpa using Nat.add_le_add_right
      (card_le_card (sdiff_subset :
        (univ \ verticesOn ((R ∪ A) ∪ K) : Finset V) ⊆ univ)) 1
  have hexp :
      r - (verticesOn ((R ∪ A) ∪ K)).card ≤
        r - (((R ∪ A) ∪ K).card + 2) := by omega
  have hpow :
      ((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
          (r - (verticesOn ((R ∪ A) ∪ K)).card) ≤
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 2)) := by
    calc
      ((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
          (r - (verticesOn ((R ∪ A) ∪ K)).card) ≤
          (Fintype.card V + 1) ^
            (r - (verticesOn ((R ∪ A) ∪ K)).card) :=
        pow_le_pow_left₀ zero_le hbase _
      _ ≤ (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 2)) :=
        pow_le_pow_right₀ (by omega) hexp
  calc
    (familyExtensions (exactBankOutsideExtensions r j B R K) A).card ≤
        2 ^ (r ^ 3) *
          ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
            (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
              (r - (verticesOn ((R ∪ A) ∪ K)).card))) :=
      card_familyExtensions_exactBankOutsideExtensions_le hr
    _ ≤ 2 ^ (r ^ 3) * ((r + 1) *
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 2))) := by
      gcongr
      omega
    _ = (2 ^ (r ^ 3) * (r + 1)) *
        (Fintype.card V + 1) ^
          (r - (((R ∪ A) ∪ K).card + 2)) := by
      simp only [mul_assoc]

/-- Every uniform rooted extension weight of one exact bank class is bounded
by the explicit enlarged-root polynomial count. -/
theorem extensionWeight_exactBankOutsideExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V} (hr : 5 ≤ r) (p : ℝ≥0) :
    extensionWeight
        (fun S : exactBankOutsideExtensions r j B R K ↦ S.1)
        (constantTripleWeight p) A ≤
      (2 ^ (r ^ 3) *
        ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
          (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn ((R ∪ A) ∪ K)).card))) : ℕ) *
        p ^ (j - 2 - A.card) := by
  rw [extensionWeight_exactBankOutsideExtensions]
  have hcard :
      ((familyExtensions
        (exactBankOutsideExtensions r j B R K) A).card : ℝ≥0) ≤
        (2 ^ (r ^ 3) *
          ((r - (verticesOn ((R ∪ A) ∪ K)).card + 1) *
            (((univ \ verticesOn ((R ∪ A) ∪ K) : Finset V).card + 1) ^
              (r - (verticesOn ((R ∪ A) ∪ K)).card))) : ℕ) := by
    exact_mod_cast
      card_familyExtensions_exactBankOutsideExtensions_le
        (r := r) (j := j) (B := B) (R := R) (K := K) (A := A) hr
  simpa only [mul_comm] using
    mul_le_mul_right hcard (p ^ (j - 2 - A.card))

/-- A distinguished-triangle class filtered by a further root embeds in the
generic exact class rooted at the original root, the further root, and the
distinguished triangle. -/
theorem familyExtensions_exactBankOutsideExtensionsThrough_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K A : TripleSystemOn V) (T : TripleOn V) :
    familyExtensions (exactBankOutsideExtensionsThrough r j B R K T) A ⊆
      exactBankOutsideExtensions r j B (insert T (R ∪ A)) K := by
  intro S hS
  obtain ⟨hSThrough, hAS⟩ := mem_familyExtensions_iff.mp hS
  obtain ⟨hSexact, hTS, _hTR⟩ :=
    mem_exactBankOutsideExtensionsThrough_iff.mp hSThrough
  obtain ⟨hcard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hSexact
  apply mem_exactBankOutsideExtensions_iff.mpr
  refine ⟨hcard, ?_, E, hE, hEout, hEin⟩
  exact insert_subset hTS (union_subset hRS hAS)

/-- A distinguished class is also contained in the generic exact extension
family whose original root has been enlarged by the distinguished triangle. -/
theorem familyExtensions_exactBankOutsideExtensionsThrough_subset_extensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (r j : ℕ) (B R K A : TripleSystemOn V) (T : TripleOn V) :
    familyExtensions (exactBankOutsideExtensionsThrough r j B R K T) A ⊆
      familyExtensions (exactBankOutsideExtensions r j B (insert T R) K) A := by
  intro S hS
  obtain ⟨hSThrough, hAS⟩ := mem_familyExtensions_iff.mp hS
  obtain ⟨hSexact, hTS, _hTR⟩ :=
    mem_exactBankOutsideExtensionsThrough_iff.mp hSThrough
  obtain ⟨hcard, hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hSexact
  apply mem_familyExtensions_iff.mpr
  refine ⟨mem_exactBankOutsideExtensions_iff.mpr ?_, hAS⟩
  exact ⟨hcard, insert_subset hTS hRS, E, hE, hEout, hEin⟩

/-- Cardinal bound for a distinguished-triangle class after an arbitrary
further root has been prescribed. -/
theorem card_familyExtensions_exactBankOutsideExtensionsThrough_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) :
    (familyExtensions
        (exactBankOutsideExtensionsThrough r j B R K T) A).card ≤
      2 ^ (r ^ 3) *
        ((r - (verticesOn (insert T (R ∪ A) ∪ K)).card + 1) *
          (((univ \ verticesOn (insert T (R ∪ A) ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn (insert T (R ∪ A) ∪ K)).card))) := by
  calc
    (familyExtensions
        (exactBankOutsideExtensionsThrough r j B R K T) A).card ≤
        (exactBankOutsideExtensions r j B (insert T (R ∪ A)) K).card :=
      card_le_card
        (familyExtensions_exactBankOutsideExtensionsThrough_subset
          r j B R K A T)
    _ ≤ _ := card_exactBankOutsideExtensions_le hr

/-- Uniform-weight form of the distinguished-triangle enlarged-root bound. -/
theorem extensionWeight_exactBankOutsideExtensionsThrough_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {r j : ℕ} {B R K A : TripleSystemOn V} {T : TripleOn V}
    (hr : 5 ≤ r) (p : ℝ≥0) :
    extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (constantTripleWeight p) A ≤
      (2 ^ (r ^ 3) *
        ((r - (verticesOn (insert T (R ∪ A) ∪ K)).card + 1) *
          (((univ \ verticesOn (insert T (R ∪ A) ∪ K) : Finset V).card + 1) ^
            (r - (verticesOn (insert T (R ∪ A) ∪ K)).card))) : ℕ) *
        p ^ (j - 2 - A.card) := by
  change extensionWeight
        (fun S : exactBankOutsideExtensionsThrough r j B R K T ↦ S.1)
        (fun _ ↦ p) A ≤ _
  rw [extensionWeight_constant_eq _ (j - 2)
    exactBankOutsideExtensionsThrough_fixed_card p A]
  have hcard :
      ((familyExtensions
        (exactBankOutsideExtensionsThrough r j B R K T) A).card : ℝ≥0) ≤
        (2 ^ (r ^ 3) *
          ((r - (verticesOn (insert T (R ∪ A) ∪ K)).card + 1) *
            (((univ \ verticesOn (insert T (R ∪ A) ∪ K) : Finset V).card + 1) ^
              (r - (verticesOn (insert T (R ∪ A) ∪ K)).card))) : ℕ) := by
    exact_mod_cast
      card_familyExtensions_exactBankOutsideExtensionsThrough_le
        (r := r) (j := j) (B := B) (R := R) (K := K)
        (A := A) (T := T) hr
  simpa only [mul_comm] using
    mul_le_mul_right hcard (p ^ (j - 2 - A.card))

end Erdos207
