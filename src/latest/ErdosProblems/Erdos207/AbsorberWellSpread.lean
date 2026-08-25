/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCompletionCount

/-!
# Indexed absorber-induced forbidden families

KSSS group outside parts by their number of triangles.  Property A2 gives
the key dichotomy used in every well-spread count: after fixing a subfamily
`R`, either all absorber triangles lie in one bounded local family, or an
additional outside triangle meets a non-flexible absorber vertex.
-/

namespace Erdos207

open Finset

/-- Outside parts with exactly `j - 2` triangles which can be completed by
bank triangles to a minimal configuration of cutoff at most `q`. -/
noncomputable def absorberInducedConfigurationsOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (q j : ℕ) (B : TripleSystemOn V) : ForbiddenFamilyOn V := by
  classical
  exact (univ : Finset (TripleSystemOn V)).filter fun S ↦
    S.card = j - 2 ∧ ∃ r ∈ Icc 5 q, ∃ E : TripleSystemOn V,
      IsErdosConfigOn r E ∧ E \ B = S

@[simp]
lemma mem_absorberInducedConfigurationsOn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B S : TripleSystemOn V} :
    S ∈ absorberInducedConfigurationsOn q j B ↔
      S.card = j - 2 ∧ ∃ r, 5 ≤ r ∧ r ≤ q ∧
        ∃ E : TripleSystemOn V, IsErdosConfigOn r E ∧ E \ B = S := by
  classical
  simp [absorberInducedConfigurationsOn, and_assoc]

/-- Every indexed induced family is a subfamily of the unindexed forbidden
family used by the constrained process (at nonempty sizes). -/
lemma absorberInducedConfigurationsOn_subset_erdosForbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {B : TripleSystemOn V} (hj : 3 ≤ j) :
    absorberInducedConfigurationsOn q j B ⊆
      absorberErdosForbiddenConfigurationsOn q B := by
  intro S hS
  obtain ⟨hScard, r, hr5, hrq, E, hE, hEB⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hS
  apply mem_absorberErdosForbiddenConfigurationsOn_iff.mpr
  refine ⟨?_, r, by omega, hrq, E, hE,
    IsErdosConfig.isPackingOn hE hr5, hEB⟩
  rw [nonempty_iff_ne_empty]
  intro hSempty
  rw [hSempty, card_empty] at hScard
  omega

/-- Vertices incident with at least one absorber edge. -/
noncomputable def graphSupportFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v ↦ ∃ w, H.Adj v w

@[simp]
lemma mem_graphSupportFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {v : V} :
    v ∈ graphSupportFinset H ↔ ∃ w, H.Adj v w := by
  classical
  simp [graphSupportFinset]

/-- Uniform form of the A2 split: after the root family `R` is fixed, one
local bank `L` works simultaneously for every indexed outside extension of
`R`.  This uniformity is essential when the alternatives are counted. -/
theorem absorberInduced_extensions_local_or_meets_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      ∀ S ∈ absorberInducedConfigurationsOn q j B, R ⊆ S →
        ((∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
            E \ B = S → E ∩ B ⊆ L) ∨
          ∃ r E T v, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
            E \ B = S ∧ T ∈ S ∧ T ∉ R ∧ v ∈ T.1 ∧
            v ∈ graphSupportFinset H ∧ v ∉ X) := by
  obtain ⟨L, hLB, hLM, hL⟩ :=
    hA2 (SimpleGraph.completeGraph V) le_top R hRq
      (consistsOfTriangles_completeGraph R)
  refine ⟨L, hLB, hLM, ?_⟩
  intro S hS hRS
  by_cases hall : ∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
      E \ B = S → E ∩ B ⊆ L
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨r, E, hr5, hrq, hE, hEout, hEnotL⟩ := hall
    have hRE : R ⊆ E := by
      intro T hTR
      have hTS : T ∈ S := hRS hTR
      have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
      exact (mem_sdiff.mp hTdiff).1
    rcases hL r hr5 hrq E hE hRE with hlocal | hnonlocal
    · exact (hEnotL hlocal).elim
    · obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hnonlocal
      have hTnotR : T ∉ R := by
        intro hTR
        exact hTfree (mem_union.mpr (Or.inl hTR))
      have hTnotB : T ∉ B := by
        intro hTB
        exact hTfree (mem_union.mpr (Or.inr hTB))
      have hTS : T ∈ S := by
        have : T ∈ E \ B := mem_sdiff.mpr ⟨hTE, hTnotB⟩
        simpa only [hEout] using this
      exact ⟨r, E, T, v, hr5, hrq, hE, hEout, hTS, hTnotR,
        hvT, mem_graphSupportFinset_iff.mpr hvH, hvX⟩

/-- The same A2 split retaining the fact that the completion in the support
branch is genuinely nonlocal.  In particular its exact bank part is
nonempty.  This retained negation is needed for the strict WS4 exponent. -/
theorem absorberInduced_extensions_local_or_genuinely_meets_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      ∀ S ∈ absorberInducedConfigurationsOn q j B, R ⊆ S →
        ((∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
            E \ B = S → E ∩ B ⊆ L) ∨
          ∃ r E T v, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
            E \ B = S ∧ ¬ E ∩ B ⊆ L ∧ T ∈ S ∧ T ∉ R ∧
            v ∈ T.1 ∧ v ∈ graphSupportFinset H ∧ v ∉ X) := by
  obtain ⟨L, hLB, hLM, hL⟩ :=
    hA2 (SimpleGraph.completeGraph V) le_top R hRq
      (consistsOfTriangles_completeGraph R)
  refine ⟨L, hLB, hLM, ?_⟩
  intro S hS hRS
  by_cases hall : ∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
      E \ B = S → E ∩ B ⊆ L
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨r, E, hr5, hrq, hE, hEout, hEnotL⟩ := hall
    have hRE : R ⊆ E := by
      intro T hTR
      have hTS : T ∈ S := hRS hTR
      exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1
    rcases hL r hr5 hrq E hE hRE with hlocal | hnonlocal
    · exact (hEnotL hlocal).elim
    · obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hnonlocal
      have hTnotR : T ∉ R := by
        intro hTR
        exact hTfree (mem_union.mpr (Or.inl hTR))
      have hTnotB : T ∉ B := by
        intro hTB
        exact hTfree (mem_union.mpr (Or.inr hTB))
      have hTS : T ∈ S := by
        have : T ∈ E \ B := mem_sdiff.mpr ⟨hTE, hTnotB⟩
        simpa only [hEout] using this
      exact ⟨r, E, T, v, hr5, hrq, hE, hEout, hEnotL, hTS,
        hTnotR, hvT, mem_graphSupportFinset_iff.mpr hvH, hvX⟩

/-- The exact A2 split behind KSSS Lemma 7.2.  In the nonlocal branch the
distinguished triangle is part of the outside family `S`, is not among the
fixed triangles `R`, and meets `V(H) \ X`. -/
theorem absorberInduced_local_or_meets_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B S R : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hS : S ∈ absorberInducedConfigurationsOn q j B)
    (hRS : R ⊆ S) (hRq : R.card ≤ q) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      ((∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
          E \ B = S → E ∩ B ⊆ L) ∨
        ∃ r E T v, 5 ≤ r ∧ r ≤ q ∧ IsErdosConfigOn r E ∧
          E \ B = S ∧ T ∈ S ∧ T ∉ R ∧ v ∈ T.1 ∧
          v ∈ graphSupportFinset H ∧ v ∉ X) := by
  obtain ⟨_hScard, r₀, hr₀5, hr₀q, E₀, hE₀, hE₀out⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hS
  have hRE₀ : R ⊆ E₀ := by
    intro T hTR
    have hTS : T ∈ S := hRS hTR
    have hTdiff : T ∈ E₀ \ B := by simpa only [hE₀out] using hTS
    exact (mem_sdiff.mp hTdiff).1
  obtain ⟨L, hLB, hLM, hL⟩ :=
    hA2 (SimpleGraph.completeGraph V) le_top R hRq
      (consistsOfTriangles_completeGraph R)
  refine ⟨L, hLB, hLM, ?_⟩
  by_cases hall : ∀ r E, 5 ≤ r → r ≤ q → IsErdosConfigOn r E →
      E \ B = S → E ∩ B ⊆ L
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨r, E, hr5, hrq, hE, hEout, hEnotL⟩ := hall
    have hRE : R ⊆ E := by
      intro T hTR
      have hTS : T ∈ S := hRS hTR
      have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
      exact (mem_sdiff.mp hTdiff).1
    rcases hL r hr5 hrq E hE hRE with hlocal | hnonlocal
    · exact (hEnotL hlocal).elim
    · obtain ⟨T, hTE, hTfree, v, hvT, hvH, hvX⟩ := hnonlocal
      have hTnotR : T ∉ R := by
        intro hTR
        exact hTfree (mem_union.mpr (Or.inl hTR))
      have hTnotB : T ∉ B := by
        intro hTB
        exact hTfree (mem_union.mpr (Or.inr hTB))
      have hTS : T ∈ S := by
        have : T ∈ E \ B := mem_sdiff.mpr ⟨hTE, hTnotB⟩
        simpa only [hEout] using this
      exact ⟨r, E, T, v, hr5, hrq, hE, hEout, hTS, hTnotR,
        hvT, mem_graphSupportFinset_iff.mpr hvH, hvX⟩

/-- A fixed indexed outside part has at most `q * 2^M` bank completions. -/
theorem card_erdosBankCompletions_le_of_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M j : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B S : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hS : S ∈ absorberInducedConfigurationsOn q j B) :
    (erdosBankCompletions q B S).card ≤ q * 2 ^ M := by
  apply card_erdosBankCompletions_le hA2
  obtain ⟨hScard, r, hr5, hrq, E, hE, hEout⟩ :=
    mem_absorberInducedConfigurationsOn_iff.mp hS
  rw [hScard]
  have hjr : j ≤ r := by
    have hSsub : S ⊆ E := by
      intro T hTS
      have hTdiff : T ∈ E \ B := by simpa only [hEout] using hTS
      exact (mem_sdiff.mp hTdiff).1
    have hcard := card_le_card hSsub
    rw [hE.1.1] at hcard
    omega
  omega

end Erdos207
