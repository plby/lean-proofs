/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.DHJ.Tiling
import ErdosProblems.Erdos185.DHJ.Correlation
import ErdosProblems.Erdos185.DHJ.Iteration

/-!
# The ternary density increment

This file combines the correlation and insensitive-set tiling statements.
The first theorem is the finite averaging calculation which turns an almost
tiling of the structured set into a dense tile.  The final theorem packages
the result with constants which depend only on the fixed density floor, not
on the current density.  That uniformity is what permits finite iteration.
-/

open scoped BigOperators

namespace Erdos185.DHJ

open Combinatorics

private theorem density_eq_erdos171_density {X : Type*} [Fintype X]
    (A : Finset X) : density A = Erdos171.density A :=
  rfl

private theorem pullback_eq_subspacePullback
    {eta alpha iota : Type*} [Fintype eta] [Fintype alpha]
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha)) :
    pullbackFinset U A = Erdos171.subspacePullback U A := by
  classical
  ext x
  simp [Erdos171.mem_subspacePullback]

private theorem densityIn_eq_erdos171
    {eta alpha iota : Type*} [Fintype eta] [Fintype alpha]
    [Fintype (eta → alpha)] [DecidableEq eta]
    (U : Subspace eta alpha iota) (A : Finset (iota → alpha)) :
    densityIn U A = Erdos171.density (Erdos171.subspacePullback U A) := by
  rw [densityIn, pullback_eq_subspacePullback]
  rw [Erdos171.density, Nat.card_eq_fintype_card]

/-! The strictly positive common ambient density of the tiles lets one pass
from an inequality on their disjoint union to one of the tiles. -/

private theorem exists_dense_tile {m d : ℕ}
    (A : Finset (Word 3 m))
    (T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin m))
    {c : ℝ}
    (hglobal : c * density T.covered < density (A ∩ T.covered)) :
    ∃ U ∈ T.tiles, c < densityIn U A := by
  classical
  let p : Subspace (Fin d) (Fin 3) (Fin m) → Finset (Word 3 m) :=
    fun U ↦ Erdos171.subspacePoints U
  let q : Subspace (Fin d) (Fin 3) (Fin m) → Finset (Word 3 m) :=
    fun U ↦ Erdos171.subspacePoints U ∩ A
  have hqdisj : (T.tiles : Set (Subspace (Fin d) (Fin 3) (Fin m))).PairwiseDisjoint q := by
    intro U hU V hV hne
    exact (T.pairwiseDisjoint hU hV hne).mono (Finset.inter_subset_left)
      (Finset.inter_subset_left)
  have hinter : T.tiles.biUnion q = A ∩ T.covered := by
    ext x
    simp only [Finset.mem_biUnion, q, p, Erdos171.SubspaceTiling.mem_covered,
      Finset.mem_inter]
    aesop
  have hsum_global :
      c * (∑ U ∈ T.tiles, Erdos171.density (p U)) <
        ∑ U ∈ T.tiles, Erdos171.density (q U) := by
    rw [← Erdos171.SubspaceTiling.density_covered,
      ← Erdos171.density_biUnion hqdisj, hinter]
    simpa only [density_eq_erdos171_density] using hglobal
  have hex : ∃ U ∈ T.tiles,
      c * Erdos171.density (p U) < Erdos171.density (q U) := by
    by_contra! h
    have hsum :
        ∑ U ∈ T.tiles, Erdos171.density (q U) ≤
          ∑ U ∈ T.tiles, c * Erdos171.density (p U) := by
      gcongr with U hU
      exact h U hU
    rw [← Finset.mul_sum] at hsum
    exact (not_lt_of_ge hsum) hsum_global
  obtain ⟨U, hUT, hU⟩ := hex
  refine ⟨U, hUT, ?_⟩
  have hfactor := Erdos171.density_inter_subspacePoints U A
  have htilepos : 0 < Erdos171.density (Erdos171.subspacePoints U) := by
    rw [Erdos171.density_eq_card_div_card,
      Erdos171.card_subspacePoints_fin, Erdos171.card_word]
    positivity
  have hpU : p U = Erdos171.subspacePoints U := rfl
  have hqU : q U = Erdos171.subspacePoints U ∩ A := rfl
  rw [hpU, hqU, hfactor] at hU
  have hlocal : c < Erdos171.density (Erdos171.subspacePullback U A) := by
    apply lt_of_mul_lt_mul_left _ htilepos.le
    simpa only [mul_comm] using hU
  simpa only [densityIn_eq_erdos171] using hlocal

/-! The scalar part of Proposition 6 in Dodos--Kanellopoulos--Tyros. -/

theorem exists_density_increment_of_correlation_tiling {m d : ℕ}
    (A D : Finset (Word 3 m)) (alpha γ : ℝ)
    (halpha : 0 ≤ alpha) (hγ : 0 < γ)
    (hD : γ ≤ density D)
    (hcorr : (alpha + γ) * density D ≤ density (A ∩ D))
    (T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin m))
    (hcontained : T.IsContainedIn D)
    (huncovered : density (D \ T.covered) < γ ^ 2 / 2) :
    ∃ U ∈ T.tiles, alpha + γ / 2 < densityIn U A := by
  classical
  have hcovD : T.covered ⊆ D :=
    (Erdos171.SubspaceTiling.covered_subset_iff T D).2 hcontained
  have hu : density T.covered ≤ density D := density_mono hcovD
  have hsplitD : density (D \ T.covered) + density T.covered = density D := by
    rw [density_eq_erdos171_density, density_eq_erdos171_density,
      density_eq_erdos171_density]
    have hs := Erdos171.density_sdiff_add_density_inter D T.covered
    rw [Finset.inter_eq_right.mpr hcovD] at hs
    exact hs
  have hsplitA :
      density ((A ∩ D) \ T.covered) + density (A ∩ T.covered) =
        density (A ∩ D) := by
    rw [density_eq_erdos171_density, density_eq_erdos171_density,
      density_eq_erdos171_density]
    have hs := Erdos171.density_sdiff_add_density_inter (A ∩ D) T.covered
    have hi : (A ∩ D) ∩ T.covered = A ∩ T.covered := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hxA, _⟩, hxT⟩
        exact ⟨hxA, hxT⟩
      · rintro ⟨hxA, hxT⟩
        exact ⟨⟨hxA, hcovD hxT⟩, hxT⟩
    simpa only [hi] using hs
  have hrem_le : density ((A ∩ D) \ T.covered) ≤ density (D \ T.covered) := by
    apply density_mono
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
    exact ⟨hx.1.2, hx.2⟩
  have hc :
      (alpha + γ) * density D - density (D \ T.covered) ≤
        density (A ∩ T.covered) := by
    linarith
  have hcoefficient : 0 ≤ alpha + γ / 2 := by
    positivity
  have hutarget :
      (alpha + γ / 2) * density T.covered ≤
        (alpha + γ / 2) * density D :=
    mul_le_mul_of_nonneg_left hu hcoefficient
  have hgap : density (D \ T.covered) < (γ / 2) * density D := by
    nlinarith [sq_pos_of_pos hγ]
  have hmass :
      (alpha + γ / 2) * density T.covered <
        density (A ∩ T.covered) := by
    nlinarith
  apply exists_dense_tile A T
  exact hmass

/-! ## Quantifier-compatible assembly

The two propositions below record the exact output contracts of the
correlation and tiling modules.  In particular, the correlation constants
are chosen before the target dimension, so the eventual additive gain is
uniform throughout the iteration. -/

def TernaryCorrelationPrinciple : Prop :=
  ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
    ∃ p : CorrelationConstants, p.delta = delta ∧
      ∃ lower : ℕ, ∀ m : ℕ, lower ≤ m →
        ∃ n : ℕ, ∀ A : Finset (Word 3 n), delta ≤ density A →
          HasLine A ∨
            ∃ W : Subspace (Fin m) (Fin 3) (Fin n),
              Nonempty (InsensitiveCorrelation p (density A) (pullbackFinset W A))

def TwoInsensitiveTilingPrinciple : Prop :=
  ∀ (d lower : ℕ) (beta : ℝ), 0 < beta →
    ∃ m : ℕ, lower ≤ m ∧
      ∀ D₀ D₁ : Finset (Word 3 m),
        Erdos171.IsLastInsensitive 0 (D₀ : Set (Word 3 m)) →
        Erdos171.IsLastInsensitive 1 (D₁ : Set (Word 3 m)) →
          ∃ T : Erdos171.SubspaceTiling (Fin d) (Fin 3) (Fin m),
            T.IsContainedIn (D₀ ∩ D₁) ∧
              density ((D₀ ∩ D₁) \ T.covered) < 4 * beta

/-- Proposition 6 of Dodos--Kanellopoulos--Tyros, in the precise uniform
form needed by `Iteration.lean`. -/
theorem ternaryIncrementPrinciple_of_correlation_tiling
    (hcorr : TernaryCorrelationPrinciple)
    (htile : TwoInsensitiveTilingPrinciple) :
    TernaryIncrementPrinciple := by
  intro delta hdelta
  by_cases hdeltaOne : delta ≤ 1
  · obtain ⟨p, hpdelta, lower, hp⟩ := hcorr delta hdelta hdeltaOne
    refine ⟨p.gamma / 2, half_pos p.gamma_pos, ?_⟩
    intro d
    let beta : ℝ := p.gamma ^ 2 / 8
    have hbeta : 0 < beta := by
      dsimp only [beta]
      exact div_pos (sq_pos_of_pos p.gamma_pos) (by norm_num)
    obtain ⟨m, hm, hmTile⟩ := htile d lower beta hbeta
    obtain ⟨n, hn⟩ := hp m hm
    refine ⟨n, ?_⟩
    intro A hA
    rcases hn A hA with hline | ⟨W, hS⟩
    · exact Or.inl hline
    · obtain ⟨S⟩ := hS
      obtain ⟨T, hcontained, herror⟩ :=
        hmTile S.first S.second S.first_insensitive S.second_insensitive
      have herror' :
          density ((S.first ∩ S.second) \ T.covered) < p.gamma ^ 2 / 2 := by
        have hfour : 4 * beta = p.gamma ^ 2 / 2 := by
          dsimp only [beta]
          ring
        simpa only [hfour] using herror
      obtain ⟨U, _hUT, hU⟩ :=
        exists_density_increment_of_correlation_tiling
          (pullbackFinset W A) (S.first ∩ S.second) (density A) p.gamma
          (density_nonneg A) p.gamma_pos
          S.mass S.correlated T hcontained herror'
      refine Or.inr ⟨W.comp U, ?_⟩
      rw [densityIn_comp]
      exact le_of_lt hU
  · refine ⟨1, zero_lt_one, ?_⟩
    intro d
    refine ⟨0, ?_⟩
    intro A hA
    exfalso
    have hupper := density_le_one A
    exact hdeltaOne (hA.trans hupper)

/-- The concrete uniform ternary increment, obtained from the correlation
theorem and the two-insensitive-factor almost-tiling theorem. -/
theorem ternaryIncrementPrinciple : TernaryIncrementPrinciple := by
  intro delta hdelta
  by_cases hdeltaOne : delta ≤ 1
  · obtain ⟨s, _hsdelta, lower, hcorr⟩ :=
      exists_uniform_insensitiveCorrelation delta hdelta hdeltaOne
    let p : CorrelationConstants := s.constants
    refine ⟨p.gamma / 2, half_pos p.gamma_pos, ?_⟩
    intro d
    let beta : ℝ := p.gamma ^ 2 / 8
    have hbeta : 0 < beta := by
      dsimp only [beta]
      exact div_pos (sq_pos_of_pos p.gamma_pos) (by norm_num)
    obtain ⟨m, hm, htile⟩ :=
      exists_two_insensitive_tiling_dimension d lower beta hbeta
    obtain ⟨n, hn⟩ := hcorr m hm
    refine ⟨n, ?_⟩
    intro A hA
    rcases hn A hA with hline | ⟨W, hS⟩
    · exact Or.inl hline
    · obtain ⟨S⟩ := hS
      have hgammaOne : p.gamma ≤ 1 := by
        calc
          p.gamma ≤ p.eta / 2 := p.gamma_le_eta_div_two
          _ ≤ 1 := by nlinarith [p.eta_le_one]
      have hfourBeta : 4 * beta ≤ p.gamma := by
        have hsquare : p.gamma ^ 2 ≤ p.gamma := by
          nlinarith [mul_nonneg p.gamma_nonneg (sub_nonneg.mpr hgammaOne)]
        dsimp only [beta]
        nlinarith
      obtain ⟨T, hcontained, herror⟩ :=
        htile S.first S.second S.first_insensitive S.second_insensitive
          (hfourBeta.trans S.mass)
      have herror' :
          density ((S.first ∩ S.second) \ T.covered) < p.gamma ^ 2 / 2 := by
        have hfour : 4 * beta = p.gamma ^ 2 / 2 := by
          dsimp only [beta]
          ring
        simpa only [hfour] using herror
      obtain ⟨U, _hUT, hU⟩ :=
        exists_density_increment_of_correlation_tiling
          (pullbackFinset W A) (S.first ∩ S.second) (density A) p.gamma
          (density_nonneg A) p.gamma_pos S.mass S.correlated T hcontained herror'
      refine Or.inr ⟨W.comp U, ?_⟩
      rw [densityIn_comp]
      exact le_of_lt hU
  · refine ⟨1, zero_lt_one, ?_⟩
    intro d
    refine ⟨0, ?_⟩
    intro A hA
    exfalso
    have hupper := density_le_one A
    exact hdeltaOne (hA.trans hupper)

end Erdos185.DHJ
