/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedRandomRegularization
import ErdosProblems.Erdos207.RandomRegularizedOrderChoice

/-! # The source-correct fixed-envelope order step in the original prior-data law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_fixed_random_regularization_order_step
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j s : ℕ} {W : Vortex V ell} {delta a : ℝ≥0}
    (params : SourceRandomConfigurationParameters W j delta a s)
    (P : FiniteLaw D) (e : (d : D) → I d ↪ TripleOn V)
    (L earlier : (d : D) → Finset (Finset (I d))) (hL : ∀ d E, E ∈ L d → E.card = j - 2)
    (hsize : ∀ d, 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card (I d))
    (hdensity : ∀ d, (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree
      (regularizationForbiddenFamily (e d) (j - 2) (trimForbiddenSupersets (L d) (earlier d)) (earlier d)) ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card (I d)) (j - 2 - 1))
    (beta : ℝ≥0)
    (hbeta : ∀ d, regularizationBaseHazard (trimForbiddenSupersets (L d) (earlier d)) (j - 2) ≤ beta)
    (hsource : 2 * beta ≤ sourceRandomConfigurationProbability W.terminalSize delta j)
    (b t : ℕ) (ht : ∀ d, finiteHypergraphDegreeGap (trimForbiddenSupersets (L d) (earlier d)) ≤ t)
    (C : ForbiddenFamilyOn V) (hC : C ⊆ terminalRandomConfigurations W j)
    (hblocked : ∀ d (E : Finset (I d)), E.card = j - 2 → E.map (e d) ∉ C →
      E ∈ regularizationForbiddenFamily (e d) (j - 2) (trimForbiddenSupersets (L d) (earlier d)) (earlier d))
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (epsilon rho : ℝ≥0) (hrho : 0 < rho)
    (hepsilon : ∀ d, (finiteHypergraphDegreeGap (trimForbiddenSupersets (L d) (earlier d)) : ℝ) *
      (2 * Fintype.card (I d) * Real.exp (-(b : ℝ) / 8192)) ≤ epsilon)
    (hbudget : sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ + epsilon / rho < 1) :
    ∃ R : ForbiddenFamilyOn V, ∃ Lstar : (d : D) → Finset (Finset (I d)),
      R ⊆ C ∧
      SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a) ∧
      SourceAugmentationCounts j W.terminalSize F R a ∧
      (∀ d, (∀ E ∈ Lstar d, E.card = j - 2) ∧
        finiteHypergraphMaxDegree (Lstar d) ≤ 9 * finiteHypergraphMaxDegree (L d) ∧
        (∀ E ∈ Lstar d, ∀ A ∈ earlier d, ¬ A ⊆ E) ∧
        (∀ E ∈ L d, ∃ A ∈ earlier d ∪ Lstar d, A ⊆ E) ∧
        (Lstar d \ L d).image (Finset.map (e d)) ⊆ F ∪ R) ∧
      P.probability (fun d ↦ b < finiteHypergraphDegreeGap (Lstar d)) < rho := by
  let G := fun d ↦ trimForbiddenSupersets (L d) (earlier d)
  let H := fun d ↦ regularizationForbiddenFamily (e d) (j - 2) (G d) (earlier d)
  have hGH : ∀ d, G d ⊆ H d := fun d ↦ subset_regularizationForbiddenFamily (e d) (j - 2) (G d) (earlier d)
  obtain ⟨R, M, hRC, hspread, hcounts, hmarg, haccepted, hfail⟩ :=
    exists_fixed_random_regularization params P e G H hGH hsize hdensity beta hbeta hsource
      b t ht C hC hblocked F y z hF hdeltaY epsilon rho hrho hepsilon hbudget
  refine ⟨R, fun d ↦ regularizedOrderChoice (e d) j b (L d) (earlier d) (F ∪ R),
    hRC, hspread, hcounts, ?_, ?_⟩
  · intro d
    exact regularizedOrderChoice_properties (e d) j b (L d) (earlier d) (F ∪ R) (hL d)
  · have hcontain : M.SupportedOn (fun x ↦ x.2.2 ⊆ F ∪ R) :=
      fun x hx ↦ (haccepted x hx).trans subset_union_right
    exact (regularizedOrderChoice_gap_failure_of_marginal e j b L earlier hL (F ∪ R)
      M Prod.fst P hmarg (fun x ↦ x.2.2) hcontain).trans_lt hfail

end

end Erdos207
