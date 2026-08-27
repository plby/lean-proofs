/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedSourceEnvelope
import ErdosProblems.Erdos207.SourceWellSpreadSubfamily

/-! # A fixed source envelope inside a prescribed deterministic shell -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_fixed_shell_source_envelope
    {Ω D V : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {ell j s : ℕ} {W : Vortex V ell} {delta a : ℝ≥0}
    (params : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw Ω) (data : Ω → D) (seed : Ω → ForbiddenFamilyOn V)
    (P : FiniteLaw D) (Q : FiniteLaw (ForbiddenFamilyOn V))
    (hind : FiniteLaw.map (fun x ↦ (data x, seed x)) L = P.jointBind (fun _ ↦ Q))
    (hQ : ∀ U, Q.probability (fun R ↦ U ⊆ R) ≤
      sourceRandomConfigurationProbability W.terminalSize delta j ^ U.card)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize)
    (C : ForbiddenFamilyOn V) (hC : C ⊆ terminalRandomConfigurations W j)
    (accepted : Ω → ForbiddenFamilyOn V)
    (hsupport : L.SupportedOn (fun x ↦ accepted x ⊆ seed x ∧ accepted x ⊆ C))
    (Bad : Ω → Prop) (epsilon rho : ℝ≥0) (hrho : 0 < rho)
    (hbad : L.probability Bad ≤ epsilon)
    (hbudget : sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ + epsilon / rho < 1) :
    ∃ R : ForbiddenFamilyOn V, ∃ M : FiniteLaw Ω,
      R ⊆ C ∧
      SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a) ∧
      SourceAugmentationCounts j W.terminalSize F R a ∧
      FiniteLaw.map data M = P ∧
      M.SupportedOn (fun x ↦ accepted x ⊆ R) ∧
      (∀ A : Ω → Prop, L.SupportedOn A → M.SupportedOn A) ∧
      M.probability Bad < rho := by
  obtain ⟨R, M, _, hspread, hcounts, hdata, haccepted, hpersist, hfail⟩ :=
    exists_fixed_source_envelope params L data seed P Q hind hQ F y z hF hdeltaY accepted
      (fun x hx ↦ ⟨(hsupport x hx).1, ((hsupport x hx).2).trans hC⟩)
      Bad epsilon rho hrho hbad hbudget
  refine ⟨R ∩ C, M, inter_subset_right,
    hspread.of_subset (union_subset_union Subset.rfl inter_subset_left),
    hcounts.mono inter_subset_left, hdata, ?_, hpersist, hfail⟩
  have hMC := hpersist (fun x ↦ accepted x ⊆ C) (fun x hx ↦ (hsupport x hx).2)
  intro x hx
  exact subset_inter (haccepted x hx) (hMC x hx)

end

end Erdos207
