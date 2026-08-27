/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedRandomOrderStep
import ErdosProblems.Erdos207.SourceRegularizationInputScalars

/-! # Discharging the fixed random order step from the established numerical inputs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_fixed_random_order_of_inputs
    {D V K : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [DecidableEq K]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j b s : ℕ} {W : Vortex V ell} {y z a delta : ℝ≥0}
    (P : FiniteLaw D) (e : (d : D) → I d ↪ TripleOn V)
    (hsupport : ∀ d i, (e d i).1 ⊆ W.U (Fin.last ell))
    (L : (d : D) → Finset (Finset (I d))) (F : ForbiddenFamilyOn V)
    (sigma constant B : D → ℝ≥0)
    (hinputs : ∀ d, SourceRegularizationOrderInput W j (L d) F b s y z a delta (sigma d) (constant d) (B d))
    (orders : Finset K) (earlier : (d : D) → K → Finset (Finset (I d))) (size : K → ℕ)
    (horders : orders.card ≤ W.terminalSize)
    (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ j - 2)
    (huniform : ∀ d i, i ∈ orders → ∀ E ∈ earlier d i, E.card = size i)
    (hearlier : ∀ d i, i ∈ orders → finiteHypergraphMaxDegree (earlier d i) ≤ W.terminalSize ^ (size i - 1))
    (C : ForbiddenFamilyOn V) (hC : C ⊆ terminalRandomConfigurations W j)
    (hgeometry : ∀ d (E : Finset (I d)), E.card = j - 2 →
      E.map (e d) ∈ terminalRandomConfigurations W j → E.map (e d) ∈ C)
    (epsilon rho : ℝ≥0) (hrho : 0 < rho)
    (hepsilon : ∀ d, (finiteHypergraphMaxDegree (L d) : ℝ) *
      (2 * Fintype.card (I d) * Real.exp (-(b : ℝ) / 8192)) ≤ epsilon)
    (hbudget : sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ + epsilon / rho < 1) :
    ∃ R : ForbiddenFamilyOn V, ∃ Lstar : (d : D) → Finset (Finset (I d)),
      R ⊆ C ∧
      SourceVortexWellSpread W j (F ∪ R) (y + a) (z + 3 * a) ∧
      SourceAugmentationCounts j W.terminalSize F R a ∧
      (∀ d, (∀ E ∈ Lstar d, E.card = j - 2) ∧
        finiteHypergraphMaxDegree (Lstar d) ≤ 9 * finiteHypergraphMaxDegree (L d) ∧
        (∀ E ∈ Lstar d, ∀ A ∈ orders.biUnion (earlier d), ¬ A ⊆ E) ∧
        (∀ E ∈ L d, ∃ A ∈ orders.biUnion (earlier d) ∪ Lstar d, A ⊆ E) ∧
        (Lstar d \ L d).image (Finset.map (e d)) ⊆ F ∪ R) ∧
      P.probability (fun d ↦ b < finiteHypergraphDegreeGap (Lstar d)) < rho := by
  obtain ⟨d0, _⟩ := P.exists_mass_pos
  have hj := (hinputs d0).parameters.order
  have he : j - 2 - 1 = j - 3 := by omega
  let beta := sourceRandomConfigurationProbability W.terminalSize delta j / 2
  have hscalar (d : D) := (hinputs d).scalar_conditions (e d) (hsupport d) orders (earlier d) size
    horders hsize (huniform d) (hearlier d)
  have hgapmax (d : D) : finiteHypergraphDegreeGap (trimForbiddenSupersets (L d) (orders.biUnion (earlier d))) ≤
      finiteHypergraphMaxDegree (L d) :=
    (Nat.sub_le _ _).trans (finiteHypergraphMaxDegree_mono (trimForbiddenSupersets_subset _ _))
  apply exists_fixed_random_regularization_order_step (hinputs d0).parameters P e L
    (fun d ↦ orders.biUnion (earlier d)) (fun d ↦ (hinputs d).uniform)
    (fun d ↦ by simpa only [he] using (hinputs d).size)
    (fun d ↦ (hscalar d).1) beta
    (fun d ↦ (le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)).mpr (by
      simpa only [mul_comm] using (hscalar d).2.1))
    (by dsimp only [beta]; exact (mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)).le)
    b (W.terminalSize ^ (j - 3))
    (fun d ↦ by have hm := (hinputs d).maximum_power; have hg := hgapmax d; omega)
    C hC
    (fun d E hE hnot ↦ regularizationForbiddenFamily_contains_nonCandidates W (e d) (hsupport d)
      (trimForbiddenSupersets (L d) (orders.biUnion (earlier d))) (orders.biUnion (earlier d)) E hE
      (fun hterm ↦ hnot (hgeometry d E hE hterm)))
    F y z (hinputs d0).spread (hinputs d0).delta_y epsilon rho hrho
    (fun d ↦ ?_) hbudget
  have hgapReal : (finiteHypergraphDegreeGap (trimForbiddenSupersets (L d) (orders.biUnion (earlier d))) : ℝ) ≤
      finiteHypergraphMaxDegree (L d) := by exact_mod_cast hgapmax d
  exact (mul_le_mul_of_nonneg_right hgapReal (by positivity)).trans (hepsilon d)

end

end Erdos207
