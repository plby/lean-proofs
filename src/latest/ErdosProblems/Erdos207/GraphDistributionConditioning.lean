/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphRestrictedDistribution
import ErdosProblems.Erdos207.FiniteConditioning

/-! # Conditioning the source-correct graph distribution preserves every prescription -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsInitialGraphProductBound.mono_error
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C error error' : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C error) (he : error ≤ error') :
    IsInitialGraphProductBound L selected G p C error' := by
  intro Q E hE
  exact (h Q E hE).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) zero_le)

theorem IsInitialGraphProductBound.mono_constant
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C C' error : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C error) (hC : C ≤ C') :
    IsInitialGraphProductBound L selected G p C' error := by
  intro Q E hE
  exact (h Q E hE).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left' hC _) zero_le)

theorem IsInitialGraphProductBound.conditionOn
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C error : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C error)
    (Good : Ω → Prop) (hGood : 0 < L.probability Good) :
    IsInitialGraphProductBound (L.conditionOn Good hGood) selected G p (C / L.probability Good) error := by
  intro Q E hE
  let m := Q.card + E.card
  let X := p ^ E.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + error
  by_cases hm : m = 0
  · have hQ : Q = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hE' : E = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    subst Q
    subst E
    exact ((L.conditionOn Good hGood).probability_le_one _).trans (by simp)
  · have hzpow : L.probability Good ^ m ≤ L.probability Good :=
      pow_le_of_le_one zero_le (L.probability_le_one Good) hm
    have hscale : C ^ m / L.probability Good ≤ (C / L.probability Good) ^ m := by
      rw [div_pow]
      gcongr
    calc
      _ ≤ L.probability (fun ω ↦ Q ⊆ selected ω ∧ ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) /
          L.probability Good := L.conditionOn_probability_le Good _ hGood
      _ ≤ (C ^ m * X) / L.probability Good := div_le_div_of_nonneg_right (h Q E hE) zero_le
      _ = (C ^ m / L.probability Good) * X := by ring
      _ ≤ (C / L.probability Good) ^ m * X := mul_le_mul_of_nonneg_right hscale zero_le

theorem IsInitialGraphProductBound.conditionOn_half
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C error : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C error)
    (Good : Ω → Prop) (hGood : 0 < L.probability Good) (hhalf : 1 / 2 ≤ L.probability Good) :
    IsInitialGraphProductBound (L.conditionOn Good hGood) selected G p (2 * C) error := by
  apply (h.conditionOn Good hGood).mono_constant
  calc
    C / L.probability Good ≤ C / (1 / 2) := div_le_div_of_nonneg_left zero_le (by norm_num) hhalf
    _ = 2 * C := by ring

theorem IsInitialGraphProductBound.map
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} (f : Ω → Ξ) {selected : Ξ → TripleSystemOn V}
    {G : SimpleGraph V} {p C error : ℝ≥0}
    (h : IsInitialGraphProductBound L (fun ω ↦ selected (f ω)) G p C error) :
    IsInitialGraphProductBound (L.map f) selected G p C error := by
  intro Q E hE
  simpa only [FiniteLaw.probability_map] using h Q E hE

end

end Erdos207
