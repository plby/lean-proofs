/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualGraphDistribution
import ErdosProblems.Erdos207.ReserveEdgeSampling

/-! # Reserve prescriptions together with full-union residual edges -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ResidualReserveDistributionEvent
    {Ω V : Type*} [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V) (reserve : Ω → Finset (Sym2 V))
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)) (ω : Ω) : Prop :=
  ResidualDistributionEvent initial later Ifix Dfix Efix ω ∧ Rfix ⊆ reserve ω

def IsResidualReserveStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (reserve : Ω → Finset (Sym2 V))
    (p r C b : ℝ≥0) : Prop :=
  ∀ (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)),
    Disjoint Ifix Dfix → Efix ⊆ graphEdges G →
    L.probability (ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix Rfix) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * r ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W k p Dfix + b)

theorem IsResidualReserveStronglyWellDistributed.mono
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C C' b b' : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hC : C ≤ C') (hb : b ≤ b') :
    IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C' b' := by
  intro Ifix Dfix Efix Rfix hdis hE
  exact (h Ifix Dfix Efix Rfix hdis hE).trans (by gcongr)

theorem IsResidualReserveStronglyWellDistributed.toResidual
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)}
    {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b) :
    IsResidualGraphStronglyWellDistributed L W k G initial later p C b := by
  intro Ifix Dfix Efix hdis hE
  have hraw := h Ifix Dfix Efix ∅ hdis hE
  have hevent : ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix ∅ =
      ResidualDistributionEvent initial later Ifix Dfix Efix := by
    funext ω
    simp only [ResidualReserveDistributionEvent, empty_subset, and_true]
  rw [hevent] at hraw
  simpa only [card_empty, Nat.add_zero, pow_zero, mul_one] using hraw

theorem IsResidualReserveStronglyWellDistributed.map
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} (f : Ω → Ξ) {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ξ → TripleSystemOn V} {reserve : Ξ → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G
      (fun ω ↦ initial (f ω)) (fun ω ↦ later (f ω)) (fun ω ↦ reserve (f ω)) p r C b) :
    IsResidualReserveStronglyWellDistributed (L.map f) W k G initial later reserve p r C b := by
  intro Ifix Dfix Efix Rfix hdis hE
  rw [FiniteLaw.probability_map]
  exact h Ifix Dfix Efix Rfix hdis hE

theorem IsResidualReserveStronglyWellDistributed.conditionOn
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (h : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (Good : Ω → Prop) (hGood : 0 < L.probability Good) :
    IsResidualReserveStronglyWellDistributed (L.conditionOn Good hGood) W k G
      initial later reserve p r (C / L.probability Good) b := by
  intro Ifix Dfix Efix Rfix hdis hE
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p ^ Efix.card * r ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
    laterTriangleScale W k p Dfix + b
  by_cases hm : m = 0
  · have hI : Ifix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hD : Dfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hE' : Efix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hR : Rfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    subst Ifix
    subst Dfix
    subst Efix
    subst Rfix
    exact ((L.conditionOn Good hGood).probability_le_one _).trans (by simp)
  · have hzpow : L.probability Good ^ m ≤ L.probability Good :=
      pow_le_of_le_one zero_le (L.probability_le_one Good) hm
    have hscale : C ^ m / L.probability Good ≤ (C / L.probability Good) ^ m := by
      rw [div_pow]
      gcongr
    calc
      _ ≤ L.probability (ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix Rfix) /
          L.probability Good := L.conditionOn_probability_le Good _ hGood
      _ ≤ (C ^ m * X) / L.probability Good :=
          div_le_div_of_nonneg_right (h Ifix Dfix Efix Rfix hdis hE) zero_le
      _ = (C ^ m / L.probability Good) * X := by ring
      _ ≤ (C / L.probability Good) ^ m * X := mul_le_mul_of_nonneg_right hscale zero_le

theorem IsResidualGraphStronglyWellDistributed.jointBind_reserveEdges
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {G : Omega → SimpleGraph V} {G₀ : SimpleGraph V} {U : Finset V}
    {p C b r : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G₀ initial later p C b)
    (hC : 1 ≤ C) (hr : r ≤ 1) :
    IsResidualReserveStronglyWellDistributed
      (L.jointBind fun omega ↦ reserveEdgeLaw (G omega) U r hr)
      W k G₀ (fun z ↦ initial z.1) (fun z ↦ later z.1)
      (fun z ↦ reserveEdges (G z.1) U z.2) p r C b := by
  intro Ifix Dfix Efix Rfix hdisj hE
  let K : Omega → FiniteLaw (Sym2 V → Bool) :=
    fun omega ↦ reserveEdgeLaw (G omega) U r hr
  let Old : Omega → Prop :=
    ResidualDistributionEvent initial later Ifix Dfix Efix
  let Reserve : Omega → (Sym2 V → Bool) → Prop :=
    fun omega bits ↦ Rfix ⊆ reserveEdges (G omega) U bits
  have hconditional : ∀ omega, Old omega →
      (K omega).probability (Reserve omega) ≤ r ^ Rfix.card := by
    intro omega _hold
    by_cases hcross : Rfix ⊆ crossingEdges (G omega) U
    · exact le_of_eq (reserveEdgeLaw_probability_subset_reserveEdges
        (G omega) U r hr Rfix hcross)
    · have himpossible : ∀ bits, ¬ Reserve omega bits := by
        intro bits hR
        exact hcross (hR.trans
          (reserveEdges_subset_crossingEdges (G omega) U bits))
      have hzero : (K omega).probability (Reserve omega) = 0 := by
        apply le_antisymm
        · calc
            (K omega).probability (Reserve omega) ≤
                (K omega).probability (fun _ ↦ False) := by
              apply FiniteLaw.probability_mono
              intro bits hbits
              exact himpossible bits hbits
            _ = 0 := FiniteLaw.probability_false _
        · exact zero_le
      rw [hzero]
      exact zero_le
  have hjoint :
      (L.jointBind K).probability (fun z ↦ Old z.1 ∧ Reserve z.1 z.2) ≤
        r ^ Rfix.card * L.probability Old :=
    L.jointBind_probability_and_le K Old Reserve (r ^ Rfix.card)
      hconditional
  have hold := hstrong Ifix Dfix Efix hdisj hE
  have hpowC : C ^ (Ifix.card + Dfix.card + Efix.card) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) := by
    exact pow_le_pow_right₀ hC (by omega)
  have hrpow : r ^ Rfix.card ≤ 1 := pow_le_one₀ (by positivity) hr
  calc
    (L.jointBind fun omega ↦ reserveEdgeLaw (G omega) U r hr).probability
        (ResidualReserveDistributionEvent
          (fun z ↦ initial z.1) (fun z ↦ later z.1)
          (fun z ↦ reserveEdges (G z.1) U z.2)
          Ifix Dfix Efix Rfix) =
        (L.jointBind K).probability
          (fun z ↦ Old z.1 ∧ Reserve z.1 z.2) := by rfl
    _ ≤ r ^ Rfix.card * L.probability Old := hjoint
    _ ≤ r ^ Rfix.card *
        (C ^ (Ifix.card + Dfix.card + Efix.card) *
          (p ^ Efix.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p Dfix + b)) := by gcongr
    _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * r ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b) := by
      calc
        r ^ Rfix.card *
            (C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b)) =
            C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + r ^ Rfix.card * b) := by
          ring
        _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b) := by
          gcongr
          exact mul_le_of_le_one_left (by positivity) hrpow
        _ ≤ C ^
              (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b) := by
          gcongr

end

end Erdos207
