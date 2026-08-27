/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualReserveDistribution

/-! # Joint initial, later, candidate and reserve-edge prescriptions -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem residualReserveCandidateTerm_le
    (lambda C J X b delta : ℝ≥0) (q m a : ℕ)
    (hlambda : lambda ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J) (hm : m ≤ 2 * a) (hq : q ≤ a) :
    lambda ^ q * (C ^ m * (X + b)) + J ^ q * delta ≤
      (max (C ^ 2) J) ^ a * (lambda ^ q * X + b + delta) := by
  let A := max (C ^ 2) J
  have hA : 1 ≤ A := hJ.trans (le_max_right _ _)
  have hCm : C ^ m ≤ A ^ a := by
    calc
      _ ≤ C ^ (2 * a) := pow_le_pow_right₀ hC hm
      _ = (C ^ 2) ^ a := pow_mul _ _ _
      _ ≤ _ := pow_le_pow_left' (le_max_left _ _) _
  have hJq : J ^ q ≤ A ^ a :=
    (pow_le_pow_left' (le_max_right _ _) _).trans (pow_le_pow_right₀ hA hq)
  have hlb : lambda ^ q * b ≤ b := mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hlambda)
  calc
    _ = C ^ m * (lambda ^ q * X + lambda ^ q * b) + J ^ q * delta := by ring
    _ ≤ A ^ a * (lambda ^ q * X + b) + A ^ a * delta :=
      add_le_add (mul_le_mul hCm (add_le_add le_rfl hlb) zero_le zero_le)
        (mul_le_mul_of_nonneg_right hJq zero_le)
    _ = _ := by ring

theorem IsResidualReserveStronglyWellDistributed.jointBind_candidate_prescriptions
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (candidate : Ω → Ξ → TripleSystemOn V) (lambda J delta : ℝ≥0)
    (hlambda : lambda ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hcandidate : ∀ ω, 0 < L.mass ω → ∀ Q,
      (K ω).probability (fun ξ ↦ Q ⊆ candidate ω ξ) ≤ lambda ^ Q.card + J ^ Q.card * delta)
    (Ifix Dfix Qfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (hdis : Disjoint Ifix Dfix) (hE : Efix ⊆ graphEdges G) (hR : Rfix ⊆ Efix) :
    (L.jointBind K).probability (fun z ↦
      ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix Rfix z.1 ∧
        Qfix ⊆ candidate z.1 z.2) ≤
      (max (C ^ 2) J) ^ (Ifix.card + Dfix.card + Qfix.card + Efix.card) *
        (lambda ^ Qfix.card * (p ^ Efix.card * r ^ Rfix.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W k p Dfix) + b + delta) := by
  let Old := ResidualReserveDistributionEvent initial later reserve Ifix Dfix Efix Rfix
  have hjoint := L.jointBind_probability_and_le_on_support K Old
    (fun ω ξ ↦ Qfix ⊆ candidate ω ξ) (lambda ^ Qfix.card + J ^ Qfix.card * delta)
    (fun ω hω _ ↦ hcandidate ω hω Qfix)
  have hold := hstrong Ifix Dfix Efix Rfix hdis hE
  have hRcard := card_le_card hR
  apply hjoint.trans
  calc
    _ = lambda ^ Qfix.card * L.probability Old +
        J ^ Qfix.card * delta * L.probability Old := by ring
    _ ≤ lambda ^ Qfix.card * (C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * r ^ Rfix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W k p Dfix + b)) + J ^ Qfix.card * delta :=
      add_le_add (mul_le_mul_of_nonneg_left hold zero_le)
        (mul_le_of_le_one_right zero_le (L.probability_le_one Old))
    _ ≤ _ := residualReserveCandidateTerm_le lambda C J _ b delta _ _ _ hlambda hC hJ (by omega) (by omega)

end

end Erdos207
