/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialSparsificationReserveLaw
import ErdosProblems.Erdos207.InitialSparsificationStrongLaw

/-!
# Adjoining a deterministic reserve at density one

At reserve density one the reserve prescription costs no probability.  Thus
any initial selected/uncovered product law remains valid after recording an
arbitrary state-dependent reserve.  This elementary observation is useful
for the initial sparsification, whose canonical reserve is precisely the set
of crossing edges that it left uncovered.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsInitialProductBound.toInitialReserveProductBound_one
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)} {p C b : ℝ≥0}
    (h : IsInitialProductBound L selected p C b) (hC : 1 ≤ C) :
    IsInitialReserveProductBound L selected reserve p 1 C b := by
  intro Ifix Efix Rfix
  have hmono : L.probability (fun omega ↦
      Ifix ⊆ selected omega ∧
      (∀ e ∈ Efix, e ∉ (coveredGraph (selected omega)).edgeSet) ∧
      Rfix ⊆ reserve omega) ≤
      L.probability (fun omega ↦
        Ifix ⊆ selected omega ∧
        ∀ e ∈ Efix,
          e ∉ (coveredGraph (selected omega)).edgeSet) := by
    apply L.probability_mono
    intro omega homega
    exact ⟨homega.1, homega.2.1⟩
  refine hmono.trans ((h Ifix Efix).trans ?_)
  have hpow : C ^ (Ifix.card + Efix.card) ≤
      C ^ (Ifix.card + Efix.card + Rfix.card) :=
    pow_le_pow_right' hC (by omega)
  simpa using
    (mul_le_mul_of_nonneg_right hpow
      (show (0 : ℝ≥0) ≤ p ^ Efix.card *
        (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card + b from zero_le))

theorem IsInitialProductBound.toReserveStronglyWellDistributed_one
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)} {selected : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)} {p C b : ℝ≥0}
    (h : IsInitialProductBound L selected p C b) (hC : 1 ≤ C) :
    IsReserveStronglyWellDistributed L W k selected
      (fun _ ↦ (∅ : TripleSystemOn V)) reserve p 1 C b :=
  (h.toInitialReserveProductBound_one hC).toReserveStronglyWellDistributed

end

end Erdos207
