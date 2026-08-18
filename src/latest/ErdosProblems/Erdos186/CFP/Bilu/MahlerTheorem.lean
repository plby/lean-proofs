/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.BasisReduction
import ErdosProblems.Erdos186.CFP.Bilu.MinimaAttainment

/-!
# Mahler's basis theorem

This file assembles compatible attainment of the successive minima, the
saturated-flag basis construction, and Cassels' centered coefficient
reduction.  The result is the exact basis lemma used by Bilu, including the
sharp first factor `1` and the factors `i / 2` thereafter (in one-based
indexing).
-/

namespace Erdos186.CFP.Bilu.Mahler

open Module

/-- **Mahler's basis theorem** in the exact form of Bilu's Lemma 2.1. -/
theorem mahlerBasisStatement : MahlerBasisStatement := by
  intro n p hp
  obtain ⟨x, hxli, hxmin⟩ :=
    exists_independent_integralPoint_le_successiveMinimum p hp
  obtain ⟨b, a, hred⟩ :=
    exists_centeredReduction_of_linearIndependent x hxli
  exact ⟨b,
    isMahlerBasis_of_centeredReduction_of_minima_upper p x b a hred hxmin⟩

/-- Pointwise existential form of Mahler's basis theorem. -/
theorem exists_isMahlerBasis {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n), IsMahlerBasis p b :=
  mahlerBasisStatement n p hp

end Erdos186.CFP.Bilu.Mahler
