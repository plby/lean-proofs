/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5TwoPowTheorem
import ErdosProblems.Erdos186.CFP.Bilu.Section94RankThresholdBoundary

/-!
# The source `2^(d+1-delta)` affine-slice theorem

Freiman's arbitrary-gap `2^n` theorem is specialized at rank `d + 1`.
Since every positive `delta` makes `2^(d+1-delta)` strictly smaller than
`2^(d+1)`, half of that positive gap gives the strict hypothesis required by
the affine-slice theorem while still accepting the source's non-strict
doubling estimate.
-/

namespace Erdos186.CFP.Bilu.Section5RpowAffineSlice

open Module
open Section7FreimanMap Section5TwoN Section5TwoPowTheorem
  Section94RankThresholdBoundary

noncomputable section

/-- The source-facing generalized Freiman theorem in precisely the form
consumed by the Section 5.5 sorted-tail argument. -/
theorem exists_rpowAffineSliceStatement
    (d : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ proportionConstant : ℕ,
      RpowAffineSliceStatement d proportionConstant delta := by
  let sourceCoefficient : ℝ :=
    Real.rpow 2 ((d : ℝ) + 1 - delta)
  let leadingCoefficient : ℝ := ((2 ^ (d + 1) : ℕ) : ℝ)
  let epsilon : ℝ := (leadingCoefficient - sourceCoefficient) / 2
  have hexponent : (d : ℝ) + 1 - delta < (d + 1 : ℕ) := by
    norm_num
    linarith
  have hsource_lt : sourceCoefficient < leadingCoefficient := by
    have h := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hexponent
    change Real.rpow 2 ((d : ℝ) + 1 - delta) <
      (((2 ^ (d + 1) : ℕ) : ℝ))
    calc
      Real.rpow 2 ((d : ℝ) + 1 - delta) <
          Real.rpow 2 ((d + 1 : ℕ) : ℝ) := h
      _ = (((2 ^ (d + 1) : ℕ) : ℝ)) := by
        exact (Real.rpow_natCast (2 : ℝ) (d + 1)).trans (by
          norm_num [Nat.cast_pow])
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  obtain ⟨proportionConstant, hslice⟩ :=
    exists_constant_affineSlice_twoPowGap
      (d + 1) (by omega) epsilon hepsilon
  refine ⟨proportionConstant, ?_⟩
  intro rank hdrank S hS hdouble
  have hfinrank : d + 1 ≤ finrank ℝ (Fin rank → ℝ) := by
    simpa using hdrank
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hcoefficient : sourceCoefficient < leadingCoefficient - epsilon := by
    dsimp [epsilon]
    linarith
  have hstrict : ((pairSumset S).card : ℝ) <
      (leadingCoefficient - epsilon) * S.card :=
    hdouble.trans_lt (mul_lt_mul_of_pos_right hcoefficient hcard)
  exact hslice (Fin rank → ℝ) hfinrank S hS (by
    simpa [leadingCoefficient] using hstrict)

end

end Erdos186.CFP.Bilu.Section5RpowAffineSlice

#print axioms
  Erdos186.CFP.Bilu.Section5RpowAffineSlice.exists_rpowAffineSliceStatement
