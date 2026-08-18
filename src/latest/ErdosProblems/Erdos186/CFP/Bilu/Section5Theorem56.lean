/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5ProjectionSlice

/-!
# Bilu Theorem 5.6 from Freiman's rank-dimensional `2r` theorem

Theorem 5.1 is the genuinely geometric input: in an ambient space of rank
`r`, doubling strictly below `(2*r - 1)` forces a positive proportion into
a proper affine plane.  This file records that input as a proposition and
proves Bilu's generalized Theorem 5.6 from it, using the generic projection
and pullback developed in the preceding files.

No conclusion is weakened in this reduction: the proportion constant is
unchanged, and the returned source plane has dimension strictly below `r`.
-/

namespace Erdos186.CFP.Bilu.Section5Theorem56

open Set Module Submodule
open Section7FreimanMap Section5TwoN Section5GenericProjection
  Section5ProjectionSlice

noncomputable section

universe u

/-- Exact natural-cardinality form of Freiman's Theorem 5.1 with
`epsilon = 1` in rank `rank`. -/
def RankTwoNStatement (rank proportionConstant : ℕ) : Prop :=
  ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [DecidableEq W],
    finrank ℝ W = rank →
    ∀ S : Finset W, S.Nonempty →
      (pairSumset S).card < (2 * rank - 1) * S.card →
      Nonempty (AffineSliceWitness rank proportionConstant S)

/-- The all-ranks assertion supplied by Freiman's Theorem 5.1.  The
proportion constant may depend on the rank, but not on the finite set or
its ambient realization. -/
def TwoNTheoremStatement : Prop :=
  ∀ rank : ℕ, 0 < rank →
    ∃ proportionConstant : ℕ,
      RankTwoNStatement.{u} rank proportionConstant

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]

local instance quotientDecidableEq (A : Submodule ℝ V) :
    DecidableEq (V ⧸ A) := Classical.decEq _

local instance finiteDimensionalSubmoduleIsClosed (A : Submodule ℝ V) :
    IsClosed (A : Set V) := A.closed_of_finiteDimensional

/-- Bilu Theorem 5.6, with a fixed source constant, follows from the
rank-dimensional Theorem 5.1 with exactly that same constant. -/
theorem exists_affineSlice_of_rankTwoN
    {rank proportionConstant : ℕ}
    (hTwoN : RankTwoNStatement.{u} rank proportionConstant)
    (S : Finset V) (hS : S.Nonempty)
    (hrank : 0 < rank) (hrank_le : rank ≤ finrank ℝ V)
    (hdouble :
      (pairSumset S).card < (2 * rank - 1) * S.card) :
    Nonempty (AffineSliceWitness rank proportionConstant S) := by
  let P : GenericProjection S rank := genericProjection S rank
  have hquotientRank : finrank ℝ (V ⧸ P.kernel) = rank :=
    P.finrank_quotient_eq hrank_le
  have hquotientNonempty : (S.image P.kernel.mkQ).Nonempty := hS.image _
  have hsourceCard : (S.image P.kernel.mkQ).card = S.card :=
    Finset.card_image_of_injOn (P.mkQ_injOn hS hrank)
  have hquotientDouble :
      (pairSumset (S.image P.kernel.mkQ)).card <
        (2 * rank - 1) * (S.image P.kernel.mkQ).card := by
    rw [card_pairSumset_image_mkQ P hrank, hsourceCard]
    exact hdouble
  have hW : Nonempty (AffineSliceWitness rank proportionConstant
      (S.image P.kernel.mkQ)) :=
    hTwoN (V ⧸ P.kernel) hquotientRank
      (S.image P.kernel.mkQ) hquotientNonempty hquotientDouble
  exact exists_affineSlice_of_quotient P hS hrank hW

/-- Existential-constant form of generalized Theorem 5.6. -/
theorem exists_constant_affineSlice_of_twoNTheorem
    (hTwoN : TwoNTheoremStatement.{u})
    (rank : ℕ) (hrank : 0 < rank) :
    ∃ proportionConstant : ℕ,
      ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W]
        [FiniteDimensional ℝ W] [DecidableEq W],
        rank ≤ finrank ℝ W →
        ∀ S : Finset W, S.Nonempty →
          (pairSumset S).card < (2 * rank - 1) * S.card →
          Nonempty (AffineSliceWitness rank proportionConstant S) := by
  obtain ⟨proportionConstant, hRank⟩ := hTwoN rank hrank
  refine ⟨proportionConstant, ?_⟩
  intro W _ _ _ _ hrank_le S hS hdouble
  exact exists_affineSlice_of_rankTwoN hRank S hS hrank hrank_le hdouble

end


end Erdos186.CFP.Bilu.Section5Theorem56

#print axioms Erdos186.CFP.Bilu.Section5Theorem56.exists_affineSlice_of_rankTwoN
#print axioms Erdos186.CFP.Bilu.Section5Theorem56.exists_constant_affineSlice_of_twoNTheorem
