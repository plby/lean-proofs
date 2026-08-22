/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaCreationSlots

/-!
# Source/replacement split of the restricted oriented Theta screen

The physical restricted screen uses `I₁ ∪ I₀`.  The two parts have
different clock semantics: `I₁` is below the current level and is handled
by the rank-stable Proposition 4.5 product, whereas `I₀` is the artificial
above-level comparison window and is handled by the actual-rank-increment
replacement family.  This file makes that split pathwise explicit.
-/

namespace Erdos1165.HLOZSourceOrientedThetaWindowSplit

open HLOZShellZeroReplacementWindows HLOZSourceOrientedThetaBalance
open HLOZThetaSourceBalance
open LazyDecomposition TilingOrientedShellZeroSourcePartition
open TilingShellZeroSourcePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def orientedRestrictedThetaSourceAtCreation (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (s : WalkPath) : Finset Point :=
  (orientedTilingThetaAtCreation t o m k w externalLow externalHigh s).filter
    fun b ↦ localTime s (creationTimeNat m k s) b ∈
      shellZeroSourceTotalWindow m w

def orientedRestrictedThetaReplacementAtCreation (t : DominoTiling)
    (o : Orientation) (m k w externalLow externalHigh : ℕ)
    (s : WalkPath) : Finset Point :=
  (orientedTilingThetaAtCreation t o m k w externalLow externalHigh s).filter
    fun b ↦ localTime s (creationTimeNat m k s) b ∈
      shellZeroReplacementTotalWindow m w

theorem orientedTilingThetaAtCreation_eq_source_union_replacement
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    orientedTilingThetaAtCreation t o m k w externalLow externalHigh s =
      orientedRestrictedThetaSourceAtCreation t o m k w externalLow
          externalHigh s ∪
        orientedRestrictedThetaReplacementAtCreation t o m k w externalLow
          externalHigh s := by
  classical
  apply Finset.ext
  intro b
  rw [Finset.mem_union, orientedRestrictedThetaSourceAtCreation,
    orientedRestrictedThetaReplacementAtCreation, Finset.mem_filter,
    Finset.mem_filter]
  constructor
  · intro hb
    have hbVTwo := hb
    rw [orientedTilingThetaAtCreation, orientedTilingThetaBases,
      Finset.mem_filter, mem_orientedTilingVTwoBases_iff,
      tilingVTwoBases, Finset.mem_filter] at hbVTwo
    have hbWindow := hbVTwo.1.1.2.2
    rw [Finset.mem_union] at hbWindow
    rcases hbWindow with hs | hr
    · exact Or.inl ⟨hb, hs⟩
    · exact Or.inr ⟨hb, hr⟩
  · rintro (⟨hb, _⟩ | ⟨hb, _⟩) <;> exact hb

theorem orientedRestrictedThetaSourceAtCreation_subset
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    orientedRestrictedThetaSourceAtCreation t o m k w externalLow
        externalHigh s ⊆
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s :=
  Finset.filter_subset _ _

theorem orientedRestrictedThetaReplacementAtCreation_subset
    (t : DominoTiling) (o : Orientation)
    (m k w externalLow externalHigh : ℕ) (s : WalkPath) :
    orientedRestrictedThetaReplacementAtCreation t o m k w externalLow
        externalHigh s ⊆
      orientedTilingThetaAtCreation t o m k w externalLow externalHigh s :=
  Finset.filter_subset _ _

end

end Erdos1165.HLOZSourceOrientedThetaWindowSplit
