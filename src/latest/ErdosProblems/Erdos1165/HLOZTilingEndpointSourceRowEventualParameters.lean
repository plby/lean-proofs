/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCheckerOriginSafeProp49Family
import ErdosProblems.Erdos1165.HLOZTilingEndpointSourceRowUpperData

/-!
# Uniform eventual parameters for all physical source rows

All window, prefix-origin, and external-coordinate side conditions can be
chosen uniformly over the finite low mesh.  Final rankwise source coverage
therefore does not carry a separate checker width hypothesis.
-/

open Filter

namespace Erdos1165.HLOZTilingEndpointSourceRowEventualParameters

open HLOZCheckerOriginSafeProp49Family
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open LazyDecomposition ScreeningInstantiation

/-- All deterministic arithmetic needed to build every physical source row
at one level. -/
structure TilingEndpointSourceRowParametersAt (m : ℕ) : Prop where
  m_gt_one : 1 < m
  width : 3 ≤ shellWidth48 m
  shell_arithmetic : ShellZeroWindowArithmeticAt m
  external_arithmetic : ShellZeroExternalWindowArithmeticAt m
    (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)
  window : ∀ a ∈ lowGapMesh, Prop49WindowArithmeticAt m a

/-- One level threshold simultaneously supplies the arithmetic for every
low cell and all six physical rows. -/
theorem eventually_tilingEndpointSourceRowParametersAt :
    ∀ᶠ m : ℕ in atTop, TilingEndpointSourceRowParametersAt m := by
  have hall : ∀ᶠ m : ℕ in atTop,
      ∀ a ∈ lowGapMesh, Prop49WindowArithmeticAt m a :=
    (Finset.eventually_all lowGapMesh).2 fun a ha ↦
      eventually_prop49WindowArithmeticAt a ha
  filter_upwards [eventually_ge_atTop (2 : ℕ),
      eventually_three_le_shellWidth48,
      eventually_shellZeroWindowArithmeticAt,
      eventually_shellZeroExternalWindowArithmetic48, hall] with
      m hm hwidth hshell hexternal hwindow
  exact ⟨by omega, hwidth, hshell, hexternal, hwindow⟩

end Erdos1165.HLOZTilingEndpointSourceRowEventualParameters
