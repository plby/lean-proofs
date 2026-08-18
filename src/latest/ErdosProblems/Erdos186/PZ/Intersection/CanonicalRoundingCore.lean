/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceCoreBounds

/-!
# The canonical CFP rounding core

Equation (15) rounds only with generators not used by the small reserved
absorber.  The canonical choice is therefore `W.core \ W.reserved`.  This
file discharges its set-theoretic and coordinate-bound properties from an
actual enhanced CFP witness.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The part of the enhanced CFP core left for zonotope rounding. -/
def canonicalRoundingCore {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    Finset (LatticePoint d) :=
  W.core \ W.reserved

theorem canonicalRoundingCore_subset_core
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    canonicalRoundingCore W ⊆ W.core := by
  exact Finset.sdiff_subset

theorem reserved_disjoint_canonicalRoundingCore
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    Disjoint W.reserved (canonicalRoundingCore W) := by
  exact disjoint_sdiff_self_right

theorem canonicalRoundingCore_subset_input
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    canonicalRoundingCore W ⊆ A := by
  exact (canonicalRoundingCore_subset_core W).trans W.core_subset

/-- The canonical rounding core of a selected translated candidate inherits
the source coefficient-box coordinate width. -/
theorem canonicalRoundingCore_coordinateBound_of_identifiedTranslate
    {ambient r s D k loss : ℕ}
    (P : GAP ambient r) {X : Finset (LatticePoint r)}
    {x : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (hx : x ∈ (gapCoefficientBox P).carrier)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X x)
      s D k loss) :
    ∀ y ∈ canonicalRoundingCore W, ∀ i,
      |(y i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  intro y hy i
  exact enhancedCore_coordinateBound_of_identifiedTranslate P hX hx W y
    (canonicalRoundingCore_subset_core W hy) i

end

end Erdos186.PZ.Intersection
