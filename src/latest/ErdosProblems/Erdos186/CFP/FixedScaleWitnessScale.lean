/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness

/-!
# Weakening the denominator of a fixed-scale witness

Increasing the denominator only weakens the lower comparison between the
reserve parameter and the dilation scale.  This is the direct fixed-witness
analogue of `PreprocessedReserveCertificate.increaseScaleDen`.
-/

namespace Erdos186.CFP

noncomputable section

namespace FixedScaleWitness

/-- Replace the fixed scale denominator by a larger positive denominator. -/
def increaseScaleDen
    {d s D k loss scaleNum scaleDen scaleDen' : ℕ}
    {A : Finset (LatticePoint d)}
    (W : FixedScaleWitness A s D k loss scaleNum scaleDen)
    (hle : scaleDen ≤ scaleDen') (hpos : 0 < scaleDen') :
    FixedScaleWitness A s D k loss scaleNum scaleDen' := by
  have hscaleLower : W.enhanced.scaleNum * s ≤ scaleDen' * k := by
    calc
      W.enhanced.scaleNum * s ≤ W.enhanced.scaleDen * k :=
        W.enhanced.scale_lower
      _ = scaleDen * k := by rw [W.scaleDen_eq]
      _ ≤ scaleDen' * k := Nat.mul_le_mul_right k hle
  refine ⟨{ W.enhanced with
    scaleDen := scaleDen'
    scaleDen_pos := hpos
    scale_lower := hscaleLower }, ?_, rfl⟩
  exact W.scaleNum_eq

end FixedScaleWitness

end

end Erdos186.CFP

#print axioms Erdos186.CFP.FixedScaleWitness.increaseScaleDen
