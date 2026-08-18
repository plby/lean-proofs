/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.AnisotropicAdjugateCapacity

/-!
# Positive-dimension anisotropic adjugate capacity

The determinant argument is naturally written in dimension `n + 1`.  This
small adapter exposes the same source-control-box theorem for an arbitrary
positive dimension, which is the form returned by the irreducibility
selection.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

theorem enhancedWitness_anisotropic_errorBox_of_sourceControlBox_pos
    {d s D k loss margin ambient : ℕ}
    {X : Finset (LatticePoint d)}
    (hd : 0 < d)
    (W : CFP.EnhancedCFPWitness X s D k loss)
    (hrank : W.rank = d) (S : GAP ambient d) (m : ℕ)
    (hm : 0 < m) (t : LatticePoint d)
    {radii : Fin d → ℕ}
    (hcentered : (rankCastGAP W.progression hrank).Centered radii)
    (hcontain : (rankCastGAP W.progression hrank).carrier ⊆
      CFP.translate t (controlIntegerBox S m).carrier)
    (gamma rho : ℝ) (hgamma : 0 < gamma) (hrho : 0 ≤ rho)
    (hvolume : gamma * (S.volume : ℝ) ≤
      ((rankCastGAP W.progression hrank).volume : ℝ))
    (hdet : (stepMatrix (rankCastGAP W.progression hrank)).det ≠ 0)
    (hhierarchy :
      rho * (((d.factorial * (2 * m) ^ (d - 1) *
        3 ^ d : ℕ) : ℝ)) ≤ gamma * margin) :
    ∀ e : LatticePoint d,
      e ∈ gapStepLattice W.progression →
      (∀ j, |(e j : ℝ)| ≤ rho * (S.widths j - 1 : ℕ)) →
      e ∈ (W.progression.dilate margin).carrier := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact enhancedWitness_anisotropic_errorBox_of_sourceControlBox
    W hrank S m hm t hcentered hcontain gamma rho hgamma hrho hvolume
      hdet hhierarchy

end

end Erdos186.PZ.Intersection
