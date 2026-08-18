/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SideTarget
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice

/-!
# Casting a selected progression to square rank

Lemma 11 returns an equality between the selected displayed rank and the
ambient coefficient dimension.  These helpers transport the selected GAP
across that equality and record that its carrier, volume, properness,
nondegeneracy, and generated step lattice are unchanged.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Regard a rank-`r` progression in `Z^n` as square after a proof `r=n`. -/
def rankCastGAP {n r : ℕ} (P : GAP n r) (h : r = n) : GAP n n := by
  subst r
  exact P

theorem rankCastGAP_carrier {n r : ℕ} (P : GAP n r) (h : r = n) :
    (rankCastGAP P h).carrier = P.carrier := by
  subst r
  rfl

theorem rankCastGAP_volume {n r : ℕ} (P : GAP n r) (h : r = n) :
    (rankCastGAP P h).volume = P.volume := by
  subst r
  rfl

theorem rankCastGAP_dilate_carrier {n r k : ℕ} (P : GAP n r)
    (h : r = n) :
    ((rankCastGAP P h).dilate k).carrier = (P.dilate k).carrier := by
  subst r
  rfl

theorem rankCastGAP_stepLattice {n r : ℕ} (P : GAP n r) (h : r = n) :
    stepLattice (rankCastGAP P h) = gapStepLattice P := by
  subst r
  rfl

theorem rankCastGAP_nondegenerate {n r : ℕ} {P : GAP n r}
    (h : r = n) (hP : P.Nondegenerate) :
    (rankCastGAP P h).Nondegenerate := by
  subst r
  exact hP

theorem rankCastGAP_symmetric {n r : ℕ} {P : GAP n r}
    (h : r = n) (hP : P.Symmetric) :
    (rankCastGAP P h).Symmetric := by
  subst r
  exact hP

theorem rankCastGAP_dilate_proper {n r k : ℕ} {P : GAP n r}
    (h : r = n) (hP : (P.dilate k).Proper) :
    ((rankCastGAP P h).dilate k).Proper := by
  subst r
  exact hP

end

end Erdos186.PZ.Intersection
