/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.LatticeIntersection
import ErdosProblems.Erdos186.PZ.Intersection.Lattice

/-!
# From finite-index sublattices to a common covering radius

This file connects the finite-index lattice intersection theorem to the
covering-radius interface used by the Pham--Zakharov intersection argument.
The radius is the product of the two discrete covolumes (or any larger
product of supplied upper bounds).
-/

namespace Erdos186.PZ.Intersection

open Erdos186.LatticeIntersection

noncomputable section

set_option autoImplicit false

/-- Two full-rank sublattices have a common covering radius bounded by the
product of their covolumes. -/
theorem hasCommonCoveringRadius_of_fullRank {d : ℕ}
    (L K : Sublattice d) (hL : FullRank L) (hK : FullRank K) :
    HasCommonCoveringRadius (L : Set (LatticePoint d))
      (K : Set (LatticePoint d)) (covolume L * covolume K) := by
  intro x
  obtain ⟨y, hyL, hyK, hybox⟩ :=
    exists_common_mem_halfOpenBox hL hK le_rfl le_rfl x
  refine ⟨y, hyL, hyK, ?_⟩
  intro i
  have hi := hybox i
  rw [abs_le]
  constructor <;> omega

/-- Version with externally supplied covolume bounds. -/
theorem hasCommonCoveringRadius_of_covolume_le {d C₁ C₂ : ℕ}
    (L K : Sublattice d) (hL : FullRank L) (hK : FullRank K)
    (hLcov : covolume L ≤ C₁) (hKcov : covolume K ≤ C₂) :
    HasCommonCoveringRadius (L : Set (LatticePoint d))
      (K : Set (LatticePoint d)) (C₁ * C₂) := by
  intro x
  obtain ⟨y, hyL, hyK, hybox⟩ :=
    exists_common_mem_halfOpenBox hL hK hLcov hKcov x
  refine ⟨y, hyL, hyK, ?_⟩
  intro i
  have hi := hybox i
  rw [abs_le]
  constructor <;> omega

end

end Erdos186.PZ.Intersection
