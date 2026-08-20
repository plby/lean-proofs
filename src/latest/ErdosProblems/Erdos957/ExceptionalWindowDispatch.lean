import ErdosProblems.Erdos957.RoleCollisions

/-!
# Finite cyclic dispatch for the exceptional Erdős 957 arrivals

This file contains the source-position bookkeeping shared by the two
exceptional collision kernels.  It turns the genuine seven-window
membership certificate into the six possible noncentral cyclic orbit
positions.  No collision or capacity conclusion is assumed here.
-/

noncomputable section

namespace Erdos957ExceptionalWindowDispatch

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P}

/-- A source distinct from the centre of its seven-window occupies one of
the three predecessor or three successor slots.  The statement is phrased
at `sourceIndex`, the exact hull subtype used by all normalized charts. -/
lemma sourceIndex_orbit_cases_of_mem_seven_window
    {s t : Source P W}
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hne : s ≠ t) :
    sourceIndex P W t.1 t.property =
        (P.next⁻¹ ^ 3) (sourceIndex P W s.1 s.property) ∨
      sourceIndex P W t.1 t.property =
        (P.next⁻¹ ^ 2) (sourceIndex P W s.1 s.property) ∨
      sourceIndex P W t.1 t.property =
        P.next⁻¹ (sourceIndex P W s.1 s.property) ∨
      sourceIndex P W t.1 t.property =
        P.next (sourceIndex P W s.1 s.property) ∨
      sourceIndex P W t.1 t.property =
        (P.next ^ 2) (sourceIndex P W s.1 s.property) ∨
      sourceIndex P W t.1 t.property =
        (P.next ^ 3) (sourceIndex P W s.1 s.property) := by
  rcases Finset.mem_image.mp htWindow with ⟨j, -, hj⟩
  have hsource : sourceIndex P W t.1 t.property =
      sevenShift P.next j (sourceIndex P W s.1 s.property) := by
    apply Subtype.ext
    exact hj.symm
  fin_cases j
  · left
    simpa using hsource
  · right; left
    simpa using hsource
  · right; right; left
    simpa using hsource
  · exfalso
    have hidx : sourceIndex P W t.1 t.property =
        sourceIndex P W s.1 s.property := by
      simpa using hsource
    apply hne
    exact Subtype.ext (congrArg Subtype.val hidx).symm
  · right; right; right; left
    simpa using hsource
  · right; right; right; right; left
    simpa using hsource
  · right; right; right; right; right
    simpa using hsource

end Erdos957ExceptionalWindowDispatch

#print axioms Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
