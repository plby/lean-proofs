/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReferencePromotion

/-!
# Reference-independent literal traces of native occurrences

The data type keeps only chronological vertices and directions. Admissible
traces will still require an actual valid native occurrence. At a fixed
reference and source the erasure is injective, so it cannot create a large
hammock by counting certificates for the same route several times.
-/

namespace Erdos599.ColouredSafeTrace

open Set DirectedPath Alternating ColouredSafeReverseReachability

universe u

inductive Trace (V : Type u) : Type u
  | finite (length : ℕ) (vertex : Fin (length + 1) → V)
      (direction : Fin length → Direction)
  | infinite (vertex : ℕ → V) (direction : ℕ → Direction)

variable {V : Type u} {Gamma : DWeb V}
variable {W Y : Set Gamma.DPath} {s : V}

def Trace.vertexSet (Q : Trace V) : Set V :=
  match Q with
  | .finite _ vertex _ => Set.range vertex
  | .infinite vertex _ => Set.range vertex

def Trace.terminal? (Q : Trace V) : Option V :=
  match Q with
  | .finite n vertex _ => some (vertex (Fin.last n))
  | .infinite _ _ => none

def ofOccurrence (A : CurrentSafeOccurrence W Y s) : Trace V :=
  match A with
  | .finite _ Q .. => .finite Q.length Q.vertex Q.direction
  | .infinite Q .. => .infinite Q.vertex Q.direction

@[simp] theorem ofOccurrence_vertexSet (A : CurrentSafeOccurrence W Y s) :
    (ofOccurrence A).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem ofOccurrence_terminal? (A : CurrentSafeOccurrence W Y s) :
    (ofOccurrence A).terminal? = A.terminal? := by
  cases A with
  | infinite Q hQ hfirst => rfl
  | finite t Q hQ hfirst hlast =>
      exact congrArg some hlast

theorem Trace.vertexSet_countable (Q : Trace V) : Q.vertexSet.Countable := by
  cases Q with
  | infinite vertex direction => exact Set.countable_range vertex
  | finite n vertex direction => exact (Set.finite_range vertex).countable

/-- Only proof fields and a terminal already determined by the word are erased. -/
theorem ofOccurrence_injective :
    Function.Injective (ofOccurrence (W := W) (Y := Y) (s := s)) := by
  intro A B h
  cases A with
  | infinite Q hQ hfirst =>
      cases B with
      | finite t P hP hpfirst hplast => cases h
      | infinite P hP hpfirst =>
          rcases Q with ⟨v, d, hspec, hinj⟩
          rcases P with ⟨w, f, hspec', hinj'⟩
          change Trace.infinite v d = Trace.infinite w f at h
          cases h
          rfl
  | finite t Q hQ hfirst hlast =>
      cases B with
      | infinite P hP hpfirst => cases h
      | finite r P hP hpfirst hplast =>
          rcases Q with ⟨n, v, d, hspec, hinj⟩
          rcases P with ⟨m, w, f, hspec', hinj'⟩
          change Trace.finite n v d = Trace.finite m w f at h
          cases h
          have htr : t = r := hlast.symm.trans hplast
          cases htr
          rfl

open Cardinal Ladder Blueprint DWeb.KappaLadder.Deferred
open ColouredSafeEndpointReference ColouredSafeEndpointStageReference

variable {kappa : Cardinal.{u}} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa} {e : Option V}

@[simp] theorem ofOccurrence_promote (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (stageReference hL a s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    ofOccurrence (A.retypeEndpointLimitReference hL hRoof) = ofOccurrence A := by
  cases A <;> rfl

@[simp] theorem ofOccurrence_localize (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence W (reference L.limitWarp s e) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    ofOccurrence (A.retypeEndpointStageReference hL hRoof) = ofOccurrence A := by
  cases A <;> rfl

#print axioms ofOccurrence_injective
#print axioms ofOccurrence_promote
#print axioms ofOccurrence_localize

end Erdos599.ColouredSafeTrace
