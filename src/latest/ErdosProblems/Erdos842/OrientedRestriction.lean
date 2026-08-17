import ErdosProblems.Erdos842.SurvivorChords

/-!
# Boolean orientations of a triangle chord

For each unoriented chord key `k : Fin 3`, there are exactly two proper nonempty restrictions
of the cyclically directed triangle.  This file chooses the singleton `baseRestriction k` as the
`true` orientation and its complement as the `false` orientation.  It records their complete
boundary vectors and a uniqueness principle suited to constructing canonical survivors.
-/

namespace Erdos842.OrientedRestriction

open Erdos842.Coefficient
open Erdos842.SurvivorChords

/-- The two oriented restrictions above an unoriented chord key.  `true` is the canonical
singleton `baseRestriction`; `false` is its complementary orientation. -/
def orientedRestriction (k : Fin 3) (isBase : Bool) : Finset (Fin 3) :=
  if isBase then baseRestriction k else Finset.univ \ baseRestriction k

/-- The boundary value at the cyclic successor of the chord key. -/
def successorBoundary (isBase : Bool) : ℤ :=
  if isBase then -1 else 1

@[simp] theorem orientedRestriction_true (k : Fin 3) :
    orientedRestriction k true = baseRestriction k := rfl

@[simp] theorem orientedRestriction_false (k : Fin 3) :
    orientedRestriction k false = Finset.univ \ baseRestriction k := rfl

@[simp] theorem successorBoundary_true : successorBoundary true = -1 := rfl

@[simp] theorem successorBoundary_false : successorBoundary false = 1 := rfl

@[simp] theorem successorBoundary_not (isBase : Bool) :
    successorBoundary (!isBase) = -successorBoundary isBase := by
  cases isBase <;> rfl

/-- Both Boolean orientations select at least one directed triangle side. -/
@[simp] theorem orientedRestriction_ne_empty (k : Fin 3) (isBase : Bool) :
    orientedRestriction k isBase ≠ ∅ := by
  decide +revert

/-- Both Boolean orientations omit at least one directed triangle side. -/
@[simp] theorem orientedRestriction_ne_univ (k : Fin 3) (isBase : Bool) :
    orientedRestriction k isBase ≠ (Finset.univ : Finset (Fin 3)) := by
  decide +revert

/-- The two Boolean orientations lie over the requested unoriented chord key. -/
@[simp] theorem unorientedChordKey_orientedRestriction (k : Fin 3) (isBase : Bool) :
    unorientedChordKey (orientedRestriction k isBase) = k := by
  cases isBase <;> simp [orientedRestriction]

/-- The Boolean parameter is recovered by the orientation bit from `SurvivorChords`. -/
@[simp] theorem orientationBit_orientedRestriction (k : Fin 3) (isBase : Bool) :
    orientationBit (orientedRestriction k isBase) = isBase := by
  decide +revert

/-- Each Boolean orientation belongs to the exact two-element fibre over `k`. -/
@[simp] theorem orientedRestriction_mem_restrictionsForChord (k : Fin 3) (isBase : Bool) :
    orientedRestriction k isBase ∈ restrictionsForChord k := by
  simp [mem_restrictionsForChord]

/-- For a fixed chord key, the Boolean orientation parameterization is injective. -/
theorem orientedRestriction_injective (k : Fin 3) :
    Function.Injective (orientedRestriction k) := by
  intro a b hab
  have := congrArg orientationBit hab
  simpa using this

/-- Flipping the Boolean orientation complements the selected triangle sides. -/
@[simp] theorem orientedRestriction_not (k : Fin 3) (isBase : Bool) :
    orientedRestriction k (!isBase) =
      Finset.univ \ orientedRestriction k isBase := by
  decide +revert

/-- The boundary vanishes at the unoriented chord key. -/
@[simp] theorem triangleBoundary_orientedRestriction_key (k : Fin 3) (isBase : Bool) :
    triangleBoundary (orientedRestriction k isBase) k = 0 := by
  decide +revert

/-- At `k + 1` cyclically, the boundary is `-1` for the base orientation and `+1` for its
complement. -/
@[simp] theorem triangleBoundary_orientedRestriction_succ
    (k : Fin 3) (isBase : Bool) :
    triangleBoundary (orientedRestriction k isBase) (triSucc k) =
      successorBoundary isBase := by
  decide +revert

/-- At `k + 2` cyclically, the boundary has the opposite sign from the value at `k + 1`. -/
@[simp] theorem triangleBoundary_orientedRestriction_pred
    (k : Fin 3) (isBase : Bool) :
    triangleBoundary (orientedRestriction k isBase) (triPred k) =
      -successorBoundary isBase := by
  decide +revert

/-- Complete boundary vector of a Boolean oriented restriction. -/
theorem triangleBoundary_orientedRestriction (k j : Fin 3) (isBase : Bool) :
    triangleBoundary (orientedRestriction k isBase) j =
      if j = k then 0
      else if j = triSucc k then successorBoundary isBase
      else -successorBoundary isBase := by
  decide +revert

/-- A proper nonempty restriction is uniquely determined by its unoriented key and its boundary
value at the cyclic successor of that key. -/
theorem eq_orientedRestriction_of_key_of_boundary_succ
    (S : Finset (Fin 3)) (k : Fin 3) (isBase : Bool)
    (hne : S ≠ ∅) (hfull : S ≠ Finset.univ)
    (hkey : unorientedChordKey S = k)
    (hsucc : triangleBoundary S (triSucc k) = successorBoundary isBase) :
    S = orientedRestriction k isBase := by
  decide +revert

/-- Exact characterization form of the uniqueness theorem. -/
theorem eq_orientedRestriction_iff_boundary_succ
    (S : Finset (Fin 3)) (k : Fin 3) (isBase : Bool)
    (hne : S ≠ ∅) (hfull : S ≠ Finset.univ)
    (hkey : unorientedChordKey S = k) :
    S = orientedRestriction k isBase ↔
      triangleBoundary S (triSucc k) = successorBoundary isBase := by
  constructor
  · rintro rfl
    exact triangleBoundary_orientedRestriction_succ k isBase
  · exact eq_orientedRestriction_of_key_of_boundary_succ S k isBase hne hfull hkey

end Erdos842.OrientedRestriction
