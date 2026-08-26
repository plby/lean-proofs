import ErdosProblems.Erdos556.Basic

/-!
# The three-dimensional cube profiles

A coordinate is either fixed to a Boolean value or free. These are the
27 profiles used in the structural reduction of a three-colouring.
-/

namespace Erdos556

open Finset

abbrev CubeVertex := Fin 3 → Bool
abbrev CubeProfile := Fin 3 → Option Bool

def profileVertices (p : CubeProfile) : Finset CubeVertex :=
  univ.filter (fun v => ∀ i, p i = none ∨ p i = some (v i))

def profileDimension (p : CubeProfile) : ℕ :=
  (univ.filter (fun i => p i = none)).card

def cubeFace (i : Fin 3) (b : Bool) : CubeProfile :=
  fun j => if j = i then some b else none

def wholeCube : CubeProfile := fun _ => none

theorem profileDimension_le_three (p : CubeProfile) : profileDimension p ≤ 3 := by
  have h := card_le_univ (univ.filter (fun i : Fin 3 => p i = none))
  simpa only [profileDimension, Fintype.card_fin] using h

theorem profileVertices_card : ∀ p : CubeProfile,
    (profileVertices p).card = 2 ^ profileDimension p := by
  decide

theorem cubeFace_dimension : ∀ (i : Fin 3) (b : Bool), profileDimension (cubeFace i b) = 2 := by
  decide

theorem wholeCube_dimension : profileDimension wholeCube = 3 := by decide

theorem profileDimension_three_iff : ∀ p : CubeProfile,
    profileDimension p = 3 ↔ p = wholeCube := by
  decide

theorem profileDimension_two_iff : ∀ p : CubeProfile,
    profileDimension p = 2 ↔ ∃ (i : Fin 3) (b : Bool), p = cubeFace i b := by
  decide

#print axioms profileVertices_card
#print axioms profileDimension_two_iff

end Erdos556
