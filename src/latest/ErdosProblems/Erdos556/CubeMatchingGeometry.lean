import ErdosProblems.Erdos556.CubeGeometry

/-! Encoding a cube perfect matching by its directions at the four even vertices. -/

namespace Erdos556

open Finset

def evenCubeVertex (i : Fin 4) : CubeVertex :=
  ![![false, false, false], ![false, true, true], ![true, false, true], ![true, true, false]] i

def matchingProfile (i : Fin 4) (a : Fin 3) : CubeProfile :=
  fun j => if j = a then none else some (evenCubeVertex i j)

def oddCubeEnd (i : Fin 4) (a : Fin 3) : CubeVertex :=
  fun j => if j = a then !(evenCubeVertex i j) else evenCubeVertex i j

theorem matchingProfile_dimension : ∀ (i : Fin 4) (a : Fin 3),
    profileDimension (matchingProfile i a) = 1 := by decide

theorem evenCubeVertex_mem_matchingProfile : ∀ (i : Fin 4) (a : Fin 3),
    evenCubeVertex i ∈ profileVertices (matchingProfile i a) := by decide

theorem oddCubeEnd_mem_matchingProfile : ∀ (i : Fin 4) (a : Fin 3),
    oddCubeEnd i a ∈ profileVertices (matchingProfile i a) := by decide

theorem matchingProfile_exists : ∀ p : CubeProfile, profileDimension p = 1 →
    ∃ (i : Fin 4) (a : Fin 3), p = matchingProfile i a := by decide

theorem matchingProfile_pair_injective :
    Function.Injective (fun p : Fin 4 × Fin 3 => matchingProfile p.1 p.2) := by decide

theorem evenCubeVertex_in_matchingProfile_iff : ∀ (i j : Fin 4) (a : Fin 3),
    evenCubeVertex i ∈ profileVertices (matchingProfile j a) ↔ i = j := by decide

def profileOppositeAt (p q : CubeProfile) (i : Fin 3) : Prop :=
  (p i = some false ∧ q i = some true) ∨ (p i = some true ∧ q i = some false)

instance (p q : CubeProfile) (i : Fin 3) : Decidable (profileOppositeAt p q i) :=
  inferInstanceAs (Decidable ((p i = some false ∧ q i = some true) ∨
    (p i = some true ∧ q i = some false)))

def uniqueProfileSeparator (p q : CubeProfile) (i : Fin 3) : Prop :=
  profileOppositeAt p q i ∧ ∀ j, j ≠ i → ¬ profileOppositeAt p q j

instance (p q : CubeProfile) (i : Fin 3) : Decidable (uniqueProfileSeparator p q i) :=
  inferInstanceAs (Decidable (profileOppositeAt p q i ∧ ∀ j, j ≠ i → ¬ profileOppositeAt p q j))

def HasPatternOneSeparators (p : Fin 4 → CubeProfile) (k : Fin 3 → Fin 3) : Prop :=
  uniqueProfileSeparator (p 0) (p 2) (k 0) ∧ uniqueProfileSeparator (p 1) (p 3) (k 0) ∧
  uniqueProfileSeparator (p 0) (p 1) (k 1) ∧ uniqueProfileSeparator (p 2) (p 3) (k 1)

def HasPatternTwoSeparators (p : Fin 4 → CubeProfile) (k : Fin 3 → Fin 3) : Prop :=
  uniqueProfileSeparator (p 0) (p 2) (k 0) ∧ uniqueProfileSeparator (p 0) (p 3) (k 0) ∧
  uniqueProfileSeparator (p 1) (p 2) (k 0) ∧ uniqueProfileSeparator (p 1) (p 3) (k 0) ∧
  uniqueProfileSeparator (p 0) (p 1) (k 1) ∧ uniqueProfileSeparator (p 2) (p 3) (k 2)

instance (p : Fin 4 → CubeProfile) (k : Fin 3 → Fin 3) : Decidable (HasPatternOneSeparators p k) :=
  inferInstanceAs (Decidable (uniqueProfileSeparator (p 0) (p 2) (k 0) ∧
    uniqueProfileSeparator (p 1) (p 3) (k 0) ∧ uniqueProfileSeparator (p 0) (p 1) (k 1) ∧
    uniqueProfileSeparator (p 2) (p 3) (k 1)))

instance (p : Fin 4 → CubeProfile) (k : Fin 3 → Fin 3) : Decidable (HasPatternTwoSeparators p k) :=
  inferInstanceAs (Decidable (uniqueProfileSeparator (p 0) (p 2) (k 0) ∧
    uniqueProfileSeparator (p 0) (p 3) (k 0) ∧ uniqueProfileSeparator (p 1) (p 2) (k 0) ∧
    uniqueProfileSeparator (p 1) (p 3) (k 0) ∧ uniqueProfileSeparator (p 0) (p 1) (k 1) ∧
    uniqueProfileSeparator (p 2) (p 3) (k 2)))

#print axioms matchingProfile_exists

end Erdos556
