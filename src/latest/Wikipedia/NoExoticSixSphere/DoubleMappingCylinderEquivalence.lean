import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderInverseHomotopy

/-!
# The actual cylinder collapse is a homotopy equivalence for a cofibration

The collapsed extended motion glues on the original pushout and gives
the second inverse homotopy. Together with the cylinder-side homotopy,
this proves that the original collapse map is a homotopy equivalence.
The only hypothesis is homotopy extension for the left attaching map.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.DoubleMappingCylinder

variable {A X Y P : TopCat.{u}} (e : A ⟶ X) (f : A ⟶ Y)
    {i : X ⟶ P} {j : Y ⟶ P} (hP : IsPushout e f i j)
    (K : C(I × X, space e f)) (hK0 : ∀ x, K (0, x) = left e f x)
    (hKe : ∀ s a, K (s, e a) = tube e f (σ s, a))

def collapseLeft : C(I × X, P) := (collapse e f hP).hom.comp K

def collapseRight : C(I × Y, P) := j.hom.comp ContinuousMap.snd

include hKe in
theorem collapse_compatible (s : I) (a : A) :
    collapseLeft e f hP K (s, e a) = collapseRight (j := j) (s, f a) := by
  change collapse e f hP (K (s, e a)) = j (f a)
  rw [hKe]
  exact congrArg (fun m ↦ m (σ s, a)) (tube_collapse e f hP)

def collapseFamily : C(I × P, P) :=
  PushoutHomotopy.glueFamily (collapseLeft e f hP K) (collapseRight (j := j))
    (collapse_compatible e f hP K hKe) hP

theorem collapseFamily_left (s : I) (x : X) :
    collapseFamily e f hP K hKe (s, i x) = collapse e f hP (K (s, x)) :=
  PushoutHomotopy.glueFamily_inl (S := A) (A := X) (B := Y) (P := P) (Z := P)
    (f := e) (g := f) (i := i) (j := j)
    (collapseLeft e f hP K) (collapseRight (j := j)) (collapse_compatible e f hP K hKe) hP s x

theorem collapseFamily_right (s : I) (y : Y) : collapseFamily e f hP K hKe (s, j y) = j y :=
  PushoutHomotopy.glueFamily_inr (S := A) (A := X) (B := Y) (P := P) (Z := P)
    (f := e) (g := f) (i := i) (j := j)
    (collapseLeft e f hP K) (collapseRight (j := j)) (collapse_compatible e f hP K hKe) hP s y

include hK0 in
theorem collapseFamily_zero (p : P) : collapseFamily e f hP K hKe (0, p) = p := by
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := PushoutHomotopy.jointly_surjective hP p
  · rw [collapseFamily_left, hK0]
    exact congrArg (fun m ↦ m x) (left_collapse e f hP)
  · exact collapseFamily_right e f hP K hKe 0 y

theorem collapseFamily_one (p : P) :
    collapseFamily e f hP K hKe (1, p) = collapse e f hP (inverseMap e f hP K hKe p) := by
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := PushoutHomotopy.jointly_surjective hP p
  · rw [collapseFamily_left]
    have hi : inverseMap e f hP K hKe (i x) = K (1, x) :=
      congrArg (fun m ↦ m x) (left_inverseMap e f hP K hKe)
    exact (congrArg (collapse e f hP) hi).symm
  · rw [collapseFamily_right]
    have hj : inverseMap e f hP K hKe (j y) = right e f y :=
      congrArg (fun m ↦ m y) (right_inverseMap e f hP K hKe)
    have hc : collapse e f hP (right e f y) = j y :=
      congrArg (fun m ↦ m y) (right_collapse e f hP)
    exact hc.symm.trans (congrArg (collapse e f hP) hj.symm)

def collapseHomotopy : (ContinuousMap.id P).Homotopy
    (inverseMap e f hP K hKe ≫ collapse e f hP).hom where
  toContinuousMap := collapseFamily e f hP K hKe
  map_zero_left := collapseFamily_zero e f hP K hK0 hKe
  map_one_left := collapseFamily_one e f hP K hKe

theorem exists_collapse_equiv (he : HomotopyExtension.HasHomotopyExtension e) :
    ∃ E : ContinuousMap.HomotopyEquiv (space e f) P, E.toFun = (collapse e f hP).hom := by
  obtain ⟨K, hK0, hKe⟩ := exists_extension e f he
  exact ⟨⟨(collapse e f hP).hom, (inverseMap e f hP K hKe).hom,
    ⟨(inverseHomotopy e f hP K hK0 hKe).symm⟩,
    ⟨(collapseHomotopy e f hP K hK0 hKe).symm⟩⟩, rfl⟩

end NoExoticSixSphere.DoubleMappingCylinder
