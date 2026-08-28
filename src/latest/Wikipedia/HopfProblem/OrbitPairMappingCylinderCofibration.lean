import Wikipedia.HopfProblem.OrbitPairMappingCylinder
import Wikipedia.HopfProblem.OrbitPairCylinderRelativeEndpoint
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionDeformation

/-!
# The actual mapping-cylinder source map has homotopy extension

Extend the prescribed source homotopy over the product cylinder while
fixing its opposite endpoint. It then agrees with the constant family on
the target space and glues through the actual mapping-cylinder pushout.
If the original map is a homotopy equivalence, its source inclusion is
therefore a strong deformation retract inclusion.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

theorem jointly_surjective {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j) (p : P) :
    (∃ a, i a = p) ∨ ∃ b, j b = p :=
  Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) p

end Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

namespace Wikipedia.HopfProblem.OrbitPair.MappingCylinder

open HomotopyExtension

variable {A B : TopCat.{u}}

theorem source_hasHomotopyExtension_of_pushout {P : TopCat.{u}} (f : A ⟶ B)
    (i : B ⟶ P) (j : TopCat.of (I × A) ⟶ P)
    (hP : IsPushout f (cylinderEndpoint A 0) i j) :
    HasHomotopyExtension (cylinderEndpoint A 1 ≫ j) := by
  intro Z F G h0
  let Fc := F.comp j.hom
  obtain ⟨K, hK0, hKbot, hKtop⟩ := extend_cylinder_one_relative_zero Fc G h0
  let Hb : C(I × B, Z) := (F.comp i.hom).comp ContinuousMap.snd
  have hc : ∀ (t : I) (a : A), Hb (t, f a) = K (t, cylinderEndpoint A 0 a) := by
    intro t a
    change F (i (f a)) = K (t, (0, a))
    rw [hKbot]
    exact congrArg F (congrArg (fun m ↦ m a) hP.w)
  let H := PushoutHomotopy.glueFamily Hb K hc hP
  refine ⟨H, ?_, ?_⟩
  · intro p
    obtain (⟨b, rfl⟩ | ⟨c, rfl⟩) := PushoutHomotopy.jointly_surjective hP p
    · change PushoutHomotopy.glueFamily Hb K hc hP (0, i b) = F (i b)
      rw [PushoutHomotopy.glueFamily_inl]
      rfl
    · change PushoutHomotopy.glueFamily Hb K hc hP (0, j c) = F (j c)
      rw [PushoutHomotopy.glueFamily_inr, hK0]
      rfl
  · intro t a
    change PushoutHomotopy.glueFamily Hb K hc hP (t, j (1, a)) = G (t, a)
    rw [PushoutHomotopy.glueFamily_inr, hKtop]

variable (f : A ⟶ B)

theorem source_hasHomotopyExtension : HasHomotopyExtension (source f) :=
  source_hasHomotopyExtension_of_pushout f (target f) (cylinder f) (square f)

theorem source_strong_deformation_retraction (e : ContinuousMap.HomotopyEquiv A B)
    (he : e.toFun = f.hom) :
    ∃ r : C(space f, A), r.comp (source f).hom = ContinuousMap.id A ∧
      Nonempty ((ContinuousMap.id (space f)).HomotopyRel
        ((source f).hom.comp r) (Set.range (source f))) :=
  exists_strong_deformation_retraction (source f) (source_hasHomotopyExtension f)
    (sourceEquiv f e he) (sourceEquiv_forward f e he)

end Wikipedia.HopfProblem.OrbitPair.MappingCylinder
