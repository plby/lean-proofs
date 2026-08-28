import Wikipedia.HopfProblem.OrbitPairSubdivisionDimensionPreservation

/-!
# Native subdivision and unions of subcomplexes

Subdivision sends a subcomplex to the range of its actual subdivided
inclusion. The checked preservation of monomorphisms and pushouts implies
that this operation preserves binary unions and intersections. In
particular, the subdivided union-attachment square is an actual pushout
and pullback, not a postulated gluing model.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

instance sd_preservesMonomorphisms : SSet.sd.{u}.PreservesMonomorphisms where
  preserves := by
    intro X Y f hf
    exact SubdivisionParameters.sd_map_mono f

instance dualSd_preservesMonomorphisms : dualSd.{u}.PreservesMonomorphisms where
  preserves := by
    intro X Y f hf
    exact SubdivisionParameters.dualSd_map_mono f

end Wikipedia.HopfProblem.OrbitPair.Subdivision

namespace Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex

variable (L : SSet.{u} ⥤ SSet.{u}) {X : SSet.{u}}

def image (A : X.Subcomplex) : (L.obj X).Subcomplex := SSet.Subcomplex.range (L.map A.ι)

theorem inclusion_factor {A B : X.Subcomplex} (h : A ≤ B) :
    L.map (SSet.Subcomplex.homOfLE h) ≫ L.map B.ι = L.map A.ι :=
  (L.map_comp _ _).symm.trans (congrArg L.map (SSet.Subcomplex.homOfLE_ι h))

theorem image_monotone : Monotone (image L (X := X)) := by
  intro A B h d z hz
  obtain ⟨a, rfl⟩ := hz
  exact ⟨(L.map (SSet.Subcomplex.homOfLE h)).app d a,
    congrArg (fun f ↦ f.app d a) (inclusion_factor L h)⟩

theorem image_top : image L (⊤ : X.Subcomplex) = ⊤ := by
  let : IsIso (L.map (⊤ : X.Subcomplex).ι) :=
    inferInstanceAs (IsIso (L.map (SSet.Subcomplex.topIso X).hom))
  exact SSet.Subcomplex.range_eq_top (L.map (⊤ : X.Subcomplex).ι)

variable [PreservesColimitsOfShape WalkingSpan L]

theorem union_isPushout (A B : X.Subcomplex) :
    IsPushout (L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      (L.map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) := by
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact sq.isPushout.map L

theorem image_sup (A B : X.Subcomplex) : image L (A ⊔ B) = image L A ⊔ image L B := by
  apply le_antisymm
  · intro d z hz
    obtain ⟨p, rfl⟩ := hz
    obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) := Types.eq_or_eq_of_isPushout ((union_isPushout L A B).app d) p
    · exact Or.inl ⟨a, (congrArg (fun f ↦ f.app d a)
        (inclusion_factor L (le_sup_left : A ≤ A ⊔ B))).symm⟩
    · exact Or.inr ⟨b, (congrArg (fun f ↦ f.app d b)
        (inclusion_factor L (le_sup_right : B ≤ A ⊔ B))).symm⟩
  · exact sup_le (image_monotone L le_sup_left) (image_monotone L le_sup_right)

variable [L.PreservesMonomorphisms]

theorem union_isPullback (A B : X.Subcomplex) :
    IsPullback (L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)))
      (L.map (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)))
      (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  exact Types.isPullback_of_isPushout ((union_isPushout L A B).app d)
    (injective_of_mono ((L.map (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))).app d))

theorem image_inf (A B : X.Subcomplex) : image L (A ⊓ B) = image L A ⊓ image L B := by
  apply le_antisymm
  · exact le_inf (image_monotone L inf_le_left) (image_monotone L inf_le_right)
  · intro d z hz
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
    have hab : (L.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))).app d a =
        (L.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))).app d b := by
      apply injective_of_mono ((L.map (A ⊔ B).ι).app d)
      exact ((congrArg (fun f ↦ f.app d a)
        (inclusion_factor L (le_sup_left : A ≤ A ⊔ B))).trans ha).trans
          (((congrArg (fun f ↦ f.app d b)
            (inclusion_factor L (le_sup_right : B ≤ A ⊔ B))).trans hb).symm)
    obtain ⟨c, hca, _⟩ := Types.exists_of_isPullback ((union_isPullback L A B).app d) a b hab
    refine ⟨c, ?_⟩
    exact (congrArg (fun f ↦ f.app d c)
      (inclusion_factor L (inf_le_left : A ⊓ B ≤ A))).symm.trans
        ((congrArg ((L.map A.ι).app d) hca).trans ha)

end Wikipedia.HopfProblem.OrbitPair.SubdivisionSubcomplex
