import Wikipedia.HopfProblem.OrbitPairSubdivisionPosetComparison

/-!
# Embeddings and standard-simplex isomorphisms for the poset comparison

The nondegenerate-poset functor reflects the face order along simplicial
monomorphisms. Its nerve therefore preserves monomorphisms. On a standard
simplex the comparison is an actual simplicial isomorphism.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset

variable {X Y : SSet.{u}}

theorem subcomplex_image_le_image_iff (f : X ⟶ Y) [Mono f] (A B : X.Subcomplex) :
    A.image f ≤ B.image f ↔ A ≤ B := by
  constructor
  · intro h d a ha
    have hm : f.app d a ∈ (B.image f).obj d := h d ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := hm
    have hba := injective_of_mono (f.app d) he
    simpa only [hba] using hb
  · exact fun h ↦ SSet.Subcomplex.image_monotone f h

theorem map_le_map_iff (f : X ⟶ Y) [Mono f] (x y : X.N) :
    map f x ≤ map f y ↔ x ≤ y := by
  change (map f x).subcomplex ≤ (map f y).subcomplex ↔ x.subcomplex ≤ y.subcomplex
  rw [map_subcomplex, map_subcomplex, subcomplex_image_le_image_iff]

theorem map_injective (f : X ⟶ Y) [Mono f] : Function.Injective (map f) := by
  intro x y h
  exact le_antisymm ((map_le_map_iff f x y).mp h.le)
    ((map_le_map_iff f y x).mp h.symm.le)

instance nerveFunctor_map_mono (f : X ⟶ Y) [Mono f] : Mono (nerveFunctor.map f) :=
  FinitePoset.nerveMap_mono (map f) (map_injective f)

theorem map_of_mono (f : X ⟶ Y) [Mono f] (x : X.N) :
    map f x = SSet.N.mk (f.app _ x.simplex)
      ((SSet.nonDegenerate_iff_of_mono f x.simplex).mpr x.nonDegenerate) := by
  apply SSet.S.toN_eq_iff.mpr
  rfl

theorem map_of_iso (e : X ≅ Y) (x : X.N) :
    map e.hom x = SSet.N.orderIsoOfIso e x := map_of_mono e.hom x

def standardFaceIso (n : ℕ) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) ≃o (SSet.stdSimplex.obj ⦋n⦌).N :=
  (nerveChainsOrderIso (ULift.{u} (Fin (n + 1)))).symm.trans
    (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve n).symm)

theorem standardFaceIso_apply (n : ℕ)
    (A : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    standardFaceIso n A = standardFace n A :=
  (map_of_iso (SSet.stdSimplex.isoNerve n).symm
    (chainNondegenerate (ULift.{u} (Fin (n + 1))) A)).symm

def standardComparisonIso (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ≅ nerveFunctor.obj (SSet.stdSimplex.obj n) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of (NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))))
    (β := PartOrd.of (SSet.stdSimplex.obj n).N) (standardFaceIso n.len))

theorem standardComparisonIso_hom (n : SimplexCategory) :
    (standardComparisonIso.{u} n).hom = standardComparison n := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext i
  exact standardFaceIso_apply n.len (x.obj i)

instance standardComparison_isIso (n : SimplexCategory) : IsIso (standardComparison.{u} n) := by
  rw [← standardComparisonIso_hom]
  infer_instance

end Wikipedia.HopfProblem.OrbitPair.NondegeneratePoset
