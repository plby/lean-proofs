import Wikipedia.HopfProblem.OrbitPairSubdivisionPosetComparison

/-!
# Native dual subdivision and its first-vertex map

The cosimplicial model is the nerve of the oppositely ordered poset of
nonempty faces. Its actual left Kan extension defines dual subdivision.
Taking the first vertex is natural even under noninjective operators.
Regularity and realization equivalences are not assumed here.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial PartialOrder Opposite

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

def dualStandard : SimplexCategory ⥤ SSet.{u} :=
  SimplexCategory.toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙
    PartOrd.dual ⋙ PartOrd.nerveFunctor

instance dual_hasPointwiseLeftKanExtension :
    SSet.stdSimplex.{u}.HasPointwiseLeftKanExtension dualStandard.{u} := by
  change (uliftYoneda.{u} (C := SimplexCategory)).HasPointwiseLeftKanExtension dualStandard.{u}
  infer_instance

instance dual_hasLeftKanExtension :
    SSet.stdSimplex.{u}.HasLeftKanExtension dualStandard.{u} := by
  change (uliftYoneda.{u} (C := SimplexCategory)).HasLeftKanExtension dualStandard.{u}
  infer_instance

def dualSd : SSet.{u} ⥤ SSet.{u} := SSet.stdSimplex.{u}.leftKanExtension dualStandard.{u}

def dualEx : SSet.{u} ⥤ SSet.{u} := Presheaf.restrictedULiftYoneda.{0} dualStandard.{u}

instance dual_leftKanUnit :
    (SSet.stdSimplex.{u}.leftKanExtension dualStandard.{u}).IsLeftKanExtension
      (SSet.stdSimplex.{u}.leftKanExtensionUnit dualStandard.{u}) := by
  change (uliftYoneda.{u}.leftKanExtension dualStandard.{u}).IsLeftKanExtension
    (uliftYoneda.{u}.leftKanExtensionUnit dualStandard.{u})
  infer_instance

def dualAdjunction : dualSd.{u} ⊣ dualEx := by
  change uliftYoneda.{u}.leftKanExtension dualStandard.{u} ⊣
    Presheaf.restrictedULiftYoneda.{0} dualStandard.{u}
  exact Presheaf.uliftYonedaAdjunction.{0}
    (uliftYoneda.{u}.leftKanExtension dualStandard.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit dualStandard.{u})

instance dualSd_isLeftAdjoint : dualSd.{u}.IsLeftAdjoint := dualAdjunction.isLeftAdjoint

def dualSdIso : SSet.stdSimplex.{u} ⋙ dualSd ≅ dualStandard.{u} := by
  change uliftYoneda.{u} ⋙ uliftYoneda.{u}.leftKanExtension dualStandard.{u} ≅ dualStandard.{u}
  exact Presheaf.isExtensionAlongULiftYoneda.{0} dualStandard.{u}

instance dualSd_isLeftKanExtension : dualSd.{u}.IsLeftKanExtension dualSdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit dualStandard.{u}))

def chainFirstVertex {X : Type u} [LinearOrder X] :
    OrderDual (NonemptyFiniteChains X) →o X where
  toFun A := A.finset.min' A.nonempty
  monotone' A B h := Finset.min'_le A.finset _ (h (Finset.min'_mem B.finset B.nonempty))

theorem chainFirstVertex_mem {X : Type u} [LinearOrder X] (A : NonemptyFiniteChains X) :
    chainFirstVertex A ∈ A.finset := Finset.min'_mem A.finset A.nonempty

theorem chainFirstVertex_map {X : Type u} {Y : Type v} [LinearOrder X] [LinearOrder Y]
    (f : X →o Y) (A : NonemptyFiniteChains X) :
    chainFirstVertex (A.map f) = f (chainFirstVertex A) := by
  classical
  change (A.map f).finset.min' (A.map f).nonempty = f (A.finset.min' A.nonempty)
  apply le_antisymm
  · apply Finset.min'_le
    exact (NonemptyFiniteChains.mem_map_iff A f _).mpr
      ⟨A.finset.min' A.nonempty, Finset.min'_mem _ _, rfl⟩
  · apply Finset.le_min'
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (NonemptyFiniteChains.mem_map_iff A f y).mp hy
    exact f.monotone (Finset.min'_le A.finset a ha)

def simplexFirstVertex (n : SimplexCategory) :
    dualStandard.{u}.obj n ⟶ SSet.stdSimplex.obj n :=
  nerveMap (chainFirstVertex (X := ULift.{u} (Fin (n.len + 1)))).monotone.functor ≫
    (SSet.stdSimplex.isoNerve n.len).inv

theorem simplexFirstVertex_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    dualStandard.{u}.map f ≫ simplexFirstVertex n =
      simplexFirstVertex m ≫ SSet.stdSimplex.map f := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  rcases m with ⟨m⟩
  rcases n with ⟨n⟩
  obtain ⟨⟨k⟩⟩ := k
  apply SSet.stdSimplex.ext
  intro i
  change (chainFirstVertex (X := ULift.{u} (Fin (n + 1)))
    ((x.obj i).map (SimplexCategory.toPartOrd.{u}.map f).hom)).down =
    f.toOrderHom (chainFirstVertex (X := ULift.{u} (Fin (m + 1))) (x.obj i)).down
  have h := chainFirstVertex_map (X := ULift.{u} (Fin (m + 1)))
    (Y := ULift.{u} (Fin (n + 1))) (SimplexCategory.toPartOrd.{u}.map f).hom
      (show NonemptyFiniteChains (ULift.{u} (Fin (m + 1))) from x.obj i)
  exact congrArg ULift.down h

def simplexFirstVertexNat : dualStandard.{u} ⟶ SSet.stdSimplex where
  app := simplexFirstVertex
  naturality _ _ f := simplexFirstVertex_naturality f

def firstVertex : dualSd.{u} ⟶ 𝟭 SSet :=
  dualSd.descOfIsLeftKanExtension dualSdIso.inv (𝟭 SSet)
    (simplexFirstVertexNat ≫ (Functor.rightUnitor SSet.stdSimplex).inv)

theorem firstVertex_stdSimplex (n : SimplexCategory) :
    dualSdIso.inv.app n ≫ firstVertex.app (SSet.stdSimplex.obj n) = simplexFirstVertex n :=
  dualSd.descOfIsLeftKanExtension_fac_app dualSdIso.inv (𝟭 SSet)
    (simplexFirstVertexNat ≫ (Functor.rightUnitor SSet.stdSimplex).inv) n

end Wikipedia.HopfProblem.OrbitPair.Subdivision
