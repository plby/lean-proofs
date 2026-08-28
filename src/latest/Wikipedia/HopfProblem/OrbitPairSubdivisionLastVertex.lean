import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.Data.Finset.Max

/-!
# The last-vertex map on the native subdivision functor

Taking the maximum of a nonempty chain commutes with every monotone map,
including noninjective maps. This gives a map from each subdivided standard
simplex to the original simplex, natural in all simplex operators. The
actual left Kan extension then gives a natural transformation `SSet.sd ⟶ 𝟭`.
No barycentre map or unproved subdivision homeomorphism is used here.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial Opposite PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

def chainLastVertex {X : Type u} [LinearOrder X] : NonemptyFiniteChains X →o X where
  toFun A := A.finset.max' A.nonempty
  monotone' A _B h := Finset.max'_subset A.nonempty h

theorem chainLastVertex_mem {X : Type u} [LinearOrder X] (A : NonemptyFiniteChains X) :
    chainLastVertex A ∈ A.finset :=
  Finset.max'_mem A.finset A.nonempty

theorem chainLastVertex_map {X : Type u} {Y : Type v} [LinearOrder X] [LinearOrder Y]
    (f : X →o Y) (A : NonemptyFiniteChains X) :
    chainLastVertex (A.map f) = f (chainLastVertex A) := by
  classical
  change (A.map f).finset.max' (A.map f).nonempty = f (A.finset.max' A.nonempty)
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (NonemptyFiniteChains.mem_map_iff A f y).mp hy
    exact f.monotone (Finset.le_max' A.finset a ha)
  · apply Finset.le_max'
    exact (NonemptyFiniteChains.mem_map_iff A f _).mpr
      ⟨A.finset.max' A.nonempty, Finset.max'_mem _ _, rfl⟩

def simplexLastVertex (n : SimplexCategory) :
    SimplexCategory.sd.{u}.obj n ⟶ SSet.stdSimplex.obj n :=
  nerveMap (chainLastVertex (X := ULift.{u} (Fin (n.len + 1)))).monotone.functor ≫
    (SSet.stdSimplex.isoNerve n.len).inv

theorem simplexLastVertex_apply (n k : ℕ)
    (x : (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋k⦌) (i : Fin (k + 1)) :
    (simplexLastVertex ⦋n⦌).app (op ⦋k⦌) x i =
      (chainLastVertex (X := ULift.{u} (Fin (n + 1))) (x.obj i)).down := rfl

theorem simplexLastVertex_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.sd.{u}.map f ≫ simplexLastVertex n =
      simplexLastVertex m ≫ SSet.stdSimplex.map f := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  rcases m with ⟨m⟩
  rcases n with ⟨n⟩
  obtain ⟨⟨k⟩⟩ := k
  apply SSet.stdSimplex.ext
  intro i
  change (chainLastVertex (X := ULift.{u} (Fin (n + 1)))
    ((x.obj i).map (SimplexCategory.toPartOrd.{u}.map f).hom)).down =
    f.toOrderHom (chainLastVertex (X := ULift.{u} (Fin (m + 1))) (x.obj i)).down
  have h := chainLastVertex_map (X := ULift.{u} (Fin (m + 1)))
    (Y := ULift.{u} (Fin (n + 1))) (SimplexCategory.toPartOrd.{u}.map f).hom (x.obj i)
  exact congrArg ULift.down h

def simplexLastVertexNat : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex where
  app := simplexLastVertex
  naturality _ _ f := simplexLastVertex_naturality f

def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 SSet)
    (simplexLastVertexNat ≫ (Functor.rightUnitor SSet.stdSimplex).inv)

theorem lastVertex_stdSimplex (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫ lastVertex.app (SSet.stdSimplex.obj n) =
      simplexLastVertex n := by
  exact SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv (𝟭 SSet)
    (simplexLastVertexNat ≫ (Functor.rightUnitor SSet.stdSimplex).inv) n

theorem lastVertex_simplex (S : SSet.{u}) (n : ℕ) (x : S _⦋n⦌) :
    SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫ SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
        lastVertex.app S = simplexLastVertex ⦋n⦌ ≫ SSet.yonedaEquiv.symm x := by
  rw [lastVertex.naturality, ← Category.assoc, lastVertex_stdSimplex]
  rfl

end Wikipedia.HopfProblem.OrbitPair.Subdivision
