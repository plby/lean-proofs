import Wikipedia.HopfProblem.OrbitPairSubdivisionHomeomorphism
import Wikipedia.HopfProblem.OrbitPairSubdivisionVertexHomotopy
import Mathlib.Topology.Homotopy.Equiv

/-!
# The actual standard last-vertex map is a homotopy equivalence

The barycentric homeomorphism supplies an inverse. Its checked homotopy
from the last-vertex map supplies both inverse identities. The final
equivalence has exactly the realized native last-vertex map as its forward
map, rather than an unspecified homotopy-equivalent replacement.
-/

noncomputable section

universe u v

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair

namespace HomotopyEquivalence

def replaceForward {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (f : C(X, Y))
    (h : f.Homotopic e.toFun) : ContinuousMap.HomotopyEquiv X Y where
  toFun := f
  invFun := e.invFun
  left_inv := (ContinuousMap.Homotopic.comp (.refl _) h).trans e.left_inv
  right_inv := (ContinuousMap.Homotopic.comp h (.refl _)).trans e.right_inv

end HomotopyEquivalence

namespace Subdivision

open FirstHurewicz

def geometricLastVertexEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv
    (SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌)) (Simplex n) :=
  HomotopyEquivalence.replaceForward (barycentricHomeomorph n).toHomotopyEquiv
    (realizedLastVertex n) ⟨(barycentricHomotopy n).toHomotopy⟩

def simplexLastVertexEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv
    (SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌))
    (SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)) :=
  (geometricLastVertexEquiv n).trans (standardCoordinates n).symm.toHomotopyEquiv

theorem simplexLastVertexEquiv_forward (n : ℕ) :
    (simplexLastVertexEquiv.{u} n).toFun =
      (SSet.toTop.map (simplexLastVertex ⦋n⦌)).hom := by
  apply ContinuousMap.ext
  intro x
  exact (standardCoordinates n).symm_apply_apply _

def standardLastVertexEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv
    (SSet.toTop.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋n⦌)))
    (SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.sdIso.app ⦋n⦌))).toHomotopyEquiv.trans
    (simplexLastVertexEquiv n)

theorem standardLastVertexEquiv_forward (n : ℕ) :
    (standardLastVertexEquiv.{u} n).toFun =
      (SSet.toTop.map (lastVertex.app (SSet.stdSimplex.obj ⦋n⦌))).hom := by
  change (simplexLastVertexEquiv n).toFun.comp
    (SSet.toTop.map (SSet.stdSimplex.sdIso.hom.app ⦋n⦌)).hom = _
  rw [simplexLastVertexEquiv_forward]
  have h : SSet.stdSimplex.sdIso.hom.app ⦋n⦌ ≫ simplexLastVertex ⦋n⦌ =
      lastVertex.app (SSet.stdSimplex.obj ⦋n⦌) := by
    rw [← lastVertex_stdSimplex, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact congrArg TopCat.Hom.hom ((SSet.toTop.map_comp _ _).symm.trans (congrArg _ h))

end Subdivision

end Wikipedia.HopfProblem.OrbitPair
