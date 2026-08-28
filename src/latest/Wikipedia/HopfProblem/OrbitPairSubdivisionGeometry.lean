import Wikipedia.HopfProblem.OrbitPairSubdivisionLastVertex
import Wikipedia.HopfProblem.OrbitPairRealizationAffineCoordinates
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# Barycentric coordinates on the native subdivided standard simplex

The actual realization of a standard simplex is identified with its usual
geometric simplex. Under this identification, realization of the checked
last-vertex map is affine interpolation of the chain maxima. Interpolation
of the chain barycentres is also a continuous map on the native realization.
This file does not assert a subdivision homeomorphism for arbitrary sets.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex AffineCoordinates

def standardCoordinates (n : ℕ) :
    SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n⦌) ≃ₜ Simplex n :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋n⦌)).trans Homeomorph.ulift

theorem characteristic_eq_realizedMap (S : SSet.{u}) (n : ℕ) (x : S _⦋n⦌)
    (t : Simplex n) :
    characteristic S n x t = (SSet.toTop.map (SSet.yonedaEquiv.symm x))
      ((SSet.toTopSimplex.inv.app ⦋n⦌) (ULift.up t)) := by
  exact ConcreteCategory.congr_hom (sSetTopAdj_unit_app_app_down S (Opposite.op ⦋n⦌) x)
    (ULift.up t)

theorem standardCoordinates_characteristic (n k : ℕ)
    (x : (SSet.stdSimplex.{u}.obj ⦋n⦌) _⦋k⦌) (t : Simplex k) :
    standardCoordinates n (characteristic (SSet.stdSimplex.obj ⦋n⦌) k x t) =
      stdSimplex.map (SSet.stdSimplex.objEquiv x).toOrderHom t := by
  let f := SSet.stdSimplex.objEquiv x
  have hy : SSet.yonedaEquiv.symm x = SSet.stdSimplex.map f := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, SSet.yonedaEquiv_map]
    exact (SSet.stdSimplex.objEquiv.symm_apply_apply x).symm
  have hc := characteristic_eq_realizedMap (SSet.stdSimplex.obj ⦋n⦌) k x t
  rw [hy] at hc
  have hcat : SSet.toTopSimplex.{u}.inv.app ⦋k⦌ ≫
      SSet.toTop.map (SSet.stdSimplex.map f) ≫ SSet.toTopSimplex.hom.app ⦋n⦌ =
      SimplexCategory.toTop.map f := by
    calc
      _ = SSet.toTopSimplex.inv.app ⦋k⦌ ≫
          SSet.toTopSimplex.hom.app ⦋k⦌ ≫ SimplexCategory.toTop.map f :=
        congrArg (fun g ↦ SSet.toTopSimplex.inv.app ⦋k⦌ ≫ g)
          (SSet.toTopSimplex.hom.naturality f)
      _ = _ := Iso.inv_hom_id_assoc (SSet.toTopSimplex.app ⦋k⦌)
        (SimplexCategory.toTop.map f)
  exact (congrArg (standardCoordinates n) hc).trans
    (congrArg ULift.down (ConcreteCategory.congr_hom hcat (ULift.up t)))

def chainBarycentre (n : ℕ)
    (A : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) : Simplex n := by
  classical
  letI : Nonempty A.finset := A.nonempty.to_subtype
  exact stdSimplex.map (fun i : A.finset ↦ i.val.down) stdSimplex.barycenter

def barycentricMap (n : ℕ) : C(SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌), Simplex n) :=
  nerveInterpolation (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (chainBarycentre n)

def realizedLastVertex (n : ℕ) :
    C(SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌), Simplex n) :=
  (⟨standardCoordinates n, (standardCoordinates n).continuous⟩ :
    C(SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌), Simplex n)).comp
      (SSet.toTop.map (simplexLastVertex ⦋n⦌)).hom

theorem realizedLastVertex_eq_interpolation (n : ℕ) :
    realizedLastVertex.{u} n =
      nerveInterpolation (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
        (fun A ↦ stdSimplex.vertex (chainLastVertex A).down) := by
  apply continuousMap_ext_characteristic
  intro k x t
  change standardCoordinates n ((SSet.toTop.map (simplexLastVertex ⦋n⦌))
    (characteristic (SimplexCategory.sd.obj ⦋n⦌) k x t)) = _
  rw [realizedMap_characteristic, standardCoordinates_characteristic]
  refine Eq.trans ?_ (nerveInterpolation_characteristic
    (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (fun A ↦ stdSimplex.vertex (chainLastVertex A).down) k x t).symm
  exact (weighted_vertices (stdSimplex.map
    (fun i ↦ (chainLastVertex (X := ULift.{u} (Fin (n + 1))) (x.obj i)).down) t)).symm.trans
      (weighted_map (fun i ↦ (chainLastVertex
        (X := ULift.{u} (Fin (n + 1))) (x.obj i)).down)
        (fun j ↦ stdSimplex.vertex j) t)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
