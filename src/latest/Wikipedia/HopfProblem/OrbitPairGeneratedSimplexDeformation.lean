import Wikipedia.HopfProblem.OrbitPairPushoutDeformation
import Mathlib.Topology.Homotopy.Contractible

/-!
# Deformation retraction of a generated simplex onto its zeroth face

All maps in the deformation are realizations of the checked native
simplicial maps. The standard relative homotopy is glued through the
actual attaching pushout. This gives a homotopy equivalence and transfers
contractibility from the generated zeroth face.
-/

noncomputable section

universe u

open CategoryTheory Simplicial unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.InitialFace

theorem standard_contractible (n : ℕ) :
    ContractibleSpace (SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋n⦌)) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  let p := (Subdivision.standardCoordinates.{u} n).symm
    (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))
  exact ⟨p, ⟨standardBlend n (ContinuousMap.id _) (ContinuousMap.const _ p)⟩⟩

variable {X : SSet.{u}} {n : ℕ} (z : X _⦋n + 1⦌) (hz : InitialInjective z)

def generatedDeformation :
    (ContinuousMap.id (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet))).HomotopyRel
      (SSet.toTop.map (retraction z hz) ≫ SSet.toTop.map (inclusion z)).hom
      (Set.range (SSet.toTop.map (inclusion z))) := by
  have H := (standardCollapseHomotopy.{u} n).cast rfl
    (congrArg TopCat.Hom.hom
      (SSet.toTop.map_comp (SSet.stdSimplex.σ (0 : Fin (n + 1))) (SSet.stdSimplex.δ 0)))
  exact PushoutHomotopy.deformation (realized_pushout z hz)
    (SSet.toTop.map (retraction z hz)) (SSet.toTop.map (SSet.stdSimplex.σ (0 : Fin (n + 1))))
    (realized_inclusion_retraction z hz) (realized_characteristic_retraction z hz) H

def generatedFaceHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet))
      (SSet.toTop.obj (SSet.Subcomplex.ofSimplex (X.δ 0 z) : SSet)) where
  toFun := (SSet.toTop.map (retraction z hz)).hom
  invFun := (SSet.toTop.map (inclusion z)).hom
  left_inv := ⟨(generatedDeformation z hz).toHomotopy.symm⟩
  right_inv := by
    have h : (SSet.toTop.map (retraction z hz)).hom.comp
        (SSet.toTop.map (inclusion z)).hom = ContinuousMap.id _ :=
      congrArg TopCat.Hom.hom (realized_inclusion_retraction z hz)
    rw [h]

include hz in
theorem generated_contractible_of_face
    [ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex (X.δ 0 z) : SSet))] :
    ContractibleSpace (SSet.toTop.obj (SSet.Subcomplex.ofSimplex z : SSet)) :=
  (generatedFaceHomotopyEquiv z hz).contractibleSpace

end Wikipedia.HopfProblem.OrbitPair.InitialFace
