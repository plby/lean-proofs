import Wikipedia.NoExoticSixSphere.CubicalProductSuspension
import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# A cubical suspension homomorphism between the actual sphere homotopy groups

The target is the standard sphere, using the explicit ordered Euclidean
coordinates on the compactified product. The construction is the actual
product quotient on representatives. Its group law is inherited from the
proved concatenation identity, not assigned to a new quotient type.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.CubicalSphereSuspension

open CubicalProductSuspension
open Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct

def lineHomeomorph : Line ≃ₜ ℝ :=
  (PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℝ)).trans (Homeomorph.funUnique (Fin 1) ℝ)

theorem lineHomeomorph_apply (v : Line) : lineHomeomorph v = v 0 := rfl

def productCoordinates (n : ℕ) :
    (Line × EuclideanSpace ℝ (Fin n)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  (lineHomeomorph.prodCongr (Homeomorph.refl _)).trans (coordinates n).toHomeomorph

theorem productCoordinates_head (n : ℕ) (p : Line × EuclideanSpace ℝ (Fin n)) :
    productCoordinates n p 0 = p.1 0 := rfl

theorem productCoordinates_tail (n : ℕ) (p : Line × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    productCoordinates n p i.succ = p.2 i := rfl

def sphereHomeomorph (n : ℕ) :
    OnePoint (Line × EuclideanSpace ℝ (Fin n)) ≃ₜ Sphere (n + 1) :=
  (productCoordinates n).onePointCongr.trans (euclideanOnePointSphere (n + 1))

theorem sphereHomeomorph_infty (n : ℕ) : sphereHomeomorph n ∞ = spherePole (n + 1) :=
  euclideanOnePointSphere_infty (n + 1)

theorem sphereHomeomorph_coe (n : ℕ) (p : Line × EuclideanSpace ℝ (Fin n)) :
    sphereHomeomorph n (↑p : OnePoint _) =
      euclideanOnePointSphere (n + 1) (↑(productCoordinates n p) : OnePoint _) := rfl

theorem inverseSphere_pole (n : ℕ) :
    (euclideanOnePointSphere n).symm (spherePole n) = ∞ :=
  (euclideanOnePointSphere n).symm_apply_eq.mpr (euclideanOnePointSphere_infty n).symm

def loop {m n : ℕ} (p : GenLoop (Fin m) (Sphere n) (spherePole n)) :
    GenLoop (Fin (m + 1)) (Sphere (n + 1)) (spherePole (n + 1)) :=
  HigherHomotopy.genLoopMap (sphereHomeomorph n).toHomotopyEquiv.toFun
    (sphereHomeomorph_infty n)
    (CubicalProductSuspension.loop (HigherHomotopy.genLoopMap
      (euclideanOnePointSphere n).symm.toHomotopyEquiv.toFun (inverseSphere_pole n) p))

theorem loop_apply {m n : ℕ} (p : GenLoop (Fin m) (Sphere n) (spherePole n))
    (u : Fin (m + 1) → I) :
    loop p u = sphereHomeomorph n (OnePointProduct.map
      (clock (u 0), (euclideanOnePointSphere n).symm (p (tail u)))) := rfl

def hom (m n : ℕ) [Nonempty (Fin m)] :
    HomotopyGroup (Fin m) (Sphere n) (spherePole n) →*
      HomotopyGroup (Fin (m + 1)) (Sphere (n + 1)) (spherePole (n + 1)) :=
  (HigherHomotopy.mapMonoidHom (sphereHomeomorph n).toHomotopyEquiv.toFun
    (sphereHomeomorph_infty n)).comp
      (CubicalProductSuspension.hom.comp
        (HigherHomotopy.mapMonoidHom (euclideanOnePointSphere n).symm.toHomotopyEquiv.toFun
          (inverseSphere_pole n)))

theorem hom_mk {m n : ℕ} [Nonempty (Fin m)]
    (p : GenLoop (Fin m) (Sphere n) (spherePole n)) :
    hom m n (⟦p⟧ : HomotopyGroup (Fin m) (Sphere n) (spherePole n)) = ⟦loop p⟧ := rfl

end NoExoticSixSphere.CubicalSphereSuspension
