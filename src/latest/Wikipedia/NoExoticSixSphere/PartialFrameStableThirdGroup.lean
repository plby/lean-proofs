import Wikipedia.NoExoticSixSphere.PartialFrameHomotopyStability
import Wikipedia.NoExoticSixSphere.PartialFrameThirdGroup

/-!
# The actual third groups of partial frames with three-dimensional complement

Start with the computed two-column space and iterate actual reconstruction.
The base spheres have dimension at least five, so the native third homotopy
maps are isomorphisms by relative column lifting. The constructed Hurewicz
comparison then gives third homology and removes the basepoint restriction.

This computes the obstruction groups, not a geometric quadratic refinement
or a dimension-six nullbordism theorem.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open Wikipedia.HopfProblem.SingularMayerVietoris

def basedStableThirdHomotopyEquivZModTwo (r : ℕ) :
    Additive (HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2))
      (baseFrame 3 (r + 2))) ≃ₗ[ℤ] ZMod 2 := by
  induction r with
  | zero => exact ColumnHomology.thirdHomotopyEquivZModTwo (pole 1) (baseFrame 3 2)
  | succ r ih =>
    let e : Additive (HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2))
        (baseFrame 3 (r + 2))) ≃ₗ[ℤ]
        Additive (HomotopyGroup (Fin 3) (Space (3 + ((r + 1) + 2)) ((r + 1) + 2))
          (baseFrame 3 ((r + 1) + 2))) :=
      (reconstruction_homotopyMulEquiv (m := 3) (pole (r + 2)) (pole (3 + (r + 2)))
        (by omega) (baseFrame 3 (r + 2))).toAdditive.toIntLinearEquiv
    exact e.symm.trans ih

def stableThirdHomologyEquivZModTwo (r : ℕ) :
    SingularHomology (Space (3 + (r + 2)) (r + 2)) 3 ≃ₗ[ℤ] ZMod 2 :=
  (thirdHurewiczLinearEquiv (by decide : 2 < 3) (r + 2) (baseFrame 3 (r + 2))).symm.trans
    (basedStableThirdHomotopyEquivZModTwo r)

def stableThirdHomotopyEquivZModTwo (r : ℕ) (a : Space (3 + (r + 2)) (r + 2)) :
    Additive (HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) ≃ₗ[ℤ] ZMod 2 :=
  (thirdHurewiczLinearEquiv (by decide : 2 < 3) (r + 2) a).trans
    (stableThirdHomologyEquivZModTwo r)

end NoExoticSixSphere.Stiefel
