import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity
import Wikipedia.HopfProblem.ThirdHurewiczIso

/-!
# The third Hurewicz comparison for actual partial normal frames

The proved native connectivity supplies both hypotheses of the workspace's
constructed third Hurewicz isomorphism. Thus the actual third homotopy group
of a partial-frame space with complement dimension at least three is identified
with its actual integral singular homology, without connectivity or Hurewicz
assumptions. This does not yet compute the resulting group.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open Wikipedia.HopfProblem.SingularMayerVietoris

def thirdHurewiczLinearEquiv {c : ℕ} (hc : 2 < c) (r : ℕ) (a : Space (c + r) r) :
    Additive (HomotopyGroup (Fin 3) (Space (c + r) r) a) ≃ₗ[ℤ]
      SingularHomology (Space (c + r) r) 3 := by
  let := simplyConnectedSpace (by omega : 1 < c) r
  let := subsingleton_homotopyGroup_of_lt hc r a
  exact Wikipedia.HopfProblem.ThirdHurewicz.hurewiczLinearEquiv a

end NoExoticSixSphere.Stiefel
