import Wikipedia.NoExoticSixSphere.ModHomologyHomotopy
import Mathlib.Topology.Homotopy.Equiv

/-!
# Actual finite-coefficient homology equivalences from homotopy equivalences

Both directions are the native continuous-map actions on the original
coefficient homology. The supplied genuine homotopies prove the two
inverse identities, without passing through an abstract replacement group.
-/

noncomputable section

open ContinuousMap
open Wikipedia.HopfProblem.SphereHomologyCoefficients

namespace NoExoticSixSphere

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original finite-coefficient homology maps of an actual homotopy equivalence. -/
def modHomologyHomotopyEquiv (p : ℕ) (e : X ≃ₕ Y) (n : ℕ) :
    ModHomology p X n ≃ₗ[ℤ] ModHomology p Y n where
  toFun := modHomologyMap p e.toFun n
  invFun := modHomologyMap p e.invFun n
  left_inv := by
    intro a
    have he := modHomologyMap_homotopic p e.left_inv n
    rw [modHomologyMap_comp, modHomologyMap_id] at he
    exact LinearMap.congr_fun he a
  right_inv := by
    intro a
    have he := modHomologyMap_homotopic p e.right_inv n
    rw [modHomologyMap_comp, modHomologyMap_id] at he
    exact LinearMap.congr_fun he a
  map_add' := (modHomologyMap p e.toFun n).map_add
  map_smul' := (modHomologyMap p e.toFun n).map_smul

theorem modHomologyHomotopyEquiv_apply (p : ℕ) (e : X ≃ₕ Y) (n : ℕ)
    (a : ModHomology p X n) :
    modHomologyHomotopyEquiv p e n a = modHomologyMap p e.toFun n a := rfl

theorem modHomologyHomotopyEquiv_symm_apply (p : ℕ) (e : X ≃ₕ Y) (n : ℕ)
    (a : ModHomology p Y n) :
    (modHomologyHomotopyEquiv p e n).symm a = modHomologyMap p e.invFun n a := rfl

end NoExoticSixSphere
