import ErdosProblems.Erdos941.ConicWords

/-! # Explicit words that move a target height modulo a prime square -/

namespace Erdos941

def alternatingWord (k : ℕ) : List Axis :=
  (List.replicate k [(false, false), (false, true)]).flatten

def kernelLinear {R : Type*} [CommRing R] (p u : R) :
    (R × R × R) →ₗ[R] (R × R × R) where
  toFun v := (v.1 + p * u * v.2.2, v.2.1 - p * u * v.2.2,
    v.2.2 + p * u * (v.2.1 - v.1))
  map_add' v w := by ext <;> dsimp <;> ring
  map_smul' r v := by ext <;> dsimp <;> ring

theorem linearMap_eq_of_three_values {R : Type*} [CommRing R]
    (f g : (R × R × R) →ₗ[R] (R × R × R))
    (h0 : f (1, 0, 0) = g (1, 0, 0))
    (h1 : f (0, 1, 0) = g (0, 1, 0))
    (h2 : f (0, 0, 1) = g (0, 0, 1)) : f = g := by
  apply LinearMap.ext
  intro v
  rw [PairLocal.map_eq_three_combination f, PairLocal.map_eq_three_combination g, h0, h1, h2]

theorem five_kernel_word :
    linearWord (17 : ZMod 25) (alternatingWord 3) = kernelLinear 5 2 := by
  apply linearMap_eq_of_three_values <;> decide

theorem seven_kernel_word :
    linearWord (33 : ZMod 49) (alternatingWord 4) = kernelLinear 7 3 := by
  apply linearMap_eq_of_three_values <;> decide

theorem thirteen_kernel_word :
    linearWord (113 : ZMod 169) (alternatingWord 7) = kernelLinear 13 1 := by
  apply linearMap_eq_of_three_values <;> decide

end Erdos941
