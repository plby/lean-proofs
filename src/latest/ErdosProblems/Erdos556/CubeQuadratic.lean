import ErdosProblems.Erdos556.CubeWeights

/-!
# Algebra of the cube energy

The energy is a symmetric quadratic form minus a linear term. Adding
weight at one profile gives an explicit derivative and square term.
-/

namespace Erdos556

open Finset

def cubeBilinear (x y : CubeProfile → ℝ) : ℝ :=
  ∑ p, ∑ q, cubeOverlap p q * x p * y q

def cubeLinear (x : CubeProfile → ℝ) : ℝ :=
  ∑ p, (profileDimension p : ℝ) * x p

theorem cubeEnergy_eq (w : CubeProfile → ℝ) :
    cubeEnergy w = cubeBilinear w w - cubeLinear w := rfl

theorem cubeBilinear_add_left (x y z : CubeProfile → ℝ) :
    cubeBilinear (x + y) z = cubeBilinear x z + cubeBilinear y z := by
  simp only [cubeBilinear, Pi.add_apply, mul_add, add_mul, sum_add_distrib]

theorem cubeBilinear_add_right (x y z : CubeProfile → ℝ) :
    cubeBilinear x (y + z) = cubeBilinear x y + cubeBilinear x z := by
  simp only [cubeBilinear, Pi.add_apply, mul_add, sum_add_distrib]

theorem cubeBilinear_symm (x y : CubeProfile → ℝ) : cubeBilinear x y = cubeBilinear y x := by
  rw [cubeBilinear, sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [cubeOverlap_symm q p]
  ring

theorem cubeBilinear_single_left (x : CubeProfile → ℝ) (p : CubeProfile) (t : ℝ) :
    cubeBilinear (Pi.single p t) x = t * ∑ q, cubeOverlap p q * x q := by
  classical
  simp [cubeBilinear, Pi.single_apply, ite_mul, mul_ite, mul_sum, mul_assoc, mul_comm, mul_left_comm]

theorem cubeBilinear_single_right (x : CubeProfile → ℝ) (p : CubeProfile) (t : ℝ) :
    cubeBilinear x (Pi.single p t) = t * ∑ q, cubeOverlap p q * x q := by
  rw [cubeBilinear_symm, cubeBilinear_single_left]

theorem cubeBilinear_single_single (p : CubeProfile) (s t : ℝ) :
    cubeBilinear (Pi.single p s) (Pi.single p t) = s * t := by
  classical
  rw [cubeBilinear_single_left]
  simp [Pi.single_apply, mul_ite, cubeOverlap_self]

theorem cubeLinear_add (x y : CubeProfile → ℝ) : cubeLinear (x + y) = cubeLinear x + cubeLinear y := by
  simp only [cubeLinear, Pi.add_apply, mul_add, sum_add_distrib]

theorem cubeLinear_single (p : CubeProfile) (t : ℝ) :
    cubeLinear (Pi.single p t) = profileDimension p * t := by
  classical
  simp [cubeLinear, Pi.single_apply, mul_ite]

theorem cubeEnergy_add_single (w : CubeProfile → ℝ) (p : CubeProfile) (t : ℝ) :
    cubeEnergy (w + Pi.single p t) = cubeEnergy w + t * cubeGradient w p + t ^ 2 := by
  simp only [cubeEnergy_eq]
  rw [cubeBilinear_add_left, cubeBilinear_add_right, cubeBilinear_add_right,
    cubeBilinear_single_right, cubeBilinear_single_left, cubeBilinear_single_single,
    cubeLinear_add, cubeLinear_single]
  dsimp [cubeGradient]
  ring

theorem cubeGradient_add_single (w : CubeProfile → ℝ) (p q : CubeProfile) (t : ℝ) :
    cubeGradient (w + Pi.single p t) q = cubeGradient w q + 2 * t * cubeOverlap q p := by
  classical
  simp only [cubeGradient, Pi.add_apply, mul_add, sum_add_distrib]
  have hsum : (∑ r, cubeOverlap q r * (Pi.single p t : CubeProfile → ℝ) r) = cubeOverlap q p * t := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum]
  ring

#print axioms cubeEnergy_add_single
#print axioms cubeGradient_add_single

end Erdos556
