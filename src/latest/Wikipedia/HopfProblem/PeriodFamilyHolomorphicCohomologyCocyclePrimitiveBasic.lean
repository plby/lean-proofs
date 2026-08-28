import Wikipedia.HopfProblem.PeriodFamily
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# The actual period-coordinate primitive in a holomorphic family

Four native holomorphic base functions define a complex-valued function
on the original covering space by evaluating the inverse real period
isomorphism. Its change under an original deck translation is exactly
the corresponding lattice character, which is holomorphic on the base.
The primitive itself is not asserted to be holomorphic.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

/-- Four actual bundled holomorphic functions on the original base. -/
abbrev Coefficients (V : Type*) (B : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] :=
  Fin 4 → ContMDiffMap (modelWithCornersSelf ℂ V) 𝓘(ℂ) B ℂ ω

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The literal primitive in the inverse real coordinates of the original
varying period isomorphism. -/
def primitive (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (x : B × ComplexPlane₂) : ℂ :=
  ∑ j, a j x.1 * (((P.periodEquiv x.1).symm x.2 j : ℝ) : ℂ)

/-- The actual additive character of the fixed marked integer lattice. -/
def character (a : Coefficients V B) (b : B) (g : standardLattice) : ℂ :=
  ∑ j, a j b * ((g.val j : ℝ) : ℂ)

@[simp] theorem primitive_zero (P : HolomorphicPeriodMap V B)
    (x : B × ComplexPlane₂) : primitive P (0 : Coefficients V B) x = 0 := by
  simp [primitive]

theorem primitive_add (P : HolomorphicPeriodMap V B) (a a' : Coefficients V B)
    (x : B × ComplexPlane₂) :
    primitive P (a + a') x = primitive P a x + primitive P a' x := by
  simp [primitive, add_mul, Finset.sum_add_distrib]

@[simp] theorem primitive_neg (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (x : B × ComplexPlane₂) : primitive P (-a) x = -primitive P a x := by
  simp [primitive]

theorem primitive_sub (P : HolomorphicPeriodMap V B) (a a' : Coefficients V B)
    (x : B × ComplexPlane₂) :
    primitive P (a - a') x = primitive P a x - primitive P a' x := by
  simp [primitive, sub_mul, Finset.sum_sub_distrib]

theorem primitive_smul (P : HolomorphicPeriodMap V B) (c : ℂ)
    (a : Coefficients V B) (x : B × ComplexPlane₂) :
    primitive P (c • a) x = c * primitive P a x := by
  simp [primitive, smul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp] theorem character_zero (b : B) (g : standardLattice) :
    character (0 : Coefficients V B) b g = 0 := by
  simp [character]

theorem character_add (a a' : Coefficients V B) (b : B) (g : standardLattice) :
    character (a + a') b g = character a b g + character a' b g := by
  simp [character, add_mul, Finset.sum_add_distrib]

@[simp] theorem character_neg (a : Coefficients V B) (b : B) (g : standardLattice) :
    character (-a) b g = -character a b g := by
  simp [character]

theorem character_sub (a a' : Coefficients V B) (b : B) (g : standardLattice) :
    character (a - a') b g = character a b g - character a' b g := by
  simp [character, sub_mul, Finset.sum_sub_distrib]

theorem character_smul (c : ℂ) (a : Coefficients V B) (b : B) (g : standardLattice) :
    character (c • a) b g = c * character a b g := by
  simp [character, smul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp] theorem character_lattice_zero (a : Coefficients V B) (b : B) :
    character a b 0 = 0 := by
  simp [character]

theorem character_lattice_add (a : Coefficients V B) (b : B)
    (g h : standardLattice) :
    character a b (g + h) = character a b g + character a b h := by
  simp [character, mul_add, Finset.sum_add_distrib]

@[simp] theorem character_lattice_neg (a : Coefficients V B) (b : B)
    (g : standardLattice) : character a b (-g) = -character a b g := by
  simp [character]

theorem character_lattice_sub (a : Coefficients V B) (b : B)
    (g h : standardLattice) :
    character a b (g - h) = character a b g - character a b h := by
  simp [character, mul_sub, Finset.sum_sub_distrib]

/-- Each fixed lattice character is a holomorphic function in the original
base charts, without any extra assumption on the base. -/
theorem character_holomorphic (a : Coefficients V B) (g : standardLattice) :
    ContMDiff (modelWithCornersSelf ℂ V) 𝓘(ℂ) ω (fun b => character a b g) := by
  apply contMDiff_finsetSum
  intro j _
  exact (a j).contMDiff.mul contMDiff_const

/-- Literal translation by an original period adds exactly its character. -/
theorem primitive_add_period (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (b : B) (z : ComplexPlane₂) (g : standardLattice) :
    primitive P a (b, z + P.periodEquiv b g) = primitive P a (b, z) + character a b g := by
  simp [primitive, character, map_add, mul_add, Finset.sum_add_distrib]

/-- The same formula for the original covering action, not a substitute
action on an algebraic model. -/
theorem primitive_deck (P : HolomorphicPeriodMap V B) (a : Coefficients V B)
    (g : Multiplicative standardLattice) (x : B × ComplexPlane₂) :
    letI := P.coveringAction
    primitive P a (g • x) = primitive P a x + character a x.1 g.toAdd := by
  let := P.coveringAction
  exact primitive_add_period P a x.1 x.2 g.toAdd

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
