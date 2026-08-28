import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocyclePrimitiveBasic

/-!
# Holomorphic linear forms and their literal period primitives

Evaluating an actual holomorphic fibrewise complex-linear form on the
four original period columns gives four native holomorphic base
functions. The primitive of these coefficients equals the original
linear form on the covering space, as an equality of functions.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle

/-- The two native holomorphic coefficient functions of a fibrewise
complex-linear form. -/
abbrev LinearCoefficients (V : Type*) (B : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B] :=
  Fin 2 → ContMDiffMap (modelWithCornersSelf ℂ V) 𝓘(ℂ) B ℂ ω

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The actual fibrewise complex-linear form on the original cover. -/
def linearPrimitive (l : LinearCoefficients V B) (x : B × ComplexPlane₂) : ℂ :=
  ∑ k, l k x.1 * x.2 k

/-- The four native holomorphic functions obtained by evaluating the
linear form on the original varying period columns. -/
def linearCoefficients (P : HolomorphicPeriodMap V B) (l : LinearCoefficients V B) :
    Coefficients V B := fun j =>
  ⟨fun b => ∑ k, l k b * (P.periodEquiv b (Pi.single j 1)) k, by
    apply contMDiff_finsetSum
    intro k _
    exact (l k).contMDiff.mul
      (contMDiff_pi_space.mp (P.holomorphic_periodEquiv_const (Pi.single j 1)) k)⟩

@[simp] theorem linearCoefficients_apply (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) (j : Fin 4) (b : B) :
    linearCoefficients P l j b = ∑ k, l k b * (P.periodEquiv b (Pi.single j 1)) k := rfl

@[simp] theorem linearPrimitive_zero (x : B × ComplexPlane₂) :
    linearPrimitive (0 : LinearCoefficients V B) x = 0 := by
  simp [linearPrimitive]

theorem linearPrimitive_add (l l' : LinearCoefficients V B) (x : B × ComplexPlane₂) :
    linearPrimitive (l + l') x = linearPrimitive l x + linearPrimitive l' x := by
  simp [linearPrimitive, add_mul, Finset.sum_add_distrib]

theorem linearPrimitive_smul (c : ℂ) (l : LinearCoefficients V B)
    (x : B × ComplexPlane₂) : linearPrimitive (c • l) x = c * linearPrimitive l x := by
  simp [linearPrimitive, smul_eq_mul, mul_assoc, mul_add]

@[simp] theorem linearCoefficients_zero (P : HolomorphicPeriodMap V B) :
    linearCoefficients P (0 : LinearCoefficients V B) = 0 := by
  funext j
  apply ContMDiffMap.ext
  intro b
  simp

theorem linearCoefficients_add (P : HolomorphicPeriodMap V B)
    (l l' : LinearCoefficients V B) :
    linearCoefficients P (l + l') = linearCoefficients P l + linearCoefficients P l' := by
  funext j
  apply ContMDiffMap.ext
  intro b
  simp [add_mul, Finset.sum_add_distrib]

theorem linearCoefficients_smul (P : HolomorphicPeriodMap V B) (c : ℂ)
    (l : LinearCoefficients V B) :
    linearCoefficients P (c • l) = c • linearCoefficients P l := by
  funext j
  apply ContMDiffMap.ext
  intro b
  simp [smul_eq_mul, mul_assoc, mul_add]

/-- The real period isomorphism sends a vector to the corresponding
linear combination of its genuine original period columns. -/
theorem periodEquiv_sum_columns (P : HolomorphicPeriodMap V B) (b : B)
    (v : RealPlane₄) :
    (∑ j, v j • P.periodEquiv b (Pi.single j 1)) = P.periodEquiv b v := by
  calc
    _ = P.periodEquiv b (∑ j, v j • Pi.single j 1) := by
      simp only [map_sum, map_smul]
    _ = P.periodEquiv b v := by
      congr 1
      simp only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single]

/-- Reconstruction of each complex coordinate from the actual inverse
real period coordinates, with the real scalars embedded in `ℂ`. -/
theorem periodEquiv_inverse_columns (P : HolomorphicPeriodMap V B) (b : B)
    (z : ComplexPlane₂) (k : Fin 2) :
    (∑ j, (P.periodEquiv b (Pi.single j 1)) k *
      (((P.periodEquiv b).symm z j : ℝ) : ℂ)) = z k := by
  have h := congrArg (fun w : ComplexPlane₂ => w k)
    (periodEquiv_sum_columns P b ((P.periodEquiv b).symm z))
  simpa [Finset.sum_apply, Complex.real_smul, mul_comm] using h

/-- The primitive of the actual period coefficients is literally the
original complex-linear form on the original covering space. -/
theorem primitive_linearCoefficients_apply (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) (x : B × ComplexPlane₂) :
    primitive P (linearCoefficients P l) x = linearPrimitive l x := by
  simp only [primitive, linearCoefficients_apply, linearPrimitive, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_assoc, ← Finset.mul_sum, periodEquiv_inverse_columns]

/-- Function-level equality, independent of any quotient or cohomology
comparison. -/
theorem primitive_linearCoefficients (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) :
    primitive P (linearCoefficients P l) = linearPrimitive l :=
  funext (primitive_linearCoefficients_apply P l)

/-- On each actual lattice period the corresponding character is the
value of the original complex-linear form. -/
theorem character_linearCoefficients (P : HolomorphicPeriodMap V B)
    (l : LinearCoefficients V B) (b : B) (g : standardLattice) :
    character (linearCoefficients P l) b g = linearPrimitive l (b, P.periodEquiv b g) := by
  rw [← primitive_linearCoefficients_apply P l]
  simp [primitive, character]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Cocycle
