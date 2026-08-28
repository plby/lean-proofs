import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingStructures
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureConjugation
import Wikipedia.HomotopyGroupsOfSpheres.ComplexStructureRotationAlgebra

/-!
# A symplectic lift of the reference rotation

The product `J₀ J` of anticommuting quaternionic complex structures is itself
a quaternionic complex structure. Conjugation by its half-angle exponential
sends `J₀` to `cos θ J₀ + sin θ J`, giving actual continuous transport along
the reference path.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

open ComplexStructureRotationAlgebra Exponential

variable {n : ℕ} {J₀ : ComplexStructures.Space n}

private theorem real_neg_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (r : ℝ) (v : V) : (-r) • v = -(r • v) := neg_smul r v

def productSkew (J : Space J₀) : SkewSpace n :=
  ⟨J₀.val.val * J.val.val.val, ⟨
    product_star J₀.val.val J.val.val.val J₀.val.property.1 J.val.val.property.1 J.property,
    (commutant n).mul_mem J₀.val.property.2 J.val.val.property.2⟩⟩

def productStructure (J : Space J₀) : ComplexStructures.Space n :=
  ⟨productSkew J,
    product_square J₀.val.val J.val.val.val J₀.property J.val.property J.property⟩

theorem productStructure_operator (J : Space J₀) :
    (productStructure J).val.val = J₀.val.val * J.val.val.val := rfl

theorem continuous_productStructure : Continuous (productStructure (J₀ := J₀)) := by
  have hJ : Continuous (fun J : Space J₀ ↦ J.val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact ((continuous_const.clm_comp hJ).subtype_mk _).subtype_mk _

def conjugator (J : Space J₀) (θ : ℝ) : symplecticSubgroup n :=
  exp ((θ / 2) • (productStructure J).val)

theorem conjugator_zero (J : Space J₀) : conjugator J 0 = 1 := by
  change exp (((0 : ℝ) / 2) • (productStructure J).val) = 1
  rw [zero_div, zero_smul, exp_zero]

theorem conjugator_inverse (J : Space J₀) (θ : ℝ) :
    (conjugator J θ)⁻¹ = exp ((-(θ / 2)) • (productStructure J).val) := by
  unfold conjugator
  symm
  have hn : (-(θ / 2)) • (productStructure J).val =
      -((θ / 2) • (productStructure J).val) :=
    real_neg_smul (V := SkewSpace n) _ _
  rw [hn, exp_neg]

theorem continuous_conjugator (J : Space J₀) : Continuous (conjugator J) :=
  (contMDiff_exp_smul (productStructure J).val).continuous.comp
    (continuous_id.div_const 2)

theorem conjugator_rotation (J : Space J₀) (θ : ℝ) :
    ComplexStructures.conjugate (conjugator J θ) J₀ = rotation J θ := by
  have hPJ : (productStructure J).val.val * J₀.val.val = J.val.val.val :=
    product_mul_left J₀.val.val J.val.val.val J₀.property J.property
  have hJP : J₀.val.val * (productStructure J).val.val = -J.val.val.val :=
    left_mul_product J₀.val.val J.val.val.val J₀.property
  have hKP : J.val.val.val * (productStructure J).val.val = J₀.val.val :=
    right_mul_product J₀.val.val J.val.val.val J.val.property J.property
  have hrot := conjugation_rotation J₀.val.val J.val.val.val (productStructure J).val.val
    hPJ hJP hKP (Real.cos (θ / 2)) (Real.sin (θ / 2))
  have hdouble : 2 * (θ / 2) = θ := by ring
  have hc : Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    rw [← Real.cos_two_mul', hdouble]
  have hs : 2 * Real.sin (θ / 2) * Real.cos (θ / 2) = Real.sin θ := by
    rw [← Real.sin_two_mul, hdouble]
  rw [hc, hs] at hrot
  apply Subtype.ext
  apply Subtype.ext
  rw [ComplexStructures.conjugate_operator, conjugator_inverse]
  change (exp ((θ / 2) • (productStructure J).val)).val.val.val *
    (J₀.val.val * (exp ((-(θ / 2)) • (productStructure J).val)).val.val.val) =
      Real.cos θ • J₀.val.val + Real.sin θ • J.val.val.val
  rw [ComplexStructures.exp_smul, ComplexStructures.exp_smul, Real.cos_neg, Real.sin_neg]
  exact hrot

theorem conjugator_pi (J : Space J₀) :
    ComplexStructures.conjugate (conjugator J Real.pi) J₀ =
      ComplexStructures.negative J₀ := by rw [conjugator_rotation, rotation_pi]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
