import Wikipedia.NoExoticSixSphere.QuaternionicHopfProjectionOperator

/-!
# Division between points in the same actual quaternionic Hopf fiber

The Hermitian pairing of two lifts is their right quaternionic quotient.
This is proved from the original Hopf polynomial's projection operator.
It does not give the seven-sphere an associative group structure.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

abbrev FiberGroup := Wikipedia.HopfProblem.UnitQuaternionSphere.UnitQuaternions

def divisionQuaternion (x y : V 8) : ℍ :=
  star (first x) * first y + star (second x) * second y

theorem unit_normSq_sum (x : Sphere 7) :
    Quaternion.normSq (first x.val) + Quaternion.normSq (second x.val) = 1 := by
  rw [normSq_sum, mem_sphere_zero_iff_norm.mp x.property, one_pow]

theorem projectionOperator_hopf_first (x : Sphere 7) (y : V 8) :
    first (projectionOperator (sphereMap x).val y) =
      (2 : ℝ) • (first x.val * divisionQuaternion x.val y) := by
  have hc : 1 + (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val)) =
      2 * Quaternion.normSq (first x.val) := by linarith [unit_normSq_sum x]
  rw [first_projectionOperator]
  change projectedFirst (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val))
    (tailQuaternion (polynomial x.val)) (first y) (second y) = _
  rw [polynomial, tailQuaternion_join]
  simp only [projectedFirst, divisionQuaternion, hc, mul_add, ← mul_assoc,
    Quaternion.self_mul_star, Quaternion.coe_mul_eq_smul, smul_add, smul_smul,
    smul_mul_assoc]

theorem projectionOperator_hopf_second (x : Sphere 7) (y : V 8) :
    second (projectionOperator (sphereMap x).val y) =
      (2 : ℝ) • (second x.val * divisionQuaternion x.val y) := by
  have hc : 1 - (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val)) =
      2 * Quaternion.normSq (second x.val) := by linarith [unit_normSq_sum x]
  rw [second_projectionOperator]
  change projectedSecond (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val))
    (tailQuaternion (polynomial x.val)) (first y) (second y) = _
  rw [polynomial, tailQuaternion_join]
  simp only [projectedSecond, divisionQuaternion, hc, Quaternion.star_smul,
    star_mul, star_star, mul_add, ← mul_assoc, Quaternion.self_mul_star,
    Quaternion.coe_mul_eq_smul, smul_add, smul_smul, smul_mul_assoc]

theorem first_mul_division (x y : Sphere 7) (h : sphereMap x = sphereMap y) :
    first x.val * divisionQuaternion x.val y.val = first y.val := by
  have he := projectionOperator_hopf_first x y.val
  rw [h, projectionOperator_self, map_smul] at he
  exact (smul_right_injective ℍ (by norm_num : (2 : ℝ) ≠ 0)) he.symm

theorem second_mul_division (x y : Sphere 7) (h : sphereMap x = sphereMap y) :
    second x.val * divisionQuaternion x.val y.val = second y.val := by
  have he := projectionOperator_hopf_second x y.val
  rw [h, projectionOperator_self, map_smul] at he
  exact (smul_right_injective ℍ (by norm_num : (2 : ℝ) ≠ 0)) he.symm

theorem divisionQuaternion_normSq (x y : Sphere 7) (h : sphereMap x = sphereMap y) :
    Quaternion.normSq (divisionQuaternion x.val y.val) = 1 := by
  have hy := unit_normSq_sum y
  rw [← first_mul_division x y h, ← second_mul_division x y h, map_mul, map_mul,
    ← add_mul, unit_normSq_sum, one_mul] at hy
  exact hy

def fiberDivision (x y : Sphere 7) (h : sphereMap x = sphereMap y) : FiberGroup :=
  ⟨divisionQuaternion x.val y.val, by
    constructor
    · rw [Quaternion.star_mul_self, divisionQuaternion_normSq x y h, Quaternion.coe_one]
    · rw [Quaternion.self_mul_star, divisionQuaternion_normSq x y h, Quaternion.coe_one]⟩

theorem divisionQuaternion_self (x : Sphere 7) : divisionQuaternion x.val x.val = 1 := by
  rw [divisionQuaternion, Quaternion.star_mul_self, Quaternion.star_mul_self,
    ← Quaternion.coe_add, unit_normSq_sum, Quaternion.coe_one]

theorem fiberDivision_self (x : Sphere 7) : fiberDivision x x rfl = 1 :=
  Subtype.ext (divisionQuaternion_self x)

theorem continuous_divisionQuaternion :
    Continuous (fun z : V 8 × V 8 ↦ divisionQuaternion z.1 z.2) :=
  ((conjugation.continuous.comp (first.continuous.comp continuous_fst)).mul
    (first.continuous.comp continuous_snd)).add
      ((conjugation.continuous.comp (second.continuous.comp continuous_fst)).mul
        (second.continuous.comp continuous_snd))

theorem continuous_fiberDivision {X : Type*} [TopologicalSpace X]
    (a b : C(X, Sphere 7)) (h : ∀ x, sphereMap (a x) = sphereMap (b x)) :
    Continuous (fun x ↦ fiberDivision (a x) (b x) (h x)) :=
  (continuous_divisionQuaternion.comp
    ((continuous_subtype_val.comp a.continuous).prodMk
      (continuous_subtype_val.comp b.continuous))).subtype_mk _

end NoExoticSixSphere.QuaternionicHopf
