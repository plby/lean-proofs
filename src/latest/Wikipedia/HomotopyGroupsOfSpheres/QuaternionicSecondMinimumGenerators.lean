import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReferenceRotation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureExponential

/-!
# Midpoints and generators of minimum complex-structure rotations

For a fixed complex structure `a`, the midpoint parameter `P` and the unit
generator `Q` are related by `Q = -a P` and `P = a Q`. Both belong to the
actual anticommuting complex-structure locus. These are continuous inverse
maps, and their exponential paths are exactly the original rotations.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures

open ComplexStructureRotationAlgebra Exponential

variable {n : ℕ} {a : ComplexStructures.Space n}

private theorem continuous_neg_map {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] {f : X → V} (h : Continuous f) :
    Continuous (fun x ↦ -(f x)) := h.neg

private theorem mul_scalar_sum {A : Type*} [Ring A] [Algebra ℝ A] (J K : A) (c s : ℝ) :
    J * (c • (1 : A) + s • K) = c • J + s • (J * K) := by
  rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm]

private theorem product_anticommute_left {A : Type*} [Ring A] (J K : A)
    (hJ : J * J = -1) (hJK : J * K = -(K * J)) :
    J * (J * K) = -((J * K) * J) := by
  rw [left_mul_product J K hJ, product_mul_left J K hJ hJK]

private theorem negative_anticommute_right {A : Type*} [Ring A] (J K : A)
    (hJK : J * K = -(K * J)) : J * (-K) = -((-K) * J) := by
  rw [mul_neg, neg_mul, hJK]

private theorem left_mul_negative_product {A : Type*} [Ring A] (J K : A)
    (hJ : J * J = -1) : J * (-(J * K)) = K := by
  rw [mul_neg, left_mul_product J K hJ, neg_neg]

def midpointParameter (Q : Space a) : Space a :=
  ⟨productStructure Q,
    product_anticommute_left a.val.val Q.val.val.val a.property Q.property⟩

def generatorParameter (P : Space a) : Space a :=
  ⟨ComplexStructures.negative (productStructure P),
    negative_anticommute_right a.val.val (productStructure P).val.val
      (product_anticommute_left a.val.val P.val.val.val a.property P.property)⟩

theorem midpoint_generator (P : Space a) : midpointParameter (generatorParameter P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact left_mul_negative_product a.val.val P.val.val.val a.property

theorem generator_midpoint (Q : Space a) : generatorParameter (midpointParameter Q) = Q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change -(a.val.val * (a.val.val * Q.val.val.val)) = Q.val.val.val
  rw [left_mul_product a.val.val Q.val.val.val a.property, neg_neg]

theorem continuous_midpointParameter : Continuous (midpointParameter (a := a)) :=
  continuous_productStructure.subtype_mk _

theorem continuous_generatorParameter : Continuous (generatorParameter (a := a)) := by
  have h : Continuous (fun P : Space a ↦ (productStructure P).val) :=
    continuous_subtype_val.comp continuous_productStructure
  have hn := continuous_neg_map (V := SkewSpace n) h
  exact (hn.subtype_mk _).subtype_mk _

def generatorHomeomorph (a : ComplexStructures.Space n) : Space a ≃ₜ Space a where
  toFun := generatorParameter
  invFun := midpointParameter
  left_inv := midpoint_generator
  right_inv := generator_midpoint
  continuous_toFun := continuous_generatorParameter
  continuous_invFun := continuous_midpointParameter

theorem left_mul_generator (P : Space a) :
    a.val.val * (generatorParameter P).val.val.val = P.val.val.val :=
  left_mul_negative_product a.val.val P.val.val.val a.property

theorem rotation_toSymplectic (P : Space a) (θ : ℝ) :
    ComplexStructures.toSymplectic (rotation P θ) =
      ComplexStructures.toSymplectic a * exp (θ • (generatorParameter P).val.val) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change Real.cos θ • a.val.val + Real.sin θ • P.val.val.val =
    a.val.val * (exp (θ • (generatorParameter P).val.val)).val.val.val
  rw [ComplexStructures.exp_smul, mul_scalar_sum, left_mul_generator]

def generatorDirection (P : Space a) : ComplexStructures.AntiSkewSpace a :=
  ⟨(generatorParameter P).val.val.val,
    ⟨(generatorParameter P).val.val.property, (generatorParameter P).property⟩⟩

theorem generatorDirection_toSkew (P : Space a) :
    ComplexStructures.antiSkewToSkew a (generatorDirection P) =
      (generatorParameter P).val.val := rfl

theorem exponentialCurve_generatorDirection (P : Space a) (t : ℝ) :
    ComplexStructures.exponentialCurve a (generatorDirection P) t = rotation P t := by
  apply ComplexStructures.toSymplectic_injective
  rw [ComplexStructures.exponentialCurve_toSymplectic, generatorDirection_toSkew,
    rotation_toSymplectic]

def speed (P : Space a) : ComplexStructures.AntiSkewSpace a := Real.pi • generatorDirection P

theorem speed_toSkew (P : Space a) :
    ComplexStructures.antiSkewToSkew a (speed P) = Real.pi • (generatorParameter P).val.val :=
  (ComplexStructures.antiSkewToSkew a).map_smul _ _

theorem exponentialCurve_speed (P : Space a) (t : ℝ) :
    ComplexStructures.exponentialCurve a (speed P) t = rotation P (t * Real.pi) := by
  apply ComplexStructures.toSymplectic_injective
  rw [ComplexStructures.exponentialCurve_toSymplectic, speed_toSkew, smul_smul,
    rotation_toSymplectic]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.AnticommutingStructures
