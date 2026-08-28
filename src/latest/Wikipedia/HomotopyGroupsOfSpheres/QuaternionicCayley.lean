import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicOperatorGroup
import Wikipedia.NoExoticSixSphere.CayleyChart

/-!
# Cayley coordinates within the quaternionic operator group

The real Cayley transform preserves the quaternionic commutant. Restricting
the existing orthogonal chart therefore gives actual local coordinates on
the symplectic group, with the original subspace topology.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

theorem inverse_mem_commutant (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (hT : T ∈ commutant n)
    (hi : T.IsInvertible) : T.inverse ∈ commutant n := by
  apply (mem_commutant_iff n _).mpr
  intro q
  apply ContinuousLinearMap.ext
  intro v
  apply hi.injective
  change T (T.inverse (rightAction n q v)) = T (rightAction n q (T.inverse v))
  have hc (w : Vector (4 * n + 4)) : T (rightAction n q w) = rightAction n q (T w) :=
    DFunLike.congr_fun ((mem_commutant_iff n T).mp hT q) w
  rw [hi.self_apply_inverse, hc, hi.self_apply_inverse]

theorem fraction_mem_commutant (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (hT : T ∈ commutant n)
    (hi : (1 + T).IsInvertible) : fraction T ∈ commutant n :=
  (commutant n).mul_mem ((commutant n).sub_mem (commutant n).one_mem hT)
    (inverse_mem_commutant n (1 + T) ((commutant n).add_mem (commutant n).one_mem hT) hi)

/-- Skew-adjoint operators that also preserve quaternionic scalar multiplication. -/
def skewSubmodule (n : ℕ) :
    Submodule ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  skewAdjoint.submodule ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ⊓
    (commutant n).toSubmodule

abbrev SkewSpace (n : ℕ) := ↥(skewSubmodule n)

def toOrthogonalSkew (n : ℕ) : SkewSpace n →ₗ[ℝ] SkewOperators (4 * n + 4) where
  toFun K := ⟨K.val, K.property.1⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def symplecticCayley (n : ℕ) (K : SkewSpace n) : symplecticSubgroup n :=
  ⟨orthogonal (toOrthogonalSkew n K), (mem_symplecticSubgroup_iff n _).mpr
    (fraction_mem_commutant n K.val K.property.2
      (one_add_isInvertible (toOrthogonalSkew n K)))⟩

theorem continuous_toOrthogonalSkew (n : ℕ) : Continuous (toOrthogonalSkew n) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_symplecticCayley (n : ℕ) : Continuous (symplecticCayley n) := by
  have h : Continuous (fun K : SkewSpace n => orthogonal (toOrthogonalSkew n K)) :=
    (continuous_orthogonal (n := 4 * n + 4)).comp (continuous_toOrthogonalSkew n)
  exact h.subtype_mk _

def cayleyDomain (n : ℕ) : Set (symplecticSubgroup n) :=
  {a | (1 + a.val.val.val).IsInvertible}

theorem isOpen_cayleyDomain (n : ℕ) : IsOpen (cayleyDomain n) :=
  isOpen_domain.preimage continuous_subtype_val

def symplecticCoordinate (n : ℕ) (a : symplecticSubgroup n) (ha : a ∈ cayleyDomain n) :
    SkewSpace n :=
  ⟨fraction a.val.val.val, ⟨fraction_adjoint_eq_neg a.val ha,
    fraction_mem_commutant n a.val.val.val
      ((mem_symplecticSubgroup_iff n a.val).mp a.property) ha⟩⟩

theorem continuous_symplecticCoordinate (n : ℕ) :
    Continuous (fun a : cayleyDomain n => symplecticCoordinate n a.val a.property) :=
  (continuous_subtype_val.comp
    (continuous_coordinate (fun a : cayleyDomain n => a.val.val)
      (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.property))).subtype_mk _

theorem symplecticCayley_mem (n : ℕ) (K : SkewSpace n) :
    symplecticCayley n K ∈ cayleyDomain n := orthogonal_mem_domain (toOrthogonalSkew n K)

theorem symplecticCayley_coordinate (n : ℕ) (a : symplecticSubgroup n)
    (ha : a ∈ cayleyDomain n) : symplecticCayley n (symplecticCoordinate n a ha) = a :=
  Subtype.ext (orthogonal_coordinate a.val ha)

theorem symplecticCoordinate_cayley (n : ℕ) (K : SkewSpace n) :
    symplecticCoordinate n (symplecticCayley n K) (symplecticCayley_mem n K) = K := by
  apply Subtype.ext
  change fraction (fraction K.val) = K.val
  exact fraction_fraction K.val (one_add_isInvertible (toOrthogonalSkew n K))

/-- The Cayley neighborhood is homeomorphic to the actual quaternionic skew-adjoint space. -/
def cayleyHomeomorph (n : ℕ) : cayleyDomain n ≃ₜ SkewSpace n where
  toFun a := symplecticCoordinate n a.val a.property
  invFun K := ⟨symplecticCayley n K, symplecticCayley_mem n K⟩
  left_inv a := Subtype.ext (symplecticCayley_coordinate n a.val a.property)
  right_inv := symplecticCoordinate_cayley n
  continuous_toFun := continuous_symplecticCoordinate n
  continuous_invFun := (continuous_symplecticCayley n).subtype_mk _

theorem symplecticCayley_zero (n : ℕ) : symplecticCayley n 0 = 1 :=
  Subtype.ext orthogonal_zero

theorem one_mem_cayleyDomain (n : ℕ) : (1 : symplecticSubgroup n) ∈ cayleyDomain n :=
  identity_mem_domain

def cayleyCoordinates (n : ℕ) (a : symplecticSubgroup n) : SkewSpace n := by
  classical
  exact if h : a ∈ cayleyDomain n then symplecticCoordinate n a h else 0

theorem cayleyCoordinates_of_mem (n : ℕ) (a : symplecticSubgroup n)
    (ha : a ∈ cayleyDomain n) : cayleyCoordinates n a = symplecticCoordinate n a ha :=
  dif_pos ha

/-- The native open partial homeomorphism on the actual symplectic operator group. -/
def cayleyChart (n : ℕ) : OpenPartialHomeomorph (symplecticSubgroup n) (SkewSpace n) where
  toFun := cayleyCoordinates n
  invFun := symplecticCayley n
  source := cayleyDomain n
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' K _ := symplecticCayley_mem n K
  left_inv' a ha := by
    rw [cayleyCoordinates_of_mem n a ha]
    exact symplecticCayley_coordinate n a ha
  right_inv' K _ := by
    rw [cayleyCoordinates_of_mem n _ (symplecticCayley_mem n K)]
    exact symplecticCoordinate_cayley n K
  open_source := isOpen_cayleyDomain n
  open_target := isOpen_univ
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_symplecticCoordinate n).congr
      (fun a => (cayleyCoordinates_of_mem n a.val a.property).symm)
  continuousOn_invFun := (continuous_symplecticCayley n).continuousOn

theorem cayleyChart_one (n : ℕ) : cayleyChart n 1 = 0 := by
  change cayleyCoordinates n 1 = 0
  rw [← symplecticCayley_zero n, cayleyCoordinates_of_mem n _ (symplecticCayley_mem n 0),
    symplecticCoordinate_cayley]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
