import Wikipedia.HomotopyGroupsOfSpheres.CayleyReversibility
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureSquares
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureDirections

/-!
# Cayley coordinates on the original quaternionic complex-structure locus

Relative symplectic operators are reversible with respect to the base complex
structure. Their Cayley coordinates therefore lie in its anticommuting skew
subspace. Conversely every such skew direction produces an actual complex
structure, and the two constructions are continuous inverses.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

variable {n : ℕ}

def relative (J J' : Space n) : symplecticSubgroup n :=
  (toSymplectic J)⁻¹ * toSymplectic J'

theorem relative_self (J : Space n) : relative J J = 1 := inv_mul_cancel _

theorem relative_reversible (J J' : Space n) :
    toSymplectic J * relative J J' = (relative J J')⁻¹ * toSymplectic J := by
  have hs : toSymplectic J' * toSymplectic J' = toSymplectic J * toSymplectic J :=
    (toSymplectic_mul_self J').trans (toSymplectic_mul_self J).symm
  calc
    toSymplectic J * relative J J' = toSymplectic J' := mul_inv_cancel_left _ _
    _ = (toSymplectic J')⁻¹ * (toSymplectic J' * toSymplectic J') :=
      (inv_mul_cancel_left _ _).symm
    _ = (toSymplectic J')⁻¹ * (toSymplectic J * toSymplectic J) := by rw [hs]
    _ = (relative J J')⁻¹ * toSymplectic J := by
      rw [relative, mul_inv_rev, inv_inv, mul_assoc]

theorem cayley_sandwich (J : Space n) (K : AntiSkewSpace J) :
    symplecticCayley n (antiSkewToSkew J K) * toSymplectic J *
      symplecticCayley n (antiSkewToSkew J K) = toSymplectic J := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact CayleyReversibility.fraction_sandwich_of_anticommute
    (toOrthogonalSkew n (antiSkewToSkew J K)) J.val.val K.property.2

theorem point_square (J : Space n) (K : AntiSkewSpace J) :
    (toSymplectic J * symplecticCayley n (antiSkewToSkew J K)).val.val.val.comp
      (toSymplectic J * symplecticCayley n (antiSkewToSkew J K)).val.val.val =
        -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  let q := symplecticCayley n (antiSkewToSkew J K)
  have he : (toSymplectic J * q) * (toSymplectic J * q) = antipode n := by
    calc
      (toSymplectic J * q) * (toSymplectic J * q) =
          toSymplectic J * (q * toSymplectic J * q) := by simp only [mul_assoc]
      _ = toSymplectic J * toSymplectic J := by rw [cayley_sandwich J K]
      _ = antipode n := toSymplectic_mul_self J
  have hop := congrArg (fun a : symplecticSubgroup n ↦ a.val.val.val) he
  rw [antipode_operator] at hop
  exact hop

def point (J : Space n) (K : AntiSkewSpace J) : Space n :=
  ofSymplecticSquare (toSymplectic J * symplecticCayley n (antiSkewToSkew J K))
    (point_square J K)

theorem point_toSymplectic (J : Space n) (K : AntiSkewSpace J) :
    toSymplectic (point J K) = toSymplectic J * symplecticCayley n (antiSkewToSkew J K) :=
  toSymplectic_ofSymplecticSquare _ _

theorem relative_point (J : Space n) (K : AntiSkewSpace J) :
    relative J (point J K) = symplecticCayley n (antiSkewToSkew J K) := by
  rw [relative, point_toSymplectic, inv_mul_cancel_left]

theorem point_zero (J : Space n) : point J 0 = J := by
  apply toSymplectic_injective
  rw [point_toSymplectic, map_zero, symplecticCayley_zero, mul_one]

def domain (J : Space n) : Set (Space n) :=
  {J' | relative J J' ∈ cayleyDomain n}

theorem point_mem_domain (J : Space n) (K : AntiSkewSpace J) : point J K ∈ domain J := by
  change relative J (point J K) ∈ cayleyDomain n
  rw [relative_point]
  exact symplecticCayley_mem n _

theorem self_mem_domain (J : Space n) : J ∈ domain J := by
  change relative J J ∈ cayleyDomain n
  rw [relative_self]
  exact one_mem_cayleyDomain n

theorem coordinate_anticommute (J J' : Space n) (h : J' ∈ domain J) :
    J.val.val.comp (fraction (relative J J').val.val.val) =
      -((fraction (relative J J').val.val.val).comp J.val.val) := by
  have he := congrArg (fun a : symplecticSubgroup n ↦ a.val.val.val)
    (relative_reversible J J')
  exact CayleyReversibility.fraction_anticommute_of_reversible
    (relative J J').val J.val.val he h

def coordinate (J J' : Space n) (h : J' ∈ domain J) : AntiSkewSpace J :=
  ⟨(symplecticCoordinate n (relative J J') h).val,
    ⟨(symplecticCoordinate n (relative J J') h).property, coordinate_anticommute J J' h⟩⟩

theorem antiSkewToSkew_coordinate (J J' : Space n) (h : J' ∈ domain J) :
    antiSkewToSkew J (coordinate J J' h) = symplecticCoordinate n (relative J J') h := rfl

theorem point_coordinate (J J' : Space n) (h : J' ∈ domain J) :
    point J (coordinate J J' h) = J' := by
  apply toSymplectic_injective
  rw [point_toSymplectic, antiSkewToSkew_coordinate]
  have hs : relative J J' ∈ cayleyDomain n := h
  exact (congrArg (fun a : symplecticSubgroup n ↦ toSymplectic J * a)
    (symplecticCayley_coordinate n (relative J J') hs)).trans (mul_inv_cancel_left _ _)

theorem coordinate_point (J : Space n) (K : AntiSkewSpace J) :
    coordinate J (point J K) (point_mem_domain J K) = K := by
  apply Subtype.ext
  change fraction (relative J (point J K)).val.val.val = K.val
  rw [relative_point]
  exact fraction_fraction K.val (one_add_isInvertible (toOrthogonalSkew n (antiSkewToSkew J K)))

theorem coordinate_self (J : Space n) : coordinate J J (self_mem_domain J) = 0 := by
  apply Subtype.ext
  have h := congrArg (fun K : AntiSkewSpace J ↦ K.val) (coordinate_point J 0)
  change fraction (relative J (point J 0)).val.val.val = 0 at h
  rw [point_zero] at h
  exact h

theorem continuous_relative (J : Space n) : Continuous (relative J) :=
  continuous_const.mul continuous_toSymplectic

theorem isOpen_domain (J : Space n) : IsOpen (domain J) :=
  (isOpen_cayleyDomain n).preimage (continuous_relative J)

theorem continuous_point (J : Space n) : Continuous (point J) := by
  have hc : Continuous (fun K : AntiSkewSpace J ↦
      toSymplectic J * symplecticCayley n (antiSkewToSkew J K)) :=
    continuous_const.mul ((continuous_symplecticCayley n).comp (continuous_antiSkewToSkew J))
  exact continuous_ofSymplecticSquare _ hc (point_square J)

theorem continuous_coordinate (J : Space n) :
    Continuous (fun p : domain J ↦ coordinate J p.val p.property) := by
  have hr : Continuous (fun p : domain J ↦ relative J p.val) :=
    (continuous_relative J).comp continuous_subtype_val
  have hop : Continuous (fun p : domain J ↦ (relative J p.val).val.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp hr))
  have hf : Continuous (fun p : domain J ↦ fraction (relative J p.val).val.val.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hs : (1 + (relative J p.val).val.val.val).IsInvertible := p.property
    exact ContinuousAt.comp (f := fun p : domain J ↦ (relative J p.val).val.val.val) (x := p)
      (contDiffAt_fraction (relative J p.val).val.val.val hs).continuousAt hop.continuousAt
  exact hf.subtype_mk _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley
