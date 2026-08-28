import Wikipedia.HopfProblem.EllipticFirstHomologyLattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The two elliptic relations in Lemma 7.19

In coordinates `(c,g₁,g₂)`, the two relations are `(-a₁,3,0)` and
`(-a₂,0,4)`. This file computes their actual integral span and quotient.
The quotient character has coefficients `(12,4*a₁,3*a₂)`.

These are statements about the integral presentation matrices; no
identification with the singular homology of a glued space is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.PairRelations

abbrev Source := Fin 3 → ℤ

def firstRelation (a₁ : ℤ) : Source := ![-a₁, 3, 0]

def secondRelation (a₂ : ℤ) : Source := ![-a₂, 0, 4]

def relationSubmodule (a₁ a₂ : ℤ) : Submodule ℤ Source :=
  Submodule.span ℤ {firstRelation a₁, secondRelation a₂}

/-- The integral character specified in the source. -/
def projection (a₁ a₂ : ℤ) : Source →ₗ[ℤ] ℤ where
  toFun x := 12 * x 0 + 4 * a₁ * x 1 + 3 * a₂ * x 2
  map_add' x y := by simp; ring
  map_smul' n x := by simp; ring

@[simp] theorem projection_apply (a₁ a₂ : ℤ) (x : Source) :
    projection a₁ a₂ x = 12 * x 0 + 4 * a₁ * x 1 + 3 * a₂ * x 2 := rfl

@[simp] theorem projection_firstRelation (a₁ a₂ : ℤ) :
    projection a₁ a₂ (firstRelation a₁) = 0 := by
  simp [firstRelation]
  ring

@[simp] theorem projection_secondRelation (a₁ a₂ : ℤ) :
    projection a₁ a₂ (secondRelation a₂) = 0 := by
  simp [secondRelation]
  ring

theorem relations_le_ker (a₁ a₂ : ℤ) :
    relationSubmodule a₁ a₂ ≤ LinearMap.ker (projection a₁ a₂) := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact projection_firstRelation a₁ a₂
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact projection_secondRelation a₁ a₂

/-- A preimage of one obtained from the two Bézout identities. -/
def sectionVector (u t p q : ℤ) : Source := ![t - q, u, -p]

variable (a₁ a₂ u t p q : ℤ)
variable (h₁ : u * a₁ + t * 3 = 1) (h₂ : p * a₂ + q * 4 = 1)

include h₁ h₂

theorem projection_sectionVector :
    projection a₁ a₂ (sectionVector u t p q) = 1 := by
  change 12 * (t - q) + 4 * a₁ * u + 3 * a₂ * (-p) = 1
  linear_combination 4 * h₁ - 3 * h₂

theorem projection_surjective_of_bezout : Function.Surjective (projection a₁ a₂) := by
  intro n
  refine ⟨n • sectionVector u t p q, ?_⟩
  rw [map_smul, projection_sectionVector a₁ a₂ u t p q h₁ h₂]
  simp

/-- The two Bézout identities extract the relation coefficients from
every kernel vector, using integral arithmetic only. -/
theorem projection_ker_of_bezout :
    LinearMap.ker (projection a₁ a₂) = relationSubmodule a₁ a₂ := by
  apply le_antisymm _ (relations_le_ker a₁ a₂)
  intro x hx
  change 12 * x 0 + 4 * a₁ * x 1 + 3 * a₂ * x 2 = 0 at hx
  have hd₁ : (3 : ℤ) ∣ x 1 := by
    refine ⟨t * x 1 - u * (4 * x 0 + a₁ * x 1 + a₂ * x 2), ?_⟩
    linear_combination u * hx - x 1 * h₁
  have hd₂ : (4 : ℤ) ∣ x 2 := by
    refine ⟨p * (3 * x 0 + a₁ * x 1 + a₂ * x 2) + q * x 2, ?_⟩
    linear_combination -p * hx - x 2 * h₂
  obtain ⟨s₁, hs₁⟩ := hd₁
  obtain ⟨s₂, hs₂⟩ := hd₂
  apply Submodule.mem_span_pair.mpr
  refine ⟨s₁, s₂, ?_⟩
  ext i
  fin_cases i
  · change s₁ * (-a₁) + s₂ * (-a₂) = x 0
    apply mul_left_cancel₀ (show (12 : ℤ) ≠ 0 by norm_num)
    rw [hs₁, hs₂] at hx
    linear_combination -hx
  · change s₁ * 3 + s₂ * 0 = x 1
    simp [hs₁, mul_comm]
  · change s₁ * 0 + s₂ * 4 = x 2
    simp [hs₂, mul_comm]

/-- The genuine integral quotient by both relations is infinite cyclic. -/
def quotientEquivOfBezout : (Source ⧸ relationSubmodule a₁ a₂) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (projection_ker_of_bezout a₁ a₂ u t p q h₁ h₂).symm).trans
    ((projection a₁ a₂).quotKerEquivOfSurjective
      (projection_surjective_of_bezout a₁ a₂ u t p q h₁ h₂))

@[simp] theorem quotientEquivOfBezout_mk (x : Source) :
    quotientEquivOfBezout a₁ a₂ u t p q h₁ h₂ (Submodule.Quotient.mk x) =
      projection a₁ a₂ x := by
  simp [quotientEquivOfBezout]

omit h₁ h₂

/-- Nondivisibility by three supplies the needed Bézout coefficients,
including for negative integers. -/
theorem bezout_three (a : ℤ) (ha : ¬ (3 : ℤ) ∣ a) :
    ∃ u t : ℤ, u * a + t * 3 = 1 := by
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases hmod with hmod | hmod
  · refine ⟨1, -(a / 3), ?_⟩
    omega
  · refine ⟨-1, a / 3 + 1, ?_⟩
    omega

/-- Oddness supplies the Bézout identity with four. -/
theorem bezout_four (a : ℤ) (ha : Odd a) :
    ∃ p q : ℤ, p * a + q * 4 = 1 := by
  obtain ⟨k, hk⟩ := ha
  have hmod : a % 4 = 1 ∨ a % 4 = 3 := by omega
  rcases hmod with hmod | hmod
  · refine ⟨1, -(a / 4), ?_⟩
    omega
  · refine ⟨-1, a / 4 + 1, ?_⟩
    omega

variable (ha₁ : ¬ (3 : ℤ) ∣ a₁) (ha₂ : Odd a₂)

include ha₁ ha₂

theorem projection_surjective : Function.Surjective (projection a₁ a₂) := by
  obtain ⟨u, t, h₁⟩ := bezout_three a₁ ha₁
  obtain ⟨p, q, h₂⟩ := bezout_four a₂ ha₂
  exact projection_surjective_of_bezout a₁ a₂ u t p q h₁ h₂

theorem projection_ker : LinearMap.ker (projection a₁ a₂) = relationSubmodule a₁ a₂ := by
  obtain ⟨u, t, h₁⟩ := bezout_three a₁ ha₁
  obtain ⟨p, q, h₂⟩ := bezout_four a₂ ha₂
  exact projection_ker_of_bezout a₁ a₂ u t p q h₁ h₂

/-- The actual quotient is infinite cyclic for every admissible pair. -/
def quotientEquiv : (Source ⧸ relationSubmodule a₁ a₂) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ (projection_ker a₁ a₂ ha₁ ha₂).symm).trans
    ((projection a₁ a₂).quotKerEquivOfSurjective
      (projection_surjective a₁ a₂ ha₁ ha₂))

@[simp] theorem quotientEquiv_mk (x : Source) :
    quotientEquiv a₁ a₂ ha₁ ha₂ (Submodule.Quotient.mk x) =
      12 * x 0 + 4 * a₁ * x 1 + 3 * a₂ * x 2 := by
  simp [quotientEquiv]

@[simp] theorem quotientEquiv_c :
    quotientEquiv a₁ a₂ ha₁ ha₂ (Submodule.Quotient.mk ![1, 0, 0]) = 12 := by simp

@[simp] theorem quotientEquiv_g₁ :
    quotientEquiv a₁ a₂ ha₁ ha₂ (Submodule.Quotient.mk ![0, 1, 0]) = 4 * a₁ := by simp

@[simp] theorem quotientEquiv_g₂ :
    quotientEquiv a₁ a₂ ha₁ ha₂ (Submodule.Quotient.mk ![0, 0, 1]) = 3 * a₂ := by simp

omit ha₁ ha₂ in
/-- In the main choice `(a₁,a₂)=(1,-1)`, the quotient character is `(12,4,-3)`. -/
theorem main_projection (x : Source) : projection 1 (-1) x = 12 * x 0 + 4 * x 1 - 3 * x 2 := by
  simp [projection]
  ring

omit ha₁ ha₂

/-- The main coefficient choice gives an unconditional integral isomorphism. -/
def mainQuotientEquiv : (Source ⧸ relationSubmodule 1 (-1)) ≃ₗ[ℤ] ℤ :=
  quotientEquiv 1 (-1) (by norm_num) (by norm_num)

@[simp] theorem mainQuotientEquiv_mk (x : Source) :
    mainQuotientEquiv (Submodule.Quotient.mk x) = 12 * x 0 + 4 * x 1 - 3 * x 2 := by
  simp [mainQuotientEquiv, sub_eq_add_neg]

/-- The class of `g₁ + g₂` is the positive primitive generator in the main case. -/
@[simp] theorem mainQuotientEquiv_symm_apply (n : ℤ) :
    mainQuotientEquiv.symm n = Submodule.Quotient.mk ![0, n, n] := by
  apply mainQuotientEquiv.injective
  rw [LinearEquiv.apply_symm_apply, mainQuotientEquiv_mk]
  simp
  ring

abbrev PairedTarget := Fin 4 → ℤ

/-- The source's signed map to both raw coinvariant lattices, using the
actual invariant functionals rather than independently chosen coordinates. -/
def pairedCoinvariantMap : Lattice →ₗ[ℤ] PairedTarget where
  toFun w := ![γ w, psiOne w, -γ w, -psiTwo w]
  map_add' w z := by
    ext i
    fin_cases i <;> simp [γ, add_comm]
  map_smul' a w := by
    ext i
    fin_cases i <;> simp [γ, psiOne, psiTwo] <;> ring

@[simp] theorem pairedCoinvariantMap_apply (w : Lattice) :
    pairedCoinvariantMap w = ![γ w, psiOne w, -γ w, -psiTwo w] := rfl

/-- An integral preimage for every vector satisfying the one image relation. -/
def pairedCoinvariantLift (x : PairedTarget) : Lattice :=
  ![x 0, x 1 + x 3, -x 1 - 2 * x 3, 0]

theorem pairedCoinvariantMap_lift (x : PairedTarget) (hx : x 0 + x 2 = 0) :
    pairedCoinvariantMap (pairedCoinvariantLift x) = x := by
  ext i
  fin_cases i <;>
    simp [pairedCoinvariantMap, pairedCoinvariantLift, γ, psiOne, psiTwo] <;> omega

theorem pairedCoinvariantMap_range_iff (x : PairedTarget) :
    x ∈ LinearMap.range pairedCoinvariantMap ↔ x 0 + x 2 = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    simp [pairedCoinvariantMap]
  · intro hx
    exact ⟨pairedCoinvariantLift x, pairedCoinvariantMap_lift x hx⟩

/-- The image is the full, saturated three-generator lattice occurring
before imposing the two elliptic relations. -/
theorem pairedCoinvariantMap_range_eq_span :
    LinearMap.range pairedCoinvariantMap =
      Submodule.span ℤ {(![1, 0, -1, 0] : PairedTarget),
        ![0, 1, 0, 0], ![0, 0, 0, 1]} := by
  ext x
  rw [pairedCoinvariantMap_range_iff, Submodule.mem_span_triple]
  constructor
  · intro hx
    have hx₂ : -x 0 = x 2 := by omega
    refine ⟨x 0, x 1, x 3, ?_⟩
    ext i
    fin_cases i <;> simp [hx₂]
  · rintro ⟨a, b, c, rfl⟩
    simp

def sumFirstThird : PairedTarget →ₗ[ℤ] ℤ where
  toFun x := x 0 + x 2
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem sumFirstThird_apply (x : PairedTarget) :
    sumFirstThird x = x 0 + x 2 := rfl

theorem sumFirstThird_surjective : Function.Surjective sumFirstThird := by
  intro z
  exact ⟨![z, 0, 0, 0], by simp⟩

theorem pairedCoinvariantMap_range_eq_ker :
    LinearMap.range pairedCoinvariantMap = LinearMap.ker sumFirstThird := by
  ext x
  rw [pairedCoinvariantMap_range_iff, LinearMap.mem_ker, sumFirstThird_apply]

/-- The actual raw paired cokernel is infinite cyclic. -/
def pairedCoinvariantCokernelEquiv :
    (PairedTarget ⧸ LinearMap.range pairedCoinvariantMap) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ pairedCoinvariantMap_range_eq_ker).trans
    (sumFirstThird.quotKerEquivOfSurjective sumFirstThird_surjective)

@[simp] theorem pairedCoinvariantCokernelEquiv_mk (x : PairedTarget) :
    pairedCoinvariantCokernelEquiv (Submodule.Quotient.mk x) = x 0 + x 2 := by
  simp [pairedCoinvariantCokernelEquiv]

end Wikipedia.HopfProblem.Elliptic.PairRelations
