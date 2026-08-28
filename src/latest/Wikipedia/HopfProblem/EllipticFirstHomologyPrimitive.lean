import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A primitive relation in the elliptic abelianization

This file computes the actual integral quotient by the relation `(a,b,-m)`.
An explicit Bézout identity gives quotient coordinates and a section, so
the quotient is genuinely free of rank two, with no residual torsion.

These are algebraic quotient statements. No identification with singular
homology is asserted here; the degree-one Hurewicz bridge is separate.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.PrimitiveRelation

abbrev Source := Fin 3 → ℤ
abbrev Target := Fin 2 → ℤ

def relationVector (a b m : ℤ) : Source := ![a, b, -m]

def relationSubmodule (a b m : ℤ) : Submodule ℤ Source :=
  Submodule.span ℤ {relationVector a b m}

/-- The first two coordinates are the original translation lattice. -/
def firstTwo : Target →ₗ[ℤ] Source where
  toFun x := ![x 0, x 1, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp

/-- The translation lattice maps to the quotient by the relation. -/
def translationMap (a b m : ℤ) : Target →ₗ[ℤ] (Source ⧸ relationSubmodule a b m) :=
  (relationSubmodule a b m).mkQ.comp firstTwo

/-- Explicit coordinates on the rank-two quotient. -/
def projection (a b m u t : ℤ) : Source →ₗ[ℤ] Target where
  toFun x := ![m * x 0 + a * x 2, x 1 - b * (u * x 0 - t * x 2)]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

@[simp] theorem projection_apply (a b m u t : ℤ) (x : Source) :
    projection a b m u t x =
      ![m * x 0 + a * x 2, x 1 - b * (u * x 0 - t * x 2)] := rfl

/-- A linear section of the quotient coordinates once `u*a+t*m=1`. -/
def sectionMap (u t : ℤ) : Target →ₗ[ℤ] Source where
  toFun y := ![t * y 0, y 1, u * y 0]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

@[simp] theorem sectionMap_apply (u t : ℤ) (y : Target) :
    sectionMap u t y = ![t * y 0, y 1, u * y 0] := rfl

/-- Read the coefficient of the primitive relation. -/
def relationCoefficient (u t : ℤ) : Source →ₗ[ℤ] ℤ where
  toFun x := u * x 0 - t * x 2
  map_add' x y := by simp; ring
  map_smul' r x := by simp; ring

variable (a b m u t : ℤ) (hbez : u * a + t * m = 1)

include hbez

theorem projection_relation : projection a b m u t (relationVector a b m) = 0 := by
  ext i
  fin_cases i
  · change m * a + a * (-m) = 0
    ring
  · change b - b * (u * a - t * (-m)) = 0
    linear_combination -b * hbez

@[simp] theorem projection_section (y : Target) :
    projection a b m u t (sectionMap u t y) = y := by
  ext i
  fin_cases i
  · change m * (t * y 0) + a * (u * y 0) = y 0
    linear_combination y 0 * hbez
  · change y 1 - b * (u * (t * y 0) - t * (u * y 0)) = y 1
    ring

theorem projection_surjective : Function.Surjective (projection a b m u t) :=
  fun y => ⟨sectionMap u t y, projection_section a b m u t hbez y⟩

@[simp] theorem relationCoefficient_relation :
    relationCoefficient u t (relationVector a b m) = 1 := by
  simpa [relationCoefficient, relationVector] using hbez

omit hbez in
@[simp] theorem relationCoefficient_section (y : Target) :
    relationCoefficient u t (sectionMap u t y) = 0 := by
  simp [relationCoefficient]
  ring

/-- Every vector splits into its relation coefficient and its two
quotient coordinates, by an explicit integral formula. -/
theorem decomposition (x : Source) :
    x = relationCoefficient u t x • relationVector a b m +
      sectionMap u t (projection a b m u t x) := by
  ext i
  fin_cases i
  · change x 0 = (u * x 0 - t * x 2) • a + t * (m * x 0 + a * x 2)
    simp only [smul_eq_mul]
    linear_combination -(x 0) * hbez
  · change x 1 = (u * x 0 - t * x 2) • b + (x 1 - b * (u * x 0 - t * x 2))
    simp only [smul_eq_mul]
    ring
  · change x 2 = (u * x 0 - t * x 2) • (-m) + u * (m * x 0 + a * x 2)
    simp only [smul_eq_mul]
    linear_combination -(x 2) * hbez

/-- The kernel is exactly the integral span of the stated relation. -/
theorem projection_ker : LinearMap.ker (projection a b m u t) = relationSubmodule a b m := by
  ext x
  constructor
  · intro hx
    have hx0 : projection a b m u t x = 0 := hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨relationCoefficient u t x, ?_⟩
    simpa only [hx0, map_zero, add_zero] using (decomposition a b m u t hbez x).symm
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change projection a b m u t (c • relationVector a b m) = 0
    rw [map_smul, projection_relation a b m u t hbez, smul_zero]

/-- The primitive-relation quotient is explicitly free of rank two. -/
def quotientEquiv : (Source ⧸ relationSubmodule a b m) ≃ₗ[ℤ] Target :=
  (Submodule.quotEquivOfEq _ _ (projection_ker a b m u t hbez).symm).trans
    ((projection a b m u t).quotKerEquivOfSurjective
      (projection_surjective a b m u t hbez))

@[simp] theorem quotientEquiv_mk (x : Source) :
    quotientEquiv a b m u t hbez (Submodule.Quotient.mk x) = projection a b m u t x := by
  simp [quotientEquiv]

@[simp] theorem quotientEquiv_symm_apply (y : Target) :
    (quotientEquiv a b m u t hbez).symm y = Submodule.Quotient.mk (sectionMap u t y) := by
  apply (quotientEquiv a b m u t hbez).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_mk,
    projection_section a b m u t hbez]

omit hbez

/-- An integral triangular map describing the translation coordinates. -/
def planeMap (m c : ℤ) : Target →ₗ[ℤ] Target :=
  (!![m, 0; -c, 1] : Matrix (Fin 2) (Fin 2) ℤ).mulVecLin

theorem planeMap_apply (m c : ℤ) (x : Target) :
    planeMap m c x = ![m * x 0, x 1 - c * x 0] := by
  ext i
  fin_cases i <;>
    simp [planeMap, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

theorem planeMap_range_iff (m c : ℤ) (y : Target) :
    y ∈ LinearMap.range (planeMap m c) ↔ m ∣ y 0 := by
  change (∃ x, planeMap m c x = y) ↔ m ∣ y 0
  constructor
  · rintro ⟨x, rfl⟩
    rw [planeMap_apply]
    exact ⟨x 0, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨![n, y 1 + c * n], ?_⟩
    rw [planeMap_apply]
    ext i
    fin_cases i <;> simp [hn]

/-- Reduction of the first coordinate modulo the unsigned order. -/
def firstReduction (m : ℤ) : Target →ₗ[ℤ] ZMod m.natAbs :=
  (Int.castAddHom (ZMod m.natAbs)).toIntLinearMap.comp (LinearMap.proj 0)

@[simp] theorem firstReduction_apply (m : ℤ) (x : Target) :
    firstReduction m x = (x 0 : ZMod m.natAbs) := rfl

theorem firstReduction_surjective (m : ℤ) : Function.Surjective (firstReduction m) := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨![n, 0], rfl⟩

theorem firstReduction_eq_zero_iff (m : ℤ) (x : Target) :
    firstReduction m x = 0 ↔ m ∣ x 0 := by
  rw [firstReduction_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.natCast_natAbs, abs_dvd]

theorem planeMap_range_eq_ker (m c : ℤ) :
    LinearMap.range (planeMap m c) = LinearMap.ker (firstReduction m) := by
  ext x
  rw [planeMap_range_iff, LinearMap.mem_ker, firstReduction_eq_zero_iff]

/-- The actual cokernel is cyclic, also when `m = 0`, where it is infinite. -/
def planeCokernelEquiv (m c : ℤ) :
    (Target ⧸ LinearMap.range (planeMap m c)) ≃ₗ[ℤ] ZMod m.natAbs :=
  (Submodule.quotEquivOfEq _ _ (planeMap_range_eq_ker m c)).trans
    ((firstReduction m).quotKerEquivOfSurjective (firstReduction_surjective m))

@[simp] theorem planeCokernelEquiv_mk (m c : ℤ) (x : Target) :
    planeCokernelEquiv m c (Submodule.Quotient.mk x) = (x 0 : ZMod m.natAbs) := by
  simp [planeCokernelEquiv]

theorem planeCokernel_card (m c : ℤ) :
    Nat.card (Target ⧸ LinearMap.range (planeMap m c)) = m.natAbs := by
  calc
    _ = Nat.card (ZMod m.natAbs) := Nat.card_congr (planeCokernelEquiv m c).toEquiv
    _ = m.natAbs := Nat.card_zmod _

theorem planeMap_range_index (m c : ℤ) :
    (LinearMap.range (planeMap m c)).toAddSubgroup.index = m.natAbs :=
  planeCokernel_card m c

theorem planeMap_injective (m c : ℤ) (hm : m ≠ 0) : Function.Injective (planeMap m c) := by
  intro x y h
  have h0 : m * x 0 = m * y 0 := by simpa [planeMap_apply] using congrFun h 0
  have hx0 : x 0 = y 0 := mul_left_cancel₀ hm h0
  have h1 : x 1 - c * x 0 = y 1 - c * y 0 := by
    simpa [planeMap_apply] using congrFun h 1
  have hx1 : x 1 = y 1 := by
    rw [hx0] at h1
    exact sub_left_inj.mp h1
  ext i
  fin_cases i <;> assumption

/-- Restricting quotient coordinates to translations gives a triangular map. -/
theorem projection_firstTwo (x : Target) :
    projection a b m u t (firstTwo x) = planeMap m (b * u) x := by
  rw [planeMap_apply]
  ext i
  fin_cases i
  · change m * x 0 + a * 0 = m * x 0
    ring
  · change x 1 - b * (u * x 0 - t * 0) = x 1 - (b * u) * x 0
    ring

theorem projection_comp_firstTwo :
    (projection a b m u t).comp firstTwo = planeMap m (b * u) :=
  LinearMap.ext (projection_firstTwo a b m u t)

include hbez

theorem quotientEquiv_comp_translationMap :
    (quotientEquiv a b m u t hbez).toLinearMap.comp (translationMap a b m) =
      planeMap m (b * u) := by
  apply LinearMap.ext
  intro x
  change quotientEquiv a b m u t hbez (Submodule.Quotient.mk (firstTwo x)) = _
  rw [quotientEquiv_mk, projection_firstTwo]

/-- In the free quotient coordinates the image of translations is exactly
the sublattice with first coordinate divisible by `m`. -/
theorem translationMap_range_iff (y : Source ⧸ relationSubmodule a b m) :
    y ∈ LinearMap.range (translationMap a b m) ↔
      m ∣ quotientEquiv a b m u t hbez y 0 := by
  rw [← planeMap_range_iff m (b * u)]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    exact (LinearMap.congr_fun (quotientEquiv_comp_translationMap a b m u t hbez) x).symm
  · rintro ⟨x, hx⟩
    refine ⟨x, (quotientEquiv a b m u t hbez).injective ?_⟩
    exact (LinearMap.congr_fun (quotientEquiv_comp_translationMap a b m u t hbez) x).trans hx

/-- The translation lattice has index `|m|` in the actual quotient, not just
in an auxiliary model. -/
theorem translationMap_range_index :
    (LinearMap.range (translationMap a b m)).toAddSubgroup.index = m.natAbs := by
  calc
    _ = (LinearMap.range (planeMap m (b * u))).toAddSubgroup.index := by
      rw [← quotientEquiv_comp_translationMap a b m u t hbez,
        LinearMap.range_comp, Submodule.map_toAddSubgroup]
      exact (AddSubgroup.index_map_equiv _ (quotientEquiv a b m u t hbez).toAddEquiv).symm
    _ = m.natAbs := planeMap_range_index m (b * u)

theorem translationMap_injective (hm : m ≠ 0) :
    Function.Injective (translationMap a b m) := by
  intro x y h
  apply planeMap_injective m (b * u) hm
  rw [← quotientEquiv_comp_translationMap a b m u t hbez]
  exact congrArg (quotientEquiv a b m u t hbez) h

omit hbez

abbrev RelationQuotient (a b m : ℤ) := Source ⧸ relationSubmodule a b m

def e₀ : Source := ![1, 0, 0]
def e₁ : Source := ![0, 1, 0]
def e₂ : Source := ![0, 0, 1]

theorem source_decomposition (x : Source) :
    x = x 0 • e₀ + x 1 • e₁ + x 2 • e₂ := by
  ext i
  fin_cases i <;> simp [e₀, e₁, e₂]

theorem functional_apply (F : Source →ₗ[ℤ] ℤ) (x : Source) :
    F x = x 0 * F e₀ + x 1 * F e₁ + x 2 * F e₂ := by
  calc
    F x = F (x 0 • e₀ + x 1 • e₁ + x 2 • e₂) := congrArg F (source_decomposition x)
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

/-- Restrict an integral functional on the actual quotient to the two
translation basis vectors. -/
def dualRestriction (a b m : ℤ) :
    (RelationQuotient a b m →ₗ[ℤ] ℤ) →ₗ[ℤ] Target where
  toFun F := ![F (Submodule.Quotient.mk e₀), F (Submodule.Quotient.mk e₁)]
  map_add' F G := by ext i; fin_cases i <;> simp
  map_smul' n F := by ext i; fin_cases i <;> simp

@[simp] theorem dualRestriction_apply (a b m : ℤ)
    (F : RelationQuotient a b m →ₗ[ℤ] ℤ) :
    dualRestriction a b m F =
      ![F (Submodule.Quotient.mk e₀), F (Submodule.Quotient.mk e₁)] := rfl

def coordinateFunctional (s t k : ℤ) : Source →ₗ[ℤ] ℤ where
  toFun x := s * x 0 + t * x 1 + k * x 2
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' n x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem quotientFunctional_relation (a b m : ℤ)
    (F : RelationQuotient a b m →ₗ[ℤ] ℤ) :
    a * F (Submodule.Quotient.mk e₀) + b * F (Submodule.Quotient.mk e₁) =
      m * F (Submodule.Quotient.mk e₂) := by
  let ℓ : Source →ₗ[ℤ] ℤ := F.comp (relationSubmodule a b m).mkQ
  have hr : ℓ (relationVector a b m) = 0 := by
    change F (Submodule.Quotient.mk (relationVector a b m)) = 0
    rw [(Submodule.Quotient.mk_eq_zero (relationSubmodule a b m)).mpr
      (Submodule.subset_span (Set.mem_singleton _)), map_zero]
  rw [functional_apply] at hr
  apply sub_eq_zero.mp
  simpa [relationVector, ℓ, sub_eq_add_neg] using hr

/-- The dual translation image is the congruence lattice prescribed by
the relation. This assertion needs no Bézout or nonzero hypothesis. -/
theorem dualRestriction_range_iff (a b m : ℤ) (v : Target) :
    v ∈ LinearMap.range (dualRestriction a b m) ↔ m ∣ a * v 0 + b * v 1 := by
  change (∃ F, dualRestriction a b m F = v) ↔ _
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨F (Submodule.Quotient.mk e₂), ?_⟩
    simpa [dualRestriction] using quotientFunctional_relation a b m F
  · rintro ⟨k, hk⟩
    have hker : relationSubmodule a b m ≤
        LinearMap.ker (coordinateFunctional (v 0) (v 1) k) := by
      apply Submodule.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change v 0 * a + v 1 * b + k * (-m) = 0
      calc
        _ = a * v 0 + b * v 1 - m * k := by ring
        _ = 0 := sub_eq_zero.mpr hk
    let F : RelationQuotient a b m →ₗ[ℤ] ℤ :=
      (relationSubmodule a b m).liftQ (coordinateFunctional (v 0) (v 1) k) hker
    refine ⟨F, ?_⟩
    ext i
    fin_cases i <;> simp [dualRestriction, F, coordinateFunctional, e₀, e₁]

theorem dualRestriction_apply_translation (a b m : ℤ)
    (F : RelationQuotient a b m →ₗ[ℤ] ℤ) (x : Target) :
    F (translationMap a b m x) =
      x 0 * dualRestriction a b m F 0 + x 1 * dualRestriction a b m F 1 := by
  simpa [translationMap, firstTwo, dualRestriction] using
    functional_apply (F.comp (relationSubmodule a b m).mkQ) (firstTwo x)

/-- For nonzero order, an integral functional is determined by its values
on the translation lattice. -/
theorem dualRestriction_injective (a b m : ℤ) (hm : m ≠ 0) :
    Function.Injective (dualRestriction a b m) := by
  intro F G h
  have h₀ : F (Submodule.Quotient.mk e₀) = G (Submodule.Quotient.mk e₀) :=
    congrFun h 0
  have h₁ : F (Submodule.Quotient.mk e₁) = G (Submodule.Quotient.mk e₁) :=
    congrFun h 1
  have h₂ : F (Submodule.Quotient.mk e₂) = G (Submodule.Quotient.mk e₂) := by
    apply mul_left_cancel₀ hm
    calc
      m * F (Submodule.Quotient.mk e₂) =
          a * F (Submodule.Quotient.mk e₀) + b * F (Submodule.Quotient.mk e₁) :=
            (quotientFunctional_relation a b m F).symm
      _ = a * G (Submodule.Quotient.mk e₀) + b * G (Submodule.Quotient.mk e₁) := by
            rw [h₀, h₁]
      _ = m * G (Submodule.Quotient.mk e₂) := quotientFunctional_relation a b m G
  apply (relationSubmodule a b m).quot_hom_ext F G
  intro x
  calc
    F (Submodule.Quotient.mk x) = x 0 * F (Submodule.Quotient.mk e₀) +
        x 1 * F (Submodule.Quotient.mk e₁) + x 2 * F (Submodule.Quotient.mk e₂) :=
      functional_apply (F.comp (relationSubmodule a b m).mkQ) x
    _ = x 0 * G (Submodule.Quotient.mk e₀) +
        x 1 * G (Submodule.Quotient.mk e₁) + x 2 * G (Submodule.Quotient.mk e₂) := by
      rw [h₀, h₁, h₂]
    _ = G (Submodule.Quotient.mk x) :=
      (functional_apply (G.comp (relationSubmodule a b m).mkQ) x).symm

end Wikipedia.HopfProblem.Elliptic.PrimitiveRelation
