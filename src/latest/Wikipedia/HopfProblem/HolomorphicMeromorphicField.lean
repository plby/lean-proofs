import Wikipedia.HopfProblem.HolomorphicMeromorphicStalk
import Mathlib.Algebra.Field.Basic

/-!
# The field of genuine meromorphic functions on a connected manifold

Inversion preserves local meromorphy: on the zero-germ locus the inverse
is zero, and near every nonzero germ one interchanges the actual local
numerator and denominator. The native identity principle proves that
a nonzero meromorphic function on a connected domain has no zero germs.
It is therefore a unit in the actual section ring.

The resulting field retains all locally represented fraction-stalk
sections. No global fraction representation is imposed.
-/

noncomputable section

open Set Topology TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- Pointwise inversion in the full local fraction fields is again
locally represented by genuine holomorphic fractions. -/
def inverseSection {U : Opens M} (a : Section I M U) : Section I M U := by
  classical
  refine ⟨fun x => (a x)⁻¹, ?_⟩
  intro x
  by_cases hx : a x = 0
  · obtain ⟨V, hVU, _, hxV, hV⟩ := exists_neighborhood_eq_of_germ_eq I M
      a (0 : Section I M U) x.val x.property x.property hx
    refine ⟨V, hxV, homOfLE hVU, 0, 1, ?_, ?_⟩
    · intro y
      rw [map_one]
      exact one_ne_zero
    · intro y
      have hy : a (Set.inclusion hVU y) = 0 := hV y
      change (a (Set.inclusion hVU y))⁻¹ = _
      rw [hy]
      simp only [fraction, map_zero, map_one, zero_div, inv_zero]
  · obtain ⟨V, hVU, hxV, p, q, hq, ha⟩ := local_representation I M a x
    let v : V := ⟨x.val, hxV⟩
    have hp : holomorphicGerm I M V v p ≠ 0 := by
      intro hzero
      apply hx
      have hav : a x = fraction I M V p q v := ha v
      rw [hav]
      change sectionGerm I M V v p / sectionGerm I M V v q = 0
      rw [(sectionGerm_eq_zero_iff I M V v p).mpr hzero, zero_div]
    obtain ⟨W, hWV, hxW, hWp⟩ :=
      HolomorphicFunctionSheaf.exists_open_restriction_germs_ne_zero I V p x.val hxV hp
    let pW := HolomorphicFunctionSheaf.restrictionAlgHom I M hWV p
    let qW := HolomorphicFunctionSheaf.restrictionAlgHom I M hWV q
    have hpW : ∀ y : W, holomorphicGerm I M W y pW ≠ 0 := fun y => hWp y
    refine ⟨W, hxW, homOfLE (hWV.trans hVU), qW, pW, hpW, ?_⟩
    intro y
    change (a (Set.inclusion (hWV.trans hVU) y))⁻¹ = fraction I M W qW pW y
    calc
      (a (Set.inclusion (hWV.trans hVU) y))⁻¹ =
          (fraction I M V p q (Set.inclusion hWV y))⁻¹ :=
        congrArg Inv.inv (ha (Set.inclusion hWV y))
      _ = (fraction I M W pW qW y)⁻¹ :=
        congrArg Inv.inv (fraction_restrict I M hWV p q y).symm
      _ = fraction I M W qW pW y := by simp only [fraction, inv_div]

@[simp] theorem inverseSection_apply {U : Opens M} (a : Section I M U) (x : U) :
    inverseSection I M a x = (a x)⁻¹ := rfl

/-- A nonzero meromorphic section on a connected domain has no zero
fraction germ at any point. -/
theorem section_ne_zero_at_of_ne_zero {U : Opens M} [PreconnectedSpace U]
    (a : Section I M U) (ha : a ≠ 0) (x : U) : a x ≠ 0 := by
  intro hx
  exact ha (section_eq_of_germ_eq I M a 0 x hx)

/-- Every nonzero section on a connected domain is a genuine unit. -/
theorem section_isUnit_of_ne_zero {U : Opens M} [PreconnectedSpace U]
    (a : Section I M U) (ha : a ≠ 0) : IsUnit a := by
  refine ⟨⟨a, inverseSection I M a, ?_, ?_⟩, rfl⟩
  · apply section_ext
    intro x
    exact mul_inv_cancel₀ (section_ne_zero_at_of_ne_zero I M a ha x)
  · apply section_ext
    intro x
    exact inv_mul_cancel₀ (section_ne_zero_at_of_ne_zero I M a ha x)

instance section_nontrivial (U : Opens M) [Nonempty U] : Nontrivial (Section I M U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact (zero_ne_one : (0 : Germ I M x.val) ≠ 1) (congrArg (fun a : Section I M U => a x) h)

/-- The actual ring of all locally meromorphic sections is a field on
every nonempty connected original domain. -/
instance section_field (U : Opens M) [ConnectedSpace U] : Field (Section I M U) :=
  Field.ofIsUnitOrEqZero fun a => by
    by_cases ha : a = 0
    · exact Or.inr ha
    · exact Or.inl (section_isUnit_of_ne_zero I M a ha)

@[simp] theorem section_inv_apply {U : Opens M} [ConnectedSpace U]
    (a : Section I M U) (x : U) : (a⁻¹) x = (a x)⁻¹ :=
  map_inv₀ (evalRingHom I M U x) a

/-- The field of genuine meromorphic functions on the original whole manifold. -/
abbrev Function := Section I M ⊤

/-- Complex constants act through the original native holomorphic functions. -/
def constantRingHom (U : Opens M) : ℂ →+* Section I M U :=
  (ofHolomorphicRingHom I M U).comp
    (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U))

instance section_algebra (U : Opens M) : Algebra ℂ (Section I M U) :=
  (constantRingHom I M U).toAlgebra

@[simp] theorem algebraMap_section (U : Opens M) (c : ℂ) :
    algebraMap ℂ (Section I M U) c =
      ofHolomorphic I M U (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U) c) := rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic
