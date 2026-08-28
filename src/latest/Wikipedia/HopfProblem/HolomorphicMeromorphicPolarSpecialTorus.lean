import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarRepresentation
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionSpecial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# The full native meromorphic field of a generic special period torus

Every original meromorphic function has the actual native polar line bundle
and two holomorphic sections constructed above. On a special period torus
outside the proved exceptional set, the classification theorem makes any
two such native sections proportional. The original full meromorphic
function is therefore constant.

The resulting algebra equivalence and zero transcendence degree concern
the original sheaf of locally represented fraction-stalk sections, not a
restricted field defined using line-bundle ratios.
-/

noncomputable section

open Set Topology TopologicalSpace Bundle
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSpecialTorus

open SpecialPeriods UpperHalfPlane PeriodTorusTypeOneOne

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

local instance torusGlobalDomain_connected (z : ℍ) :
    ConnectedSpace (⊤ : Opens (specialPeriodMap.point z).Torus) :=
  Subtype.connectedSpace isConnected_univ

/-- Every genuine meromorphic function on the actual special torus is
constant away from the actual exceptional set. No section presentation is
assumed: its native polar bundle is constructed from the original function. -/
theorem exists_eq_constant (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (s : Function IC (specialPeriodMap.point z).Torus) :
    ∃ c : ℂ, s = algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus) c := by
  let M := (specialPeriodMap.point z).Torus
  let e : (ℂ × ℂ) ≃L[ℂ] ComplexPlane₂ := (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
  obtain ⟨c, hc⟩ :=
    PeriodTorusLineBundleClassification.nativeSections_proportional_of_not_exceptional
      z (PolarRepresentation.bundleCore IC M e s).Fiber hz
      (PolarRepresentation.nativeDenominator IC M e s)
      (PolarRepresentation.nativeDenominator_ne_zero IC M e s)
      (PolarRepresentation.nativeNumerator IC M e s)
  exact ⟨c, PolarRepresentation.eq_constant_of_native_proportionality IC M e s c hc⟩

/-- The canonical constant map onto the original meromorphic field is
surjective, as a conclusion of analytic preparation and native bundles. -/
theorem algebraMap_surjective (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    Function.Surjective
      (algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus)) := by
  intro s
  obtain ⟨c, hc⟩ := exists_eq_constant z hz s
  exact ⟨c, hc.symm⟩

/-- Actual complex constants identify with the full native meromorphic
function field, with the canonical inclusion as the forward map. -/
def constantAlgebraEquiv (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    ℂ ≃ₐ[ℂ] Function IC (specialPeriodMap.point z).Torus :=
  AlgEquiv.ofBijective (Algebra.ofId ℂ (Function IC (specialPeriodMap.point z).Torus))
    ⟨(algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus)).injective,
      algebraMap_surjective z hz⟩

@[simp] theorem constantAlgebraEquiv_apply (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (c : ℂ) :
    constantAlgebraEquiv z hz c =
      algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus) c := rfl

/-- The original meromorphic function field is genuinely algebra-isomorphic
to `ℂ`; the field itself has not been redefined. -/
def meromorphicFieldEquiv (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    Function IC (specialPeriodMap.point z).Torus ≃ₐ[ℂ] ℂ :=
  (constantAlgebraEquiv z hz).symm

@[simp] theorem meromorphicFieldEquiv_constant (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (c : ℂ) :
    meromorphicFieldEquiv z hz
      (algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus) c) = c :=
  (constantAlgebraEquiv z hz).symm_apply_apply c

/-- Complex vector-space dimension of the full native meromorphic field. -/
theorem meromorphic_finrank_eq_one (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    Module.finrank ℂ (Function IC (specialPeriodMap.point z).Torus) = 1 := by
  calc
    _ = Module.finrank ℂ ℂ := (meromorphicFieldEquiv z hz).toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self ℂ

/-- The actual cardinal-valued algebraic dimension is zero. -/
theorem meromorphic_trdeg_eq_zero (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    Algebra.trdeg ℂ (Function IC (specialPeriodMap.point z).Torus) = 0 := by
  let : Algebra.IsAlgebraic ℂ (Function IC (specialPeriodMap.point z).Torus) :=
    ⟨fun s => by
      obtain ⟨c, rfl⟩ := algebraMap_surjective z hz s
      exact isAlgebraic_algebraMap c⟩
  exact trdeg_eq_zero

/-- The corresponding natural-number algebraic dimension is also zero. -/
theorem meromorphic_trdeg_toNat_eq_zero (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet) :
    Cardinal.toNat (Algebra.trdeg ℂ (Function IC (specialPeriodMap.point z).Torus)) = 0 := by
  rw [meromorphic_trdeg_eq_zero z hz]
  simp

/-- The exceptional values can be taken on the actual normalized base,
independently of the meromorphic function. -/
theorem exists_eq_constant_of_base_not_exceptional (z : ℍ)
    (hz : specialSourceCoordinate z ∉ exceptionalPeriodBaseValues)
    (s : Function IC (specialPeriodMap.point z).Torus) :
    ∃ c : ℂ, s = algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus) c := by
  apply exists_eq_constant z _ s
  rw [exceptionalTypeOneOneSet_eq]
  exact fun h => hz ⟨z, h, rfl⟩

/-- On every torus above a nonexceptional actual base value the full
native meromorphic field has transcendence degree zero. -/
theorem meromorphic_trdeg_eq_zero_of_base_not_exceptional (z : ℍ)
    (hz : specialSourceCoordinate z ∉ exceptionalPeriodBaseValues) :
    Algebra.trdeg ℂ (Function IC (specialPeriodMap.point z).Torus) = 0 := by
  apply meromorphic_trdeg_eq_zero z
  rw [exceptionalTypeOneOneSet_eq]
  exact fun h => hz ⟨z, h, rfl⟩

/-- A single genuinely countable exceptional set works for every
meromorphic function on every actual special torus. -/
theorem exists_countable_exceptional_values :
    ∃ S : Set ℂ, S.Countable ∧ Dense Sᶜ ∧
      ∀ z : ℍ, specialSourceCoordinate z ∉ S →
        ∀ s : Function IC (specialPeriodMap.point z).Torus,
          ∃ c : ℂ, s = algebraMap ℂ (Function IC (specialPeriodMap.point z).Torus) c :=
  ⟨exceptionalPeriodBaseValues, exceptionalPeriodBaseValues_countable,
    exceptionalPeriodBaseValues_compl_dense, exists_eq_constant_of_base_not_exceptional⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSpecialTorus
