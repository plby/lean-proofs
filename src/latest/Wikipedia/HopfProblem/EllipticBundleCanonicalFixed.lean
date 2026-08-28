import Wikipedia.HopfProblem.EllipticBundleCanonicalAtlas
import Wikipedia.HopfProblem.EllipticBundleCanonicalCharts
import Wikipedia.HopfProblem.EllipticBundleFixedCharacters
import Wikipedia.HopfProblem.EllipticBundleCoreCriterion

/-!
# Canonical bundles at every admissible elliptic fixed period

The actual chart-derivative calculation identifies the canonical cocycle
at any fixed period, not only at the explicit central family period.
The general covector atlas supplies its full alternating-two-covector
fibres and pullback law; the character criterion gives the exact least
positive analytically trivial tensor-power degree.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

open HolomorphicCharacterBundle

local notation "I₂" => modelWithCornersSelf ℂ Model

variable (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)

def fixedData : TransitionData (Surface j p v hv) (Surface j p v hv) := by
  letI := affineAction j p v hv.1
  exact AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j p v hv)
    (canonicalCharacter j)

instance fixedData_isHolomorphic : (fixedData j p v hv).IsHolomorphic I₂ := by
  let := affineAction j p v hv.1
  change (AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j p v hv)
    (canonicalCharacter j)).IsHolomorphic I₂
  infer_instance

theorem fixed_chart_source_subset (i : Surface j p v hv) :
    (chartAt Model i).source ⊆ (fixedData j p v hv).baseSet i := by
  let := affineAction j p v hv.1
  exact quotient_chart_source_subset
    (E := Model) (surfaceProjection_isQuotientCoveringMap j p v hv) i

/-- The character transition is determined by the actual surface Jacobian. -/
theorem fixed_jacobian_eq_transition (i k x : Surface j p v hv)
    (hi : x ∈ (chartAt Model i).source) (hk : x ∈ (chartAt Model k).source) :
    LinearMap.det (fderiv ℂ
      ((chartAt Model i).symm.trans (chartAt Model k)) (chartAt Model i x)).toLinearMap =
        ((fixedData j p v hv).transition k i x : ℂ) := by
  let := affineAction j p v hv.1
  have hiB := fixed_chart_source_subset j p v hv i hi
  have hkB := fixed_chart_source_subset j p v hv k hk
  have hc : (fixedData j p v hv).transition i k x *
      (fixedData j p v hv).transition k i x = 1 :=
    ((fixedData j p v hv).transition_comp k i k x ⟨⟨hkB, hiB⟩, hkB⟩).trans
      ((fixedData j p v hv).transition_self k x hkB)
  have hinv := congrArg (fun u : ℂˣ => (u : ℂ)) (eq_inv_of_mul_eq_one_right hc)
  rw [Units.val_inv_eq_inv_val] at hinv
  rw [surface_chart_det_fderiv j p v hv i k x hi hk, fixedPeriod_linearEquiv_det, hinv]
  change ((canonicalPhase j)⁻¹) ^
      (AssociatedCore.deck (surfaceCovering j p v hv) i k x).toAdd.val =
    (canonicalCharacter j (AssociatedCore.deck (surfaceCovering j p v hv) i k x) : ℂ)⁻¹
  rw [canonicalCharacter_apply, inv_pow]

/-- This atlas identifies the original cocycle fibres with full continuous
alternating two-covectors, using the original surface chart derivatives. -/
def fixedAtlas : CocycleAtlas (fixedData j p v hv) where
  chart := chartAt Model
  chart_mem_maximalAtlas := fun i => IsManifold.chart_mem_maximalAtlas i
  chart_source_subset := fixed_chart_source_subset j p v hv
  mem_source := mem_chart_source Model
  jacobian_eq := fixed_jacobian_eq_transition j p v hv

abbrev fixedBundle := (fixedAtlas j p v hv).core

def fixedPowerData (n : ℕ) : TransitionData (Surface j p v hv) (Surface j p v hv) := by
  letI := affineAction j p v hv.1
  exact AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j p v hv)
    (canonicalCharacter j ^ n)

instance fixedPowerData_isHolomorphic (n : ℕ) :
    (fixedPowerData j p v hv n).IsHolomorphic I₂ := by
  let := affineAction j p v hv.1
  change (AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j p v hv)
    (canonicalCharacter j ^ n)).IsHolomorphic I₂
  infer_instance

/-- The power cocycle is the tensor power of the geometric canonical cocycle. -/
@[simp] theorem fixedPowerData_transition (n : ℕ) (i k x : Surface j p v hv) :
    (fixedPowerData j p v hv n).transition i k x =
      ((fixedData j p v hv).transition i k x) ^ n := by
  let := affineAction j p v hv.1
  exact AssociatedCore.data_pow_transition
    (surfaceProjection_isQuotientCoveringMap j p v hv) (canonicalCharacter j) n i k x

@[simp] theorem fixedPowerData_one : fixedPowerData j p v hv 1 = fixedData j p v hv := by
  let := affineAction j p v hv.1
  exact congrArg (AssociatedCore.data (surfaceProjection_isQuotientCoveringMap j p v hv))
    (pow_one (canonicalCharacter j))

/-- Actual fibre-linear analytic product triviality occurs exactly at the
multiples of the elliptic order. -/
theorem fixedPower_analyticTrivialization_iff (n : ℕ) :
    Nonempty ((fixedPowerData j p v hv n).AnalyticTrivialization I₂) ↔ j.order ∣ n := by
  let := affineAction j p v hv.1
  have h := BundleCore.characterCore_power_analyticTrivialization_iff
    (surfaceProjection_isQuotientCoveringMap j p v hv) (canonicalCharacter j)
      (affineAction_holomorphic j p v hv.1) n
  exact h.trans (by rw [canonicalCharacter_orderOf])

theorem fixedPower_order_isLeast :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((fixedPowerData j p v hv n).AnalyticTrivialization I₂)} j.order := by
  refine ⟨⟨j.order_pos,
    (fixedPower_analyticTrivialization_iff j p v hv j.order).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((fixedPower_analyticTrivialization_iff j p v hv n).mp hn.2)

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
