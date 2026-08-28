import Wikipedia.HopfProblem.EllipticBundleCanonicalAtlas
import Wikipedia.HopfProblem.EllipticBundleCanonicalCharts
import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.EllipticBundleCoreCriterion

/-!
# The canonical character bundle of the central elliptic quotient surfaces

For the central periods and every admissible twist, the actual elliptic
surface charts identify the canonical bundle with the character cocycle
whose generator is `canonicalPhase`. The determinant equality comes from
the derivatives of the original affine action and the original quotient
charts. The fibres are identified with full continuous alternating
two-covectors by the canonical atlas construction.

The canonical bundle is then analytically identified with the actual
associated orbit quotient. Its power cocycles are explicitly the powers
of its original transition maps, and analytic triviality occurs exactly
in degrees divisible by the specified order three or four. No global
frame, coboundary expression, or triviality of this bundle is assumed.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

open HolomorphicCharacterBundle

local notation "I₂" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)
local notation "I₃q" => modelWithCornersSelf ℂ (Model × ℂ)

/-- The canonical-character cocycle of the actual surface covering. -/
def centralData (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    TransitionData (Surface j (centralPeriod j) v hv) (Surface j (centralPeriod j) v hv) := by
  letI := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (canonicalCharacter j)

instance centralData_isHolomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    (centralData j v hv).IsHolomorphic I₂ := by
  let := affineAction j (centralPeriod j) v hv.1
  change (AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j)).IsHolomorphic I₂
  infer_instance

theorem central_chart_source_subset (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (i : Surface j (centralPeriod j) v hv) :
    (chartAt Model i).source ⊆ (centralData j v hv).baseSet i := by
  let := affineAction j (centralPeriod j) v hv.1
  exact quotient_chart_source_subset
    (E := Model) (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) i

/-- The actual surface Jacobian is the reversed canonical-character
transition; the order reversal is forced by cotangent pullback. -/
theorem central_jacobian_eq_transition (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (i k x : Surface j (centralPeriod j) v hv)
    (hi : x ∈ (chartAt Model i).source) (hk : x ∈ (chartAt Model k).source) :
    LinearMap.det (fderiv ℂ
      ((chartAt Model i).symm.trans (chartAt Model k)) (chartAt Model i x)).toLinearMap =
        ((centralData j v hv).transition k i x : ℂ) := by
  let := affineAction j (centralPeriod j) v hv.1
  have hiB := central_chart_source_subset j v hv i hi
  have hkB := central_chart_source_subset j v hv k hk
  have hc : (centralData j v hv).transition i k x *
      (centralData j v hv).transition k i x = 1 :=
    ((centralData j v hv).transition_comp k i k x ⟨⟨hkB, hiB⟩, hkB⟩).trans
      ((centralData j v hv).transition_self k x hkB)
  have hinv := congrArg (fun u : ℂˣ => (u : ℂ)) (eq_inv_of_mul_eq_one_right hc)
  rw [Units.val_inv_eq_inv_val] at hinv
  rw [surface_chart_det_fderiv j (centralPeriod j) v hv i k x hi hk,
    central_linearEquiv_det, hinv]
  change ((canonicalPhase j)⁻¹) ^
      (AssociatedCore.deck (surfaceCovering j (centralPeriod j) v hv) i k x).toAdd.val =
    (canonicalCharacter j
      (AssociatedCore.deck (surfaceCovering j (centralPeriod j) v hv) i k x) : ℂ)⁻¹
  rw [canonicalCharacter_apply, inv_pow]

/-- The existing surface atlas identifies the actual character bundle
with the inverse-Jacobian canonical bundle. -/
def centralAtlas (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    CocycleAtlas (centralData j v hv) where
  chart := chartAt Model
  chart_mem_maximalAtlas := fun i => IsManifold.chart_mem_maximalAtlas i
  chart_source_subset := central_chart_source_subset j v hv
  mem_source := mem_chart_source Model
  jacobian_eq := central_jacobian_eq_transition j v hv

/-- The actual holomorphic canonical line bundle of the central quotient
surface, expressed in its character-cocycle charts. -/
abbrev centralBundle (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :=
  (centralAtlas j v hv).core

theorem centralBundle_holomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContMDiffVectorBundle ω ℂ (centralBundle j v hv).Fiber I₂ :=
  (centralAtlas j v hv).holomorphicVectorBundle

theorem centralBundle_fibre_rank_one (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Surface j (centralPeriod j) v hv) :
    Module.finrank ℂ ((centralBundle j v hv).Fiber x) = 1 :=
  (centralAtlas j v hv).fibre_rank_one x

theorem centralBundle_totalSpace_isManifold (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsManifold I₃ ω (centralBundle j v hv).TotalSpace :=
  (centralAtlas j v hv).totalSpace_isManifold

/-- The canonical fibre, in an actual analytic surface chart, is the full
space of continuous alternating two-covectors. -/
def centralCoordinateEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (i : Surface j (centralPeriod j) v hv) {x : Surface j (centralPeriod j) v hv}
    (hx : x ∈ (chartAt Model i).source) :
    (centralBundle j v hv).Fiber x ≃L[ℂ] TopCovector :=
  (centralAtlas j v hv).coordinateEquiv i hx

theorem central_inCoordinates_change (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (i k : Surface j (centralPeriod j) v hv) {x : Surface j (centralPeriod j) v hv}
    (hi : x ∈ (chartAt Model i).source) (hk : x ∈ (chartAt Model k).source)
    (z : (centralBundle j v hv).Fiber x) :
    (centralAtlas j v hv).inCoordinates k x z =
      ((centralAtlas j v hv).inCoordinates i x z).compContinuousLinearMap
        (fderiv ℂ ((chartAt Model k).symm.trans (chartAt Model i)) (chartAt Model k x)) :=
  (centralAtlas j v hv).inCoordinates_change i k hi hk z

/-- The canonical line bundle is analytically identified with the actual
diagonal orbit quotient for its character, retaining both original
topologies and analytic atlases. -/
def centralAssociatedIdentification (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := affineAction j (centralPeriod j) v hv.1
    letI := associatedChartedSpace (E := Model)
      (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (canonicalCharacter j)
    Diffeomorph I₃ I₃q (centralBundle j v hv).TotalSpace
      (AssociatedSpace (A := (centralPeriod j).val.Torus) (canonicalCharacter j)) ω := by
  letI := affineAction j (centralPeriod j) v hv.1
  let hq := surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv
  letI := associatedChartedSpace (E := Model) hq (canonicalCharacter j)
  exact AssociatedCore.identification hq (canonicalCharacter j)
    (affineAction_holomorphic j (centralPeriod j) v hv.1)

@[simp] theorem centralAssociatedIdentification_preserves_base
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (p : (centralBundle j v hv).TotalSpace) :
    letI := affineAction j (centralPeriod j) v hv.1
    projection (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j) (centralAssociatedIdentification j v hv p) = p.proj := by
  let := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.projection_toAssociated
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (canonicalCharacter j) p

/-- In every actual surface chart the identification uses the original
bundle scalar coordinate. In particular it is complex-linear on fibres. -/
theorem centralAssociatedIdentification_localTriv
    (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (i : Surface j (centralPeriod j) v hv) (p : (centralBundle j v hv).TotalSpace)
    (hp : p.proj ∈ (chartAt Model i).source) :
    letI := affineAction j (centralPeriod j) v hv.1
    centralAssociatedIdentification j v hv p =
      associatedMap (canonicalCharacter j)
        (AssociatedCore.lift
          (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) i p.proj,
          ((centralBundle j v hv).localTriv i p).2) := by
  let := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.toAssociated_localTriv
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (canonicalCharacter j)
    i p (central_chart_source_subset j v hv i hp)

/-- The character-cocycle realization of a tensor power of the canonical
line bundle. Its relation to the original transition maps is proved below;
the tensor-product interpretation uses the actual fibre tensor equivalences
and local-chart covariance in `AssociatedCoreTensor`. -/
def centralPowerData (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    TransitionData (Surface j (centralPeriod j) v hv) (Surface j (centralPeriod j) v hv) := by
  letI := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j ^ n)

instance centralPowerData_isHolomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) : (centralPowerData j v hv n).IsHolomorphic I₂ := by
  let := affineAction j (centralPeriod j) v hv.1
  change (AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j ^ n)).IsHolomorphic I₂
  infer_instance

@[simp] theorem centralPowerData_transition (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) (i k x : Surface j (centralPeriod j) v hv) :
    (centralPowerData j v hv n).transition i k x =
      ((centralData j v hv).transition i k x) ^ n := by
  let := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.data_pow_transition
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j) n i k x

@[simp] theorem centralPowerData_one (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    centralPowerData j v hv 1 = centralData j v hv := by
  simp only [centralPowerData, pow_one, centralData]

/-- A canonical tensor power admits an actual base-preserving,
fibrewise-linear analytic product diffeomorphism exactly when its degree
is divisible by the order of the elliptic quotient. -/
theorem centralPower_analyticTrivialization_iff (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    Nonempty ((centralPowerData j v hv n).AnalyticTrivialization I₂) ↔ j.order ∣ n := by
  let := affineAction j (centralPeriod j) v hv.1
  have h := BundleCore.characterCore_power_analyticTrivialization_iff
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (canonicalCharacter j) (affineAction_holomorphic j (centralPeriod j) v hv.1) n
  exact h.trans (by rw [canonicalCharacter_orderOf])

/-- The order three or four is the least positive analytically trivial
tensor-power degree of the actual canonical bundle. -/
theorem centralPower_order_isLeast (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((centralPowerData j v hv n).AnalyticTrivialization I₂)} j.order := by
  refine ⟨⟨j.order_pos,
    (centralPower_analyticTrivialization_iff j v hv j.order).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((centralPower_analyticTrivialization_iff j v hv n).mp hn.2)

theorem centralPower_order_trivial (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Nonempty ((centralPowerData j v hv j.order).AnalyticTrivialization I₂) :=
  (centralPower_analyticTrivialization_iff j v hv j.order).mpr (dvd_refl _)

theorem centralBundle_not_analytically_trivial (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : ¬ Nonempty ((centralData j v hv).AnalyticTrivialization I₂) := by
  intro h
  have h1 : Nonempty ((centralPowerData j v hv 1).AnalyticTrivialization I₂) := by
    simpa only [centralPowerData_one] using h
  have hd := (centralPower_analyticTrivialization_iff j v hv 1).mp h1
  cases j <;> norm_num [Kind.order] at hd

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
