import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedTangent
import Wikipedia.HopfProblem.HolomorphicAutomorphismLocalRecovery

/-!
# A genuine compact-open detector for the vertical parameter

A small compact disc on a toric coordinate axis lies in an actual
inverse chart of the original coordinate covering. If an automorphism
from the vertical action carries its image into the chart target,
uniqueness of lifts recovers the entire scaled disc. Its endpoint then
recovers the nonzero complex parameter. Only compact-open convergence
is used, not convergence of differentials.
-/

noncomputable section

open Filter Set Topology Metric
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

open VerticalAction.FixedCoordinates HolomorphicAutomorphismLocalRecovery

local notation "E₃" => ToricCharts.CoordinateSpace 3
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "a₀" => ToricSpace.referenceTriangle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- The actual third-coordinate line in the original cusp tube. -/
def detectionLine (t : ℂ) : Domain :=
  ⟨![0, 0, t], by
    change ‖(0 : ℂ) * 0 * t‖ < CuspGeometry.data.radius
    simpa only [zero_mul, norm_zero] using CuspGeometry.data.radius_pos⟩

@[simp] theorem detectionLine_third (t : ℂ) :
    (detectionLine t : E₃) 2 = t := rfl

theorem detectionLine_continuous : Continuous detectionLine := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem coordinateAction_detectionLine (u : ℂˣ) (t : ℂ) :
    coordinateAction u (detectionLine t) = detectionLine ((u : ℂ) * t) := by
  apply Subtype.ext
  rw [coordinateAction_coe, diagonal_apply]
  ext j
  fin_cases j <;> simp [detectionLine]

theorem chart_recovers_parameter
    (e : OpenPartialHomeomorph Domain Threefold.Space)
    (he : EqOn (globalMap a₀) e e.source) {r : ℝ} (hr : 0 < r)
    (hs : MapsTo detectionLine (closedBall (0 : ℂ) r) e.source)
    (u : ℂˣ)
    (ht : ∀ t ∈ closedBall (0 : ℂ) r,
      verticalHom u (globalMap a₀ (detectionLine t)) ∈ e.target) :
    (e.symm (verticalHom u (globalMap a₀ (detectionLine (r : ℂ)))) : E₃) 2 =
      (u : ℂ) * (r : ℂ) := by
  let A := closedBall (0 : ℂ) r
  let : PreconnectedSpace A :=
    isPreconnected_iff_preconnectedSpace.mp (convex_closedBall (0 : ℂ) r).isPreconnected
  have hzero : (0 : ℂ) ∈ A := mem_closedBall_self hr.le
  have hrmem : (r : ℂ) ∈ A := by
    change dist (r : ℂ) 0 ≤ r
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, le_refl]
  let g : A → Domain := fun t => coordinateAction u (detectionLine t)
  let h : A → Threefold.Space := fun t => verticalHom u (globalMap a₀ (detectionLine t))
  have hg : Continuous g := (coordinateAction_holomorphic u).continuous.comp
    (detectionLine_continuous.comp continuous_subtype_val)
  have hh : Continuous h := (verticalHom u).continuous.comp
    ((globalMap_holomorphic a₀).continuous.comp
      (detectionLine_continuous.comp continuous_subtype_val))
  have hp : ∀ t : A, globalMap a₀ (g t) = h t := fun t =>
    (globalMap_coordinateAction u a₀ (detectionLine t)).symm
  have hstart : g ⟨0, hzero⟩ ∈ e.source := by
    simpa only [g, coordinateAction_detectionLine, mul_zero] using hs hzero
  have hrec := localInverse_eq_lift (globalMap a₀)
    (globalMap_isLocalDiffeomorph a₀).isLocalHomeomorph e he g hg h hh
    (fun t => ht t t.property) hp ⟨0, hzero⟩ hstart ⟨(r : ℂ), hrmem⟩
  have hcoord := congrArg (fun z : Domain => (z : E₃) 2) hrec
  simpa only [g, h, coordinateAction_detectionLine, detectionLine_third] using hcoord.symm

/-- The actual C* parameter admits a scalar detector continuous near
the identity for the full ordinary compact-open automorphism topology. -/
theorem exists_local_parameter_recovery :
    ∃ R : Aut → ℂ, ContinuousAt R 1 ∧ R 1 = 1 ∧
      ∀ᶠ u in (𝓝 (1 : Aut)).comap verticalHom, R (verticalHom u) = (u : ℂ) := by
  obtain ⟨e₀, hzero, he₀⟩ := globalMap_isLocalDiffeomorph a₀ (detectionLine 0)
  let e := e₀.toOpenPartialHomeomorph
  have he : EqOn (globalMap a₀) e e.source := he₀
  have hline : detectionLine ⁻¹' e.source ∈ 𝓝 (0 : ℂ) :=
    detectionLine_continuous.continuousAt (e.open_source.mem_nhds hzero)
  obtain ⟨r, hr, hs⟩ := nhds_basis_closedBall.mem_iff.mp hline
  let K : Set Threefold.Space :=
    (globalMap a₀ ∘ detectionLine) '' closedBall (0 : ℂ) r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).image
    ((globalMap_holomorphic a₀).continuous.comp detectionLine_continuous)
  let W : Set Aut := {f | MapsTo f K e.target}
  have hW : IsOpen W :=
    (ContinuousMap.isOpen_setOfPred_mapsTo hK e.open_target).preimage
      (HolomorphicAutomorphism.continuous_toContinuousMap IF Threefold.Space)
  have hW1 : (1 : Aut) ∈ W := by
    rintro y ⟨t, ht, rfl⟩
    change globalMap a₀ (detectionLine t) ∈ e.target
    rw [he (hs ht)]
    exact e.map_source (hs ht)
  have hrmem : (r : ℂ) ∈ closedBall (0 : ℂ) r := by
    change dist (r : ℂ) 0 ≤ r
    simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, le_refl]
  let q : Threefold.Space := globalMap a₀ (detectionLine (r : ℂ))
  have hq : q ∈ e.target := hW1 ⟨(r : ℂ), hrmem, rfl⟩
  let R : Aut → ℂ := fun f => (e.symm (f q) : E₃) 2 / (r : ℂ)
  have hev : Continuous (fun f : Aut => f q) :=
    (show Continuous (fun f : C(Threefold.Space, Threefold.Space) => f q) from
      continuous_eval_const q).comp
      (HolomorphicAutomorphism.continuous_toContinuousMap IF Threefold.Space)
  have hei : ContinuousAt (fun f : Aut => e.symm (f q)) 1 :=
    (e.symm.continuousAt hq).comp_of_eq (hev.continuousAt (x := 1)) rfl
  have hcoord : Continuous (fun z : Domain => (z : E₃) 2) :=
    (continuous_apply 2).comp continuous_subtype_val
  have hR : ContinuousAt R 1 :=
    (hcoord.continuousAt.comp (f := fun f : Aut => e.symm (f q)) hei).div_const (r : ℂ)
  have hrec : ∀ u : ℂˣ, verticalHom u ∈ W → R (verticalHom u) = (u : ℂ) := by
    intro u hu
    change (e.symm (verticalHom u q) : E₃) 2 / (r : ℂ) = (u : ℂ)
    rw [chart_recovers_parameter e he hr hs u (fun t ht => hu ⟨t, ht, rfl⟩)]
    exact mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  refine ⟨R, hR, ?_, ?_⟩
  · simpa only [map_one, Units.val_one] using hrec 1 (by simpa using hW1)
  · exact (show ∀ᶠ u in (𝓝 (1 : Aut)).comap verticalHom, verticalHom u ∈ W from
      Filter.preimage_mem_comap (hW.mem_nhds hW1)).mono hrec

/-- The actual vertical action is a topological group embedding into
the full native biholomorphism group in its usual topology. -/
theorem verticalHom_isEmbedding : IsEmbedding verticalHom := by
  obtain ⟨R, hR, hR1, hrec⟩ := exists_local_parameter_recovery
  exact isEmbedding_of_local_recovery verticalHom verticalHom_continuous
    verticalHom_injective R hR hR1 hrec

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
