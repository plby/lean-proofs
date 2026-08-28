import Wikipedia.HopfProblem.CuspPositiveRetractionQuotient
import Wikipedia.HopfProblem.CuspPositiveRetractionOrthantCharts

/-!
# Actual positive-orthant charts on the positive cusp quotient

The charts are restrictions of the original toric affine charts, followed
by local inverses of the genuine quotient covering. Their height is
exactly the product of the nonnegative coordinates. These local formulas
are the geometric input for chart-supported positive retractions.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricFan ToricSpace
open CuspPositiveRetraction (Orthant)

def positiveOpenTube (ε : ℝ) : TopologicalSpace.Opens PositivePart :=
  ⟨{x | ‖time (x : Space)‖ < ε}, isOpen_lt
    (time_holomorphic.continuous.comp continuous_subtype_val).norm continuous_const⟩

def positiveTubeOpenHomeomorph (ε : ℝ) : PositiveTube ε ≃ₜ positiveOpenTube ε :=
  positiveTubeHomeomorph ε

theorem positiveOpenTube_nonempty (ε : ℝ) (hε : 0 < ε) :
    Nonempty (positiveOpenTube ε) := by
  refine ⟨⟨positiveInclusion referenceTriangle ⟨0, fun _ => le_rfl⟩, ?_⟩⟩
  change ‖time (positiveInclusion referenceTriangle ⟨0, fun _ => le_rfl⟩ : Space)‖ < ε
  rw [norm_time_positiveInclusion]
  simpa [CuspPositiveRetraction.height] using hε

/-- Restrict the actual positive affine chart to the open positive tube. -/
def positiveTubeChart (ε : ℝ) (hε : 0 < ε) (s : Triangle) :
    OpenPartialHomeomorph (PositiveTube ε) Orthant :=
  (positiveTubeOpenHomeomorph ε).toOpenPartialHomeomorph.trans
    ((positiveParametrization s).symm.subtypeRestr (positiveOpenTube_nonempty ε hε))

@[simp] theorem positiveTubeChart_apply (ε : ℝ) (hε : 0 < ε) (s : Triangle)
    (x : PositiveTube ε) :
    positiveTubeChart ε hε s x =
      (positiveParametrization s).symm (positiveTubeToPositive ε x) := rfl

theorem positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (s : Triangle) :
    (positiveTubeChart ε hε s).source =
      {x | positiveTubeToPositive ε x ∈ Set.range (positiveInclusion s)} := by
  unfold positiveTubeChart
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.subtypeRestr_source]
  ext x
  change (x ∈ Set.univ ∧ positiveTubeToPositive ε x ∈ (positiveParametrization s).target) ↔ _
  simp only [Set.mem_univ, true_and, positiveParametrization_target, Set.mem_ofPred_eq]

theorem exists_positiveTubeChart_source (ε : ℝ) (hε : 0 < ε) (x : PositiveTube ε) :
    ∃ s : Triangle, x ∈ (positiveTubeChart ε hε s).source := by
  obtain ⟨s, r, hr⟩ := positiveInclusion_jointly_surjective (positiveTubeToPositive ε x)
  refine ⟨s, ?_⟩
  rw [positiveTubeChart_source]
  exact ⟨r, hr⟩

/-- Inverting the restricted chart gives precisely the original positive
toric inclusion; this equality takes place in the actual positive part. -/
theorem positiveTubeChart_symm_positive (ε : ℝ) (hε : 0 < ε) (s : Triangle)
    {r : Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    positiveTubeToPositive ε ((positiveTubeChart ε hε s).symm r) = positiveInclusion s r := by
  have hx := (positiveTubeChart ε hε s).map_target hr
  rw [positiveTubeChart_source] at hx
  have he := positiveInclusion_positiveParametrization_symm s hx
  have hinv := (positiveTubeChart ε hε s).right_inv hr
  rw [positiveTubeChart_apply] at hinv
  rw [hinv] at he
  exact he.symm

theorem positiveTubeChart_height_symm (ε : ℝ) (hε : 0 < ε) (s : Triangle)
    {r : Orthant} (hr : r ∈ (positiveTubeChart ε hε s).target) :
    ‖time (((positiveTubeChart ε hε s).symm r).1 : Space)‖ =
      CuspPositiveRetraction.height r := by
  have h := congrArg (fun x : PositivePart => ‖time (x : Space)‖)
    (positiveTubeChart_symm_positive ε hε s hr)
  exact h.trans (norm_time_positiveInclusion s r)

theorem positiveTubeChart_height (ε : ℝ) (hε : 0 < ε) (s : Triangle)
    {x : PositiveTube ε} (hx : x ∈ (positiveTubeChart ε hε s).source) :
    ‖time (x.1 : Space)‖ = CuspPositiveRetraction.height (positiveTubeChart ε hε s x) := by
  have h := positiveTubeChart_height_symm ε hε s
    ((positiveTubeChart ε hε s).map_source hx)
  rwa [(positiveTubeChart ε hε s).left_inv hx] at h

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε)

/-- An actual quotient chart: lift by the covering, then use the positive
restriction of a toric affine chart. -/
def quotientChart (a : PositiveTube ε) (s : Triangle) :
    OpenPartialHomeomorph (QuotientSpace C₀ ε) Orthant :=
  letI := positiveAction C₀ ε
  CoveringOrthant.localChart (project_covering C₀ ε hε hε1 hR)
    (positiveTubeChart ε hε s) a

theorem quotientChart_mem_source (a : PositiveTube ε) (s : Triangle)
    (ha : a ∈ (positiveTubeChart ε hε s).source) :
    project C₀ ε a ∈ (quotientChart C₀ ε hε hε1 hR a s).source := by
  let := positiveAction C₀ ε
  exact CoveringOrthant.self_mem_localChart_source (project_covering C₀ ε hε hε1 hR)
    (positiveTubeChart ε hε s) a ha

@[simp] theorem quotientChart_symm_apply (a : PositiveTube ε) (s : Triangle) (r : Orthant) :
    (quotientChart C₀ ε hε hε1 hR a s).symm r =
      project C₀ ε ((positiveTubeChart ε hε s).symm r) := by
  let := positiveAction C₀ ε
  exact CoveringOrthant.localChart_symm_apply (project_covering C₀ ε hε hε1 hR)
    (positiveTubeChart ε hε s) a r

theorem quotientChart_height_symm (a : PositiveTube ε) (s : Triangle)
    {r : Orthant} (hr : r ∈ (quotientChart C₀ ε hε hε1 hR a s).target) :
    height C₀ ε ((quotientChart C₀ ε hε hε1 hR a s).symm r) =
      CuspPositiveRetraction.height r := by
  let := positiveAction C₀ ε
  apply CoveringOrthant.localChart_coordinate_identity
    (project_covering C₀ ε hε hε1 hR) (positiveTubeChart ε hε s) a
    (height C₀ ε) CuspPositiveRetraction.height ?_ r hr
  intro x hx
  rw [height_project]
  exact positiveTubeChart_height ε hε s hx

theorem quotientChart_height (a : PositiveTube ε) (s : Triangle)
    {x : QuotientSpace C₀ ε} (hx : x ∈ (quotientChart C₀ ε hε hε1 hR a s).source) :
    height C₀ ε x = CuspPositiveRetraction.height (quotientChart C₀ ε hε hε1 hR a s x) := by
  have h := quotientChart_height_symm C₀ ε hε hε1 hR a s
    ((quotientChart C₀ ε hε hε1 hR a s).map_source hx)
  rwa [(quotientChart C₀ ε hε hε1 hR a s).left_inv hx] at h

include hε hε1 hR in
/-- Every point of the actual positive quotient has an open positive-orthant
chart in which the actual height is the coordinate product. -/
theorem exists_quotientChart (x : QuotientSpace C₀ ε) :
    ∃ e : OpenPartialHomeomorph (QuotientSpace C₀ ε) Orthant,
      x ∈ e.source ∧ ∀ r ∈ e.target,
        height C₀ ε (e.symm r) = CuspPositiveRetraction.height r := by
  obtain ⟨a, ha⟩ := project_surjective C₀ ε x
  obtain ⟨s, hs⟩ := exists_positiveTubeChart_source ε hε a
  refine ⟨quotientChart C₀ ε hε hε1 hR a s, ?_, ?_⟩
  · rw [← ha]
    exact quotientChart_mem_source C₀ ε hε hε1 hR a s hs
  · intro r hr
    exact quotientChart_height_symm C₀ ε hε hε1 hR a s hr

include hε hε1 hR in
/-- The parametrization form needed to transport a compactly supported
orthant homotopy to the actual positive quotient. -/
theorem exists_orthantChart (x : QuotientSpace C₀ ε) :
    ∃ (e : OpenPartialHomeomorph Orthant (QuotientSpace C₀ ε)) (r₀ : Orthant),
      r₀ ∈ e.source ∧ e r₀ = x ∧
      ∀ r ∈ e.source, height C₀ ε (e r) = CuspPositiveRetraction.height r := by
  obtain ⟨c, hx, hc⟩ := exists_quotientChart C₀ ε hε hε1 hR x
  exact ⟨c.symm, c x, c.map_source hx, c.left_inv hx, hc⟩

end Wikipedia.HopfProblem.CuspPositive
