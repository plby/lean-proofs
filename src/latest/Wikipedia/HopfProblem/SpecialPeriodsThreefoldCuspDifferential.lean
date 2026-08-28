import Wikipedia.HopfProblem.CuspStrata
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspDifferentialProduct
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspDifferentialSubmersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The actual differential of the cusp projection

An analytic normal-crossing chart identifies the genuine manifold
differential with the derivative of the coordinate product followed by
the invertible chart differential.  Thus two or more local branches,
and only those points, make the actual cusp projection critical.
-/

noncomputable section

open Function Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "I₁" => modelWithCornersSelf ℂ ℂ

namespace NormalCrossingDifferential

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]

/-- The differential of an actual analytic chart is invertible. -/
theorem chart_mfderiv_bijective {e : OpenPartialHomeomorph M E₃}
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) {x : M} (hx : x ∈ e.source) :
    Bijective (mfderiv I₃ I₃ e x) := by
  have hd : e.MDifferentiable I₃ I₃ :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  exact hd.mfderiv_bijective hx

/-- Differentiating an actual local equation, with no separately
assumed differentiability of the original function. -/
theorem mfderiv_eq_in_chart {e : OpenPartialHomeomorph M E₃}
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) {x : M} (hx : x ∈ e.source)
    {f : M → ℂ} {g : E₃ → ℂ} (hg : DifferentiableAt ℂ g (e x))
    (hlocal : ∀ w ∈ e.target, f (e.symm w) = g w) :
    mfderiv I₃ I₁ f x = (fderiv ℂ g (e x)).comp (mfderiv I₃ I₃ e x) := by
  have heq : f =ᶠ[𝓝 x] g ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simpa only [e.left_inv hy, Function.comp_apply] using
      hlocal (e y) (e.map_source hy)
  have hde : MDifferentiableAt I₃ I₃ e x :=
    (contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)
  have hd := heq.mfderiv_eq (I := I₃) (I' := I₁)
  rw [mfderiv_comp x hg.mdifferentiableAt hde] at hd
  simpa only [mfderiv_eq_fderiv] using! hd

/-- The chart differential cannot change whether the differential vanishes. -/
theorem mfderiv_eq_zero_iff_in_chart {e : OpenPartialHomeomorph M E₃}
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) {x : M} (hx : x ∈ e.source)
    {f : M → ℂ} {g : E₃ → ℂ} (hg : DifferentiableAt ℂ g (e x))
    (hlocal : ∀ w ∈ e.target, f (e.symm w) = g w) :
    mfderiv I₃ I₁ f x = 0 ↔ fderiv ℂ g (e x) = 0 := by
  rw [mfderiv_eq_in_chart he hx hg hlocal]
  constructor
  · intro hzero
    ext v
    obtain ⟨u, rfl⟩ := (chart_mfderiv_bijective he hx).surjective v
    exact congrArg (fun L : E₃ →L[ℂ] ℂ => L u) hzero
  · intro hzero
    rw [hzero]
    ext v
    rfl

/-- The actual analytic chart also preserves differential surjectivity. -/
theorem mfderiv_surjective_iff_in_chart {e : OpenPartialHomeomorph M E₃}
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) {x : M} (hx : x ∈ e.source)
    {f : M → ℂ} {g : E₃ → ℂ} (hg : DifferentiableAt ℂ g (e x))
    (hlocal : ∀ w ∈ e.target, f (e.symm w) = g w) :
    Surjective (mfderiv I₃ I₁ f x) ↔ Surjective (fderiv ℂ g (e x)) := by
  rw [mfderiv_eq_in_chart he hx hg hlocal]
  exact Function.Surjective.of_comp_iff _ (chart_mfderiv_bijective he hx).surjective

end NormalCrossingDifferential

section NormalCrossing

open NormalCrossingCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]

/-- At the center of a genuine normal-crossing chart, the actual
manifold differential vanishes exactly when at least two branches meet. -/
theorem NormalCrossingChartAt.mfderiv_eq_zero_iff {J : Finset (Fin 3)}
    {f : M → ℂ} {x : M} (h : NormalCrossingChartAt J f x) (hJ : J.Nonempty) :
    mfderiv I₃ I₁ f x = 0 ↔ 2 ≤ J.card := by
  obtain ⟨e, he, hx, hc, hp⟩ := h
  have hd := NormalCrossingDifferential.mfderiv_eq_zero_iff_in_chart he hx
    ((coordinateProduct_contDiff J).differentiable (by simp)).differentiableAt hp
  rw [hc] at hd
  exact hd.trans (coordinateProduct_fderiv_zero_iff hJ)

/-- A single normal-crossing branch is exactly the surjective-
differential case; this is a statement about the original function. -/
theorem NormalCrossingChartAt.mfderiv_surjective_iff {J : Finset (Fin 3)}
    {f : M → ℂ} {x : M} (h : NormalCrossingChartAt J f x) (hJ : J.Nonempty) :
    Surjective (mfderiv I₃ I₁ f x) ↔ J.card = 1 := by
  obtain ⟨e, he, hx, hc, hp⟩ := h
  have hd := NormalCrossingDifferential.mfderiv_surjective_iff_in_chart he hx
    ((coordinateProduct_contDiff J).differentiable (by simp)).differentiableAt hp
  rw [hc] at hd
  exact hd.trans (coordinateProduct_fderiv_surjective_iff hJ)

end NormalCrossing

namespace CuspQuotient

open ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The already constructed branch-count chart computes the actual
differential of the central cusp projection. -/
theorem projection_mfderiv_eq_zero_iff_branchCount_of_central
    (x : QuotientSpace C ε) (hx : projection C ε x = 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    mfderiv I₃ I₁ (projection C ε) x = 0 ↔ 2 ≤ branchCount C ε x := by
  let := chartedSpace C ε hε hε1 hC hR
  obtain ⟨J, hcard, hJ, hchart⟩ :=
    normalCrossingChart_with_branchCount C ε hε hε1 hC hR x hx
  simpa only [hcard] using hchart.mfderiv_eq_zero_iff hJ

theorem projection_mfderiv_surjective_iff_branchCount_of_central
    (x : QuotientSpace C ε) (hx : projection C ε x = 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    Surjective (mfderiv I₃ I₁ (projection C ε) x) ↔ branchCount C ε x = 1 := by
  let := chartedSpace C ε hε hε1 hC hR
  obtain ⟨J, hcard, hJ, hchart⟩ :=
    normalCrossingChart_with_branchCount C ε hε hε1 hC hR x hx
  simpa only [hcard] using hchart.mfderiv_surjective_iff hJ

/-- Off the central fibre, the previously proved submersion normal form
forces surjectivity of the actual projection differential. -/
theorem projection_mfderiv_surjective_of_ne_zero (x : QuotientSpace C ε)
    (hx : projection C ε x ≠ 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    Surjective (mfderiv I₃ I₁ (projection C ε) x) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact SubmersionDifferential.mfderiv_surjective
    (CuspUniformization.projection_submersionAt C ε hε hε1 hC hR x hx)

/-- The critical-point criterion holds on the entire actual cusp
quotient, including the noncentral fibres. -/
theorem projection_mfderiv_eq_zero_iff_branchCount (x : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    mfderiv I₃ I₁ (projection C ε) x = 0 ↔ 2 ≤ branchCount C ε x := by
  let := chartedSpace C ε hε hε1 hC hR
  by_cases hx : projection C ε x = 0
  · exact projection_mfderiv_eq_zero_iff_branchCount_of_central C ε hε hε1 hC hR x hx
  · have hs := projection_mfderiv_surjective_of_ne_zero C ε hε hε1 hC hR x hx
    have hn : mfderiv I₃ I₁ (projection C ε) x ≠ 0 := by
      intro hzero
      obtain ⟨v, hv⟩ := hs (1 : ℂ)
      have hzv := congrArg (fun L : E₃ →L[ℂ] ℂ => L v) hzero
      exact (one_ne_zero : (1 : ℂ) ≠ 0) (hv.symm.trans hzv)
    have hcount : branchCount C ε x = 0 := by
      have hnot : ¬ 0 < branchCount C ε x := fun hp => hx ((branchCount_pos_iff C ε x).mp hp)
      omega
    constructor
    · intro hzero
      exact (hn hzero).elim
    · intro htwo
      omega

/-- The only failure of surjectivity is at a meeting of at least two
central branches; every other actual cusp point is regular. -/
theorem projection_mfderiv_surjective_iff_branchCount (x : QuotientSpace C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    Surjective (mfderiv I₃ I₁ (projection C ε) x) ↔ branchCount C ε x ≤ 1 := by
  let := chartedSpace C ε hε hε1 hC hR
  by_cases hx : projection C ε x = 0
  · have hs :=
      projection_mfderiv_surjective_iff_branchCount_of_central C ε hε hε1 hC hR x hx
    have hpos : 0 < branchCount C ε x := (branchCount_pos_iff C ε x).mpr hx
    exact hs.trans (by omega)
  · have hs := projection_mfderiv_surjective_of_ne_zero C ε hε hε1 hC hR x hx
    have hcount : branchCount C ε x = 0 := by
      have hnot : ¬ 0 < branchCount C ε x := fun hp => hx ((branchCount_pos_iff C ε x).mp hp)
      omega
    exact ⟨fun _ => by omega, fun _ => hs⟩

end CuspQuotient

end Wikipedia.HopfProblem
