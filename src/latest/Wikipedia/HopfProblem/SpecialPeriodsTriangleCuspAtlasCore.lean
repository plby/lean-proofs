import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientAtlasCore
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Adding one compatible complex coordinate at infinity

A complex curve together with an actual topological chart about the new
point of its one-point compactification acquires a complex atlas, provided
that the chart is locally biholomorphic on the old curve.  The construction
uses the original topology and the supplied chart.  No uniformization or
surjective projection onto the added point is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.OnePointAtlas

variable {Q : Type*} [TopologicalSpace Q] [Nonempty Q]

def inclusionChart : OpenPartialHomeomorph Q (OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : Q → OnePoint Q)

@[simp] theorem inclusionChart_source : (inclusionChart (Q := Q)).source = univ :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_source _

@[simp] theorem inclusionChart_target : (inclusionChart (Q := Q)).target =
    range ((↑) : Q → OnePoint Q) :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_target _

@[simp] theorem inclusionChart_apply (q : Q) : inclusionChart q = (q : OnePoint Q) := rfl

@[simp] theorem inclusionChart_symm_coe (q : Q) :
    (inclusionChart (Q := Q)).symm (q : OnePoint Q) = q :=
  (inclusionChart (Q := Q)).left_inv (by simp)

variable [ChartedSpace ℂ Q]

/-- An original chart, transported through the literal open inclusion. -/
def oldChart (q : Q) : OpenPartialHomeomorph (OnePoint Q) ℂ :=
  (inclusionChart (Q := Q)).symm.trans (chartAt ℂ q)

@[simp] theorem oldChart_coe (q x : Q) : oldChart q (x : OnePoint Q) = chartAt ℂ q x := by
  change chartAt ℂ q ((inclusionChart (Q := Q)).symm (x : OnePoint Q)) = _
  rw [inclusionChart_symm_coe]

theorem oldChart_comp_coe (q : Q) : oldChart q ∘ ((↑) : Q → OnePoint Q) = chartAt ℂ q := by
  funext x
  exact oldChart_coe q x

@[simp] theorem coe_mem_oldChart_source (q x : Q) :
    (x : OnePoint Q) ∈ (oldChart q).source ↔ x ∈ (chartAt ℂ q).source := by
  change ((x : OnePoint Q) ∈ (inclusionChart (Q := Q)).target ∧
    (inclusionChart (Q := Q)).symm (x : OnePoint Q) ∈ (chartAt ℂ q).source) ↔ _
  simp only [inclusionChart_target, mem_range_self, inclusionChart_symm_coe, true_and]

theorem oldChart_preimage_source (q : Q) :
    ((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source = (chartAt ℂ q).source := by
  ext x
  exact coe_mem_oldChart_source q x

theorem infty_not_mem_oldChart_source (q : Q) : (∞ : OnePoint Q) ∉ (oldChart q).source := by
  intro hx
  have hr : (∞ : OnePoint Q) ∈ range ((↑) : Q → OnePoint Q) :=
    inclusionChart_target (Q := Q) ▸ hx.1
  obtain ⟨x, hx⟩ := hr
  exact OnePoint.coe_ne_infty x hx

section Analytic

variable [IsManifold 𝓘(ℂ) ω Q]

theorem oldChart_pullback_holomorphic (q : Q) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q))
      (((↑) : Q → OnePoint Q) ⁻¹' (oldChart q).source) := by
  rw [oldChart_comp_coe, oldChart_preimage_source]
  exact contMDiffOn_chart

theorem oldChart_pullback_localDiffeomorph (q x : Q)
    (hx : (x : OnePoint Q) ∈ (oldChart q).source) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (oldChart q ∘ ((↑) : Q → OnePoint Q)) x := by
  rw [oldChart_comp_coe]
  refine ⟨{
    toPartialEquiv := (chartAt ℂ q).toPartialEquiv
    open_source := (chartAt ℂ q).open_source
    open_target := (chartAt ℂ q).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }, ?_, ?_⟩
  · exact (coe_mem_oldChart_source q x).mp hx
  · exact eqOn_refl _ _

end Analytic

variable (e : OpenPartialHomeomorph (OnePoint Q) ℂ)

def chart : Option Q → OpenPartialHomeomorph (OnePoint Q) ℂ
  | none => e
  | some q => oldChart q

theorem chart_cover (he : (∞ : OnePoint Q) ∈ e.source) (x : OnePoint Q) :
    ∃ i, x ∈ (chart e i).source := by
  induction x using OnePoint.rec
  · exact ⟨none, he⟩
  · rename_i q
    exact ⟨some q, (coe_mem_oldChart_source q q).mpr (mem_chart_source ℂ q)⟩

theorem overlap_ne_infty (i j : Option Q) (hij : i ≠ j) (z : ℂ)
    (hz : z ∈ ((chart e i).symm.trans (chart e j)).source) :
    (chart e i).symm z ≠ (∞ : OnePoint Q) := by
  intro hinfty
  cases i with
  | some q =>
      apply infty_not_mem_oldChart_source q
      rw [← hinfty]
      exact (oldChart q).map_target hz.1
  | none =>
      cases j with
      | none => exact hij rfl
      | some q =>
          apply infty_not_mem_oldChart_source q
          rw [← hinfty]
          exact hz.2

/-- The original atlas and one compatible point chart give the actual
atlas data on the compactification. -/
def data [IsManifold 𝓘(ℂ) ω Q] (he : (∞ : OnePoint Q) ∈ e.source)
    (hholo : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q))
      (((↑) : Q → OnePoint Q) ⁻¹' e.source))
    (hlocal : ∀ x : Q, (x : OnePoint Q) ∈ e.source →
      IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (e ∘ ((↑) : Q → OnePoint Q)) x) :
    BranchedQuotientAtlas.Data (E := ℂ) ((↑) : Q → OnePoint Q) (Option Q) where
  chart := chart e
  cover := chart_cover e he
  continuous_project := OnePoint.continuous_coe
  pullback_contMDiff i := by
    cases i with
    | none => exact hholo
    | some q => exact oldChart_pullback_holomorphic q
  overlap_lift i j hij z hz := by
    have hne := overlap_ne_infty e i j hij z hz
    obtain ⟨x, hx⟩ : ∃ x : Q, (x : OnePoint Q) = (chart e i).symm z := by
      induction h : (chart e i).symm z using OnePoint.rec
      · exact (hne h).elim
      · rename_i x
        exact ⟨x, rfl⟩
    have hsource : (x : OnePoint Q) ∈ (chart e i).source := by
      rw [hx]
      exact (chart e i).map_target hz.1
    refine ⟨x, hx, ?_⟩
    cases i with
    | none => exact hlocal x hsource
    | some q => exact oldChart_pullback_localDiffeomorph q x hsource

end Wikipedia.HopfProblem.OnePointAtlas
