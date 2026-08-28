import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve

/-!
# One native field chart from compatible chart germs on a compact locus

Forward chart germs preserve the actual native pulled-back field.
Local field-chart germs form an open neighborhood. Compact injectivity
therefore constructs one genuine partial diffeomorphism, carrying the
same model field throughout its entire target.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem partialChartField_eq_of_forward_germ
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞) (W : D → D)
    {p : D} (hpΦ : p ∈ Φ.source) (hpΨ : p ∈ Ψ.source)
    (heq : (Φ : D → M) =ᶠ[𝓝 p] Ψ) :
    FlowConstruction.partialChartField Φ.symm W (Φ p) =
      FlowConstruction.partialChartField Ψ.symm W (Φ p) := by
  have hval : Φ p = Ψ p := heq.eq_of_nhds
  have hyΨ : Φ p ∈ Ψ.target := hval.symm ▸ Ψ.map_source' hpΨ
  have hiΦ : Φ.symm (Φ p) = p := Φ.left_inv' hpΦ
  have hiΨ : Ψ.symm (Φ p) = p := by rw [hval]; exact Ψ.left_inv' hpΨ
  rw [FlowConstruction.partialChartField_eq_mfderiv_symm Φ.symm W (Φ.map_source' hpΦ),
    FlowConstruction.partialChartField_eq_mfderiv_symm Ψ.symm W hyΨ]
  change mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Φ (Φ.symm (Φ p))
      ((NormedSpace.fromTangentSpace (Φ.symm (Φ p))).symm (W (Φ.symm (Φ p)))) =
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) Ψ (Ψ.symm (Φ p))
      ((NormedSpace.fromTangentSpace (Ψ.symm (Φ p))).symm (W (Ψ.symm (Φ p))))
  rw [hiΦ, hiΨ, heq.mfderiv_eq]
  rfl

theorem isLocalDiffeomorphAt_of_chart_germ
    (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {f : D → M} {p : D} (hp : p ∈ Φ.source)
    (heq : f =ᶠ[𝓝 p] Φ) : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp heq
  let Ψ := PartialChart.restrictSource Φ hU
  exact ⟨Ψ, ⟨hp, hpU⟩, fun x hx => hUsub hx.2⟩

variable [T2Space M]

open Classical in
theorem exists_native_field_chart_near_compact
    (f : D → M) (W : D → D) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    {K : Set D} (hK : IsCompact K) (hinj : InjOn f K)
    (hlocal : ∀ p ∈ K,
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
        p ∈ Φ.source ∧ f =ᶠ[𝓝 p] Φ ∧
        ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
      K ⊆ Φ.source ∧ (∀ p, Φ p = f p) ∧
      ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y := by
  let U : Set D := {p | ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞,
    p ∈ Φ.source ∧ f =ᶠ[𝓝 p] Φ ∧
    ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm W y}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨Ψ, hp, heq, hfield⟩
    filter_upwards [Ψ.open_source.mem_nhds hp, heq.eventuallyEq_nhds] with q hq hqeq
    exact ⟨Ψ, hq, hqeq, hfield⟩
  have hloc (p : D) (hp : p ∈ K) : IsLocalDiffeomorphAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f p := by
    obtain ⟨Ψ, hpΨ, heq, _⟩ := hlocal p hp
    exact isLocalDiffeomorphAt_of_chart_germ Ψ hpΨ heq
  obtain ⟨Φ, hKΦ, hΦU, hmap⟩ :=
    exists_partialDiffeomorph_near_compact hK hinj hloc hU hlocal
  refine ⟨Φ, hKΦ, fun p => congrFun hmap p, ?_⟩
  intro y hy
  have hp : Φ.symm y ∈ Φ.source := Φ.map_target' hy
  obtain ⟨Ψ, hpΨ, heq, hfield⟩ := hΦU hp
  have hΦeq : (Φ : D → M) =ᶠ[𝓝 (Φ.symm y)] Ψ := by rw [hmap]; exact heq
  have hi : Φ (Φ.symm y) = y := Φ.right_inv' hy
  have hΨval : Ψ (Φ.symm y) = y := hΦeq.eq_of_nhds.symm.trans hi
  have hyΨ : y ∈ Ψ.target := hΨval ▸ Ψ.map_source' hpΨ
  have hsame := partialChartField_eq_of_forward_germ Φ Ψ W hp hpΨ hΦeq
  rw [hi] at hsame
  exact (hfield y hyΨ).trans hsame.symm

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
