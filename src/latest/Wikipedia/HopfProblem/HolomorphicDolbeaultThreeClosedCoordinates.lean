import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle

/-!
# Native chart domains and covector coefficients on original open sets

An open form is extended by zero only to name a representative on the
ambient manifold.  Its coefficients use the original preferred manifold
charts and the original real tangent Hom-bundle coordinates.  Every
assertion at a coordinate point is confined to the actual chart target
whose inverse image lies in the section's original open domain.
-/

noncomputable section

open Bundle Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- An ambient representative of the original dependent covectors,
equal to zero only outside the actual open domain. -/
def extendForm (U : Opens M) (a : ∀ x : U, Forms.Covector E M (x : M))
    (x : M) : Forms.Covector E M x := by
  classical
  exact if hx : x ∈ U then a ⟨x, hx⟩ else 0

@[simp] theorem extendForm_apply (U : Opens M)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : M) (hx : x ∈ U) :
    extendForm E M U a x = a ⟨x, hx⟩ := by
  classical
  simp only [extendForm, dif_pos hx]

/-- The genuine coordinate domain in a fixed original preferred chart. -/
def coordinateDomain (U : Opens M) (x₀ : M) : Opens E :=
  ⟨(chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' (U : Set M),
    (chartAt E x₀).isOpen_inter_preimage_symm U.isOpen⟩

omit [NormedSpace ℝ E] in
@[simp] theorem mem_coordinateDomain (U : Opens M) (x₀ : M) (z : E) :
    z ∈ coordinateDomain E M U x₀ ↔
      z ∈ (chartAt E x₀).target ∧ (chartAt E x₀).symm z ∈ U := Iff.rfl

omit [NormedSpace ℝ E] in
theorem coordinateDomain_mono {U V : Opens M} (h : U ≤ V) (x₀ : M) :
    coordinateDomain E M U x₀ ≤ coordinateDomain E M V x₀ :=
  fun _ hz => ⟨hz.1, h hz.2⟩

omit [NormedSpace ℝ E] in
/-- A chart's own centre belongs to the coordinate domain whenever
the original base point belongs to the section domain. -/
theorem mem_coordinateDomain_self (U : Opens M) (x : M) (hx : x ∈ U) :
    chartAt E x x ∈ coordinateDomain E M U x := by
  refine ⟨mem_chart_target E x, ?_⟩
  change (chartAt E x).symm (chartAt E x x) ∈ U
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  exact hx

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Literal real tangent Hom-bundle coefficients in an actual original
chart, with the ambient representative evaluated at its inverse image. -/
def coordinateForm (U : Opens M) (a : ∀ x : U, Forms.Covector E M (x : M))
    (x₀ : M) (z : E) : E →L[ℝ] ℂ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E) : M → Type)
    ℂ (fun _ : M => ℂ) x₀ ((chartAt E x₀).symm z) x₀ ((chartAt E x₀).symm z)
      (extendForm E M U a ((chartAt E x₀).symm z))

/-- On its actual domain the coordinate function is the native form
coordinate at the literal inverse-chart point. -/
theorem coordinateForm_eq_inCoordinates (U : Opens M)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (z : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    coordinateForm E M U a x₀ z =
      Forms.inCoordinates E M a x₀ ⟨(chartAt E x₀).symm z, hz.2⟩ := by
  rw [Forms.inCoordinates_eq]
  dsimp only [coordinateForm]
  rw [extendForm_apply E M U a _ hz.2]

/-- Evaluation of the native coordinate covector uses the actual inverse
tangent trivialization, not a global coordinate frame. -/
theorem coordinateForm_apply (U : Opens M)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (z v : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    coordinateForm E M U a x₀ z v =
      a ⟨(chartAt E x₀).symm z, hz.2⟩
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type) x₀).symmL ℝ
          ((chartAt E x₀).symm z) v) := by
  rw [coordinateForm_eq_inCoordinates E M U a x₀ z hz, Forms.inCoordinates_apply]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Extending a literal restriction changes no native covector on the
smaller original open set. -/
theorem extendForm_restriction_apply {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (x : M) (hx : x ∈ U) :
    extendForm E M U (fun y => a ⟨(y : M), h y.property⟩) x =
      extendForm E M V a x := by
  rw [extendForm_apply E M U _ x hx, extendForm_apply E M V a x (h hx)]

/-- Literal restriction leaves the original chart coefficient unchanged
at every point of the smaller actual coordinate domain. -/
theorem coordinateForm_restriction_apply {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (x₀ : M) (z : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    coordinateForm E M U (fun y => a ⟨(y : M), h y.property⟩) x₀ z =
      coordinateForm E M V a x₀ z := by
  dsimp only [coordinateForm]
  rw [extendForm_restriction_apply E M h a _ hz.2]

/-- The entire native coefficient germ is unchanged by literal open
restriction, so its actual derivatives are unchanged as well. -/
theorem coordinateForm_restriction_germ {U V : Opens M} (h : U ≤ V)
    (a : ∀ x : V, Forms.Covector E M (x : M)) (x₀ : M) (z : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    coordinateForm E M U (fun y => a ⟨(y : M), h y.property⟩) x₀ =ᶠ[𝓝 z]
      coordinateForm E M V a x₀ := by
  filter_upwards [(coordinateDomain E M U x₀).isOpen.mem_nhds hz] with y hy
  exact coordinateForm_restriction_apply E M h a x₀ y hy

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
