import Wikipedia.HopfProblem.CuspFibreImmersion
import Wikipedia.HopfProblem.CuspFibreManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Biholomorphic identification of the nonzero fibres

Both the fibre inclusion and the period-torus parametrization are analytic
immersions into the ambient cusp threefold. Their topological identification
is therefore analytic in both directions.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

/-- The complex structure of an embedded submanifold is determined by its
ambient immersion and its subspace topology. -/
def biholomorphOfEmbeddedHomeomorph
    {T U Q : Type*} [TopologicalSpace T] [ChartedSpace ComplexPlane₂ T]
    [TopologicalSpace U] [ChartedSpace ComplexPlane₂ U]
    [TopologicalSpace Q] [ChartedSpace (CoordinateSpace 3) Q]
    (e : T ≃ₜ U) {f : T → Q} {g : U → Q}
    (hf : Manifold.IsImmersion I₂ I₃ ω f)
    (hg : Manifold.IsImmersion I₂ I₃ ω g)
    (hcomm : ∀ x, g (e x) = f x) : Diffeomorph I₂ I₂ T U ω where
  toEquiv := e.toEquiv
  contMDiff_toFun := (ContMDiff.iff_comp_isImmersion hg).mpr
    ⟨e.continuous, hf.contMDiff.congr hcomm⟩
  contMDiff_invFun := (ContMDiff.iff_comp_isImmersion hf).mpr
    ⟨e.symm.continuous, hg.contMDiff.congr (fun y => by
      change f (e.symm y) = g y
      rw [← hcomm, e.apply_symm_apply])⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The full-period torus is biholomorphic to the actual cusp fibre, equipped
with the complex atlas obtained by slicing the ambient projection charts. -/
def fibreBiholomorph :
    letI := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
    Diffeomorph I₂ I₂ (periodData C s hlog hRp).Torus
      (projection C ε ⁻¹' {exponential s}) ω := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
  exact biholomorphOfEmbeddedHomeomorph (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR)
    (fibreMap_isImmersion ε s hs C hε hε1 hC hR hlog hRp)
    (fibre_inclusion_isImmersionOfComplement C ε hε hε1 hC hR
      (exponential s) (exponential_ne_zero s)).isImmersion (fun _ => rfl)

@[simp] theorem fibreBiholomorph_apply (z : (periodData C s hlog hRp).Torus) :
    (fibreBiholomorph C ε s hs hlog hRp hε hε1 hC hR z : QuotientSpace C ε) =
      fibreMap C ε s hs hlog hRp z := rfl

theorem fibreHomeomorph_holomorphic :
    letI := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
    ContMDiff I₂ I₂ ω (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) := by
  let := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
  exact (fibreBiholomorph C ε s hs hlog hRp hε hε1 hC hR).contMDiff

theorem fibreHomeomorph_symm_holomorphic :
    letI := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
    ContMDiff I₂ I₂ ω (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR).symm := by
  let := fibreChartedSpace C ε hε hε1 hC hR (exponential s) (exponential_ne_zero s)
  exact (fibreBiholomorph C ε s hs hlog hRp hε hε1 hC hR).symm.contMDiff

/-- The analytic, not merely topological, torus identification for every
nonzero cusp fibre. Its complex structure comes from the ambient threefold. -/
theorem nonzero_fibre_biholomorphic_torus {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    letI := fibreChartedSpace C ε hε hε1 hC hR t ht0
    ∃ p : FullPeriodMatrix,
      Nonempty (Diffeomorph I₂ I₂ p.Torus (projection C ε ⁻¹' {t}) ω) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℂ, exponential s = t :=
    ⟨logarithm t, exponential_logarithm ht0⟩
  let := fibreChartedSpace C ε hε hε1 hC hR (exponential s) ht0
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr ht0
  have hlog := Real.log_neg hpos (ht.trans hε1)
  have hRp := hR _ hpos ht
  exact ⟨periodData C s hlog hRp,
    ⟨fibreBiholomorph C ε s ht hlog hRp hε hε1 hC hR⟩⟩

end Wikipedia.HopfProblem.CuspUniformization
