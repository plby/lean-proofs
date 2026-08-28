import Wikipedia.HopfProblem.RiemannBoundaryInfinity
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# The logarithmic chart at the one-point boundary

The actual logarithmic half-strip chart extends continuously to zero by
the point at infinity in `OnePoint ℂ`. The topology at infinity is the
one-point compactification topology: continuity is proved by escape from
compact sets, using the previously proved imaginary-part limit.

We also identify every plane domain with its finite image in `OnePoint ℂ`
by a genuine homeomorphism for the inherited subspace topologies.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- The logarithmic half-strip coordinate with its ideal value at zero. -/
def onePointLogHalfStrip (a c : ℝ) (q : ℂ) : OnePoint ℂ :=
  if q = 0 then ∞ else (logHalfStrip a c q : OnePoint ℂ)

@[simp] theorem onePointLogHalfStrip_zero (a c : ℝ) :
    onePointLogHalfStrip a c 0 = ∞ := by
  simp [onePointLogHalfStrip]

theorem onePointLogHalfStrip_of_ne_zero (a c : ℝ) {q : ℂ} (hq : q ≠ 0) :
    onePointLogHalfStrip a c q = (logHalfStrip a c q : OnePoint ℂ) := by
  simp [onePointLogHalfStrip, hq]

@[simp] theorem onePointLogHalfStrip_eq_infty_iff (a c : ℝ) (q : ℂ) :
    onePointLogHalfStrip a c q = ∞ ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [onePointLogHalfStrip, hq]

/-- Adding the ideal value also removes the exceptional equality
`log 0 = log 1`; the actual one-point logarithmic chart is injective. -/
theorem onePointLogHalfStrip_injective (a : ℝ) {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (onePointLogHalfStrip a c) := by
  intro q r hqr
  by_cases hq : q = 0
  · subst q
    have hr : r = 0 := (onePointLogHalfStrip_eq_infty_iff a c r).mp
      (hqr.symm.trans (onePointLogHalfStrip_zero a c))
    exact hr.symm
  have hr : r ≠ 0 := by
    intro hr
    subst r
    exact hq ((onePointLogHalfStrip_eq_infty_iff a c q).mp
      (hqr.trans (onePointLogHalfStrip_zero a c)))
  rw [onePointLogHalfStrip_of_ne_zero a c hq,
    onePointLogHalfStrip_of_ne_zero a c hr] at hqr
  have hlog : log q = log r := by
    have hfin := OnePoint.coe_injective hqr
    have hmul : I * (c : ℂ) * log q = I * (c : ℂ) * log r :=
      sub_right_injective hfin
    exact mul_left_cancel₀ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hmul
  simpa only [exp_log hq, exp_log hr] using congrArg exp hlog

/-- The actual logarithmic chart escapes every compact subset of the plane. -/
theorem tendsto_logHalfStrip_cocompact (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (logHalfStrip a c) (𝓝[≠] 0) (cocompact ℂ) := by
  have hn : Tendsto (fun q : ℂ => ‖logHalfStrip a c q‖) (𝓝[≠] 0) atTop :=
    tendsto_atTop_mono (fun q => im_le_norm (logHalfStrip a c q))
      (tendsto_logHalfStrip_im_atTop a hc)
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn

/-- In the one-point compactification, compact-set escape is convergence
to the actual ideal point. -/
theorem tendsto_coe_logHalfStrip_infty (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℂ => (logHalfStrip a c q : OnePoint ℂ))
      (𝓝[≠] 0) (𝓝 ∞) := by
  have hcoe : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  exact hcoe.comp (tendsto_logHalfStrip_cocompact a hc)

/-- The logarithmic source coordinate really is continuous at its newly
added ideal point; no boundary continuity is supplied as a hypothesis. -/
theorem continuousAt_onePointLogHalfStrip_zero (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ContinuousAt (onePointLogHalfStrip a c) 0 := by
  rw [continuousAt_iff_punctured_nhds, onePointLogHalfStrip_zero]
  apply (tendsto_coe_logHalfStrip_infty a hc).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (onePointLogHalfStrip_of_ne_zero a c hq).symm

/-- The finite image of a plane domain in the one-point compactification. -/
def onePointDomain (D : Set ℂ) : Set (OnePoint ℂ) :=
  ((↑) : ℂ → OnePoint ℂ) '' D

@[simp] theorem coe_mem_onePointDomain {D : Set ℂ} {z : ℂ} :
    (z : OnePoint ℂ) ∈ onePointDomain D ↔ z ∈ D := by
  exact OnePoint.coe_injective.mem_set_image

@[simp] theorem infty_notMem_onePointDomain (D : Set ℂ) :
    ∞ ∉ onePointDomain D :=
  OnePoint.infty_notMem_image_coe

/-- Exact membership of the one-point logarithmic chart in a finite domain. -/
@[simp] theorem onePointLogHalfStrip_mem_onePointDomain
    {D : Set ℂ} (a c : ℝ) (q : ℂ) :
    onePointLogHalfStrip a c q ∈ onePointDomain D ↔
      q ≠ 0 ∧ logHalfStrip a c q ∈ D := by
  by_cases hq : q = 0 <;> simp [onePointLogHalfStrip, hq]

theorem isOpen_onePointDomain {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (onePointDomain D) :=
  OnePoint.isOpen_image_coe.mpr hD

/-- A plane domain and its finite image in `OnePoint ℂ` have their natural
subspace topologies and are homeomorphic by the usual inclusion. -/
def onePointDomainHomeomorph (D : Set ℂ) : D ≃ₜ onePointDomain D :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage D

@[simp] theorem onePointDomainHomeomorph_apply_coe (D : Set ℂ) (z : D) :
    (onePointDomainHomeomorph D z : OnePoint ℂ) = (z : ℂ) := rfl

/-- A given genuine disc homeomorphism can be viewed on the corresponding
finite domain in the one-point compactification. -/
def onePointDomainDiscHomeomorph {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) :
    onePointDomain D ≃ₜ ball (0 : ℂ) 1 :=
  (onePointDomainHomeomorph D).symm.trans e

@[simp] theorem onePointDomainDiscHomeomorph_apply {D : Set ℂ}
    (e : D ≃ₜ ball (0 : ℂ) 1) (z : D) :
    onePointDomainDiscHomeomorph e (onePointDomainHomeomorph D z) = e z := by
  simp [onePointDomainDiscHomeomorph]

/-- The map on the finite one-point domain is literally the original map.
The arbitrary value assigned at infinity does not affect this identity. -/
theorem onePointDomainDiscHomeomorph_representative {D : Set ℂ}
    (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (b : ℂ) (z : onePointDomain D) :
    (z : OnePoint ℂ).elim b f = (onePointDomainDiscHomeomorph e z : ℂ) := by
  obtain ⟨w, rfl⟩ := (onePointDomainHomeomorph D).surjective z
  simpa only [onePointDomainHomeomorph_apply_coe, OnePoint.elim_some,
    onePointDomainDiscHomeomorph_apply] using he w

/-- Any actual compact-set-escaping net in a plane domain witnesses that
infinity belongs to the frontier of its finite one-point image. -/
theorem infty_mem_frontier_onePointDomain_of_cocompact
    {D : Set ℂ} {α : Type*} {l : Filter α} [NeBot l] {z : α → ℂ}
    (hz : Tendsto z l (cocompact ℂ)) (hmem : ∀ᶠ i in l, z i ∈ D) :
    (∞ : OnePoint ℂ) ∈ frontier (onePointDomain D) := by
  have hcoe : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝 ∞) := by
    simpa only [coclosedCompact_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  have hcl : (∞ : OnePoint ℂ) ∈ closure (onePointDomain D) := by
    apply isClosed_closure.mem_of_tendsto (hcoe.comp hz)
    filter_upwards [hmem] with i hi
    exact subset_closure (coe_mem_onePointDomain.mpr hi)
  exact ⟨hcl, fun hi => infty_notMem_onePointDomain D (interior_subset hi)⟩

end Wikipedia.HopfProblem.RiemannBoundary
