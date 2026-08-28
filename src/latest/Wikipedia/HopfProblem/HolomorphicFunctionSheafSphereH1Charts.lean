import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ChartsPullback

/-!
# Holomorphic sphere sections from their actual two chart coefficients

A finite-coordinate function with a holomorphic reciprocal-coordinate
extension at infinity defines a genuine holomorphic section on the
original sphere open set.  The proof uses the constructed sphere atlas,
and requires neither a refinement of that open set nor an assumed
holomorphic gluing theorem.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Metric
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

open RiemannSphere

/-- A function with the prescribed finite values and the prescribed
value at the actual point at infinity. -/
def fromFinite (f : ℂ → ℂ) (c : ℂ) : RiemannSphere → ℂ :=
  OnePoint.rec c f

@[simp] theorem fromFinite_coe (f : ℂ → ℂ) (c z : ℂ) :
    fromFinite f c (z : RiemannSphere) = f z := rfl

@[simp] theorem fromFinite_infty (f : ℂ → ℂ) (c : ℂ) :
    fromFinite f c (∞ : RiemannSphere) = c := rfl

theorem fromFinite_infinityParametrization (f : ℂ → ℂ) (c : ℂ) {u : ℂ} (hu : u ≠ 0) :
    fromFinite f c (infinityParametrization u) = f u⁻¹ := by
  rw [infinityParametrization_of_ne hu, fromFinite_coe]

/-- A pointwise chart criterion for the actual two-chart sphere atlas. -/
theorem contMDiffAt_of_comp_affineMap (g : RiemannSphere → ℂ) (b : Bool) (z : ℂ)
    (hg : ContDiffAt ℂ ω (g ∘ standardCharts.affineMap b) z) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (standardCharts.affineMap b z) := by
  let e := (standardCharts.parametrization b).symm
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω RiemannSphere :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  have hz : standardCharts.affineMap b z ∈ e.source := by
    change standardCharts.affineMap b z ∈ (standardCharts.parametrization b).target
    rw [TwoAffineCharts.parametrization_target]
    exact mem_range_self z
  have hchart := contMDiffAt_of_mem_maximalAtlas he hz
  have hz' : e (standardCharts.affineMap b z) = z :=
    standardCharts.parametrization_symm_apply b z
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ standardCharts.affineMap b)
      (e (standardCharts.affineMap b z)) := by
    rw [hz']
    exact hg.contMDiffAt
  apply (hg'.comp _ hchart).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hz] with p hp
  change g p = g (standardCharts.affineMap b (e p))
  exact (congrArg g ((standardCharts.parametrization b).right_inv hp)).symm

/-- Analyticity in the finite coordinate gives actual manifold
holomorphicity at the corresponding finite sphere point. -/
theorem fromFinite_contMDiffAt_coe (f : ℂ → ℂ) (c z : ℂ) (hf : AnalyticAt ℂ f z) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fromFinite f c) (z : RiemannSphere) := by
  apply contMDiffAt_of_comp_affineMap (fromFinite f c) false z
  exact hf.contDiffAt

/-- A reciprocal-coordinate extension is a genuine holomorphicity
certificate at infinity, even when its matching equation is only given
where the reciprocal point belongs to the original open set. -/
theorem fromFinite_contMDiffAt_infty (U : Opens RiemannSphere)
    (f : ℂ → ℂ) (c : ℂ) (hU : (∞ : RiemannSphere) ∈ U)
    (r : ℝ) (hr : 0 < r) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F (ball (0 : ℂ) r)) (hF0 : F 0 = c)
    (hmatch : ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 →
      infinityParametrization u ∈ U → f u⁻¹ = F u) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fromFinite f c) (∞ : RiemannSphere) := by
  have hzero : (0 : ℂ) ∈ infinityOpen U := by
    simpa only [mem_infinityOpen, infinityParametrization_zero] using hU
  have heq : fromFinite f c ∘ infinityParametrization =ᶠ[𝓝 (0 : ℂ)] F := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr,
      (infinityOpen U).isOpen.mem_nhds hzero] with u hu hUu
    by_cases hu0 : u = 0
    · subst u
      simpa only [Function.comp_apply, infinityParametrization_zero, fromFinite_infty]
        using hF0.symm
    · exact (fromFinite_infinityParametrization f c hu0).trans (hmatch u hu hu0 hUu)
  have hg : ContDiffAt ℂ ω (fromFinite f c ∘ infinityParametrization) 0 :=
    (hF 0 (mem_ball_self hr)).contDiffAt.congr_of_eventuallyEq heq
  have h := contMDiffAt_of_comp_affineMap (fromFinite f c) true 0 hg
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fromFinite f c) (infinityParametrization 0) at h
  simpa only [infinityParametrization_zero] using h

variable (U : Opens RiemannSphere) (f : ℂ → ℂ) (c : ℂ)
  (hf : AnalyticOnNhd ℂ f (finiteOpen U))
  (hInf : (∞ : RiemannSphere) ∈ U → ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
    AnalyticOnNhd ℂ F (ball (0 : ℂ) r) ∧ F 0 = c ∧
      ∀ u ∈ ball (0 : ℂ) r, u ≠ 0 → infinityParametrization u ∈ U → f u⁻¹ = F u)

include hf hInf in
/-- The finite function and its verified infinity extension give an
actual holomorphic function on the original open subset of the sphere. -/
theorem fromFinite_contMDiff :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun p : U => fromFinite f c p) := by
  rintro ⟨p, hp⟩
  apply contMDiffAt_subtype_iff.mpr
  induction p using OnePoint.rec with
  | infty =>
    obtain ⟨r, hr, F, hF, hF0, hmatch⟩ := hInf hp
    exact fromFinite_contMDiffAt_infty U f c hp r hr F hF hF0 hmatch
  | coe z => exact fromFinite_contMDiffAt_coe f c z (hf z hp)

/-- The genuine bundled holomorphic section, not merely its finite
coefficient or a section on a refined cover. -/
def fromFiniteSection : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
  ⟨fun p => fromFinite f c p, fromFinite_contMDiff U f c hf hInf⟩

@[simp] theorem fromFiniteSection_apply (p : U) :
    fromFiniteSection U f c hf hInf p = fromFinite f c p := rfl

@[simp] theorem fromFiniteSection_coe (z : ℂ) (hz : (z : RiemannSphere) ∈ U) :
    fromFiniteSection U f c hf hInf ⟨(z : RiemannSphere), hz⟩ = f z := rfl

@[simp] theorem fromFiniteSection_infty (hU : (∞ : RiemannSphere) ∈ U) :
    fromFiniteSection U f c hf hInf ⟨(∞ : RiemannSphere), hU⟩ = c := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
