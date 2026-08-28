import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDescentPullback
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Charts

/-!
# From a removable finite-coordinate germ to an actual base section

The finite coefficient of a holomorphic section on a sphere open set is
analytic at every point of that set. An analytic extension of this
coefficient across the finite point `1` defines a genuine holomorphic
section on a smaller original sphere open set. Its agreement with the
original section is pointwise on the actual overlap, not just an
equality of germs.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Metric
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

open HolomorphicFunctionSheaf.SphereH1

/-- The actual finite-coordinate coefficient, extended by zero outside
the original sphere open set. -/
def finiteExtension (W : Opens RiemannSphere) (h : BaseSection W) (q : ℂ) : ℂ := by
  classical
  exact if hq : (q : RiemannSphere) ∈ W then h ⟨(q : RiemannSphere), hq⟩ else 0

@[simp] theorem finiteExtension_apply (W : Opens RiemannSphere) (h : BaseSection W)
    (q : ℂ) (hq : (q : RiemannSphere) ∈ W) :
    finiteExtension W h q = h ⟨(q : RiemannSphere), hq⟩ := by
  classical
  simp only [finiteExtension, dif_pos hq]

@[simp] theorem finiteExtension_of_not_mem (W : Opens RiemannSphere) (h : BaseSection W)
    (q : ℂ) (hq : (q : RiemannSphere) ∉ W) :
    finiteExtension W h q = 0 := by
  classical
  simp only [finiteExtension, dif_neg hq]

/-- This is the coefficient in the actual affine chart of the original
sphere, with exactly the original section values. -/
theorem finiteExtension_eq_finiteCoefficient (W : Opens RiemannSphere)
    (h : BaseSection W) : finiteExtension W h = finiteCoefficient W h := rfl

theorem finiteExtension_analyticAt (W : Opens RiemannSphere) (h : BaseSection W)
    (q : ℂ) (hq : (q : RiemannSphere) ∈ W) :
    AnalyticAt ℂ (finiteExtension W h) q :=
  finiteCoefficient_analyticAt W h q hq

theorem finiteExtension_analyticOnNhd (W : Opens RiemannSphere) (h : BaseSection W) :
    AnalyticOnNhd ℂ (finiteExtension W h) (finiteOpen W) :=
  fun q hq => finiteExtension_analyticAt W h q hq

/-- Punctured membership in the actual base open set gives punctured
analyticity of the actual coefficient. -/
theorem finiteExtension_eventually_analyticAt (W : Opens RiemannSphere)
    (h : BaseSection W) {b : ℂ}
    (hmem : ∀ᶠ q : ℂ in 𝓝[≠] b, (q : RiemannSphere) ∈ W) :
    ∀ᶠ q in 𝓝[≠] b, AnalyticAt ℂ (finiteExtension W h) q :=
  hmem.mono fun q hq => finiteExtension_analyticAt W h q hq

/-- An actual analytic extension at the finite point `1` gives a
holomorphic section on a genuine smaller sphere open set, agreeing with
the original section everywhere on their overlap. No cover property of
`W` is assumed. -/
theorem exists_baseSection_extension (U W : Opens RiemannSphere)
    (hU : ((1 : ℂ) : RiemannSphere) ∈ U)
    (hW : ((1 : ℂ) : RiemannSphere) ∉ W) (h : BaseSection W)
    (Fext : ℂ → ℂ) (hFext : AnalyticAt ℂ Fext 1)
    (hmatch : Fext =ᶠ[𝓝[≠] 1] finiteExtension W h) :
    ∃ V : Opens RiemannSphere, V ≤ U ∧ ((1 : ℂ) : RiemannSphere) ∈ V ∧
      ∃ H : BaseSection V,
        ∀ p : V, ∀ hp : (p : RiemannSphere) ∈ W, H p = h ⟨p, hp⟩ := by
  have hnear : ∀ᶠ q in 𝓝 (1 : ℂ), AnalyticAt ℂ Fext q ∧
      (q : RiemannSphere) ∈ U ∧ (q ≠ 1 → Fext q = finiteExtension W h q) := by
    filter_upwards [hFext.eventually_analyticAt,
      (finiteOpen U).isOpen.mem_nhds hU, eventually_nhdsWithin_iff.mp hmatch]
      with q hqA hqU hqmatch
    exact ⟨hqA, hqU, fun hq => hqmatch hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let V : Opens RiemannSphere :=
    ⟨((↑) : ℂ → RiemannSphere) '' ball (1 : ℂ) r,
      OnePoint.isOpenMap_coe _ isOpen_ball⟩
  have hhol : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun p : V => fromFinite Fext 0 (p : RiemannSphere)) := by
    rintro ⟨p, hp⟩
    obtain ⟨q, hq, rfl⟩ := hp
    apply contMDiffAt_subtype_iff.mpr
    exact fromFinite_contMDiffAt_coe Fext 0 q (hball hq).1
  refine ⟨V, ?_, ?_, ⟨fun p => fromFinite Fext 0 p, hhol⟩, ?_⟩
  · rintro p ⟨q, hq, rfl⟩
    exact (hball hq).2.1
  · exact ⟨1, mem_ball_self hr, rfl⟩
  · rintro ⟨p, hp⟩ hpW
    obtain ⟨q, hq, rfl⟩ := hp
    change Fext q = h ⟨(q : RiemannSphere), hpW⟩
    have hq1 : q ≠ 1 := by
      intro hq1
      apply hW
      simpa only [hq1] using hpW
    exact ((hball hq).2.2 hq1).trans (finiteExtension_apply W h q hpW)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
