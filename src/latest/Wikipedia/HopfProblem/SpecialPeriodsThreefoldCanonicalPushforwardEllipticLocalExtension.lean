import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticNativeRemovable
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticBaseExtension

/-!
# An actual local base section across the second elliptic value

The native ramified removability theorem is applied to sections on the
full inverse image of an arbitrary base open set.  Surjectivity of the
actual projection supplies a central point.  An arbitrary holomorphic
base coefficient on the punctured open, representing the section on
the actual regular locus, therefore extends to a genuine holomorphic
base section on a smaller open neighborhood of the second elliptic value.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

theorem finiteCoordinate_coe_of_ne_infty {p : RiemannSphere}
    (hp : p ≠ (∞ : RiemannSphere)) :
    (CanonicalGlobal.BaseTwist.finiteCoordinate p : RiemannSphere) = p := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl

/-- Punctured base coefficients of actual canonical sections have an
actual local holomorphic extension at the second elliptic value.
The section representation is the only input about the coefficient;
the pole exclusion and the local holomorphic extension are proved. -/
theorem exists_baseSection_extension_of_nativeSection
    (U W : Opens RiemannSphere)
    (s : NativeBundleSections.Section Threefold.Canonical.bundle IF (Threefold.basePreimage U))
    (hU : ((1 : ℂ) : RiemannSphere) ∈ U)
    (hW : ((1 : ℂ) : RiemannSphere) ∉ W)
    (hWfinite : ∀ q : ℂ, (q : RiemannSphere) ∈ U → q ≠ 1 → (q : RiemannSphere) ∈ W)
    (h : Threefold.BaseSection W)
    (heq : ∀ x : Threefold.basePreimage U,
      ∀ hxW : Threefold.projectionSphere x.val ∈ W,
      x.val ∈ Threefold.regularLocus →
      s x = h ⟨Threefold.projectionSphere x.val, hxW⟩ •
        GlobalMeromorphicSection.rawSection x.val) :
    ∃ V : Opens RiemannSphere, V ≤ U ∧ ((1 : ℂ) : RiemannSphere) ∈ V ∧
      ∃ H : Threefold.BaseSection V,
        ∀ p : V, ∀ hp : (p : RiemannSphere) ∈ W, H p = h ⟨p, hp⟩ := by
  obtain ⟨a, ha⟩ := Threefold.projectionSphere_surjective ((1 : ℂ) : RiemannSphere)
  have haS : a ∈ GlobalEllipticDivisor.support := ha
  let y : GlobalEllipticDivisor.patch :=
    ⟨a, GlobalEllipticDivisor.support_subset_patch haS⟩
  have hy : y.val ∈ GlobalEllipticDivisor.support := haS
  have hyU : y.val ∈ Threefold.basePreimage U := by
    change Threefold.projectionSphere a ∈ U
    rw [ha]
    exact hU
  have hmem : ∀ᶠ q : ℂ in 𝓝[≠] (1 : ℂ), (q : RiemannSphere) ∈ W := by
    have hnear : ∀ᶠ q : ℂ in 𝓝 (1 : ℂ), (q : RiemannSphere) ∈ U :=
      (HolomorphicFunctionSheaf.SphereH1.finiteOpen U).isOpen.mem_nhds hU
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with q hq hn
    exact hWfinite q hq hn
  have hF := finiteExtension_eventually_analyticAt W h hmem
  have hrep : ∀ x : Threefold.basePreimage U, x.val ∈ Threefold.regularLocus →
      s x = finiteExtension W h (CanonicalGlobal.BaseTwist.finiteCoordinate
        (Threefold.projectionSphere x.val)) • GlobalMeromorphicSection.rawSection x.val := by
    intro x hx
    have hr := (Threefold.mem_sphereRegularPatch _).mp
      ((Threefold.mem_regularLocus_iff_sphere x.val).mp hx)
    let q := CanonicalGlobal.BaseTwist.finiteCoordinate (Threefold.projectionSphere x.val)
    have hq : (q : RiemannSphere) = Threefold.projectionSphere x.val :=
      finiteCoordinate_coe_of_ne_infty hr.1
    have hqU : (q : RiemannSphere) ∈ U := by
      rw [hq]
      exact x.property
    have hq1 : q ≠ 1 := by
      intro he
      apply hr.2.2
      rw [← hq, he]
    have hqW : (q : RiemannSphere) ∈ W := hWfinite q hqU hq1
    have hxW : Threefold.projectionSphere x.val ∈ W := by
      rw [← hq]
      exact hqW
    have hc : finiteExtension W h q = h ⟨Threefold.projectionSphere x.val, hxW⟩ :=
      (finiteExtension_apply W h q hqW).trans (congrArg h (Subtype.ext hq))
    exact (heq x hxW hx).trans
      (congrArg (fun c : ℂ => c • GlobalMeromorphicSection.rawSection x.val) hc.symm)
  obtain ⟨Fext, hA, hmatch, _⟩ := exists_analytic_baseCoefficient_extension
    (Threefold.basePreimage U) s y hy hyU (finiteExtension W h) hrep hF
  exact exists_baseSection_extension U W hU hW h Fext hA hmatch

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
