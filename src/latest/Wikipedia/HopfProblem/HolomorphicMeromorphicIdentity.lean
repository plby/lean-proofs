import Wikipedia.HopfProblem.HolomorphicMeromorphicIdentityAnalytic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChart
import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain

/-!
# Identity principles and nonzero germs in the native manifold atlas

The analytic identity principle on connected model balls implies local
propagation of nonzero holomorphic germs.  The actual extended charts
transfer this fact to the original boundaryless complex manifold.  The
zero-germ and nonzero-germ loci of a scalar holomorphic map are therefore
both open and closed, giving the identity principle on a connected domain.

For sections of the genuine holomorphic function sheaf these are the
actual categorical stalk germs.  A nonzero germ admits a smaller open
domain on which every restricted germ is nonzero.  A section with no zero
germs has dense cozero locus.  No alternative charts or topology are used.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- Nonzero scalar holomorphic germs propagate to an actual neighborhood
in the original manifold, by the identity principle in its existing chart. -/
theorem contMDiffAt_eventually_nonzero_germ {f : M → ℂ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℂ) ω f x) (hne : ¬ f =ᶠ[𝓝 x] 0) :
    ∀ᶠ y in 𝓝 x, ¬ f =ᶠ[𝓝 y] 0 := by
  let F : E → ℂ := f ∘ (extChartAt I x).symm
  have hF : AnalyticAt ℂ F (extChartAt I x x) := by
    have h := contMDiffAt_iff_source.mp hf
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    exact h.contDiffAt.analyticAt
  have hFne : ¬ F =ᶠ[𝓝 (extChartAt I x x)] 0 := by
    intro h
    apply hne
    change f =ᶠ[Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x))] 0 at h
    rwa [HolomorphicFunctionSheaf.chartInverse_map_nhds I x] at h
  have hlocal := analyticAt_eventually_nonzero_germ hF hFne
  have hlocalM := (continuousAt_extChartAt (I := I) x).eventually hlocal
  filter_upwards [hlocalM, extChartAt_source_mem_nhds (I := I) x] with y hy hys
  intro hzero
  apply hy
  have hinv : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x y)) (𝓝 y) := by
    simpa only [ContinuousAt, (extChartAt I x).left_inv hys] using
      (continuousAt_extChartAt_symm' (I := I) (x := x) hys)
  exact hzero.comp_tendsto hinv

theorem isOpen_contMDiff_nonzero_germ_locus {f : M → ℂ}
    (hf : ContMDiff I 𝓘(ℂ) ω f) : IsOpen {x : M | ¬ f =ᶠ[𝓝 x] 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact contMDiffAt_eventually_nonzero_germ I (hf x) hx

/-- Vanishing on a neighborhood is an open condition by topology and a
closed condition by the actual analytic identity principle. -/
theorem isClopen_contMDiff_zero_germ_locus {f : M → ℂ}
    (hf : ContMDiff I 𝓘(ℂ) ω f) : IsClopen {x : M | f =ᶠ[𝓝 x] 0} := by
  refine ⟨?_, isOpen_setOfPred_eventually_nhds⟩
  simpa only [compl_ofPred, not_not] using
    (isOpen_contMDiff_nonzero_germ_locus I hf).isClosed_compl

theorem isClopen_contMDiff_nonzero_germ_locus {f : M → ℂ}
    (hf : ContMDiff I 𝓘(ℂ) ω f) : IsClopen {x : M | ¬ f =ᶠ[𝓝 x] 0} :=
  (isClopen_contMDiff_zero_germ_locus I hf).compl

/-- The scalar identity principle on a connected native complex manifold:
vanishing of one neighborhood germ forces global vanishing. -/
theorem contMDiff_eq_zero_of_eventuallyEq_zero [PreconnectedSpace M]
    {f : M → ℂ} (hf : ContMDiff I 𝓘(ℂ) ω f) {x : M}
    (hzero : f =ᶠ[𝓝 x] 0) : f = 0 := by
  have hall := (isClopen_contMDiff_zero_germ_locus I hf).eq_univ ⟨x, hzero⟩
  funext y
  have hy : f =ᶠ[𝓝 y] 0 := by
    have hym : y ∈ ({z : M | f =ᶠ[𝓝 z] 0} : Set M) := by
      rw [hall]
      trivial
    exact hym
  exact hy.self_of_nhds

/-- Equality of one actual neighborhood germ determines a scalar
holomorphic function on a connected native complex manifold. -/
theorem contMDiff_eq_of_eventuallyEq [PreconnectedSpace M]
    {f g : M → ℂ} (hf : ContMDiff I 𝓘(ℂ) ω f) (hg : ContMDiff I 𝓘(ℂ) ω g)
    {x : M} (hfg : f =ᶠ[𝓝 x] g) : f = g := by
  have hz : (fun y => f y - g y) =ᶠ[𝓝 x] 0 :=
    hfg.mono fun _ h => sub_eq_zero.mpr h
  have hident := contMDiff_eq_zero_of_eventuallyEq_zero I (hf.sub hg) hz
  funext y
  exact sub_eq_zero.mp (congrFun hident y)

end Wikipedia.HopfProblem.HolomorphicMeromorphicIdentity

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization HolomorphicMeromorphicIdentity

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

/-- Zero in the actual categorical stalk means that the section's literal
extension vanishes on a neighborhood in the original manifold. -/
theorem germ_eq_zero_iff_extend_eventuallyEq_zero (U : Opens M)
    (f : Section I M U) (x : M) (hx : x ∈ U) :
    (presheaf I M).germ U x hx f = 0 ↔ extendManifoldSection I U f =ᶠ[𝓝 x] 0 := by
  rw [← (chartStalkEquiv I x).map_eq_zero_iff, chartStalkEquiv_germ,
    Germs.ofAnalytic_eq_zero_iff]
  change extendManifoldSection I U f =ᶠ[
    Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x))] 0 ↔ _
  rw [chartInverse_map_nhds I x]

/-- Equivalently, zero in the native stalk is vanishing on a neighborhood
in the section's actual open domain. -/
theorem germ_eq_zero_iff_eventuallyEq_zero (U : Opens M) (f : Section I M U) (x : U) :
    (presheaf I M).germ U x x.property f = 0 ↔ (f : U → ℂ) =ᶠ[𝓝 x] 0 := by
  rw [germ_eq_zero_iff_extend_eventuallyEq_zero]
  rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x]
  change (fun y : U => extendManifoldSection I U f y) =ᶠ[𝓝 x] 0 ↔ _
  rw [extendManifoldSection_comp_val I U f]

/-- The nonzero native-stalk-germ locus is clopen in the original section
domain.  In particular no locally chosen denominator disappears as a germ
at a sufficiently nearby point. -/
theorem isClopen_nonzero_germ_locus (U : Opens M) (f : Section I M U) :
    IsClopen {x : U | (presheaf I M).germ U x x.property f ≠ 0} := by
  have he : {x : U | (presheaf I M).germ U x x.property f ≠ 0} =
      {x : U | ¬ (f : U → ℂ) =ᶠ[𝓝 x] 0} := by
    ext x
    exact not_congr (germ_eq_zero_iff_eventuallyEq_zero I U f x)
  rw [he]
  exact isClopen_contMDiff_nonzero_germ_locus I f.contMDiff

theorem isOpen_nonzero_germ_locus (U : Opens M) (f : Section I M U) :
    IsOpen {x : U | (presheaf I M).germ U x x.property f ≠ 0} :=
  (isClopen_nonzero_germ_locus I U f).isOpen

/-- A nonzero native germ persists on a smaller actual open neighborhood
contained in the given section domain. -/
theorem exists_open_nonzero_germ_neighborhood (U : Opens M) (f : Section I M U)
    (x : M) (hx : x ∈ U) (hne : (presheaf I M).germ U x hx f ≠ 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), x ∈ V ∧
      ∀ y (hy : y ∈ V), (presheaf I M).germ U y (hVU hy) f ≠ 0 := by
  have hne' : ¬ extendManifoldSection I U f =ᶠ[𝓝 x] 0 :=
    fun h => hne ((germ_eq_zero_iff_extend_eventuallyEq_zero I U f x hx).mpr h)
  have hlocal := contMDiffAt_eventually_nonzero_germ I
    (extendManifoldSection_contMDiffAt I U f x hx) hne'
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp
    (inter_mem (U.isOpen.mem_nhds hx) hlocal)
  let V' : Opens M := ⟨V, hVo⟩
  have hVU : V' ≤ U := fun _ hy => (hVsub hy).1
  refine ⟨V', hVU, hxV, ?_⟩
  intro y hy hzero
  exact (hVsub hy).2
    ((germ_eq_zero_iff_extend_eventuallyEq_zero I U f y (hVU hy)).mp hzero)

/-- The same neighborhood conclusion for the literal restricted section
and its native stalk germs, as used by local meromorphic denominators. -/
theorem exists_open_restriction_germs_ne_zero (U : Opens M) (f : Section I M U)
    (x : M) (hx : x ∈ U) (hne : (presheaf I M).germ U x hx f ≠ 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), x ∈ V ∧
      ∀ y : V, (presheaf I M).germ V y y.property
        ((presheaf I M).map (homOfLE hVU).op f) ≠ 0 := by
  obtain ⟨V, hVU, hxV, hV⟩ := exists_open_nonzero_germ_neighborhood I U f x hx hne
  refine ⟨V, hVU, hxV, fun y => ?_⟩
  intro hzero
  exact hV y y.property
    (((presheaf I M).germ_res_apply (homOfLE hVU) y.val y.property f).symm.trans hzero)

/-- If every native germ is nonzero, the section is nonzero on a dense
subset of its original open domain. -/
theorem dense_cozero_of_germs_ne_zero (U : Opens M) (f : Section I M U)
    (hne : ∀ x : U, (presheaf I M).germ U x x.property f ≠ 0) :
    Dense {x : U | f x ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro V hVo hVne
  by_contra hnone
  obtain ⟨x, hx⟩ := hVne
  apply hne x
  apply (germ_eq_zero_iff_eventuallyEq_zero I U f x).mpr
  filter_upwards [hVo.mem_nhds hx] with y hy
  by_contra hyzero
  exact hnone ⟨y, hy, hyzero⟩

/-- Equality of one native stalk germ determines holomorphic sections on
a connected original open domain. -/
theorem section_eq_of_germ_eq (U : Opens M) [PreconnectedSpace U]
    (f g : Section I M U) (x : U)
    (hfg : (presheaf I M).germ U x x.property f =
      (presheaf I M).germ U x x.property g) : f = g := by
  have hz : (presheaf I M).germ U x x.property (f - g) = 0 := by
    let γ : Section I M U →+* (presheaf I M).stalk x.val :=
      ((presheaf I M).germ U x.val x.property).hom
    have hγ : γ f = γ g := hfg
    change γ (f - g) = 0
    rw [map_sub, hγ, sub_self]
  have he := (germ_eq_zero_iff_eventuallyEq_zero I U (f - g) x).mp hz
  have hident := contMDiff_eq_zero_of_eventuallyEq_zero I (f - g).contMDiff he
  apply ContMDiffMap.ext
  intro y
  exact sub_eq_zero.mp (congrFun hident y)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
