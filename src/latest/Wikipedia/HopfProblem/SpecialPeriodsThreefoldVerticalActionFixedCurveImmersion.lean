import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCurve
import Wikipedia.HopfProblem.CuspCurveImmersion

/-!
# The actual double-curve inclusions are holomorphic immersions

The native cusp-axis immersion charts transport through the actual cusp
local biholomorphism. The explicit coordinate-model equivalence changes
only the chart coordinates, not the glued threefold's atlas or the literal
global double-curve inclusion.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve

section ChartTransport

variable {E V W F A M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace A] [ChartedSpace E A]
  [TopologicalSpace M] [ChartedSpace V M]
  [TopologicalSpace N] [ChartedSpace W N]
  [IsManifold (modelWithCornersSelf ℂ W) ω N]

/-- Transport an immersion normal form through a local biholomorphism
whose target uses a different, explicitly equivalent coordinate model. -/
private theorem immersionAt_postcomp_modelEquiv (L : V ≃L[ℂ] W)
    {f : A → M} {q : M → N} {x : A}
    (hf : Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω f x)
    (hq : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ W) ω q (f x)) :
    Manifold.IsImmersionAtOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ W) ω (q ∘ f) x := by
  let e := hq.localInverse.toOpenPartialHomeomorph
  have hUmem : f ⁻¹' e.target ∈ 𝓝 x :=
    hf.continuousAt (e.open_target.mem_nhds hq.localInverse_mem_target)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hUmem
  let d := hf.domChart.restr U
  let c₀ := e.trans hf.codChart
  let c := c₀.transHomeomorph L.toHomeomorph
  have hself : e (q (f x)) = f x :=
    hq.localInverse_left_inv hq.localInverse_mem_target
  have hc₀ : ContMDiffOn (modelWithCornersSelf ℂ W) (modelWithCornersSelf ℂ V) ω
      c₀ c₀.source :=
    (contMDiffOn_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).comp
      (hq.localInverse.contMDiffOn_toFun.mono inter_subset_left) (fun _ hy => hy.2)
  have hc₀' : ContMDiffOn (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ W) ω
      c₀.symm c₀.target :=
    hq.localInverse.contMDiffOn_invFun.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hf.codChart_mem_maximalAtlas).mono
        inter_subset_left) (fun _ hy => hy.2)
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hq.contMDiffAt.continuousAt.comp hf.continuousAt) (hf.equiv.trans L) d c
      ?_ ?_ ?_ ?_ ?_
  · change x ∈ (hf.domChart.restr U).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hU]
    exact ⟨hf.mem_domChart_source, hxU⟩
  · refine ⟨hq.localInverse_mem_source, ?_⟩
    change e (q (f x)) ∈ hf.codChart.source
    rw [hself]
    exact hf.mem_codChart_source
  · exact restr_mem_maximalAtlas _ hf.domChart_mem_maximalAtlas hU
  · apply c.mem_maximalAtlas_of_contMDiffOn
    · exact L.contDiff.contMDiff.comp_contMDiffOn hc₀
    · exact hc₀'.comp L.symm.contDiff.contMDiff.contMDiffOn (fun _ hy => hy)
  · intro z hz
    have hz' : z ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hz
    have hz0 : z ∈ hf.domChart.target := hz'.1
    have hfz : f (hf.domChart.symm z) ∈ e.target := by
      have hmem := d.map_target hz'
      change (hf.domChart.restr U).symm z ∈ (hf.domChart.restr U).source at hmem
      rw [OpenPartialHomeomorph.restr_source' _ _ hU] at hmem
      exact hUsub hmem.2
    have heq : e (q (f (hf.domChart.symm z))) = f (hf.domChart.symm z) :=
      hq.localInverse_left_inv hfz
    change L (hf.codChart (e (q (f (hf.domChart.symm z))))) = L (hf.equiv (z, 0))
    rw [heq]
    exact congrArg L (hf.writtenInCharts
      (by simpa [OpenPartialHomeomorph.extend] using hz0))

end ChartTransport

open ToricCharts ToricFan

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_t2Space Threefold.space_isManifold

/-- Every original native axis remains an immersion after its actual
inclusion into the glued threefold. -/
theorem axisMap_inclusion_isImmersionOfComplement (s : Triangle) (i : Fin 3) :
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) I₁ IF ω
      (CuspGeometry.inclusion ∘ CuspQuotient.axisMap CuspGeometry.data.correction
        CuspGeometry.data.radius CuspGeometry.data.radius_pos s i) := by
  let := CuspQuotient.chartedSpace CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift
  let : ChartedSpace (CoordinateSpace 3) CuspGeometry.LocalSpace :=
    CuspGeometry.nativeChartedSpace
  have haxis : Manifold.IsImmersionOfComplement (CoordinateSpace 2) I₁
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (CuspQuotient.axisMap CuspGeometry.data.correction CuspGeometry.data.radius
        CuspGeometry.data.radius_pos s i) :=
    CuspQuotient.axisMap_isImmersionOfComplement CuspGeometry.data.radius
      CuspGeometry.data.radius_pos CuspGeometry.data.correction
      CuspGeometry.data.radius_lt_one CuspGeometry.data.holomorphic
      CuspGeometry.data.smallDrift s i
  intro z
  exact immersionAt_postcomp_modelEquiv (M := CuspGeometry.LocalSpace)
    cuspModelEquiv (haxis z) (CuspGeometry.inclusion_isLocalDiffeomorph _)

/-- The literal global double-curve inclusion has complex codimension two
in the unchanged glued atlas. -/
theorem inclusion_isImmersionOfComplement (i : Fin 3) :
    letI := chartedSpace i
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) I₁ IF ω
      (Subtype.val : Curve i → Threefold.Space) := by
  let := chartedSpace i
  apply (charts i).immersion_of_comp_affineMaps _ continuous_subtype_val
  intro b
  cases b
  · exact axisMap_inclusion_isImmersionOfComplement ToricSpace.referenceTriangle i
  · exact axisMap_inclusion_isImmersionOfComplement (Triangle.upperNeighbour i) i

/-- The actual two-axis complex atlas makes the global named curve a
holomorphically immersed sphere in the original threefold. -/
theorem inclusion_isImmersion (i : Fin 3) :
    letI := chartedSpace i
    Manifold.IsImmersion I₁ IF ω (Subtype.val : Curve i → Threefold.Space) := by
  let := chartedSpace i
  exact (inclusion_isImmersionOfComplement i).isImmersion

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCurve
