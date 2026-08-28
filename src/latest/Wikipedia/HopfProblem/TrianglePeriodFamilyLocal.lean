import Wikipedia.HopfProblem.TrianglePeriodFamilyQuotient

/-!
# Actual local analytic identifications of the triangle quotient family

Over a local inverse patch of the base covering, the quotient is
biholomorphic to the full open part of the supplied varying-period
family over that inverse branch.  Both complex structures are inherited
from their constructed atlases; no fixed-complex-torus trivialization is
asserted.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- The actual inverse branch selected from the base covering. -/
def baseLocalInverse (b : B) : OpenPartialHomeomorph D.BaseSpace B :=
  DiagonalQuotient.baseLocalInverse hq b

@[simp] theorem baseLocalInverse_symm (b : B) :
    (D.baseLocalInverse hq b).symm = D.baseQuotient :=
  hq.isCoveringMap.isLocalHomeomorph.localInverseAt_symm b

/-- The base patch is exactly the source of the chosen covering inverse. -/
def basePatch (b : B) : Opens D.BaseSpace := DiagonalQuotient.patch hq b

/-- The open sheet of the original base selected by that inverse branch. -/
def baseSheet (b : B) : Opens B :=
  ⟨(D.baseLocalInverse hq b).target, (D.baseLocalInverse hq b).open_target⟩

/-- The full original period family over the chosen open base sheet. -/
def upstairsPatch (b : B) : Opens D.TotalSpace :=
  ⟨D.periods.projection ⁻¹' (D.baseSheet hq b : Set B),
    (D.baseSheet hq b).isOpen.preimage D.periods.projection_proper.continuous⟩

/-- The full quotient family over the chosen open base patch. -/
def downstairsPatch (b : B) : Opens D.Space :=
  ⟨D.projection ⁻¹' (D.basePatch hq b : Set D.BaseSpace),
    (D.basePatch hq b).isOpen.preimage D.projection_continuous⟩

theorem quotient_mapsTo_patch (b : B) :
    MapsTo D.quotient (D.upstairsPatch hq b : Set D.TotalSpace)
      (D.downstairsPatch hq b : Set D.Space) := by
  intro x hx
  change D.projection (D.quotient x) ∈ (D.baseLocalInverse hq b).source
  rw [D.projection_quotient]
  simpa only [D.baseLocalInverse_symm] using (D.baseLocalInverse hq b).map_target hx

/-- The actual quotient map restricted to the two full open families. -/
def localQuotient (b : B) : D.upstairsPatch hq b → D.downstairsPatch hq b :=
  fun x => ⟨D.quotient x.val, D.quotient_mapsTo_patch hq b x.property⟩

@[simp] theorem localQuotient_coe (b : B) (x : D.upstairsPatch hq b) :
    (D.localQuotient hq b x : D.Space) = D.quotient x.val := rfl

theorem localQuotient_injective (b : B) : Function.Injective (D.localQuotient hq b) := by
  let := D.totalAction
  let := hq.isCancelSMul
  intro x y hxy
  have heq : D.quotient x.val = D.quotient y.val := congrArg Subtype.val hxy
  have hb : D.periods.projection x.val = D.periods.projection y.val :=
    hq.isCoveringMap.isLocalHomeomorph.injOn_localInverseAt_target x.property y.property
      (by simpa only [D.projection_quotient] using congrArg D.projection heq)
  obtain ⟨g, hg⟩ := (D.quotient_eq_iff x.val y.val).mp heq
  have hgbase : g • y.val.1 = y.val.1 := by
    have he := congrArg Prod.fst hg
    change g • y.val.1 = x.val.1 at he
    exact he.trans hb
  have hg1 : g = 1 := IsCancelSMul.right_cancel _ _ y.val.1
    (hgbase.trans (one_smul TriangleGroup y.val.1).symm)
  apply Subtype.ext
  simpa only [hg1, one_smul] using hg.symm

theorem localQuotient_surjective (b : B) : Function.Surjective (D.localQuotient hq b) := by
  let := D.totalAction
  intro y
  obtain ⟨x, hx⟩ := D.quotient_surjective y.val
  have hy : D.baseQuotient (D.periods.projection x) ∈ (D.baseLocalInverse hq b).source := by
    have hy := y.property
    change D.projection y.val ∈ (D.baseLocalInverse hq b).source at hy
    rwa [← hx, D.projection_quotient] at hy
  have hbase := hq.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem hy
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hbase
  have hsource : g • x ∈ D.upstairsPatch hq b := by
    change g • x.1 ∈ (D.baseLocalInverse hq b).target
    have he : g • x.1 = D.baseLocalInverse hq b (D.baseQuotient x.1) := hg
    rw [he]
    exact (D.baseLocalInverse hq b).map_source hy
  refine ⟨⟨g • x, hsource⟩, ?_⟩
  apply Subtype.ext
  change D.quotient (g • x) = y.val
  rw [D.quotient_smul, hx]

theorem localQuotient_continuous (b : B) : Continuous (D.localQuotient hq b) :=
  (D.quotient_continuous.comp continuous_subtype_val).subtype_mk _

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual quotient covering is locally biholomorphic for the
explicitly selected varying-period and quotient atlases. -/
theorem quotient_isLocalDiffeomorph :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap hq)
    D.totalAction_holomorphic

/-- Restriction to the open sheet and full base-patch preimage retains
the genuine local analytic inverse. -/
theorem localQuotient_isLocalDiffeomorph (b : B) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.localQuotient hq b) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  exact isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ (V × ComplexPlane₂))
    (modelWithCornersSelf ℂ (V × ComplexPlane₂)) (D.quotient_isLocalDiffeomorph hq)
    (D.upstairsPatch hq b) (D.downstairsPatch hq b) (D.quotient_mapsTo_patch hq b)

/-- The quotient restricted over one actual base inverse branch is a
biholomorphism of the two full open varying-period families. -/
def localBiholomorph (b : B) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    Diffeomorph (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (modelWithCornersSelf ℂ (V × ComplexPlane₂))
      (D.upstairsPatch hq b) (D.downstairsPatch hq b) ω := by
  letI := D.periods.totalChartedSpace
  letI := D.chartedSpace hq
  exact (D.localQuotient_isLocalDiffeomorph hq b).diffeomorphOfBijective
    ⟨D.localQuotient_injective hq b, D.localQuotient_surjective hq b⟩

@[simp] theorem localBiholomorph_apply_coe (b : B) (x : D.upstairsPatch hq b) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    (D.localBiholomorph hq b x : D.Space) = D.quotient x.val := rfl

/-- This is an identification of the actual family projections, with
the base coordinate changed by the original quotient covering. -/
theorem localBiholomorph_projection (b : B) (x : D.upstairsPatch hq b) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    D.projection (D.localBiholomorph hq b x).val =
      D.baseQuotient (D.periods.projection x.val) :=
  D.projection_quotient x.val

/-- The inverse identification uses precisely the chosen inverse branch
on the base, rather than an unrelated topological product coordinate. -/
theorem localBiholomorph_symm_projection (b : B) (y : D.downstairsPatch hq b) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace hq
    D.periods.projection ((D.localBiholomorph hq b).symm y).val =
      D.baseLocalInverse hq b (D.projection y.val) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  let e := D.localBiholomorph hq b
  have hb : D.periods.projection (e.symm y).val ∈ (D.baseLocalInverse hq b).target :=
    (e.symm y).property
  have hp : D.projection y.val = D.baseQuotient (D.periods.projection (e.symm y).val) := by
    have h := D.localBiholomorph_projection hq b (e.symm y)
    change D.projection (e (e.symm y)).val = _ at h
    simpa only [e.apply_symm_apply] using h
  have he : D.baseLocalInverse hq b
      (D.baseQuotient (D.periods.projection (e.symm y).val)) =
      D.periods.projection (e.symm y).val := by
    simpa only [D.baseLocalInverse_symm] using (D.baseLocalInverse hq b).right_inv hb
  exact ((congrArg (D.baseLocalInverse hq b) hp).trans he).symm

theorem localQuotient_openEmbedding (b : B) : IsOpenEmbedding (D.localQuotient hq b) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  exact (D.localBiholomorph hq b).toHomeomorph.isOpenEmbedding

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
