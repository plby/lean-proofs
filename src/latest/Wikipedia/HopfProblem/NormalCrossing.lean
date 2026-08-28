import Wikipedia.HopfProblem.NormalCrossingCoordinates
import Wikipedia.HopfProblem.CoveringManifold

/-!
# Analytic normal-crossing equations

The definition records a chart in the maximal analytic atlas, centred
at the point, in which the function is a product of distinct coordinates.
The property is preserved under open restriction and descends through
the holomorphic quotient coverings constructed here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

def NormalCrossingChartAt {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]
    (J : Finset (Fin 3)) (f : M → ℂ) (x : M) : Prop :=
  ∃ e : OpenPartialHomeomorph M E₃,
    e ∈ IsManifold.maximalAtlas I₃ ω M ∧ x ∈ e.source ∧ e x = 0 ∧
      ∀ w ∈ e.target, f (e.symm w) = ∏ j ∈ J, w j

def HasNormalCrossingAt {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M]
    (f : M → ℂ) (x : M) : Prop :=
  ∃ J : Finset (Fin 3), J.Nonempty ∧ NormalCrossingChartAt J f x

theorem normalCrossingChartAt_product (a : E₃) (J : Finset (Fin 3)) (hJ : J.Nonempty)
    (hzero : ∀ j ∈ J, a j = 0) (hunit : ∀ j ∉ J, a j ≠ 0) :
    NormalCrossingChartAt J Triangle.time a := by
  obtain ⟨i, hi⟩ := hJ
  let e := NormalCrossingCoordinates.centeredChart J i hi a
  refine ⟨e, ?_, NormalCrossingCoordinates.mem_centeredChart_source J i hi a hunit,
    NormalCrossingCoordinates.centeredChart_center J i hi a (hzero i hi), ?_⟩
  · exact e.mem_maximalAtlas_of_contMDiffOn
      (NormalCrossingCoordinates.centeredChart_holomorphic J i hi a).contMDiffOn
      (NormalCrossingCoordinates.centeredChart_symm_holomorphic J i hi a).contMDiffOn
  · exact fun _ hw => NormalCrossingCoordinates.centeredChart_symm_product J i hi a hzero hw

theorem normalCrossingAt_product (a : E₃) (ha : Triangle.time a = 0) :
    HasNormalCrossingAt Triangle.time a := by
  classical
  let J := Finset.univ.filter (fun j : Fin 3 => a j = 0)
  have hJ : J.Nonempty := by
    obtain h | h | h := (Triangle.central_fibre a).mp ha
    · exact ⟨0, by simp [J, h]⟩
    · exact ⟨1, by simp [J, h]⟩
    · exact ⟨2, by simp [J, h]⟩
  have hzero : ∀ j ∈ J, a j = 0 := fun _ hj => (Finset.mem_filter.mp hj).2
  have hunit : ∀ j ∉ J, a j ≠ 0 := by
    intro j hj h
    exact hj (by simp [J, h])
  exact ⟨J, hJ, normalCrossingChartAt_product a J hJ hzero hunit⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold I₃ ω M]

theorem NormalCrossingChartAt.of_chart {J : Finset (Fin 3)} {f : M → ℂ} {g : E₃ → ℂ}
    {x : M} (e : OpenPartialHomeomorph M E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) (hx : x ∈ e.source)
    (hp : ∀ w ∈ e.target, f (e.symm w) = g w) (h : NormalCrossingChartAt J g (e x)) :
    NormalCrossingChartAt J f x := by
  obtain ⟨d, hd, ha, hc, hprod⟩ := h
  refine ⟨e.trans d, ?_, ⟨hx, ha⟩, hc, ?_⟩
  · apply (e.trans d).mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hd).comp
        ((contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ hy => hy.2)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hd).mono inter_subset_left) (fun _ hy => hy.2)
  · intro w hw
    change f (e.symm (d.symm w)) = ∏ j ∈ J, w j
    rw [hp _ hw.2, hprod _ hw.1]

theorem normalCrossingAt_of_chart {f : M → ℂ} {x : M} (e : OpenPartialHomeomorph M E₃)
    (he : e ∈ IsManifold.maximalAtlas I₃ ω M) (hx : x ∈ e.source) (hf : f x = 0)
    (hp : ∀ w ∈ e.target, f (e.symm w) = Triangle.time w) : HasNormalCrossingAt f x := by
  have hzero : Triangle.time (e x) = 0 := by
    rw [← hp (e x) (e.map_source hx), e.left_inv hx, hf]
  obtain ⟨J, hJ, h⟩ := normalCrossingAt_product (e x) hzero
  exact ⟨J, hJ, h.of_chart e he hx hp⟩

theorem normalCrossing_subtype_chart (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (e : OpenPartialHomeomorph M E₃) (he : e ∈ IsManifold.maximalAtlas I₃ ω M) :
    e.subtypeRestr hU ∈ IsManifold.maximalAtlas I₃ ω U := by
  apply (e.subtypeRestr hU).mem_maximalAtlas_of_contMDiffOn
  · rw [e.subtypeRestr_source]
    have hv : ContMDiff I₃ I₃ ω (Subtype.val : U → M) := contMDiff_subtype_val
    exact (contMDiffOn_of_mem_maximalAtlas he).comp hv.contMDiffOn (fun _ hx => hx)
  · have hv : ContMDiffOn I₃ I₃ ω (Subtype.val ∘ (e.subtypeRestr hU).symm)
        (e.subtypeRestr hU).target :=
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono
        (e.subtypeRestr_target_subset hU)).congr (fun _ hw => e.subtypeRestr_symm_apply hU hw)
    intro w hw
    have hi : ContMDiffWithinAt I₃ I₃ ω (Subtype.val ∘ (e.subtypeRestr hU).symm)
        (e.subtypeRestr hU).target w ↔
      ContMDiffWithinAt I₃ I₃ ω (e.subtypeRestr hU).symm (e.subtypeRestr hU).target w :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact hi.mp (hv w hw)

theorem NormalCrossingChartAt.restrict {J : Finset (Fin 3)} {f : M → ℂ}
    (U : TopologicalSpace.Opens M) (x : U) (h : NormalCrossingChartAt J f (x : M)) :
    NormalCrossingChartAt J (fun y : U => f (y : M)) x := by
  obtain ⟨e, he, hx, hc, hp⟩ := h
  refine ⟨e.subtypeRestr ⟨x⟩, normalCrossing_subtype_chart U ⟨x⟩ e he, ?_, hc, ?_⟩
  · rw [e.subtypeRestr_source]
    exact hx
  · intro w hw
    change f ((e.subtypeRestr ⟨x⟩).symm w : M) = ∏ j ∈ J, w j
    rw [show ((e.subtypeRestr ⟨x⟩).symm w : M) = e.symm w from
      e.subtypeRestr_symm_apply ⟨x⟩ hw]
    exact hp w (e.subtypeRestr_target_subset ⟨x⟩ hw)

theorem HasNormalCrossingAt.restrict {f : M → ℂ} (U : TopologicalSpace.Opens M)
    (x : U) (h : HasNormalCrossingAt f (x : M)) :
    HasNormalCrossingAt (fun y : U => f (y : M)) x := by
  obtain ⟨J, hJ, h⟩ := h
  exact ⟨J, hJ, h.restrict U x⟩

theorem NormalCrossingChartAt.descend {Q G : Type*} [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (hG : ∀ g : G, ContMDiff I₃ I₃ ω (fun x : M => g • x))
    {J : Finset (Fin 3)} {f : Q → ℂ} {a : M} (h : NormalCrossingChartAt J (f ∘ q) a) :
    letI := CoveringQuotient.chartedSpace (E := E₃) hq
    NormalCrossingChartAt J f (q a) := by
  let := CoveringQuotient.chartedSpace (E := E₃) hq
  let := CoveringQuotient.isManifold (E := E₃) hq ω hG
  obtain ⟨e, he, ha, hc, hp⟩ := h
  let d := (CoveringQuotient.localInverse hq a).trans e
  have hs : (d.symm : E₃ → Q) = q ∘ e.symm := by
    change (CoveringQuotient.localInverse hq a).symm ∘ e.symm = _
    rw [CoveringQuotient.localInverse_symm]
  have hself : CoveringQuotient.localInverse hq a (q a) = a :=
    hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas he).comp
        ((CoveringQuotient.localInverse_holomorphic hq ω hG a).mono inter_subset_left)
        (fun _ hx => hx.2)
    · rw [hs]
      exact (CoveringQuotient.contMDiff_project hq ω hG).comp_contMDiffOn
        ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)
  · refine ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, ?_⟩
    change CoveringQuotient.localInverse hq a (q a) ∈ e.source
    rw [hself]
    exact ha
  · change e (CoveringQuotient.localInverse hq a (q a)) = 0
    rw [hself, hc]
  · intro w hw
    rw [hs]
    exact hp w hw.1

theorem HasNormalCrossingAt.descend {Q G : Type*} [TopologicalSpace Q] [Group G]
    [MulAction G M] {q : M → Q} (hq : IsQuotientCoveringMap q G)
    (hG : ∀ g : G, ContMDiff I₃ I₃ ω (fun x : M => g • x))
    {f : Q → ℂ} {a : M} (h : HasNormalCrossingAt (f ∘ q) a) :
    letI := CoveringQuotient.chartedSpace (E := E₃) hq
    HasNormalCrossingAt f (q a) := by
  let := CoveringQuotient.chartedSpace (E := E₃) hq
  obtain ⟨J, hJ, h⟩ := h
  exact ⟨J, hJ, h.descend hq hG⟩

end Wikipedia.HopfProblem
