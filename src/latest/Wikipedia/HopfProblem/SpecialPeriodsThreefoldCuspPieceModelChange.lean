import Wikipedia.HopfProblem.ToricCharts
import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# A common coordinate model for the cusp piece

The native toric charts have model `Fin 3 → ℂ`.  The other threefold pieces
have model `ℂ × ComplexPlane₂`.  The explicit complex-linear coordinate
equivalence below transports an atlas between these models.  Its identity
map is proved to be a biholomorphism; no compatibility of the two atlases
is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

/-- Split the first toric coordinate from the remaining two coordinates. -/
def cuspModelEquiv : ToricCharts.CoordinateSpace 3 ≃L[ℂ] (ℂ × ComplexPlane₂) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := ![x.1, x.2 0, x.2 1]
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_add' x y := rfl
  map_smul' r x := rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_fst
    · exact (continuous_apply 0).comp continuous_snd
    · exact (continuous_apply 1).comp continuous_snd

@[simp] theorem cuspModelEquiv_apply (x : ToricCharts.CoordinateSpace 3) :
    cuspModelEquiv x = (x 0, fun i => x i.succ) := rfl

@[simp] theorem cuspModelEquiv_symm_apply (x : ℂ × ComplexPlane₂) :
    cuspModelEquiv.symm x = ![x.1, x.2 0, x.2 1] := rfl

namespace ModelChange

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) (X : Type*) [TopologicalSpace X] [ChartedSpace E X]

/-- Compose each old chart with the given complex-linear equivalence. -/
@[instance_reducible] def chartedSpace : ChartedSpace F X where
  atlas := (fun c : OpenPartialHomeomorph X E =>
    c.trans e.toHomeomorph.toOpenPartialHomeomorph) '' atlas E X
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp only [mfld_simps]
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas E x)

@[simp] theorem chartAt_apply (x y : X) :
    letI := chartedSpace e X
    chartAt F x y = e (chartAt E x y) := rfl

@[simp] theorem chartAt_symm_apply (x : X) (y : F) :
    letI := chartedSpace e X
    (chartAt F x).symm y = (chartAt E x).symm (e.symm y) := rfl

@[simp] theorem chartAt_source (x : X) :
    letI := chartedSpace e X
    (chartAt F x).source = (chartAt E x).source := by
  simp [chartAt, ChartedSpace.chartAt]

@[simp] theorem chartAt_target (x : X) :
    letI := chartedSpace e X
    (chartAt F x).target = e.symm ⁻¹' (chartAt E x).target := by
  simp [chartAt, ChartedSpace.chartAt]

/-- The identity between the old and the transported atlas is analytic in
both directions, because its coordinate expressions are `e` and `e.symm`. -/
def diffeomorph (n : ℕ∞ω) :
    letI := chartedSpace e X
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) X X n := by
  let := chartedSpace e X
  refine { toEquiv := Equiv.refl X, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : y ∈ (chartAt E x).target := by simpa using hy.1
      simpa [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        congrArg e ((chartAt E x).right_inv hy')
    · simp only [mfld_simps]
  · intro x
    apply contMDiffWithinAt_iff'.2
    refine ⟨continuousWithinAt_id, ?_⟩
    apply e.symm.contDiff.contDiffWithinAt.congr_of_mem
    · intro y hy
      have hy' : e.symm y ∈ (chartAt E x).target := by
        simpa only [mfld_simps, chartAt_target] using hy.1
      simpa [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using
        (chartAt E x).right_inv hy'
    · simp only [mfld_simps]

@[simp] theorem diffeomorph_apply (n : ℕ∞ω) (x : X) :
    diffeomorph e X n x = x := rfl

@[simp] theorem diffeomorph_symm_apply (n : ℕ∞ω) (x : X) :
    letI := chartedSpace e X
    (diffeomorph e X n).symm x = x := rfl

/-- The transported atlas is a complex manifold whenever the native one is. -/
theorem isManifold (n : ℕ∞ω) [IsManifold (modelWithCornersSelf ℂ E) n X] :
    letI := chartedSpace e X
    IsManifold (modelWithCornersSelf ℂ F) n X := by
  let := chartedSpace e X
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hcd : ContDiffOn ℂ n (c.symm.trans d) (c.symm.trans d).source := by
    simpa [contDiffPregroupoid] using
      ((contDiffGroupoid n (modelWithCornersSelf ℂ E)).compatible hc hd).1
  have hcomp := e.contDiff.comp_contDiffOn
    (hcd.comp e.symm.contDiff.contDiffOn
      (show MapsTo e.symm (e.symm ⁻¹' (c.symm.trans d).source)
        (c.symm.trans d).source from fun _ hy => hy))
  simpa [preimage_preimage, Function.comp_def, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_target] using hcomp

/-- On an open subset, use the atlas inherited from the changed *ambient*
space.  The underlying identity is again analytic in both directions. -/
def openDiffeomorph (U : TopologicalSpace.Opens X) (n : ℕ∞ω) :
    letI := chartedSpace e X
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) U U n := by
  let := chartedSpace e X
  refine { toEquiv := Equiv.refl U, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · intro x
    have he : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) n
        (fun y : U => (y : X)) x ↔
        ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) n
          (Equiv.refl U) x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    apply he.mp
    exact contMDiffAt_subtype_iff.mpr (diffeomorph e X n).contMDiffAt
  · intro x
    have he : ContMDiffAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ E) n
        (fun y : U => (y : X)) x ↔
        ContMDiffAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ E) n
          (Equiv.refl U).symm x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    apply he.mp
    exact contMDiffAt_subtype_iff.mpr (diffeomorph e X n).symm.contMDiffAt

@[simp] theorem openDiffeomorph_apply (U : TopologicalSpace.Opens X) (n : ℕ∞ω) (x : U) :
    openDiffeomorph e X U n x = x := rfl

@[simp] theorem openDiffeomorph_symm_apply (U : TopologicalSpace.Opens X)
    (n : ℕ∞ω) (x : U) :
    letI := chartedSpace e X
    (openDiffeomorph e X U n).symm x = x := rfl

section Transfer

variable {G H Y : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ G H) (n : ℕ∞ω)

/-- A map into the changed model is analytic exactly when it is analytic
into the native model. -/
theorem contMDiff_right_iff (f : Y → X) :
    letI := chartedSpace e X
    ContMDiff I (modelWithCornersSelf ℂ F) n f ↔
      ContMDiff I (modelWithCornersSelf ℂ E) n f := by
  let := chartedSpace e X
  exact (diffeomorph e X n).contMDiff_diffeomorph_comp_iff le_rfl

/-- A map out of the changed model is analytic exactly when it is analytic
out of the native model. -/
theorem contMDiff_left_iff (f : X → Y) :
    letI := chartedSpace e X
    ContMDiff (modelWithCornersSelf ℂ F) I n f ↔
      ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  let := chartedSpace e X
  exact ((diffeomorph e X n).contMDiff_comp_diffeomorph_iff le_rfl).symm

/-- The corresponding map-into criterion for an inherited open-subset atlas. -/
theorem contMDiff_open_right_iff (U : TopologicalSpace.Opens X) (f : Y → U) :
    letI := chartedSpace e X
    ContMDiff I (modelWithCornersSelf ℂ F) n f ↔
      ContMDiff I (modelWithCornersSelf ℂ E) n f := by
  let := chartedSpace e X
  exact (openDiffeomorph e X U n).contMDiff_diffeomorph_comp_iff le_rfl

/-- The corresponding map-out criterion for an inherited open-subset atlas. -/
theorem contMDiff_open_left_iff (U : TopologicalSpace.Opens X) (f : U → Y) :
    letI := chartedSpace e X
    ContMDiff (modelWithCornersSelf ℂ F) I n f ↔
      ContMDiff (modelWithCornersSelf ℂ E) I n f := by
  let := chartedSpace e X
  exact ((openDiffeomorph e X U n).contMDiff_comp_diffeomorph_iff le_rfl).symm

end Transfer

end ModelChange

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
