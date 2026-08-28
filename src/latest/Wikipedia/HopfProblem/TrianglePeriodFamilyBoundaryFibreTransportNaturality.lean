import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreTransport
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportPaths

/-!
# Actual fibre transport followed by inclusion on singular homology

The horizontal covering lift and a fixed real-torus coordinate give a
jointly continuous homotopy on an entire literal family fibre. Its endpoint
is the previously constructed actual fibre-transport homeomorphism followed
by inclusion. Homotopy invariance proves the inclusion--transport identity
in every singular-homology degree. The flat coordinates are also explicitly
identified with the original complex period-column loops.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)

/-- The literal inclusion of a family fibre, without choosing a torus marking. -/
def boundaryFibreInclusion (x : D.BaseSpace) : C(D.projection ⁻¹' {x}, D.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem boundaryFibreInclusion_apply (x : D.BaseSpace)
    (f : D.projection ⁻¹' {x}) : D.boundaryFibreInclusion x f = f.val := rfl

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- With one initial covering lift fixed, the entire actual initial fibre
moves continuously along the unique lifted base path. Its endpoint is the
actual transport homeomorphism, not a separately prescribed marking map. -/
def boundaryTransportHomotopy (b : B) {y : D.BaseSpace}
    (γ : Path (D.baseQuotient b) y) :
    (D.boundaryFibreInclusion (D.baseQuotient b)).Homotopy
      ((D.boundaryFibreInclusion y).comp
        (D.pathTransport hq γ :
          C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {y}))) where
  toFun tf := D.horizontalPath hq γ b rfl
    ((D.flatFibreHomeomorph hq b).symm tf.2) tf.1
  continuous_toFun := by
    change Continuous (fun tf : unitInterval × (D.projection ⁻¹' {D.baseQuotient b}) =>
      D.quotient (hq.isCoveringMap.liftPath γ b γ.source tf.1,
        (D.flatFibreHomeomorph hq b).symm tf.2))
    exact D.quotient_continuous.comp
      (((hq.isCoveringMap.liftPath γ b γ.source).continuous.comp continuous_fst).prodMk
        ((D.flatFibreHomeomorph hq b).symm.continuous.comp continuous_snd))
  map_zero_left f := by
    change D.horizontalPath hq γ b rfl ((D.flatFibreHomeomorph hq b).symm f) 0 = f.val
    rw [D.horizontalPath_source]
    exact (D.flatFibreHomeomorph_coe hq b ((D.flatFibreHomeomorph hq b).symm f)).symm.trans
      (congrArg Subtype.val ((D.flatFibreHomeomorph hq b).apply_symm_apply f))
  map_one_left f := by
    change D.horizontalPath hq γ b rfl ((D.flatFibreHomeomorph hq b).symm f) 1 =
      (D.pathTransport hq γ f : D.Space)
    rw [D.horizontalPath_target_transport]
    have hf : (⟨D.quotient (b, (D.flatFibreHomeomorph hq b).symm f), rfl⟩ :
        D.projection ⁻¹' {D.baseQuotient b}) = f :=
      (Subtype.ext
        (D.flatFibreHomeomorph_coe hq b ((D.flatFibreHomeomorph hq b).symm f))).symm.trans
        ((D.flatFibreHomeomorph hq b).apply_symm_apply f)
    exact congrArg (fun u => (D.pathTransport hq γ u : D.Space)) hf

/-- The actual whole-fibre homotopy keeps its real-torus coordinate fixed
and uses precisely the original covering path lift. -/
@[simp] theorem boundaryTransportHomotopy_apply (b : B) {y : D.BaseSpace}
    (γ : Path (D.baseQuotient b) y) (t : unitInterval)
    (f : D.projection ⁻¹' {D.baseQuotient b}) :
    D.boundaryTransportHomotopy hq b γ (t, f) =
      D.quotient (hq.isCoveringMap.liftPath γ b γ.source t,
        (D.flatFibreHomeomorph hq b).symm f) := rfl

/-- In the actual initial marking, this is the unchanged coordinate `f`
at every time, simultaneously for every point of the marked torus. -/
theorem boundaryTransportHomotopy_flat (b : B) {y : D.BaseSpace}
    (γ : Path (D.baseQuotient b) y) (t : unitInterval) (f : RealTorus₄) :
    D.boundaryTransportHomotopy hq b γ (t, D.flatFibreHomeomorph hq b f) =
      D.quotient (hq.isCoveringMap.liftPath γ b γ.source t, f) := by
  rw [D.boundaryTransportHomotopy_apply, Homeomorph.symm_apply_apply]

/-- Every actual base path admits this genuine whole-fibre homotopy;
the required initial lift exists by surjectivity of the actual quotient. -/
theorem boundaryFibreInclusion_homotopic_pathTransport {x y : D.BaseSpace}
    (γ : Path x y) :
    (D.boundaryFibreInclusion x).Homotopic
      ((D.boundaryFibreInclusion y).comp
        (D.pathTransport hq γ : C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y}))) := by
  obtain ⟨b, rfl⟩ := D.baseQuotient_surjective x
  exact ⟨D.boundaryTransportHomotopy hq b γ⟩

/-- Transport followed by the actual final fibre inclusion induces the
actual initial inclusion on integral singular homology in every degree. -/
theorem boundaryFibreInclusion_homology_pathTransport {x y : D.BaseSpace}
    (γ : Path x y) (n : ℕ) :
    (singularHomologyMap (D.boundaryFibreInclusion y) n).comp
        (singularHomologyMap (D.pathTransport hq γ :
          C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y})) n) =
      singularHomologyMap (D.boundaryFibreInclusion x) n := by
  rw [← singularHomologyMap_comp]
  exact (homotopic_homologyMap (D.boundaryFibreInclusion_homotopic_pathTransport hq γ) n).symm

/-- The same identity expressed by the already constructed all-degree
homology-transport equivalence of the literal fibres. -/
theorem boundaryFibreInclusion_homologyTransportDegree {x y : D.BaseSpace}
    (γ : Path x y) (n : ℕ) :
    (singularHomologyMap (D.boundaryFibreInclusion y) n).comp
        (D.homologyTransportDegree hq n (Path.Homotopic.Quotient.mk γ)).toLinearMap =
      singularHomologyMap (D.boundaryFibreInclusion x) n :=
  D.boundaryFibreInclusion_homology_pathTransport hq γ n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable (D : Data ℂ TriangleRegularPoint)

/-- The marked real-torus inclusion is the actual complex period-torus
inclusion composed with its original real-period homeomorphism. -/
theorem pointFamilyFibreInclusion_eq_period_comp (z : TriangleRegularPoint) :
    pointFamilyFibreInclusion D z =
      (⟨D.fibreInclusion z, D.fibreInclusion_continuous z⟩ :
        C((D.periods.point z).Torus, D.Space)).comp
          (D.periods.torusHomeomorph z : C(RealTorus₄, (D.periods.point z).Torus)) := by
  apply ContinuousMap.ext
  intro f
  change D.quotient (z, f) =
    D.quotient (z, (D.periods.torusHomeomorph z).symm (D.periods.torusHomeomorph z f))
  rw [Homeomorph.symm_apply_apply]

/-- The actual geometric period-marking square commutes in every degree. -/
theorem pointFamilyFibreInclusion_homology_period (z : TriangleRegularPoint) (n : ℕ) :
    (singularHomologyMap
      (⟨D.fibreInclusion z, D.fibreInclusion_continuous z⟩ :
        C((D.periods.point z).Torus, D.Space)) n).comp
        (singularHomologyMap (D.periods.torusHomeomorph z :
          C(RealTorus₄, (D.periods.point z).Torus)) n) =
      singularHomologyMap (pointFamilyFibreInclusion D z) n := by
  rw [← singularHomologyMap_comp, ← pointFamilyFibreInclusion_eq_period_comp]

/-- At every time, a straight marked lattice loop is literally the loop
of the same original complex period columns in that time's actual fibre. -/
theorem pointFamilyFibreHomotopy_periodLoop {z w : TriangleRegularPoint}
    (γ : Path z w) (t s : unitInterval) (c : Lattice) :
    pointFamilyFibreHomotopy D γ (t, FlatTorus.periodLoop c s) =
      D.fibreInclusion (γ t) ((D.periods.point (γ t)).periodLoop c s) := by
  have he : D.periods.torusHomeomorph (γ t) (FlatTorus.periodLoop c s) =
      (D.periods.point (γ t)).periodLoop c s := by
    rw [FlatTorus.periodLoop_apply, D.torusHomeomorph_mkQ,
      PeriodDomain.periodLoop_apply, map_smul, D.periodEquiv_realCast]
  rw [← he]
  change D.quotient (γ t, FlatTorus.periodLoop c s) =
    D.quotient (γ t, (D.periods.torusHomeomorph (γ t)).symm
      (D.periods.torusHomeomorph (γ t) (FlatTorus.periodLoop c s)))
  rw [Homeomorph.symm_apply_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
