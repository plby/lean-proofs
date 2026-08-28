import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportMarking

/-!
# Agreement with the actual normalized period-torus markings

The family's real-period homeomorphism has exactly the same period columns as
the canonical period-torus coordinate map. Its circle-coordinate comparison is
therefore literal, and actual singular functoriality identifies both higher
homology markings. The marking of the literal descended fibre consequently
agrees with the canonical marking under its actual period-torus homeomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)

/-- The actual family-period homeomorphism agrees with the canonical projection on
every real covering-space representative. -/
theorem torusHomeomorph_mkQ_eq_flatProjection (b : B) (x : RealPlane₄) :
    D.periods.torusHomeomorph b (standardLattice.mkQ x) =
      flatProjection (D.periods.point b) x := by
  rw [D.torusHomeomorph_mkQ]
  exact congrArg (D.periods.point b).lattice.mkQ
    ((D.periodEquiv_matrix b x).trans (Elliptic.periodEquiv_matrix (D.periods.point b) x).symm)

/-- The two actual circle-coordinate maps agree pointwise, without a base-covering hypothesis. -/
theorem periodTorusCircleHomeomorph_torusHomeomorph (b : B) (x : RealTorus₄) :
    periodTorusCircleHomeomorph (D.periods.point b) (D.periods.torusHomeomorph b x) =
      flatTorusCircleHomeomorph x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [D.torusHomeomorph_mkQ_eq_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, flatTorusCircleHomeomorph_mkQ]

/-- The same equality as an identity of actual continuous maps. -/
theorem periodTorusCircleHomeomorph_torusHomeomorph_comp (b : B) :
    (periodTorusCircleHomeomorph (D.periods.point b) :
      C((D.periods.point b).Torus, ProductTorus 4)).comp
        (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus)) =
      (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) := by
  apply ContinuousMap.ext
  intro x
  exact D.periodTorusCircleHomeomorph_torusHomeomorph b x

/-- The geometric identity gives the same induced singular-homology map in every degree. -/
theorem singularHomology_circle_torusHomeomorph (b : B) (n : ℕ) :
    (singularHomologyMap (periodTorusCircleHomeomorph (D.periods.point b) :
      C((D.periods.point b).Torus, ProductTorus 4)) n).comp
        (singularHomologyMap (D.periods.torusHomeomorph b :
          C(RealTorus₄, (D.periods.point b).Torus)) n) =
      singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n := by
  rw [← singularHomologyMap_comp, D.periodTorusCircleHomeomorph_torusHomeomorph_comp]

/-- The actual real-period homeomorphism preserves the canonical exterior-square marking. -/
theorem singularH2Equiv_inducedHomology_torusHomeomorph (b : B)
    (a : SingularHomology RealTorus₄ 2) :
    periodTorusH2ExteriorEquiv (D.periods.point b)
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 2 a) =
      FlatTorus.singularH2Equiv a := by
  calc
    _ = coordinateTorusH2ExteriorEquiv
        (singularHomologyMap (periodTorusCircleHomeomorph (D.periods.point b) :
          C((D.periods.point b).Torus, ProductTorus 4)) 2
          (singularHomologyMap (D.periods.torusHomeomorph b :
            C(RealTorus₄, (D.periods.point b).Torus)) 2 a)) :=
      (coordinateTorusH2ExteriorEquiv_periodCoordinates (D.periods.point b) _).symm
    _ = coordinateTorusH2ExteriorEquiv
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 2 a) :=
      congrArg coordinateTorusH2ExteriorEquiv
        (LinearMap.congr_fun (D.singularHomology_circle_torusHomeomorph b 2) a)
    _ = _ := rfl

/-- The actual real-period homeomorphism preserves the canonical exterior-cube marking. -/
theorem singularH3Equiv_inducedHomology_torusHomeomorph (b : B)
    (a : SingularHomology RealTorus₄ 3) :
    periodTorusH3ExteriorEquiv (D.periods.point b)
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 3 a) =
      FlatTorus.singularH3Equiv a := by
  calc
    _ = coordinateTorusH3ExteriorEquiv
        (singularHomologyMap (periodTorusCircleHomeomorph (D.periods.point b) :
          C((D.periods.point b).Torus, ProductTorus 4)) 3
          (singularHomologyMap (D.periods.torusHomeomorph b :
            C(RealTorus₄, (D.periods.point b).Torus)) 3 a)) :=
      (coordinateTorusH3ExteriorEquiv_periodCoordinates (D.periods.point b) _).symm
    _ = coordinateTorusH3ExteriorEquiv
        (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) 3 a) :=
      congrArg coordinateTorusH3ExteriorEquiv
        (LinearMap.congr_fun (D.singularHomology_circle_torusHomeomorph b 3) a)
    _ = _ := rfl

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- The literal descended fibre has the canonical period-torus second-homology marking. -/
theorem fibreSingularH2Equiv_inducedHomology_period (b : B)
    (a : SingularHomology (D.periods.point b).Torus 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      periodTorusH2ExteriorEquiv (D.periods.point b) a := by
  obtain ⟨x, rfl⟩ :=
    (homeomorphHomologyEquiv (D.periods.torusHomeomorph b) 2).surjective a
  change D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 2
        (singularHomologyMap (D.periods.torusHomeomorph b :
          C(RealTorus₄, (D.periods.point b).Torus)) 2 x)) =
    periodTorusH2ExteriorEquiv (D.periods.point b)
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 2 x)
  have hc : singularHomologyMap (D.flatFibreHomeomorph hq b :
      C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 x =
    singularHomologyMap (D.fibreHomeomorph hq b :
      C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 2
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 2 x) :=
    LinearMap.congr_fun (singularHomologyMap_comp
      (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus))
      (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 2) x
  rw [← hc, D.fibreSingularH2Equiv_inducedHomology_flat,
    D.singularH2Equiv_inducedHomology_torusHomeomorph]

/-- The literal descended fibre has the canonical period-torus third-homology marking. -/
theorem fibreSingularH3Equiv_inducedHomology_period (b : B)
    (a : SingularHomology (D.periods.point b).Torus 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      periodTorusH3ExteriorEquiv (D.periods.point b) a := by
  obtain ⟨x, rfl⟩ :=
    (homeomorphHomologyEquiv (D.periods.torusHomeomorph b) 3).surjective a
  change D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 3
        (singularHomologyMap (D.periods.torusHomeomorph b :
          C(RealTorus₄, (D.periods.point b).Torus)) 3 x)) =
    periodTorusH3ExteriorEquiv (D.periods.point b)
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 3 x)
  have hc : singularHomologyMap (D.flatFibreHomeomorph hq b :
      C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 x =
    singularHomologyMap (D.fibreHomeomorph hq b :
      C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 3
      (singularHomologyMap (D.periods.torusHomeomorph b :
        C(RealTorus₄, (D.periods.point b).Torus)) 3 x) :=
    LinearMap.congr_fun (singularHomologyMap_comp
      (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus))
      (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) 3) x
  rw [← hc, D.fibreSingularH3Equiv_inducedHomology_flat,
    D.singularH3Equiv_inducedHomology_torusHomeomorph]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
