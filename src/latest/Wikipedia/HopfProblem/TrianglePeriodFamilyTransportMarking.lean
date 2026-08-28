import Wikipedia.HopfProblem.TrianglePeriodFamilyFibres
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTorus
import Wikipedia.HopfProblem.CuspFirstHomologyTopology

/-!
# The column marking on actual descended triangle-family fibres

The flat coordinate torus identifies homeomorphically with the actual
fibre of the descended family. Its genuine integral singular-homology
marking transfers through the induced singular-homology equivalence.
Straight loops in the real coordinates map to the actual complex period
loops, so this marking agrees with the original period-column marking.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open FirstHurewicz SpecialPeriods

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

@[simp] theorem torusHomeomorph_mkQ (b : B) (x : RealPlane₄) :
    D.periods.torusHomeomorph b (standardLattice.mkQ x) =
      (D.periods.point b).lattice.mkQ (D.periods.periodEquiv b x) := rfl

@[simp] theorem torusHomeomorph_zero (b : B) :
    D.periods.torusHomeomorph b 0 = 0 := by
  simpa only [map_zero] using D.torusHomeomorph_mkQ b 0

/-- Integral real coordinates give exactly the original complex period
columns, with no change of order, signs, or normalization. -/
theorem periodEquiv_realCast (b : B) (c : Lattice) :
    D.periods.periodEquiv b (Elliptic.realCast c) =
      (D.periods.point b).periodVector c := by
  rw [D.periodEquiv_matrix, PeriodDomain.periodVector_apply]
  simp only [Elliptic.realCast, Complex.ofReal_intCast]

/-- The actual real-period homeomorphism carries straight flat period
loops to straight loops of the actual complex period columns. -/
theorem periodLoop_map_torusHomeomorph (b : B) (c : Lattice) :
    (FlatTorus.periodLoop c).map (D.periods.torusHomeomorph b).continuous =
      ((D.periods.point b).periodLoop c).cast
        (D.torusHomeomorph_zero b) (D.torusHomeomorph_zero b) := by
  ext t
  change D.periods.torusHomeomorph b (FlatTorus.periodLoop c t) =
    (D.periods.point b).periodLoop c t
  rw [FlatTorus.periodLoop_apply, D.torusHomeomorph_mkQ,
    PeriodDomain.periodLoop_apply, map_smul, D.periodEquiv_realCast]

theorem inducedHomology_periodLoop_torusHomeomorph (b : B) (c : Lattice) :
    inducedHomology (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus))
      (loopHomologyClass (FlatTorus.periodLoop c)) =
        loopHomologyClass ((D.periods.point b).periodLoop c) := by
  rw [inducedHomology_loopHomologyClass, D.periodLoop_map_torusHomeomorph]
  rfl

/-- The flat and complex-period column markings agree on the actual
induced integral singular-homology map. -/
theorem singularH1Equiv_inducedHomology_torusHomeomorph (b : B)
    (a : SingularH1 RealTorus₄) :
    (D.periods.point b).singularH1Equiv
      (inducedHomology (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus)) a) =
        FlatTorus.singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := FlatTorus.singularH1Equiv.symm.surjective a
  rw [FlatTorus.singularH1Equiv_symm_apply, D.inducedHomology_periodLoop_torusHomeomorph,
    PeriodDomain.singularH1Equiv_periodLoop, FlatTorus.singularH1Equiv_periodLoop]

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- The actual flat coordinate torus parametrizes the genuine descended fibre. -/
def flatFibreHomeomorph (b : B) :
    RealTorus₄ ≃ₜ (D.projection ⁻¹' {D.baseQuotient b}) :=
  (D.periods.torusHomeomorph b).trans (D.fibreHomeomorph hq b)

@[simp] theorem flatFibreHomeomorph_coe (b : B) (x : RealTorus₄) :
    (D.flatFibreHomeomorph hq b x : D.Space) = D.quotient (b, x) := by
  change (D.fibreHomeomorph hq b (D.periods.torusHomeomorph b x) : D.Space) = _
  rw [D.fibreHomeomorph_coe]
  change D.quotient (b, (D.periods.torusHomeomorph b).symm
    (D.periods.torusHomeomorph b x)) = _
  rw [Homeomorph.symm_apply_apply]

/-- The actual fibre's integral singular homology in the geometric flat
coordinate marking, transferred by the genuine singular functor. -/
def fibreSingularH1Equiv (b : B) :
    SingularH1 (D.projection ⁻¹' {D.baseQuotient b}) ≃ₗ[ℤ] Lattice :=
  (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b)).symm.trans FlatTorus.singularH1Equiv

theorem fibreSingularH1Equiv_inducedHomology_flat (b : B) (a : SingularH1 RealTorus₄) :
    D.fibreSingularH1Equiv hq b
      (inducedHomology (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) a) =
      FlatTorus.singularH1Equiv a := by
  change FlatTorus.singularH1Equiv
    ((homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b)).symm
      (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- A straight marked integral loop, mapped to the actual descended fibre. -/
def fibrePeriodLoop (b : B) (c : Lattice) :
    Path (D.flatFibreHomeomorph hq b 0) (D.flatFibreHomeomorph hq b 0) :=
  (FlatTorus.periodLoop c).map (D.flatFibreHomeomorph hq b).continuous

theorem fibrePeriodLoop_coe_apply (b : B) (c : Lattice) (t : unitInterval) :
    (D.fibrePeriodLoop hq b c t : D.Space) =
      D.quotient (b, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast c)) := by
  change (D.flatFibreHomeomorph hq b (FlatTorus.periodLoop c t) : D.Space) = _
  rw [D.flatFibreHomeomorph_coe, FlatTorus.periodLoop_apply]

/-- The genuine singular loop class has exactly its ordered integral coordinate. -/
@[simp] theorem fibreSingularH1Equiv_periodLoop (b : B) (c : Lattice) :
    D.fibreSingularH1Equiv hq b (loopHomologyClass (D.fibrePeriodLoop hq b c)) = c := by
  have hn := inducedHomology_loopHomologyClass
    (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b}))
    0 (FlatTorus.periodLoop c)
  change inducedHomology
    (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b}))
    (loopHomologyClass (FlatTorus.periodLoop c)) =
      loopHomologyClass (D.fibrePeriodLoop hq b c) at hn
  rw [← hn, D.fibreSingularH1Equiv_inducedHomology_flat, FlatTorus.singularH1Equiv_periodLoop]

@[simp] theorem fibreSingularH1Equiv_symm_apply (b : B) (c : Lattice) :
    (D.fibreSingularH1Equiv hq b).symm c = loopHomologyClass (D.fibrePeriodLoop hq b c) := by
  apply (D.fibreSingularH1Equiv hq b).injective
  rw [LinearEquiv.apply_symm_apply, D.fibreSingularH1Equiv_periodLoop]

/-- The marking of the actual descended fibre agrees with the original
complex period-column marking under the actual fibre homeomorphism. -/
theorem fibreSingularH1Equiv_inducedHomology_period (b : B)
    (a : SingularH1 (D.periods.point b).Torus) :
    D.fibreSingularH1Equiv hq b
      (inducedHomology (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})) a) =
      (D.periods.point b).singularH1Equiv a := by
  obtain ⟨x, rfl⟩ := (homeomorphHomologyEquiv (D.periods.torusHomeomorph b)).surjective a
  change D.fibreSingularH1Equiv hq b
    (inducedHomology (D.fibreHomeomorph hq b :
      C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b}))
        (inducedHomology
          (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus)) x)) =
    (D.periods.point b).singularH1Equiv
      (inducedHomology
        (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus)) x)
  have hc := congrArg (fun L => L x)
    (inducedHomology_comp
      (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus))
      (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b})))
  change inducedHomology
    (D.flatFibreHomeomorph hq b : C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) x =
      inducedHomology (D.fibreHomeomorph hq b :
        C((D.periods.point b).Torus, D.projection ⁻¹' {D.baseQuotient b}))
        (inducedHomology
          (D.periods.torusHomeomorph b : C(RealTorus₄, (D.periods.point b).Torus)) x) at hc
  rw [← hc, D.fibreSingularH1Equiv_inducedHomology_flat,
    D.singularH1Equiv_inducedHomology_torusHomeomorph]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
