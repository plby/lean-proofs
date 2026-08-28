import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRepresentation
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTorus

/-!
# Fundamental-group maps in the actual varying-period family

The flat-torus covering fixes the ordered integral period marking.
The inclusion of these actual fibre loops, the actual family projection,
and the actual zero section give the three pointed group homomorphisms
used in the split-extension calculation.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The actual zero of the fibre represented above the chosen base lift. -/
def fundamentalGroupBasepoint (b : B) : D.Space := D.quotient (b, 0)

@[simp] theorem zeroSection_fundamentalGroupBasepoint (b : B) :
    D.zeroSection (D.baseQuotient b) = D.fundamentalGroupBasepoint b := rfl

/-- The actual flat coordinate torus includes into the descended period family. -/
def flatFibreFundamentalGroupHom (b : B) :
    FundamentalGroup RealTorus₄ 0 →*
      FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  FundamentalGroup.map
    ⟨fun x : RealTorus₄ => D.quotient (b, x),
      D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩ 0

/-- Include genuine fibre loops with the source's ordered integral column marking. -/
def latticeFundamentalGroupHom (b : B) :
    Multiplicative Lattice →* FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  (D.flatFibreFundamentalGroupHom b).comp FlatTorus.fundamentalGroupEquiv.symm.toMonoidHom

/-- The pointed homomorphism of the actual proper family projection. -/
def projectionFundamentalGroupHom (b : B) :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) →*
      FundamentalGroup D.BaseSpace (D.baseQuotient b) :=
  FundamentalGroup.map ⟨D.projection, D.projection_continuous⟩ (D.fundamentalGroupBasepoint b)

/-- The pointed homomorphism of the already constructed zero section. -/
def sectionFundamentalGroupHom (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →*
      FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  FundamentalGroup.map ⟨D.zeroSection, D.zeroSection_continuous⟩ (D.baseQuotient b)

@[simp] theorem flatFibreFundamentalGroupHom_eq_diagonal (b : B) :
    D.flatFibreFundamentalGroupHom b =
      DiagonalQuotient.fibreFundamentalGroupHom (G := TriangleGroup) b (0 : RealTorus₄) := rfl

@[simp] theorem projectionFundamentalGroupHom_eq_diagonal (b : B) :
    D.projectionFundamentalGroupHom b =
      DiagonalQuotient.projectionFundamentalGroupHom (G := TriangleGroup) b (0 : RealTorus₄) := rfl

@[simp] theorem sectionFundamentalGroupHom_eq_diagonal (b : B) :
    D.sectionFundamentalGroupHom b =
      DiagonalQuotient.sectionFundamentalGroupHom (0 : RealTorus₄)
        triangleTorusAction_zero b := rfl

/-- The induced section splits the actual projection. -/
theorem projectionFundamentalGroupHom_comp_section (b : B) :
    (D.projectionFundamentalGroupHom b).comp (D.sectionFundamentalGroupHom b) =
      MonoidHom.id (FundamentalGroup D.BaseSpace (D.baseQuotient b)) :=
  DiagonalQuotient.projectionFundamentalGroupHom_comp_section
    (0 : RealTorus₄) triangleTorusAction_zero b

theorem projectionFundamentalGroupHom_surjective (b : B) :
    Function.Surjective (D.projectionFundamentalGroupHom b) :=
  DiagonalQuotient.projectionFundamentalGroupHom_surjective
    (0 : RealTorus₄) triangleTorusAction_zero b

theorem sectionFundamentalGroupHom_injective (b : B) :
    Function.Injective (D.sectionFundamentalGroupHom b) :=
  DiagonalQuotient.sectionFundamentalGroupHom_injective
    (0 : RealTorus₄) triangleTorusAction_zero b

@[simp] theorem projectionFundamentalGroupHom_lattice (b : B) (v : Multiplicative Lattice) :
    D.projectionFundamentalGroupHom b (D.latticeFundamentalGroupHom b v) = 1 :=
  DiagonalQuotient.projectionFundamentalGroupHom_fibre b (0 : RealTorus₄)
    (FlatTorus.fundamentalGroupEquiv.symm v)

/-- The lattice generator is the actual straight period loop followed by
the genuine family inclusion. -/
theorem latticeFundamentalGroupHom_periodLoop (b : B) (v : Lattice) :
    D.latticeFundamentalGroupHom b (Multiplicative.ofAdd v) =
      D.flatFibreFundamentalGroupHom b
        (Path.Homotopic.Quotient.mk (FlatTorus.periodLoop v)) := by
  change D.flatFibreFundamentalGroupHom b
    (FlatTorus.fundamentalGroupEquiv.symm (Multiplicative.ofAdd v)) = _
  rw [FlatTorus.fundamentalGroupEquiv_symm_apply]
  rfl

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

@[simp] theorem deckTransportHom_eq_diagonal (b : B) :
    D.deckTransportHom hq b = DiagonalQuotient.deckTransportHom hq b := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
