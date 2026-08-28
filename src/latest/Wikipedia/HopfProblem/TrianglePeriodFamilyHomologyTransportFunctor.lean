import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMonodromy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual singular-homology transport in every degree

The actual fibre-transport homeomorphisms induce equivalences between the
literal singular homology groups. Identity, composition, inverse, and
homotopy invariance follow from the actual singular-homology functor.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)
  (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)
  {x y z : D.BaseSpace}

/-- Transport on the actual singular-homology module, in an arbitrary degree. -/
def homologyTransportDegree (n : ℕ) (γ : Path.Homotopic.Quotient x y) :
    SingularHomology (D.projection ⁻¹' {x}) n ≃ₗ[ℤ]
      SingularHomology (D.projection ⁻¹' {y}) n :=
  homeomorphHomologyEquiv (D.transport hq γ) n

@[simp] theorem homologyTransportDegree_toLinearMap (n : ℕ)
    (γ : Path.Homotopic.Quotient x y) :
    (D.homologyTransportDegree hq n γ).toLinearMap =
      singularHomologyMap
        (D.transport hq γ : C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y})) n := rfl

@[simp] theorem homologyTransportDegree_apply (n : ℕ)
    (γ : Path.Homotopic.Quotient x y) (a : SingularHomology (D.projection ⁻¹' {x}) n) :
    D.homologyTransportDegree hq n γ a = singularHomologyMap
      (D.transport hq γ : C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y})) n a := rfl

@[simp] theorem homologyTransportDegree_refl (n : ℕ) (x : D.BaseSpace) :
    D.homologyTransportDegree hq n (Path.Homotopic.Quotient.refl x) =
      LinearEquiv.refl ℤ (SingularHomology (D.projection ⁻¹' {x}) n) := by
  simp only [homologyTransportDegree, D.transport_refl, homeomorphHomologyEquiv_refl]

theorem homologyTransportDegree_trans (n : ℕ) (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) :
    D.homologyTransportDegree hq n (γ.trans δ) =
      (D.homologyTransportDegree hq n γ).trans (D.homologyTransportDegree hq n δ) := by
  simp only [homologyTransportDegree, D.transport_trans, homeomorphHomologyEquiv_trans]

@[simp] theorem homologyTransportDegree_trans_apply (n : ℕ)
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z)
    (a : SingularHomology (D.projection ⁻¹' {x}) n) :
    D.homologyTransportDegree hq n (γ.trans δ) a =
      D.homologyTransportDegree hq n δ (D.homologyTransportDegree hq n γ a) := by
  rw [D.homologyTransportDegree_trans, LinearEquiv.trans_apply]

@[simp] theorem homologyTransportDegree_symm (n : ℕ) (γ : Path.Homotopic.Quotient x y) :
    D.homologyTransportDegree hq n γ.symm = (D.homologyTransportDegree hq n γ).symm := by
  simp only [homologyTransportDegree, D.transport_symm, homeomorphHomologyEquiv_symm]

theorem homologyTransportDegree_homotopy (n : ℕ) {γ δ : Path x y} (h : γ.Homotopic δ) :
    D.homologyTransportDegree hq n (Path.Homotopic.Quotient.mk γ) =
      D.homologyTransportDegree hq n (Path.Homotopic.Quotient.mk δ) :=
  congrArg (D.homologyTransportDegree hq n) (Path.Homotopic.Quotient.eq.mpr h)

theorem homologyTransportDegree_eq_of_lift_endpoint_eq (n : ℕ)
    {γ δ : Path.Homotopic.Quotient x y} (b : D.baseQuotient ⁻¹' {x})
    (he : hq.isCoveringMap.monodromy γ b = hq.isCoveringMap.monodromy δ b) :
    D.homologyTransportDegree hq n γ = D.homologyTransportDegree hq n δ :=
  congrArg (fun e => homeomorphHomologyEquiv e n)
    (D.transport_eq_of_lift_endpoint_eq hq b he)

/-- The actual loop-transport representation on the literal homology of a family fibre. -/
def homologyMonodromyDegreeHom (n : ℕ) (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →*
      (SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) n ≃ₗ[ℤ]
        SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) n) where
  toFun γ := D.homologyTransportDegree hq n γ
  map_one' := by
    rw [FundamentalGroup.one_def, D.homologyTransportDegree_refl]
    rfl
  map_mul' γ δ := by
    rw [FundamentalGroup.mul_def, D.homologyTransportDegree_trans]
    rfl

@[simp] theorem homologyMonodromyDegreeHom_apply (n : ℕ) (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.homologyMonodromyDegreeHom hq n b γ = D.homologyTransportDegree hq n γ := rfl

/-- The actual flat-coordinate square commutes on singular homology in every degree. -/
theorem transport_inducedHomologyDegree_flat (n : ℕ) (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) n
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) n a) =
      singularHomologyMap (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) n
          (singularHomologyMap (triangleTorusHomeomorph (D.deckTransportHom hq b γ) :
            C(RealTorus₄, RealTorus₄)) n a) := by
  have he := congrArg (fun f => singularHomologyMap f n) (D.transport_flat_commutes hq b γ)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at he
  exact LinearMap.congr_fun he a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
