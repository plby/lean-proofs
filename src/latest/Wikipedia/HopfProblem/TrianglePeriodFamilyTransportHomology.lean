import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMaps
import Wikipedia.HopfProblem.CuspFirstHomologyTopology

/-!
# Actual singular-homology transport in the triangle period family

The fibre homeomorphisms induce linear equivalences on the literal singular
first homology groups. Their identity and composition laws come from the
singular chain functor. Loop transport therefore defines a representation
on the actual fibre homology before any choice of lattice coordinates.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem

namespace FirstHurewicz

@[simp] theorem homeomorphHomologyEquiv_refl (X : Type) [TopologicalSpace X] :
    homeomorphHomologyEquiv (Homeomorph.refl X) = LinearEquiv.refl ℤ (SingularH1 X) := by
  have he : (Homeomorph.refl X : C(X, X)) = ContinuousMap.id X := rfl
  ext h
  change inducedHomology (Homeomorph.refl X : C(X, X)) h = h
  rw [he, inducedHomology_id]
  rfl

@[simp] theorem homeomorphHomologyEquiv_trans {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) :
    homeomorphHomologyEquiv (e.trans f) =
      (homeomorphHomologyEquiv e).trans (homeomorphHomologyEquiv f) := by
  have he : (e.trans f : C(X, Z)) = (f : C(Y, Z)).comp (e : C(X, Y)) := rfl
  ext h
  change inducedHomology (e.trans f : C(X, Z)) h =
    inducedHomology (f : C(Y, Z)) (inducedHomology (e : C(X, Y)) h)
  rw [he, inducedHomology_comp]
  rfl

end FirstHurewicz

namespace TrianglePeriodFamily.Data

open SpecialPeriods FirstHurewicz

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)
    {x y z : D.BaseSpace}

/-- The actual singular-homology equivalence induced by fibre transport. -/
def homologyTransport (γ : Path.Homotopic.Quotient x y) :
    SingularH1 (D.projection ⁻¹' {x}) ≃ₗ[ℤ] SingularH1 (D.projection ⁻¹' {y}) :=
  homeomorphHomologyEquiv (D.transport hq γ)

@[simp] theorem homologyTransport_toLinearMap (γ : Path.Homotopic.Quotient x y) :
    (D.homologyTransport hq γ).toLinearMap =
      inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y})) := rfl

@[simp] theorem homologyTransport_apply (γ : Path.Homotopic.Quotient x y)
    (a : SingularH1 (D.projection ⁻¹' {x})) :
    D.homologyTransport hq γ a =
      inducedHomology (D.transport hq γ : C(D.projection ⁻¹' {x}, D.projection ⁻¹' {y})) a := rfl

@[simp] theorem homologyTransport_symm_apply (γ : Path.Homotopic.Quotient x y)
    (a : SingularH1 (D.projection ⁻¹' {y})) :
    (D.homologyTransport hq γ).symm a =
      inducedHomology
        ((D.transport hq γ).symm : C(D.projection ⁻¹' {y}, D.projection ⁻¹' {x})) a := rfl

@[simp] theorem homologyTransport_refl (x : D.BaseSpace) :
    D.homologyTransport hq (Path.Homotopic.Quotient.refl x) =
      LinearEquiv.refl ℤ (SingularH1 (D.projection ⁻¹' {x})) := by
  simp only [homologyTransport, D.transport_refl, homeomorphHomologyEquiv_refl]

/-- Actual homology transport follows path concatenation in its geometric order. -/
theorem homologyTransport_trans (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) :
    D.homologyTransport hq (γ.trans δ) =
      (D.homologyTransport hq γ).trans (D.homologyTransport hq δ) := by
  simp only [homologyTransport, D.transport_trans, homeomorphHomologyEquiv_trans]

@[simp] theorem homologyTransport_trans_apply (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) (a : SingularH1 (D.projection ⁻¹' {x})) :
    D.homologyTransport hq (γ.trans δ) a =
      D.homologyTransport hq δ (D.homologyTransport hq γ a) := by
  rw [D.homologyTransport_trans, LinearEquiv.trans_apply]

@[simp] theorem homologyTransport_symm (γ : Path.Homotopic.Quotient x y) :
    D.homologyTransport hq γ.symm = (D.homologyTransport hq γ).symm := by
  simp only [homologyTransport, D.transport_symm, homeomorphHomologyEquiv_symm]

theorem homologyTransport_homotopy {γ δ : Path x y} (h : γ.Homotopic δ) :
    D.homologyTransport hq (Path.Homotopic.Quotient.mk γ) =
      D.homologyTransport hq (Path.Homotopic.Quotient.mk δ) :=
  congrArg (D.homologyTransport hq) (Path.Homotopic.Quotient.eq.mpr h)

theorem homologyTransport_eq_of_lift_endpoint_eq {γ δ : Path.Homotopic.Quotient x y}
    (b : D.baseQuotient ⁻¹' {x})
    (he : hq.isCoveringMap.monodromy γ b = hq.isCoveringMap.monodromy δ b) :
    D.homologyTransport hq γ = D.homologyTransport hq δ :=
  congrArg homeomorphHomologyEquiv (D.transport_eq_of_lift_endpoint_eq hq b he)

/-- Loop transport acts on the actual first homology of the family fibre.
Fundamental-group multiplication is reversed path concatenation, matching
the composition convention for linear automorphisms. -/
def homologyMonodromyHom (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →*
      (SingularH1 (D.projection ⁻¹' {D.baseQuotient b}) ≃ₗ[ℤ]
        SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) where
  toFun γ := D.homologyTransport hq γ
  map_one' := by
    rw [FundamentalGroup.one_def, D.homologyTransport_refl]
    rfl
  map_mul' γ δ := by
    rw [FundamentalGroup.mul_def, D.homologyTransport_trans]
    rfl

@[simp] theorem homologyMonodromyHom_apply (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.homologyMonodromyHom hq b γ = D.homologyTransport hq γ := rfl

@[simp] theorem homologyMonodromyHom_toLinearMap (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.homologyMonodromyHom hq b γ).toLinearMap = inducedHomology
      (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) := rfl

@[simp] theorem homologyMonodromyHom_apply_class (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularH1 (D.projection ⁻¹' {D.baseQuotient b})) :
    D.homologyMonodromyHom hq b γ a = inducedHomology
      (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) a := rfl

end TrianglePeriodFamily.Data

end Wikipedia.HopfProblem
