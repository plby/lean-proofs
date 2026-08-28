import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainSingular
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular

/-!
# The integral instance of additive singular cochains

Additive cochains with coefficients in `ℤ` agree with the existing native
integer-linear singular cochains.  The comparison keeps every cochain's
values on the original chains, intertwines the actual differentials, and
is natural for the original continuous-map pullbacks.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

/-- Forget only the integer-module structure of an integral cochain complex. -/
abbrev forgetIntegralCochains :
    CochainComplex (ModuleCat.{0} ℤ) ℕ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The coefficient-`ℤ` complex is the existing native integral cochain
complex with its scalar structure forgotten. -/
def integralCochainIso (X : Type) [TopologicalSpace X] :
    singularCochainComplex X (AddCommGrpCat.of ℤ) ≅
      forgetIntegralCochains.obj (SingularCohomologyFree.singularCochainComplex X) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (intLinearAddHomEquiv (Chains X n) ℤ).symm.toAddCommGrpIso) ?_
  intro i j _
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

/-- The forward comparison gives an additive cochain its unique compatible
integer-linear structure, for the native chain-module structure. -/
@[simp]
theorem integralCochainIso_hom_f (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : Cochains X (AddCommGrpCat.of ℤ) n) :
    (integralCochainIso X).hom.f n φ = addHomToIntLinearMap φ := rfl

/-- Every value on an original singular chain is unchanged. -/
@[simp]
theorem integralCochainIso_hom_f_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : Cochains X (AddCommGrpCat.of ℤ) n) (c : Chains X n) :
    DFunLike.coe (F := Chains X n →ₗ[ℤ] ℤ) ((integralCochainIso X).hom.f n φ) c =
      φ c := rfl

/-- The reverse comparison forgets only the scalar-compatibility proof. -/
@[simp]
theorem integralCochainIso_inv_f (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : Chains X n →ₗ[ℤ] ℤ) :
    (integralCochainIso X).inv.f n φ = φ.toAddMonoidHom := rfl

@[simp]
theorem integralCochainIso_inv_f_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (φ : Chains X n →ₗ[ℤ] ℤ) (c : Chains X n) :
    (integralCochainIso X).inv.f n φ c = φ c := rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The comparison intertwines the original continuous-map pullbacks as
an equality of maps of the actual cochain complexes. -/
theorem integralCochainIso_naturality (f : C(X, Y)) :
    singularPullback (AddCommGrpCat.of ℤ) f ≫ (integralCochainIso X).hom =
      (integralCochainIso Y).hom ≫
        forgetIntegralCochains.map (SingularCohomologyFree.singularPullback f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  apply LinearMap.ext
  intro c
  rfl

/-- The inverse comparison is natural for the same native pullbacks. -/
theorem integralCochainIso_inv_naturality (f : C(X, Y)) :
    forgetIntegralCochains.map (SingularCohomologyFree.singularPullback f) ≫
        (integralCochainIso X).inv =
      (integralCochainIso Y).inv ≫ singularPullback (AddCommGrpCat.of ℤ) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  ext φ c
  rfl

/-- Under the comparison, pullback still evaluates the original cochain
on the original induced singular chain. -/
@[simp]
theorem integralCochainIso_pullback_apply (f : C(X, Y)) (n : ℕ)
    (φ : Cochains Y (AddCommGrpCat.of ℤ) n) (c : Chains X n) :
    DFunLike.coe (F := Chains X n →ₗ[ℤ] ℤ) ((integralCochainIso X).hom.f n
        ((singularPullback (AddCommGrpCat.of ℤ) f).f n φ)) c =
      φ (inducedChain f n c) := rfl

@[simp]
theorem integralCochainIso_pullback_simplex (f : C(X, Y)) (n : ℕ)
    (φ : Cochains Y (AddCommGrpCat.of ℤ) n) (σ : SingularSimplex X n) :
    DFunLike.coe (F := Chains X n →ₗ[ℤ] ℤ) ((integralCochainIso X).hom.f n
        ((singularPullback (AddCommGrpCat.of ℤ) f).f n φ)) (simplexChain X n σ) =
      φ (simplexChain Y n (f.comp σ)) := by
  rw [integralCochainIso_pullback_apply, inducedChain_simplex]

/-- The integral comparison is an isomorphism of the native contravariant
singular cochain functors. -/
def integralCochainNatIso :
    singularCochainFunctor (AddCommGrpCat.of ℤ) ≅
      SingularCohomologyFree.singularCochainFunctor ⋙ forgetIntegralCochains :=
  NatIso.ofComponents (fun X => integralCochainIso X.unop)
    (fun f => integralCochainIso_naturality f.unop.hom)

@[simp]
theorem integralCochainNatIso_app (X : Type) [TopologicalSpace X] :
    integralCochainNatIso.app (op (TopCat.of X)) = integralCochainIso X := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
