import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafRawNaturality
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalComplex
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExact

/-!
# Actual global-cochain naturality under continuous maps

The native sheaf pullback maps assemble to a map of the original sheaf
cochain complexes into the genuine pushed-forward complex. Evaluation
on the top open gives the original map of global-section complexes:
the actual preimage of the top open is definitionally top.

On an original global singular cochain this map is exactly its original
singular pullback followed by the native comparison unit. Thus the
original global-complex comparison is natural for every continuous map,
without an exactness or geometric hypothesis on that map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})

/-- The original cochain sheaf complex, pushed forward by the actual
topological sheaf functor. -/
abbrev pushforwardCochainComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).obj
    (cochainSheafComplex X A)

/-- The original degreewise maps form a genuine map of sheaf cochain
complexes, since they commute with the original differentials. -/
def cochainPullbackComplex : cochainSheafComplex Y A ⟶ pushforwardCochainComplex f A where
  f n := cochainPullback f A n
  comm' i j _ := cochainPullback_d f A i j

@[simp]
theorem cochainPullbackComplex_f (n : ℕ) :
    (cochainPullbackComplex f A).f n = cochainPullback f A n := rfl

/-- Evaluation of the native pullback on the actual top open gives
the corresponding morphism of original global-section complexes. -/
def globalSheafPullback : globalSheafCochainComplex Y A ⟶ globalSheafCochainComplex X A where
  f n := (cochainPullback f A n).hom.app (op ⊤)
  comm' i j _ :=
    NatTrans.congr_app
      (congrArg (fun θ : cochainSheaf Y A i ⟶
          (TopCat.Sheaf.pushforward AddCommGrpCat f).obj (cochainSheaf X A j) => θ.hom)
        (cochainPullback_d f A i j)) (op ⊤)

/-- Its degreewise map is the literal top-open component, not a
separately chosen map of abstract cohomology groups. -/
@[simp]
theorem globalSheafPullback_f (n : ℕ) :
    (globalSheafPullback f A).f n = (cochainPullback f A n).hom.app (op ⊤) := rfl

/-- The original global unit sends genuine singular pullback to
genuine sheaf pullback on the original global section groups. -/
theorem globalCochainUnit_pullback (n : ℕ) (φ : Cochains Y A n) :
    (globalSheafPullback f A).f n (globalCochainUnit Y A n φ) =
      globalCochainUnit X A n ((singularPullback A f.hom).f n φ) := by
  change (cochainPullback f A n).hom.app (op ⊤)
      ((cochainSheafUnit Y A n).app (op ⊤) (restrictGlobalCochain A n φ ⊤)) =
    (cochainSheafUnit X A n).app (op ⊤)
      (restrictGlobalCochain A n ((singularPullback A f.hom).f n φ) ⊤)
  rw [cochainPullback_app_unit, rawPullback_restrictGlobal_top]
  rfl

/-- The full original singular-to-global-sheaf cochain comparison
commutes with every continuous map. -/
theorem globalCochainComparison_naturality :
    singularPullback A f.hom ≫ globalCochainComparison X A =
      globalCochainComparison Y A ≫ globalSheafPullback f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  exact (globalCochainUnit_pullback f A n φ).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
