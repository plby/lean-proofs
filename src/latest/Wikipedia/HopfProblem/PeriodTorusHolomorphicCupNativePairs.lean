import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairExact
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationNative

/-!
# The original native coefficient pairs in the cup diagram

The native Dolbeault pair sheaf and the generic pair construction have
the same actual coefficients. Their comparison is identity on values;
the original two derivatives and top differential are retained.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

/-- Identity on the original native pair coefficients. -/
def nativePairIso (p : PeriodDomain) :
    Dolbeault.pairSheaf p ≅ Pairs.sheaf (Dolbeault.smoothSheaf p) where
  hom := ⟨{ app _ := 𝟙 _, naturality _ _ _ := rfl }⟩
  inv := ⟨{ app _ := 𝟙 _, naturality _ _ _ := rfl }⟩
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    rfl

@[simp] theorem nativePairIso_hom_app (p : PeriodDomain) (U : Opens p.Torus)
    (s : Dolbeault.PairSection p U) : (nativePairIso p).hom.hom.app (op U) s = s := rfl

@[simp] theorem nativePairIso_inv_app (p : PeriodDomain) (U : Opens p.Torus)
    (s : Dolbeault.PairSection p U) : (nativePairIso p).inv.hom.app (op U) s = s := rfl

/-- The first actual coefficient of the original native differential. -/
@[reassoc] theorem differential_nativePair_fst (p : PeriodDomain) :
    Dolbeault.differential p ≫ (nativePairIso p).hom ≫
        Pairs.fst (Dolbeault.smoothSheaf p) = Derivation.derivativeMap p 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- The second actual coefficient of the original native differential. -/
@[reassoc] theorem differential_nativePair_snd (p : PeriodDomain) :
    Dolbeault.differential p ≫ (nativePairIso p).hom ≫
        Pairs.snd (Dolbeault.smoothSheaf p) = Derivation.derivativeMap p 1 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

/-- The actual top differential keeps its original coordinate order and sign. -/
theorem nativePair_topDifferential (p : PeriodDomain) :
    (nativePairIso p).inv ≫ Dolbeault.topDifferential p =
      Pairs.snd (Dolbeault.smoothSheaf p) ≫ Derivation.derivativeMap p 0 -
        Pairs.fst (Dolbeault.smoothSheaf p) ≫ Derivation.derivativeMap p 1 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
