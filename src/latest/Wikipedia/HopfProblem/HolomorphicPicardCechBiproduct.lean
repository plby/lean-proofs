import Wikipedia.HopfProblem.HolomorphicPicardCechSheafMap
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Pairing actual Čech cocycles in the sheaf biproduct

The biproduct is that of the original abelian-sheaf category. Its actual
inclusions and projections give the pairing of literal cocycles.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicPicard.Cech

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    {ι : Type} {U : ι → Opens X}

def pairCocycle (c : CechOneCocycle F U) (d : CechOneCocycle G U) :
    CechOneCocycle (F ⊞ G) U :=
  mapCocycle biprod.inl c + mapCocycle biprod.inr d

@[simp] theorem mapCocycle_fst_pair (c : CechOneCocycle F U) (d : CechOneCocycle G U) :
    mapCocycle (biprod.fst : F ⊞ G ⟶ F) (pairCocycle c d) = c := by
  simp only [pairCocycle, map_add, ← mapCocycle_comp, biprod.inl_fst, biprod.inr_fst,
    mapCocycle_id, mapCocycle_zero, add_zero]

@[simp] theorem mapCocycle_snd_pair (c : CechOneCocycle F U) (d : CechOneCocycle G U) :
    mapCocycle (biprod.snd : F ⊞ G ⟶ G) (pairCocycle c d) = d := by
  simp only [pairCocycle, map_add, ← mapCocycle_comp, biprod.inl_snd, biprod.inr_snd,
    mapCocycle_id, mapCocycle_zero, zero_add]

theorem mapCocycle_sum_pair (c d : CechOneCocycle F U) :
    mapCocycle ((biprod.fst : F ⊞ F ⟶ F) + biprod.snd) (pairCocycle c d) = c + d := by
  rw [mapCocycle_add, mapCocycle_fst_pair, mapCocycle_snd_pair]

end Wikipedia.HopfProblem.HolomorphicPicard.Cech
