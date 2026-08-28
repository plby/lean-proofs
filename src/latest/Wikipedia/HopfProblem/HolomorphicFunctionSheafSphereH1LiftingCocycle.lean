import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1LiftingLocal

/-!
# The actual overlap cocycle of local lifts

For a short exact sequence of additive sheaves, differences of local
lifts of one global section lie in the kernel on each actual overlap.
Sectionwise left exactness lifts those differences to the first sheaf;
sectionwise injectivity proves the genuine triple-overlap identity.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {ι : Type}

/-- The actual difference of two local sections on their overlap. -/
def overlapDifference (E : TopCat.Sheaf AddCommGrpCat.{0} X)
    (U : ι → Opens X) (t : ∀ i : ι, Section E (U i)) (i j : ι) :
    Section E (U i ⊓ U j) :=
  res E inf_le_left (t i) - res E inf_le_right (t j)

/-- Differences telescope after literal restriction to a triple intersection. -/
theorem overlapDifference_condition (E : TopCat.Sheaf AddCommGrpCat.{0} X)
    (U : ι → Opens X) (t : ∀ i : ι, Section E (U i)) (i j k : ι) :
    res E (V := (U i ⊓ U j) ⊓ U k) inf_le_left (overlapDifference E U t i j) +
      res E (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_right le_rfl) (overlapDifference E U t j k) =
      res E (V := (U i ⊓ U j) ⊓ U k)
        (inf_le_inf inf_le_left le_rfl) (overlapDifference E U t i k) := by
  simp only [overlapDifference, map_sub, res_trans]
  abel

/-- The overlap differences of actual local lifts give an actual cocycle
in the kernel sheaf, not an assumed pointwise exactness condition. -/
theorem exists_difference_cocycle
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (U : ι → Opens X) (s : Section S.X₃ ⊤)
    (t : ∀ i : ι, Section S.X₂ (U i))
    (ht : ∀ i : ι, S.g.hom.app (op (U i)) (t i) = res S.X₃ le_top s) :
    ∃ c : CechOneCocycle S.X₁ U, ∀ i j : ι,
      S.f.hom.app (op (U i ⊓ U j)) (c.value i j) = overlapDifference S.X₂ U t i j := by
  classical
  have hk (i j : ι) : S.g.hom.app (op (U i ⊓ U j))
      (overlapDifference S.X₂ U t i j) = 0 := by
    simp only [overlapDifference, map_sub, ← res_map, ht, res_trans, sub_self]
  choose c hc using fun i j => section_kernel_lift hS
    (overlapDifference S.X₂ U t i j) (hk i j)
  refine ⟨⟨c, ?_⟩, hc⟩
  intro i j k
  apply section_f_injective hS ((U i ⊓ U j) ⊓ U k)
  simp only [map_add, ← res_map, hc]
  exact overlapDifference_condition S.X₂ U t i j k

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
