import ErdosProblems.Erdos547.LabelledEmbedding
import ErdosProblems.Erdos547.AttachLeavesColour

/-!
# Embedding the two-coloured cut forest into two prescribed pools
-/

namespace Erdos547

open Finset SimpleGraph

variable {U V : Type*}

def completeColourGraph (col : U → Fin 2) : SimpleGraph U where
  Adj u v := col u ≠ col v
  symm := ⟨fun _ _ h ↦ Ne.symm h⟩
  loopless := ⟨fun _ h ↦ h rfl⟩

theorem completeColourGraph_connected (col : U → Fin 2) (hcol : Function.Surjective col) :
    (completeColourGraph col).Connected := by
  obtain ⟨u₀, _hu₀⟩ := hcol 0
  let : Nonempty U := ⟨u₀⟩
  constructor
  intro u v
  by_cases huv : col u ≠ col v
  · exact (show (completeColourGraph col).Adj u v from huv).reachable
  · have heq : col u = col v := not_not.mp huv
    obtain ⟨w, hw⟩ := hcol (flipTreeColour (col u))
    have huw : (completeColourGraph col).Adj u w := by
      change col u ≠ col w
      rw [hw]
      exact (flipTreeColour_ne (col u)).symm
    have hwv : (completeColourGraph col).Adj w v := by
      change col w ≠ col v
      rw [hw, ← heq]
      exact flipTreeColour_ne (col u)
    exact huw.reachable.trans hwv.reachable

open scoped Classical in
theorem exists_copy_of_two_coloured_forest [Fintype U]
    (F : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hF : F.IsAcyclic) (col : U → Fin 2) (hcol : Function.Surjective col)
    (hproper : ∀ u v, F.Adj u v → col u ≠ col v)
    (pool : Fin 2 → Finset V) (hdis : ∀ i j, i ≠ j → Disjoint (pool i) (pool j))
    (hdegree : ∀ i j, i ≠ j → ∀ z ∈ pool i,
      Fintype.card U ≤ degreeIn G (pool j) z)
    (r : U) (z : V) (hz : z ∈ pool (col r)) :
    ∃ f : F.Copy G, f r = z ∧ ∀ u, f u ∈ pool (col u) := by
  classical
  have hsuper : F ≤ completeColourGraph col := fun u v huv ↦ hproper u v huv
  have hconnected := completeColourGraph_connected col hcol
  obtain ⟨T, hFT, hTC, hT⟩ := hconnected.exists_isTree_le_of_le_of_isAcyclic hsuper hF
  obtain ⟨f, hfr, hfp⟩ := exists_copy_of_labelled_degree T G hT col pool hdis
    (by
      intro u v huv w hw
      exact (Finset.card_le_univ _).trans (hdegree (col u) (col v) (hTC huv) w hw))
    r z hz
  exact ⟨f.comp (SimpleGraph.Copy.ofLE F T hFT), hfr, hfp⟩

end Erdos547

#print axioms Erdos547.exists_copy_of_two_coloured_forest
