import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Transporting degree counts from an induced graph to the original graph
-/

namespace Erdos547

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
theorem degreeIn_image_subtype [DecidableEq V] (A : Set V) (S : Finset A) (v : A) :
    degreeIn G (S.image (fun x : A ↦ x.val)) v.val =
      degreeIn (G.induce A) S v := by
  classical
  unfold degreeIn
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ Subtype.coe_injective

end Erdos547

#print axioms Erdos547.degreeIn_image_subtype
