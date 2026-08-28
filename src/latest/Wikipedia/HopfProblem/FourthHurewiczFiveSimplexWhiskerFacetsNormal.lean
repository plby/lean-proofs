import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerFacetsNormalBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerCell
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerPieces
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexUncurryBasic

/-!
# The literal normal facets of a whiskered cubical cell

Uncurrying prepends the path coordinate. On every normal facet, the two
outer arms are constant by codimension-two basedness, and the middle arm
is the original ordered facet. The equality uses the exact native nested
concatenation times, without reparametrization or homotopy assumptions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- Every normal facet of the whiskered cell is exactly the original facet
with a constant loop prepended and appended in the first coordinate. -/
theorem whiskeredCell_face_normal (F : BasedCubicalCell (n + 2) x)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1)
    (h : i ≠ Fin.last n ∨ ε = 0) :
    uncurryLoop (cubicalFace (whiskeredCell F) i ε hε) =
      GenLoop.transAt 0 GenLoop.const
        (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) := by
  apply GenLoop.ext
  intro u
  have hcons (s : I) : Function.update u 0 s = Fin.cons s (fun j => u j.succ) := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simp
  change F.val (whiskerMap n (cubeFacet n i ε (fun j => u j.succ), u 0)) =
    GenLoop.transAt 0 GenLoop.const
      (GenLoop.transAt 0 (cubicalFace F i.succ ε hε) GenLoop.const) u
  rw [whiskerMap_concat]
  simp only [GenLoop.transAt, GenLoop.coe_copy, GenLoop.const_apply,
    Function.update_self, Function.update_idem]
  split_ifs with hs ht
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 0 (Or.inl rfl) _
  · rw [cubicalFace_apply, hcons, cubeFacet_succ_cons]
  · exact whiskerFacetNormal_arm_based F i ε hε h _ 1 (Or.inr rfl) _

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
