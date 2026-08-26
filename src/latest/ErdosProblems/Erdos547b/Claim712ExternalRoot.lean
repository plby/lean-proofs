/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim712

open Finset SimpleGraph

/-- The external-root greedy step used for the selected natural subtree in
Claim 7.12.  The distinguished target root is sent to `rootImage`, which is
allowed to lie outside `H`; all remaining vertices land in `H`.

The source obtains both cardinal hypotheses from
`deg(rootImage,H) > |S|` and `δ(G[H]) > e(S)=|S|-1`. -/
theorem exists_external_root_tree_copy
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (T : SimpleGraph A) (G : SimpleGraph B) [DecidableRel G.Adj]
    (hT : T.IsTree) (root : A) (rootImage : B) (H : Finset B)
    (hroot : Fintype.card A ≤ ((G.neighborFinset rootImage) ∩ H).card)
    (hmin : ∀ v ∈ H,
      Fintype.card A ≤ ((G.neighborFinset v) ∩ H).card) :
    ∃ f : T.Copy G,
      f root = rootImage ∧ ∀ a, a ≠ root → f a ∈ H := by
  let candidate : A → Finset B := fun _ => H
  apply Erdos547b.ZhaoLemma59.exists_rooted_candidate_copy
    T G hT root candidate rootImage
  · intro a hra
    change Fintype.card A ≤ #(H.filter (G.Adj rootImage))
    rw [show H.filter (G.Adj rootImage) = G.neighborFinset rootImage ∩ H by
      ext w
      simp [and_comm]]
    exact hroot
  · intro a b hab hbr v hv
    have hvH : v ∈ H := by simpa [candidate] using hv
    change Fintype.card A ≤ #(H.filter (G.Adj v))
    rw [show H.filter (G.Adj v) = G.neighborFinset v ∩ H by
      ext w
      simp [and_comm]]
    exact hmin v hvH

end Erdos547b.ZhaoClaim712

#print axioms Erdos547b.ZhaoClaim712.exists_external_root_tree_copy
