import Arxiv.Arxiv2411_18291.GroupEliminationIndices
import Arxiv.Arxiv2411_18291.RootedCliqueGrouping
import Arxiv.Arxiv2411_18291.IntegralGenerationTransitivity

/-!
# Retaining representatives while eliminating their other group members

Remove precisely the indexed nonrepresentatives. Every representative stays
in the retained family, and identities for representative-minus-member
differences preserve the entire original integer span. On each labelled
root edge, at most one retained clique per group remains.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ}

def groupEliminationRemoved (G : Finset (Finset (Block V q))) (Q : G → Block V q) :
    Finset (Block V q) := univ.image fun i : GroupEliminationIndex G Q => i.2.val

def groupEliminationRetained (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (Q : G → Block V q) : Finset (Block V q) :=
  D \ groupEliminationRemoved G Q

theorem representative_mem_retained (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (hQ : ∀ c, Q c ∈ c.val) (c : G) :
    Q c ∈ groupEliminationRetained D G Q := by
  refine mem_sdiff.mpr ⟨hsub c.val c.property (hQ c), ?_⟩
  intro h
  obtain ⟨i, _, hi⟩ := mem_image.mp h
  exact representative_not_eliminated G hdis Q hQ c i hi.symm

theorem retained_group_member_eq (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (Q : G → Block V q) (c : G)
    {P : Block V q} (hP : P ∈ groupEliminationRetained D G Q) (hPc : P ∈ c.val) : P = Q c := by
  by_contra hne
  let i : GroupEliminationIndex G Q := ⟨c, ⟨P, mem_erase.mpr ⟨hne, hPc⟩⟩⟩
  exact (mem_sdiff.mp hP).2 (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

variable [Fintype V]

theorem groupElimination_preserves_generation (D : Finset (Block V q))
    (G : Finset (Finset (Block V q))) (hsub : ∀ c ∈ G, c ⊆ D)
    (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (Q : G → Block V q) (hQ : ∀ c, Q c ∈ c.val) (F : Finset (Block V q))
    (hkeep : groupEliminationRetained D G Q ⊆ F)
    (helim : ∀ i : GroupEliminationIndex G Q,
      GeneratedBy F (indicator (cliqueEdges r (Q i.1)) - indicator (cliqueEdges r i.2.val)))
    {J : Block V r → ℤ} (hJ : GeneratedBy D J) : GeneratedBy F J := by
  apply hJ.trans
  intro P hP
  by_cases hrem : P ∈ groupEliminationRemoved G Q
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hrem
    have hleft := generatedBy_clique (r := r)
      (hkeep (representative_mem_retained D G hsub hdis Q hQ i.1))
    convert hleft.sub (helim i) using 1
    abel
  · exact generatedBy_clique (hkeep (mem_sdiff.mpr ⟨hP, hrem⟩))

omit [Fintype V] in
theorem RootedCliqueGrouping.retained_root_count {D : Finset (Block V q)}
    {B : Hypergraph V r} {m : ℕ} (R : RootedCliqueGrouping D B m)
    (Q : R.groups → Block V q) (e : B) :
    ((groupEliminationRetained D R.groups Q).filter fun P => e.val.val ⊆ P.val).card ≤ m := by
  have hsub : (groupEliminationRetained D R.groups Q).filter (fun P => e.val.val ⊆ P.val) ⊆
      (univ.filter fun c : R.groups => R.root c = e).image Q := by
    intro P hP
    obtain ⟨hkeep, heP⟩ := mem_filter.mp hP
    obtain ⟨c, hc, hPc⟩ := R.covers e P (mem_sdiff.mp hkeep).1 heP
    have heq := retained_group_member_eq D R.groups Q c hkeep hPc
    exact mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, hc⟩, heq.symm⟩
  exact (card_le_card hsub).trans (card_image_le.trans (R.root_count e))

end Arxiv2411_18291
