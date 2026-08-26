import Mathlib
import ErdosProblems.Erdos550.HPRootedPair

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restricted rooted-pair steps with dynamically free reservoirs

The Hladký--Piguet matching algorithm invokes Lemma 5.12 after deleting all
previously used vertices and the vertices not typical back to the head
cluster.  This adapter chooses equal fixed reservoirs inside those dynamic
free pools and exposes the conclusion in the form needed for block gluing.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

/-- Embed one small rooted component with its root prescribed on the left.
All images lie in the supplied free pools. -/
theorem hp_restricted_pair_step_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    {s t freeL freeR rootPool : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    (hdens : d ≤ (G.edgeDensity s t : ℝ))
    (hfreeL : freeL ⊆ s) (hfreeR : freeR ⊆ t)
    (hrootPool : rootPool ⊆ freeL)
    (L : ℕ)
    (hLfree : L ≤ freeL.card) (hRfree : L ≤ freeR.card)
    (hrootCard : L ≤ rootPool.card)
    (hLsig : ε * (s.card : ℝ) ≤ (L : ℝ))
    (hRsig : ε * (t.card : ℝ) ≤ (L : ℝ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (root : A) (hroot : parent root = none)
    (hrootUnique : ∀ a, parent a = none → a = root)
    (col : A → Bool) (hrootCol : col root = false)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hroom :
      ε * (max s.card t.card : ℝ) + (Fintype.card A : ℝ)
        ≤ (d - 2 * ε) * (L : ℝ)) :
    ∃ f : A → V, Function.Injective f ∧
      f root ∈ rootPool ∧
      (∀ a, f a ∈ (if col a then freeR else freeL)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  obtain ⟨SP, hSPsub, hSPcard⟩ :=
    Finset.exists_subset_card_eq hLfree
  obtain ⟨SQ, hSQsub, hSQcard⟩ :=
    Finset.exists_subset_card_eq hRfree
  obtain ⟨f, hfinj, hfroot, hfside, hfadj⟩ :=
    hp_rootedTree_embedding_left G hε0 hε1 hd1
      hs ht huni hdens
      (hSPsub.trans hfreeL) (hSQsub.trans hfreeR)
      (hrootPool.trans hfreeL)
      L hSPcard hSQcard hrootCard hLsig hRsig
      parent rank hrank root hroot hrootUnique col hrootCol hcol hroom
  refine ⟨f, hfinj, hfroot, ?_, hfadj⟩
  intro a
  by_cases har : a = root
  · subst a
    simpa [hrootCol] using! hrootPool hfroot
  · have h := hfside a har
    by_cases hca : col a
    · simpa [hca] using! hSQsub (by simpa [hca] using! h)
    · simpa [hca] using! hSPsub (by simpa [hca] using! h)

/-- Symmetric dynamically-free step with the prescribed root on the right. -/
theorem hp_restricted_pair_step_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    {s t freeL freeR rootPool : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    (hdens : d ≤ (G.edgeDensity s t : ℝ))
    (hfreeL : freeL ⊆ s) (hfreeR : freeR ⊆ t)
    (hrootPool : rootPool ⊆ freeR)
    (L : ℕ)
    (hLfree : L ≤ freeL.card) (hRfree : L ≤ freeR.card)
    (hrootCard : L ≤ rootPool.card)
    (hLsig : ε * (s.card : ℝ) ≤ (L : ℝ))
    (hRsig : ε * (t.card : ℝ) ≤ (L : ℝ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (root : A) (hroot : parent root = none)
    (hrootUnique : ∀ a, parent a = none → a = root)
    (col : A → Bool) (hrootCol : col root = true)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hroom :
      ε * (max s.card t.card : ℝ) + (Fintype.card A : ℝ)
        ≤ (d - 2 * ε) * (L : ℝ)) :
    ∃ f : A → V, Function.Injective f ∧
      f root ∈ rootPool ∧
      (∀ a, f a ∈ (if col a then freeR else freeL)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  obtain ⟨SP, hSPsub, hSPcard⟩ :=
    Finset.exists_subset_card_eq hLfree
  obtain ⟨SQ, hSQsub, hSQcard⟩ :=
    Finset.exists_subset_card_eq hRfree
  obtain ⟨f, hfinj, hfroot, hfside, hfadj⟩ :=
    hp_rootedTree_embedding_right G hε0 hε1 hd1
      hs ht huni hdens
      (hSPsub.trans hfreeL) (hSQsub.trans hfreeR)
      (hrootPool.trans hfreeR)
      L hSPcard hSQcard hrootCard hLsig hRsig
      parent rank hrank root hroot hrootUnique col hrootCol hcol hroom
  refine ⟨f, hfinj, hfroot, ?_, hfadj⟩
  intro a
  by_cases har : a = root
  · subst a
    simpa [hrootCol] using! hrootPool hfroot
  · have h := hfside a har
    by_cases hca : col a
    · simpa [hca] using! hSQsub (by simpa [hca] using! h)
    · simpa [hca] using! hSPsub (by simpa [hca] using! h)

end Erdos550
