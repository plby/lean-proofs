/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The neighbourhood-pattern pigeonhole lemma. -/

import ErdosProblems.Erdos717.DenseReservoir
import Mathlib.Combinatorics.Pigeonhole

open Function Set
open SimpleGraph

namespace Erdos717

/-- Exact finite form of the Fox--Lee--Sudakov neighbourhood-pattern
pigeonhole argument.  `I` is a maximum independent set, every vertex of `W`
has at most `b` neighbours in `I`, and `Q` is any lower bound surviving the
number `choose |I| b` of possible enlarged neighbourhood patterns. -/
theorem exists_subset_indepBoundOn_of_neighborhood_pattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I W : Finset V) (b Q : ℕ)
    (hIP : I ⊆ P) (hWP : W ⊆ P)
    (hIind : G.IsIndepSet I) (hImax : IndepBoundOn G P I.card)
    (hIW : Disjoint I W) (hb : b ≤ I.card)
    (hdegree : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b)
    (hlarge : I.card.choose b * Q ≤ W.card) :
    ∃ U : Finset V, U ⊆ W ∧ Q ≤ U.card ∧ IndepBoundOn G U b := by
  classical
  have hpattern (v : V) (hv : v ∈ W) :
      ∃ J : Finset V, G.neighborFinset v ∩ I ⊆ J ∧ J ⊆ I ∧ J.card = b := by
    exact Finset.exists_subsuperset_card_eq (Finset.inter_subset_right)
      (hdegree v hv) hb
  let pattern (v : V) : Finset V := if hv : v ∈ W then
    Classical.choose (hpattern v hv) else ∅
  have pattern_spec {v : V} (hv : v ∈ W) :
      G.neighborFinset v ∩ I ⊆ pattern v ∧ pattern v ⊆ I ∧
        (pattern v).card = b := by
    simp only [pattern, dif_pos hv]
    exact Classical.choose_spec (hpattern v hv)
  let patterns := I.powersetCard b
  have hmaps : ∀ v ∈ W, pattern v ∈ patterns := by
    intro v hv
    exact Finset.mem_powersetCard.mpr ⟨(pattern_spec hv).2.1,
      (pattern_spec hv).2.2⟩
  have hpatternsNonempty : patterns.Nonempty := by
    obtain ⟨J, _hsub, _hsup, hJcard⟩ :=
      Finset.exists_subsuperset_card_eq (s := ∅) (t := I) (n := b)
        (Finset.empty_subset I) (by simp) hb
    exact ⟨J, Finset.mem_powersetCard.mpr ⟨_hsup, hJcard⟩⟩
  have hpatternCard : patterns.card = I.card.choose b := by
    simp [patterns]
  obtain ⟨J, hJpatterns, hJUcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := pattern) hmaps hpatternsNonempty (by simpa [hpatternCard] using hlarge)
  let U := W.filter fun v => pattern v = J
  have hUsub : U ⊆ W := Finset.filter_subset _ _
  have hUcard : Q ≤ U.card := by
    simpa only [U] using hJUcard
  have hJsub : J ⊆ I := (Finset.mem_powersetCard.mp hJpatterns).1
  have hJcard : J.card = b := (Finset.mem_powersetCard.mp hJpatterns).2
  have hlocal : IndepBoundOn G U b := by
    intro A hAU hAind
    have hAW : A ⊆ W := hAU.trans hUsub
    have hAI : Disjoint A I := by
      rw [Finset.disjoint_left]
      intro x hxA hxI
      exact (Finset.disjoint_left.mp hIW) hxI (hAW hxA)
    have hcross : ∀ x ∈ A, ∀ y ∈ I \ J, ¬G.Adj x y := by
      intro x hxA y hyIJ hxy
      have hxU := hAU hxA
      have hpat : pattern x = J := (Finset.mem_filter.mp hxU).2
      have hyI := (Finset.mem_sdiff.mp hyIJ).1
      have hyN : y ∈ G.neighborFinset x := by
        exact (G.mem_neighborFinset x y).mpr hxy
      have hyPattern : y ∈ pattern x :=
        (pattern_spec (hUsub hxU)).1 (Finset.mem_inter.mpr ⟨hyN, hyI⟩)
      exact (Finset.mem_sdiff.mp hyIJ).2 (hpat ▸ hyPattern)
    have hIminus : G.IsIndepSet (I \ J : Finset V) :=
      hIind.mono (by exact_mod_cast Finset.sdiff_subset)
    have hunionInd : G.IsIndepSet (↑(A ∪ (I \ J)) : Set V) := by
      rw [G.isIndepSet_iff]
      intro x hx y hy hxy
      simp only [Finset.coe_union, Set.mem_union] at hx hy
      rcases hx with hxA | hxI
      · rcases hy with hyA | hyI
        · exact (G.isIndepSet_iff.mp hAind) hxA hyA hxy
        · exact hcross x hxA y hyI
      · rcases hy with hyA | hyI
        · exact fun h => hcross y hyA x hxI h.symm
        · exact (G.isIndepSet_iff.mp hIminus) hxI hyI hxy
    have hcardUnion : (A ∪ (I \ J)).card = A.card + (I \ J).card := by
      rw [Finset.card_union_of_disjoint]
      exact hAI.mono_right Finset.sdiff_subset
    have hindCard : (A ∪ (I \ J)).card ≤ I.card := by
      apply hImax (A ∪ (I \ J))
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hxA | hxI
        · exact hWP (hAW hxA)
        · exact hIP ((Finset.mem_sdiff.mp hxI).1)
      · exact hunionInd
    have hdiffCard : (I \ J).card = I.card - b := by
      rw [Finset.card_sdiff_of_subset hJsub, hJcard]
    rw [hcardUnion, hdiffCard] at hindCard
    omega
  exact ⟨U, hUsub, hUcard, hlocal⟩

end Erdos717
