/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68

/-! # Two-tier leaf completion by a direct Hall argument -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoTwoTierLeafCompletion

open Finset Fintype SimpleGraph Erdos547b.ZhaoClaim68

universe u v

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
variable [DecidableEq α] [DecidableEq β]

theorem card_leafChoices_add_slack
    (W : Finset α) {T : SimpleGraph α} (G : SimpleGraph β) [DecidableRel G.Adj]
    (parent : {x // x ∈ W} → α) (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (slack : ℕ) (x : {x // x ∈ W})
    (hdegree : Fintype.card α - 1 ≤ G.degree (f ⟨parent x, hparent x⟩) + slack) :
    W.card ≤ (leafChoices W G parent hparent f x).card + slack := by
  let p := f ⟨parent x, hparent x⟩
  let N := G.neighborFinset p
  let U := baseImages W f
  have hpU : p ∈ U := Finset.mem_image.mpr ⟨⟨parent x, hparent x⟩, Finset.mem_univ _, rfl⟩
  have hpN : p ∉ N := by simp [N]
  have hproper : N ∩ U ⊂ U := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro heq
    have hp : p ∈ N ∩ U := heq.symm ▸ hpU
    exact hpN (Finset.mem_inter.mp hp).1
  have hinter : (N ∩ U).card + 1 ≤ U.card := Finset.card_lt_card hproper
  have hU : U.card = Fintype.card α - W.card := by
    have himage : (Finset.univ.image (fun x => f x)).card =
        (Finset.univ : Finset {x // x ∉ W}).card :=
      Finset.card_image_of_injective _ (fun _ _ h => f.injective h)
    change (Finset.univ.image (fun x => f x)).card = _
    rw [himage, Finset.card_univ]
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun x : α => x ∈ W)
  have hN : Fintype.card α - 1 ≤ N.card + slack := hdegree
  have hW := Finset.card_le_univ W
  rw [leafChoices, Finset.card_sdiff]
  change W.card ≤ N.card - (U ∩ N).card + slack
  rw [Finset.inter_comm]
  omega

theorem exists_leafRepresentatives_twoTier
    (W : Finset α) {T : SimpleGraph α} (G : SimpleGraph β) [DecidableRel G.Adj]
    (parent : {x // x ∈ W} → α) (hparent : ∀ x, parent x ∉ W)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G) (High : Finset {x // x ∈ W})
    (hhigh : ∀ x ∈ High, Fintype.card α - 1 ≤ G.degree (f ⟨parent x, hparent x⟩))
    (hlow : ∀ x ∉ High, Fintype.card α - 1 - High.card ≤ G.degree (f ⟨parent x, hparent x⟩)) :
    ∃ g : {x // x ∈ W} → β, Function.Injective g ∧
      ∀ x, g x ∈ leafChoices W G parent hparent f x := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective (leafChoices W G parent hparent f)).mp
  intro s
  by_cases hs : s = ∅
  · simp [hs]
  by_cases hh : ∃ x ∈ s, x ∈ High
  · obtain ⟨x, hx, hxH⟩ := hh
    have hchoices := card_leafChoices_add_slack W G parent hparent f 0 x (by simpa using hhigh x hxH)
    have hcard : s.card ≤ W.card := by simpa only [Fintype.card_coe] using Finset.card_le_univ s
    have hlarge : W.card ≤ (leafChoices W G parent hparent f x).card := by simpa using hchoices
    exact hcard.trans (hlarge.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem _ hx)))
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hsLow : s ⊆ Finset.univ \ High := by
      intro y hy
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hh ⟨y, hy, h⟩⟩
    have hxLow : x ∉ High := fun h => hh ⟨x, hx, h⟩
    have hchoices := card_leafChoices_add_slack W G parent hparent f High.card x (by
      have h := hlow x hxLow
      omega)
    have hcard : s.card ≤ W.card - High.card := by
      have h := Finset.card_le_card hsLow
      simpa only [Finset.card_sdiff_of_subset (Finset.subset_univ High),
        Finset.card_univ, Fintype.card_coe] using h
    have hlarge : W.card - High.card ≤ (leafChoices W G parent hparent f x).card := by omega
    exact hcard.trans (hlarge.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem _ hx)))

theorem exists_copy_of_twoTier_leaves
    {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (T : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (W : Finset α)
    (parent : (x : {x // x ∈ W}) → α)
    (hparent_not_mem : ∀ x, parent x ∉ W)
    (_hparent_adj : ∀ x, T.Adj (parent x) x)
    (hleaf : ∀ x : {x // x ∈ W}, ∀ y, T.Adj x y → y = parent x)
    (f : (T.induce (↑W : Set α)ᶜ).Copy G)
    (High : Finset {x // x ∈ W})
    (hhigh : ∀ x ∈ High, Fintype.card α - 1 ≤ G.degree (f ⟨parent x, hparent_not_mem x⟩))
    (hlow : ∀ x ∉ High, Fintype.card α - 1 - High.card ≤ G.degree (f ⟨parent x, hparent_not_mem x⟩)) :
    ∃ F : T.Copy G,
      (∀ x : {x // x ∉ W}, F x = f x) ∧
      (∀ x : {x // x ∈ W}, G.Adj (f ⟨parent x, hparent_not_mem x⟩) (F x)) := by
  obtain ⟨g, hginj, hgchoice⟩ :=
    exists_leafRepresentatives_twoTier W G parent hparent_not_mem f High hhigh hlow
  let F0 : α → β := fun x => if hx : x ∈ W then g ⟨x, hx⟩ else f ⟨x, hx⟩
  have hF0_inj : Function.Injective F0 := by
    intro x y hxy
    by_cases hx : x ∈ W
    · by_cases hy : y ∈ W
      · have : (⟨x, hx⟩ : {x // x ∈ W}) = ⟨y, hy⟩ := by
          apply hginj
          simpa [F0, hx, hy] using hxy
        exact congrArg Subtype.val this
      · exfalso
        have hchoice := hgchoice ⟨x, hx⟩
        have hnotbase : g ⟨x, hx⟩ ∉ baseImages W f := by
          exact Finset.mem_sdiff.mp hchoice |>.2
        apply hnotbase
        apply Finset.mem_image.mpr
        exact ⟨⟨y, hy⟩, Finset.mem_univ _, by simpa [F0, hx, hy] using hxy.symm⟩
    · by_cases hy : y ∈ W
      · exfalso
        have hchoice := hgchoice ⟨y, hy⟩
        have hnotbase : g ⟨y, hy⟩ ∉ baseImages W f := by
          exact Finset.mem_sdiff.mp hchoice |>.2
        apply hnotbase
        apply Finset.mem_image.mpr
        exact ⟨⟨x, hx⟩, Finset.mem_univ _, by simpa [F0, hx, hy] using hxy⟩
      · have : (⟨x, hx⟩ : {x // x ∉ W}) = ⟨y, hy⟩ := by
          apply f.injective
          simpa [F0, hx, hy] using hxy
        exact congrArg Subtype.val this
  have hF0_adj : ∀ ⦃x y⦄, T.Adj x y → G.Adj (F0 x) (F0 y) := by
    intro x y hxy
    by_cases hx : x ∈ W
    · have hyeq : y = parent ⟨x, hx⟩ := hleaf ⟨x, hx⟩ y hxy
      subst y
      have hyp : parent ⟨x, hx⟩ ∉ W := hparent_not_mem ⟨x, hx⟩
      have hchoice := Finset.mem_sdiff.mp (hgchoice ⟨x, hx⟩)
      have hadj : G.Adj (f ⟨parent ⟨x, hx⟩, hyp⟩) (g ⟨x, hx⟩) := by
        exact (G.mem_neighborFinset _ _).mp hchoice.1
      simpa [F0, hx, hyp] using hadj.symm
    · by_cases hy : y ∈ W
      · have hxeq : x = parent ⟨y, hy⟩ := hleaf ⟨y, hy⟩ x hxy.symm
        subst x
        have hxp : parent ⟨y, hy⟩ ∉ W := hparent_not_mem ⟨y, hy⟩
        have hchoice := Finset.mem_sdiff.mp (hgchoice ⟨y, hy⟩)
        have hadj : G.Adj (f ⟨parent ⟨y, hy⟩, hxp⟩) (g ⟨y, hy⟩) := by
          exact (G.mem_neighborFinset _ _).mp hchoice.1
        simpa [F0, hy, hxp] using hadj
      · have hinduced : (T.induce (↑W : Set α)ᶜ).Adj
            ⟨x, hx⟩ ⟨y, hy⟩ := by simpa using hxy
        simpa [F0, hx, hy] using f.toHom.map_rel hinduced
  let F : T.Copy G := ⟨⟨F0, fun {_ _} h => hF0_adj h⟩, hF0_inj⟩
  refine ⟨F, ?_, ?_⟩
  · intro x
    simp [F, F0, x.property]
  · intro x
    have hchoice := Finset.mem_sdiff.mp (hgchoice x)
    have hadj : G.Adj (f ⟨parent x, hparent_not_mem x⟩) (g x) :=
      (G.mem_neighborFinset _ _).mp hchoice.1
    simpa [F, F0, x.property] using hadj

end Erdos547b.ZhaoTwoTierLeafCompletion

#print axioms Erdos547b.ZhaoTwoTierLeafCompletion.card_leafChoices_add_slack
#print axioms Erdos547b.ZhaoTwoTierLeafCompletion.exists_leafRepresentatives_twoTier
#print axioms Erdos547b.ZhaoTwoTierLeafCompletion.exists_copy_of_twoTier_leaves
