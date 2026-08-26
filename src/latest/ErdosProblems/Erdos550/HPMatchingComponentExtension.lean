import Mathlib
import ErdosProblems.Erdos550.HPComponentBlockStep
import ErdosProblems.Erdos550.HPComponentPackedGlue
import ErdosProblems.Erdos550.RestrictedHPStep

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative matching-wide component extension

This is the sharp local engine used by the parity-routed induction.  The aggregate
surplus selects one matching edge.  The packedness dichotomy orients the
component, the rooted regular-pair lemma embeds it, and exact side-cardinality
accounting updates packedness on the whole matching.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

set_option maxHeartbeats 800000 in
theorem hp_matching_component_extension
    {A : Type} {V κ : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype κ] [DecidableEq κ]
    (T : SimpleGraph A) (Sseed P : Finset A)
    {parent : A → Option A} {rank : A → ℕ}
    (D : RootedSeedComponentData T Sseed parent)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (col routeColour : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : NonseedComponent T Sseed)
    (hboundary : ∀ a ∈ componentSeeds T Sseed c.1,
      ∀ b ∈ componentSeeds T Sseed c.1, col a = col b)
    (head : Bool)
    (hroute : ∀ x : RootedComponentVertex T Sseed c,
      routeColour x.1 = head)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    (Good : Finset κ) (hGood : Good.Nonempty)
    (left right freeL freeR contactL contactR rootPoolL rootPoolR :
      κ → Finset V)
    (retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (hleft : ∀ k ∈ Good, (left k).Nonempty)
    (hright : ∀ k ∈ Good, (right k).Nonempty)
    (huni : ∀ k ∈ Good, G.IsUniform ε (left k) (right k))
    (hdens : ∀ k ∈ Good,
      d ≤ (G.edgeDensity (left k) (right k) : ℝ))
    (hfreeL : ∀ k ∈ Good, freeL k ⊆ left k)
    (hfreeR : ∀ k ∈ Good, freeR k ⊆ right k)
    (hcontactL : ∀ k ∈ Good, contactL k ⊆ freeL k)
    (hcontactR : ∀ k ∈ Good, contactR k ⊆ freeR k)
    (hrootPoolL : ∀ k ∈ Good, rootPoolL k ⊆ contactL k)
    (hrootPoolR : ∀ k ∈ Good, rootPoolR k ⊆ contactR k)
    (hLR : ∀ k, Disjoint (left k) (right k))
    (hother : ∀ k j, k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j))
    (hcontactLRet : ∀ k ∈ Good, contactL k ⊆ retained head)
    (hcontactRRet : ∀ k ∈ Good, contactR k ⊆ retained head)
    (hfreeLRegion : ∀ k ∈ Good, freeL k ⊆ matchingRegion head)
    (hfreeRRegion : ∀ k ∈ Good, freeR k ⊆ matchingRegion head)
    (anchor : V)
    (hrootAdjL : ∀ k ∈ Good, ∀ v ∈ rootPoolL k, G.Adj anchor v)
    (hrootAdjR : ∀ k ∈ Good, ∀ v ∈ rootPoolR k, G.Adj anchor v)
    (f : A → V)
    (hfreeLFresh : ∀ k ∈ Good, Disjoint (freeL k) (P.image f))
    (hfreeRFresh : ∀ k ∈ Good, Disjoint (freeR k) (P.image f))
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ err cap : ℝ) (Lnat : ℕ)
    (hpacked : HPMatchingPacked P f left right
      leftThreshold rightThreshold margin τ)
    (hBP : Disjoint (componentNonseedVertices T Sseed c.1) P)
    (hcomponent :
      (Fintype.card (RootedComponentVertex T Sseed c) : ℝ) ≤ τ)
    (hLsig : ∀ k ∈ Good,
      ε * ((left k).card : ℝ) ≤ (Lnat : ℝ))
    (hRsig : ∀ k ∈ Good,
      ε * ((right k).card : ℝ) ≤ (Lnat : ℝ))
    (hpairRoom : ∀ k ∈ Good,
      ε * (max (left k).card (right k).card : ℝ) +
          (Fintype.card (RootedComponentVertex T Sseed c) : ℝ)
        ≤ (d - 2 * ε) * (Lnat : ℝ))
    (hsurplus :
      (∑ k ∈ Good,
          (matchingSideLoad P f (left k) +
            matchingSideLoad P f (right k))) +
          (Good.card : ℝ) * ((Lnat : ℝ) + margin) ≤
        ∑ k ∈ Good, (leftThreshold k + rightThreshold k))
    (htypL : ∀ k ∈ Good,
      leftThreshold k - matchingSideLoad P f (left k) - err ≤
        ((rootPoolL k).card : ℝ))
    (htypR : ∀ k ∈ Good,
      rightThreshold k - matchingSideLoad P f (right k) - err ≤
        ((rootPoolR k).card : ℝ))
    (hrootFromRoom :
      2 * (Lnat : ℝ) + 2 * err ≤ (Lnat : ℝ) + margin)
    (hrootMargin : (Lnat : ℝ) + τ + err ≤ margin)
    (hlocalMargin : (Lnat : ℝ) + τ ≤ margin)
    (hLcap : ∀ k ∈ Good, leftThreshold k ≤ cap)
    (hRcap : ∀ k ∈ Good, rightThreshold k ≤ cap)
    (hfreeLCard : ∀ k ∈ Good,
      cap - matchingSideLoad P f (left k) ≤ ((freeL k).card : ℝ))
    (hfreeRCard : ∀ k ∈ Good,
      cap - matchingSideLoad P f (right k) ≤ ((freeR k).card : ℝ)) :
    ∃ (k : κ) (swap : Bool)
      (fC : RootedComponentVertex T Sseed c → V),
      k ∈ Good ∧
      Function.Injective fC ∧
      Disjoint (Finset.univ.image fC) (P.image f) ∧
      G.Adj anchor (fC (componentLocalRoot T Sseed D c)) ∧
      (∀ x y, componentLocalParent T Sseed D c x = some y →
        G.Adj (fC x) (fC y)) ∧
      (∀ s ∈ componentSeeds T Sseed c.1,
        ∀ x : RootedComponentVertex T Sseed c,
          parent s = some x.1 → fC x ∈ retained head) ∧
      (∀ x, fC x ∈ matchingRegion (routeColour x.1)) ∧
      HPMatchingPacked
        (P ∪ componentNonseedVertices T Sseed c.1)
        (glueOnBlock (componentNonseedVertices T Sseed c.1) f
          (liftComponentMap T Sseed c fC))
        left right leftThreshold rightThreshold margin τ := by
  let a : ℝ :=
    (componentSideCount T Sseed col c (D.root c) false : ℕ)
  let b : ℝ :=
    (componentSideCount T Sseed col c (D.root c) true : ℕ)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hab : a + b ≤ τ := by
    have hsum :=
      componentSideCount_false_add_true T Sseed col c (D.root c)
    have hsumReal :
        (componentSideCount T Sseed col c (D.root c) false : ℝ) +
            (componentSideCount T Sseed col c (D.root c) true : ℝ) =
          (Fintype.card (RootedComponentVertex T Sseed c) : ℝ) := by
      exact_mod_cast hsum
    dsimp [a, b]
    exact hsumReal.trans_le hcomponent
  obtain ⟨k, hk, swap, hroot, hroomL, hroomR, hpackNew⟩ :=
    restricted_hp_select_joint_surplus Good hGood
      (fun k => matchingSideLoad P f (left k))
      (fun k => matchingSideLoad P f (right k))
      leftThreshold rightThreshold
      (fun k => ((rootPoolL k).card : ℝ))
      (fun k => ((rootPoolR k).card : ℝ))
      a b cap margin τ err (Lnat : ℝ) (Lnat : ℝ)
      ha hb hab hpacked hsurplus htypL htypR hrootFromRoom
      hrootMargin hlocalMargin hLcap hRcap
  have hLfreeNat : Lnat ≤ (freeL k).card := by
    exact_mod_cast hroomL.trans (hfreeLCard k hk)
  have hRfreeNat : Lnat ≤ (freeR k).card := by
    exact_mod_cast hroomR.trans (hfreeRCard k hk)
  have himageFresh :
      ∀ {fC : RootedComponentVertex T Sseed c → V},
        (∀ x, fC x ∈ freeL k ∪ freeR k) →
        Disjoint (Finset.univ.image fC) (P.image f) := by
    intro fC hfside
    rw [Finset.disjoint_left]
    intro v hvImage hvOld
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hvImage
    rcases Finset.mem_union.mp (hfside x) with hxL | hxR
    · exact Finset.disjoint_left.mp (hfreeLFresh k hk) hxL hvOld
    · exact Finset.disjoint_left.mp (hfreeRFresh k hk) hxR hvOld
  cases hs : swap with
  | false =>
      have hrootNat : Lnat ≤ (rootPoolL k).card := by
        exact_mod_cast (by simpa [hs] using! hroot)
      have hcontactNat : Lnat ≤ (contactL k).card :=
        hrootNat.trans (Finset.card_le_card (hrootPoolL k hk))
      obtain ⟨fC, hfCinj, hfroot, hfside, hfadj, hfcontact⟩ :=
        hp_component_block_step T Sseed D hrank hparentAdj col hcol
          c hboundary G hε0 hε1 hd1
          (hleft k hk) (hright k hk) (huni k hk) (hdens k hk)
          ((hcontactL k hk).trans (hfreeL k hk))
          (hfreeR k hk) (hrootPoolL k hk)
          anchor (hrootAdjL k hk) Lnat hcontactNat hRfreeNat hrootNat
          (hLsig k hk) (hRsig k hk) (hpairRoom k hk)
      have hfUnion : ∀ x, fC x ∈ freeL k ∪ freeR k := by
        intro x
        by_cases hx : relativeComponentColor col (D.root c) x.1
        · exact Finset.mem_union_right _
            (by simpa [hx] using! hfside x)
        · exact Finset.mem_union_left _
            (hcontactL k hk (by simpa [hx] using! hfside x))
      have hfFresh := himageFresh hfUnion
      have hpackedNew :=
        hpMatchingPacked_glue_component T Sseed P col c (D.root c)
          f fC hfCinj left right leftThreshold rightThreshold
          margin τ k false (contactL k) (freeR k)
          ((hcontactL k hk).trans (hfreeL k hk))
          (hfreeR k hk) (hLR k)
          (fun j hj => hother k j hj.symm)
          (by simpa using! hfside) hpacked hBP
          (by simpa only [image_liftComponentMap] using! hfFresh)
          (by simpa [a, b, hs] using! hpackNew)
      refine ⟨k, false, fC, hk, hfCinj, hfFresh, hfroot, hfadj,
        ?_, ?_, hpackedNew⟩
      · intro s hsc x hsx
        exact hcontactLRet k hk (hfcontact s hsc x hsx)
      · intro x
        rw [hroute x]
        rcases Finset.mem_union.mp (hfUnion x) with hxL | hxR
        · exact hfreeLRegion k hk hxL
        · exact hfreeRRegion k hk hxR
  | true =>
      have hrootNat : Lnat ≤ (rootPoolR k).card := by
        exact_mod_cast (by simpa [hs] using! hroot)
      have hcontactNat : Lnat ≤ (contactR k).card :=
        hrootNat.trans (Finset.card_le_card (hrootPoolR k hk))
      have hdens' :
          d ≤ (G.edgeDensity (right k) (left k) : ℝ) := by
        simpa only [SimpleGraph.edgeDensity_comm] using! hdens k hk
      obtain ⟨fC, hfCinj, hfroot, hfside, hfadj, hfcontact⟩ :=
        hp_component_block_step T Sseed D hrank hparentAdj col hcol
          c hboundary G hε0 hε1 hd1
          (hright k hk) (hleft k hk) (huni k hk).symm hdens'
          ((hcontactR k hk).trans (hfreeR k hk))
          (hfreeL k hk) (hrootPoolR k hk)
          anchor (hrootAdjR k hk) Lnat hcontactNat hLfreeNat hrootNat
          (hRsig k hk) (hLsig k hk)
          (by simpa [max_comm] using! hpairRoom k hk)
      have hfUnion : ∀ x, fC x ∈ freeL k ∪ freeR k := by
        intro x
        by_cases hx : relativeComponentColor col (D.root c) x.1
        · exact Finset.mem_union_left _
            (by simpa [hx] using! hfside x)
        · exact Finset.mem_union_right _
            (hcontactR k hk (by simpa [hx] using! hfside x))
      have hfFresh := himageFresh hfUnion
      have hpackedNew :=
        hpMatchingPacked_glue_component T Sseed P col c (D.root c)
          f fC hfCinj left right leftThreshold rightThreshold
          margin τ k true (freeL k) (contactR k)
          (hfreeL k hk)
          ((hcontactR k hk).trans (hfreeR k hk)) (hLR k)
          (fun j hj => hother k j hj.symm)
          (by simpa using! hfside) hpacked hBP
          (by simpa only [image_liftComponentMap] using! hfFresh)
          (by simpa [a, b, hs] using! hpackNew)
      refine ⟨k, true, fC, hk, hfCinj, hfFresh, hfroot, hfadj,
        ?_, ?_, hpackedNew⟩
      · intro s hsc x hsx
        exact hcontactRRet k hk (hfcontact s hsc x hsx)
      · intro x
        rw [hroute x]
        rcases Finset.mem_union.mp (hfUnion x) with hxL | hxR
        · exact hfreeLRegion k hk hxL
        · exact hfreeRRegion k hk hxR

end Erdos550
