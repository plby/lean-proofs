import Mathlib
import ErdosProblems.Erdos550.HPDynamicEndpointPools
import ErdosProblems.Erdos550.HPMatchingComponentExtension

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Matching-wide extension from retained endpoint data

This wrapper constructs all state-dependent free sets and root pools from the
fixed retained endpoint sets.  The exact current image load and the retained
loss are the only deletions.  It therefore removes the auxiliary pool choices
from the component-extension interface used in the final off--Turán assembly.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

set_option maxHeartbeats 1000000 in
theorem hp_matching_dynamic_component_extension
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
    (left right retainedL retainedR : κ → Finset V)
    (retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (hleft : ∀ k ∈ Good, (left k).Nonempty)
    (hright : ∀ k ∈ Good, (right k).Nonempty)
    (huni : ∀ k ∈ Good, G.IsUniform ε (left k) (right k))
    (hdens : ∀ k ∈ Good,
      d ≤ (G.edgeDensity (left k) (right k) : ℝ))
    (hretL : ∀ k ∈ Good, retainedL k ⊆ left k)
    (hretR : ∀ k ∈ Good, retainedR k ⊆ right k)
    (hretLGlobal : ∀ k ∈ Good, retainedL k ⊆ retained head)
    (hretRGlobal : ∀ k ∈ Good, retainedR k ⊆ retained head)
    (hleftRegion : ∀ k ∈ Good, left k ⊆ matchingRegion head)
    (hrightRegion : ∀ k ∈ Good, right k ⊆ matchingRegion head)
    (hLR : ∀ k, Disjoint (left k) (right k))
    (hother : ∀ k j, k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j))
    (anchor : V)
    (f : A → V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ err cap retainedLoss : ℝ) (Lnat : ℕ)
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
    (hretLLoss : ∀ k ∈ Good, 0 < leftThreshold k →
      (((left k) \ retainedL k).card : ℝ) ≤ retainedLoss)
    (hretRLoss : ∀ k ∈ Good, 0 < rightThreshold k →
      (((right k) \ retainedR k).card : ℝ) ≤ retainedLoss)
    (hcapL : ∀ k ∈ Good,
      cap ≤ ((left k).card : ℝ))
    (hcapR : ∀ k ∈ Good,
      cap ≤ ((right k).card : ℝ))
    (hanchorL : ∀ k ∈ Good,
      leftThreshold k ≤
        (((left k).filter fun v => G.Adj anchor v).card : ℝ))
    (hanchorR : ∀ k ∈ Good,
      rightThreshold k ≤
        (((right k).filter fun v => G.Adj anchor v).card : ℝ))
    (herr0 : 0 ≤ err)
    (herr : retainedLoss ≤ err)
    (hrootFromRoom :
      2 * (Lnat : ℝ) + 2 * err ≤ (Lnat : ℝ) + margin)
    (hrootMargin : (Lnat : ℝ) + τ + err ≤ margin)
    (hlocalMargin : (Lnat : ℝ) + τ ≤ margin)
    (hLcap : ∀ k ∈ Good, leftThreshold k ≤ cap)
    (hRcap : ∀ k ∈ Good, rightThreshold k ≤ cap) :
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
  let used := P.image f
  let freeL : κ → Finset V :=
    fun k => hpFreeEndpoint used (left k) (left k)
  let freeR : κ → Finset V :=
    fun k => hpFreeEndpoint used (right k) (right k)
  let contactL : κ → Finset V :=
    fun k => hpFreeEndpoint used (left k) (retainedL k)
  let contactR : κ → Finset V :=
    fun k => hpFreeEndpoint used (right k) (retainedR k)
  let rootPoolL : κ → Finset V :=
    fun k => hpRootPool G anchor used (left k) (retainedL k)
  let rootPoolR : κ → Finset V :=
    fun k => hpRootPool G anchor used (right k) (retainedR k)
  apply hp_matching_component_extension
    T Sseed P D hrank hparentAdj col routeColour hcol c hboundary
    head hroute G hε0 hε1 hd1 Good hGood
    left right freeL freeR contactL contactR rootPoolL rootPoolR
    retained matchingRegion
  · exact hleft
  · exact hright
  · exact huni
  · exact hdens
  · intro k hk
    exact hpFreeEndpoint_subset_endpoint used (left k) (left k)
  · intro k hk
    exact hpFreeEndpoint_subset_endpoint used (right k) (right k)
  · intro k hk
    exact hpFreeEndpoint_mono_retained
      used (left k) (retainedL k) (left k) (hretL k hk)
  · intro k hk
    exact hpFreeEndpoint_mono_retained
      used (right k) (retainedR k) (right k) (hretR k hk)
  · intro k hk
    exact hpRootPool_subset_free G anchor used (left k) (retainedL k)
  · intro k hk
    exact hpRootPool_subset_free G anchor used (right k) (retainedR k)
  · exact hLR
  · exact hother
  · intro k hk
    exact (hpFreeEndpoint_subset_retained used (left k) (retainedL k)).trans
      (hretLGlobal k hk)
  · intro k hk
    exact (hpFreeEndpoint_subset_retained used (right k) (retainedR k)).trans
      (hretRGlobal k hk)
  · intro k hk
    exact (hpFreeEndpoint_subset_endpoint used (left k) (left k)).trans
      (hleftRegion k hk)
  · intro k hk
    exact (hpFreeEndpoint_subset_endpoint used (right k) (right k)).trans
      (hrightRegion k hk)
  · intro k hk
    exact hpRootPool_adj G anchor used (left k) (retainedL k)
  · intro k hk
    exact hpRootPool_adj G anchor used (right k) (retainedR k)
  · intro k hk
    simpa [freeL, used] using!
      hpFreeEndpoint_disjoint_used used (left k) (left k)
  · intro k hk
    simpa [freeR, used] using!
      hpFreeEndpoint_disjoint_used used (right k) (right k)
  · exact hpacked
  · exact hBP
  · exact hcomponent
  · exact hLsig
  · exact hRsig
  · exact hpairRoom
  · exact hsurplus
  · intro k hk
    by_cases ht : 0 < leftThreshold k
    · have h :=
        hpRootPool_card_lower G anchor used (left k) (retainedL k)
          (leftThreshold k) 0 retainedLoss (by simpa using! hanchorL k hk)
          (hretLLoss k hk ht)
      simpa [rootPoolL, used, matchingSideLoad] using!
        (show leftThreshold k -
            (((used ∩ left k).card : ℝ)) - err ≤
              (hpRootPool G anchor used (left k) (retainedL k)).card by
          linarith)
    · have hload :
          (0 : ℝ) ≤ ((used ∩ left k).card : ℕ) := by positivity
      have hcard :
          (0 : ℝ) ≤
            (hpRootPool G anchor used (left k) (retainedL k)).card := by
        positivity
      simp only [rootPoolL, matchingSideLoad]
      linarith
  · intro k hk
    by_cases ht : 0 < rightThreshold k
    · have h :=
        hpRootPool_card_lower G anchor used (right k) (retainedR k)
          (rightThreshold k) 0 retainedLoss (by simpa using! hanchorR k hk)
          (hretRLoss k hk ht)
      simpa [rootPoolR, used, matchingSideLoad] using!
        (show rightThreshold k -
            (((used ∩ right k).card : ℝ)) - err ≤
              (hpRootPool G anchor used (right k) (retainedR k)).card by
          linarith)
    · have hload :
          (0 : ℝ) ≤ ((used ∩ right k).card : ℕ) := by positivity
      have hcard :
          (0 : ℝ) ≤
            (hpRootPool G anchor used (right k) (retainedR k)).card := by
        positivity
      simp only [rootPoolR, matchingSideLoad]
      linarith
  · exact hrootFromRoom
  · exact hrootMargin
  · exact hlocalMargin
  · exact hLcap
  · exact hRcap
  · intro k hk
    have hempty : left k \ left k = ∅ := Finset.sdiff_self _
    have hzero : (((left k \ left k).card : ℕ) : ℝ) ≤ 0 := by
      rw [hempty]
      simp
    simpa [freeL, used, matchingSideLoad] using!
      hpFreeEndpoint_card_lower used (left k) (left k)
        cap 0 hzero (by simpa using! hcapL k hk)
  · intro k hk
    have hempty : right k \ right k = ∅ := Finset.sdiff_self _
    have hzero : (((right k \ right k).card : ℕ) : ℝ) ≤ 0 := by
      rw [hempty]
      simp
    simpa [freeR, used, matchingSideLoad] using!
      hpFreeEndpoint_card_lower used (right k) (right k)
        cap 0 hzero (by simpa using! hcapR k hk)

end Erdos550
