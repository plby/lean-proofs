import Mathlib
import ErdosProblems.Erdos550.HPDirectStaticEmbedding
import ErdosProblems.Erdos550.HPLoadAccounting
import ErdosProblems.Erdos550.HPMatchingDynamicExtension
import ErdosProblems.Erdos550.HPRetainedRegion
import ErdosProblems.Erdos550.ParityComponentDemand

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Parity-routed embedding from allocated matching resources

This is the combinatorial embedding theorem for the direct off--Turán
route.  Complete matching edges are assigned to the two head colours.  At each
ready component, a state-independent allocated-surplus bound controls the
state-dependent matching load, and the dynamic endpoint wrapper embeds the
component while preserving packedness and all deferred contacts.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

set_option maxHeartbeats 1500000 in
theorem hp_parity_matching_tree_embedding
    {A : Type} {V κ : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype κ] [DecidableEq κ]
    (T : SimpleGraph A)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sseed : Finset A)
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (D : RootedSeedComponentData T Sseed parent)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hboundary : ∀ c : NonseedComponent T Sseed,
      ∀ a ∈ componentSeeds T Sseed c.1,
        ∀ b ∈ componentSeeds T Sseed c.1, col a = col b)
    (headCore : Bool → Finset V)
    (K : Bool → Finset κ)
    (left right retainedL retainedR : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) (hτ : 0 ≤ τ)
    (hheadMatching :
      ∀ b k, Disjoint (headCore b) (left k) ∧
        Disjoint (headCore b) (right k))
    (hheadRegion : ∀ b r,
      Disjoint (headCore b) (hpMatchingRegion (K r) left right))
    (hregionDisj :
      Disjoint (hpMatchingRegion (K false) left right)
        (hpMatchingRegion (K true) left right))
    (hcore : ∀ b, Sseed.card < (headCore b).card)
    (hheadAdj : ∀ b c, b ≠ c → ∀ u ∈ headCore c,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hretLSeedDegree : ∀ b k, k ∈ K b → ∀ u ∈ retainedL k,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hretRSeedDegree : ∀ b k, k ∈ K b → ∀ u ∈ retainedR k,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hleft : ∀ k, (left k).Nonempty)
    (hright : ∀ k, (right k).Nonempty)
    (hLR : ∀ k, Disjoint (left k) (right k))
    (hother : ∀ k j, k ≠ j →
      Disjoint (left k ∪ right k) (left j ∪ right j))
    (hretL : ∀ k, retainedL k ⊆ left k)
    (hretR : ∀ k, retainedR k ⊆ right k)
    {ε d : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hd1 : d ≤ 1)
    (huni : ∀ k, G.IsUniform ε (left k) (right k))
    (hdens : ∀ k, d ≤ (G.edgeDensity (left k) (right k) : ℝ))
    (Good : Bool → V → Finset κ)
    (hGoodSubset : ∀ b u, Good b u ⊆ K b)
    (hGood : ∀ b u, u ∈ headCore b →
      0 < parityRouteDemand T Sseed D col b →
      (Good b u).Nonempty)
    (hanchorL : ∀ b u, u ∈ headCore b → ∀ k ∈ Good b u,
      leftThreshold k ≤
        (((left k).filter fun v => G.Adj u v).card : ℝ))
    (hanchorR : ∀ b u, u ∈ headCore b → ∀ k ∈ Good b u,
      rightThreshold k ≤
        (((right k).filter fun v => G.Adj u v).card : ℝ))
    (retainedLoss err cap : ℝ) (Lnat : ℕ)
    (hcomponent : ∀ c : NonseedComponent T Sseed,
      (Fintype.card (RootedComponentVertex T Sseed c) : ℝ) ≤ τ)
    (hLsig : ∀ k, ε * ((left k).card : ℝ) ≤ (Lnat : ℝ))
    (hRsig : ∀ k, ε * ((right k).card : ℝ) ≤ (Lnat : ℝ))
    (hpairRoom : ∀ c : NonseedComponent T Sseed, ∀ k,
      ε * (max (left k).card (right k).card : ℝ) +
          (Fintype.card (RootedComponentVertex T Sseed c) : ℝ)
        ≤ (d - 2 * ε) * (Lnat : ℝ))
    (hretLLoss : ∀ k, 0 < leftThreshold k →
      (((left k) \ retainedL k).card : ℝ) ≤ retainedLoss)
    (hretRLoss : ∀ k, 0 < rightThreshold k →
      (((right k) \ retainedR k).card : ℝ) ≤ retainedLoss)
    (hcapL : ∀ k, cap ≤ ((left k).card : ℝ))
    (hcapR : ∀ k, cap ≤ ((right k).card : ℝ))
    (herr0 : 0 ≤ err)
    (herr : retainedLoss ≤ err)
    (hrootFromRoom :
      2 * (Lnat : ℝ) + 2 * err ≤ (Lnat : ℝ) + margin)
    (hrootMargin : (Lnat : ℝ) + τ + err ≤ margin)
    (hlocalMargin : (Lnat : ℝ) + τ ≤ margin)
    (hLcap : ∀ k, leftThreshold k ≤ cap)
    (hRcap : ∀ k, rightThreshold k ≤ cap)
    (hallocated : ∀ b u, u ∈ headCore b →
      0 < parityRouteDemand T Sseed D col b →
      parityRouteDemand T Sseed D col b +
          ((Good b u).card : ℝ) * ((Lnat : ℝ) + margin) ≤
        ∑ k ∈ Good b u, (leftThreshold k + rightThreshold k)) :
    T ⊑ G := by
  let routeColour : A → Bool :=
    parityRouteColour T Sseed D col
  let matchingRegion : Bool → Finset V :=
    fun b => hpMatchingRegion (K b) left right
  let retained : Bool → Finset V :=
    fun b => hpRetainedRegion (K b) retainedL retainedR
  letI : DecidableRel T.Adj := Classical.decRel _
  apply hp_direct_tree_embedding_static_seed
    T G Sseed parent rank hrank hedge D col routeColour
    headCore retained matchingRegion left right
    leftThreshold rightThreshold margin τ hτ
    hheadMatching
  · exact hheadRegion
  · exact hcol
  · exact hcore
  · exact hheadAdj
  · intro b u hu
    have hdeg :
        (Sseed.card : ℝ) <
          (((headCore b).filter fun v => G.Adj v u).card : ℝ) := by
      apply hpRetainedRegion_degree G (K b) retainedL retainedR
        (headCore b) (Sseed.card : ℝ)
      · intro k hk v hv
        exact_mod_cast hretLSeedDegree b k hk v hv
      · intro k hk v hv
        exact_mod_cast hretRSeedDegree b k hk v hv
      · exact hu
    exact_mod_cast hdeg
  · intro P f hPblock hfinj hInv a haP hready haSeed
    let c := nonseedComponentOf T Sseed a haSeed
    have haroot : a = D.root c :=
      ready_nonseed_eq_component_root T Sseed P parent D hPblock
        a haSeed haP hready
    let upper := componentUpperSeed T Sseed D c
    have hrootUpper : parent (D.root c) = some upper := by
      exact componentRoot_parent_upperSeed T Sseed D c
    have hupperP : upper ∈ P := by
      apply hready upper
      simpa [haroot] using! hrootUpper
    let b := componentHeadColour T Sseed D col c
    have hb : b = col upper := by rfl
    have hanchorCore : f upper ∈ headCore b := by
      rw [hb]
      exact hInv.1 upper hupperP (componentUpperSeed_mem T Sseed D c)
    have hroutePos :
        0 < parityRouteDemand T Sseed D col b := by
      exact parityRouteDemand_pos_of_component T Sseed D col c
    have hGoodSub : Good b (f upper) ⊆ K b :=
      hGoodSubset b (f upper)
    have hload :
        (∑ k ∈ Good b (f upper),
            (matchingSideLoad P f (left k) +
              matchingSideLoad P f (right k))) ≤
          parityRouteDemand T Sseed D col b := by
      apply (matching_load_sum_le_route_card_on_subset
        Sseed P f col routeColour headCore K
        (Good b (f upper)) left right b hGoodSub
        hInv.1 hInv.2.2.1 hheadRegion hregionDisj
        (fun r k hk => hLR k)
        (fun r k hk j hj hkj => hother k j hkj)).trans
      exact route_filter_card_eq_parityRouteDemand
        T Sseed P D col b
    have hsurplus :
        (∑ k ∈ Good b (f upper),
            (matchingSideLoad P f (left k) +
              matchingSideLoad P f (right k))) +
            ((Good b (f upper)).card : ℝ) *
              ((Lnat : ℝ) + margin) ≤
          ∑ k ∈ Good b (f upper),
            (leftThreshold k + rightThreshold k) :=
      matching_surplus_of_route_demand
        (Good b (f upper))
        (fun k => matchingSideLoad P f (left k))
        (fun k => matchingSideLoad P f (right k))
        leftThreshold rightThreshold
        (parityRouteDemand T Sseed D col b)
        ((Lnat : ℝ) + margin) hload
        (hallocated b (f upper) hanchorCore hroutePos)
    have hBP :
        Disjoint (componentNonseedVertices T Sseed c.1) P := by
      have hblock :
          tauFineBlock T Sseed a =
            componentNonseedVertices T Sseed c.1 := by
        rw [tauFineBlock, dif_neg haSeed]
      rw [← hblock]
      exact tauFineBlock_disjoint_of_not_mem
        T Sseed P hPblock haP
    have hroute :
        ∀ x : RootedComponentVertex T Sseed c,
          routeColour x.1 = b := by
      intro x
      exact parityRouteColour_component T Sseed D col c x.2
    obtain ⟨k, swap, fC, hk, hfCinj, hfCfresh, hfCroot,
        hfCinternal, hfCcontact, hfCregion, hpacked⟩ :=
      hp_matching_dynamic_component_extension
        T Sseed P D hrank hparentAdj col routeColour hcol
        c (hboundary c) b hroute G
        hε0 hε1 hd1 (Good b (f upper))
        (hGood b (f upper) hanchorCore hroutePos)
        left right retainedL retainedR retained matchingRegion
        (fun k hk => hleft k) (fun k hk => hright k)
        (fun k hk => huni k) (fun k hk => hdens k)
        (fun k hk => hretL k) (fun k hk => hretR k)
        (fun k hk => retainedL_subset_hpRetainedRegion
          (K b) retainedL retainedR (hGoodSub hk))
        (fun k hk => retainedR_subset_hpRetainedRegion
          (K b) retainedL retainedR (hGoodSub hk))
        (fun k hk => left_subset_hpMatchingRegion
          (K b) left right (hGoodSub hk))
        (fun k hk => right_subset_hpMatchingRegion
          (K b) left right (hGoodSub hk))
        hLR hother (f upper) f
        leftThreshold rightThreshold margin τ err cap retainedLoss Lnat
        hInv.2.2.2 hBP (hcomponent c)
        (fun k hk => hLsig k) (fun k hk => hRsig k)
        (fun k hk => hpairRoom c k) hsurplus
        (fun k hk => hretLLoss k) (fun k hk => hretRLoss k)
        (fun k hk => hcapL k) (fun k hk => hcapR k)
        (hanchorL b (f upper) hanchorCore)
        (hanchorR b (f upper) hanchorCore)
        herr0 herr hrootFromRoom hrootMargin hlocalMargin
        (fun k hk => hLcap k) (fun k hk => hRcap k)
    refine ⟨fC, hfCinj, hfCfresh, ?_, ?_, ?_, hfCregion, hpacked⟩
    · intro x y hxy
      exact hfCinternal x y
        (componentLocalParent_eq_some_of_global T Sseed D c hxy)
    · intro y hy
      have hyUpper : y = upper := by
        rw [hrootUpper] at hy
        exact Option.some.inj hy.symm
      subst y
      exact
        (G.adj_comm (f upper)
          (fC (componentLocalRoot T Sseed D c))).mp hfCroot
    · intro s hsSeed x hsx
      have hxNonseed :
          x.1 ∈ componentNonseedVertices T Sseed c.1 := by
        simpa [c] using! x.2
      have hxSupp : x.1 ∈ c.1.supp :=
        (mem_componentNonseedVertices_iff T Sseed c.1 x.1).mp
          hxNonseed |>.2
      have hsComp : s ∈ componentSeeds T Sseed c.1 :=
        seed_mem_componentSeeds_of_adj T Sseed c.1 hsSeed
          hxSupp (hparentAdj s x.1 hsx)
      have hupperComp :
          upper ∈ componentSeeds T Sseed c.1 := by
        apply seed_mem_componentSeeds_of_adj T Sseed c.1
          (componentUpperSeed_mem T Sseed D c)
        · exact
            (mem_componentNonseedVertices_iff
              T Sseed c.1 (D.root c)).mp (D.root_mem c) |>.2
        · exact (hparentAdj (D.root c) upper hrootUpper).symm
      have hsColour : col s = b := by
        simpa [b, componentHeadColour] using!
          hboundary c s hsComp upper hupperComp
      rw [hsColour]
      exact hfCcontact s hsComp x hsx

end Erdos550
