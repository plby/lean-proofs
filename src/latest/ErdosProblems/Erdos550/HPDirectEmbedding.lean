import Mathlib
import ErdosProblems.Erdos550.ComponentFreshExtension
import ErdosProblems.Erdos550.HPDirectInvariant
import ErdosProblems.Erdos550.HPSeedPool
import ErdosProblems.Erdos550.StatefulTauFineEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Stateful parity-refined matching embedding

This is the induction theorem used in the direct off--Turán route.  It reduces the
whole tree embedding to two concrete resource statements:

* every ready seed has more than `|Sseed|` candidates in its dynamic head pool;
* every ready nonseed component has one fresh rooted-pair embedding preserving
  retained contacts, matching support, and matching-wide packedness.

All ordering, injective gluing, deferred parent edges, and the final graph-copy
packaging are proved here.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

set_option maxHeartbeats 800000 in
theorem hp_direct_tree_embedding
    {A : Type} {V κ : Type*}
    [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq κ]
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sseed : Finset A)
    (parent : A → Option A) (rank : A → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (D : RootedSeedComponentData T Sseed parent)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) (hτ : 0 ≤ τ)
    (hheadMatching :
      ∀ b k, Disjoint (headCore b) (CLeft k) ∧
        Disjoint (headCore b) (CRight k))
    (hheadRegion : ∀ b r, Disjoint (headCore b) (matchingRegion r))
    (hseedRoom :
      ∀ (P : Finset A) (f : A → V),
        IsBlockClosed (tauFineBlock T Sseed) P →
        Set.InjOn f P →
        HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
          CLeft CRight leftThreshold rightThreshold margin τ P f →
        ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
          a ∈ Sseed →
          Sseed.card <
            (seedCandidatePool G parent col headCore f a).card)
    (hcomponent :
      ∀ (P : Finset A) (f : A → V),
        IsBlockClosed (tauFineBlock T Sseed) P →
        Set.InjOn f P →
        HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
          CLeft CRight leftThreshold rightThreshold margin τ P f →
        ∀ a ∉ P, (∀ y, parent a = some y → y ∈ P) →
          ∀ haSeed : a ∉ Sseed,
        let c := nonseedComponentOf T Sseed a haSeed
        ∃ fC : RootedComponentVertex T Sseed c → V,
          Function.Injective fC ∧
          Disjoint (Finset.univ.image fC) (P.image f) ∧
          (∀ (x y : RootedComponentVertex T Sseed c),
            parent x.1 = some y.1 → G.Adj (fC x) (fC y)) ∧
          (∀ y, parent (D.root c) = some y →
            G.Adj (fC (componentLocalRoot T Sseed D c)) (f y)) ∧
          (∀ s ∈ Sseed, ∀ x : RootedComponentVertex T Sseed c,
            parent s = some x.1 → fC x ∈ retained (col s)) ∧
          (∀ x, fC x ∈ matchingRegion (routeColour x.1)) ∧
          HPMatchingPacked
            (P ∪ componentNonseedVertices T Sseed c.1)
            (glueOnBlock (componentNonseedVertices T Sseed c.1) f
              (liftComponentMap T Sseed c fC))
            CLeft CRight leftThreshold rightThreshold margin τ) :
    T ⊑ G := by
  let Inv : Finset A → (A → V) → Prop :=
    HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ
  apply stateful_tauFine_graph_embedding T G Sseed parent rank
    hrank hedge D Inv
  · exact hpDirectInvariant_empty Sseed parent col routeColour headCore retained
      matchingRegion CLeft CRight leftThreshold rightThreshold
      margin τ hτ _
  · intro P f hPblock _hPdown hfinj _hfadj hInv a haP hready haSeed
    let pool := seedCandidatePool G parent col headCore f a
    have hpoolHead : pool ⊆ headCore (col a) :=
      seedCandidatePool_subset G parent col headCore f a
    have hfreshCard :
        (P.image f ∩ pool).card < pool.card := by
      apply seedCandidatePool_fresh_card Sseed P f routeColour
        (headCore (col a)) pool matchingRegion hInv.2.2.1
        (hheadRegion (col a)) hpoolHead
      exact hseedRoom P f hPblock hfinj hInv a haP hready haSeed
    rw [tauFineBlock, dif_pos haSeed]
    apply seed_singleton_fresh_extension G parent Inv P f a haP
      hready pool hfreshCard
      (seedCandidatePool_parent_adj G parent col headCore f a)
    intro v hvPool hvUnused
    let g : A → V := fun x =>
      if x = a then v else Classical.arbitrary V
    have hBP : Disjoint ({a} : Finset A) P := by
      simp [Finset.disjoint_left, haP]
    have himg : Disjoint (({a} : Finset A).image g) (P.image f) := by
      rw [Finset.disjoint_left]
      intro z hzNew hzOld
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzNew
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      exact hvUnused (by simpa [g] using! hzOld)
    have hcore : g a ∈ headCore (col a) := by
      simpa [g] using! hpoolHead hvPool
    have hleft : ∀ k, Disjoint (({a} : Finset A).image g) (CLeft k) := by
      intro k
      rw [Finset.disjoint_left]
      intro z hzNew hzLeft
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzNew
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      exact Finset.disjoint_left.mp (hheadMatching (col a) k).1
        hcore hzLeft
    have hright : ∀ k, Disjoint (({a} : Finset A).image g) (CRight k) := by
      intro k
      rw [Finset.disjoint_left]
      intro z hzNew hzRight
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hzNew
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      exact Finset.disjoint_left.mp (hheadMatching (col a) k).2
        hcore hzRight
    have hnew :=
      hpDirectInvariant_seed_glue Sseed parent col routeColour headCore retained
        matchingRegion CLeft CRight leftThreshold rightThreshold
        margin τ P f g a hInv haSeed hcore hBP himg hleft hright
    have hmap :
        glueOnBlock ({a} : Finset A) f g =
          (fun x => if x = a then v else f x) := by
      funext x
      by_cases hxa : x = a <;> simp [glueOnBlock, g, hxa]
    simpa [hmap] using! hnew
  · intro P f hPblock _hPdown hfinj _hfadj hInv a haP hready haSeed
    let c := nonseedComponentOf T Sseed a haSeed
    obtain ⟨fC, hfCinj, hfCfresh, hfCinternal, hfCroot,
        hfCcontact, hfCregion, hpacked⟩ :=
      hcomponent P f hPblock hfinj hInv a haP hready haSeed
    have haroot :
        a = D.root (nonseedComponentOf T Sseed a haSeed) :=
      ready_nonseed_eq_component_root T Sseed P parent D hPblock
        a haSeed haP hready
    have hblock :
        tauFineBlock T Sseed a =
          componentNonseedVertices T Sseed c.1 := by
      rw [tauFineBlock, dif_neg haSeed]
    have hBP :
        Disjoint (componentNonseedVertices T Sseed c.1) P := by
      rw [← hblock]
      exact tauFineBlock_disjoint_of_not_mem T Sseed P hPblock haP
    have hBSeed :
        Disjoint (componentNonseedVertices T Sseed c.1) Sseed := by
      rw [Finset.disjoint_left]
      intro x hxB hxSeed
      exact (mem_componentNonseedVertices_iff T Sseed c.1 x).mp hxB |>.1
        hxSeed
    let g := liftComponentMap T Sseed c fC
    have hcontact :
        ∀ s ∈ Sseed, ∀ x ∈ componentNonseedVertices T Sseed c.1,
          parent s = some x → g x ∈ retained (col s) := by
      intro s hs x hx hsx
      simpa [g, liftComponentMap, hx] using!
        hfCcontact s hs (⟨x, hx⟩ : RootedComponentVertex T Sseed c) hsx
    have hregion :
        ∀ x ∈ componentNonseedVertices T Sseed c.1,
          g x ∈ matchingRegion (routeColour x) := by
      intro x hx
      simpa [g, liftComponentMap, hx] using!
        hfCregion (⟨x, hx⟩ : RootedComponentVertex T Sseed c)
    have hInvNew :=
      hpDirectInvariant_component_glue Sseed parent col routeColour headCore retained
        matchingRegion CLeft CRight leftThreshold rightThreshold
        margin τ P (componentNonseedVertices T Sseed c.1) f g
        hInv hBP hBSeed hcontact hregion hpacked
    apply component_fresh_block_extension T G Sseed P parent D hPblock
      f Inv a haSeed haP hready c rfl fC hfCinj hfCfresh
      hfCinternal hfCroot
    simpa [hblock, g] using! hInvNew

end Erdos550
