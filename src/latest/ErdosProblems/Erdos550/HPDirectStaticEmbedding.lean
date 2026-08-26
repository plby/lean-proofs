import Mathlib
import ErdosProblems.Erdos550.HPDirectEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Static seed resources for the direct off--Turán embedding

The induction theorem asks for a dynamic fresh-pool estimate at every ready
seed.  This wrapper derives that estimate from the fixed head-core and
retained-contact degree bounds, leaving the matching-wide component extension
as its final input.
-/

open Finset SimpleGraph

namespace Erdos550

open Classical

set_option maxHeartbeats 800000 in
theorem hp_direct_tree_embedding_static_seed
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
    (hheadRegion : ∀ b r,
      Disjoint (headCore b) (matchingRegion r))
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hcore : ∀ b, Sseed.card < (headCore b).card)
    (hheadAdj : ∀ b c, b ≠ c → ∀ u ∈ headCore c,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hretainedAdj : ∀ b, ∀ u ∈ retained b,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hcomponent :
      ∀ (P : Finset A) (f : A → V),
        IsBlockClosed (tauFineBlock T Sseed) P →
        Set.InjOn f P →
        HPDirectInvariant Sseed parent col routeColour
          headCore retained matchingRegion CLeft CRight
          leftThreshold rightThreshold margin τ P f →
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
  apply hp_direct_tree_embedding T G Sseed parent rank hrank hedge D
    col routeColour headCore retained matchingRegion CLeft CRight
    leftThreshold rightThreshold margin τ hτ
    hheadMatching hheadRegion
  · intro P f hPblock hfinj hInv a haP hready haSeed
    exact seedCandidatePool_card_gt G Sseed P parent col routeColour
      headCore retained matchingRegion CLeft CRight
      leftThreshold rightThreshold margin τ f hInv hcol
      hcore hheadAdj hretainedAdj a haSeed hready
  · exact hcomponent

end Erdos550
