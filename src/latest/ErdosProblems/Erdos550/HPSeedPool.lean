import Mathlib
import ErdosProblems.Erdos550.HPDirectInvariant
import ErdosProblems.Erdos550.SeedSingletonExtension

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dynamic seed pools for the parity-refined embedding

Only seed vertices occupy the two head cores; all processed nonseeds lie in
the disjoint regular-matching region.  Consequently the number of already
used vertices in a seed pool is bounded by the separator size, independently
of how many shrub vertices have already been embedded.
-/

open Finset

namespace Erdos550

open Classical

/-- Head-core vertices adjacent to the already embedded parent of `a`.  For a
root seed (whose parent is `none`) this is the whole head core. -/
noncomputable def seedCandidatePool
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parent : A → Option A)
    (col : A → Bool) (headCore : Bool → Finset V)
    (f : A → V) (a : A) : Finset V :=
  (headCore (col a)).filter fun v =>
    ∀ y, parent a = some y → G.Adj v (f y)

lemma seedCandidatePool_subset
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parent : A → Option A)
    (col : A → Bool) (headCore : Bool → Finset V)
    (f : A → V) (a : A) :
    seedCandidatePool G parent col headCore f a ⊆ headCore (col a) :=
  Finset.filter_subset _ _

lemma seedCandidatePool_parent_adj
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parent : A → Option A)
    (col : A → Bool) (headCore : Bool → Finset V)
    (f : A → V) (a : A) :
    ∀ v ∈ seedCandidatePool G parent col headCore f a,
      ∀ y, parent a = some y → G.Adj v (f y) := by
  intro v hv y hay
  exact (Finset.mem_filter.mp hv).2 y hay

/-- The used part of a head-core pool is charged only to processed seeds. -/
lemma processed_image_inter_headCore_card_le_seed
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed P : Finset A) (f : A → V)
    (routeColour : A → Bool)
    (head : Finset V) (matchingRegion : Bool → Finset V)
    (hnonseed : ∀ x ∈ P, x ∉ Sseed →
      f x ∈ matchingRegion (routeColour x))
    (hdisj : ∀ b, Disjoint head (matchingRegion b))
    (pool : Finset V) (hpool : pool ⊆ head) :
    (P.image f ∩ pool).card ≤ Sseed.card := by
  have hsub :
      P.image f ∩ pool ⊆ (P ∩ Sseed).image f := by
    intro v hv
    obtain ⟨hvImage, hvPool⟩ := Finset.mem_inter.mp hv
    obtain ⟨x, hxP, rfl⟩ := Finset.mem_image.mp hvImage
    have hxSeed : x ∈ Sseed := by
      by_contra hxNot
      exact Finset.disjoint_left.mp (hdisj (routeColour x))
        (hpool hvPool) (hnonseed x hxP hxNot)
    exact Finset.mem_image.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hxP, hxSeed⟩, rfl⟩
  calc
    (P.image f ∩ pool).card ≤ ((P ∩ Sseed).image f).card :=
      Finset.card_le_card hsub
    _ ≤ (P ∩ Sseed).card := Finset.card_image_le
    _ ≤ Sseed.card :=
      Finset.card_le_card Finset.inter_subset_right

/-- Separator-size room in the dynamic pool supplies the exact freshness
inequality used by the singleton extension. -/
lemma seedCandidatePool_fresh_card
    {A V : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed P : Finset A) (f : A → V)
    (routeColour : A → Bool)
    (head pool : Finset V) (matchingRegion : Bool → Finset V)
    (hnonseed : ∀ x ∈ P, x ∉ Sseed →
      f x ∈ matchingRegion (routeColour x))
    (hdisj : ∀ b, Disjoint head (matchingRegion b))
    (hpool : pool ⊆ head)
    (hroom : Sseed.card < pool.card) :
    (P.image f ∩ pool).card < pool.card :=
  (processed_image_inter_headCore_card_le_seed
    Sseed P f routeColour head matchingRegion hnonseed hdisj pool hpool).trans_lt hroom

/-- The dynamic seed-pool inequality follows from three static facts: both
head cores themselves are larger than the separator, opposite head-core
vertices see more than the separator into one another, and every retained
matching vertex sees more than the separator into its designated head core. -/
lemma seedCandidatePool_card_gt
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sseed P : Finset A) (parent : A → Option A)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (f : A → V)
    (hInv : HPDirectInvariant Sseed parent col routeColour
      headCore retained matchingRegion CLeft CRight
      leftThreshold rightThreshold margin τ P f)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hcore : ∀ b, Sseed.card < (headCore b).card)
    (hheadAdj : ∀ b c, b ≠ c → ∀ u ∈ headCore c,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (hretainedAdj : ∀ b, ∀ u ∈ retained b,
      Sseed.card <
        ((headCore b).filter fun v => G.Adj v u).card)
    (a : A) (haSeed : a ∈ Sseed)
    (hready : ∀ y, parent a = some y → y ∈ P) :
    Sseed.card <
      (seedCandidatePool G parent col headCore f a).card := by
  cases hpa : parent a with
  | none =>
      simpa [seedCandidatePool, hpa] using! hcore (col a)
  | some y =>
      have hyP : y ∈ P := hready y hpa
      have hdegree :
          Sseed.card <
            ((headCore (col a)).filter fun v => G.Adj v (f y)).card := by
        by_cases hySeed : y ∈ Sseed
        · exact hheadAdj (col a) (col y) (hcol a y hpa)
            (f y) (hInv.1 y hyP hySeed)
        · exact hretainedAdj (col a) (f y)
            (hInv.2.1 a haSeed y hyP hySeed hpa)
      simpa [seedCandidatePool, hpa] using! hdegree

end Erdos550
