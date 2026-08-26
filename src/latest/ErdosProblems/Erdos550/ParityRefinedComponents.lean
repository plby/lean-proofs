import Mathlib
import ErdosProblems.Erdos550.ParityRefinedSeparator
import ErdosProblems.Erdos550.TauFineSingleNeighbor

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Components after the parity refinement

This file proves the component facts behind the parity repair.  The key rooted
tree observation is that the old upper boundary seed meets its old component
only at the component root.  Consequently, when a parity-bad root is promoted,
the upper boundary disappears from every remaining component; the only
possible old boundary is the unique lower seed, which has the same tree colour
as the promoted root.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The upper boundary seed of a rooted deleted component is adjacent inside
that component only to its root. -/
lemma componentUpperSeed_adj_eq_root
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A} {rank : A → ℕ}
    (D : RootedSeedComponentRankData T S parent rank)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (c : NonseedComponent T S)
    {x : A}
    (hx : x ∈ componentNonseedVertices T S c.1)
    (hadj : T.Adj
      (componentUpperSeed T S D.toRootedSeedComponentData c) x) :
    x = D.root c := by
  let u := componentUpperSeed T S D.toRootedSeedComponentData c
  rcases hedge u x hadj with hux | hxu
  · have hxuRank : rank x < rank u := hrank u x hux
    have hurRank : rank u < rank (D.root c) :=
      hrank _ _ (componentRoot_parent_upperSeed T S
        D.toRootedSeedComponentData c)
    have hrx : rank (D.root c) ≤ rank x :=
      D.root_rank_min c x hx
    omega
  · by_contra hxr
    obtain ⟨y, hy, hxy⟩ :=
      D.parent_internal c x hx hxr
    rw [hxu] at hxy
    have huy : u = y := Option.some.inj hxy
    subst y
    have huNotS :=
      (mem_componentNonseedVertices_iff T S c.1 u).mp hy |>.1
    exact huNotS
      (componentUpperSeed_mem T S D.toRootedSeedComponentData c)

/-- A promoted root which is adjacent to a refined component belongs to the
old component containing that refined component. -/
lemma promotedRoot_mem_oldComponent_of_refined_attachment
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (S B : Finset A)
    (c : NonseedComponent T (S ∪ B))
    (v : A)
    (hv : v ∈ componentNonseedVertices T (S ∪ B) c.1)
    {p : A}
    (hpB : p ∈ B)
    (hpNotS : p ∉ S)
    (hp : p ∈ componentSeeds T (S ∪ B) c.1) :
    p ∈ ((seedDeleted T S).connectedComponentMk v).supp := by
  obtain ⟨x, hx, hpx⟩ :=
    component_attachment_witness T (S ∪ B) c hp
  have hvSupp :
      v ∈ c.1.supp :=
    (mem_componentNonseedVertices_iff T (S ∪ B) c.1 v).mp hv |>.2
  have hxSupp :
      x ∈ c.1.supp :=
    (mem_componentNonseedVertices_iff T (S ∪ B) c.1 x).mp hx |>.2
  have hxOld :=
    refined_component_support_mem_old T S B c.1 hvSupp hxSupp
  have hxNotNew :
      x ∉ S ∪ B :=
    (mem_componentNonseedVertices_iff T (S ∪ B) c.1 x).mp hx |>.1
  have hxNotS : x ∉ S := fun hxS =>
    hxNotNew (Finset.mem_union_left B hxS)
  exact component_supp_closed_of_nonseed_adj T S
    ((seedDeleted T S).connectedComponentMk v)
    hxOld hxNotS hpNotS hpx.symm

/-- Two promoted roots lying in one old nonseed component arise from the same
old indexed component and hence are equal. -/
lemma parityPromotionRoot_unique_in_oldComponent
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (d : NonseedComponent T S)
    {p q : A}
    (hpD : p ∈ componentNonseedVertices T S d.1)
    (hqD : q ∈ componentNonseedVertices T S d.1)
    (hp : p ∈ parityPromotionRoots T S D col)
    (hq : q ∈ parityPromotionRoots T S D col) :
    p = q := by
  obtain ⟨cp, hcpBad, hcp⟩ :=
    (mem_parityPromotionRoots_iff T S D col p).mp hp
  obtain ⟨cq, hcqBad, hcq⟩ :=
    (mem_parityPromotionRoots_iff T S D col q).mp hq
  have hcpD : cp = d := by
    have hpCp : p ∈ componentNonseedVertices T S cp.1 := by
      rw [← hcp]
      exact D.root_mem cp
    by_contra hne
    have hdisj :=
      componentNonseedVertices_pairwise_disjoint T S
        (by simp) (by simp) hne
    exact Finset.disjoint_left.mp hdisj hpCp hpD
  have hcqD : cq = d := by
    have hqCq : q ∈ componentNonseedVertices T S cq.1 := by
      rw [← hcq]
      exact D.root_mem cq
    by_contra hne
    have hdisj :=
      componentNonseedVertices_pairwise_disjoint T S
        (by simp) (by simp) hne
    exact Finset.disjoint_left.mp hdisj hqCq hqD
  rw [hcpD] at hcp
  rw [hcqD] at hcq
  exact hcp.symm.trans hcq

/-- An old component containing a promoted root is exactly the parity-bad
component which produced that root. -/
lemma parityPromotionRoot_component_bad
    (T : SimpleGraph A) (S : Finset A)
    {parent : A → Option A}
    (D : RootedSeedComponentData T S parent)
    (col : A → Bool)
    (d : NonseedComponent T S)
    {p : A}
    (hpD : p ∈ componentNonseedVertices T S d.1)
    (hp : p ∈ parityPromotionRoots T S D col) :
    d ∈ parityBadComponents T S D col := by
  obtain ⟨cp, hcpBad, hcp⟩ :=
    (mem_parityPromotionRoots_iff T S D col p).mp hp
  have hpCp : p ∈ componentNonseedVertices T S cp.1 := by
    rw [← hcp]
    exact D.root_mem cp
  by_contra hdBad
  have hne : cp ≠ d := fun h => hdBad (h ▸ hcpBad)
  have hdisj :=
    componentNonseedVertices_pairwise_disjoint T S
      (by simp) (by simp) hne
  exact Finset.disjoint_left.mp hdisj hpCp hpD

/-- The parity repair preserves the two-attachment bound and, more
importantly, makes all boundary seeds of every refined component have the same
global tree colour. -/
theorem parityRefined_component_boundary
    (T : SimpleGraph A) [DecidableRel T.Adj]
    (S : Finset A)
    {parent : A → Option A} {rank : A → ℕ}
    (D : RootedSeedComponentRankData T S parent rank)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hparentAdj : ∀ a b, parent a = some b → T.Adj a b)
    (hedge : ∀ a b, T.Adj a b →
      parent a = some b ∨ parent b = some a)
    (hattach : ∀ d : NonseedComponent T S,
      (componentSeeds T S d.1).card ≤ 2)
    (col : A → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (c : NonseedComponent T
      (S ∪ parityPromotionRoots T S
        D.toRootedSeedComponentData col)) :
    (componentSeeds T
        (S ∪ parityPromotionRoots T S
          D.toRootedSeedComponentData col) c.1).card ≤ 2 ∧
      ∀ a ∈ componentSeeds T
          (S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col) c.1,
        ∀ b ∈ componentSeeds T
          (S ∪ parityPromotionRoots T S
            D.toRootedSeedComponentData col) c.1,
          col a = col b := by
  let B := parityPromotionRoots T S D.toRootedSeedComponentData col
  obtain ⟨v, hv⟩ :=
    componentNonseedVertices_nonempty T (S ∪ B) c
  have hvNotNew : v ∉ S ∪ B :=
    (mem_componentNonseedVertices_iff T (S ∪ B) c.1 v).mp hv |>.1
  have hvNotS : v ∉ S := fun hvS =>
    hvNotNew (Finset.mem_union_left B hvS)
  let d : NonseedComponent T S :=
    nonseedComponentOf T S v hvNotS
  have hvD : v ∈ componentNonseedVertices T S d.1 :=
    mem_component_of_nonseed T S v hvNotS
  have suppOld : ∀ {x},
      x ∈ componentNonseedVertices T (S ∪ B) c.1 →
        x ∈ d.1.supp := by
    intro x hx
    have hvSupp :
        v ∈ c.1.supp :=
      (mem_componentNonseedVertices_iff T (S ∪ B) c.1 v).mp hv |>.2
    have hxSupp :
        x ∈ c.1.supp :=
      (mem_componentNonseedVertices_iff T (S ∪ B) c.1 x).mp hx |>.2
    simpa [d, nonseedComponentOf, seedComponent] using!
      (refined_component_support_mem_old T S B c.1 hvSupp hxSupp)
  have attachOld : ∀ {s},
      s ∈ componentSeeds T (S ∪ B) c.1 → s ∈ S →
        s ∈ componentSeeds T S d.1 := by
    intro s hs hsS
    obtain ⟨x, hx, hsx⟩ :=
      component_attachment_witness T (S ∪ B) c hs
    exact seed_mem_componentSeeds_of_adj T S d.1 hsS
      (suppOld hx) hsx
  have promotedInside : ∀ {p},
      p ∈ componentSeeds T (S ∪ B) c.1 → p ∈ B →
        p ∈ componentNonseedVertices T S d.1 := by
    intro p hp hpB
    have hpNotS : p ∉ S := by
      intro hpS
      exact Finset.disjoint_left.mp
        (parityPromotionRoots_disjoint T S
          D.toRootedSeedComponentData col) hpS hpB
    have hpSupp :
        p ∈ d.1.supp := by
      simpa [d, nonseedComponentOf, seedComponent] using!
        (promotedRoot_mem_oldComponent_of_refined_attachment
          T S B c v hv hpB hpNotS hp)
    exact (mem_componentNonseedVertices_iff T S d.1 p).2
      ⟨hpNotS, hpSupp⟩
  have upperNotAttach :
      d ∈ parityBadComponents T S D.toRootedSeedComponentData col →
      componentUpperSeed T S D.toRootedSeedComponentData d ∉
        componentSeeds T (S ∪ B) c.1 := by
    intro hdBad hu
    obtain ⟨x, hx, hux⟩ :=
      component_attachment_witness T (S ∪ B) c hu
    have hxNotNew : x ∉ S ∪ B :=
      (mem_componentNonseedVertices_iff T (S ∪ B) c.1 x).mp hx |>.1
    have hxNotS : x ∉ S := fun hxS =>
      hxNotNew (Finset.mem_union_left B hxS)
    have hxD : x ∈ componentNonseedVertices T S d.1 :=
      (mem_componentNonseedVertices_iff T S d.1 x).2
        ⟨hxNotS, suppOld hx⟩
    have hxr : x = D.root d :=
      componentUpperSeed_adj_eq_root T S D hrank hedge d hxD hux
    have hrB : D.root d ∈ B := by
      exact (mem_parityPromotionRoots_iff T S
        D.toRootedSeedComponentData col (D.root d)).2
        ⟨d, hdBad, rfl⟩
    exact hxNotNew (Finset.mem_union_right S (hxr ▸ hrB))
  have lowerCard :
      (componentLowerSeeds T S D.toRootedSeedComponentData d).card ≤ 1 :=
    componentLowerSeeds_card_le_one T S
      D.toRootedSeedComponentData hparentAdj hattach d
  by_cases hdBad :
      d ∈ parityBadComponents T S D.toRootedSeedComponentData col
  · have hsub :
        componentSeeds T (S ∪ B) c.1 ⊆
          {D.root d} ∪
            componentLowerSeeds T S D.toRootedSeedComponentData d := by
      intro s hs
      have hsNew := componentSeeds_subset T (S ∪ B) c.1 hs
      rcases Finset.mem_union.mp hsNew with hsS | hsB
      · have hsOld := attachOld hs hsS
        have hsNe :
            s ≠ componentUpperSeed T S
              D.toRootedSeedComponentData d := by
          intro heq
          exact upperNotAttach hdBad (heq ▸ hs)
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hsOld, by simpa using! hsNe⟩)
      · have hsD := promotedInside hs hsB
        have hrB : D.root d ∈ B :=
          (mem_parityPromotionRoots_iff T S
            D.toRootedSeedComponentData col (D.root d)).2
            ⟨d, hdBad, rfl⟩
        have hsr : s = D.root d :=
          parityPromotionRoot_unique_in_oldComponent T S
            D.toRootedSeedComponentData col d hsD (D.root_mem d)
            hsB hrB
        exact Finset.mem_union_left _ (by simpa [hsr])
    have hcard :
        (componentSeeds T (S ∪ B) c.1).card ≤ 2 := by
      refine (Finset.card_le_card hsub).trans ?_
      calc
        ({D.root d} ∪
            componentLowerSeeds T S
              D.toRootedSeedComponentData d).card
            ≤ 1 +
              (componentLowerSeeds T S
                D.toRootedSeedComponentData d).card := by
                simpa using! Finset.card_union_le
                  ({D.root d} : Finset A)
                  (componentLowerSeeds T S
                    D.toRootedSeedComponentData d)
        _ ≤ 2 := by omega
    refine ⟨hcard, ?_⟩
    intro a ha b hb
    have colourEqRoot : ∀ {s},
        s ∈ componentSeeds T (S ∪ B) c.1 →
          col s = col (D.root d) := by
      intro s hs
      have hs' := hsub hs
      rcases Finset.mem_union.mp hs' with hsr | hslower
      · exact congrArg col (by simpa using! hsr)
      · exact parityBad_lower_colour_eq_root T S
          D.toRootedSeedComponentData hparentAdj hattach col hcol
          ⟨d, hdBad⟩ hslower
    exact (colourEqRoot ha).trans (colourEqRoot hb).symm
  · have hsub :
        componentSeeds T (S ∪ B) c.1 ⊆ componentSeeds T S d.1 := by
      intro s hs
      have hsNew := componentSeeds_subset T (S ∪ B) c.1 hs
      rcases Finset.mem_union.mp hsNew with hsS | hsB
      · exact attachOld hs hsS
      · have hsD := promotedInside hs hsB
        exact False.elim (hdBad
          (parityPromotionRoot_component_bad T S
            D.toRootedSeedComponentData col d hsD hsB))
    have hcard :
        (componentSeeds T (S ∪ B) c.1).card ≤ 2 :=
      (Finset.card_le_card hsub).trans (hattach d)
    refine ⟨hcard, ?_⟩
    intro a ha b hb
    have colourEqUpper : ∀ {s},
        s ∈ componentSeeds T (S ∪ B) c.1 →
          col s =
            col (componentUpperSeed T S
              D.toRootedSeedComponentData d) := by
      intro s hs
      have hsOld := hsub hs
      by_cases hsu :
          s = componentUpperSeed T S
            D.toRootedSeedComponentData d
      · simpa [hsu]
      · exact parityGood_lower_colour_eq_upper T S
          D.toRootedSeedComponentData col d hdBad
          (Finset.mem_sdiff.mpr ⟨hsOld, by simpa using! hsu⟩)
    exact (colourEqUpper ha).trans (colourEqUpper hb).symm

end Erdos550
