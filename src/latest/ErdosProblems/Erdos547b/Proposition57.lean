/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.TreePartition
import ErdosProblems.Erdos547b.RegularPair

/-!
# Zhao's Proposition 5.7: merging a root-partition

Zhao's arrow notation for an online forest embedding says that, when a root
is reached, all but a bounded set of vertices of the root cluster may be used
as its image.  `FlexiblePartialEmbedding` below makes this precise: the bad
set is part of the certificate, and every injective assignment of all roots
outside the bad sets is realized.

The proposition itself only uses the incidence properties of a root-partition:
the two supports cover the forest, they overlap only at roots, and every edge
lies wholly in one support.  We therefore prove the slightly stronger graph
statement.  An actual ordered rooted forest and a root-partition in Zhao's
Definition 5.6 satisfy these three properties component by component.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoProp57

open Finset SimpleGraph

variable {A B : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

/-- The incidence-level content of Zhao's Definition 5.6.  `left` and
`right` are the vertex supports of the two root-subforests. -/
structure RootPartition (F : SimpleGraph A) (roots left right : Finset A) : Prop where
  cover : left ∪ right = Finset.univ
  overlap_roots : left ∩ right ⊆ roots
  edge_cover : ∀ ⦃x y : A⦄, F.Adj x y →
    (x ∈ left ∧ y ∈ left) ∨ (x ∈ right ∧ y ∈ right)

/-- An embedding of the part of `F` supported on `support`.  Roots use the
prescribed common root map; all non-roots land in `target`. -/
structure SupportedRootEmbedding (F : SimpleGraph A) (G : SimpleGraph B)
    (roots support : Finset A) (target : Finset B) (rootImage : A → B) where
  toFun : A → B
  map_adj : ∀ ⦃x y : A⦄, F.Adj x y → x ∈ support → y ∈ support →
    G.Adj (toFun x) (toFun y)
  injOn : ∀ ⦃x y : A⦄, x ∈ support → y ∈ support →
    toFun x = toFun y → x = y
  map_root : ∀ ⦃r : A⦄, r ∈ roots → r ∈ support → toFun r = rootImage r
  map_nonroot : ∀ ⦃x : A⦄, x ∈ support → x ∉ roots → toFun x ∈ target

/-- A rigorous certificate for Zhao's notation saying that a supported
rooted forest embeds with at most `slack` forbidden choices for each root.

The realization is deliberately quantified over the root assignment.  This
is the mathematical content of the source's phrase "all but `slack` vertices
can be chosen as the image of the root." -/
structure FlexiblePartialEmbedding (F : SimpleGraph A) (G : SimpleGraph B)
    (roots support : Finset A) (rootCluster target : Finset B) (slack : ℕ) where
  bad : A → Finset B
  bad_subset : ∀ r, bad r ⊆ rootCluster
  card_bad : ∀ ⦃r : A⦄, r ∈ roots → r ∈ support → #(bad r) ≤ slack
  realize : ∀ rootImage : A → B,
    (∀ ⦃r q : A⦄, r ∈ roots → q ∈ roots → rootImage r = rootImage q → r = q) →
    (∀ ⦃r : A⦄, r ∈ roots → rootImage r ∈ rootCluster) →
    (∀ ⦃r : A⦄, r ∈ roots → r ∈ support → rootImage r ∉ bad r) →
    Nonempty (SupportedRootEmbedding F G roots support target rootImage)

/-- The corresponding full-forest embedding certificate. -/
structure RootedTargetEmbedding (F : SimpleGraph A) (G : SimpleGraph B)
    (roots : Finset A) (target : Finset B) (rootImage : A → B) where
  copy : F.Copy G
  map_root : ∀ ⦃r : A⦄, r ∈ roots → copy r = rootImage r
  map_nonroot : ∀ ⦃x : A⦄, x ∉ roots → copy x ∈ target

/-- Full-forest version of Zhao's flexibility notation. -/
structure FlexibleEmbedding (F : SimpleGraph A) (G : SimpleGraph B)
    (roots : Finset A) (rootCluster target : Finset B) (slack : ℕ) where
  bad : A → Finset B
  bad_subset : ∀ r, bad r ⊆ rootCluster
  card_bad : ∀ ⦃r : A⦄, r ∈ roots → #(bad r) ≤ slack
  realize : ∀ rootImage : A → B,
    (∀ ⦃r q : A⦄, r ∈ roots → q ∈ roots → rootImage r = rootImage q → r = q) →
    (∀ ⦃r : A⦄, r ∈ roots → rootImage r ∈ rootCluster) →
    (∀ ⦃r : A⦄, r ∈ roots → rootImage r ∉ bad r) →
    Nonempty (RootedTargetEmbedding F G roots target rootImage)

/-- The abstract merging lemma underlying Proposition 5.7.  Two online
certificates on a root-partition merge, and their exceptional-root losses
add.  Disjointness of the two matching supports and of the root cluster from
both matching supports is exactly what proves global injectivity. -/
theorem merge_flexiblePartialEmbedding
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots left right : Finset A)
    (rootCluster targetLeft targetRight : Finset B)
    (slackLeft slackRight : ℕ)
    (part : RootPartition F roots left right)
    (hrootLeft : Disjoint rootCluster targetLeft)
    (hrootRight : Disjoint rootCluster targetRight)
    (htarget : Disjoint targetLeft targetRight)
    (embLeft : FlexiblePartialEmbedding F G roots left rootCluster targetLeft slackLeft)
    (embRight : FlexiblePartialEmbedding F G roots right rootCluster targetRight slackRight) :
    Nonempty (FlexibleEmbedding F G roots rootCluster (targetLeft ∪ targetRight)
      (slackLeft + slackRight)) := by
  classical
  let combinedBad : A → Finset B := fun r =>
    (if r ∈ left then embLeft.bad r else ∅) ∪
      (if r ∈ right then embRight.bad r else ∅)
  refine ⟨
    { bad := combinedBad
      bad_subset := ?_
      card_bad := ?_
      realize := ?_ }⟩
  · intro r
    apply Finset.union_subset
    · split_ifs with hr
      · exact embLeft.bad_subset r
      · exact Finset.empty_subset _
    · split_ifs with hr
      · exact embRight.bad_subset r
      · exact Finset.empty_subset _
  · intro r hr
    have hrCover : r ∈ left ∨ r ∈ right := by
      have : r ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ r
      simpa only [Finset.mem_union] using this
    calc
      #(combinedBad r) ≤
          #(if r ∈ left then embLeft.bad r else ∅) +
            #(if r ∈ right then embRight.bad r else ∅) := Finset.card_union_le _ _
      _ ≤ slackLeft + slackRight := by
        apply Nat.add_le_add
        · split_ifs with hrl
          · exact embLeft.card_bad hr hrl
          · simp
        · split_ifs with hrr
          · exact embRight.card_bad hr hrr
          · simp
  · intro rootImage hrootInj hrootMem hrootGood
    have hgoodLeft : ∀ ⦃r : A⦄, r ∈ roots → r ∈ left →
        rootImage r ∉ embLeft.bad r := by
      intro r hr hrl hbad
      exact hrootGood hr (by
        simp only [combinedBad, hrl, if_pos, Finset.mem_union]
        exact Or.inl hbad)
    have hgoodRight : ∀ ⦃r : A⦄, r ∈ roots → r ∈ right →
        rootImage r ∉ embRight.bad r := by
      intro r hr hrr hbad
      exact hrootGood hr (by
        simp only [combinedBad, hrr, if_pos, Finset.mem_union]
        exact Or.inr hbad)
    let eLeft := (embLeft.realize rootImage hrootInj hrootMem hgoodLeft).some
    let eRight := (embRight.realize rootImage hrootInj hrootMem hgoodRight).some
    let glued : A → B := fun x => if x ∈ left then eLeft.toFun x else eRight.toFun x
    have hright (x : A) (hx : x ∈ right) : glued x = eRight.toFun x := by
      by_cases hxl : x ∈ left
      · have hxr : x ∈ roots := part.overlap_roots (by
          exact Finset.mem_inter.mpr ⟨hxl, hx⟩)
        have hle : eLeft.toFun x = rootImage x := eLeft.map_root hxr hxl
        have hre : eRight.toFun x = rootImage x := eRight.map_root hxr hx
        simp only [glued, hxl, if_pos, hle, hre]
      · simp only [glued, if_neg hxl]
    have hleft (x : A) (hx : x ∈ left) : glued x = eLeft.toFun x := by
      simp only [glued, hx, if_pos]
    have hgluedRoot {r : A} (hr : r ∈ roots) : glued r = rootImage r := by
      have hrCover : r ∈ left ∨ r ∈ right := by
        have : r ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ r
        simpa only [Finset.mem_union] using this
      rcases hrCover with hrl | hrr
      · rw [hleft r hrl]
        exact eLeft.map_root hr hrl
      · rw [hright r hrr]
        exact eRight.map_root hr hrr
    have hgluedNonroot {x : A} (hxroot : x ∉ roots) :
        glued x ∈ targetLeft ∪ targetRight := by
      by_cases hxl : x ∈ left
      · exact Finset.mem_union_left _ (by
          rw [hleft x hxl]
          exact eLeft.map_nonroot hxl hxroot)
      · have hxr : x ∈ right := by
          have : x ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ x
          exact (Finset.mem_union.mp this).resolve_left hxl
        exact Finset.mem_union_right _ (by
          rw [hright x hxr]
          exact eRight.map_nonroot hxr hxroot)
    have hgluedAdj : ∀ ⦃x y : A⦄, F.Adj x y → G.Adj (glued x) (glued y) := by
      intro x y hxy
      rcases part.edge_cover hxy with hL | hR
      · rw [hleft x hL.1, hleft y hL.2]
        exact eLeft.map_adj hxy hL.1 hL.2
      · rw [hright x hR.1, hright y hR.2]
        exact eRight.map_adj hxy hR.1 hR.2
    have hgluedInj : Function.Injective glued := by
      intro x y hxy
      by_cases hxl : x ∈ left
      · by_cases hyl : y ∈ left
        · apply eLeft.injOn hxl hyl
          simpa only [hleft x hxl, hleft y hyl] using hxy
        · have hyr : y ∈ right := by
            have : y ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ y
            exact (Finset.mem_union.mp this).resolve_left hyl
          by_cases hxr : x ∈ roots
          · by_cases hyrRoot : y ∈ roots
            · exact hrootInj hxr hyrRoot (by
                rw [← hgluedRoot hxr, ← hgluedRoot hyrRoot]
                exact hxy)
            · have hxA : glued x ∈ rootCluster := by
                rw [hgluedRoot hxr]
                exact hrootMem hxr
              have hyT : glued y ∈ targetRight := by
                rw [hright y hyr]
                exact eRight.map_nonroot hyr hyrRoot
              exfalso
              exact Finset.disjoint_left.mp hrootRight hxA (hxy ▸ hyT)
          · have hxT : glued x ∈ targetLeft := by
              rw [hleft x hxl]
              exact eLeft.map_nonroot hxl hxr
            by_cases hyrRoot : y ∈ roots
            · have hyA : glued y ∈ rootCluster := by
                rw [hgluedRoot hyrRoot]
                exact hrootMem hyrRoot
              exfalso
              exact Finset.disjoint_left.mp hrootLeft hyA (hxy.symm ▸ hxT)
            · have hyT : glued y ∈ targetRight := by
                rw [hright y hyr]
                exact eRight.map_nonroot hyr hyrRoot
              exfalso
              exact Finset.disjoint_left.mp htarget hxT (hxy ▸ hyT)
      · have hxr : x ∈ right := by
          have : x ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ x
          exact (Finset.mem_union.mp this).resolve_left hxl
        by_cases hyl : y ∈ left
        · have := hxy.symm
          by_cases hyrRoot : y ∈ roots
          · by_cases hxrRoot : x ∈ roots
            · exact (hrootInj hyrRoot hxrRoot (by
                rw [← hgluedRoot hyrRoot, ← hgluedRoot hxrRoot]
                exact this)).symm
            · have hyA : glued y ∈ rootCluster := by
                rw [hgluedRoot hyrRoot]
                exact hrootMem hyrRoot
              have hxT : glued x ∈ targetRight := by
                rw [hright x hxr]
                exact eRight.map_nonroot hxr hxrRoot
              exfalso
              exact Finset.disjoint_left.mp hrootRight hyA (hxy ▸ hxT)
          · have hyT : glued y ∈ targetLeft := by
              rw [hleft y hyl]
              exact eLeft.map_nonroot hyl hyrRoot
            by_cases hxrRoot : x ∈ roots
            · have hxA : glued x ∈ rootCluster := by
                rw [hgluedRoot hxrRoot]
                exact hrootMem hxrRoot
              exfalso
              exact Finset.disjoint_left.mp hrootLeft hxA (hxy ▸ hyT)
            · have hxT : glued x ∈ targetRight := by
                rw [hright x hxr]
                exact eRight.map_nonroot hxr hxrRoot
              exfalso
              exact Finset.disjoint_left.mp htarget hyT (hxy ▸ hxT)
        · have hyr : y ∈ right := by
            have : y ∈ left ∪ right := by rw [part.cover]; exact Finset.mem_univ y
            exact (Finset.mem_union.mp this).resolve_left hyl
          apply eRight.injOn hxr hyr
          simpa only [hright x hxr, hright y hyr] using hxy
    let copy : F.Copy G :=
      ⟨⟨glued, fun {_ _} hxy => hgluedAdj hxy⟩, hgluedInj⟩
    exact ⟨⟨copy, (by
      intro r hr
      simpa [copy] using hgluedRoot hr), (by
      intro x hx
      simpa [copy] using hgluedNonroot hx)⟩⟩

/-- Zhao, Proposition 5.7, with integral slack `s`: two disjoint
root-partition embeddings having `2s` exceptional choices merge into an
embedding having `4s` exceptional choices.  In the paper `s = √ε N` (with
integer rounding understood), the root cluster is `A`, and the target sets
are the vertex sets of the disjoint cluster-matchings `M₀` and `M₁`. -/
theorem proposition_5_7
    (F : SimpleGraph A) (G : SimpleGraph B)
    (roots left right : Finset A)
    (rootCluster targetLeft targetRight : Finset B)
    (s : ℕ)
    (part : RootPartition F roots left right)
    (hrootLeft : Disjoint rootCluster targetLeft)
    (hrootRight : Disjoint rootCluster targetRight)
    (htarget : Disjoint targetLeft targetRight)
    (embLeft : FlexiblePartialEmbedding F G roots left rootCluster targetLeft (2 * s))
    (embRight : FlexiblePartialEmbedding F G roots right rootCluster targetRight (2 * s)) :
    Nonempty (FlexibleEmbedding F G roots rootCluster
      (targetLeft ∪ targetRight) (4 * s)) := by
  have h :=
    merge_flexiblePartialEmbedding F G roots left right rootCluster targetLeft targetRight
      (2 * s) (2 * s) part hrootLeft hrootRight htarget embLeft embRight
  have hs : 2 * s + 2 * s = 4 * s := by omega
  rw [← hs]
  exact h

end Erdos547b.ZhaoProp57

#print axioms Erdos547b.ZhaoProp57.merge_flexiblePartialEmbedding
#print axioms Erdos547b.ZhaoProp57.proposition_5_7
