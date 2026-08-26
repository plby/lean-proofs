/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma614

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma614Full

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair

universe v

/-!
# The regular-pair bad-root version of Zhao's online forest arrow

The earlier `exists_flexibleEmbedding_of_uniformPairs` assumes the required
degree condition for every possible image of every root, and consequently
uses the empty bad set.  The theorem below records the form actually supplied
by regularity: for component `i`, the bad images are precisely the atypical
vertices of the uniform pair `(rootCluster, Y i)`.

The hypothesis `hrootCap` separates the two numerical ingredients.  Once a
root image is not atypical, uniformity gives degree at least
`(d(rootCluster,Y i)-rho)|Y i|`; `hrootCap` says that this is enough for the
rooted-tree embedding.  Thus no pointwise root-degree assumption remains.
-/

/-- A regular-pair construction of Zhao's flexible ordered-forest arrow with
an honest exceptional set of root images.

For the literal root `⟨i, F.root i⟩`, the exceptional set is
`atypicalVertices G rho rootCluster (Y i)`.  Its cardinality is bounded by
`slack` using `card_atypicalVertices_le`.  Values of `bad` away from literal
roots are irrelevant to `FlexibleEmbedding` and are chosen to be empty. -/
theorem exists_flexibleEmbedding_of_rootUniformPairs
    {m : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : Erdos547b.RegularPair.OrderedRootedForest m)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootCluster : Finset B) {rho : ℝ}
    (X Y : Fin m → Finset B) (slack : ℕ)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i))
    (hrootUnif : ∀ i, G.IsUniform rho rootCluster (Y i))
    (hrho : rho ≤ 1)
    (hcapX : ∀ i, (F.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootCap : ∀ i, (F.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity rootCluster (Y i) - rho) * #(Y i))
    (hslack : rho * (#rootCluster : ℝ) ≤ slack)
    (hrootOutside : ∀ z ∈ rootCluster, ∀ i,
      z ∉ cleanedSide G rho (X i) (Y i) ∧
      z ∉ cleanedSide G rho (Y i) (X i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    Nonempty (Erdos547b.ZhaoProp57.FlexibleEmbedding
      F.graph G (ORF.roots F) rootCluster
      (ORF.target F (fun i c ↦ if c = 0 then
        cleanedSide G rho (X i) (Y i)
      else cleanedSide G rho (Y i) (X i))) slack) := by
  classical
  let candidate : Fin m → Fin 2 → Finset B := fun i c ↦ if c = 0 then
    cleanedSide G rho (X i) (Y i)
    else cleanedSide G rho (Y i) (X i)
  let bad : (Σ i, Fin (F.size i)) → Finset B := fun r ↦
    if r.2 = F.root r.1 then atypicalVertices G rho rootCluster (Y r.1)
    else ∅
  refine ⟨
    { bad := bad
      bad_subset := ?_
      card_bad := ?_
      realize := ?_ }⟩
  · intro r
    dsimp only [bad]
    split_ifs
    · exact filter_subset _ _
    · exact empty_subset _
  · intro r hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    have hreal :
        (#(atypicalVertices G rho rootCluster (Y i)) : ℝ) ≤
          rho * #rootCluster :=
      card_atypicalVertices_le G (hrootUnif i) hrho
    have hreal' :
        (#(atypicalVertices G rho rootCluster (Y i)) : ℝ) ≤ slack :=
      hreal.trans hslack
    have hnat : #(atypicalVertices G rho rootCluster (Y i)) ≤ slack := by
      exact_mod_cast hreal'
    simpa [bad] using hnat
  · intro rootMap hrootMapInj hrootMapMem hrootMapGood
    let rootImage : Fin m → B := fun i ↦ rootMap ⟨i, F.root i⟩
    have hriInj : Function.Injective rootImage := by
      intro i j hij
      have hsigma : (⟨i, F.root i⟩ : Σ i, Fin (F.size i)) =
          ⟨j, F.root j⟩ := by
        apply hrootMapInj
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · exact hij
      exact Sigma.mk.inj_iff.mp hsigma |>.1
    have hriMem (i : Fin m) : rootImage i ∈ rootCluster := by
      apply hrootMapMem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hriGood (i : Fin m) :
        rootImage i ∉ atypicalVertices G rho rootCluster (Y i) := by
      have hi := hrootMapGood
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      simpa [bad] using hi
    have hriDegree (i : Fin m) :
        (F.size i : ℝ) + rho * #(Y i) ≤
          (#((Y i).filter (G.Adj (rootImage i))) : ℝ) := by
      apply (hrootCap i).trans
      apply le_of_not_gt
      intro hlt
      apply hriGood i
      simp only [atypicalVertices, Finset.mem_filter]
      exact ⟨hriMem i, hlt⟩
    obtain ⟨E, hEroot, hEmem⟩ :=
      F.exists_embedding_over_disjoint_uniform_pairs G rootImage X Y
        hriInj hunif hrho hcapX hcapY hriDegree
        (fun i k ↦ hrootOutside (rootImage i) (hriMem i) k) hdisjoint
    refine ⟨
      { copy := E.toGraphCopy
        map_root := ?_
        map_nonroot := ?_ }⟩
    · intro r hr
      obtain ⟨i, -, hir⟩ := Finset.mem_image.mp hr
      subst r
      change E.copy i (F.root i) = rootMap ⟨i, F.root i⟩
      exact hEroot i
    · rintro ⟨i, a⟩ hnotroot
      have ha : a ≠ F.root i := by
        intro ha
        apply hnotroot
        subst a
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hm := hEmem i a ha
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      by_cases hc : (F.isTree i).coloringTwoOfVert (F.root i) a = 0
      · apply Finset.mem_union_left
        change E.copy i a ∈ cleanedSide G rho (X i) (Y i)
        simpa [candidate, hc] using hm
      · apply Finset.mem_union_right
        change E.copy i a ∈ cleanedSide G rho (Y i) (X i)
        simpa [candidate, hc] using hm

#print axioms Erdos547b.ZhaoLemma614Full.exists_flexibleEmbedding_of_rootUniformPairs

end Erdos547b.ZhaoLemma614Full
