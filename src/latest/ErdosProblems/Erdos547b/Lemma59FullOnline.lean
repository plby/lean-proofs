/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma614
import ErdosProblems.Erdos547b.Proposition57

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59FullOnline

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair

universe u v

variable {V : Type u} {B : Type v} [Fintype V] [DecidableEq V]
  {T : SimpleGraph V} [DecidableRel T.Adj]
  {globalRoot : V} {small : ℕ}

/-! ## The parent really belongs to the earlier numbered component -/

theorem componentIndex_parent
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0) :
    P.componentIndex (P.parent j hj) = P.parentPart j hj := by
  unfold ZhaoForestPartition.componentIndex
  apply P.components.injective
  rw [P.components.apply_symm_apply]
  apply ConnectedComponent.eq_of_common_vertex
    ConnectedComponent.connectedComponentMk_mem
  exact P.parent_mem j hj

theorem parentCoordinate_earlier
    (P : ZhaoForestPartition T globalRoot small)
    (j : Fin P.numParts) (hj : j.val ≠ 0) :
    (P.toOrderedForestVertex (P.parent j hj)).1.val < j.val := by
  change (P.componentIndex (P.parent j hj)).val < j.val
  rw [componentIndex_parent P j hj]
  exact P.parent_earlier j hj

/-! ## Candidate blocks and the online component record -/

/-- The cleaned candidate block occupied by a non-root vertex of component
`i` and bipartition colour `c`. -/
def sideCandidate [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y : Fin P.numParts → Finset B) (i : Fin P.numParts) (c : Fin 2) :
    Finset B :=
  if c = 0 then cleanedSide G rho (X i) (Y i)
  else cleanedSide G rho (Y i) (X i)

/-- The possible locations of the already embedded parent of component `j`.
If that parent is itself a component root this is its root-reservoir; otherwise
it is its cleaned bipartition block. -/
def parentCandidate [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y rootCandidate : Fin P.numParts → Finset B)
    (j : Fin P.numParts) (hj : j.val ≠ 0) : Finset B :=
  let p := P.toOrderedForestVertex (P.parent j hj)
  if p.2 = P.orderedForest.root p.1 then rootCandidate p.1
  else sideCandidate P G rho X Y p.1
    ((P.orderedForest.isTree p.1).coloringTwoOfVert
      (P.orderedForest.root p.1) p.2)

/-- The roots in the sigma-type graph of the ordered cut forest. -/
def orderedRoots (P : ZhaoForestPartition T globalRoot small) :
    Finset (Σ i, Fin (P.orderedForest.size i)) :=
  Finset.univ.image fun i ↦ ⟨i, P.orderedForest.root i⟩

/-- The union of all cleaned non-root blocks. -/
def orderedTarget [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y : Fin P.numParts → Finset B) : Finset B :=
  Finset.univ.biUnion fun i ↦
    sideCandidate P G rho X Y i 0 ∪ sideCandidate P G rho X Y i 1

/-- Concrete data produced when one component is processed online. -/
structure ComponentRealization [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y rootCandidate : Fin P.numParts → Finset B)
    (i : Fin P.numParts) where
  rootImage : B
  root_mem : rootImage ∈ rootCandidate i
  copy : (P.orderedForest.tree i).Copy G
  map_root : copy (P.orderedForest.root i) = rootImage
  map_nonroot : ∀ a, a ≠ P.orderedForest.root i →
    copy a ∈ sideCandidate P G rho X Y i
      ((P.orderedForest.isTree i).coloringTwoOfVert
        (P.orderedForest.root i) a)

section OnlineConstruction

variable [Fintype B] [DecidableEq B]
  (P : ZhaoForestPartition T globalRoot small)
  (G : SimpleGraph B) [DecidableRel G.Adj]
  (rho : ℝ) (X Y rootCandidate : Fin P.numParts → Finset B)
  (hunif : ∀ i, G.IsUniform rho (X i) (Y i))
  (hrho : rho ≤ 1)
  (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
    (G.edgeDensity (X i) (Y i) - rho) * #(X i))
  (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
    (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
  (hrootDegree : ∀ i z, z ∈ rootCandidate i →
    (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (#((Y i).filter (G.Adj z)) : ℝ))
  (hfirst : P.numParts ≤ #(rootCandidate ⟨0, P.numParts_pos⟩))
  (hlink : ∀ j (hj : j.val ≠ 0), ∀ z,
    z ∈ parentCandidate P G rho X Y rootCandidate j hj →
    P.numParts ≤ #((rootCandidate j).filter (G.Adj z)))

/-- One online step, parametrized by the already constructed earlier
components.  Besides the new component copy, it records freshness of the new
root and adjacency to the actual embedded parent. -/
structure OnlineStep (i : Fin P.numParts)
    (prior : ∀ k : Fin P.numParts, k.val < i.val →
      ComponentRealization P G rho X Y rootCandidate k) where
  data : ComponentRealization P G rho X Y rootCandidate i
  fresh : ∀ k (hk : k.val < i.val),
    data.rootImage ≠ (prior k hk).rootImage
  parent_adj : ∀ hi : i.val ≠ 0,
    let p := P.toOrderedForestVertex (P.parent i hi)
    G.Adj ((prior p.1 (parentCoordinate_earlier P i hi)).copy p.2)
      data.rootImage

/-- Execute one online step.  The root is chosen from the live neighborhood
of the already embedded parent after deleting every earlier root image. -/
noncomputable def onlineStep (i : Fin P.numParts)
    (prior : ∀ k : Fin P.numParts, k.val < i.val →
      ComponentRealization P G rho X Y rootCandidate k) :
    OnlineStep P G rho X Y rootCandidate i prior := by
  classical
  let parentImage : (hi : i.val ≠ 0) → B := fun hi ↦
    let p := P.toOrderedForestVertex (P.parent i hi)
    (prior p.1 (parentCoordinate_earlier P i hi)).copy p.2
  let eligible : Finset B := if hi : i.val = 0 then rootCandidate i
    else (rootCandidate i).filter (G.Adj (parentImage hi))
  have heligible : P.numParts ≤ #eligible := by
    by_cases hi : i.val = 0
    · have hii : i = ⟨0, P.numParts_pos⟩ := Fin.eq_of_val_eq hi
      subst i
      simpa [eligible] using hfirst
    · have hpMem : parentImage hi ∈
          parentCandidate P G rho X Y rootCandidate i hi := by
        let p := P.toOrderedForestVertex (P.parent i hi)
        by_cases hp : p.2 = P.orderedForest.root p.1
        · have hm := (prior p.1 (parentCoordinate_earlier P i hi)).root_mem
          simpa [parentImage, parentCandidate, p, hp,
            (prior p.1 (parentCoordinate_earlier P i hi)).map_root] using hm
        · have hm := (prior p.1 (parentCoordinate_earlier P i hi)).map_nonroot p.2 hp
          simpa [parentImage, parentCandidate, p, hp] using hm
      simpa [eligible, hi] using hlink i hi (parentImage hi) hpMem
  let earlier : Finset (Fin P.numParts) := Finset.Iio i
  let used : Finset B := earlier.attach.image fun k ↦
    (prior k.1 (by
      have hkIio : k.1 ∈ Finset.Iio i := k.2
      exact Fin.mk_lt_mk.mp (Finset.mem_Iio.mp hkIio))).rootImage
  have hused : #used ≤ i.val := by
    calc
      #used ≤ #earlier.attach := Finset.card_image_le
      _ = #earlier := Finset.card_attach
      _ = i.val := by simp [earlier]
  have hused_lt : #used < #eligible := by
    exact lt_of_le_of_lt hused (lt_of_lt_of_le i.isLt heligible)
  let hex : ∃ z ∈ eligible, z ∉ used :=
    Finset.exists_mem_notMem_of_card_lt_card hused_lt
  let z : B := Classical.choose hex
  have hzEligible : z ∈ eligible := (Classical.choose_spec hex).1
  have hzUnused : z ∉ used := (Classical.choose_spec hex).2
  have hzRoot : z ∈ rootCandidate i := by
    by_cases hi : i.val = 0
    · simpa [eligible, hi] using hzEligible
    · exact (Finset.mem_filter.mp (by
        simpa [eligible, hi] using hzEligible)).1
  let hcopyEx :=
    exists_rooted_tree_copy_of_uniform (P.orderedForest.tree i) G
      (P.orderedForest.isTree i) (P.orderedForest.root i) z
      (hunif i) hrho (by simpa using hcapX i) (by simpa using hcapY i)
      (by simpa using hrootDegree i z hzRoot)
  let copy := Classical.choose hcopyEx
  have hcopyRoot := (Classical.choose_spec hcopyEx).1
  have hcopyMem := (Classical.choose_spec hcopyEx).2
  let data : ComponentRealization P G rho X Y rootCandidate i :=
    { rootImage := z
      root_mem := hzRoot
      copy := copy
      map_root := hcopyRoot
      map_nonroot := by
        intro a ha
        simpa [sideCandidate] using hcopyMem a ha }
  refine
    { data := data
      fresh := ?_
      parent_adj := ?_ }
  · intro k hk hEq
    apply hzUnused
    apply Finset.mem_image.mpr
    refine ⟨⟨k, by simpa [earlier] using hk⟩, Finset.mem_attach _ _, ?_⟩
    · exact hEq.symm
  · intro hi
    have hzAdj : G.Adj (parentImage hi) z :=
      (Finset.mem_filter.mp (by
        simpa [eligible, hi] using hzEligible)).2
    simpa [parentImage, data] using hzAdj

/-- The online run over all components, justified by `parent_earlier`. -/
noncomputable def onlineComponent (i : Fin P.numParts) :
    ComponentRealization P G rho X Y rootCandidate i :=
  (onlineStep P G rho X Y rootCandidate hunif hrho hcapX hcapY
    hrootDegree hfirst hlink i
    (fun k _hk ↦ onlineComponent k)).data
termination_by i.val

theorem onlineComponent_fresh (i k : Fin P.numParts) (hk : k.val < i.val) :
    (onlineComponent P G rho X Y rootCandidate hunif hrho hcapX hcapY
      hrootDegree hfirst hlink i).rootImage ≠
    (onlineComponent P G rho X Y rootCandidate hunif hrho hcapX hcapY
      hrootDegree hfirst hlink k).rootImage := by
  rw [onlineComponent.eq_def]
  exact (onlineStep P G rho X Y rootCandidate hunif hrho hcapX hcapY
    hrootDegree hfirst hlink i
      (fun k hk ↦ onlineComponent P G rho X Y rootCandidate hunif hrho
        hcapX hcapY hrootDegree hfirst hlink k)).fresh k hk

theorem onlineComponent_parent_adj (j : Fin P.numParts) (hj : j.val ≠ 0) :
    let p := P.toOrderedForestVertex (P.parent j hj)
    G.Adj
      ((onlineComponent P G rho X Y rootCandidate hunif hrho hcapX hcapY
        hrootDegree hfirst hlink p.1).copy p.2)
      (onlineComponent P G rho X Y rootCandidate hunif hrho hcapX hcapY
        hrootDegree hfirst hlink j).rootImage := by
  rw [onlineComponent.eq_def]
  exact (onlineStep P G rho X Y rootCandidate hunif hrho hcapX hcapY
    hrootDegree hfirst hlink j
      (fun k hk ↦ onlineComponent P G rho X Y rootCandidate hunif hrho
        hcapX hcapY hrootDegree hfirst hlink k)).parent_adj hj

end OnlineConstruction

/-! ## Globally injective assembly and restoration of the cut edges -/

/-- Full concrete output of the online Lemma-5.9 construction.  It exposes
the chosen roots, their candidate membership, the simultaneous ordered-forest
embedding, the literal cut-forest copy, every restored parent link, and the
resulting copy of the original tree. -/
structure FullOnlineEmbedding [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y rootCandidate : Fin P.numParts → Finset B) where
  rootImage : Fin P.numParts → B
  rootInjective : Function.Injective rootImage
  root_mem : ∀ i, rootImage i ∈ rootCandidate i
  forestEmbedding : P.orderedForest.Embedding G
  map_root : ∀ i,
    forestEmbedding.copy i (P.orderedForest.root i) = rootImage i
  map_nonroot : ∀ i a, a ≠ P.orderedForest.root i →
    forestEmbedding.copy i a ∈ sideCandidate P G rho X Y i
      ((P.orderedForest.isTree i).coloringTwoOfVert
        (P.orderedForest.root i) a)
  cutForestCopy : P.cutForest.Copy G
  cutForestCopy_apply : ∀ x,
    cutForestCopy x = forestEmbedding.copy
      (P.toOrderedForestVertex x).1 (P.toOrderedForestVertex x).2
  cutAdj : ∀ j (hj : j.val ≠ 0),
    G.Adj (cutForestCopy (P.roots j)) (cutForestCopy (P.parent j hj))
  fullCopy : T.Copy G

/-- **Full online/flexible form of Zhao Lemma 5.9 used by Lemma 6.14.**

`rootCandidate i` is the live root reservoir after the ordinary typicality
exceptions (the `bad` sets in Zhao's arrow notation) have been removed.
The first reservoir has `numParts` choices.  At every later step, every
possible image of the already embedded parent has `numParts` neighbors in the
new root reservoir.  Thus earlier root images can be forbidden online and a
fresh root still chosen.  The regular-pair hypotheses then embed the actual
component, not an assumed candidate/embedding continuation.

The conclusion contains the literal `cutForest.Copy G`, its actual deleted
edge adjacencies, and the restored `T.Copy G` produced by repository Lemma
6.14's checked glue constructor. -/
theorem exists_fullOnlineEmbedding
    [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (X Y rootCandidate : Fin P.numParts → Finset B)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i))
    (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hrootDegree : ∀ i z, z ∈ rootCandidate i →
      (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
        (#((Y i).filter (G.Adj z)) : ℝ))
    (hfirst : P.numParts ≤ #(rootCandidate ⟨0, P.numParts_pos⟩))
    (hlink : ∀ j (hj : j.val ≠ 0), ∀ z,
      z ∈ parentCandidate P G rho X Y rootCandidate j hj →
      P.numParts ≤ #((rootCandidate j).filter (G.Adj z)))
    (hrootOutside : ∀ i z, z ∈ rootCandidate i → ∀ k,
      z ∉ cleanedSide G rho (X k) (Y k) ∧
      z ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    Nonempty (FullOnlineEmbedding P G rho X Y rootCandidate) := by
  classical
  let D : ∀ i, ComponentRealization P G rho X Y rootCandidate i := fun i ↦
    onlineComponent P G rho X Y rootCandidate hunif hrho hcapX hcapY
      hrootDegree hfirst hlink i
  let rootImage : Fin P.numParts → B := fun i ↦ (D i).rootImage
  let copies : ∀ i, (P.orderedForest.tree i).Copy G := fun i ↦ (D i).copy
  have hri : Function.Injective rootImage := by
    intro i k hik
    by_contra hne
    have hvalne : i.val ≠ k.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hvalne with hikv | hkiv
    · exact (onlineComponent_fresh P G rho X Y rootCandidate hunif hrho
        hcapX hcapY hrootDegree hfirst hlink k i hikv) (by
          simpa [rootImage, D] using hik.symm)
    · exact (onlineComponent_fresh P G rho X Y rootCandidate hunif hrho
        hcapX hcapY hrootDegree hfirst hlink i k hkiv) (by
          simpa [rootImage, D] using hik)
  have hfroot : ∀ i, copies i (P.orderedForest.root i) = rootImage i := by
    intro i
    exact (D i).map_root
  have hfmem : ∀ i a, a ≠ P.orderedForest.root i →
      copies i a ∈ sideCandidate P G rho X Y i
        ((P.orderedForest.isTree i).coloringTwoOfVert
          (P.orderedForest.root i) a) := by
    intro i a ha
    exact (D i).map_nonroot a ha
  have hrootOut : ∀ i k c, rootImage i ∉ sideCandidate P G rho X Y k c := by
    intro i k c
    rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · simpa [rootImage, D, sideCandidate] using
        (hrootOutside i (rootImage i) (by exact (D i).root_mem) k).1
    · simpa [rootImage, D, sideCandidate] using
        (hrootOutside i (rootImage i) (by exact (D i).root_mem) k).2
  have hsideDisjoint : ∀ i k, i ≠ k →
      Disjoint
        (sideCandidate P G rho X Y i 0 ∪ sideCandidate P G rho X Y i 1)
        (sideCandidate P G rho X Y k 0 ∪ sideCandidate P G rho X Y k 1) := by
    intro i k hik
    simpa [sideCandidate] using hdisjoint i k hik
  have hinjective : Function.Injective
      (fun z : Σ i, Fin (P.orderedForest.size i) ↦ copies z.1 z.2) := by
    rintro ⟨i, a⟩ ⟨k, b⟩ hab
    dsimp only at hab
    by_cases hik : i = k
    · subst k
      have hab' : a = b := (copies i).injective hab
      subst b
      rfl
    · by_cases ha : a = P.orderedForest.root i
      · by_cases hb : b = P.orderedForest.root k
        · subst a
          subst b
          exfalso
          apply hik
          apply hri
          simpa [hfroot] using hab
        · have hbmem := hfmem k b hb
          have hout := hrootOut i k
            ((P.orderedForest.isTree k).coloringTwoOfVert
              (P.orderedForest.root k) b)
          exfalso
          apply hout
          rw [← hfroot i, ← ha, hab]
          exact hbmem
      · by_cases hb : b = P.orderedForest.root k
        · have hamem := hfmem i a ha
          have hout := hrootOut k i
            ((P.orderedForest.isTree i).coloringTwoOfVert
              (P.orderedForest.root i) a)
          exfalso
          apply hout
          rw [← hfroot k, ← hb, ← hab]
          exact hamem
        · have hamem := hfmem i a ha
          have hbmem := hfmem k b hb
          have haUnion : copies i a ∈
              sideCandidate P G rho X Y i 0 ∪
                sideCandidate P G rho X Y i 1 := by
            rcases OrderedRootedForest.fin_two_eq_zero_or_one
                ((P.orderedForest.isTree i).coloringTwoOfVert
                  (P.orderedForest.root i) a) with hc | hc
            · rw [hc] at hamem
              exact Finset.mem_union_left _ hamem
            · rw [hc] at hamem
              exact Finset.mem_union_right _ hamem
          have hbUnion : copies k b ∈
              sideCandidate P G rho X Y k 0 ∪
                sideCandidate P G rho X Y k 1 := by
            rcases OrderedRootedForest.fin_two_eq_zero_or_one
                ((P.orderedForest.isTree k).coloringTwoOfVert
                  (P.orderedForest.root k) b) with hc | hc
            · rw [hc] at hbmem
              exact Finset.mem_union_left _ hbmem
            · rw [hc] at hbmem
              exact Finset.mem_union_right _ hbmem
          exact False.elim
            (Finset.disjoint_left.mp (hsideDisjoint i k hik) haUnion
              (hab ▸ hbUnion))
  let E : P.orderedForest.Embedding G := ⟨copies, hinjective⟩
  let f : P.cutForest.Copy G := E.toGraphCopy.comp P.cutForestCopy
  have hf_apply (x : V) :
      f x = E.copy (P.toOrderedForestVertex x).1
        (P.toOrderedForestVertex x).2 := by
    change E.toGraphCopy (P.cutForestCopy x) = _
    rw [Erdos547b.ZhaoLemma614Full.cutForestCopy_apply]
    rfl
  have hf_root (i : Fin P.numParts) : f (P.roots i) = rootImage i := by
    rw [hf_apply, Erdos547b.ZhaoLemma614Full.toOrderedForestVertex_root]
    exact hfroot i
  have hcut : ∀ j (hj : j.val ≠ 0),
      G.Adj (f (P.roots j)) (f (P.parent j hj)) := by
    intro j hj
    rw [hf_root, hf_apply]
    have hadj := onlineComponent_parent_adj P G rho X Y rootCandidate
      hunif hrho hcapX hcapY hrootDegree hfirst hlink j hj
    exact (by simpa [E, copies, D, rootImage] using hadj.symm)
  let full : T.Copy G :=
    Erdos547b.ZhaoLemma614Full.copy_of_cutForestCopy_of_cutAdj P f hcut
  exact ⟨
    { rootImage := rootImage
      rootInjective := hri
      root_mem := fun i ↦ (D i).root_mem
      forestEmbedding := E
      map_root := hfroot
      map_nonroot := hfmem
      cutForestCopy := f
      cutForestCopy_apply := hf_apply
      cutAdj := hcut
      fullCopy := full }⟩

/-! ## The literal bad-root sets from Zhao's flexible arrow -/

/-- Root choices which fail the degree threshold into the first child side.
This is an actual finite set computed from the host graph, rather than an
uninterpreted exceptional-set interface. -/
def badRootChoices [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (Y rootCluster : Fin P.numParts → Finset B)
    (i : Fin P.numParts) : Finset B :=
  (rootCluster i).filter fun z ↦
    (#((Y i).filter (G.Adj z)) : ℝ) <
      (P.orderedForest.size i : ℝ) + rho * #(Y i)

/-- The live root reservoir after deleting `badRootChoices`. -/
def goodRootChoices [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (Y rootCluster : Fin P.numParts → Finset B)
    (i : Fin P.numParts) : Finset B :=
  rootCluster i \ badRootChoices P G rho Y rootCluster i

/-- The exact `ZhaoProp57.FlexibleEmbedding` supplied by the same uniform
pairs.  Its bad set is the concrete degree-failure set above.  Every injective
assignment of the component roots to the common root cluster outside those
bad sets is realized, with every non-root kept in the displayed cleaned
candidate union. -/
theorem exists_zhaoProp57_flexibleEmbedding
    [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (X Y : Fin P.numParts → Finset B)
    (rootCluster : Finset B) (slack : ℕ)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i))
    (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hbad : ∀ i,
      #(badRootChoices P G rho Y (fun _ ↦ rootCluster) i) ≤ slack)
    (hrootOutside : ∀ z, z ∈ rootCluster → ∀ i,
      z ∉ cleanedSide G rho (X i) (Y i) ∧
      z ∉ cleanedSide G rho (Y i) (X i))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    Nonempty (Erdos547b.ZhaoProp57.FlexibleEmbedding
      P.orderedForest.graph G (orderedRoots P) rootCluster
        (orderedTarget P G rho X Y) slack) := by
  classical
  refine ⟨
    { bad := fun z ↦
        badRootChoices P G rho Y (fun _ ↦ rootCluster) z.1
      bad_subset := ?_
      card_bad := ?_
      realize := ?_ }⟩
  · intro z
    exact Finset.filter_subset _ _
  · intro r _hr
    exact hbad r.1
  · intro rootMap hrootMapInj hrootMapMem hrootGood
    let rootImage : Fin P.numParts → B := fun i ↦
      rootMap ⟨i, P.orderedForest.root i⟩
    have hri : Function.Injective rootImage := by
      intro i k hik
      have hsigma : (⟨i, P.orderedForest.root i⟩ :
          Σ i, Fin (P.orderedForest.size i)) =
          ⟨k, P.orderedForest.root k⟩ := by
        apply hrootMapInj
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        · exact hik
      exact Sigma.mk.inj_iff.mp hsigma |>.1
    have hriMem (i : Fin P.numParts) : rootImage i ∈ rootCluster := by
      apply hrootMapMem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hriDegree (i : Fin P.numParts) :
        (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
          (#((Y i).filter (G.Adj (rootImage i))) : ℝ) := by
      apply le_of_not_gt
      intro hlt
      apply hrootGood (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩)
      change rootImage i ∈
        badRootChoices P G rho Y (fun _ ↦ rootCluster) i
      exact Finset.mem_filter.mpr ⟨hriMem i, hlt⟩
    obtain ⟨E, hEroot, hEmem⟩ :=
      P.orderedForest.exists_embedding_over_disjoint_uniform_pairs
        G rootImage X Y hri hunif hrho hcapX hcapY hriDegree
          (fun i k ↦ hrootOutside (rootImage i) (hriMem i) k) hdisjoint
    refine ⟨
      { copy := E.toGraphCopy
        map_root := ?_
        map_nonroot := ?_ }⟩
    · intro r hr
      obtain ⟨i, -, hir⟩ := Finset.mem_image.mp hr
      subst r
      change E.copy i (P.orderedForest.root i) =
        rootMap ⟨i, P.orderedForest.root i⟩
      exact hEroot i
    · rintro ⟨i, a⟩ hnotroot
      have ha : a ≠ P.orderedForest.root i := by
        intro ha
        apply hnotroot
        subst a
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hm := hEmem i a ha
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      by_cases hc : (P.orderedForest.isTree i).coloringTwoOfVert
          (P.orderedForest.root i) a = 0
      · apply Finset.mem_union_left
        change E.copy i a ∈ sideCandidate P G rho X Y i 0
        simpa [sideCandidate, hc] using hm
      · apply Finset.mem_union_right
        change E.copy i a ∈ sideCandidate P G rho X Y i 1
        simpa [sideCandidate, hc] using hm

/-- Full online output together with the explicitly computed bad-root sets
and their Zhao-style slack bound. -/
structure FlexibleFullOnlineEmbedding [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (X Y rootCluster : Fin P.numParts → Finset B) (slack : ℕ) where
  bad : Fin P.numParts → Finset B
  bad_eq : bad = badRootChoices P G rho Y rootCluster
  bad_subset : ∀ i, bad i ⊆ rootCluster i
  card_bad : ∀ i, #(bad i) ≤ slack
  online : FullOnlineEmbedding P G rho X Y
    (goodRootChoices P G rho Y rootCluster)

/-- Flexible/bad-set packaging of `exists_fullOnlineEmbedding`.  The bad set
is definitionally the set of root-cluster vertices which fail the required
degree inequality; once its cardinality is bounded, all remaining hypotheses
are ordinary uniform-pair, cardinal, adjacency, and disjointness facts. -/
theorem exists_flexibleFullOnlineEmbedding
    [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ) (X Y rootCluster : Fin P.numParts → Finset B) (slack : ℕ)
    (hunif : ∀ i, G.IsUniform rho (X i) (Y i))
    (hrho : rho ≤ 1)
    (hcapX : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(X i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(X i))
    (hcapY : ∀ i, (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
      (G.edgeDensity (X i) (Y i) - rho) * #(Y i))
    (hbad : ∀ i, #(badRootChoices P G rho Y rootCluster i) ≤ slack)
    (hfirst : P.numParts ≤
      #(goodRootChoices P G rho Y rootCluster ⟨0, P.numParts_pos⟩))
    (hlink : ∀ j (hj : j.val ≠ 0), ∀ z,
      z ∈ parentCandidate P G rho X Y
        (goodRootChoices P G rho Y rootCluster) j hj →
      P.numParts ≤
        #((goodRootChoices P G rho Y rootCluster j).filter (G.Adj z)))
    (hrootOutside : ∀ i z, z ∈ rootCluster i → ∀ k,
      z ∉ cleanedSide G rho (X k) (Y k) ∧
      z ∉ cleanedSide G rho (Y k) (X k))
    (hdisjoint : ∀ i k, i ≠ k →
      Disjoint
        (cleanedSide G rho (X i) (Y i) ∪
          cleanedSide G rho (Y i) (X i))
        (cleanedSide G rho (X k) (Y k) ∪
          cleanedSide G rho (Y k) (X k))) :
    Nonempty (FlexibleFullOnlineEmbedding P G rho X Y rootCluster slack) := by
  classical
  have hrootDegree : ∀ i z,
      z ∈ goodRootChoices P G rho Y rootCluster i →
      (P.orderedForest.size i : ℝ) + rho * #(Y i) ≤
        (#((Y i).filter (G.Adj z)) : ℝ) := by
    intro i z hz
    have hz' := Finset.mem_sdiff.mp hz
    have hnotbad := hz'.2
    simp only [badRootChoices, Finset.mem_filter, hz'.1, true_and] at hnotbad
    exact le_of_not_gt hnotbad
  let H := (exists_fullOnlineEmbedding P G rho X Y
    (goodRootChoices P G rho Y rootCluster) hunif hrho hcapX hcapY
      hrootDegree hfirst hlink (by
        intro i z hz k
        exact hrootOutside i z (Finset.mem_sdiff.mp hz).1 k) hdisjoint).some
  exact ⟨
    { bad := badRootChoices P G rho Y rootCluster
      bad_eq := rfl
      bad_subset := fun i ↦ Finset.filter_subset _ _
      card_bad := hbad
      online := H }⟩

end Erdos547b.ZhaoLemma59FullOnline

#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_fullOnlineEmbedding
#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_zhaoProp57_flexibleEmbedding
#print axioms Erdos547b.ZhaoLemma59FullOnline.exists_flexibleFullOnlineEmbedding
