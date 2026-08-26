/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Partite

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.RootFixedPeeling

open Finset Fintype SimpleGraph

/-- A well-founded parent certificate for a rooted forest.  Roots have rank
zero.  Every non-root has a unique lower-rank neighbour (its parent), and
adjacent vertices have distinct ranks.  Consequently a maximum-rank
non-root is a leaf; deleting it preserves the same certificate.

Unlike a condition quantified over *all* root-containing vertex subsets,
this is satisfied by ordinary rooted paths and trees: take distance from
the root of each component. -/
def HasRootedLeafPeeling {α : Type*} [Fintype α] [DecidableEq α]
    (F : SimpleGraph α) (roots : Finset α) : Prop :=
  ∃ rank : α → ℕ,
    (∀ x ∈ roots, rank x = 0) ∧
    (∀ x, x ∉ roots → ∃ p, F.Adj x p ∧ rank p < rank x ∧
      ∀ y, F.Adj x y → rank y < rank x → y = p) ∧
    ∀ ⦃x y⦄, F.Adj x y → rank x ≠ rank y

private theorem partCard_induce_compl_singleton_le {r : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {F : SimpleGraph α}
    (c : F.Coloring (Fin r)) (x : α) (i : Fin r) :
    Coloring.partCard (c.comap (Embedding.induce ({x}ᶜ : Set α)).toHom) i ≤
      Coloring.partCard c i := by
  classical
  unfold Coloring.partCard
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨y, hy, rfl⟩
  simpa using hy

private theorem partCard_delete_eq {r : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {F : SimpleGraph α}
    (c : F.Coloring (Fin r)) (x : α) :
    Coloring.partCard c (c x) =
      Coloring.partCard
        (c.comap (Embedding.induce ({x}ᶜ : Set α)).toHom) (c x) + 1 := by
  classical
  let s : Set α := {x}ᶜ
  let c' : (F.induce s).Coloring (Fin r) :=
    c.comap (Embedding.induce s).toHom
  unfold Coloring.partCard
  rw [show (Finset.univ.filter fun a : α => c a = c x) =
      insert x ((Finset.univ.filter fun a : α => c a = c x).erase x) by
    rw [Finset.insert_erase (by simp)]]
  rw [Finset.card_insert_of_notMem]
  · congr 1
    apply Finset.card_bij (fun a ha => ⟨a, by
      have := (Finset.mem_erase.mp ha).1
      simpa [s] using this⟩)
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      simpa [c', s, ha.2]
    · intro a₁ ha₁ a₂ ha₂ h
      exact Subtype.ext_iff.mp h
    · intro a ha
      refine ⟨a.1, ?_, rfl⟩
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.2, by simpa [c', s] using ha⟩
  · simp

private theorem rooted_embedding_aux
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (F : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (roots : Finset α) (hrootIndependent : F.IsIndepSet (roots : Set α))
    (hpeel : HasRootedLeafPeeling F roots)
    (c : F.Coloring (Fin 2)) (A : Fin 2 → Finset β)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (rootImage : {x // x ∈ roots} → β)
    (hrootImageInj : Function.Injective rootImage)
    (hrootImageMem : ∀ x : {x // x ∈ roots}, rootImage x ∈ A (c x))
    (hcap : ∀ i, Coloring.partCard c i ≤ (A i).card)
    (hdeg : ∀ i j, i ≠ j → ∀ v ∈ A i,
      Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ A j).card)
    (n : ℕ) (hn : (Finset.univ \ roots).card = n) :
    ∃ f : F.Copy G,
      Copy.RespectsParts c A f ∧
      ∀ x : {x // x ∈ roots}, f x = rootImage x := by
  classical
  induction n generalizing α with
  | zero =>
      have hcover : roots = Finset.univ := by
        have hempty : Finset.univ \ roots = ∅ := Finset.card_eq_zero.mp hn
        rw [Finset.sdiff_eq_empty_iff_subset] at hempty
        exact Finset.Subset.antisymm (Finset.subset_univ _) hempty
      let fMap : α → β := fun x => rootImage ⟨x, by simp [hcover]⟩
      have hfInj : Function.Injective fMap := by
        intro x y hxy
        have hsub : (⟨x, by simp [hcover]⟩ : {x // x ∈ roots}) =
            ⟨y, by simp [hcover]⟩ := by
          apply hrootImageInj
          exact hxy
        exact Subtype.ext_iff.mp hsub
      have hfAdj : ∀ ⦃x y⦄, F.Adj x y → G.Adj (fMap x) (fMap y) := by
        intro x y hxy
        exact False.elim (hrootIndependent (by simp [hcover]) (by simp [hcover])
          hxy.ne hxy)
      let f : F.Copy G := ⟨⟨fMap, fun {_ _} h => hfAdj h⟩, hfInj⟩
      refine ⟨f, ?_, ?_⟩
      · intro x
        simpa [f, fMap] using hrootImageMem ⟨x, by simp [hcover]⟩
      · intro x
        rfl
  | succ n ih =>
      rcases hpeel with ⟨rank, hrootRank, hparent, hrankNe⟩
      have hremaining : (Finset.univ \ roots).Nonempty := by
        exact Finset.card_pos.mp (by omega)
      obtain ⟨x, hxRemaining, hmax⟩ :=
        Finset.exists_max_image (Finset.univ \ roots) rank hremaining
      have hxRoot : x ∉ roots := (Finset.mem_sdiff.mp hxRemaining).2
      obtain ⟨p, hxp, hpRank, hpLowerUnique⟩ := hparent x hxRoot
      have hxRankPos : 0 < rank x := (Nat.zero_le (rank p)).trans_lt hpRank
      have hpUnique : ∀ y ∈ Finset.univ, F.Adj x y → y = p := by
        intro y _ hxy
        apply hpLowerUnique y hxy
        by_cases hyRoot : y ∈ roots
        · simpa [hrootRank y hyRoot] using hxRankPos
        · have hyRemaining : y ∈ Finset.univ \ roots := by simp [hyRoot]
          have hyLe := hmax y hyRemaining
          have hyNe : rank y ≠ rank x := (hrankNe hxy).symm
          exact Nat.lt_of_le_of_ne hyLe hyNe
      let s : Set α := {x}ᶜ
      let F' : SimpleGraph s := F.induce s
      let roots' : Finset s := Finset.univ.filter fun y => (y : α) ∈ roots
      let c' : F'.Coloring (Fin 2) := c.comap (Embedding.induce s).toHom
      let A' := A
      have hxpNe : p ≠ x := hxp.ne'
      let ps : s := ⟨p, by simpa [s] using hxpNe⟩
      have hrootsCard : roots'.card = roots.card := by
        apply Finset.card_bij (s := roots') (t := roots) (fun y hy => (y : α))
        · intro y hy
          exact (Finset.mem_filter.mp hy).2
        · intro a ha b hb hab
          exact Subtype.ext hab
        · intro y hy
          refine ⟨⟨y, by simpa [s] using fun h : y = x => hxRoot (h ▸ hy)⟩, ?_, rfl⟩
          simp [roots', hy]
      have hn' : (Finset.univ \ roots').card = n := by
        have hcardS : Fintype.card s = Fintype.card α - 1 := by
          change Fintype.card {a : α // ¬a = x} = Fintype.card α - 1
          rw [Fintype.card_subtype_compl]
          simp
        have hrootsLe : roots.card ≤ Fintype.card α := Finset.card_le_univ roots
        have hrootsLeS : roots'.card ≤ Fintype.card s := Finset.card_le_univ roots'
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ roots'),
          Finset.card_univ, hcardS, hrootsCard]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ roots),
          Finset.card_univ] at hn
        omega
      have hrootIndependent' : F'.IsIndepSet (roots' : Set s) := by
        intro a ha b hb hab hAdj
        exact hrootIndependent (by simpa [roots'] using ha)
          (by simpa [roots'] using hb) (fun h => hab (Subtype.ext h)) hAdj
      have hpeel' : HasRootedLeafPeeling F' roots' := by
        let rank' : s → ℕ := fun y => rank y
        refine ⟨rank', ?_, ?_, ?_⟩
        · intro y hy
          exact hrootRank y ((Finset.mem_filter.mp hy).2)
        · intro y hyRoot'
          have hyRoot : (y : α) ∉ roots := by
            intro hy
            exact hyRoot' (by simp [roots', hy])
          obtain ⟨parent, hyp, hpRank', hpUnique'⟩ := hparent y hyRoot
          have hyRemaining : (y : α) ∈ Finset.univ \ roots := by simp [hyRoot]
          have hyLeMax : rank y ≤ rank x := hmax y hyRemaining
          have hparentNeX : parent ≠ x := by
            intro h
            subst parent
            omega
          let parent' : s := ⟨parent, by simpa [s] using hparentNeX⟩
          refine ⟨parent', ?_, hpRank', ?_⟩
          · simpa [F', parent'] using hyp
          · intro z hyz hzRank
            have hzEq : (z : α) = parent :=
              hpUnique' z (by simpa [F'] using hyz) hzRank
            exact Subtype.ext hzEq
        · intro y z hyz
          exact hrankNe (by simpa [F'] using hyz)
      let rootEquiv : {y // y ∈ roots'} ≃ {y // y ∈ roots} :=
        { toFun := fun y => ⟨y.1.1, (Finset.mem_filter.mp y.2).2⟩
          invFun := fun y => ⟨⟨y.1, by
            have hyx : y.1 ≠ x := fun h => hxRoot (h ▸ y.2)
            simpa [s] using hyx⟩, by simp [roots', y.2]⟩
          left_inv := fun y => by ext; rfl
          right_inv := fun y => by ext; rfl }
      let rootImage' : {y // y ∈ roots'} → β := fun y => rootImage (rootEquiv y)
      have hrootImageInj' : Function.Injective rootImage' :=
        hrootImageInj.comp rootEquiv.injective
      have hrootImageMem' : ∀ y : {y // y ∈ roots'},
          rootImage' y ∈ A' (c' y) := by
        intro y
        simpa [rootImage', rootEquiv, A', c'] using hrootImageMem (rootEquiv y)
      have hcap' : ∀ i, Coloring.partCard c' i ≤ (A' i).card := by
        intro i
        exact (partCard_induce_compl_singleton_le c x i).trans (hcap i)
      have hdeg' : ∀ i j, i ≠ j → ∀ v ∈ A' i,
          Coloring.partCard c' j ≤ ((G.neighborFinset v) ∩ A' j).card := by
        intro i j hij v hv
        exact (partCard_induce_compl_singleton_le c x j).trans
          (hdeg i j hij v hv)
      obtain ⟨f, hfparts, hfroots⟩ :=
        ih F' roots' hrootIndependent' hpeel' c' rootImage'
          hrootImageInj' hrootImageMem' hcap' hdeg' hn'
      have hcolors : c p ≠ c x := c.valid hxp.symm
      have hpPart : f ps ∈ A (c p) := by simpa [A', c', ps] using hfparts ps
      let used : Finset β :=
        (Finset.univ.filter fun a : s => c' a = c x).image f
      have husedCard : used.card = Coloring.partCard c' (c x) := by
        dsimp only [used, Coloring.partCard]
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
      have hpartCard : Coloring.partCard c (c x) =
          Coloring.partCard c' (c x) + 1 := partCard_delete_eq c x
      have hcand : used.card < ((G.neighborFinset (f ps)) ∩ A (c x)).card := by
        rw [husedCard]
        have := hdeg (c p) (c x) hcolors (f ps) hpPart
        omega
      obtain ⟨w, hwCand, hwUnused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hcand
      have hwAdj : G.Adj (f ps) w :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hwCand).1
      have hwPart : w ∈ A (c x) := (Finset.mem_inter.mp hwCand).2
      have hwNotRange : ∀ a : s, w ≠ f a := by
        intro a hwa
        by_cases hc : c a = c x
        · apply hwUnused
          exact Finset.mem_image.mpr ⟨a, by simpa [c'] using hc, hwa.symm⟩
        · have hdisj := hA (Set.mem_univ (c x)) (Set.mem_univ (c a))
            (fun h => hc h.symm)
          have hfa : f a ∈ A (c a) := by simpa [A', c'] using hfparts a
          rw [← hwa] at hfa
          exact Finset.disjoint_left.mp hdisj hwPart hfa
      let fMap : α → β := fun a =>
        if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      have hfMapAdj : ∀ ⦃a b⦄, F.Adj a b → G.Adj (fMap a) (fMap b) := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          have hbp : b = p := hpUnique b (Finset.mem_univ b) hab
          subst b
          simpa [fMap, ps, hxp.ne, hxp.ne'] using hwAdj.symm
        · by_cases hb : b = x
          · subst b
            have hap : a = p := hpUnique a (Finset.mem_univ a) hab.symm
            subst a
            simpa [fMap, ps, hxp.ne, hxp.ne'] using hwAdj
          · have hab' : F'.Adj (⟨a, by simpa [s] using ha⟩ : s)
                ⟨b, by simpa [s] using hb⟩ := by simpa [F'] using hab
            have hm := f.toHom.map_rel hab'
            simpa [fMap, ha, hb] using hm
      have hfMapInj : Function.Injective fMap := by
        intro a b hab
        by_cases ha : a = x
        · subst a
          by_cases hb : b = x
          · exact hb.symm
          · exfalso
            apply hwNotRange ⟨b, by simpa [s] using hb⟩
            simpa [fMap, hb] using hab
        · by_cases hb : b = x
          · subst b
            exfalso
            apply hwNotRange ⟨a, by simpa [s] using ha⟩
            simpa [fMap, ha] using hab.symm
          · have hsub : (⟨a, by simpa [s] using ha⟩ : s) =
                ⟨b, by simpa [s] using hb⟩ := by
              apply f.injective
              simpa [fMap, ha, hb] using hab
            exact Subtype.ext_iff.mp hsub
      let f' : F.Copy G := ⟨⟨fMap, fun {_ _} h => hfMapAdj h⟩, hfMapInj⟩
      refine ⟨f', ?_, ?_⟩
      · intro a
        by_cases ha : a = x
        · subst a
          simpa [f', fMap] using hwPart
        · simpa [f', fMap, ha, A', c'] using
            hfparts ⟨a, by simpa [s] using ha⟩
      · intro r
        have hrx : (r : α) ≠ x := fun h => hxRoot (h ▸ r.2)
        let r' : {y // y ∈ roots'} :=
          ⟨⟨r, by simpa [s] using hrx⟩, by simp [roots', r.2]⟩
        have hrEq : rootEquiv r' = r := by ext; rfl
        have := hfroots r'
        simpa [f', fMap, hrx, rootImage', hrEq, r'] using this

/-- Class-sharp greedy embedding of a rooted bipartite forest with all root
images prescribed simultaneously.  The capacity and degree thresholds are
the two target colour-class sizes, not the total forest order. -/
theorem rooted_forest_embedding_respecting_parts
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (F : SimpleGraph α) (G : SimpleGraph β) [DecidableRel G.Adj]
    (roots : Finset α) (hrootIndependent : F.IsIndepSet (roots : Set α))
    (hpeel : HasRootedLeafPeeling F roots)
    (c : F.Coloring (Fin 2)) (A : Fin 2 → Finset β)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (rootImage : {x // x ∈ roots} → β)
    (hrootImageInj : Function.Injective rootImage)
    (hrootImageMem : ∀ x : {x // x ∈ roots}, rootImage x ∈ A (c x))
    (hcap : ∀ i, Coloring.partCard c i ≤ (A i).card)
    (hdeg : ∀ i j, i ≠ j → ∀ v ∈ A i,
      Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ A j).card) :
    ∃ f : F.Copy G,
      Copy.RespectsParts c A f ∧
      ∀ x : {x // x ∈ roots}, f x = rootImage x := by
  apply rooted_embedding_aux F G roots hrootIndependent hpeel c A hA rootImage
    hrootImageInj hrootImageMem hcap hdeg (Finset.univ \ roots).card rfl

end Erdos547b.RootFixedPeeling

#print axioms Erdos547b.RootFixedPeeling.rooted_forest_embedding_respecting_parts
