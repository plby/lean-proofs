/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EC2
import ErdosProblems.Erdos547b.Partite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Lean.Elab.Tactic.Omega
import ErdosProblems.Erdos547b.Claim712NaturalSubtree
import ErdosProblems.Erdos547b.Claim712ForestGlue
import ErdosProblems.Erdos547b.Claim712Reservoir

open scoped SimpleGraph

noncomputable section

namespace Erdos547Claim712

open Finset SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

private theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · exact Or.inl h
  · right
    subst i
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl

theorem degreeInto_eq_card_neighbor_inter
    (G : SimpleGraph W) [DecidableRel G.Adj] (w : W) (A : Finset W) :
    Erdos547EC2.degreeInto G w A = ((G.neighborFinset w) ∩ A).card := by
  classical
  unfold Erdos547EC2.degreeInto
  congr 1
  ext x
  simp [and_comm]

/-- Cardinality of one class of an arbitrary two-labeling.  Unlike a graph
coloring, label zero is allowed to contain edges. -/
def labelCard (c : V → Fin 2) (i : Fin 2) : ℕ :=
  (Finset.univ.filter fun x => c x = i).card

@[simp] theorem labelCard_eq_card_filter (c : V → Fin 2) (i : Fin 2) :
    labelCard c i = (Finset.univ.filter fun x => c x = i).card := rfl

theorem labelCard_induce_compl_singleton_le (c : V → Fin 2) (x : V) (i : Fin 2) :
    labelCard (fun y : ({x}ᶜ : Set V) => c y) i ≤ labelCard c i := by
  classical
  unfold labelCard
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨y, hy, rfl⟩
  simpa using hy

theorem labelCard_induce_compl_singleton_eq_of_ne
    (c : V → Fin 2) (x : V) (i : Fin 2) (hxi : c x ≠ i) :
    labelCard (fun y : ({x}ᶜ : Set V) => c y) i = labelCard c i := by
  classical
  unfold labelCard
  apply Finset.card_bij
    (s := Finset.univ.filter fun y : ({x}ᶜ : Set V) => c y = i)
    (t := Finset.univ.filter fun y : V => c y = i)
    (fun y _ => (y : V))
  · intro y hy
    simpa using hy
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro y hy
    have hyx : y ≠ x := by
      intro h
      subst y
      exact hxi (by simpa using (Finset.mem_filter.mp hy).2)
    refine ⟨⟨y, by simpa using hyx⟩, ?_, rfl⟩
    simpa using hy

/-- Leaf-induction embedding with an arbitrary two-labeling.  Edges may lie
inside label zero; label one is independent.  The host compatibility relation
is therefore exactly “at least one endpoint has label zero”. -/
private theorem tree_embedding_respecting_semibipartition_aux
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hT : T.IsTree) (c : V → Fin 2) (A : Fin 2 → Finset W)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (hcompat : ∀ ⦃x y⦄, T.Adj x y → c x = 0 ∨ c y = 0)
    (hcap : ∀ i, labelCard c i ≤ (A i).card)
    (hdeg : ∀ i j, (i = 0 ∨ j = 0) → ∀ w ∈ A i,
      labelCard c j ≤ ((G.neighborFinset w) ∩ A j).card)
    (n : ℕ) (hcard : Fintype.card V = n + 1) :
    ∃ f : Copy T G, ∀ x, f x ∈ A (c x) := by
  classical
  induction n generalizing V W with
  | zero =>
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
      have hpos : 0 < labelCard c (c x) := by
        unfold labelCard
        exact Finset.card_pos.mpr ⟨x, by simp⟩
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (hpos.trans_le (hcap (c x)))
      let f : V → W := fun _ => w
      let Fcopy : Copy T G := ⟨⟨f, by
        intro u v huv
        exact False.elim (T.ne_of_adj huv (by rw [hx u, hx v]))⟩, by
          intro u v _
          rw [hx u, hx v]⟩
      refine ⟨Fcopy, ?_⟩
      · intro u
        dsimp only [Fcopy]
        change f u ∈ A (c u)
        simpa [f, hx u, hx x] using hw
  | succ n ih =>
      have hlarge : 1 < Fintype.card V := by omega
      letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hlarge
      obtain ⟨x, hx⟩ :=
        @IsTree.exists_vert_degree_one_of_nontrivial V T _ (inferInstance) _ hT
      obtain ⟨p, hxp, hpuniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
      let s : Set V := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let c' : s → Fin 2 := fun y => c y
      have hcard' : Fintype.card s = n + 1 := by
        have hc := Fintype.card_subtype_compl (fun a : V => a = x)
        change Fintype.card {a : V // ¬a = x} = n + 1
        rw [hc, hcard]
        simp
      have hT' : T'.IsTree := by
        exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hx,
          hT.isAcyclic.induce s⟩
      have hcompat' : ∀ ⦃u v⦄, T'.Adj u v → c' u = 0 ∨ c' v = 0 := by
        intro u v huv
        exact hcompat huv
      have hcap' : ∀ i, labelCard c' i ≤ (A i).card := by
        intro i
        exact (labelCard_induce_compl_singleton_le c x i).trans (hcap i)
      have hdeg' : ∀ i j, (i = 0 ∨ j = 0) → ∀ w ∈ A i,
          labelCard c' j ≤ ((G.neighborFinset w) ∩ A j).card := by
        intro i j hij w hw
        exact (labelCard_induce_compl_singleton_le c x j).trans (hdeg i j hij w hw)
      obtain ⟨f, hf⟩ := ih T' G hT' c' A hA hcompat' hcap' hdeg' hcard'
      let ps : s := ⟨p, by simpa [s] using hxp.ne'⟩
      have hcomp : c p = 0 ∨ c x = 0 := hcompat hxp.symm
      have hpPart : f ps ∈ A (c p) := by simpa [c', ps] using hf ps
      let used : Finset W :=
        (Finset.univ.filter fun a : s => c' a = c x).image f
      have hused : used.card = labelCard c' (c x) := by
        dsimp only [used, labelCard]
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
      have hpart : labelCard c (c x) = labelCard c' (c x) + 1 := by
        unfold labelCard
        rw [show (Finset.univ.filter fun a : V => c a = c x) =
            insert x ((Finset.univ.filter fun a : V => c a = c x).erase x) by
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
            constructor
            · exact a.2
            · simpa [c', s] using ha
        · simp
      have hcand : used.card < ((G.neighborFinset (f ps)) ∩ A (c x)).card := by
        rw [hused]
        have hd := hdeg (c p) (c x) hcomp (f ps) hpPart
        omega
      obtain ⟨w, hwCand, hwUnused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hcand
      have hwAdj : G.Adj (f ps) w :=
        (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hwCand).1
      have hwPart : w ∈ A (c x) := (Finset.mem_inter.mp hwCand).2
      have hwNotRange : ∀ a : s, w ≠ f a := by
        intro a hwa
        by_cases hca : c a = c x
        · apply hwUnused
          exact Finset.mem_image.mpr ⟨a, by simpa [c'] using hca, hwa.symm⟩
        · have hdisj := hA (Set.mem_univ (c x)) (Set.mem_univ (c a))
            (fun h => hca h.symm)
          have hfa : f a ∈ A (c a) := by simpa [c'] using hf a
          rw [← hwa] at hfa
          exact (Finset.disjoint_left.mp hdisj hwPart hfa).elim
      let F : V → W := fun a => if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      refine ⟨⟨⟨F, ?_⟩, ?_⟩, ?_⟩
      · intro u v huv
        by_cases hu : u = x
        · subst u
          have hvp : v = p := hpuniq v huv
          subst v
          simpa [F, ps, hxp.ne, hxp.ne'] using hwAdj.symm
        · by_cases hv : v = x
          · subst v
            have hup : u = p := hpuniq u huv.symm
            subst u
            simpa [F, ps, hxp.ne, hxp.ne'] using hwAdj
          · have huv' : T'.Adj (⟨u, by simpa [s] using hu⟩ : s)
                ⟨v, by simpa [s] using hv⟩ := by simpa [T'] using huv
            have hm := f.toHom.map_adj huv'
            simpa [F, hu, hv] using hm
      · intro u v huv
        by_cases hu : u = x
        · subst u
          by_cases hv : v = x
          · exact hv.symm
          · exfalso
            apply hwNotRange ⟨v, by simpa [s] using hv⟩
            simpa [F, hv] using huv
        · by_cases hv : v = x
          · subst v
            exfalso
            apply hwNotRange ⟨u, by simpa [s] using hu⟩
            simpa [F, hu] using huv.symm
          · have heq : (⟨u, by simpa [s] using hu⟩ : s) =
                ⟨v, by simpa [s] using hv⟩ := by
              apply f.injective
              simpa [F, hu, hv] using huv
            exact Subtype.ext_iff.mp heq
      · intro u
        by_cases hu : u = x
        · subst u
          change F x ∈ A (c x)
          simpa [F] using hwPart
        · change F u ∈ A (c u)
          simpa [F, hu, c'] using hf ⟨u, by simpa [s] using hu⟩

/-- Public semibipartite embedding lemma used in Fact 7.2(2). -/
theorem tree_embedding_respecting_semibipartition
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel G.Adj]
    (hT : T.IsTree) (c : V → Fin 2) (A : Fin 2 → Finset W)
    (hA : Set.PairwiseDisjoint Set.univ A)
    (hcompat : ∀ ⦃x y⦄, T.Adj x y → c x = 0 ∨ c y = 0)
    (hcap : ∀ i, labelCard c i ≤ (A i).card)
    (hdeg : ∀ i j, (i = 0 ∨ j = 0) → ∀ w ∈ A i,
      labelCard c j ≤ ((G.neighborFinset w) ∩ A j).card) :
    ∃ f : Copy T G, ∀ x, f x ∈ A (c x) := by
  apply tree_embedding_respecting_semibipartition_aux T G hT c A hA hcompat hcap hdeg
    (Fintype.card V - 1)
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hT.connected.nonempty
  omega

/-- If one side of a vertex partition is independent and has no leaves, then
it is strictly smaller than the other side.  This is the counting fact behind
the delayed-leaf proof of Zhao's Fact 7.2(2).  Internal edges in `U₀` are
allowed. -/
theorem independent_side_card_lt_of_no_leaves
    (T : SimpleGraph V) [DecidableRel T.Adj] (U₀ U₁ : Finset V)
    (hT : T.IsTree) (hdisj : Disjoint U₀ U₁)
    (hcover : U₀ ∪ U₁ = Finset.univ) (hU₀ : U₀.Nonempty)
    (hindep : T.IsIndepSet (U₁ : Set V))
    (hnoleaf : ∀ x ∈ U₁, T.degree x ≠ 1) :
    U₁.card < U₀.card := by
  classical
  by_cases hU₁ : U₁.Nonempty
  · have hcardV : Fintype.card V = U₀.card + U₁.card := by
      rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj]
    have htwo : 1 < Fintype.card V := by
      have h0 := Finset.card_pos.mpr hU₀
      have h1 := Finset.card_pos.mpr hU₁
      omega
    letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp htwo
    let H : SimpleGraph V := T.between (U₁ : Set V) (U₀ : Set V)
    have hdeg (x : V) (hx : x ∈ U₁) : H.degree x = T.degree x := by
      rw [← H.card_neighborFinset_eq_degree, ← T.card_neighborFinset_eq_degree]
      congr 1
      ext y
      simp only [mem_neighborFinset, H, between_adj]
      constructor
      · exact fun h => h.1
      · intro hxy
        have hy : y ∈ U₀ ∨ y ∈ U₁ := by
          have : y ∈ U₀ ∪ U₁ := by simpa [hcover]
          exact Finset.mem_union.mp this
        rcases hy with hy0 | hy1
        · exact ⟨hxy, Or.inl ⟨hx, hy0⟩⟩
        · exact False.elim (hindep hx hy1 hxy.ne hxy)
    have hpoint (x : V) (hx : x ∈ U₁) : 2 ≤ H.degree x := by
      rw [hdeg x hx]
      have hpos := hT.preconnected.degree_pos_of_nontrivial x
      have hne := hnoleaf x hx
      omega
    have hsumLower : 2 * U₁.card ≤ ∑ x ∈ U₁, H.degree x := by
      calc
        2 * U₁.card = ∑ _x ∈ U₁, 2 := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun x hx => hpoint x hx
    have hbip : H.IsBipartiteWith (U₁ : Set V) (U₀ : Set V) :=
      between_isBipartiteWith (Finset.disjoint_coe.mpr hdisj.symm)
    have hsum : (∑ x ∈ U₁, H.degree x) = H.edgeFinset.card :=
      isBipartiteWith_sum_degrees_eq_card_edges hbip
    have hedgeLe : H.edgeFinset.card ≤ T.edgeFinset.card :=
      Finset.card_le_card (edgeFinset_mono between_le)
    have htreeEdges := hT.card_edgeFinset
    rw [hsum] at hsumLower
    rw [hcardV] at htreeEdges
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at hU₁
    subst U₁
    simpa using Finset.card_pos.mpr hU₀

/-- Label a partition by zero on its distinguished (possibly non-independent)
side and one on its complement. -/
def partitionLabel (U₀ : Finset V) (x : V) : Fin 2 :=
  if x ∈ U₀ then 0 else 1

theorem labelCard_partitionLabel_zero (U₀ : Finset V) :
    labelCard (partitionLabel U₀) 0 = U₀.card := by
  classical
  unfold labelCard
  congr 1
  ext x
  simp [partitionLabel]

theorem labelCard_partitionLabel_one_of_partition (U₀ U₁ : Finset V)
    (hdisj : Disjoint U₀ U₁) (hcover : U₀ ∪ U₁ = Finset.univ) :
    labelCard (partitionLabel U₀) 1 = U₁.card := by
  classical
  unfold labelCard
  congr 1
  ext x
  have hxcover : x ∈ U₀ ∨ x ∈ U₁ := by
    have : x ∈ U₀ ∪ U₁ := by simpa [hcover]
    exact Finset.mem_union.mp this
  constructor
  · intro hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases hx0 : x ∈ U₀
    · simp [partitionLabel, hx0] at hx
    · exact hxcover.resolve_left hx0
  · intro hx1
    have hx0 : x ∉ U₀ := fun hx0 => Finset.disjoint_left.mp hdisj hx0 hx1
    simp [partitionLabel, hx0]

private theorem fact72_part2_aux
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree)
    (U₀ U₁ : Finset V) (hdisjU : Disjoint U₀ U₁)
    (hcoverU : U₀ ∪ U₁ = Finset.univ) (hU₀ : U₀.Nonempty)
    (hindep : T.IsIndepSet (U₁ : Set V))
    (A B : Finset W) (hdisjAB : Disjoint A B) (hA : A.Nonempty)
    (hAA : ∀ a ∈ A, U₀.card ≤ Erdos547EC2.degreeInto G a A)
    (hAB : ∀ a ∈ A, U₀.card ≤ Erdos547EC2.degreeInto G a B)
    (hBA : ∀ b ∈ B, U₀.card ≤ Erdos547EC2.degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a)
    (n : ℕ) (hcard : Fintype.card V = n + 1) :
    ∃ f : Copy T G, ∀ x ∈ U₀, f x ∈ A := by
  classical
  induction n generalizing V W with
  | zero =>
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
      obtain ⟨a, ha⟩ := hA
      let F : V → W := fun _ => a
      let f : Copy T G := ⟨⟨F, by
        intro u v huv
        exact False.elim (T.ne_of_adj huv (by rw [hx u, hx v]))⟩, by
          intro u v _
          rw [hx u, hx v]⟩
      refine ⟨f, ?_⟩
      intro u hu
      dsimp only [f]
      change F u ∈ A
      exact ha
  | succ n ih =>
      by_cases hleaf : ∃ x ∈ U₁, T.degree x = 1
      · obtain ⟨x, hxU₁, hxdeg⟩ := hleaf
        have hxU₀ : x ∉ U₀ := fun hx => Finset.disjoint_left.mp hdisjU hx hxU₁
        obtain ⟨p, hxp, hpuniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hxdeg
        have hpU₀ : p ∈ U₀ := by
          have hpcover : p ∈ U₀ ∨ p ∈ U₁ := by
            have : p ∈ U₀ ∪ U₁ := by simpa [hcoverU]
            exact Finset.mem_union.mp this
          exact hpcover.resolve_right fun hpU₁ => hindep hxU₁ hpU₁ hxp.ne hxp
        let s : Set V := {x}ᶜ
        let T' : SimpleGraph s := T.induce s
        let U₀' : Finset s := Finset.univ.filter fun y => (y : V) ∈ U₀
        let U₁' : Finset s := Finset.univ.filter fun y => (y : V) ∈ U₁
        have hcard' : Fintype.card s = n + 1 := by
          have hc := Fintype.card_subtype_compl (fun a : V => a = x)
          change Fintype.card {a : V // ¬a = x} = n + 1
          rw [hc, hcard]
          simp
        have hT' : T'.IsTree := by
          exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
            hT.isAcyclic.induce s⟩
        have hU₀card : U₀'.card = U₀.card := by
          dsimp only [U₀']
          apply Finset.card_bij
            (s := Finset.univ.filter fun y : s => (y : V) ∈ U₀)
            (t := U₀) (fun y _ => (y : V))
          · intro y hy
            simpa using (Finset.mem_filter.mp hy).2
          · intro a ha b hb hab
            exact Subtype.ext hab
          · intro y hy
            refine ⟨⟨y, by simpa [s] using fun h : y = x => hxU₀ (h ▸ hy)⟩, ?_, rfl⟩
            simp [hy]
        have hdisjU' : Disjoint U₀' U₁' := by
          rw [Finset.disjoint_left]
          intro y hy0 hy1
          exact Finset.disjoint_left.mp hdisjU
            (Finset.mem_filter.mp hy0).2 (Finset.mem_filter.mp hy1).2
        have hcoverU' : U₀' ∪ U₁' = Finset.univ := by
          dsimp only [U₀', U₁']
          ext y
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          have : (y : V) ∈ U₀ ∪ U₁ := by simpa [hcoverU]
          exact iff_true_intro (Finset.mem_union.mp this)
        have hU₀' : U₀'.Nonempty := by
          obtain ⟨u, hu⟩ := hU₀
          have hux : u ≠ x := fun h => hxU₀ (h ▸ hu)
          exact ⟨⟨u, by simpa [s] using hux⟩, by simp [U₀', hu]⟩
        have hindep' : T'.IsIndepSet (U₁' : Set s) := by
          intro u hu v hv huv hadj
          exact hindep (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
            (fun h => huv (Subtype.ext h)) hadj
        have hAA' : ∀ a ∈ A, U₀'.card ≤ Erdos547EC2.degreeInto G a A := by
          simpa only [hU₀card] using hAA
        have hAB' : ∀ a ∈ A, U₀'.card ≤ Erdos547EC2.degreeInto G a B := by
          simpa only [hU₀card] using hAB
        have hBA' : ∀ b ∈ B, U₀'.card ≤ Erdos547EC2.degreeInto G b A := by
          simpa only [hU₀card] using hBA
        have hdegreeA' : ∀ a ∈ A, Fintype.card s - 1 ≤ G.degree a := by
          intro a ha
          rw [hcard']
          have hd := hdegreeA a ha
          rw [hcard] at hd
          omega
        obtain ⟨f, hfA⟩ := ih T' G hT' U₀' U₁' hdisjU' hcoverU' hU₀'
          hindep' A B hdisjAB hA hAA' hAB' hBA' hdegreeA' hcard'
        let ps : s := ⟨p, by simpa [s] using hxp.ne'⟩
        have hfpA : f ps ∈ A := by
          apply hfA ps
          dsimp only [U₀']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hpU₀
        let usedWithoutParent : Finset W := (Finset.univ.erase ps).image f
        have husedCard : usedWithoutParent.card = Fintype.card s - 1 := by
          dsimp only [usedWithoutParent]
          calc
            ((Finset.univ.erase ps).image f).card = (Finset.univ.erase ps).card :=
              Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
            _ = Fintype.card s - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ ps), Finset.card_univ]
        have hneighborCard : usedWithoutParent.card < (G.neighborFinset (f ps)).card := by
          rw [husedCard, G.card_neighborFinset_eq_degree]
          rw [hcard']
          have hd := hdegreeA (f ps) hfpA
          rw [hcard] at hd
          omega
        obtain ⟨w, hwNeighbor, hwUnused⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hneighborCard
        have hwAdj : G.Adj (f ps) w := (G.mem_neighborFinset _ _).mp hwNeighbor
        have hwNotRange : ∀ y : s, w ≠ f y := by
          intro y hwy
          by_cases hy : y = ps
          · subst y
            exact hwAdj.ne' hwy
          · apply hwUnused
            exact Finset.mem_image.mpr
              ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, hwy.symm⟩
        let F : V → W := fun y => if h : y = x then w else f ⟨y, by simpa [s] using h⟩
        let Fcopy : Copy T G := ⟨⟨F, by
          intro u v huv
          by_cases hu : u = x
          · subst u
            have hvp : v = p := hpuniq v huv
            subst v
            simpa [F, ps, hxp.ne, hxp.ne'] using hwAdj.symm
          · by_cases hv : v = x
            · subst v
              have hup : u = p := hpuniq u huv.symm
              subst u
              simpa [F, ps, hxp.ne, hxp.ne'] using hwAdj
            · have huv' : T'.Adj (⟨u, by simpa [s] using hu⟩ : s)
                  ⟨v, by simpa [s] using hv⟩ := by simpa [T'] using huv
              have hm := f.toHom.map_adj huv'
              simpa [F, hu, hv] using hm⟩, by
          intro u v huv
          by_cases hu : u = x
          · subst u
            by_cases hv : v = x
            · exact hv.symm
            · exfalso
              apply hwNotRange ⟨v, by simpa [s] using hv⟩
              simpa [F, hv] using huv
          · by_cases hv : v = x
            · subst v
              exfalso
              apply hwNotRange ⟨u, by simpa [s] using hu⟩
              simpa [F, hu] using huv.symm
            · have heq : (⟨u, by simpa [s] using hu⟩ : s) =
                  ⟨v, by simpa [s] using hv⟩ := by
                apply f.injective
                simpa [F, hu, hv] using huv
              exact Subtype.ext_iff.mp heq⟩
        refine ⟨Fcopy, ?_⟩
        intro u hu
        have hux : u ≠ x := fun h => hxU₀ (h ▸ hu)
        dsimp only [Fcopy]
        change F u ∈ A
        simpa [F, hux] using hfA ⟨u, by simpa [s] using hux⟩ (by simp [U₀', hu])
      · have hnoleaf : ∀ x ∈ U₁, T.degree x ≠ 1 := by
          intro x hx hdeg
          exact hleaf ⟨x, hx, hdeg⟩
        have hcardSides := independent_side_card_lt_of_no_leaves
          T U₀ U₁ hT hdisjU hcoverU hU₀ hindep hnoleaf
        let c : V → Fin 2 := partitionLabel U₀
        let P : Fin 2 → Finset W := fun i => if i = 0 then A else B
        have hP0 : P 0 = A := by simp [P]
        have hP1 : P 1 = B := by simp [P]
        have hPc0 : labelCard c 0 = U₀.card := by
          simpa [c] using labelCard_partitionLabel_zero U₀
        have hPc1 : labelCard c 1 = U₁.card := by
          simpa [c] using labelCard_partitionLabel_one_of_partition U₀ U₁ hdisjU hcoverU
        have hPdisj : Set.PairwiseDisjoint Set.univ P := by
          intro i hi j hj hij
          rcases fin_two_eq_zero_or_one i with rfl | rfl <;>
            rcases fin_two_eq_zero_or_one j with rfl | rfl
          · exact (hij rfl).elim
          · change Disjoint A B
            exact hdisjAB
          · change Disjoint B A
            exact hdisjAB.symm
          · exact (hij rfl).elim
        have hcompat : ∀ ⦃x y⦄, T.Adj x y → c x = 0 ∨ c y = 0 := by
          intro x y hxy
          by_contra h
          push_neg at h
          have hx1 : x ∈ U₁ := by
            have hxcover : x ∈ U₀ ∨ x ∈ U₁ := by
              have : x ∈ U₀ ∪ U₁ := by simpa [hcoverU]
              exact Finset.mem_union.mp this
            exact hxcover.resolve_left (by simpa [c, partitionLabel] using h.1)
          have hy1 : y ∈ U₁ := by
            have hycover : y ∈ U₀ ∨ y ∈ U₁ := by
              have : y ∈ U₀ ∪ U₁ := by simpa [hcoverU]
              exact Finset.mem_union.mp this
            exact hycover.resolve_left (by simpa [c, partitionLabel] using h.2)
          exact hindep hx1 hy1 hxy.ne hxy
        have hcap : ∀ i, labelCard c i ≤ (P i).card := by
          intro i
          rcases fin_two_eq_zero_or_one i with rfl | rfl
          · rw [hPc0, hP0]
            obtain ⟨a, ha⟩ := hA
            exact (hAA a ha).trans (Erdos547EC2.degreeInto_le_card G a A)
          · rw [hPc1, hP1]
            obtain ⟨a, ha⟩ := hA
            exact hcardSides.le.trans (hAB a ha) |>.trans
              (Erdos547EC2.degreeInto_le_card G a B)
        have hdeg : ∀ i j, (i = 0 ∨ j = 0) → ∀ w ∈ P i,
            labelCard c j ≤ ((G.neighborFinset w) ∩ P j).card := by
          intro i j hij w hw
          rcases fin_two_eq_zero_or_one i with rfl | rfl <;>
            rcases fin_two_eq_zero_or_one j with rfl | rfl
          · change labelCard c 0 ≤ ((G.neighborFinset w) ∩ A).card
            rw [hPc0, ← degreeInto_eq_card_neighbor_inter]
            exact hAA w (by simpa [P] using hw)
          · change labelCard c 1 ≤ ((G.neighborFinset w) ∩ B).card
            rw [hPc1, ← degreeInto_eq_card_neighbor_inter]
            exact hcardSides.le.trans (hAB w (by simpa [P] using hw))
          · change labelCard c 0 ≤ ((G.neighborFinset w) ∩ A).card
            rw [hPc0, ← degreeInto_eq_card_neighbor_inter]
            exact hBA w (by simpa [P] using hw)
          · simp at hij
        obtain ⟨f, hf⟩ := tree_embedding_respecting_semibipartition
          T G hT c P hPdisj hcompat hcap hdeg
        refine ⟨f, ?_⟩
        intro x hx
        have hcx : c x = 0 := by simp [c, partitionLabel, hx]
        simpa [hcx, hP0] using hf x

/-- Zhao's Fact 7.2(2), in a finite exact form.  `U₁` is the possibly
non-independent side and is embedded first into `A`; the independent side's
leaves are delayed and then added using the full degree condition on `A`. -/
theorem fact72_part2
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree)
    (U₁ U₂ : Finset V) (hdisjU : Disjoint U₁ U₂)
    (hcoverU : U₁ ∪ U₂ = Finset.univ) (hU₁ : U₁.Nonempty)
    (hindep : T.IsIndepSet (U₂ : Set V))
    (A B : Finset W) (hdisjAB : Disjoint A B) (hA : A.Nonempty)
    (hAA : ∀ a ∈ A, U₁.card ≤ Erdos547EC2.degreeInto G a A)
    (hAB : ∀ a ∈ A, U₁.card ≤ Erdos547EC2.degreeInto G a B)
    (hBA : ∀ b ∈ B, U₁.card ≤ Erdos547EC2.degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a) :
    T ⊑ G := by
  obtain ⟨f, -⟩ := fact72_part2_aux T G hT U₁ U₂ hdisjU hcoverU hU₁ hindep
    A B hdisjAB hA hAA hAB hBA hdegreeA (Fintype.card V - 1) (by
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hT.connected.nonempty
      omega)
  exact ⟨f⟩

/-- The exact consequence of Fact 7.2(2) used at the start of Claim 7.12:
if `T` is omitted, then it has no partition with an independent second side
whose first side fits below the common three-way minimum-degree threshold. -/
theorem omitted_tree_has_no_small_independent_complement
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (A B : Finset W) (hdisjAB : Disjoint A B) (hA : A.Nonempty)
    (q : ℕ)
    (hAA : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a A)
    (hAB : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a B)
    (hBA : ∀ b ∈ B, q ≤ Erdos547EC2.degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a) :
    ¬ ∃ U₁ U₂ : Finset V,
      Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ ∧ U₁.Nonempty ∧
      T.IsIndepSet (U₂ : Set V) ∧ U₁.card ≤ q := by
  rintro ⟨U₁, U₂, hdisjU, hcoverU, hU₁, hindep, hsmall⟩
  apply homit
  apply fact72_part2 T G hT U₁ U₂ hdisjU hcoverU hU₁ hindep A B hdisjAB hA
  · intro a ha
    exact hsmall.trans (hAA a ha)
  · intro a ha
    exact hsmall.trans (hAB a ha)
  · intro b hb
    exact hsmall.trans (hBA b hb)
  · exact hdegreeA

/-- Integer form of the final estimate in Claim 7.12.  Here `m` is the order
of the selected natural subtree, `x₁+y₁` is the order of the complementary
nonisolated forest, `y₂` is the smaller bipartition class of the selected
subtree with its root removed, and `q` is the forbidden small-side threshold.
The source's constant hierarchy is used only through
`2*n + 1 ≤ m + 4*q`. -/
theorem claim712_final_partition_estimate
    {n m x₁ y₁ y₂ q : ℕ}
    (hforest : x₁ + y₁ ≤ n + 1 - m)
    (hlargeClass : q < x₁)
    (hsmallClass : 2 * y₂ ≤ m - 1)
    (hconstants : 2 * n + 1 ≤ m + 4 * q) :
    y₁ + y₂ + 1 ≤ q := by
  omega

/-- The large-class contradiction at the end of Zhao's Claim 7.12, stated
with the actual vertex sets.  `X₁,Y₁` are the two classes of the
nonisolated complementary forest, while `X₂,Y₂` are the two classes of
the selected natural subtree after deleting its attachment root `r`.

If `X₁` were larger than the common reservoir threshold, the numerical
estimate would make `Y₁ ∪ Y₂ ∪ {r}` small.  Its complement
`X₁ ∪ X₂` is independent (the natural-subtree boundary is precisely
what permits the two bipartitions to be oriented independently).  Fact
7.2(2) would then embed the allegedly omitted tree. -/
theorem omitted_tree_forces_complement_large_class_le
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (A B : Finset W) (hdisjAB : Disjoint A B) (hA : A.Nonempty)
    (q n m : ℕ)
    (hAA : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a A)
    (hAB : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a B)
    (hBA : ∀ b ∈ B, q ≤ Erdos547EC2.degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a)
    (X₁ Y₁ X₂ Y₂ L₀ : Finset V) (r : V)
    (hforest : X₁.card + Y₁.card ≤ n + 1 - m)
    (hsmallClass : 2 * Y₂.card ≤ m - 1)
    (hconstants : 2 * n + 1 ≤ m + 4 * q)
    (hdisjU : Disjoint (Y₁ ∪ Y₂ ∪ {r}) ((X₁ ∪ X₂) ∪ L₀))
    (hcoverU : (Y₁ ∪ Y₂ ∪ {r}) ∪ ((X₁ ∪ X₂) ∪ L₀) = Finset.univ)
    (hU₁card : (Y₁ ∪ Y₂ ∪ {r}).card = Y₁.card + Y₂.card + 1)
    (hindep : T.IsIndepSet (↑((X₁ ∪ X₂) ∪ L₀) : Set V)) :
    X₁.card ≤ q := by
  by_contra hnot
  have hlarge : q < X₁.card := by omega
  have hsmall : Y₁.card + Y₂.card + 1 ≤ q :=
    claim712_final_partition_estimate hforest hlarge hsmallClass hconstants
  apply omitted_tree_has_no_small_independent_complement T G hT homit
    A B hdisjAB hA q hAA hAB hBA hdegreeA
  refine ⟨Y₁ ∪ Y₂ ∪ {r}, (X₁ ∪ X₂) ∪ L₀,
    hdisjU, hcoverU, ?_, hindep, ?_⟩
  · exact ⟨r, by simp⟩
  · rw [hU₁card]
    exact hsmall

/-- The first pruning step in Claim 7.12.  From a sparse balanced cut, all
but at most `b` large vertices on one side have cross-degree at most `s`, and
hence internal degree at least `n-s`.  The multiplicative hypothesis is the
exact integer form of the source's Markov estimate. -/
theorem exists_low_cross_large_side
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {Vᵢ Vⱼ L : Finset W} {n s b : ℕ}
    (hdisj : Disjoint Vᵢ Vⱼ) (hcover : Vᵢ ∪ Vⱼ = Finset.univ)
    (hlarge : ∀ v ∈ L, n ≤ Erdos547EC2.degreeInto G v Finset.univ)
    (hcross : (G.interedges Vᵢ Vⱼ).card < (b + 1) * (s + 1)) :
    ∃ A : Finset W,
      A ⊆ Vᵢ ∩ L ∧ (Vᵢ ∩ L).card ≤ A.card + b ∧
        (∀ v ∈ A, Erdos547EC2.degreeInto G v Vⱼ ≤ s) ∧
        ∀ v ∈ A, n - s ≤ Erdos547EC2.degreeInto G v Vᵢ := by
  classical
  let C : Finset W := Vᵢ ∩ L
  let A : Finset W := C.filter fun v => Erdos547EC2.degreeInto G v Vⱼ ≤ s
  let Bad : Finset W := C.filter fun v => ¬Erdos547EC2.degreeInto G v Vⱼ ≤ s
  have hBadSub : Bad ⊆ Vᵢ := by
    intro v hv
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).1
  have hBadDeg : ∀ v ∈ Bad, s + 1 ≤ Erdos547EC2.degreeInto G v Vⱼ := by
    intro v hv
    have := (Finset.mem_filter.mp hv).2
    omega

  have hBadMul : Bad.card * (s + 1) ≤ (G.interedges Vᵢ Vⱼ).card :=
    Erdos547EC2.card_mul_le_card_interedges_of_subset_of_degreeInto
      G hBadSub hBadDeg
  have hBadCard : Bad.card ≤ b := by
    have hmul := hBadMul.trans_lt hcross
    have := Nat.lt_of_mul_lt_mul_right hmul
    omega
  have hsplit : A.card + Bad.card = C.card := by
    dsimp only [A, Bad]
    simpa only [not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := C) (p := fun v => Erdos547EC2.degreeInto G v Vⱼ ≤ s))
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · exact (Finset.filter_subset _ _).trans (by rfl)
  · change C.card ≤ A.card + b
    omega
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv
    have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
    have hvL : v ∈ L := (Finset.mem_inter.mp hvC).2
    have hvCross : Erdos547EC2.degreeInto G v Vⱼ ≤ s :=
      (Finset.mem_filter.mp hv).2
    have hsum := Erdos547EC2.degreeInto_partition G v hdisj hcover
    have htot := hlarge v hvL
    omega

/-- The root-placement step for the complementary forest in Claim 7.12.
If the number of nontrivial components is at most the number of available
neighbours of `v₀` in `A ∪ B`, their roots can be mapped injectively to
those neighbours.  The two membership alternatives record the orientation
of each component's bipartition used by the subsequent forest embedding. -/
theorem exists_injective_root_placement
    {R : Type*} [Fintype R]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (v₀ : W) (A B : Finset W)
    (hcard : Fintype.card R ≤ Erdos547EC2.degreeInto G v₀ (A ∪ B)) :
    ∃ f : R ↪ W,
      (∀ r, G.Adj v₀ (f r)) ∧
      (∀ r, f r ∈ A ∨ f r ∈ B) := by
  classical
  let N : Finset W := (G.neighborFinset v₀) ∩ (A ∪ B)
  have hNcard : Fintype.card R ≤ N.card := by
    rw [degreeInto_eq_card_neighbor_inter] at hcard
    exact hcard
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hNcard
  refine ⟨f, ?_, ?_⟩
  · intro r
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hf ⟨r, rfl⟩)).1
  · intro r
    exact Finset.mem_union.mp (Finset.mem_inter.mp (hf ⟨r, rfl⟩)).2

/-! ### Source-faithful structural assembly for Claim 7.12 -/

/-- A rooted forest whose cone is a tree has the parent-rank certificate
needed by the simultaneous prescribed-root greedy embedding. -/
theorem hasRootedLeafPeeling_of_rootedForestCone_isTree
    {A : Type*} [Fintype A] [DecidableEq A]
    (F : SimpleGraph A) (R : Finset A)
    (hK : (Erdos547b.ZhaoLemma59.rootedForestCone F R).IsTree) :
    Erdos547b.RootFixedPeeling.HasRootedLeafPeeling F R := by
  classical
  let K := Erdos547b.ZhaoLemma59.rootedForestCone F R
  have hKT : K.IsTree := hK
  let rank : A → ℕ := fun v => K.dist none (some v) - 1
  refine ⟨rank, ?_, ?_, ?_⟩
  · intro v hv
    have hadj : K.Adj none (some v) := by
      simpa [K, Erdos547b.ZhaoLemma59.rootedForestCone] using hv
    have hd : K.dist none (some v) = 1 := K.dist_eq_one_iff_adj.mpr hadj
    simp [rank, hd]
  · intro v hv
    have hvne : (some v : Option A) ≠ none := by simp
    let po := Erdos547b.TreePartition.parent hKT none hvne
    have hpAdj : K.Adj po (some v) :=
      Erdos547b.TreePartition.parent_adj hKT none hvne
    have hpDist : K.dist none po + 1 = K.dist none (some v) :=
      Erdos547b.TreePartition.parent_dist_add_one hKT none hvne
    have hpSome : ∃ p, po = some p := by
      cases hpo : po with
      | none =>
          exfalso
          have : v ∈ R := by
            simpa [K, Erdos547b.ZhaoLemma59.rootedForestCone, hpo] using hpAdj
          exact hv this
      | some p => exact ⟨p, rfl⟩
    obtain ⟨p, hp⟩ := hpSome
    have hvDistPos : 0 < K.dist none (some v) := by
      have hne : (none : Option A) ≠ some v := by simp
      exact Nat.pos_of_ne_zero (fun hz => hne (hKT.connected.dist_eq_zero_iff.mp hz))
    have hpDistPos : 0 < K.dist none (some p) := by
      have hne : (none : Option A) ≠ some p := by simp
      exact Nat.pos_of_ne_zero (fun hz => hne (hKT.connected.dist_eq_zero_iff.mp hz))
    refine ⟨p, ?_, ?_, ?_⟩
    · simpa [K, Erdos547b.ZhaoLemma59.rootedForestCone, hp] using hpAdj.symm
    · simp only [rank]
      rw [hp] at hpDist
      omega
    · intro y hvy hyrank
      have hKy : K.Adj (some v) (some y) := by
        simpa [K, Erdos547b.ZhaoLemma59.rootedForestCone] using hvy
      have hyDistPos : 0 < K.dist none (some y) := by
        have hne : (none : Option A) ≠ some y := by simp
        exact Nat.pos_of_ne_zero (fun hz => hne (hKT.connected.dist_eq_zero_iff.mp hz))
      have hyLower : K.dist none (some y) < K.dist none (some v) := by
        change K.dist none (some y) - 1 < K.dist none (some v) - 1 at hyrank
        omega
      have hyParent : some y = Erdos547b.TreePartition.parent hKT none hvne := by
        apply Erdos547b.TreePartition.eq_parent_of_adj_of_dist_add_one
          hKT none hvne hKy.symm
        rcases hKT.dist_eq_dist_add_one_of_adj none hKy with hback | hforward
        · omega
        · omega
      rw [show Erdos547b.TreePartition.parent hKT none hvne = po by rfl, hp] at hyParent
      exact Option.some.inj hyParent
  · intro u v huv
    have hKuv : K.Adj (some u) (some v) := by
      simpa [K, Erdos547b.ZhaoLemma59.rootedForestCone] using huv
    have huPos : 0 < K.dist none (some u) := by
      exact Nat.pos_of_ne_zero (fun hz => (by
        have := hKT.connected.dist_eq_zero_iff.mp hz
        simp at this))
    have hvPos : 0 < K.dist none (some v) := by
      exact Nat.pos_of_ne_zero (fun hz => (by
        have := hKT.connected.dist_eq_zero_iff.mp hz
        simp at this))
    have hne := hKT.dist_ne_of_adj none hKuv
    change K.dist none (some u) - 1 ≠ K.dist none (some v) - 1
    omega

/-- The ambient vertices in one colour class of a colouring of an induced
subgraph.  This lets the Fact 7.2 contradiction be stated in the original
tree's vertex type. -/
noncomputable def inducedPartVertices
    (C : Finset V) {T : SimpleGraph V}
    (c : (T.induce (C : Set V)).Coloring (Fin 2)) (i : Fin 2) : Finset V := by
  classical
  exact (Finset.univ.filter fun v => c v = i).image Subtype.val

theorem card_inducedPartVertices
    (C : Finset V) {T : SimpleGraph V}
    (c : (T.induce (C : Set V)).Coloring (Fin 2)) (i : Fin 2) :
    (inducedPartVertices C c i).card = Erdos547b.Coloring.partCard c i := by
  classical
  rw [inducedPartVertices, Finset.card_image_of_injective _ Subtype.val_injective]
  rfl

@[simp] theorem mem_inducedPartVertices
    {C : Finset V} {T : SimpleGraph V}
    {c : (T.induce (C : Set V)).Coloring (Fin 2)} {i : Fin 2} {v : V} :
    v ∈ inducedPartVertices C c i ↔ ∃ hv : v ∈ C, c ⟨v, hv⟩ = i := by
  classical
  constructor
  · intro hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨z.property, (Finset.mem_filter.mp hz).2⟩
  · intro hv
    obtain ⟨hvC, hvi⟩ := hv
    exact Finset.mem_image.mpr ⟨⟨v, hvC⟩, by simp [hvi], rfl⟩

theorem inducedPartVertices_union
    (C : Finset V) {T : SimpleGraph V}
    (c : (T.induce (C : Set V)).Coloring (Fin 2)) :
    inducedPartVertices C c 0 ∪ inducedPartVertices C c 1 = C := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (mem_inducedPartVertices.mp hv).choose
    · exact (mem_inducedPartVertices.mp hv).choose
  · intro hv
    rcases fin_two_eq_zero_or_one (c ⟨v, hv⟩) with h | h
    · exact Finset.mem_union_left _ (mem_inducedPartVertices.mpr ⟨hv, h⟩)
    · exact Finset.mem_union_right _ (mem_inducedPartVertices.mpr ⟨hv, h⟩)

theorem disjoint_inducedPartVertices
    (C : Finset V) {T : SimpleGraph V}
    (c : (T.induce (C : Set V)).Coloring (Fin 2)) :
    Disjoint (inducedPartVertices C c 0) (inducedPartVertices C c 1) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  obtain ⟨hvC0, h0⟩ := mem_inducedPartVertices.mp hv0
  obtain ⟨hvC1, h1⟩ := mem_inducedPartVertices.mp hv1
  have : (⟨v, hvC0⟩ : {z // z ∈ C}) = ⟨v, hvC1⟩ := Subtype.ext rfl
  rw [this] at h0
  omega

theorem inducedPartVertices_isIndep
    (C : Finset V) {T : SimpleGraph V}
    (c : (T.induce (C : Set V)).Coloring (Fin 2)) (i : Fin 2) :
    T.IsIndepSet (inducedPartVertices C c i : Set V) := by
  classical
  rw [T.isIndepSet_iff]
  intro u hu v hv huv hadj
  obtain ⟨huC, huc⟩ := mem_inducedPartVertices.mp hu
  obtain ⟨hvC, hvc⟩ := mem_inducedPartVertices.mp hv
  have hadj' : (T.induce (C : Set V)).Adj ⟨u, huC⟩ ⟨v, hvC⟩ := hadj
  have hne := c.valid hadj'
  exact hne (huc.trans hvc.symm)

/-- The independent side in the final Fact 7.2 application consists of one
colour class of the complementary core, one parity class of the selected
subtree with its root deleted, and the deleted root-leaves. -/
theorem independent_core_selected_leaves
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V} {S : Finset V}
    (hS : SimpleGraphRose547.IsNaturalVertexSetAt T r x S)
    (P Z : Finset V)
    (hP : P ⊆ SimpleGraphRose547.complementNonisolated T x S)
    (hZ : Z ⊆ S.erase x)
    (hPind : T.IsIndepSet (P : Set V))
    (hZind : T.IsIndepSet (Z : Set V)) :
    T.IsIndepSet
      (↑((P ∪ Z) ∪ SimpleGraphRose547.complementRootLeaves T x S) : Set V) := by
  classical
  let L := SimpleGraphRose547.complementRootLeaves T x S
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [SimpleGraphRose547.naturalVertices]
  rw [T.isIndepSet_iff]
  intro u hu v hv huv hadj
  change u ∈ (P ∪ Z) ∪ L at hu
  change v ∈ (P ∪ Z) ∪ L at hv
  rcases Finset.mem_union.mp hu with huPZ | huL
  · rcases Finset.mem_union.mp huPZ with huP | huZ
    · rcases Finset.mem_union.mp hv with hvPZ | hvL
      · rcases Finset.mem_union.mp hvPZ with hvP | hvZ
        · exact hPind huP hvP huv hadj
        · have hvS : v ∈ S := (Finset.mem_erase.mp (hZ hvZ)).2
          have huOut : u ∉ S :=
            (SimpleGraphRose547.mem_complementNonisolated.mp (hP huP)).1
          have hvx := hS.singleBoundary hT hvS huOut hadj.symm
          exact (Finset.mem_erase.mp (hZ hvZ)).1 hvx
      · have hvx := (SimpleGraphRose547.mem_complementRootLeaves.mp hvL).2 hadj.symm
        have huOut : u ∉ S :=
          (SimpleGraphRose547.mem_complementNonisolated.mp (hP huP)).1
        exact huOut (hvx ▸ hxS)
    · rcases Finset.mem_union.mp hv with hvPZ | hvL
      · rcases Finset.mem_union.mp hvPZ with hvP | hvZ
        · have huS : u ∈ S := (Finset.mem_erase.mp (hZ huZ)).2
          have hvOut : v ∉ S :=
            (SimpleGraphRose547.mem_complementNonisolated.mp (hP hvP)).1
          have hux := hS.singleBoundary hT huS hvOut hadj
          exact (Finset.mem_erase.mp (hZ huZ)).1 hux
        · exact hZind huZ hvZ huv hadj
      · have hvx := (SimpleGraphRose547.mem_complementRootLeaves.mp hvL).2 hadj.symm
        exact (Finset.mem_erase.mp (hZ huZ)).1 hvx
  · have hux := (SimpleGraphRose547.mem_complementRootLeaves.mp huL).2 hadj
    rcases Finset.mem_union.mp hv with hvPZ | hvL
    · rcases Finset.mem_union.mp hvPZ with hvP | hvZ
      · have hvOut : v ∉ S :=
          (SimpleGraphRose547.mem_complementNonisolated.mp (hP hvP)).1
        exact hvOut (hux ▸ hxS)
      · exact (Finset.mem_erase.mp (hZ hvZ)).1 hux
    · have hvOut := (SimpleGraphRose547.mem_complementRootLeaves.mp hvL).1
      exact hvOut (hux ▸ hxS)

/-- Both independently oriented colour classes of the complementary forest
have size at most `q`; otherwise the smaller complementary class, the
smaller selected-subtree class, and the attachment root form the small side
of Fact 7.2(2). -/
theorem omitted_tree_forces_both_core_parts_le
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (A B : Finset W) (hdisjAB : Disjoint A B) (hA : A.Nonempty)
    (q n m : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (hAA : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a A)
    (hAB : ∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a B)
    (hBA : ∀ b ∈ B, q ≤ Erdos547EC2.degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a)
    (r x : V) (S : Finset V)
    (hS : SimpleGraphRose547.IsNaturalVertexSetAt T r x S)
    (hScard : S.card = m)
    (c : (T.induce
      (SimpleGraphRose547.complementNonisolated T x S : Set V)).Coloring (Fin 2))
    (hconstants : 2 * n + 1 ≤ m + 4 * q) :
    Erdos547b.Coloring.partCard c 0 ≤ q ∧
      Erdos547b.Coloring.partCard c 1 ≤ q := by
  classical
  let C₁ := SimpleGraphRose547.complementNonisolated T x S
  let L := SimpleGraphRose547.complementRootLeaves T x S
  let P₀ := inducedPartVertices C₁ c 0
  let P₁ := inducedPartVertices C₁ c 1
  let Z₀ := SimpleGraphRose547.parityPart T x (S.erase x) 0
  let Z₁ := SimpleGraphRose547.parityPart T x (S.erase x) 1
  let Y₂ := if Z₀.card ≤ Z₁.card then Z₀ else Z₁
  let X₂ := if Z₀.card ≤ Z₁.card then Z₁ else Z₀
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [SimpleGraphRose547.naturalVertices]
  obtain ⟨hC₁S, hC₁L, hSL, hcover, hleaf, hboundary⟩ := hS.complement_split hT
  change Disjoint C₁ S at hC₁S
  change Disjoint C₁ L at hC₁L
  change Disjoint S L at hSL
  change (C₁ ∪ S) ∪ L = Finset.univ at hcover
  have hPunion : P₀ ∪ P₁ = C₁ := by
    exact inducedPartVertices_union C₁ c
  have hPdisj : Disjoint P₀ P₁ := disjoint_inducedPartVertices C₁ c
  have hPsum : P₀.card + P₁.card = C₁.card := by
    rw [← Finset.card_union_of_disjoint hPdisj, hPunion]
  have hZunion : X₂ ∪ Y₂ = S.erase x := by
    dsimp only [X₂, Y₂]
    by_cases h : Z₀.card ≤ Z₁.card
    · simpa [h, Finset.union_comm] using
        SimpleGraphRose547.parityPart_zero_union_one T x (S.erase x)
    · simpa [h] using
        SimpleGraphRose547.parityPart_zero_union_one T x (S.erase x)
  have hZdisj : Disjoint X₂ Y₂ := by
    dsimp only [X₂, Y₂]
    by_cases h : Z₀.card ≤ Z₁.card
    · simpa [h] using
        (SimpleGraphRose547.disjoint_parityPart_zero_one T x (S.erase x)).symm
    · simpa [h] using
        SimpleGraphRose547.disjoint_parityPart_zero_one T x (S.erase x)
  have hY₂small : 2 * Y₂.card ≤ m - 1 := by
    have herase : (S.erase x).card = m - 1 := by simp [hScard, hxS]
    have hsum := SimpleGraphRose547.card_parityPart_zero_add_one
      T x (S.erase x)
    by_cases h :
        (SimpleGraphRose547.parityPart T x (S.erase x) 0).card ≤
          (SimpleGraphRose547.parityPart T x (S.erase x) 1).card
    · have hY : Y₂ = SimpleGraphRose547.parityPart T x (S.erase x) 0 := by
        simp [Y₂, Z₀, Z₁, h]
      rw [herase] at hsum
      rw [hY]
      omega
    · have hY : Y₂ = SimpleGraphRose547.parityPart T x (S.erase x) 1 := by
        simp [Y₂, Z₀, Z₁, h]
      rw [herase] at hsum
      rw [hY]
      omega
  have hX₂sub : X₂ ⊆ S.erase x := by
    intro z hz
    rw [← hZunion]
    exact Finset.mem_union_left _ hz
  have hY₂sub : Y₂ ⊆ S.erase x := by
    intro z hz
    rw [← hZunion]
    exact Finset.mem_union_right _ hz
  have hX₂ind : T.IsIndepSet (X₂ : Set V) := by
    dsimp only [X₂, Z₀, Z₁]
    by_cases h :
        (SimpleGraphRose547.parityPart T x (S.erase x) 0).card ≤
          (SimpleGraphRose547.parityPart T x (S.erase x) 1).card
    · simpa [h] using SimpleGraphRose547.isIndepSet_parityPart hT x (S.erase x) 1
    · simpa [h] using SimpleGraphRose547.isIndepSet_parityPart hT x (S.erase x) 0
  have hforest : C₁.card ≤ n + 1 - m := by
    have hCunionL : Disjoint (C₁ ∪ S) L := by
      rw [Finset.disjoint_left]
      intro z hz hzL
      rcases Finset.mem_union.mp hz with hzC | hzS
      · exact Finset.disjoint_left.mp hC₁L hzC hzL
      · exact Finset.disjoint_left.mp hSL hzS hzL
    have hcardCover := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hCunionL,
      Finset.card_union_of_disjoint hC₁S, Finset.card_univ, hcardT, hScard] at hcardCover
    have hsumle : C₁.card + m ≤ n + 1 := by omega
    exact Nat.le_sub_of_add_le hsumle
  have hUdata (X₁ Y₁ : Finset V)
      (hX₁sub : X₁ ⊆ C₁) (hY₁sub : Y₁ ⊆ C₁)
      (hXY₁ : Disjoint X₁ Y₁) (hXYcover : X₁ ∪ Y₁ = C₁)
      (hX₁ind : T.IsIndepSet (X₁ : Set V)) :
      Disjoint (Y₁ ∪ Y₂ ∪ {x}) ((X₁ ∪ X₂) ∪ L) ∧
      (Y₁ ∪ Y₂ ∪ {x}) ∪ ((X₁ ∪ X₂) ∪ L) = Finset.univ ∧
      (Y₁ ∪ Y₂ ∪ {x}).card = Y₁.card + Y₂.card + 1 ∧
      T.IsIndepSet (↑((X₁ ∪ X₂) ∪ L) : Set V) := by
    have hY₁Y₂ : Disjoint Y₁ Y₂ :=
      hC₁S.mono hY₁sub (hY₂sub.trans (Finset.erase_subset _ _))
    have hY₁x : x ∉ Y₁ := fun hx =>
      Finset.disjoint_left.mp hC₁S (hY₁sub hx) hxS
    have hY₂x : x ∉ Y₂ := fun hx => (Finset.mem_erase.mp (hY₂sub hx)).1 rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hzU₁ hzU₂
      simp only [Finset.mem_union, Finset.mem_singleton] at hzU₁ hzU₂
      rcases hzU₁ with ((hzY₁ | hzY₂) | rfl) <;>
        rcases hzU₂ with ((hzX₁ | hzX₂) | hzL)
      · exact Finset.disjoint_left.mp hXY₁ hzX₁ hzY₁
      · exact Finset.disjoint_left.mp hC₁S (hY₁sub hzY₁)
          ((Finset.mem_erase.mp (hX₂sub hzX₂)).2)
      · exact Finset.disjoint_left.mp hC₁L (hY₁sub hzY₁) hzL
      · exact Finset.disjoint_left.mp hC₁S (hX₁sub hzX₁)
          ((Finset.mem_erase.mp (hY₂sub hzY₂)).2)
      · exact Finset.disjoint_left.mp hZdisj hzX₂ hzY₂
      · exact Finset.disjoint_left.mp hSL
          ((Finset.mem_erase.mp (hY₂sub hzY₂)).2) hzL
      · exact Finset.disjoint_left.mp hC₁S (hX₁sub hzX₁) hxS
      · exact (Finset.mem_erase.mp (hX₂sub hzX₂)).1 rfl
      · exact (SimpleGraphRose547.mem_complementRootLeaves.mp hzL).1 hxS
    · ext z
      constructor
      · simp
      · intro hz
        have hzAll : z ∈ (C₁ ∪ S) ∪ L := by
          rw [hcover]
          simp
        rcases Finset.mem_union.mp hzAll with hzCS | hzL
        · rcases Finset.mem_union.mp hzCS with hzC | hzS
          · have hzParts : z ∈ X₁ ∪ Y₁ := by simpa [hXYcover] using hzC
            rcases Finset.mem_union.mp hzParts with hzX | hzY
            · simp [hzX]
            · simp [hzY]
          · by_cases hzx : z = x
            · simp [hzx]
            · have hzErase : z ∈ S.erase x := Finset.mem_erase.mpr ⟨hzx, hzS⟩
              have hzParts : z ∈ X₂ ∪ Y₂ := by simpa [hZunion] using hzErase
              rcases Finset.mem_union.mp hzParts with hzX | hzY
              · simp [hzX]
              · simp [hzY]
        · simp [hzL]
    · have hUnionSingle : Disjoint (Y₁ ∪ Y₂) {x} := by
        rw [Finset.disjoint_singleton_right]
        simp [hY₁x, hY₂x]
      rw [Finset.card_union_of_disjoint hUnionSingle,
        Finset.card_union_of_disjoint hY₁Y₂]
      simp
    · exact independent_core_selected_leaves hT hS X₁ X₂ hX₁sub hX₂sub
        hX₁ind hX₂ind
  have hP₀sub : P₀ ⊆ C₁ := by
    intro z hz
    exact (mem_inducedPartVertices.mp hz).choose
  have hP₁sub : P₁ ⊆ C₁ := by
    intro z hz
    exact (mem_inducedPartVertices.mp hz).choose
  have hP₀ind : T.IsIndepSet (P₀ : Set V) := inducedPartVertices_isIndep C₁ c 0
  have hP₁ind : T.IsIndepSet (P₁ : Set V) := inducedPartVertices_isIndep C₁ c 1
  have hfirstData := hUdata P₀ P₁ hP₀sub hP₁sub hPdisj hPunion hP₀ind
  have hsecondData := hUdata P₁ P₀ hP₁sub hP₀sub hPdisj.symm
    (by simpa [Finset.union_comm] using hPunion) hP₁ind
  constructor
  · rw [← card_inducedPartVertices C₁ c 0]
    apply omitted_tree_forces_complement_large_class_le T G hT homit A B
      hdisjAB hA q n m hAA hAB hBA hdegreeA P₀ P₁ X₂ Y₂ L x
    · omega
    · exact hY₂small
    · exact hconstants
    · exact hfirstData.1
    · exact hfirstData.2.1
    · exact hfirstData.2.2.1
    · exact hfirstData.2.2.2
  · rw [← card_inducedPartVertices C₁ c 1]
    apply omitted_tree_forces_complement_large_class_le T G hT homit A B
      hdisjAB hA q n m hAA hAB hBA hdegreeA P₁ P₀ X₂ Y₂ L x
    · omega
    · exact hY₂small
    · exact hconstants
    · exact hsecondData.1
    · exact hsecondData.2.1
    · exact hsecondData.2.2.1
    · exact hsecondData.2.2.2

/-- The complete embedding contradiction at the heart of Zhao's Claim 7.12.
The four host reservoirs already have the three degree properties delivered
by Proposition 7.3.  Fact 7.9 is invoked internally; the remaining four
numeric hypotheses are precisely the root-reservation, selected-subtree,
forest-minimum-degree, and final Fact 7.2 estimates, uniformly at the lower
endpoint returned by Fact 7.9. -/
theorem claim712_core_contradiction
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (n q k : ℕ) (hcardT : Fintype.card V = n + 1)
    (hk2 : 2 ≤ k) (hkT : k ≤ Fintype.card V)
    (A₁ B₁ A₂ B₂ : Finset W)
    (hAB₁ : Disjoint A₁ B₁) (hA₁ : A₁.Nonempty)
    (hhost12 : Disjoint (A₁ ∪ B₁) (A₂ ∪ B₂))
    (v₀ : W) (hv₀outside₁ : v₀ ∉ A₁ ∪ B₁)
    (hAA₁ : ∀ a ∈ A₁, q ≤ Erdos547EC2.degreeInto G a A₁)
    (hABdeg₁ : ∀ a ∈ A₁, q ≤ Erdos547EC2.degreeInto G a B₁)
    (hBA₁ : ∀ b ∈ B₁, q ≤ Erdos547EC2.degreeInto G b A₁)
    (hAA₂ : ∀ a ∈ A₂, q ≤ Erdos547EC2.degreeInto G a A₂)
    (hABdeg₂ : ∀ a ∈ A₂, q ≤ Erdos547EC2.degreeInto G a B₂)
    (hBA₂ : ∀ b ∈ B₂, q ≤ Erdos547EC2.degreeInto G b A₂)
    (hdegreeA₁ : ∀ a ∈ A₁, Fintype.card V - 1 ≤ G.degree a)
    (hheavy : Fintype.card V - 1 ≤ G.degree v₀)
    (hrootSupply : n + 1 ≤ (k + 1) / 2 +
      2 * Erdos547EC2.degreeInto G v₀ (A₁ ∪ B₁))
    (hselectedSupply : k ≤ Erdos547EC2.degreeInto G v₀ (A₂ ∪ B₂) + 1)
    (hselectedQ : k ≤ q + 1)
    (hconstants : 2 * n + 1 ≤ (k + 1) / 2 + 4 * q) :
    False := by
  classical
  obtain ⟨x, S, hS, hSlow, hShigh⟩ :=
    SimpleGraphRose547.exists_naturalVertexSetAt_card hT (Classical.choice hT.connected.nonempty)
      k hk2 hkT
  let C₁ := SimpleGraphRose547.complementNonisolated T x S
  let L := SimpleGraphRose547.complementRootLeaves T x S
  let R := SimpleGraphRose547.complementRoots T x S
  let F := T.induce (C₁ : Set V)
  have hxS : x ∈ S := by
    obtain ⟨kept, hkept, rfl⟩ := hS
    simp [SimpleGraphRose547.naturalVertices]
  have hScardQ : S.card ≤ q := by omega
  have hconstantS : 2 * n + 1 ≤ S.card + 4 * q := by omega
  have hcorePartsBase :
      ∀ c : F.Coloring (Fin 2),
        Erdos547b.Coloring.partCard c 0 ≤ q ∧
          Erdos547b.Coloring.partCard c 1 ≤ q := by
    intro c
    apply omitted_tree_forces_both_core_parts_le T G hT
      homit
      A₁ B₁ hAB₁ hA₁ q n S.card hcardT hAA₁ hABdeg₁ hBA₁ hdegreeA₁
      (Classical.choice hT.connected.nonempty) x S hS rfl c hconstantS
  obtain ⟨hC₁S, hC₁L, hSL, hcover, hleaf, hboundary⟩ := hS.complement_split hT
  change Disjoint C₁ S at hC₁S
  change Disjoint C₁ L at hC₁L
  change Disjoint S L at hSL
  change (C₁ ∪ S) ∪ L = Finset.univ at hcover
  have hCcard : C₁.card ≤ n + 1 - S.card := by
    have hCunionL : Disjoint (C₁ ∪ S) L := by
      rw [Finset.disjoint_left]
      intro z hz hzL
      rcases Finset.mem_union.mp hz with hzC | hzS
      · exact Finset.disjoint_left.mp hC₁L hzC hzL
      · exact Finset.disjoint_left.mp hSL hzS hzL
    have hc := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hCunionL,
      Finset.card_union_of_disjoint hC₁S, Finset.card_univ, hcardT] at hc
    exact Nat.le_sub_of_add_le (by omega)
  have hRtwo : 2 * R.card ≤ C₁.card := by
    simpa [R, C₁] using hS.two_mul_card_complementRoots_le hT
  have hRcard : Fintype.card {a // a ∈ R} ≤
      Erdos547EC2.degreeInto G v₀ (A₁ ∪ B₁) := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨rootImage, hrootImageAdj, hrootImageUnion⟩ :=
    exists_injective_root_placement G v₀ A₁ B₁ hRcard
  have hKtree :
      (Erdos547b.ZhaoLemma59.rootedForestCone F R).IsTree := by
    simpa [F, R, C₁] using hS.rootedForestCone_complement_isTree hT
  have hpeel : Erdos547b.RootFixedPeeling.HasRootedLeafPeeling F R :=
    hasRootedLeafPeeling_of_rootedForestCone_isTree F R hKtree
  have hrootIndependent : F.IsIndepSet (R : Set {z // z ∈ C₁}) := by
    rw [F.isIndepSet_iff]
    intro u hu v hv huv hadj
    have hux : T.Adj u x := by
      change u ∈ R at hu
      simpa [R] using (SimpleGraphRose547.mem_complementRoots.mp hu)
    have hvx : T.Adj v x := by
      change v ∈ R at hv
      simpa [R] using (SimpleGraphRose547.mem_complementRoots.mp hv)
    have hdu : T.dist x u = 1 := T.dist_eq_one_iff_adj.mpr hux.symm
    have hdv : T.dist x v = 1 := T.dist_eq_one_iff_adj.mpr hvx.symm
    exact hT.dist_ne_of_adj x hadj (hdu.trans hdv.symm)
  let baseColor : F.Coloring (Fin 2) :=
    Classical.choice (hT.isAcyclic.induce (C₁ : Set V)).isBipartite
  let componentRoot : {z // z ∈ C₁} → {a // a ∈ R} := fun z =>
    hS.componentRoot hT z
  let rootVertex : {a // a ∈ R} → {z // z ∈ C₁} := fun a => a
  have hadjComponent : ∀ ⦃u v : {z // z ∈ C₁}⦄,
      F.Adj u v → componentRoot u = componentRoot v := by
    intro u v huv
    exact hS.componentRoot_eq_of_adj hT huv
  have hcomponentRoot : ∀ a : {a // a ∈ R},
      componentRoot (rootVertex a) = a := by
    intro a
    exact hS.componentRoot_eq_self_of_mem hT a a.property
  let side₁ : F.Coloring (Fin 2) :=
    Erdos547b.ZhaoClaim712.orientComponents baseColor componentRoot rootVertex
      (Erdos547b.ZhaoClaim712.rootImageSide A₁ rootImage) hadjComponent
  have hsideRoot : ∀ a : {a // a ∈ R},
      side₁ (rootVertex a) =
        Erdos547b.ZhaoClaim712.rootImageSide A₁ rootImage a := by
    intro a
    exact Erdos547b.ZhaoClaim712.orientComponents_root baseColor componentRoot
      rootVertex (Erdos547b.ZhaoClaim712.rootImageSide A₁ rootImage)
      hadjComponent hcomponentRoot a
  have hrootImageMem : ∀ a : {a // a ∈ R},
      rootImage a ∈ Erdos547b.ZhaoClaim712.twoParts A₁ B₁ (side₁ (rootVertex a)) := by
    intro a
    rw [hsideRoot]
    exact Erdos547b.ZhaoClaim712.rootImage_mem_selected_side
      A₁ B₁ rootImage (fun r => Finset.mem_union.mpr (hrootImageUnion r)) a
  have hparts : Erdos547b.Coloring.partCard side₁ 0 ≤ q ∧
      Erdos547b.Coloring.partCard side₁ 1 ≤ q := hcorePartsBase side₁
  obtain ⟨a₁, ha₁⟩ := hA₁
  have hqA₁ : q ≤ A₁.card :=
    (hAA₁ a₁ ha₁).trans (Erdos547EC2.degreeInto_le_card G a₁ A₁)
  have hqB₁ : q ≤ B₁.card :=
    (hABdeg₁ a₁ ha₁).trans (Erdos547EC2.degreeInto_le_card G a₁ B₁)
  have hcap₁ : ∀ i, Erdos547b.Coloring.partCard side₁ i ≤
      (Erdos547b.ZhaoClaim712.twoParts A₁ B₁ i).card := by
    intro i
    rcases fin_two_eq_zero_or_one i with rfl | rfl
    · simpa using hparts.1.trans hqA₁
    · simpa using hparts.2.trans hqB₁
  have hdegree₁ : ∀ i j, i ≠ j →
      ∀ v ∈ Erdos547b.ZhaoClaim712.twoParts A₁ B₁ i,
        Erdos547b.Coloring.partCard side₁ j ≤
          ((G.neighborFinset v) ∩
            Erdos547b.ZhaoClaim712.twoParts A₁ B₁ j).card := by
    intro i j hij v hv
    rcases fin_two_eq_zero_or_one i with rfl | rfl <;>
      rcases fin_two_eq_zero_or_one j with rfl | rfl
    · exact (hij rfl).elim
    · have hd := hABdeg₁ v (by simpa using hv)
      rw [degreeInto_eq_card_neighbor_inter] at hd
      exact hparts.2.trans hd
    · have hd := hBA₁ v (by simpa using hv)
      rw [degreeInto_eq_card_neighbor_inter] at hd
      exact hparts.1.trans hd
    · exact (hij rfl).elim
  have hrootDegree₂ : Fintype.card {z // z ∈ S} ≤
      ((G.neighborFinset v₀) ∩ (A₂ ∪ B₂)).card := by
    rw [Fintype.card_coe, ← degreeInto_eq_card_neighbor_inter]
    omega
  have hdegMono (v : W) {D H : Finset W} (hDH : D ⊆ H) :
      Erdos547EC2.degreeInto G v D ≤ Erdos547EC2.degreeInto G v H := by
    rw [degreeInto_eq_card_neighbor_inter, degreeInto_eq_card_neighbor_inter]
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,
      hDH (Finset.mem_inter.mp hz).2⟩
  have hminDegree₂ : ∀ v ∈ A₂ ∪ B₂,
      Fintype.card {z // z ∈ S} ≤
        ((G.neighborFinset v) ∩ (A₂ ∪ B₂)).card := by
    intro v hv
    rw [Fintype.card_coe, ← degreeInto_eq_card_neighbor_inter]
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact hScardQ.trans ((hABdeg₂ v hvA).trans
        (hdegMono v (Finset.subset_union_right)))
    · exact hScardQ.trans ((hBA₂ v hvB).trans
        (hdegMono v (Finset.subset_union_left)))
  have hboundaryRoots : ∀ u : {z // z ∈ C₁}, T.Adj u x → u ∈ R := by
    intro u hux
    change u ∈ SimpleGraphRose547.complementRoots T x S
    exact SimpleGraphRose547.mem_complementRoots.mpr hux
  have hTreeS : (T.induce (S : Set V)).IsTree := hS.isTree hT
  have hcopy := Erdos547b.ZhaoClaim712.exists_claim712_full_copy_sharp
    T G x C₁ S L hC₁S hC₁L hSL hcover hxS hleaf hboundary R
    hrootIndependent hpeel hboundaryRoots side₁ hTreeS A₁ B₁ A₂ B₂
    hAB₁ hhost12 v₀ hv₀outside₁ rootImage rootImage.injective hrootImageAdj
    hrootImageMem hcap₁ hdegree₁ hrootDegree₂ hminDegree₂ hheavy
  exact homit hcopy

/-- Proposition 7.3 reservoir with the quantitative exceptional-set bound
retained after deleting the possible heavy vertex. -/
theorem exists_claim712_reservoir_side_avoiding_strong
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (Vᵢ A : Finset W) (v₀ : W) (n t s q : ℕ)
    (hVcard : Vᵢ.card = n) (hA : A ⊆ Vᵢ)
    (hinternal : ∀ a ∈ A, n - t ≤ Erdos547EC2.degreeInto G a Vᵢ)
    (hAcardAA : q + 1 + t ≤ A.card)
    (hAcardBA : q + 1 + s ≤ A.card)
    (hBcardAB : q + 1 + t + s ≤ (Vᵢ \ A).card)
    (hscale : t * n ≤ s * (s + 1)) :
    ∃ B : Finset W,
      B ⊆ Vᵢ \ A ∧ v₀ ∉ B ∧ Disjoint A B ∧
      (∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a A) ∧
      (∀ a ∈ A, q ≤ Erdos547EC2.degreeInto G a B) ∧
      (∀ b ∈ B, q ≤ Erdos547EC2.degreeInto G b A) ∧
      (Vᵢ \ (A ∪ B)).card ≤ s + 1 := by
  classical
  let C := Vᵢ \ A
  have hAC : Disjoint A C := Finset.disjoint_sdiff
  have hcoverAC : A ∪ C = Vᵢ := Finset.union_sdiff_of_subset hA
  have hsplit (v : W) :
      Erdos547EC2.degreeInto G v A + Erdos547EC2.degreeInto G v C =
        Erdos547EC2.degreeInto G v Vᵢ := by
    rw [Erdos547EC2.degreeInto_union_of_disjoint G v hAC, hcoverAC]
  have hAAraw : ∀ a ∈ A,
      A.card - t ≤ Erdos547EC2.degreeInto G a A := by
    intro a ha
    have hd := hinternal a ha
    have hle := Erdos547EC2.degreeInto_le_card G a C
    have hs := hsplit a
    have hc : A.card + C.card = n := by
      rw [← Finset.card_union_of_disjoint hAC, hcoverAC, hVcard]
    omega
  have hACraw : ∀ a ∈ A,
      C.card - t ≤ Erdos547EC2.degreeInto G a C := by
    intro a ha
    have hd := hinternal a ha
    have hle := Erdos547EC2.degreeInto_le_card G a A
    have hs := hsplit a
    have hc : A.card + C.card = n := by
      rw [← Finset.card_union_of_disjoint hAC, hcoverAC, hVcard]
    omega
  have hAcardN : A.card ≤ n := by
    rw [← hVcard]
    exact Finset.card_le_card hA
  obtain ⟨B₀, hB₀C, hmul, hremoved, hBcard, hABraw, hBAraw⟩ :=
    Erdos547EC2.zhao_proposition_7_3_discrete74
      G hAC hACraw hAcardN hscale
  let B := B₀ \ {v₀}
  have hBB₀ : B ⊆ B₀ := Finset.sdiff_subset
  have hBC : B ⊆ C := hBB₀.trans hB₀C
  have hAB : Disjoint A B := hAC.mono_right hBC
  have hremoveOne : (B₀ \ B).card ≤ 1 := by
    apply Finset.card_le_card (s := B₀ \ B) (t := {v₀})
    intro z hz
    have hzB₀ := (Finset.mem_sdiff.mp hz).1
    have hzNotB := (Finset.mem_sdiff.mp hz).2
    simp only [B, Finset.mem_sdiff, Finset.mem_singleton] at hzNotB ⊢
    by_contra hzv
    exact hzNotB ⟨hzB₀, hzv⟩
  have hCminusB : (C \ B).card ≤ s + 1 := by
    have hsubset : C \ B ⊆ (C \ B₀) ∪ (B₀ \ B) := by
      intro z hz
      obtain ⟨hzC, hzB⟩ := Finset.mem_sdiff.mp hz
      by_cases hzB₀ : z ∈ B₀
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzB₀, hzB⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzC, hzB₀⟩)
    have hCB₀ : (C \ B₀).card ≤ s := by
      have hB₀sub : B₀ ⊆ C := hB₀C
      rw [Finset.card_sdiff_of_subset hB₀sub]
      omega
    calc
      (C \ B).card ≤ ((C \ B₀) ∪ (B₀ \ B)).card :=
        Finset.card_le_card hsubset
      _ ≤ (C \ B₀).card + (B₀ \ B).card := Finset.card_union_le _ _
      _ ≤ s + 1 := Nat.add_le_add hCB₀ hremoveOne
  refine ⟨B, hBC, by simp [B], hAB, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (by omega : q ≤ A.card - t).trans (hAAraw a ha)
  · intro a ha
    have hbig : q + 1 + t ≤ B₀.card := by
      have : q + 1 + t + s ≤ C.card := by simpa [C] using hBcardAB
      omega
    have hd₀ : q + 1 ≤ Erdos547EC2.degreeInto G a B₀ :=
      (by omega : q + 1 ≤ B₀.card - t).trans (hABraw a ha)
    have hloss := Erdos547EC2.degreeInto_sub_le_of_removed_le
      G a (b := 1) hremoveOne
    omega
  · intro b hb
    exact (by omega : q ≤ A.card - s).trans (hBAraw b (hBB₀ hb))
  · have heq : Vᵢ \ (A ∪ B) = C \ B := by
      ext z
      simp [C, and_assoc]
    rw [heq]
    exact hCminusB

/-- Zhao's Claim 7.12 in a fully source-shaped, reservoir-free interface.
The hypotheses are the balanced sparse-cut estimates needed for the two
applications of Proposition 7.3.  The conclusion says that no selected
large vertex is heavy into both sides. -/
theorem claim712_no_biheavy_of_sparse_balanced
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj]
    [DecidableRel G.Adj] (hT : T.IsTree) (homit : ¬ T ⊑ G)
    (X Y L : Finset W) (n t b s q k h : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (hXcard : X.card = n) (hYcard : Y.card = n)
    (hXY : Disjoint X Y) (hcoverXY : X ∪ Y = Finset.univ)
    (hlarge : ∀ v ∈ L, n ≤ G.degree v)
    (hcross : (G.interedges X Y).card < (b + 1) * (t + 1))
    (hscale : t * n ≤ s * (s + 1))
    (hcapXt : q + 1 + t + b ≤ (X ∩ L).card)
    (hcapXs : q + 1 + s + b ≤ (X ∩ L).card)
    (hcapXc : q + 1 + t + s + (X ∩ L).card ≤ n)
    (hcapYt : q + 1 + t + b ≤ (Y ∩ L).card)
    (hcapYs : q + 1 + s + b ≤ (Y ∩ L).card)
    (hcapYc : q + 1 + t + s + (Y ∩ L).card ≤ n)
    (htHeavy : t < h) (hkHeavy : k + s ≤ h)
    (hk2 : 2 ≤ k) (hkT : k ≤ Fintype.card V)
    (hkq : k ≤ q + 1)
    (hrootNumeric : n + 1 + 2 * (s + 1) ≤
      (k + 1) / 2 + 2 * ((n + 1) / 2))
    (hfinalNumeric : 2 * n + 1 ≤ (k + 1) / 2 + 4 * q) :
    ∀ v ∈ L, ¬(h ≤ Erdos547EC2.degreeInto G v X ∧
      h ≤ Erdos547EC2.degreeInto G v Y) := by
  classical
  intro v₀ hv₀L hv₀both
  have hlargeInto : ∀ v ∈ L,
      n ≤ Erdos547EC2.degreeInto G v Finset.univ := by
    intro v hv
    unfold Erdos547EC2.degreeInto
    rw [show (Finset.univ.filter fun w => G.Adj v w) = G.neighborFinset v by
      ext w
      simp [and_comm]]
    simpa using hlarge v hv
  obtain ⟨Aₓ, hAₓsub, hAₓcard, hAₓcross, hAₓinternal⟩ :=
    exists_low_cross_large_side G hXY hcoverXY hlargeInto hcross
  have hAₓX : Aₓ ⊆ X := fun z hz => (Finset.mem_inter.mp (hAₓsub hz)).1
  have hAₓL : Aₓ ⊆ L := fun z hz => (Finset.mem_inter.mp (hAₓsub hz)).2
  have hAₓupper : Aₓ.card ≤ (X ∩ L).card := Finset.card_le_card hAₓsub
  have hAₓt : q + 1 + t ≤ Aₓ.card := by omega
  have hAₓs : q + 1 + s ≤ Aₓ.card := by omega
  have hXminusAₓ : q + 1 + t + s ≤ (X \ Aₓ).card := by
    rw [Finset.card_sdiff_of_subset hAₓX, hXcard]
    omega
  obtain ⟨Bₓ, hBₓsub, hv₀Bₓ, hAₓBₓ, hAAₓ, hABₓ, hBAₓ, hmissX⟩ :=
    exists_claim712_reservoir_side_avoiding_strong G X Aₓ v₀ n t s q
      hXcard hAₓX hAₓinternal hAₓt hAₓs hXminusAₓ hscale
  have hcrossYX : (G.interedges Y X).card < (b + 1) * (t + 1) := by
    letI : Std.Symm G.Adj := G.symm
    rw [show (G.interedges Y X).card = (G.interedges X Y).card by
      exact (@Rel.card_interedges_comm W G.Adj _ _ X Y).symm]
    exact hcross
  obtain ⟨Aᵧ, hAᵧsub, hAᵧcard, hAᵧcross, hAᵧinternal⟩ :=
    exists_low_cross_large_side G hXY.symm
      (by simpa [Finset.union_comm] using hcoverXY) hlargeInto hcrossYX
  have hAᵧY : Aᵧ ⊆ Y := fun z hz => (Finset.mem_inter.mp (hAᵧsub hz)).1
  have hAᵧL : Aᵧ ⊆ L := fun z hz => (Finset.mem_inter.mp (hAᵧsub hz)).2
  have hAᵧupper : Aᵧ.card ≤ (Y ∩ L).card := Finset.card_le_card hAᵧsub
  have hAᵧt : q + 1 + t ≤ Aᵧ.card := by omega
  have hAᵧs : q + 1 + s ≤ Aᵧ.card := by omega
  have hYminusAᵧ : q + 1 + t + s ≤ (Y \ Aᵧ).card := by
    rw [Finset.card_sdiff_of_subset hAᵧY, hYcard]
    omega
  obtain ⟨Bᵧ, hBᵧsub, hv₀Bᵧ, hAᵧBᵧ, hAAᵧ, hABᵧ, hBAᵧ, hmissY⟩ :=
    exists_claim712_reservoir_side_avoiding_strong G Y Aᵧ v₀ n t s q
      hYcard hAᵧY hAᵧinternal hAᵧt hAᵧs hYminusAᵧ hscale
  have hv₀Aₓ : v₀ ∉ Aₓ := by
    intro hv
    have := hAₓcross v₀ hv
    omega
  have hv₀Aᵧ : v₀ ∉ Aᵧ := by
    intro hv
    have := hAᵧcross v₀ hv
    omega
  have hv₀Hₓ : v₀ ∉ Aₓ ∪ Bₓ := by simp [hv₀Aₓ, hv₀Bₓ]
  have hv₀Hᵧ : v₀ ∉ Aᵧ ∪ Bᵧ := by simp [hv₀Aᵧ, hv₀Bᵧ]
  have hBₓX : Bₓ ⊆ X := fun z hz =>
    (Finset.mem_sdiff.mp (hBₓsub hz)).1
  have hBᵧY : Bᵧ ⊆ Y := fun z hz =>
    (Finset.mem_sdiff.mp (hBᵧsub hz)).1
  have hHₓX : Aₓ ∪ Bₓ ⊆ X := Finset.union_subset hAₓX hBₓX
  have hHᵧY : Aᵧ ∪ Bᵧ ⊆ Y := Finset.union_subset hAᵧY hBᵧY
  have hhostXY : Disjoint (Aₓ ∪ Bₓ) (Aᵧ ∪ Bᵧ) :=
    hXY.mono hHₓX hHᵧY
  have hAₓne : Aₓ.Nonempty := Finset.card_pos.mp (by omega)
  have hAᵧne : Aᵧ.Nonempty := Finset.card_pos.mp (by omega)
  have hdegreeAₓ : ∀ a ∈ Aₓ, Fintype.card V - 1 ≤ G.degree a := by
    intro a ha
    have := hlarge a (hAₓL ha)
    omega
  have hdegreeAᵧ : ∀ a ∈ Aᵧ, Fintype.card V - 1 ≤ G.degree a := by
    intro a ha
    have := hlarge a (hAᵧL ha)
    omega
  have hheavy : Fintype.card V - 1 ≤ G.degree v₀ := by
    have := hlarge v₀ hv₀L
    omega
  have hpartition := Erdos547EC2.degreeInto_partition G v₀ hXY hcoverXY
  have htotal : n ≤ Erdos547EC2.degreeInto G v₀ X +
      Erdos547EC2.degreeInto G v₀ Y := by
    rw [hpartition]
    exact hlargeInto v₀ hv₀L
  have hrootSupplyX
      (hbig : (n + 1) / 2 ≤ Erdos547EC2.degreeInto G v₀ X) :
      n + 1 ≤ (k + 1) / 2 +
        2 * Erdos547EC2.degreeInto G v₀ (Aₓ ∪ Bₓ) := by
    have hloss := Erdos547EC2.degreeInto_le_add_removed
      G v₀ X (Aₓ ∪ Bₓ)
    omega
  have hrootSupplyY
      (hbig : (n + 1) / 2 ≤ Erdos547EC2.degreeInto G v₀ Y) :
      n + 1 ≤ (k + 1) / 2 +
        2 * Erdos547EC2.degreeInto G v₀ (Aᵧ ∪ Bᵧ) := by
    have hloss := Erdos547EC2.degreeInto_le_add_removed
      G v₀ Y (Aᵧ ∪ Bᵧ)
    omega
  have hselectedX : k ≤ Erdos547EC2.degreeInto G v₀ (Aₓ ∪ Bₓ) + 1 := by
    have hloss := Erdos547EC2.degreeInto_le_add_removed
      G v₀ X (Aₓ ∪ Bₓ)
    omega
  have hselectedY : k ≤ Erdos547EC2.degreeInto G v₀ (Aᵧ ∪ Bᵧ) + 1 := by
    have hloss := Erdos547EC2.degreeInto_le_add_removed
      G v₀ Y (Aᵧ ∪ Bᵧ)
    omega
  by_cases hbigX : (n + 1) / 2 ≤ Erdos547EC2.degreeInto G v₀ X
  · exact claim712_core_contradiction T G hT homit n q k hcardT hk2 hkT
      Aₓ Bₓ Aᵧ Bᵧ hAₓBₓ hAₓne hhostXY v₀ hv₀Hₓ
      hAAₓ hABₓ hBAₓ hAAᵧ hABᵧ hBAᵧ hdegreeAₓ hheavy
      (hrootSupplyX hbigX) hselectedY hkq hfinalNumeric
  · have hbigY : (n + 1) / 2 ≤ Erdos547EC2.degreeInto G v₀ Y := by
      omega
    exact claim712_core_contradiction T G hT homit n q k hcardT hk2 hkT
      Aᵧ Bᵧ Aₓ Bₓ hAᵧBᵧ hAᵧne hhostXY.symm v₀ hv₀Hᵧ
      hAAᵧ hABᵧ hBAᵧ hAAₓ hABₓ hBAₓ hdegreeAᵧ hheavy
      (hrootSupplyY hbigY) hselectedX hkq hfinalNumeric

end Erdos547Claim712

#print axioms Erdos547Claim712.tree_embedding_respecting_semibipartition
#print axioms Erdos547Claim712.independent_side_card_lt_of_no_leaves
#print axioms Erdos547Claim712.fact72_part2
#print axioms Erdos547Claim712.omitted_tree_has_no_small_independent_complement
#print axioms Erdos547Claim712.claim712_final_partition_estimate
#print axioms Erdos547Claim712.omitted_tree_forces_complement_large_class_le
#print axioms Erdos547Claim712.exists_low_cross_large_side
#print axioms Erdos547Claim712.exists_injective_root_placement
#print axioms Erdos547Claim712.hasRootedLeafPeeling_of_rootedForestCone_isTree
#print axioms Erdos547Claim712.omitted_tree_forces_both_core_parts_le
#print axioms Erdos547Claim712.claim712_core_contradiction
#print axioms Erdos547Claim712.exists_claim712_reservoir_side_avoiding_strong
#print axioms Erdos547Claim712.claim712_no_biheavy_of_sparse_balanced
#check Erdos547Claim712.claim712_no_biheavy_of_sparse_balanced
#print axioms Erdos547Claim712.claim712_no_biheavy_of_sparse_balanced
