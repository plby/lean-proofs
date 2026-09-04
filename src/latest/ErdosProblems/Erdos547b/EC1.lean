import ErdosProblems.Erdos547b.Structures
import ErdosProblems.Erdos547b.Partite
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Tactic

open scoped SimpleGraph

noncomputable section

namespace Erdos547b
namespace EC1Scratch

open SimpleGraph Finset

def degreeInto {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (S : Finset V) : ℕ :=
  (S.filter (G.Adj v)).card

@[simp] theorem degreeInto_def {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    degreeInto G v S = (S.filter (G.Adj v)).card := rfl

theorem degreeInto_le_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    degreeInto G v S ≤ S.card := by
  exact Finset.card_filter_le _ _

theorem degreeInto_univ {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v Finset.univ = G.degree v := by
  rw [degreeInto, ← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp [G.mem_neighborFinset]

theorem degreeInto_mono {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {A B : Finset V}
    (hAB : A ⊆ B) : degreeInto G v A ≤ degreeInto G v B := by
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hAB hw.1, hw.2⟩

theorem degreeInto_eq_card_inter {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S : Finset V) :
    degreeInto G v S = (G.neighborFinset v ∩ S).card := by
  apply congr_arg Finset.card
  ext w
  simp [degreeInto, G.mem_neighborFinset, and_comm]

/-- A nontrivial finite tree admits a bipartition covering every vertex. -/
theorem exists_treeBipartition {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) :
    ∃ U W : Finset V,
      Disjoint U W ∧ U ∪ W = Finset.univ ∧ T.IsBipartiteWith (U : Set V) (W : Set V) := by
  classical
  rcases hT.isBipartite.exists_isBipartiteWith with ⟨U, W, hUW⟩
  let UF : Finset V := Finset.univ.filter (fun v => v ∈ U)
  let WF : Finset V := Finset.univ.filter (fun v => v ∈ W)
  have hUF : (UF : Set V) = U := by ext v; simp [UF]
  have hWF : (WF : Set V) = W := by ext v; simp [WF]
  refine ⟨UF, WF, ?_, ?_, ?_⟩
  · rw [← Finset.disjoint_coe, hUF, hWF]
    exact hUW.disjoint
  · apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hv : v ∈ T.support := by
      rw [hT.connected.preconnected.support_eq_univ]
      trivial
    have := SimpleGraph.isBipartiteWith_support_subset hUW hv
    rw [Finset.mem_union]
    change v ∈ (UF : Set V) ∨ v ∈ (WF : Set V)
    rw [hUF, hWF]
    exact this
  · simpa only [hUF, hWF] using hUW

/-- A graph embedding respects a specified pair of source/target sides. -/
def RespectsSides {V W : Type*} {T : SimpleGraph V} {G : SimpleGraph W}
    (f : SimpleGraph.Embedding T G) (U Z : Finset V) (A B : Finset W) : Prop :=
  (∀ u ∈ U, f u ∈ A) ∧ (∀ z ∈ Z, f z ∈ B)

theorem card_interedges_eq_sum_degreeInto {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (G.interedges A B).card = ∑ a ∈ A, degreeInto G a B := by
  classical
  rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion]
  rw [Finset.card_biUnion]
  · simp [degreeInto]
  · intro a ha a' ha' haa'
    change Disjoint
      (Finset.map _ (Finset.filter (G.Adj a) B))
      (Finset.map _ (Finset.filter (G.Adj a') B))
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_map, Finset.mem_filter] at he he'
    rcases he with ⟨b, ⟨_, _⟩, rfl⟩
    rcases he' with ⟨b', ⟨_, _⟩, hab⟩
    exact haa' (congrArg Prod.fst hab).symm

theorem sum_degreeInto_comm {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, degreeInto G a B) = ∑ b ∈ B, degreeInto G b A := by
  rw [← card_interedges_eq_sum_degreeInto,
    ← card_interedges_eq_sum_degreeInto]
  have := G.symm
  exact Rel.card_interedges_comm A B

/-- Zhao's elementary density-pruning fact, with the square root represented
by an explicit rational parameter `eps`. -/
theorem dense_prune {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (eps : ℚ)
    (hA : A.Nonempty) (hB : B.Nonempty) (heps : 0 < eps) (heps1 : eps < 1)
    (hdense : 1 - eps ^ 2 ≤ G.edgeDensity A B) :
    ∃ B' ⊆ B,
      (1 - eps) * (B.card : ℚ) ≤ (B'.card : ℚ) ∧
      ∀ b ∈ B', (1 - eps) * (A.card : ℚ) ≤ (degreeInto G b A : ℚ) := by
  classical
  let B' : Finset V := B.filter fun b =>
    (1 - eps) * (A.card : ℚ) ≤ (degreeInto G b A : ℚ)
  refine ⟨B', Finset.filter_subset _ _, ?_, ?_⟩
  · by_contra hcard
    have hcard' : (B'.card : ℚ) < (1 - eps) * (B.card : ℚ) :=
      lt_of_not_ge hcard
    let C : Finset V := B \ B'
    have hCB : C ⊆ B := Finset.sdiff_subset
    have hBC : B' ⊆ B := Finset.filter_subset _ _
    have hdisj : Disjoint B' C := by
      rw [Finset.disjoint_left]
      intro b hbB' hbC
      exact (Finset.mem_sdiff.mp hbC).2 hbB'
    have hBCunion : B' ∪ C = B := Finset.union_sdiff_of_subset hBC
    have hcardBC : B'.card + C.card = B.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hBCunion]
    have hcardBCq : (B'.card : ℚ) + (C.card : ℚ) = B.card := by
      exact_mod_cast hcardBC
    have hCcard : eps * (B.card : ℚ) < (C.card : ℚ) := by
      linarith
    have hCne : C.Nonempty := by
      by_contra h
      have hposB : 0 < (B.card : ℚ) := by positivity
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty, Nat.cast_zero] at hCcard
      nlinarith
    let miss : V → ℚ := fun b => (A.card : ℚ) - degreeInto G b A
    have hmiss_nonneg : ∀ b, 0 ≤ miss b := by
      intro b
      dsimp [miss]
      exact sub_nonneg.mpr (mod_cast degreeInto_le_card G b A)
    have hbad : ∀ b ∈ C, eps * (A.card : ℚ) < miss b := by
      intro b hb
      have hbB : b ∈ B := hCB hb
      have hbnot : b ∉ B' := (Finset.mem_sdiff.mp hb).2
      have hlt : (degreeInto G b A : ℚ) < (1 - eps) * (A.card : ℚ) := by
        simpa only [B', Finset.mem_filter, hbB, true_and, not_le] using hbnot
      change eps * (A.card : ℚ) < (A.card : ℚ) - degreeInto G b A
      nlinarith
    have hCsum : (C.card : ℚ) * (eps * (A.card : ℚ)) < ∑ b ∈ C, miss b := by
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using
        (Finset.sum_lt_sum_of_nonempty hCne hbad)
    have hsubsetSum : (∑ b ∈ C, miss b) ≤ ∑ b ∈ B, miss b := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hCB (fun _ _ _ => hmiss_nonneg _)
    have hsum : (∑ b ∈ B, miss b) =
        (A.card : ℚ) * B.card - (G.interedges A B).card := by
      have hdegSumNat : (∑ b ∈ B, degreeInto G b A) = (G.interedges A B).card := by
        calc
          _ = ∑ a ∈ A, degreeInto G a B := (sum_degreeInto_comm G A B).symm
          _ = (G.interedges A B).card := (card_interedges_eq_sum_degreeInto G A B).symm
      have hdegSumQ : (∑ b ∈ B, (degreeInto G b A : ℚ)) =
          ((G.interedges A B).card : ℚ) := by
        exact_mod_cast hdegSumNat
      dsimp only [miss]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hdegSumQ]
      ring
    have hdenom : 0 < ((A.card : ℚ) * B.card) := by positivity
    have hedgeLower : (1 - eps ^ 2) * ((A.card : ℚ) * B.card) ≤
        (G.interedges A B).card := by
      exact (le_div_iff₀ hdenom).mp (by simpa [G.edgeDensity_def] using hdense)
    have htotalUpper : (∑ b ∈ B, miss b) ≤
        eps ^ 2 * ((A.card : ℚ) * B.card) := by
      rw [hsum]
      nlinarith
    have hposA : 0 < (A.card : ℚ) := by positivity
    have hmul := mul_lt_mul_of_pos_right hCcard (mul_pos heps hposA)
    have hmul' : eps ^ 2 * ((A.card : ℚ) * B.card) <
        (C.card : ℚ) * (eps * (A.card : ℚ)) := by
      calc
        eps ^ 2 * ((A.card : ℚ) * B.card) =
            (eps * (B.card : ℚ)) * (eps * (A.card : ℚ)) := by ring
        _ < _ := hmul
    have hstrict : eps ^ 2 * ((A.card : ℚ) * B.card) < ∑ b ∈ B, miss b :=
      hmul'.trans (hCsum.trans_le hsubsetSum)
    exact (not_lt_of_ge htotalUpper) hstrict
  · intro b hb
    exact (Finset.mem_filter.mp hb).2

def colorClassFinset {V : Type*} [Fintype V] {T : SimpleGraph V}
    (c : T.Coloring (Fin 2)) (i : Fin 2) : Finset V :=
  Finset.univ.filter fun v => c v = i

@[simp] theorem colorClassFinset_card {V : Type*} [Fintype V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) (i : Fin 2) :
    (colorClassFinset c i).card = Coloring.partCard c i := rfl

theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, rfl⟩
  · exact Or.inl hi
  · exact Or.inr (congrArg Fin.succ (Subsingleton.elim j 0))

theorem colorClassFinset_zero_union_one {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    colorClassFinset c 0 ∪ colorClassFinset c 1 = Finset.univ := by
  ext v
  simp only [colorClassFinset, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact iff_true_intro (fin_two_eq_zero_or_one (c v))

theorem colorClassFinset_zero_disjoint_one {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    Disjoint (colorClassFinset c 0) (colorClassFinset c 1) := by
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  simp only [colorClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hv0 hv1
  omega

theorem partCard_zero_add_one {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    Coloring.partCard c 0 + Coloring.partCard c 1 = Fintype.card V := by
  rw [← colorClassFinset_card, ← colorClassFinset_card,
    ← Finset.card_union_of_disjoint (colorClassFinset_zero_disjoint_one c),
    colorClassFinset_zero_union_one, Finset.card_univ]

theorem coloring_isBipartiteWith_zero_one {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    T.IsBipartiteWith (colorClassFinset c 0 : Set V) (colorClassFinset c 1 : Set V) := by
  constructor
  · exact Finset.disjoint_coe.mpr (colorClassFinset_zero_disjoint_one c)
  · intro v w hvw
    have hne := c.valid hvw
    by_cases hcv : c v = 0
    · have hcw : c w = 1 := by
        rcases fin_two_eq_zero_or_one (c w) with h | h
        · exact False.elim (hne (hcv.trans h.symm))
        · exact h
      exact Or.inl ⟨by simp [colorClassFinset, hcv], by simp [colorClassFinset, hcw]⟩
    · have hcv' : c v = 1 := (fin_two_eq_zero_or_one (c v)).resolve_left hcv
      have hcw : c w = 0 := by
        rcases fin_two_eq_zero_or_one (c w) with h | h
        · exact h
        · exact False.elim (hne (hcv'.trans h.symm))
      exact Or.inr ⟨by simp [colorClassFinset, hcv'], by simp [colorClassFinset, hcw]⟩

/-- Fact 6.9 in the only form needed for Fact 7.2: the larger colour class
of a nontrivial bipartite tree contains a leaf. -/
theorem exists_leaf_color_one_of_partCard_lt {V : Type*} [Fintype V]
    [DecidableEq V] [Nontrivial V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (c : T.Coloring (Fin 2))
    (hlt : Coloring.partCard c 0 < Coloring.partCard c 1) :
    ∃ x : V, c x = 1 ∧ T.degree x = 1 := by
  classical
  by_contra hleaf
  push_neg at hleaf
  let W := colorClassFinset c 1
  have hdegpos : ∀ x : V, 0 < T.degree x := by
    intro x
    rw [T.degree_pos_iff_mem_support]
    rw [hT.connected.preconnected.support_eq_univ]
    trivial
  have hdegTwo : ∀ x ∈ W, 2 ≤ T.degree x := by
    intro x hx
    have hxone : T.degree x ≠ 1 := hleaf x (by
      simpa only [W, colorClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hx)
    have hxpos := hdegpos x
    omega
  have hsumLower : 2 * W.card ≤ ∑ x ∈ W, T.degree x := by
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      (Finset.sum_le_sum fun x hx => hdegTwo x hx)
  have hsumEdge : (∑ x ∈ W, T.degree x) = T.edgeFinset.card := by
    simpa only [W, colorClassFinset] using
      (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
        (coloring_isBipartiteWith_zero_one c))
  have hedge := hT.card_edgeFinset
  have hparts := partCard_zero_add_one c
  have hWcard : W.card = Coloring.partCard c 1 := rfl
  rw [hsumEdge, hWcard] at hsumLower
  omega

/-- The part of a copy which is needed after recursively deleting leaves of
colour one: colour-zero vertices remain in the high-degree host set `A`. -/
def Copy.RespectsColorZero {V W : Type*} {T : SimpleGraph V} {G : SimpleGraph W}
    (c : T.Coloring (Fin 2)) (A : Finset W) (f : Copy T G) : Prop :=
  ∀ x, c x = 0 → f x ∈ A

theorem partCard_induce_compl_singleton_of_ne {r : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (c : T.Coloring (Fin r)) (x : V) (i : Fin r) (hxi : c x ≠ i) :
    Coloring.partCard (c.comap (Embedding.induce ({x}ᶜ : Set V)).toHom) i =
      Coloring.partCard c i := by
  classical
  unfold Coloring.partCard
  apply Finset.card_bij (fun (a : ({x}ᶜ : Set V)) _ => (a : V))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hax : a ≠ x := fun h => hxi (h ▸ ha)
    refine ⟨⟨a, by simpa using hax⟩, ?_, rfl⟩
    simpa using ha

theorem partCard_induce_compl_singleton_add_one {r : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    (c : T.Coloring (Fin r)) (x : V) :
    Coloring.partCard c (c x) =
      Coloring.partCard (c.comap (Embedding.induce ({x}ᶜ : Set V)).toHom) (c x) + 1 := by
  classical
  unfold Coloring.partCard
  rw [show (Finset.univ.filter fun a : V => c a = c x) =
      insert x ((Finset.univ.filter fun a : V => c a = c x).erase x) by
    rw [Finset.insert_erase (by simp)]]
  rw [Finset.card_insert_of_notMem]
  · congr 1
    apply Finset.card_bij (fun a ha => ⟨a, by
      have := (Finset.mem_erase.mp ha).1
      simpa using this⟩)
    · intro a ha
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simpa using ha.2
    · intro a₁ _ a₂ _ h
      exact Subtype.ext_iff.mp h
    · intro a ha
      refine ⟨a.1, ?_, rfl⟩
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact a.2
      · simpa using ha
  · simp

private theorem fact72_part1_oriented_aux {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nontrivial V]
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (c : T.Coloring (Fin 2)) (A B : Finset W)
    (hAB : Disjoint A B) (d : ℕ)
    (hbalance : Coloring.partCard c 1 = Coloring.partCard c 0 + d)
    (hpos : 0 < Coloring.partCard c 0)
    (hcardA : Coloring.partCard c 0 ≤ A.card)
    (hcardB : Coloring.partCard c 0 ≤ B.card)
    (hcrossA : ∀ a ∈ A, Coloring.partCard c 0 ≤ degreeInto G a B)
    (hcrossB : ∀ b ∈ B, Coloring.partCard c 0 ≤ degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a) :
    ∃ f : Copy T G, Copy.RespectsColorZero c A f := by
  classical
  induction d generalizing V with
  | zero =>
      have heq : Coloring.partCard c 1 = Coloring.partCard c 0 := by omega
      let P : Fin 2 → Finset W := Fin.cases A (fun _ => B)
      have hP0 : P 0 = A := rfl
      have hP1 : P 1 = B := rfl
      have hPdisj : Set.PairwiseDisjoint Set.univ P := by
        intro i _ j _ hij
        fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · change Disjoint A B
          exact hAB
        · change Disjoint B A
          exact hAB.symm
        · exact False.elim (hij rfl)
      have hPcap : ∀ i, Coloring.partCard c i ≤ (P i).card := by
        intro i
        fin_cases i
        · change Coloring.partCard c 0 ≤ A.card
          exact hcardA
        · change Coloring.partCard c 1 ≤ B.card
          omega
      have hPdeg : ∀ i j, i ≠ j → ∀ v ∈ P i,
          Coloring.partCard c j ≤ ((G.neighborFinset v) ∩ P j).card := by
        intro i j hij v hv
        fin_cases i <;> fin_cases j
        · exact False.elim (hij rfl)
        · change Coloring.partCard c 1 ≤ (G.neighborFinset v ∩ B).card
          rw [heq, ← degreeInto_eq_card_inter]
          exact hcrossA v (by change v ∈ A at hv; exact hv)
        · change Coloring.partCard c 0 ≤ (G.neighborFinset v ∩ A).card
          rw [← degreeInto_eq_card_inter]
          exact hcrossB v (by change v ∈ B at hv; exact hv)
        · exact False.elim (hij rfl)
      rcases tree_embedding_respecting_parts T G hT c P hPdisj hPcap hPdeg with ⟨f, hf⟩
      refine ⟨f, ?_⟩
      intro x hx
      simpa [Copy.RespectsParts, P, hx] using hf x
  | succ d ih =>
      have hlt : Coloring.partCard c 0 < Coloring.partCard c 1 := by omega
      obtain ⟨x, hcx, hxdeg⟩ := exists_leaf_color_one_of_partCard_lt T hT c hlt
      obtain ⟨p, hxp, hp_unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hxdeg
      let s : Set V := {x}ᶜ
      let T' : SimpleGraph s := T.induce s
      let c' : T'.Coloring (Fin 2) := c.comap (Embedding.induce s).toHom
      have hcardS : Fintype.card s + 1 = Fintype.card V := by
        have hc := Fintype.card_subtype_compl (fun a : V => a = x)
        change Fintype.card {a : V // ¬a = x} + 1 = Fintype.card V
        rw [hc]
        have hVpos : 0 < Fintype.card V := Fintype.card_pos
        simp only [Fintype.card_subtype_eq, Finset.filter_eq']
        omega
      have hT' : T'.IsTree := by
        exact ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hxdeg,
          hT.isAcyclic.induce s⟩
      have hpart0 : Coloring.partCard c' 0 = Coloring.partCard c 0 := by
        exact partCard_induce_compl_singleton_of_ne c x 0 (by simpa [hcx])
      have hpart1 : Coloring.partCard c 1 = Coloring.partCard c' 1 + 1 := by
        simpa [c', s, hcx] using partCard_induce_compl_singleton_add_one c x
      have hbalance' : Coloring.partCard c' 1 = Coloring.partCard c' 0 + d := by
        omega
      have hcardSlarge : 1 < Fintype.card s := by
        have hparts' := partCard_zero_add_one c'
        omega
      let : Nontrivial s := Fintype.one_lt_card_iff_nontrivial.mp hcardSlarge
      have hcardA' : Coloring.partCard c' 0 ≤ A.card := hpart0.symm ▸ hcardA
      have hcardB' : Coloring.partCard c' 0 ≤ B.card := hpart0.symm ▸ hcardB
      have hcrossA' : ∀ a ∈ A, Coloring.partCard c' 0 ≤ degreeInto G a B := by
        simpa only [hpart0] using hcrossA
      have hcrossB' : ∀ b ∈ B, Coloring.partCard c' 0 ≤ degreeInto G b A := by
        simpa only [hpart0] using hcrossB
      have hdegreeA' : ∀ a ∈ A, Fintype.card s - 1 ≤ G.degree a := by
        intro a ha
        exact le_trans (by omega) (hdegreeA a ha)
      rcases ih T' hT' c' hbalance' (by omega)
          hcardA' hcardB' hcrossA' hcrossB' hdegreeA' with ⟨f, hfzero⟩
      let ps : s := ⟨p, by simpa [s] using hxp.ne'⟩
      have hcp : c p = 0 := by
        have hne := c.valid hxp
        rcases fin_two_eq_zero_or_one (c p) with h | h
        · exact h
        · exact False.elim (hne (hcx.trans h.symm))
      have hparentA : f ps ∈ A := by
        apply hfzero ps
        simpa [c', ps] using hcp
      let usedWithoutParent : Finset W := (Finset.univ.erase ps).image f
      have hused_card : usedWithoutParent.card = Fintype.card s - 1 := by
        dsimp only [usedWithoutParent]
        calc
          ((Finset.univ.erase ps).image f).card = (Finset.univ.erase ps).card :=
            Finset.card_image_iff.mpr fun _ _ _ _ h => f.injective h
          _ = Fintype.card s - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ ps), Finset.card_univ]
      have hneighbor_card : usedWithoutParent.card < (G.neighborFinset (f ps)).card := by
        rw [hused_card, G.card_neighborFinset_eq_degree]
        exact lt_of_lt_of_le (by omega) (hdegreeA (f ps) hparentA)
      obtain ⟨w, hw_neighbor, hw_unused⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hneighbor_card
      have hw_adj : G.Adj (f ps) w := (G.mem_neighborFinset (f ps) w).mp hw_neighbor
      have hw_not_range : ∀ a : s, w ≠ f a := by
        intro a hwa
        by_cases ha : a = ps
        · subst a
          exact hw_adj.ne' hwa
        · apply hw_unused
          exact Finset.mem_image.mpr ⟨a,
            Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩, hwa.symm⟩
      let F : V → W := fun a => if h : a = x then w else f ⟨a, by simpa [s] using h⟩
      have hFmap : ∀ (u v : V), T.Adj u v → G.Adj (F u) (F v) := by
        intro u v huv
        by_cases hu : u = x
        · subst u
          have hvp : v = p := hp_unique v huv
          subst v
          simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj.symm
        · by_cases hv : v = x
          · subst v
            have hup : u = p := hp_unique u huv.symm
            subst u
            simpa [F, ps, hxp.ne, hxp.ne'] using hw_adj
          · let us : s := ⟨u, by simpa [s] using hu⟩
            let vs : s := ⟨v, by simpa [s] using hv⟩
            have huv' : T'.Adj us vs := by simpa [T', us, vs] using huv
            have hmap := f.toHom.map_adj huv'
            simpa [F, hu, hv, us, vs] using hmap
      have hFinj : Function.Injective F := by
        intro u v huv
        by_cases hu : u = x
        · subst u
          by_cases hv : v = x
          · exact hv.symm
          · exfalso
            apply hw_not_range ⟨v, by simpa [s] using hv⟩
            simpa [F, hv] using huv
        · by_cases hv : v = x
          · subst v
            exfalso
            apply hw_not_range ⟨u, by simpa [s] using hu⟩
            simpa [F, hu] using huv.symm
          · have hsub : (⟨u, by simpa [s] using hu⟩ : s) =
                ⟨v, by simpa [s] using hv⟩ := by
              apply f.injective
              simpa [F, hu, hv] using huv
            exact Subtype.ext_iff.mp hsub
      let Fcopy : Copy T G := ⟨⟨F, fun {_ _} h => hFmap _ _ h⟩, hFinj⟩
      refine ⟨Fcopy, ?_⟩
      intro u hcu
      have hux : u ≠ x := fun h => by subst u; simp [hcx] at hcu
      dsimp only [Fcopy]
      change F u ∈ A
      simpa [F, hux, c'] using hfzero ⟨u, by simpa [s] using hux⟩ hcu

def Coloring.swapTwo {V : Type*} {T : SimpleGraph V}
    (c : T.Coloring (Fin 2)) : T.Coloring (Fin 2) :=
  Coloring.mk (fun x => if c x = 0 then 1 else 0) (by
    intro v w hvw
    have hne := c.valid hvw
    rcases fin_two_eq_zero_or_one (c v) with hv | hv <;>
      rcases fin_two_eq_zero_or_one (c w) with hw | hw <;> simp_all)

@[simp] theorem Coloring.swapTwo_eq_zero_iff {V : Type*} {T : SimpleGraph V}
    (c : T.Coloring (Fin 2)) (x : V) : Coloring.swapTwo c x = 0 ↔ c x = 1 := by
  change (if c x = 0 then 1 else 0) = 0 ↔ c x = 1
  rcases fin_two_eq_zero_or_one (c x) with h | h <;> simp [Coloring.swapTwo, h]

@[simp] theorem Coloring.swapTwo_eq_one_iff {V : Type*} {T : SimpleGraph V}
    (c : T.Coloring (Fin 2)) (x : V) : Coloring.swapTwo c x = 1 ↔ c x = 0 := by
  change (if c x = 0 then 1 else 0) = 1 ↔ c x = 0
  rcases fin_two_eq_zero_or_one (c x) with h | h <;> simp [Coloring.swapTwo, h]

@[simp] theorem Coloring.partCard_swapTwo_zero {V : Type*} [Fintype V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    Coloring.partCard (Coloring.swapTwo c) 0 = Coloring.partCard c 1 := by
  unfold Coloring.partCard
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Coloring.swapTwo_eq_zero_iff]

@[simp] theorem Coloring.partCard_swapTwo_one {V : Type*} [Fintype V]
    {T : SimpleGraph V} (c : T.Coloring (Fin 2)) :
    Coloring.partCard (Coloring.swapTwo c) 1 = Coloring.partCard c 0 := by
  unfold Coloring.partCard
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Coloring.swapTwo_eq_one_iff]

/-- Zhao's Fact 7.2(1), in a finite form convenient for the dense-cut proof.
The target colour class placed in `A` may be whichever class is smaller. -/
theorem fact72_part1 {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nontrivial V]
    (T : SimpleGraph V) (G : SimpleGraph W) [DecidableRel T.Adj] [DecidableRel G.Adj]
    (hT : T.IsTree) (c : T.Coloring (Fin 2)) (A B : Finset W)
    (hAB : Disjoint A B)
    (hcardA : min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤ A.card)
    (hcardB : min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤ B.card)
    (hcrossA : ∀ a ∈ A,
      min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤ degreeInto G a B)
    (hcrossB : ∀ b ∈ B,
      min (Coloring.partCard c 0) (Coloring.partCard c 1) ≤ degreeInto G b A)
    (hdegreeA : ∀ a ∈ A, Fintype.card V - 1 ≤ G.degree a) : T ⊑ G := by
  classical
  let u : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨v, huv⟩ := hT.connected.preconnected.exists_adj_of_nontrivial u
  have hcu_ne : c u ≠ c v := c.valid huv
  have hpos0 : 0 < Coloring.partCard c 0 := by
    unfold Coloring.partCard
    apply Finset.card_pos.mpr
    rcases fin_two_eq_zero_or_one (c u) with hu | hu
    · exact ⟨u, by simp [hu]⟩
    · have hv : c v = 0 := (fin_two_eq_zero_or_one (c v)).resolve_right
          (fun h => hcu_ne (hu.trans h.symm))
      exact ⟨v, by simp [hv]⟩
  have hpos1 : 0 < Coloring.partCard c 1 := by
    unfold Coloring.partCard
    apply Finset.card_pos.mpr
    rcases fin_two_eq_zero_or_one (c u) with hu | hu
    · have hv : c v = 1 := (fin_two_eq_zero_or_one (c v)).resolve_left
          (fun h => hcu_ne (hu.trans h.symm))
      exact ⟨v, by simp [hv]⟩
    · exact ⟨u, by simp [hu]⟩
  by_cases hle : Coloring.partCard c 0 ≤ Coloring.partCard c 1
  · let d := Coloring.partCard c 1 - Coloring.partCard c 0
    have hbal : Coloring.partCard c 1 = Coloring.partCard c 0 + d := by
      dsimp [d]
      omega
    have hmin : min (Coloring.partCard c 0) (Coloring.partCard c 1) =
        Coloring.partCard c 0 := min_eq_left hle
    rcases fact72_part1_oriented_aux T G hT c A B hAB d hbal hpos0
        (hmin ▸ hcardA) (hmin ▸ hcardB)
        (by simpa only [hmin] using hcrossA) (by simpa only [hmin] using hcrossB)
        hdegreeA with ⟨f, _⟩
    exact ⟨f⟩

  · have hle' : Coloring.partCard c 1 ≤ Coloring.partCard c 0 := by omega
    let cs := Coloring.swapTwo c
    let d := Coloring.partCard cs 1 - Coloring.partCard cs 0
    have hbal : Coloring.partCard cs 1 = Coloring.partCard cs 0 + d := by
      dsimp [d]
      simp only [cs, Coloring.partCard_swapTwo_zero, Coloring.partCard_swapTwo_one]
      omega
    have hmin : min (Coloring.partCard c 0) (Coloring.partCard c 1) =
        Coloring.partCard c 1 := min_eq_right hle'
    rcases fact72_part1_oriented_aux T G hT cs A B hAB d hbal (by simpa [cs] using hpos1)
        (by simpa [cs, hmin] using hcardA) (by simpa [cs, hmin] using hcardB)
        (by simpa [cs, hmin] using hcrossA) (by simpa [cs, hmin] using hcrossB)
        hdegreeA with ⟨f, _⟩
    exact ⟨f⟩

theorem edgeDensity_ge_of_degreeInto {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (r : ℚ)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hdeg : ∀ a ∈ A, r * (B.card : ℚ) ≤ (degreeInto G a B : ℚ)) :
    r ≤ G.edgeDensity A B := by
  classical
  have hsum : (A.card : ℚ) * (r * B.card) ≤
      ∑ a ∈ A, (degreeInto G a B : ℚ) := by
    calc
      (A.card : ℚ) * (r * B.card) = ∑ _a ∈ A, r * (B.card : ℚ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun a ha => hdeg a ha
  have hedge : (A.card : ℚ) * (r * B.card) ≤ (G.interedges A B).card := by
    rw [card_interedges_eq_sum_degreeInto]
    simpa only [Nat.cast_sum] using hsum
  have hden : 0 < ((A.card : ℚ) * B.card) := by positivity
  rw [G.edgeDensity_def]
  apply (le_div_iff₀ hden).2
  nlinarith

theorem degreeInto_le_add_removed {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C W : Finset V) :
    degreeInto G v C ≤ degreeInto G v W + (C \ W).card := by
  classical
  unfold degreeInto
  calc
    (C.filter fun w => G.Adj v w).card ≤
        ((W.filter fun w => G.Adj v w) ∪ (C \ W)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
      by_cases hxW : x ∈ W
      · exact Or.inl ⟨hxW, hx.2⟩
      · exact Or.inr ⟨hx.1, hxW⟩
    _ ≤ (W.filter fun w => G.Adj v w).card + (C \ W).card :=
      Finset.card_union_le _ _

private theorem dense_cut_oriented {W : Type*} [Fintype W] [DecidableEq W] {m t : ℕ}
    (hm : 4 ≤ m) (G : SimpleGraph W) [DecidableRel G.Adj]
    (X Y L : Finset W)
    (hXY : Disjoint X Y) (hXcard : X.card = m) (hYcard : Y.card = m)
    (hL : L = Finset.univ.filter fun v => m ≤ G.degree v)
    (hhighX : m ≤ 2 * (X ∩ L).card)
    (hdense : (9999 : ℚ) / 10000 ≤ G.edgeDensity X Y)
    (T : SimpleGraph (Fin t)) (hT : T.IsTree) (hEdges : t - 1 ≤ m) : T ⊑ G := by
  classical
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hdenseYX : 1 - ((1 : ℚ) / 100) ^ 2 ≤ G.edgeDensity Y X := by
    rw [G.edgeDensity_comm]
    norm_num at hdense ⊢
    exact hdense
  rcases dense_prune G Y X ((1 : ℚ) / 100) hYne hXne (by norm_num) (by norm_num)
      hdenseYX with ⟨X', hX'X, hX'card, hX'deg⟩
  have hX'card' : (99 : ℚ) / 100 * m ≤ (X'.card : ℚ) := by
    rw [hXcard] at hX'card
    norm_num at hX'card ⊢
    exact hX'card
  have hX'deg' : ∀ x ∈ X', (99 : ℚ) / 100 * m ≤ (degreeInto G x Y : ℚ) := by
    intro x hx
    have h := hX'deg x hx
    rw [hYcard] at h
    norm_num at h ⊢
    exact h
  let H := X ∩ L
  let A := H ∩ X'
  have hHX : H ⊆ X := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hX'X' : X' ⊆ X := hX'X
  have hUnionSub : H ∪ X' ⊆ X := Finset.union_subset hHX hX'X'
  have hUnionCard : (H ∪ X').card ≤ m := by
    simpa [hXcard] using Finset.card_le_card hUnionSub
  have hCardIdentity := Finset.card_union_add_card_inter H X'
  have hHcard : m ≤ 2 * H.card := by simpa [H] using hhighX
  have hAcard : (49 : ℚ) / 100 * m ≤ (A.card : ℚ) := by
    have hAeq : A.card = (H ∩ X').card := rfl
    have hX'q := hX'card'
    norm_num at hX'q ⊢
    rw [hAeq]
    have hHq : (m : ℚ) ≤ 2 * H.card := by exact_mod_cast hHcard
    have hUq : ((H ∪ X').card : ℚ) ≤ m := by exact_mod_cast hUnionCard
    have hIq : ((H ∪ X').card : ℚ) + (H ∩ X').card = H.card + X'.card := by
      exact_mod_cast hCardIdentity
    nlinarith
  have hAne : A.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hz
    have hz' : (A.card : ℚ) = 0 := by exact_mod_cast Nat.eq_zero_of_not_pos hz
    rw [hz'] at hAcard
    norm_num at hAcard
    have hmposq : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have hAY : Disjoint A Y := by
    exact hXY.mono (fun x hx => hHX (Finset.mem_inter.mp hx).1) (fun _ h => h)
  have hAdegree : ∀ a ∈ A, m ≤ G.degree a := by
    intro a ha
    have haH : a ∈ H := (Finset.mem_inter.mp ha).1
    have haL : a ∈ L := (Finset.mem_inter.mp haH).2
    simpa [hL] using haL
  have hAYdensity : (99 : ℚ) / 100 ≤ G.edgeDensity A Y := by
    apply edgeDensity_ge_of_degreeInto G A Y ((99 : ℚ) / 100) hAne hYne
    intro a ha
    rw [hYcard]
    exact hX'deg' a ((Finset.mem_inter.mp ha).2)
  have hAYdensity' : 1 - ((1 : ℚ) / 10) ^ 2 ≤ G.edgeDensity A Y := by
    norm_num at hAYdensity ⊢
    exact hAYdensity
  rcases dense_prune G A Y ((1 : ℚ) / 10) hAne hYne (by norm_num) (by norm_num)
      hAYdensity' with ⟨B, hBY, hBcard, hBdeg⟩
  have hBcard' : (9 : ℚ) / 10 * m ≤ (B.card : ℚ) := by
    rw [hYcard] at hBcard
    norm_num at hBcard ⊢
    exact hBcard
  have hBdegA : ∀ b ∈ B, (441 : ℚ) / 1000 * m ≤
      (degreeInto G b A : ℚ) := by
    intro b hb
    have h := hBdeg b hb
    have hA := hAcard
    norm_num at h ⊢
    nlinarith
  have hremoved : ∀ a ∈ A, (degreeInto G a Y : ℚ) ≤
      degreeInto G a B + ((Y \ B).card : ℚ) := by
    intro a ha
    exact_mod_cast degreeInto_le_add_removed G a Y B
  have hYsdiff : (Y \ B).card + B.card = m := by
    rw [Finset.card_sdiff_of_subset hBY, hYcard]
    have := Finset.card_le_card hBY
    omega
  have hAdegB : ∀ a ∈ A, (89 : ℚ) / 100 * m ≤
      (degreeInto G a B : ℚ) := by
    intro a ha
    have hfull := hX'deg' a (Finset.mem_inter.mp ha).2
    have hrem := hremoved a ha
    have hbc := hBcard'
    have hYsdiffq : ((Y \ B).card : ℚ) + B.card = m := by exact_mod_cast hYsdiff
    simp only [degreeInto] at hrem hfull ⊢
    norm_num at hfull hbc ⊢
    nlinarith
  have hAcardNat : 49 * m ≤ 100 * A.card := by
    have hq : (49 : ℚ) * m ≤ 100 * A.card := by nlinarith [hAcard]
    exact_mod_cast hq
  have hBcardNat : 9 * m ≤ 10 * B.card := by
    have hq : (9 : ℚ) * m ≤ 10 * B.card := by nlinarith [hBcard']
    exact_mod_cast hq
  have hAdegBNat : ∀ a ∈ A, 89 * m ≤ 100 * degreeInto G a B := by
    intro a ha
    have hq : (89 : ℚ) * m ≤ 100 * degreeInto G a B := by nlinarith [hAdegB a ha]
    exact_mod_cast hq
  have hBdegANat : ∀ b ∈ B, 441 * m ≤ 1000 * degreeInto G b A := by
    intro b hb
    have hq : (441 : ℚ) * m ≤ 1000 * degreeInto G b A := by nlinarith [hBdegA b hb]
    exact_mod_cast hq
  have hX'cardNat : 99 * m ≤ 100 * X'.card := by
    have hq : (99 : ℚ) * m ≤ 100 * X'.card := by nlinarith [hX'card']
    exact_mod_cast hq
  by_cases ht : t = 1
  · subst t
    have hbot : T = ⊥ := by
      apply le_antisymm
      · intro u v huv
        exact False.elim (T.ne_of_adj huv (Subsingleton.elim u v))
      · exact bot_le
    subst T
    rw [bot_isContained_iff_card_le]
    obtain ⟨w, hw⟩ := hXne
    exact Fintype.card_pos_iff.mpr ⟨w⟩
  have ht2 : 2 ≤ t := by
    have htpos : 0 < t := by simpa using Fintype.card_pos_iff.mpr hT.connected.nonempty
    omega
  let : Nontrivial (Fin t) := Fin.nontrivial_iff_two_le.mpr ht2
  let c : T.Coloring (Fin 2) := Classical.choice hT.isBipartite
  let p := min (Coloring.partCard c 0) (Coloring.partCard c 1)
  let q := max (Coloring.partCard c 0) (Coloring.partCard c 1)
  have hpq : p + q = t := by
    dsimp [p, q]
    rw [min_add_max, partCard_zero_add_one]
    simp
  by_cases hsmall : 5 * p ≤ 2 * m
  · apply fact72_part1 T G hT c A B (hAY.mono (fun _ h => h) hBY)
    · dsimp [p] at hsmall ⊢
      omega
    · dsimp [p] at hsmall ⊢
      omega
    · intro a ha
      dsimp [p] at hsmall ⊢
      have hd := hAdegBNat a ha
      simp only [degreeInto] at hd ⊢
      omega
    · intro b hb
      dsimp [p] at hsmall ⊢
      have hd := hBdegANat b hb
      simp only [degreeInto] at hd ⊢
      omega
    · intro a ha
      exact le_trans (by simpa using hEdges) (hAdegree a ha)
  · have hlarge : 2 * m < 5 * p := by omega
    have hqBound : 100 * q ≤ 89 * m := by
      have htBound : t ≤ m + 1 := by omega
      omega
    have hX'Ydensity : (99 : ℚ) / 100 ≤ G.edgeDensity X' Y := by
      apply edgeDensity_ge_of_degreeInto G X' Y ((99 : ℚ) / 100)
      · exact Finset.card_pos.mp (by omega)
      · exact hYne
      · intro x hx
        rw [hYcard]
        exact hX'deg' x hx
    have hX'Ydensity' : 1 - ((1 : ℚ) / 10) ^ 2 ≤ G.edgeDensity X' Y := by
      norm_num at hX'Ydensity ⊢
      exact hX'Ydensity
    have hX'ne : X'.Nonempty := by
      exact Finset.card_pos.mp (by omega)
    rcases dense_prune G X' Y ((1 : ℚ) / 10) hX'ne hYne (by norm_num) (by norm_num)
        hX'Ydensity' with ⟨Y', hY'Y, hY'card, hY'deg⟩
    have hY'card' : (9 : ℚ) / 10 * m ≤ (Y'.card : ℚ) := by
      rw [hYcard] at hY'card
      norm_num at hY'card ⊢
      exact hY'card
    have hY'degX' : ∀ y ∈ Y', (891 : ℚ) / 1000 * m ≤
        (degreeInto G y X' : ℚ) := by
      intro y hy
      have h := hY'deg y hy
      have hx := hX'card'
      norm_num at h hx ⊢
      nlinarith only [h, hx]
    have hYsdiff' : (Y \ Y').card + Y'.card = m := by
      rw [Finset.card_sdiff_of_subset hY'Y, hYcard]
      have := Finset.card_le_card hY'Y
      omega
    have hX'degY' : ∀ x ∈ X', (89 : ℚ) / 100 * m ≤
        (degreeInto G x Y' : ℚ) := by
      intro x hx
      have hrem := degreeInto_le_add_removed G x Y Y'
      have hfull := hX'deg' x hx
      have hyc := hY'card'
      have hYsdiffq : ((Y \ Y').card : ℚ) + Y'.card = m := by exact_mod_cast hYsdiff'
      have hremq : (degreeInto G x Y : ℚ) ≤
          degreeInto G x Y' + (Y \ Y').card := by exact_mod_cast hrem
      simp only [degreeInto] at hremq hfull ⊢
      norm_num at hfull hyc ⊢
      nlinarith only [hremq, hfull, hyc, hYsdiffq]
    have hY'cardNat : 9 * m ≤ 10 * Y'.card := by
      have hq : (9 : ℚ) * m ≤ 10 * Y'.card := by nlinarith [hY'card']
      exact_mod_cast hq
    have hY'degX'Nat : ∀ y ∈ Y', 891 * m ≤ 1000 * degreeInto G y X' := by
      intro y hy
      have hq : (891 : ℚ) * m ≤ 1000 * degreeInto G y X' := by
        nlinarith [hY'degX' y hy]
      exact_mod_cast hq
    have hX'degY'Nat : ∀ x ∈ X', 89 * m ≤ 100 * degreeInto G x Y' := by
      intro x hx
      have hq : (89 : ℚ) * m ≤ 100 * degreeInto G x Y' := by
        nlinarith [hX'degY' x hx]
      exact_mod_cast hq
    let P : Fin 2 → Finset W := Fin.cases X' (fun _ => Y')
    apply tree_isContained_of_bicolored_minDegree T G hT c P
    · intro i _ j _ hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)

      · change Disjoint X' Y'
        exact hXY.mono hX'X hY'Y
      · change Disjoint Y' X'
        exact (hXY.mono hX'X hY'Y).symm
      · exact False.elim (hij rfl)
    · intro i
      fin_cases i
      · change Coloring.partCard c 0 ≤ X'.card
        have hc0q : Coloring.partCard c 0 ≤ q := le_max_left _ _
        omega
      · change Coloring.partCard c 1 ≤ Y'.card
        have hc1q : Coloring.partCard c 1 ≤ q := le_max_right _ _
        omega
    · intro i j hij v hv
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · change Coloring.partCard c 1 ≤ (G.neighborFinset v ∩ Y').card
        rw [← degreeInto_eq_card_inter]
        have hd := hX'degY'Nat v (by change v ∈ X' at hv; exact hv)
        have hc1q : Coloring.partCard c 1 ≤ q := le_max_right _ _
        omega
      · change Coloring.partCard c 0 ≤ (G.neighborFinset v ∩ X').card
        rw [← degreeInto_eq_card_inter]
        have hd := hY'degX'Nat v (by change v ∈ Y' at hv; exact hv)
        have hc0q : Coloring.partCard c 0 ≤ q := le_max_left _ _
        omega
      · exact False.elim (hij rfl)
/-- Zhao's extremal-case-1 argument at the explicit value `c = 10⁻⁴`,
specialized to the Ramsey problem (`σ = 1/2`). -/
theorem zhaoDenseCutEmbeddingProperty : ZhaoDenseCutEmbeddingProperty := by
  classical
  refine ⟨(1 : ℚ) / 10000, by norm_num, by norm_num, 5, ?_⟩
  intro n hn G hlarge hEC
  let : DecidableRel G.Adj := Classical.decRel _
  rcases hEC with ⟨X, Y, ⟨hXY, hXYunion, hXcard, hYcard⟩, hdense⟩
  let m := n - 1
  let L : Finset (Fin (2 * n - 2)) :=
    Finset.univ.filter fun v => m ≤ G.degree v
  have hm : 4 ≤ m := by
    dsimp [m]
    omega
  have hLlarge : m ≤ L.card := by
    simpa [m, L] using hlarge
  have hLsplit : (X ∩ L) ∪ (Y ∩ L) = L := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
    · intro hv
      have hvXY : v ∈ X ∪ Y := by
        rw [hXYunion]
        exact Finset.mem_univ v
      rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvX, hv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvY, hv⟩)
  have hdisjParts : Disjoint (X ∩ L) (Y ∩ L) := hXY.mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hsum : (X ∩ L).card + (Y ∩ L).card = L.card := by
    rw [← Finset.card_union_of_disjoint hdisjParts, hLsplit]
  have hdense' : (9999 : ℚ) / 10000 ≤ G.edgeDensity X Y := by
    norm_num at hdense ⊢
    exact hdense
  unfold ZhaoContainsAllTrees
  intro t T hT hEdges
  by_cases hhighX : m ≤ 2 * (X ∩ L).card
  · exact dense_cut_oriented hm G X Y L hXY (by simpa [m] using hXcard)
      (by simpa [m] using hYcard) rfl hhighX hdense' T hT (by simpa [m] using hEdges)
  · have hhighY : m ≤ 2 * (Y ∩ L).card := by omega
    apply dense_cut_oriented hm G Y X L hXY.symm (by simpa [m] using hYcard)
      (by simpa [m] using hXcard) rfl hhighY
    · rw [G.edgeDensity_comm]
      exact hdense'
    · exact hT
    · simpa [m] using hEdges

#print axioms Erdos547b.EC1Scratch.zhaoDenseCutEmbeddingProperty

end EC1Scratch
end Erdos547b
