/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos58.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finite.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Preorder.Finite

/-!
# Erdős Problem 73

The detailed mathematical proof and Leanization map are in `tex/73.tex`.

This file fixes the exact quantifier order and division-free formulation of
the problem and formalizes the elementary packing, deletion, separation,
bramble, odd-minor, and stable-defect steps of Reed's proof.  It also proves
the `k = 0` case and reduces the general theorem to one explicitly isolated
controlled-wall/high-order-bramble statement.  The remaining statement is
not assumed: it records the graph-minor/Escher-wall layer still to be proved.
-/

open Set
open scoped SimpleGraph Function

syntax (name := answerSyntax73) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos73

universe u

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

/-- A finite family of nonempty sets of rank at most `L` whose disjoint
packing number is smaller than `p` has a transversal of size smaller than
`p * L`.

This is the elementary maximal-packing argument used below for bounded-length
odd cycles: take a maximal pairwise-disjoint subfamily and hit every member of
the original family by the union of that packing. -/
theorem exists_small_hitting_set_of_no_disjoint_subfamily
    {α : Type*} (F : Finset (Finset α)) (p L : ℕ)
    (hL : 0 < L)
    (hnonempty : ∀ A ∈ F, A.Nonempty)
    (hcard : ∀ A ∈ F, A.card ≤ L)
    (hnopack : ∀ P : Finset (Finset α), P ⊆ F →
      (P : Set (Finset α)).PairwiseDisjoint id → P.card < p) :
    ∃ X : Finset α, X.card < p * L ∧ ∀ A ∈ F, ¬ Disjoint A X := by
  have hdec : ∀ P : Finset (Finset α),
      Decidable ((P : Set (Finset α)).PairwiseDisjoint id) :=
    fun P => Classical.dec _
  let C := F.powerset.filter fun P : Finset (Finset α) =>
    (P : Set (Finset α)).PairwiseDisjoint id
  obtain ⟨P, hPmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.2
    ⟨∅, Finset.empty_mem_powerset _, by simp⟩
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hPmax
  obtain ⟨hPF, hPdisj⟩ := hPmax.1
  let X := P.biUnion id
  refine ⟨X, ?_, ?_⟩
  · have hXcard : X.card ≤ P.card * L := by
      exact Finset.card_biUnion_le_card_mul P id L fun A hAP =>
        hcard A (hPF hAP)
    have hPcard : P.card < p := hnopack P hPF hPdisj
    exact hXcard.trans_lt (Nat.mul_lt_mul_of_pos_right hPcard hL)
  · intro A hAF hAX
    have hAnP : A ∉ P := by
      intro hAP
      obtain ⟨a, haA⟩ := hnonempty A hAF
      exact (Finset.disjoint_left.mp hAX haA)
        (Finset.mem_biUnion.mpr ⟨A, hAP, haA⟩)
    refine (hPmax.not_gt ?_ (Finset.ssubset_insert hAnP)).elim
    rw [Finset.insert_subset_iff, Finset.coe_insert]
    refine ⟨⟨hAF, hPF⟩, hPdisj.insert ?_⟩
    intro B hBP _
    exact (Finset.disjoint_biUnion_right A P id).mp hAX B hBP

/-- Every subgraph has an independent set of size at least
`(|V(H)| - k) / 2`, in the exact division-free natural-number form. -/
def EverySubgraphHasLargeIndepSet {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, H.verts.ncard ≤ 2 * H.coe.indepNum + k

/-- Reed's induced-subgraph presentation of the same hereditary independence
condition. -/
def EveryInducedSubgraphHasLargeIndepSet {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Set V,
    s.ncard ≤ 2 * (((⊤ : G.Subgraph).induce s).coe.indepNum) + k

/-- Deleting at most `C` vertices leaves a bipartite induced graph. -/
def BipartiteAfterDeletingAtMost {V : Type*}
    (C : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, X.card ≤ C ∧
    (G.induce (X : Set V)ᶜ).IsBipartite

lemma BipartiteAfterDeletingAtMost.mono {V : Type*}
    {C D : ℕ} {G : SimpleGraph V} (hCD : C ≤ D)
    (h : BipartiteAfterDeletingAtMost C G) :
    BipartiteAfterDeletingAtMost D G := by
  obtain ⟨X, hXC, hX⟩ := h
  exact ⟨X, hXC.trans hCD, hX⟩

lemma bipartiteAfterDeletingAtMost_zero_iff {V : Type*}
    (G : SimpleGraph V) :
    BipartiteAfterDeletingAtMost 0 G ↔ G.IsBipartite := by
  constructor
  · rintro ⟨X, hXcard, hbip⟩
    have hX : X = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hXcard)
    subst X
    have hset : ((↑(∅ : Finset V) : Set V)ᶜ) = Set.univ := by
      ext v
      simp
    change (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)).IsBipartite at hbip
    rw [hset] at hbip
    obtain ⟨c⟩ := hbip
    refine ⟨c.comp (SimpleGraph.induceUnivIso G).symm.toHom⟩
  · rintro ⟨c⟩
    refine ⟨∅, by simp, ?_⟩
    have hbip : (G.induce Set.univ).IsBipartite :=
      ⟨c.comp (SimpleGraph.induceUnivIso G).toHom⟩
    have hset : ((↑(∅ : Finset V) : Set V)ᶜ) = Set.univ := by
      ext v
      simp
    change (G.induce ((↑(∅ : Finset V) : Set V)ᶜ)).IsBipartite
    rw [hset]
    exact hbip

/-- A vertex separation is a pair of vertex sets covering the graph, with no
edge between the two exclusive sides.  Its order is the cardinality of
`A ∩ B`.  This is the finite-set presentation used in the inductive first
step of Kawarabayashi--Reed's proof. -/
def IsVertexSeparation {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) : Prop :=
  A ∪ B = Finset.univ ∧
    ∀ ⦃a b : V⦄, a ∈ A → a ∉ B → b ∈ B → b ∉ A → ¬ G.Adj a b

/-- Bipartite colorings on the two exclusive sides of a vertex separation
glue after deleting the separator.  Extra deletion sets `X₁` and `X₂` are
allowed on the two sides; this is exactly the coloring step used when two
inductive odd-cycle transversals are combined. -/
theorem isBipartite_induce_compl_union_of_separation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B X₁ X₂ : Finset V) (hsep : IsVertexSeparation G A B)
    (hA : (G.induce (((A \ B) \ X₁ : Finset V) : Set V)).IsBipartite)
    (hB : (G.induce (((B \ A) \ X₂ : Finset V) : Set V)).IsBipartite) :
    (G.induce ((((X₁ ∪ X₂) ∪ (A ∩ B) : Finset V) : Set V)ᶜ)).IsBipartite := by
  let X := (X₁ ∪ X₂) ∪ (A ∩ B)
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  have hside : ∀ v : ↥((X : Set V)ᶜ),
      (v.1 ∈ A ∧ v.1 ∉ B ∧ v.1 ∉ X₁) ∨
        (v.1 ∈ B ∧ v.1 ∉ A ∧ v.1 ∉ X₂) := by
    intro v
    have hvX : v.1 ∉ X := by
      simpa only [Set.mem_compl_iff, Finset.mem_coe] using v.2
    have hvsep : v.1 ∉ A ∩ B := by
      intro hv
      exact hvX (Finset.mem_union_right _ hv)
    have hvcover : v.1 ∈ A ∨ v.1 ∈ B := by
      have : v.1 ∈ A ∪ B := by rw [hsep.1]; exact Finset.mem_univ _
      exact Finset.mem_union.mp this
    rcases hvcover with hvA | hvB
    · left
      refine ⟨hvA, ?_, ?_⟩
      · intro hvB
        exact hvsep (Finset.mem_inter.mpr ⟨hvA, hvB⟩)
      · intro hvX₁
        exact hvX (Finset.mem_union_left _ (Finset.mem_union_left _ hvX₁))
    · right
      refine ⟨hvB, ?_, ?_⟩
      · intro hvA
        exact hvsep (Finset.mem_inter.mpr ⟨hvA, hvB⟩)
      · intro hvX₂
        exact hvX (Finset.mem_union_left _ (Finset.mem_union_right _ hvX₂))
  let color : ↥((X : Set V)ᶜ) → Fin 2 := fun v ↦
    if hv : v.1 ∈ A then
      cA ⟨v.1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hv,
            ((hside v).resolve_right (fun h ↦ h.2.1 hv)).2.1⟩,
          (hside v).resolve_right (fun h ↦ h.2.1 hv) |>.2.2⟩⟩
    else
      cB ⟨v.1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(hside v).resolve_left (fun h ↦ hv h.1) |>.1,
            hv⟩,
          (hside v).resolve_left (fun h ↦ hv h.1) |>.2.2⟩⟩
  change (G.induce (X : Set V)ᶜ).Colorable 2
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw
  by_cases hvA : v.1 ∈ A
  · by_cases hwA : w.1 ∈ A
    · simp only [color, dif_pos hvA, dif_pos hwA]
      exact cA.valid hvw
    · have hv := (hside v).resolve_right (fun h ↦ h.2.1 hvA)
      have hw := (hside w).resolve_left (fun h ↦ hwA h.1)
      exact (hsep.2 hv.1 hv.2.1 hw.1 hw.2.1 hvw).elim
  · by_cases hwA : w.1 ∈ A
    · have hv := (hside v).resolve_left (fun h ↦ hvA h.1)
      have hw := (hside w).resolve_right (fun h ↦ h.2.1 hwA)
      exact (hsep.2 hw.1 hw.2.1 hv.1 hv.2.1 hvw.symm).elim
    · simp only [color, dif_neg hvA, dif_neg hwA]
      exact cB.valid hvw

/-- The concrete exceptional set used in the separation gluing theorem has
the expected additive cardinality bound. -/
lemma card_union_union_inter_le (A B X₁ X₂ : Finset V) :
    ((X₁ ∪ X₂) ∪ (A ∩ B)).card ≤ X₁.card + X₂.card + (A ∩ B).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- A deletion set in an induced graph can be viewed as a deletion set in
the ambient vertex type, with the same cardinality. -/
lemma bipartiteAfterDeletingAtMost_induce_finset
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) (C : ℕ)
    (h : BipartiteAfterDeletingAtMost C (G.induce (S : Set V))) :
    ∃ X : Finset V, X ⊆ S ∧ X.card ≤ C ∧
      (G.induce (((S \ X : Finset V) : Set V))).IsBipartite := by
  obtain ⟨Y, hYC, hYbip⟩ := h
  let valEmb : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  let X : Finset V := Y.map valEmb
  refine ⟨X, ?_, ?_, ?_⟩
  · intro v hvX
    obtain ⟨y, hyY, rfl⟩ := Finset.mem_map.mp hvX
    exact y.2
  · simpa only [X, Finset.card_map] using hYC
  · obtain ⟨c⟩ := hYbip
    let color : ↥(((S \ X : Finset V) : Set V)) → Fin 2 := fun v ↦
      c ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, by
        have hvX : v.1 ∉ X := (Finset.mem_sdiff.mp v.2).2
        intro hvY
        apply hvX
        exact Finset.mem_map.mpr
          ⟨⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, hvY, rfl⟩⟩
    change (G.induce ((S \ X : Finset V) : Set V)).Colorable 2
    refine ⟨SimpleGraph.Coloring.mk color ?_⟩
    intro v w hvw
    exact c.valid hvw

/-- Odd-cycle transversals on both exclusive sides of a separation combine
with its separator.  This is the precise quantitative gluing calculation
`f(k) ≥ 2 f(k-1) + ℓ(k)` in the first step of the
Kawarabayashi--Reed induction. -/
theorem bipartiteAfterDeletingAtMost_of_separation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (C₁ C₂ : ℕ) (hsep : IsVertexSeparation G A B)
    (hA : BipartiteAfterDeletingAtMost C₁
      (G.induce (((A \ B : Finset V) : Set V))))
    (hB : BipartiteAfterDeletingAtMost C₂
      (G.induce (((B \ A : Finset V) : Set V)))) :
    BipartiteAfterDeletingAtMost (C₁ + C₂ + (A ∩ B).card) G := by
  obtain ⟨X₁, -, hX₁, hbipA⟩ :=
    bipartiteAfterDeletingAtMost_induce_finset G (A \ B) C₁ hA
  obtain ⟨X₂, -, hX₂, hbipB⟩ :=
    bipartiteAfterDeletingAtMost_induce_finset G (B \ A) C₂ hB
  refine ⟨(X₁ ∪ X₂) ∪ (A ∩ B), ?_, ?_⟩
  · exact (card_union_union_inter_le A B X₁ X₂).trans
      (Nat.add_le_add_right (Nat.add_le_add hX₁ hX₂) _)
  · exact isBipartite_induce_compl_union_of_separation
      G A B X₁ X₂ hsep hbipA hbipB

/-- Two finite vertex sets touch when they meet or an edge joins them. -/
def FinsetTouches {V : Type*} (G : SimpleGraph V)
    (A B : Finset V) : Prop :=
  ¬ Disjoint A B ∨ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

lemma finsetTouches_comm {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    FinsetTouches G A B ↔ FinsetTouches G B A := by
  constructor
  · rintro (h | ⟨a, ha, b, hb, hab⟩)
    · exact Or.inl fun hBA ↦ h hBA.symm
    · exact Or.inr ⟨b, hb, a, ha, hab.symm⟩
  · rintro (h | ⟨b, hb, a, ha, hba⟩)
    · exact Or.inl fun hAB ↦ h hAB.symm
    · exact Or.inr ⟨a, ha, b, hb, hba.symm⟩

/-- A finite bramble is a finite family of nonempty connected vertex sets,
every two of which touch.  Since the host vertex type is finite, this finite
presentation loses no members from the brambles used by Reed. -/
def IsFiniteBramble {V : Type*} [Fintype V]
    (G : SimpleGraph V) (β : Finset (Finset V)) : Prop :=
  (∀ A ∈ β, (G.induce (A : Set V)).Connected) ∧
    ∀ A ∈ β, ∀ B ∈ β, A ≠ B → FinsetTouches G A B

/-- A bramble has order at least `q` when each finset meeting all its
members has at least `q` vertices. -/
def BrambleOrderAtLeast {V : Type*}
    (q : ℕ) (β : Finset (Finset V)) : Prop :=
  ∀ X : Finset V, (∀ A ∈ β, ¬ Disjoint X A) → q ≤ X.card

/-- The canonical bramble `β_W`: connected sets containing more than half
of a prescribed vertex set `W`. -/
def majorityConnectedFamily {V : Type*} [Fintype V]
    (G : SimpleGraph V) (W : Finset V) : Finset (Finset V) :=
  Finset.univ.filter fun A ↦
    (G.induce (A : Set V)).Connected ∧ W.card < 2 * (A ∩ W).card

/-- Two subsets each containing more than half of the same finite set must
intersect. -/
lemma not_disjoint_of_two_mul_inter_gt_card
    {V : Type*} [DecidableEq V] {W A B : Finset V}
    (hA : W.card < 2 * (A ∩ W).card)
    (hB : W.card < 2 * (B ∩ W).card) :
    ¬ Disjoint A B := by
  intro hAB
  have hdisj : Disjoint (A ∩ W) (B ∩ W) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hsub : (A ∩ W) ∪ (B ∩ W) ⊆ W := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_inter.mp hv).2
    · exact (Finset.mem_inter.mp hv).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  omega

/-- The majority-connected family is indeed a bramble.  Pairwise touching
is already forced by intersection; no edge case is needed. -/
theorem majorityConnectedFamily_isFiniteBramble
    {V : Type*} [Fintype V] (G : SimpleGraph V) (W : Finset V) :
    IsFiniteBramble G (majorityConnectedFamily G W) := by
  constructor
  · intro A hA
    have hA' : (G.induce (A : Set V)).Connected ∧
        W.card < 2 * (A ∩ W).card := by
      simpa only [majorityConnectedFamily, Finset.mem_filter,
        Finset.mem_univ, true_and] using hA
    exact hA'.1
  · intro A hA B hB _
    have hAm : W.card < 2 * (A ∩ W).card := by
      have hA' : (G.induce (A : Set V)).Connected ∧
          W.card < 2 * (A ∩ W).card := by
        simpa only [majorityConnectedFamily, Finset.mem_filter,
          Finset.mem_univ, true_and] using hA
      exact hA'.2
    have hBm : W.card < 2 * (B ∩ W).card := by
      have hB' : (G.induce (B : Set V)).Connected ∧
          W.card < 2 * (B ∩ W).card := by
        simpa only [majorityConnectedFamily, Finset.mem_filter,
          Finset.mem_univ, true_and] using hB
      exact hB'.2
    exact Or.inl (not_disjoint_of_two_mul_inter_gt_card hAm hBm)

/-- The usual lower-bound proof for bramble order: every smaller set misses
one bramble member. -/
lemma brambleOrderAtLeast_of_small_set_misses
    {V : Type*} (q : ℕ) (β : Finset (Finset V))
    (hmiss : ∀ X : Finset V, X.card < q →
      ∃ A ∈ β, Disjoint X A) :
    BrambleOrderAtLeast q β := by
  intro X hhit
  by_contra hq
  obtain ⟨A, hAβ, hXA⟩ := hmiss X (Nat.lt_of_not_ge hq)
  exact hhit A hAβ hXA

/-- Mapping subgraphs along a graph embedding is injective. -/
lemma subgraphMap_injective_of_embedding
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) :
    Function.Injective (fun K : G.Subgraph ↦ K.map f.toHom) := by
  have reflect_le : ∀ {K L : G.Subgraph},
      K.map f.toHom ≤ L.map f.toHom → K ≤ L := by
    intro K L hKL
    constructor
    · intro v hv
      have hfv : f v ∈ (K.map f.toHom).verts := by
        exact ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hfw⟩ := hKL.1 hfv
      exact (f.injective hfw).symm ▸ hw
    · intro v w hvw
      have hmap : (K.map f.toHom).Adj (f v) (f w) :=
        ⟨v, w, hvw, rfl, rfl⟩
      obtain ⟨v', w', hvw', hv', hw'⟩ := hKL.2 hmap
      have hvEq : v' = v := f.injective hv'
      have hwEq : w' = w := f.injective hw'
      simpa only [hvEq, hwEq] using hvw'
  intro K L h
  apply le_antisymm
  · exact reflect_le (h.le)
  · exact reflect_le (h.ge)

/-- The exact uniform assertion asked in Problem 73, normalized to finite
graphs on `Fin n`.  In particular, `C` is chosen before the graph and cannot
depend on its number of vertices. -/
def Problem73 : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    EverySubgraphHasLargeIndepSet k G →
      BipartiteAfterDeletingAtMost C G

/-- The same assertion quantified over arbitrary finite vertex types. -/
def GeneralProblem73 : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ (V : Type) [Finite V], ∀ G : SimpleGraph V,
    EverySubgraphHasLargeIndepSet k G →
      BipartiteAfterDeletingAtMost C G

/-- Removing edges cannot decrease the independence number. -/
lemma indepNum_anti {V : Type*} [Finite V] {G H : SimpleGraph V}
    (hGH : G ≤ H) : H.indepNum ≤ G.indepNum := by
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  have hIG : G.IsIndepSet (I : Set V) := by
    intro v hv w hw hvw hadj
    exact hI.isIndepSet hv hw hvw (hGH hadj)
  simpa only [hI.card_eq] using hIG.card_le_indepNum

/-- A subgraph has no more edges than the ambient graph induced on the same
vertex set. -/
lemma coe_le_induce_verts {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) :
    H.coe ≤ ((⊤ : G.Subgraph).induce H.verts).coe := by
  intro v w hadj
  exact ⟨v.2, w.2, H.adj_sub hadj⟩

/-- Quantifying the independence inequality over all subgraphs is equivalent
to quantifying over induced subgraphs. -/
theorem everySubgraph_iff_everyInducedSubgraph {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) :
    EverySubgraphHasLargeIndepSet k G ↔
      EveryInducedSubgraphHasLargeIndepSet k G := by
  constructor
  · intro h s
    exact h ((⊤ : G.Subgraph).induce s)
  · intro h H
    have hs := h H.verts
    have hα : ((⊤ : G.Subgraph).induce H.verts).coe.indepNum ≤ H.coe.indepNum :=
      indepNum_anti (coe_le_induce_verts H)
    omega

/-- A graph can be made half-stable after deleting at most `k` vertices.
The independent set `I` is explicitly required to avoid the deleted set
`Y`; the last inequality says that it contains at least half of the
remaining vertices. -/
def HasHalfStableDeletion {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ Y I : Finset V,
    Y.card ≤ k ∧ Disjoint Y I ∧ G.IsIndepSet (I : Set V) ∧
      Nat.card V - Y.card ≤ 2 * I.card

/-- Reed's `k`-near-bipartite condition: every induced subgraph can be made
half-stable after deleting at most `k` vertices. -/
def IsKNearBipartite {V : Type*} [Finite V]
    (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Set V,
    HasHalfStableDeletion k (((⊤ : G.Subgraph).induce s).coe)

/-- Reed's theorem in its uniform `k`-near-bipartite formulation, on the
same canonical finite vertex types used by `Problem73`. -/
def ReedNearBipartiteStatement : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    IsKNearBipartite k G → BipartiteAfterDeletingAtMost C G

/-- For one finite graph, additive independence defect at most `k` is
equivalent to deletion of at most `k` vertices to half-stability. -/
theorem card_le_two_mul_indepNum_add_iff_halfStableDeletion
    {V : Type*} [Finite V] (k : ℕ) (G : SimpleGraph V) :
    Nat.card V ≤ 2 * G.indepNum + k ↔ HasHalfStableDeletion k G := by
  let _ := Fintype.ofFinite V
  constructor
  · intro h
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    let r := Nat.card V - 2 * G.indepNum
    have hrk : r ≤ k := by
      dsimp only [r]
      omega
    have hrcomp : r ≤ Iᶜ.card := by
      rw [Finset.card_compl, hI.card_eq]
      rw [← Nat.card_eq_fintype_card]
      dsimp only [r]
      omega
    obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq hrcomp
    refine ⟨Y, I, ?_, ?_, hI.isIndepSet, ?_⟩
    · simpa only [hYcard] using hrk
    · rw [Finset.disjoint_left]
      intro v hvY hvI
      have : v ∈ Iᶜ := hYsub hvY
      exact (Finset.mem_compl.mp this) hvI
    · rw [hYcard, hI.card_eq]
      dsimp only [r]
      omega
  · rintro ⟨Y, I, hYk, -, hI, hhalf⟩
    have hIα : I.card ≤ G.indepNum := hI.card_le_indepNum
    have hYV : Y.card ≤ Nat.card V := by
      rw [Nat.card_eq_fintype_card]
      exact Finset.card_le_univ Y
    omega

/-- The hereditary additive inequality is exactly Reed's
`k`-near-bipartite condition. -/
theorem everyInducedSubgraph_iff_isKNearBipartite
    {V : Type*} [Finite V] (k : ℕ) (G : SimpleGraph V) :
    EveryInducedSubgraphHasLargeIndepSet k G ↔ IsKNearBipartite k G := by
  constructor
  · intro h s
    apply (card_le_two_mul_indepNum_add_iff_halfStableDeletion
      k (((⊤ : G.Subgraph).induce s).coe)).mp
    simpa only [Nat.card_coe_set_eq, SimpleGraph.Subgraph.induce_verts] using h s
  · intro h s
    have hs := (card_le_two_mul_indepNum_add_iff_halfStableDeletion
      k (((⊤ : G.Subgraph).induce s).coe)).mpr (h s)
    simpa only [Nat.card_coe_set_eq, SimpleGraph.Subgraph.induce_verts] using hs

/-- The hypothesis in the wording of Problem 73 is exactly Reed's
`k`-near-bipartite condition.  This theorem joins the two elementary
normalization steps above and is the interface to the structural theorem. -/
theorem everySubgraph_iff_isKNearBipartite
    {V : Type*} [Finite V] (k : ℕ) (G : SimpleGraph V) :
    EverySubgraphHasLargeIndepSet k G ↔ IsKNearBipartite k G := by
  rw [everySubgraph_iff_everyInducedSubgraph,
    everyInducedSubgraph_iff_isKNearBipartite]

/-- There is no loss of content between the literal statement of Problem 73
and Reed's near-bipartite formulation. -/
theorem problem73_iff_reedNearBipartiteStatement :
    Problem73 ↔ ReedNearBipartiteStatement := by
  constructor
  · intro h k
    obtain ⟨C, hC⟩ := h k
    refine ⟨C, fun n G hG ↦ hC n G ?_⟩
    exact (everySubgraph_iff_isKNearBipartite k G).mpr hG
  · intro h k
    obtain ⟨C, hC⟩ := h k
    refine ⟨C, fun n G hG ↦ hC n G ?_⟩
    exact (everySubgraph_iff_isKNearBipartite k G).mp hG

/-- Any particular subgraph whose independence deficit is exactly `r`
certifies that the hereditary deficit parameter is at least `r`. -/
lemma deficit_witness_le {V : Type*} [Finite V] {k r : ℕ}
    {G : SimpleGraph V} (hG : EverySubgraphHasLargeIndepSet k G)
    (H : G.Subgraph)
    (hdefect : H.verts.ncard = 2 * H.coe.indepNum + r) :
    r ≤ k := by
  have hbound := hG H
  omega

/-- The independence number is bounded by the number of vertices. -/
lemma indepNum_le_natCard {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.indepNum ≤ Nat.card V := by
  let _ := Fintype.ofFinite V
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  rw [← hI.card_eq, Nat.card_eq_fintype_card]
  exact Finset.card_le_univ I

/-- Independence number is additive under disjoint union of finite graphs. -/
lemma indepNum_sum {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).indepNum = G.indepNum + H.indepNum := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  apply Nat.le_antisymm
  · obtain ⟨I, hI⟩ := (G ⊕g H).exists_isNIndepSet_indepNum
    have hleft : G.IsIndepSet (I.toLeft : Set V) := by
      intro v hv w hw hvw hadj
      exact hI.isIndepSet (by simpa using hv) (by simpa using hw)
        (fun h ↦ hvw (Sum.inl.inj h)) (by simpa using hadj)
    have hright : H.IsIndepSet (I.toRight : Set W) := by
      intro v hv w hw hvw hadj
      exact hI.isIndepSet (by simpa using hv) (by simpa using hw)
        (fun h ↦ hvw (Sum.inr.inj h)) (by simpa using hadj)
    have hl := hleft.card_le_indepNum
    have hr := hright.card_le_indepNum
    rw [← hI.card_eq, ← I.card_toLeft_add_card_toRight]
    omega
  · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨J, hJ⟩ := H.exists_isNIndepSet_indepNum
    have hsum : (G ⊕g H).IsIndepSet (I.disjSum J : Set (V ⊕ W)) := by
      intro v hv w hw hvw hadj
      rcases v with v | v <;> rcases w with w | w
      · exact hI.isIndepSet (by simpa using hv) (by simpa using hw)
          (fun h ↦ hvw (congrArg Sum.inl h)) (by simpa using hadj)
      · exact SimpleGraph.not_adj_sum_inl_inr v w hadj
      · exact SimpleGraph.not_adj_sum_inl_inr w v
          ((G ⊕g H).adj_symm hadj)
      · exact hJ.isIndepSet (by simpa using hv) (by simpa using hw)
          (fun h ↦ hvw (congrArg Sum.inr h)) (by simpa using hadj)
    simpa only [Finset.card_disjSum, hI.card_eq, hJ.card_eq] using
      hsum.card_le_indepNum

/-- Vertex type of a canonical disjoint union of cycles with the listed
lengths. -/
abbrev CycleUnionVerts : List ℕ → Type
  | [] => Empty
  | n :: ns => Fin n ⊕ CycleUnionVerts ns

instance cycleUnionVertsFinite (ns : List ℕ) : Finite (CycleUnionVerts ns) := by
  induction ns with
  | nil => simp only [CycleUnionVerts]; infer_instance
  | cons n ns ih => simp only [CycleUnionVerts]; infer_instance

/-- The canonical disjoint union of the cycle graphs whose lengths occur in
`ns`. -/
def cycleUnionGraph : (ns : List ℕ) → SimpleGraph (CycleUnionVerts ns)
  | [] => ⊥
  | n :: ns => SimpleGraph.cycleGraph n ⊕g cycleUnionGraph ns

@[simp] lemma natCard_cycleUnionVerts (ns : List ℕ) :
    Nat.card (CycleUnionVerts ns) = ns.sum := by
  induction ns with
  | nil => simp [CycleUnionVerts]
  | cons n ns ih => simp [CycleUnionVerts, ih]

@[simp] lemma indepNum_cycleUnionGraph (ns : List ℕ) :
    (cycleUnionGraph ns).indepNum =
      (ns.map fun n ↦ (SimpleGraph.cycleGraph n).indepNum).sum := by
  induction ns with
  | nil =>
      have h := indepNum_le_natCard (cycleUnionGraph [])
      simpa [cycleUnionGraph, CycleUnionVerts] using h
  | cons n ns ih =>
      simpa only [cycleUnionGraph, List.map_cons, List.sum_cons, ih] using
        indepNum_sum (SimpleGraph.cycleGraph n) (cycleUnionGraph ns)

/-- A canonical representation of `p` vertex-disjoint odd cycles in `G`:
the disjoint union of `p` odd cycle graphs occurs as a (not necessarily
induced) subgraph of `G`. -/
def HasOddCyclePacking {V : Type*} (p : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ ns : List ℕ,
    ns.length = p ∧
      (∀ n ∈ ns, 3 ≤ n ∧ Odd n) ∧
        cycleUnionGraph ns ⊑ G

/-- A labelled copy of one odd cycle in a host graph, retaining the cycle
length and its elementary arithmetic properties. -/
structure OddCycleCopyData {V : Type*} (G : SimpleGraph V) where
  length : ℕ
  three_le : 3 ≤ length
  odd_length : Odd length
  copy : SimpleGraph.Copy (SimpleGraph.cycleGraph length) G

namespace OddCycleCopyData

variable {V : Type*} {G : SimpleGraph V}

/-- The vertex support of a labelled cycle copy. -/
def support (c : OddCycleCopyData G) : Finset V :=
  Finset.univ.map c.copy.toEmbedding

@[simp] lemma card_support (c : OddCycleCopyData G) :
    c.support.card = c.length := by
  simp [support]

@[simp] lemma coe_support (c : OddCycleCopyData G) :
    (c.support : Set V) = Set.range c.copy := by
  ext v
  simp only [support, Finset.coe_map, Finset.coe_univ, Set.image_univ,
    Set.mem_range]
  rfl

/-- The union of the ranges of a list of labelled cycle copies. -/
def unionSupport : List (OddCycleCopyData G) → Set V
  | [] => ∅
  | c :: cs => Set.range c.copy ∪ unionSupport cs

lemma disjoint_unionSupport_of_forall (c : OddCycleCopyData G)
    {cs : List (OddCycleCopyData G)}
    (h : ∀ d ∈ cs, Disjoint (Set.range c.copy) (Set.range d.copy)) :
    Disjoint (Set.range c.copy) (unionSupport cs) := by
  induction cs with
  | nil => simp [unionSupport]
  | cons d ds ih =>
      rw [unionSupport, disjoint_union_right]
      exact ⟨h d (by simp), ih (fun e he => h e (by simp [he]))⟩

/-- Pairwise vertex-disjoint cycle copies combine into one copy of their
canonical disjoint-union graph. -/
lemma exists_cycleUnionCopy (cs : List (OddCycleCopyData G))
    (hcs : cs.Pairwise (Disjoint on fun c => Set.range c.copy)) :
    ∃ f : SimpleGraph.Copy
        (cycleUnionGraph (cs.map OddCycleCopyData.length)) G,
      Set.range f ⊆ unionSupport cs := by
  induction cs with
  | nil =>
      let e : CycleUnionVerts [] ↪ V :=
        Function.Embedding.mk (fun x => nomatch x) (by
          intro x y _
          exact nomatch x)
      refine ⟨SimpleGraph.Copy.bot e, ?_⟩
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact nomatch y
  | cons c cs ih =>
      rw [List.pairwise_cons] at hcs
      obtain ⟨f, hf⟩ := ih hcs.2
      have hcross : Disjoint (Set.range c.copy) (unionSupport cs) :=
        disjoint_unionSupport_of_forall c hcs.1
      let hom : SimpleGraph.cycleGraph c.length ⊕g
          cycleUnionGraph (cs.map OddCycleCopyData.length) →g G :=
        { toFun := Sum.elim c.copy f
          map_rel' := by
            rintro (x | x) (y | y) hxy
            · exact c.copy.toHom.map_adj (by simpa using hxy)
            · simp at hxy
            · simp at hxy
            · exact f.toHom.map_adj (by simpa using hxy) }
      have hinj : Function.Injective hom := by
        rintro (x | x) (y | y) hxy
        · exact congrArg Sum.inl (c.copy.injective hxy)
        · exfalso
          exact Set.disjoint_left.mp hcross ⟨x, rfl⟩ (hf ⟨y, hxy.symm⟩)
        · exfalso
          exact Set.disjoint_left.mp hcross ⟨y, rfl⟩ (hf ⟨x, hxy⟩)
        · exact congrArg Sum.inr (f.injective hxy)
      let copy : SimpleGraph.Copy
          (cycleUnionGraph ((c :: cs).map OddCycleCopyData.length)) G :=
        hom.toCopy hinj
      refine ⟨copy, ?_⟩
      rintro z ⟨u, rfl⟩
      cases u with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr (hf ⟨y, rfl⟩)

end OddCycleCopyData

/-- A pairwise vertex-disjoint list of labelled odd-cycle copies is exactly
a packing in the canonical representation used by `HasOddCyclePacking`. -/
theorem hasOddCyclePacking_of_pairwise_cycleCopies {V : Type*}
    {G : SimpleGraph V} (cs : List (OddCycleCopyData G))
    (hcs : cs.Pairwise (Disjoint on fun c => Set.range c.copy)) :
    HasOddCyclePacking cs.length G := by
  obtain ⟨f, _⟩ := OddCycleCopyData.exists_cycleUnionCopy cs hcs
  refine ⟨cs.map OddCycleCopyData.length, by simp, ?_, ⟨f⟩⟩
  intro n hn
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hn
  exact ⟨c.three_le, c.odd_length⟩

/-- A subgraph is a short odd cycle if it is isomorphic to an odd cycle of
length at most `L`. -/
def IsShortOddCycleSubgraph {V : Type*} {G : SimpleGraph V}
    (L : ℕ) (H : G.Subgraph) : Prop :=
  ∃ n : ℕ, n ≤ L ∧ 3 ≤ n ∧ Odd n ∧
    Nonempty (SimpleGraph.cycleGraph n ≃g H.coe)

/-- The finite hypergraph whose edges are the vertex sets of all odd-cycle
subgraphs of length at most `L`. -/
def shortOddCycleVertexSets {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : ℕ) : Finset (Finset V) :=
  ((Finset.univ : Finset G.Subgraph).filter
    (IsShortOddCycleSubgraph L)).image fun H => H.verts.toFinset

/-- A chosen labelled cycle copy certifying membership in the finite family
`shortOddCycleVertexSets`. -/
structure ShortOddCycleWitness {V : Type*} (G : SimpleGraph V)
    (L : ℕ) (A : Finset V) where
  data : OddCycleCopyData G
  length_le : data.length ≤ L
  support_eq : data.support = A

lemma exists_shortOddCycleWitness_of_mem {V : Type*} [Fintype V]
    {G : SimpleGraph V} {L : ℕ} {A : Finset V}
    (hA : A ∈ shortOddCycleVertexSets G L) :
    Nonempty (ShortOddCycleWitness G L A) := by
  rw [shortOddCycleVertexSets, Finset.mem_image] at hA
  obtain ⟨H, hH, rfl⟩ := hA
  have hshort := (Finset.mem_filter.mp hH).2
  obtain ⟨n, hnL, hn3, hnodd, ⟨e⟩⟩ := hshort
  let copy : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G :=
    ⟨H.hom.comp e.toHom, H.hom_injective.comp e.injective⟩
  let data : OddCycleCopyData G := ⟨n, hn3, hnodd, copy⟩
  refine ⟨⟨data, hnL, ?_⟩⟩
  ext v
  simp only [OddCycleCopyData.support, Finset.mem_map, Finset.mem_univ,
    true_and, Set.mem_toFinset]
  constructor
  · rintro ⟨x, rfl⟩
    exact (e x).property
  · intro hv
    obtain ⟨x, hx⟩ := e.surjective ⟨v, hv⟩
    exact ⟨x, Subtype.ext_iff.mp hx⟩

noncomputable def shortOddCycleWitnessOfMem {V : Type*} [Fintype V]
    {G : SimpleGraph V} {L : ℕ} {A : Finset V}
    (hA : A ∈ shortOddCycleVertexSets G L) :
    ShortOddCycleWitness G L A :=
  Classical.choice (exists_shortOddCycleWitness_of_mem hA)

lemma shortOddCycleVertexSets_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} {L : ℕ} {A : Finset V}
    (hA : A ∈ shortOddCycleVertexSets G L) : A.Nonempty := by
  let w := shortOddCycleWitnessOfMem hA
  have hcard : A.card = w.data.length := by
    calc
      A.card = w.data.support.card := congrArg Finset.card w.support_eq.symm
      _ = w.data.length := OddCycleCopyData.card_support w.data
  have hthree : 3 ≤ w.data.length := w.data.three_le
  exact Finset.card_pos.mp (by omega)

lemma shortOddCycleVertexSets_card_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {L : ℕ} {A : Finset V}
    (hA : A ∈ shortOddCycleVertexSets G L) : A.card ≤ L := by
  let w := shortOddCycleWitnessOfMem hA
  calc
    A.card = w.data.support.card := congrArg Finset.card w.support_eq.symm
    _ = w.data.length := OddCycleCopyData.card_support w.data
    _ ≤ L := w.length_le

/-- Pairwise-disjoint members of the bounded odd-cycle vertex family give a
canonical odd-cycle packing of the same cardinality. -/
theorem hasOddCyclePacking_of_disjoint_shortOddCycleVertexSets
    {V : Type*} [Fintype V] {G : SimpleGraph V} {L : ℕ}
    (P : Finset (Finset V))
    (hPF : P ⊆ shortOddCycleVertexSets G L)
    (hPdisj : (P : Set (Finset V)).PairwiseDisjoint id) :
    HasOddCyclePacking P.card G := by
  let w (A : {A // A ∈ P}) : ShortOddCycleWitness G L A :=
    shortOddCycleWitnessOfMem (hPF A.property)
  let d (A : {A // A ∈ P}) : OddCycleCopyData G := (w A).data
  let cs : List (OddCycleCopyData G) := P.attach.toList.map d
  have hattach : P.attach.toList.Pairwise (Disjoint on Subtype.val) := by
    apply List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint
    · simpa using hPdisj.attach
    · exact Finset.nodup_toList _
  have hcs : cs.Pairwise (Disjoint on fun c => Set.range c.copy) := by
    dsimp only [cs]
    rw [List.pairwise_map]
    apply hattach.imp
    intro A B hAB
    change Disjoint (Set.range (d A).copy) (Set.range (d B).copy)
    rw [← OddCycleCopyData.coe_support, ← OddCycleCopyData.coe_support,
      show (d A).support = A by exact (w A).support_eq,
      show (d B).support = B by exact (w B).support_eq]
    exact Finset.disjoint_coe.mpr hAB
  have hpack := hasOddCyclePacking_of_pairwise_cycleCopies cs hcs
  simpa [cs] using hpack

/-- A cycle graph of length at least three has exactly as many edges as
vertices. -/
lemma card_edgeFinset_cycleGraph {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).edgeFinset.card = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := (SimpleGraph.cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

/-- In a cycle of length at least three, an independent set contains at most
half of the vertices, rounded down. -/
lemma two_mul_card_le_of_cycleGraph_isIndepSet {n : ℕ} (hn : 3 ≤ n)
    (I : Finset (Fin n))
    (hI : (SimpleGraph.cycleGraph n).IsIndepSet (I : Set (Fin n))) :
    2 * I.card ≤ n := by
  let B := (SimpleGraph.cycleGraph n).between (I : Set (Fin n)) (I : Set (Fin n))ᶜ
  have hB : B.IsBipartiteWith (I : Set (Fin n)) (I : Set (Fin n))ᶜ :=
    SimpleGraph.between_isBipartiteWith disjoint_compl_right
  have hdegree (v : Fin n) (hv : v ∈ I) :
      B.degree v = (SimpleGraph.cycleGraph n).degree v := by
    apply congrArg Finset.card
    ext w
    simp only [SimpleGraph.mem_neighborFinset, B, SimpleGraph.between_adj]
    constructor
    · exact fun h ↦ h.1
    · intro hvw
      refine ⟨hvw, Or.inl ⟨hv, ?_⟩⟩
      intro hw
      exact hI hv hw hvw.ne hvw
  have hBfin : B.IsBipartiteWith (I : Set (Fin n)) (Iᶜ : Finset (Fin n)) := by
    simpa only [Finset.coe_compl] using hB
  have hsum : (∑ v ∈ I, B.degree v) = B.edgeFinset.card := by
    exact SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hBfin
  have hBle : B.edgeFinset.card ≤ (SimpleGraph.cycleGraph n).edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono SimpleGraph.between_le)
  have hcycleDegree (v : Fin n) : (SimpleGraph.cycleGraph n).degree v = 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  calc
    2 * I.card = ∑ v ∈ I, (SimpleGraph.cycleGraph n).degree v := by
      simp [hcycleDegree, Nat.mul_comm]
    _ = ∑ v ∈ I, B.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (hdegree v hv).symm
    _ = B.edgeFinset.card := hsum
    _ ≤ (SimpleGraph.cycleGraph n).edgeFinset.card := hBle
    _ = n := card_edgeFinset_cycleGraph hn

/-- Graph isomorphisms transport independent sets. -/
lemma isIndepSet_image_iso_iff {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (s : Set V) :
    H.IsIndepSet (e '' s) ↔ G.IsIndepSet s := by
  constructor
  · intro h v hv w hw hvw hadj
    exact h ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
      (fun he ↦ hvw (e.injective he)) (e.map_rel_iff.mpr hadj)
  · rintro h _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hvw hadj
    exact h hv hw (fun he ↦ hvw (congrArg e he)) (e.map_rel_iff.mp hadj)

/-- The independence number is invariant under graph isomorphism. -/
lemma indepNum_eq_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    G.indepNum = H.indepNum := by
  apply Nat.le_antisymm
  · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hmap : H.IsIndepSet (I.map e.toEquiv.toEmbedding : Finset W) := by
      intro x hx y hy hxy hadj
      change x ∈ I.map e.toEquiv.toEmbedding at hx
      change y ∈ I.map e.toEquiv.toEmbedding at hy
      rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨w, hw, rfl⟩
      exact hI.isIndepSet hv hw
        (fun hvw ↦ hxy (congrArg e hvw)) (e.map_rel_iff.mp hadj)
    simpa only [Finset.card_map, hI.card_eq] using hmap.card_le_indepNum
  · obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
    have hmap : G.IsIndepSet (I.map e.symm.toEquiv.toEmbedding : Finset V) := by
      intro x hx y hy hxy hadj
      change x ∈ I.map e.symm.toEquiv.toEmbedding at hx
      change y ∈ I.map e.symm.toEquiv.toEmbedding at hy
      rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨w, hw, rfl⟩
      exact hI.isIndepSet hv hw
        (fun hvw ↦ hxy (congrArg e.symm hvw)) (e.symm.map_rel_iff.mp hadj)
    simpa only [Finset.card_map, hI.card_eq] using hmap.card_le_indepNum

/-- The hereditary independence hypothesis is transported by graph
isomorphisms. -/
lemma everySubgraphHasLargeIndepSet_of_iso
    {V W : Type*} [Finite V] [Finite W] {k : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (hG : EverySubgraphHasLargeIndepSet k G) :
    EverySubgraphHasLargeIndepSet k H := by
  intro K
  let L : G.Subgraph := K.map e.symm.toHom
  let eK : K.coe ≃g L.coe := e.symm.toCopy.isoSubgraphMap K
  have hverts : L.verts.ncard = K.verts.ncard := by
    dsimp only [L]
    rw [SimpleGraph.Subgraph.map_verts]
    exact Set.ncard_image_of_injective K.verts e.symm.injective
  have hindep : K.coe.indepNum = L.coe.indepNum :=
    indepNum_eq_of_iso eK
  calc
    K.verts.ncard = L.verts.ncard := hverts.symm
    _ ≤ 2 * L.coe.indepNum + k := hG L
    _ = 2 * K.coe.indepNum + k := by rw [hindep]

/-- Bipartiteness is invariant under graph isomorphism. -/
lemma isBipartite_of_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (hG : G.IsBipartite) :
    H.IsBipartite := by
  exact ⟨hG.some.comp e.symm.toHom⟩

/-- A bounded vertex deletion leaving a bipartite graph is transported by a
graph isomorphism, with exactly the same bound. -/
lemma bipartiteAfterDeletingAtMost_of_iso
    {V W : Type*} {C : ℕ} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : BipartiteAfterDeletingAtMost C G) :
    BipartiteAfterDeletingAtMost C H := by
  obtain ⟨X, hXC, hX⟩ := hG
  let Y : Finset W := X.map e.toEquiv.toEmbedding
  refine ⟨Y, ?_, ?_⟩
  · simpa only [Y, Finset.card_map] using hXC
  · have hbij : Set.BijOn e ((X : Set V)ᶜ) ((Y : Set W)ᶜ) := by
      change Set.BijOn e.toEquiv ((X : Set V)ᶜ) ((Y : Set W)ᶜ)
      rw [show (Y : Set W) = e.toEquiv '' (X : Set V) by
        ext w
        simp [Y]]
      rw [← e.toEquiv.image_compl]
      exact e.toEquiv.bijOn_image
    exact isBipartite_of_iso (e.induce hbij) hX

/-- The `Fin n` normalization in `Problem73` is equivalent to quantifying
over all finite vertex types. -/
theorem problem73_iff_generalProblem73 : Problem73 ↔ GeneralProblem73 := by
  constructor
  · intro h k
    obtain ⟨C, hC⟩ := h k
    refine ⟨C, ?_⟩
    intro V _ G hG
    let _ := Fintype.ofFinite V
    let H : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
    let e : G ≃g H := G.overFinIso rfl
    have hH : EverySubgraphHasLargeIndepSet k H :=
      everySubgraphHasLargeIndepSet_of_iso e hG
    have hout := hC (Fintype.card V) H hH
    exact bipartiteAfterDeletingAtMost_of_iso e.symm hout
  · intro h k
    obtain ⟨C, hC⟩ := h k
    exact ⟨C, fun n G hG ↦ hC (Fin n) G hG⟩

/-- The independence number of a cycle of length at least three is at most
half its length. -/
lemma two_mul_indepNum_cycleGraph_le {n : ℕ} (hn : 3 ≤ n) :
    2 * (SimpleGraph.cycleGraph n).indepNum ≤ n := by
  obtain ⟨I, hI⟩ :=
    (SimpleGraph.cycleGraph n).exists_isNIndepSet_indepNum
  simpa only [hI.card_eq] using
    two_mul_card_le_of_cycleGraph_isIndepSet hn I hI.isIndepSet

/-- An odd cycle has independence deficit at least one. -/
lemma two_mul_indepNum_cycleGraph_add_one_le {n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) :
    2 * (SimpleGraph.cycleGraph n).indepNum + 1 ≤ n := by
  have hle := two_mul_indepNum_cycleGraph_le hn
  have hne : 2 * (SimpleGraph.cycleGraph n).indepNum ≠ n := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (heq ▸ even_two_mul (SimpleGraph.cycleGraph n).indepNum)
  omega

/-- Vertex-disjoint copies combine into a copy of the disjoint graph sum. -/
def sumCopyOfDisjointRanges {A B V : Type*}
    {F : SimpleGraph A} {H : SimpleGraph B} {G : SimpleGraph V}
    (f : SimpleGraph.Copy F G) (g : SimpleGraph.Copy H G)
    (hfg : Disjoint (Set.range f) (Set.range g)) :
    SimpleGraph.Copy (F ⊕g H) G := by
  let hom : F ⊕g H →g G :=
    { toFun := Sum.elim f g
      map_rel' := by
        rintro (x | x) (y | y) hxy
        · exact f.toHom.map_adj (by simpa using hxy)
        · simp at hxy
        · simp at hxy
        · exact g.toHom.map_adj (by simpa using hxy) }
  refine hom.toCopy ?_
  rintro (x | x) (y | y) hxy
  · exact congrArg Sum.inl (f.injective hxy)
  · exfalso
    exact Set.disjoint_left.mp hfg ⟨x, rfl⟩ ⟨y, hxy.symm⟩
  · exfalso
    exact Set.disjoint_left.mp hfg ⟨y, rfl⟩ ⟨x, hxy⟩
  · exact congrArg Sum.inr (g.injective hxy)

/-- Removing the vertices of one odd cycle lowers the hereditary
independence-defect parameter by one.  For an arbitrary subgraph outside the
cycle, take its edge-disjoint union with the cycle as a subgraph of the
original graph; the odd cycle contributes at least one unit of defect. -/
theorem everySubgraphHasLargeIndepSet_induce_compl_oddCycle
    {V : Type*} [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hG : EverySubgraphHasLargeIndepSet (k + 1) G)
    (c : OddCycleCopyData G) :
    EverySubgraphHasLargeIndepSet k
      (G.induce (Set.range c.copy)ᶜ) := by
  intro H
  let rcopy : SimpleGraph.Copy H.coe G :=
    (SimpleGraph.Copy.induce G (Set.range c.copy)ᶜ).comp H.coeCopy
  have hdisj : Disjoint (Set.range c.copy) (Set.range rcopy) := by
    rw [Set.disjoint_left]
    intro v hvC hvR
    obtain ⟨x, rfl⟩ := hvR
    exact (H.hom x).property hvC
  let f : SimpleGraph.Copy
      (SimpleGraph.cycleGraph c.length ⊕g H.coe) G :=
    sumCopyOfDisjointRanges c.copy rcopy hdisj
  let K : G.Subgraph := f.toSubgraph
  let e : SimpleGraph.cycleGraph c.length ⊕g H.coe ≃g K.coe :=
    f.isoToSubgraph
  have hverts : K.verts.ncard = c.length + H.verts.ncard := by
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card K.verts = Nat.card (Fin c.length ⊕ H.verts) :=
        (Nat.card_congr e.toEquiv).symm
      _ = c.length + H.verts.ncard := by
        rw [Nat.card_sum, Nat.card_fin, Nat.card_coe_set_eq]
  have hindep : K.coe.indepNum =
      (SimpleGraph.cycleGraph c.length).indepNum + H.coe.indepNum := by
    rw [← indepNum_sum]
    exact (indepNum_eq_of_iso e).symm
  have hcycle := two_mul_indepNum_cycleGraph_add_one_le
    c.three_le c.odd_length
  have hbound := hG K
  rw [hverts, hindep] at hbound
  omega

/-- The vertex set of the subgraph associated with a graph copy is exactly
the range of the copy's vertex embedding. -/
lemma verts_copy_toSubgraph {A V : Type*} {F : SimpleGraph A}
    {G : SimpleGraph V} (f : SimpleGraph.Copy F G) :
    f.toSubgraph.verts = Set.range f := by
  simp [SimpleGraph.Copy.toSubgraph, SimpleGraph.Subgraph.map_verts]

/-- A subgraph whose coercion is isomorphic to an odd cycle. -/
def IsOddCycleSubgraph {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Odd n ∧
    Nonempty (SimpleGraph.cycleGraph n ≃g H.coe)

/-- Odd-cycle subgraphs remain odd-cycle subgraphs when mapped along a graph
embedding. -/
lemma IsOddCycleSubgraph.map_embedding
    {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}
    {H : G.Subgraph} (hH : IsOddCycleSubgraph H) (f : G ↪g G') :
    IsOddCycleSubgraph (H.map f.toHom) := by
  obtain ⟨n, hn3, hnodd, ⟨e⟩⟩ := hH
  exact ⟨n, hn3, hnodd,
    ⟨(f.toCopy.isoSubgraphMap H).comp e⟩⟩

/-- The ambient graph induced by the vertices of an odd-cycle subgraph is
connected.  Extra chords can only add reachability. -/
lemma IsOddCycleSubgraph.connected_induce_verts
    {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) :
    (G.induce H.verts).Connected := by
  obtain ⟨n, hn3, -, ⟨e⟩⟩ := hH
  have hcycle : (SimpleGraph.cycleGraph n).Connected := by
    have h := (SimpleGraph.cycleGraph_connected (n := n - 1))
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
    exact h
  have hcoe : H.coe.Connected := (e.connected_iff).mp hcycle
  have hinduced := hcoe.mono (coe_le_induce_verts H)
  simpa only [SimpleGraph.induce_eq_coe_induce_top] using hinduced

lemma IsOddCycleSubgraph.verts_nonempty
    {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) : H.verts.Nonempty := by
  obtain ⟨n, hn3, -, ⟨e⟩⟩ := hH
  let i : Fin n := ⟨0, by omega⟩
  exact ⟨(e i).1, (e i).2⟩

/-- Choose the labelled cycle copy carried by an odd-cycle subgraph.  This
forgets no vertex information: the range of the chosen copy is exactly the
vertex set of the subgraph. -/
noncomputable def IsOddCycleSubgraph.toCopyData
    {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) : OddCycleCopyData G := by
  choose n hn3 hnodd e using hH
  exact ⟨n, hn3, hnodd, H.coeCopy.comp e.some.toCopy⟩

@[simp] lemma IsOddCycleSubgraph.range_toCopyData
    {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) :
    Set.range hH.toCopyData.copy = H.verts := by
  classical
  unfold IsOddCycleSubgraph.toCopyData
  simp only [SimpleGraph.Copy.comp_apply]
  ext v
  simp
  constructor
  · rintro ⟨a, b, rfl⟩
    exact b
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Pairwise vertex-disjoint odd-cycle subgraphs give an integral odd-cycle
packing.  This is the subgraph-level counterpart of
`hasOddCyclePacking_of_pairwise_cycleCopies` and is the convenient endpoint
for clique-minor and wall routing arguments. -/
theorem hasOddCyclePacking_of_pairwise_oddCycleSubgraphs
    {V : Type*} {G : SimpleGraph V} (cs : List G.Subgraph)
    (hodd : ∀ H ∈ cs, IsOddCycleSubgraph H)
    (hdisj : cs.Pairwise (Disjoint on SimpleGraph.Subgraph.verts)) :
    HasOddCyclePacking cs.length G := by
  let data (H : G.Subgraph) (hH : H ∈ cs) : OddCycleCopyData G :=
    (hodd H hH).toCopyData
  let ds : List (OddCycleCopyData G) :=
    cs.pmap data (fun H hH ↦ hH)
  have hpair : ds.Pairwise (Disjoint on fun c ↦ Set.range c.copy) := by
    dsimp only [ds]
    rw [List.pairwise_pmap]
    apply hdisj.imp
    intro H K hHK hHmem hKmem
    change Disjoint (Set.range (data H hHmem).copy)
      (Set.range (data K hKmem).copy)
    rw [IsOddCycleSubgraph.range_toCopyData,
      IsOddCycleSubgraph.range_toCopyData]
    exact hHK
  have hpack := hasOddCyclePacking_of_pairwise_cycleCopies ds hpair
  simpa [ds] using hpack

/-- A finite vertex set meets every odd-cycle subgraph of the host graph. -/
def MeetsEveryOddCycleSubgraph {V : Type*} [Fintype V]
    (X : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, IsOddCycleSubgraph H →
    ¬ Disjoint H.verts.toFinset X

/-- A bipartite graph has no odd cycle length. -/
lemma oddCycleLengths_eq_empty_of_bipartite {V : Type*}
    {G : SimpleGraph V} (hG : G.IsBipartite) :
    Erdos58.oddCycleLengths G = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro n ⟨hnodd, v, c, hc, rfl⟩
  have heven : Even c.length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) v c
  exact (Nat.not_even_iff_odd.mpr hnodd) heven

/-- Exact equivalence between the deletion formulation and the transversal
formulation: the complementary induced graph is bipartite precisely when the
deleted finset meets every odd-cycle subgraph. -/
theorem bipartite_induce_compl_iff_meetsEveryOddCycleSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) (X : Finset V) :
    (G.induce (X : Set V)ᶜ).IsBipartite ↔
      MeetsEveryOddCycleSubgraph X G := by
  constructor
  · intro hbip H hH hdisj
    obtain ⟨n, hn3, hnodd, ⟨e⟩⟩ := hH
    let hom : H.coe →g G.induce (X : Set V)ᶜ :=
      { toFun := fun v ↦ ⟨v.1, by
          intro hvX
          exact Finset.disjoint_left.mp hdisj
            (Set.mem_toFinset.mpr v.2) hvX⟩
        map_rel' := by
          intro v w hadj
          exact H.adj_sub hadj }
    have hinj : Function.Injective hom := by
      intro v w hvw
      apply Subtype.ext
      change (⟨v.1, _⟩ : {x : V // x ∈ (X : Set V)ᶜ}) =
        ⟨w.1, _⟩ at hvw
      exact congrArg (fun z : {x : V // x ∈ (X : Set V)ᶜ} ↦ z.1) hvw
    let f : SimpleGraph.Copy (SimpleGraph.cycleGraph n)
        (G.induce (X : Set V)ᶜ) := (hom.toCopy hinj).comp e.toCopy
    have hnmem : n ∈ Erdos58.oddCycleLengths
        (G.induce (X : Set V)ᶜ) :=
      (Erdos58.mem_oddCycleLengths_iff_cycleGraph_isContained hn3).2
        ⟨hnodd, ⟨f⟩⟩
    have hempty := oddCycleLengths_eq_empty_of_bipartite hbip
    simpa [hempty] using hnmem
  · intro hmeet
    apply Erdos58.colorable_two_of_oddCycleLengths_eq_empty
    rw [Set.eq_empty_iff_forall_notMem]
    intro n hn
    have hn3 : 3 ≤ n := Erdos58.three_le_of_mem_oddCycleLengths hn
    have hnodd : Odd n := Erdos58.odd_of_mem_oddCycleLengths hn
    have hcontained : SimpleGraph.cycleGraph n ⊑
        G.induce (X : Set V)ᶜ :=
      ((Erdos58.mem_oddCycleLengths_iff_cycleGraph_isContained hn3).1 hn).2
    let f₀ : SimpleGraph.Copy (SimpleGraph.cycleGraph n)
        (G.induce (X : Set V)ᶜ) := hcontained.some
    let f : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G :=
      (SimpleGraph.Copy.induce G (X : Set V)ᶜ).comp f₀
    let H : G.Subgraph := f.toSubgraph
    have hHodd : IsOddCycleSubgraph H :=
      ⟨n, hn3, hnodd, ⟨f.isoToSubgraph⟩⟩
    apply hmeet H hHodd
    rw [Finset.disjoint_left]
    intro v hvH hvX
    have hvRange : v ∈ Set.range f := by
      rw [← verts_copy_toSubgraph f]
      exact Set.mem_toFinset.mp hvH
    obtain ⟨u, rfl⟩ := hvRange
    exact (f₀ u).2 hvX

/-- A finite graph is bipartite exactly when it has no subgraph which is an
odd cycle.  This is the subgraph-copy form of the standard odd-cycle
characterization and is convenient when orienting separations. -/
theorem isBipartite_iff_no_oddCycleSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsBipartite ↔ ¬ ∃ H : G.Subgraph, IsOddCycleSubgraph H := by
  constructor
  · intro hbip
    have hzero : BipartiteAfterDeletingAtMost 0 G :=
      (bipartiteAfterDeletingAtMost_zero_iff G).2 hbip
    obtain ⟨X, hXcard, hcomp⟩ := hzero
    have hX : X = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hXcard)
    subst X
    have hmeet :=
      (bipartite_induce_compl_iff_meetsEveryOddCycleSubgraph G ∅).1 hcomp
    rintro ⟨H, hH⟩
    exact hmeet H hH (by simp)
  · intro hno
    apply (bipartiteAfterDeletingAtMost_zero_iff G).1
    refine ⟨∅, by simp, ?_⟩
    apply (bipartite_induce_compl_iff_meetsEveryOddCycleSubgraph G ∅).2
    intro H hH _
    exact hno ⟨H, hH⟩

/-- Along a connected two-coloured graph, two proper two-colourings either
agree everywhere or disagree everywhere. -/
lemma coloring_two_agreement_of_reachable
    {V : Type*} {G : SimpleGraph V}
    (c d : G.Coloring (Fin 2)) {u v : V} (huv : G.Reachable u v) :
    (c u = d u ↔ c v = d v) := by
  have edge_agreement {x y : V} (hxy : G.Adj x y) :
      (c x = d x ↔ c y = d y) := by
    have hc : c x ≠ c y := by simpa using c.map_rel hxy
    have hd : d x ≠ d y := by simpa using d.map_rel hxy
    constructor
    · intro h
      apply Fin.ext
      have hval := congrArg Fin.val h
      have hcval : (c x).val ≠ (c y).val := fun e ↦ hc (Fin.ext e)
      have hdval : (d x).val ≠ (d y).val := fun e ↦ hd (Fin.ext e)
      omega
    · intro h
      apply Fin.ext
      have hval := congrArg Fin.val h
      have hcval : (c x).val ≠ (c y).val := fun e ↦ hc (Fin.ext e)
      have hdval : (d x).val ≠ (d y).val := fun e ↦ hd (Fin.ext e)
      omega
  obtain ⟨w⟩ := huv
  induction w with
  | nil => rfl
  | @cons x y z hxy p ih => exact (edge_agreement hxy).trans ih

/-- If two distinct elements of `Fin 2` are compared with the same reference
colour, exactly one comparison is an equality. -/
lemma fin_two_eq_iff_not_eq_of_ne {a b r : Fin 2} (hab : a ≠ b) :
    (a = r ↔ ¬ b = r) := by
  constructor
  · intro har hbr
    exact hab (har.trans hbr.symm)
  · intro hbr
    apply Fin.ext
    have habval : a.val ≠ b.val := fun e ↦ hab (Fin.ext e)
    have hbrval : b.val ≠ r.val := fun e ↦ hbr (Fin.ext e)
    omega

/-- A collection of pairwise vertex-disjoint regions whose induced graphs
are all non-bipartite.  Odd clique-minor and wall-routing arguments naturally
produce this certificate before choosing a particular odd cycle in each
region. -/
structure DisjointNonbipartiteRegions {V : Type*} [Fintype V]
    (p : ℕ) (G : SimpleGraph V) where
  region : Fin p → Finset V
  pairwise_disjoint : ∀ i j, i ≠ j → Disjoint (region i) (region j)
  nonbipartite : ∀ i, ¬ (G.induce (region i : Set V)).IsBipartite

/-- Pairwise-disjoint non-bipartite induced regions contain pairwise-disjoint
odd cycles, hence give the canonical integral packing used in this file. -/
theorem DisjointNonbipartiteRegions.hasOddCyclePacking
    {V : Type*} [Fintype V] {p : ℕ} {G : SimpleGraph V}
    (M : DisjointNonbipartiteRegions p G) : HasOddCyclePacking p G := by
  have hex (i : Fin p) :
      ∃ H : (G.induce (M.region i : Set V)).Subgraph,
        IsOddCycleSubgraph H := by
    apply Classical.byContradiction
    intro hno
    exact M.nonbipartite i
      ((isBipartite_iff_no_oddCycleSubgraph _).2 hno)
  choose H hHodd using hex
  let f (i : Fin p) : G.induce (M.region i : Set V) ↪g G :=
    SimpleGraph.Embedding.induce (M.region i : Set V)
  let K (i : Fin p) : G.Subgraph := (H i).map (f i).toHom
  have hKodd (i : Fin p) : IsOddCycleSubgraph (K i) :=
    (hHodd i).map_embedding (f i)
  have hKsubset (i : Fin p) : (K i).verts ⊆ (M.region i : Set V) := by
    rintro v ⟨u, -, huv⟩
    rw [← huv]
    exact u.property
  have hpair : (List.ofFn K).Pairwise
      (Disjoint on SimpleGraph.Subgraph.verts) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    change Disjoint (K i).verts (K j).verts
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hd : Disjoint (M.region i : Set V) (M.region j : Set V) :=
      Finset.disjoint_coe.mpr (M.pairwise_disjoint i j (ne_of_lt hij))
    exact Set.disjoint_left.mp hd (hKsubset i hvi) (hKsubset j hvj)
  have hpack := hasOddCyclePacking_of_pairwise_oddCycleSubgraphs
    (List.ofFn K) (by
      intro L hL
      rw [List.mem_ofFn'] at hL
      obtain ⟨i, rfl⟩ := hL
      exact hKodd i) hpair
  simpa using hpack

/-- The parity consequence of an odd clique-minor, grouped into `p`
triples of branch sets.  In a conventional odd-minor model, the branch sets
are connected and properly two-coloured and every inter-branch link joins
equal colours; the three links belonging to one triple then form an odd
cycle after routing through the branch sets.  The present certificate keeps
exactly that consequence, which is what the packing argument consumes. -/
structure OddCliqueTripleCycleModel {V : Type*} [Fintype V]
    (p : ℕ) (G : SimpleGraph V) where
  branch : Fin p → Fin 3 → Finset V
  pairwise_disjoint : ∀ i a j b, (i, a) ≠ (j, b) →
    Disjoint (branch i a) (branch j b)
  triple_nonbipartite : ∀ i,
    ¬ (G.induce (((Finset.univ : Finset (Fin 3)).biUnion
      (branch i) : Finset V) : Set V)).IsBipartite

namespace OddCliqueTripleCycleModel

variable {V : Type*} [Fintype V] {p : ℕ} {G : SimpleGraph V}

/-- The union of the three branch sets assigned to one prospective odd
cycle. -/
def tripleSupport (M : OddCliqueTripleCycleModel p G) (i : Fin p) :
    Finset V :=
  (Finset.univ : Finset (Fin 3)).biUnion (M.branch i)

lemma tripleSupport_pairwise_disjoint
    (M : OddCliqueTripleCycleModel p G) {i j : Fin p} (hij : i ≠ j) :
    Disjoint (M.tripleSupport i) (M.tripleSupport j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  simp only [tripleSupport, Finset.mem_biUnion, Finset.mem_univ, true_and] at hvi hvj
  obtain ⟨a, hva⟩ := hvi
  obtain ⟨b, hvb⟩ := hvj
  have hpairs : (i, a) ≠ (j, b) := by
    intro h
    exact hij (congrArg Prod.fst h)
  exact Finset.disjoint_left.mp (M.pairwise_disjoint i a j b hpairs) hva hvb

/-- Forgetting the three-way branch decomposition leaves pairwise-disjoint
non-bipartite regions. -/
def toDisjointNonbipartiteRegions
    (M : OddCliqueTripleCycleModel p G) :
    DisjointNonbipartiteRegions p G where
  region := M.tripleSupport
  pairwise_disjoint := fun _ _ hij ↦ M.tripleSupport_pairwise_disjoint hij
  nonbipartite := by
    intro i
    exact M.triple_nonbipartite i

/-- An odd clique-minor certificate on `3p` branch sets contains `p`
vertex-disjoint odd cycles. -/
theorem hasOddCyclePacking (M : OddCliqueTripleCycleModel p G) :
    HasOddCyclePacking p G :=
  M.toDisjointNonbipartiteRegions.hasOddCyclePacking

end OddCliqueTripleCycleModel

/-- A conventional odd-minor model, already grouped into triples.  Branch
sets are nonempty, connected, pairwise disjoint, and properly two-coloured;
the link between any two branches in one triple joins vertices of the same
model colour.  This is the usual parity definition of an odd clique minor,
specialized to the `3p` branches needed for an odd-cycle packing of size
`p`. -/
structure OddCliqueTripleMinorModel {V : Type*} [Fintype V]
    (p : ℕ) (G : SimpleGraph V) where
  branch : Fin p → Fin 3 → Finset V
  pairwise_disjoint : ∀ i a j b, (i, a) ≠ (j, b) →
    Disjoint (branch i a) (branch j b)
  branch_nonempty : ∀ i a, (branch i a).Nonempty
  branch_connected : ∀ i a,
    (G.induce (branch i a : Set V)).Connected
  color : V → Fin 2
  color_ne_of_adj : ∀ i a {u v : V}, u ∈ branch i a → v ∈ branch i a →
    G.Adj u v → color u ≠ color v
  link : ∀ i {a b : Fin 3}, a ≠ b →
    ∃ u ∈ branch i a, ∃ v ∈ branch i b,
      G.Adj u v ∧ color u = color v

namespace OddCliqueTripleMinorModel

variable {V : Type*} [Fintype V] {p : ℕ} {G : SimpleGraph V}

/-- The parity condition in a conventional odd-minor model makes the union
of every three grouped branches non-bipartite.  If a two-colouring of that
union existed, its agreement status with the model colouring would be
constant on each connected branch.  A same-colour link forces the statuses
of its two branches to be opposite, which is impossible for all three pairs
of a triangle. -/
noncomputable def toCycleModel (M : OddCliqueTripleMinorModel p G) :
    OddCliqueTripleCycleModel p G where
  branch := M.branch
  pairwise_disjoint := M.pairwise_disjoint
  triple_nonbipartite := by
    classical
    intro i hbip
    let support : Finset V :=
      (Finset.univ : Finset (Fin 3)).biUnion (M.branch i)
    have hbip' : Nonempty ((G.induce (support : Set V)).Coloring (Fin 2)) := by
      change Nonempty ((G.induce
        ((Finset.univ : Finset (Fin 3)).biUnion (M.branch i) : Set V)).Coloring
          (Fin 2)) at hbip
      simpa [support] using hbip
    let c : (G.induce (support : Set V)).Coloring (Fin 2) :=
      Classical.choice hbip'
    let incl (a : Fin 3) (u : {v // v ∈ M.branch i a}) :
        {v // v ∈ support} :=
      ⟨u.1, by
        simpa [support] using
          (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, u.2⟩)⟩
    let cBranch (a : Fin 3) :
        (G.induce (M.branch i a : Set V)).Coloring (Fin 2) :=
      SimpleGraph.Coloring.mk (fun u ↦ c (incl a u)) (by
        intro u v huv
        apply c.map_rel
        change G.Adj u.1 v.1
        exact huv)
    let dBranch (a : Fin 3) :
        (G.induce (M.branch i a : Set V)).Coloring (Fin 2) :=
      SimpleGraph.Coloring.mk (fun u ↦ M.color u.1) (by
        intro u v huv
        exact M.color_ne_of_adj i a u.2 v.2 huv)
    choose root hroot using M.branch_nonempty i
    let rootVertex (a : Fin 3) : {v // v ∈ M.branch i a} :=
      ⟨root a, hroot a⟩
    let status (a : Fin 3) : Prop :=
      cBranch a (rootVertex a) = dBranch a (rootVertex a)
    have status_at (a : Fin 3) (u : {v // v ∈ M.branch i a}) :
        status a ↔ cBranch a u = dBranch a u := by
      exact coloring_two_agreement_of_reachable (cBranch a) (dBranch a)
        ((M.branch_connected i a) (rootVertex a) u)
    have status_opposite {a b : Fin 3} (hab : a ≠ b) :
        status a ↔ ¬ status b := by
      obtain ⟨u, hu, v, hv, huv, hcolor⟩ := M.link i hab
      let uB : {x // x ∈ M.branch i a} := ⟨u, hu⟩
      let vB : {x // x ∈ M.branch i b} := ⟨v, hv⟩
      have hcne : cBranch a uB ≠ cBranch b vB := by
        apply c.map_rel
        change G.Adj u v
        exact huv
      have hstatusValues :
          (cBranch a uB = dBranch a uB) ↔
            ¬ (cBranch b vB = dBranch b vB) := by
        change c (incl a uB) = M.color u ↔
          ¬ c (incl b vB) = M.color v
        rw [hcolor]
        exact fin_two_eq_iff_not_eq_of_ne hcne
      exact (status_at a uB).trans
        (hstatusValues.trans (not_congr (status_at b vB).symm))
    have h01 := status_opposite (a := (0 : Fin 3)) (b := (1 : Fin 3))
      (by decide)
    have h12 := status_opposite (a := (1 : Fin 3)) (b := (2 : Fin 3))
      (by decide)
    have h02 := status_opposite (a := (0 : Fin 3)) (b := (2 : Fin 3))
      (by decide)
    tauto

/-- A conventional odd `K_{3p}` minor model contains `p` vertex-disjoint
odd cycles. -/
theorem hasOddCyclePacking (M : OddCliqueTripleMinorModel p G) :
    HasOddCyclePacking p G :=
  M.toCycleModel.hasOddCyclePacking

end OddCliqueTripleMinorModel

/-- The vertices in one component of the graph induced outside `Z`, viewed
back in the original vertex type. -/
def componentVertexSet {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) : Set V :=
  Subtype.val '' c.supp

/-- Finset form of `componentVertexSet`. -/
def componentVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) : Finset V :=
  (componentVertexSet G Z c).toFinset

/-- Forgetting the proof that a vertex avoids `Z` identifies a component of
`G - Z` with the corresponding induced graph on original vertices. -/
def componentIso {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) :
    c.toSimpleGraph ≃g G.induce (componentVertexSet G Z c) where
  toEquiv := Equiv.Set.image Subtype.val c.supp Subtype.val_injective
  map_rel_iff' := by rfl

@[simp]
lemma coe_componentVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) :
    (componentVertices G Z c : Set V) = componentVertexSet G Z c := by
  simp [componentVertices]

lemma componentVertices_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) :
    (G.induce (componentVertices G Z c : Set V)).Connected := by
  rw [coe_componentVertices]
  exact (componentIso G Z c).connected_iff.mp c.connected_toSimpleGraph

/-- The external open neighborhood of a finite vertex set. -/
def externalNeighborhood {V : Type*} [Fintype V] (G : SimpleGraph V)
    (T : Finset V) : Finset V :=
  Finset.univ.filter fun v ↦ v ∉ T ∧ ∃ t ∈ T, G.Adj v t

lemma mem_externalNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) (v : V) :
    v ∈ externalNeighborhood G T ↔
      v ∉ T ∧ ∃ t ∈ T, G.Adj v t := by
  simp [externalNeighborhood]

lemma componentVertices_disjoint_delete {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) :
    Disjoint (componentVertices G Z c) Z := by
  rw [Finset.disjoint_left]
  intro v hvT hvZ
  change v ∈ (componentVertices G Z c : Set V) at hvT
  rw [coe_componentVertices] at hvT
  obtain ⟨w, hwc, hwv⟩ := hvT
  subst v
  exact w.2 hvZ

/-- A component of `G - Z` can have no external neighbor outside `Z`. -/
lemma component_externalNeighborhood_subset_delete
    {V : Type*} [Fintype V] (G : SimpleGraph V) (Z : Finset V)
    (c : (G.induce (Z : Set V)ᶜ).ConnectedComponent) :
    externalNeighborhood G (componentVertices G Z c) ⊆ Z := by
  intro v hvN
  rw [mem_externalNeighborhood] at hvN
  by_contra hvZ
  obtain ⟨t, htT, hvt⟩ := hvN.2
  change t ∈ (componentVertices G Z c : Set V) at htT
  rw [coe_componentVertices] at htT
  obtain ⟨w, hwc, hwt⟩ := htT
  subst t
  let v' : {x : V // x ∈ (Z : Set V)ᶜ} := ⟨v, hvZ⟩
  have hadj : (G.induce (Z : Set V)ᶜ).Adj v' w := hvt
  have hvc : v' ∈ c.supp :=
    (c.mem_supp_congr_adj hadj).mpr hwc
  apply hvN.1
  change v ∈ (componentVertices G Z c : Set V)
  rw [coe_componentVertices]
  exact ⟨v', hvc, rfl⟩

lemma externalNeighborhood_disjoint {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) :
    Disjoint (externalNeighborhood G T) T := by
  rw [Finset.disjoint_left]
  intro v hvN hvT
  exact (mem_externalNeighborhood G T v).mp hvN |>.1 hvT

/-- The component side `T`, its external neighborhood, and everything else
form the canonical tight separation used in the bramble construction. -/
lemma separation_externalNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) :
    IsVertexSeparation G (Finset.univ \ T)
      (T ∪ externalNeighborhood G T) := by
  constructor
  · ext v
    by_cases hvT : v ∈ T <;> simp [hvT]
  · intro a b haA haB hbB hbA hab
    have hbT : b ∈ T := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hbA
      exact Classical.byContradiction fun hbT ↦ hbA hbT
    have haT : a ∉ T := (Finset.mem_sdiff.mp haA).2
    have haN : a ∉ externalNeighborhood G T := by
      intro haN
      exact haB (Finset.mem_union_right T haN)
    exact haN ((mem_externalNeighborhood G T a).2
      ⟨haT, b, hbT, hab⟩)

@[simp]
lemma inter_externalNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) :
    (Finset.univ \ T) ∩ (T ∪ externalNeighborhood G T) =
      externalNeighborhood G T := by
  ext v
  by_cases hvT : v ∈ T <;> simp [mem_externalNeighborhood, hvT]

@[simp]
lemma leftDiff_externalNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) :
    (Finset.univ \ T) \ (T ∪ externalNeighborhood G T) =
      Finset.univ \ (T ∪ externalNeighborhood G T) := by
  ext v
  simp

@[simp]
lemma rightDiff_externalNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (T : Finset V) :
    (T ∪ externalNeighborhood G T) \ (Finset.univ \ T) = T := by
  ext v
  by_cases hvT : v ∈ T <;> simp [mem_externalNeighborhood, hvT]

lemma IsOddCycleSubgraph.coe_connected
    {V : Type*} {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) : H.coe.Connected := by
  obtain ⟨n, hn3, -, ⟨e⟩⟩ := hH
  have hcycle : (SimpleGraph.cycleGraph n).Connected := by
    have h := (SimpleGraph.cycleGraph_connected (n := n - 1))
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
    exact h
  exact (e.connected_iff).mp hcycle

/-- An odd cycle outside `Z` lies inside one full component of `G - Z`,
and remains an odd-cycle subgraph after that component is viewed in `G`. -/
lemma exists_odd_componentVertices
    {V : Type*} [Fintype V] (G : SimpleGraph V) (Z : Finset V)
    (H : (G.induce (Z : Set V)ᶜ).Subgraph)
    (hH : IsOddCycleSubgraph H) :
    ∃ c : (G.induce (Z : Set V)ᶜ).ConnectedComponent,
      ∃ K : (G.induce (componentVertices G Z c : Set V)).Subgraph,
        IsOddCycleSubgraph K := by
  obtain ⟨x, hx⟩ := hH.verts_nonempty
  let c := (G.induce (Z : Set V)ᶜ).connectedComponentMk x
  have hall : ∀ y : H.verts, y.1 ∈ c.supp := by
    intro y
    have hr : (G.induce (Z : Set V)ᶜ).Reachable x y.1 :=
      hH.coe_connected.preconnected ⟨x, hx⟩ y |>.map H.hom
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y.1).2
      (SimpleGraph.ConnectedComponent.sound hr).symm
  let f : SimpleGraph.Copy H.coe
      (G.induce (componentVertices G Z c : Set V)) :=
    { toHom :=
        { toFun := fun y ↦ ⟨y.1.1, by
              rw [coe_componentVertices]
              exact ⟨y.1, hall y, rfl⟩⟩
          map_rel' := by
            intro y z hyz
            exact H.adj_sub hyz }
      injective' := by
        intro y z hyz
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun q : {v : V // v ∈ (componentVertices G Z c : Set V)} ↦ q.1)
          hyz }
  obtain ⟨n, hn3, hnodd, ⟨e⟩⟩ := hH
  let copy : SimpleGraph.Copy (SimpleGraph.cycleGraph n)
      (G.induce (componentVertices G Z c : Set V)) := f.comp e.toCopy
  let K := copy.toSubgraph
  exact ⟨c, K, n, hn3, hnodd, ⟨copy.isoToSubgraph⟩⟩

/-- Every odd-cycle subgraph has additive independence defect at least one. -/
lemma oddCycleSubgraph_defect {V : Type*} [Finite V]
    {G : SimpleGraph V} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H) :
    2 * H.coe.indepNum + 1 ≤ H.verts.ncard := by
  obtain ⟨n, hn3, hnodd, ⟨e⟩⟩ := hH
  have hc := two_mul_indepNum_cycleGraph_add_one_le hn3 hnodd
  have hi : (SimpleGraph.cycleGraph n).indepNum = H.coe.indepNum :=
    indepNum_eq_of_iso e
  have hv : H.verts.ncard = n := by
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card H.verts = Nat.card (Fin n) := (Nat.card_congr e.toEquiv).symm
      _ = n := Nat.card_fin n
  rwa [hi, ← hv] at hc

/-- A finite family of odd-cycle subgraphs is half-integral if no host
vertex belongs to more than two family members. -/
def IsHalfIntegralOddCycleFamily {V : Type*} [Fintype V]
    {G : SimpleGraph V} (P : Finset G.Subgraph) : Prop :=
  (∀ H ∈ P, IsOddCycleSubgraph H) ∧
    ∀ v : V, (P.filter fun H ↦ v ∈ H.verts).card ≤ 2

/-- A half-integral packing of `p` distinct odd-cycle subgraphs. -/
def HasHalfIntegralOddCyclePacking {V : Type*} [Fintype V]
    (p : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ P : Finset G.Subgraph,
    P.card = p ∧ IsHalfIntegralOddCycleFamily P

/-- A fixed-parameter, fixed-bound instance of the half-integral
packing/transversal dichotomy, quantified over every finite vertex type. -/
def HalfIntegralOddCycleDichotomy (p C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ G : SimpleGraph V,
    HasHalfIntegralOddCyclePacking p G ∨
      BipartiteAfterDeletingAtMost C G

/-- A graph embedding transports a half-integral odd-cycle family without
changing its cardinality or vertex congestion. -/
lemma IsHalfIntegralOddCycleFamily.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W}
    {P : Finset G.Subgraph} (hP : IsHalfIntegralOddCycleFamily P)
    (f : G ↪g G') :
    IsHalfIntegralOddCycleFamily
      (P.image fun H ↦ H.map f.toHom) := by
  let mapSub : G.Subgraph → G'.Subgraph := fun H ↦ H.map f.toHom
  have hmapinj : Function.Injective mapSub :=
    subgraphMap_injective_of_embedding f
  constructor
  · intro H hH
    obtain ⟨K, hKP, rfl⟩ := Finset.mem_image.mp hH
    exact (hP.1 K hKP).map_embedding f
  · intro w
    by_cases hw : w ∈ Set.range f
    · obtain ⟨v, rfl⟩ := hw
      have hmem : ∀ K : G.Subgraph,
          f v ∈ (mapSub K).verts ↔ v ∈ K.verts := by
        intro K
        constructor
        · rintro ⟨u, huK, huv⟩
          exact (f.injective huv).symm ▸ huK
        · intro hvK
          exact ⟨v, hvK, rfl⟩
      have hfilter :
          (P.image mapSub).filter (fun K ↦ f v ∈ K.verts) =
            (P.filter fun K ↦ v ∈ K.verts).image mapSub := by
        ext K
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨L, hLP, hLK⟩, hfvK⟩
          subst K
          exact ⟨L, ⟨hLP, (hmem L).mp hfvK⟩, rfl⟩
        · rintro ⟨L, ⟨hLP, hvL⟩, hLK⟩
          subst K
          exact ⟨⟨L, hLP, rfl⟩, (hmem L).mpr hvL⟩
      rw [hfilter, Finset.card_image_of_injective _ hmapinj]
      exact hP.2 v
    · have hempty :
          (P.image mapSub).filter (fun K ↦ w ∈ K.verts) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro K hK
        obtain ⟨L, hLP, rfl⟩ := Finset.mem_image.mp hK
        intro hwmap
        obtain ⟨v, -, hvw⟩ := hwmap
        exact hw ⟨v, hvw⟩
      rw [hempty]
      simp

/-- A half-integral packing transports along every graph embedding. -/
lemma HasHalfIntegralOddCyclePacking.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {p : ℕ}
    (hP : HasHalfIntegralOddCyclePacking p G) (f : G ↪g G') :
    HasHalfIntegralOddCyclePacking p G' := by
  obtain ⟨P, hPcard, hP⟩ := hP
  refine ⟨P.image (fun H ↦ H.map f.toHom), ?_, hP.map_embedding f⟩
  rw [Finset.card_image_of_injective _
    (subgraphMap_injective_of_embedding f)]
  exact hPcard

/-- A vertex-disjoint odd cycle may be inserted into a half-integral family.
The resulting family is still half-integral (in fact the new cycle has no
overlap with an old member). -/
lemma IsHalfIntegralOddCycleFamily.insert_disjoint
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {P : Finset G.Subgraph} {H : G.Subgraph}
    (hP : IsHalfIntegralOddCycleFamily P)
    (hH : IsOddCycleSubgraph H)
    (hdisj : ∀ K ∈ P, Disjoint H.verts K.verts) :
    IsHalfIntegralOddCycleFamily (insert H P) := by
  have hHnot : H ∉ P := by
    intro hHP
    obtain ⟨v, hvH⟩ := hH.verts_nonempty
    exact Set.disjoint_left.mp (hdisj H hHP) hvH hvH
  constructor
  · intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hKP
    · exact hH
    · exact hP.1 K hKP
  · intro v
    by_cases hvH : v ∈ H.verts
    · have hempty : P.filter (fun K ↦ v ∈ K.verts) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro K hKP
        exact Set.disjoint_left.mp (hdisj K hKP) hvH
      simp only [Finset.filter_insert, hvH, ↓reduceIte, hempty,
        Finset.insert_empty, Finset.card_singleton]
      omega
    · simp only [Finset.filter_insert, hvH, ↓reduceIte]
      exact hP.2 v

lemma IsHalfIntegralOddCycleFamily.card_insert_disjoint
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {P : Finset G.Subgraph} {H : G.Subgraph}
    (hH : IsOddCycleSubgraph H)
    (hdisj : ∀ K ∈ P, Disjoint H.verts K.verts) :
    (insert H P).card = P.card + 1 := by
  have hHnot : H ∉ P := by
    intro hHP
    obtain ⟨v, hvH⟩ := hH.verts_nonempty
    exact Set.disjoint_left.mp (hdisj H hHP) hvH hvH
  simp [hHnot]

/-- An integral odd-cycle packing on one induced side and an odd cycle on a
vertex-disjoint induced side combine to an integral packing with one more
member.  At the level of the canonical packing representation, the new
cycle is prepended to the list and the two graph copies are joined by a
disjoint graph sum. -/
lemma hasOddCyclePacking_succ_of_disjoint_induces
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {S T : Set V} (hST : Disjoint S T) {p : ℕ}
    (hP : HasOddCyclePacking p (G.induce S))
    (hT : ∃ H : (G.induce T).Subgraph, IsOddCycleSubgraph H) :
    HasOddCyclePacking (p + 1) G := by
  obtain ⟨ns, hlen, hodd, ⟨cP⟩⟩ := hP
  obtain ⟨H, hHodd⟩ := hT
  let fS : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  let fT : G.induce T ↪g G := SimpleGraph.Embedding.induce T
  let cA : SimpleGraph.Copy (cycleUnionGraph ns) G :=
    fS.toCopy.comp cP
  let dB : OddCycleCopyData (G.induce T) := hHodd.toCopyData
  let cB : SimpleGraph.Copy (SimpleGraph.cycleGraph dB.length) G :=
    fT.toCopy.comp dB.copy
  have hdisj : Disjoint (Set.range cB) (Set.range cA) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨b, rfl⟩ ⟨a, ha⟩
    have hvT : cB b ∈ T := by
      exact (dB.copy b).property
    have hvS : cB b ∈ S := by
      rw [← ha]
      exact (cP a).property
    exact Set.disjoint_left.mp hST hvS hvT
  let c : SimpleGraph.Copy
      (cycleUnionGraph (dB.length :: ns)) G :=
    sumCopyOfDisjointRanges cB cA hdisj
  refine ⟨dB.length :: ns, ?_, ?_, ⟨c⟩⟩
  · simp [hlen]
  · intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨dB.three_le, dB.odd_length⟩
    · exact hodd n hn

/-- A half-integral packing on one induced side and an odd cycle on a
vertex-disjoint induced side combine to a packing with one more member in
the ambient graph. -/
lemma hasHalfIntegralOddCyclePacking_succ_of_disjoint_induces
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {S T : Set V} (hST : Disjoint S T) {p : ℕ}
    (hP : HasHalfIntegralOddCyclePacking p (G.induce S))
    (hT : ∃ H : (G.induce T).Subgraph, IsOddCycleSubgraph H) :
    HasHalfIntegralOddCyclePacking (p + 1) G := by
  obtain ⟨P, hPcard, hPfamily⟩ := hP
  obtain ⟨H, hHodd⟩ := hT
  let fS : G.induce S ↪g G := SimpleGraph.Embedding.induce S
  let fT : G.induce T ↪g G := SimpleGraph.Embedding.induce T
  let mapS : (G.induce S).Subgraph → G.Subgraph :=
    fun K ↦ K.map fS.toHom
  let Q : Finset G.Subgraph := P.image mapS
  let K : G.Subgraph := H.map fT.toHom
  have hQfamily : IsHalfIntegralOddCycleFamily Q := by
    exact hPfamily.map_embedding fS
  have hKodd : IsOddCycleSubgraph K := hHodd.map_embedding fT
  have hKQ : ∀ L ∈ Q, Disjoint K.verts L.verts := by
    intro L hLQ
    obtain ⟨L₀, hL₀P, rfl⟩ := Finset.mem_image.mp hLQ
    apply Set.disjoint_left.mpr
    intro v hvK hvL
    obtain ⟨t, -, htv⟩ := hvK
    obtain ⟨s, -, hsv⟩ := hvL
    have hts : (t : V) = s := htv.trans hsv.symm
    exact Set.disjoint_left.mp hST s.2 (hts ▸ t.2)
  refine ⟨insert K Q, ?_, hQfamily.insert_disjoint hKodd hKQ⟩
  rw [IsHalfIntegralOddCycleFamily.card_insert_disjoint hKodd hKQ]
  change Q.card + 1 = p + 1
  rw [show Q.card = P.card by
    exact Finset.card_image_of_injective _
      (subgraphMap_injective_of_embedding fS)]
  exact congrArg (· + 1) hPcard

/-- The full low-separation induction step in the half-integral
Kawarabayashi--Reed proof.  If both exclusive sides contain an odd cycle,
then applying the parameter-`p` dichotomy to each side yields either a
parameter-`p+1` packing in the host or a transversal obtained by joining the
two side transversals with the separator. -/
theorem halfIntegralPacking_or_delete_of_twoSidedOddSeparation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C : ℕ) (hsep : IsVertexSeparation G A B)
    (hoddA : ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hoddB : ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hA : HasHalfIntegralOddCyclePacking p
        (G.induce (((A \ B : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((A \ B : Finset V) : Set V))))
    (hB : HasHalfIntegralOddCyclePacking p
        (G.induce (((B \ A : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((B \ A : Finset V) : Set V)))) :
    HasHalfIntegralOddCyclePacking (p + 1) G ∨
      BipartiteAfterDeletingAtMost (C + C + (A ∩ B).card) G := by
  have hdisj : Disjoint
      (((A \ B : Finset V) : Set V))
      (((B \ A : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro v hvAB hvBA
    have hvAB' := Finset.mem_sdiff.mp hvAB
    have hvBA' := Finset.mem_sdiff.mp hvBA
    exact hvAB'.2 hvBA'.1
  rcases hA with hpackA | hdeleteA
  · exact Or.inl
      (hasHalfIntegralOddCyclePacking_succ_of_disjoint_induces
        G hdisj hpackA hoddB)
  · rcases hB with hpackB | hdeleteB
    · exact Or.inl
        (hasHalfIntegralOddCyclePacking_succ_of_disjoint_induces
          G hdisj.symm hpackB hoddA)
    · exact Or.inr
        (bipartiteAfterDeletingAtMost_of_separation
          G A B C C hsep hdeleteA hdeleteB)

/-- Integral counterpart of the low-separation induction step.  If the two
exclusive sides both contain an odd cycle, then a `p`-packing supplied on
either side extends to a `(p+1)`-packing in the host; if both side outcomes
are deletion sets, they glue together with the separator. -/
theorem oddCyclePacking_or_delete_of_twoSidedOddSeparation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C : ℕ) (hsep : IsVertexSeparation G A B)
    (hoddA : ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hoddB : ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hA : HasOddCyclePacking p
        (G.induce (((A \ B : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((A \ B : Finset V) : Set V))))
    (hB : HasOddCyclePacking p
        (G.induce (((B \ A : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((B \ A : Finset V) : Set V)))) :
    HasOddCyclePacking (p + 1) G ∨
      BipartiteAfterDeletingAtMost (C + C + (A ∩ B).card) G := by
  have hdisj : Disjoint
      (((A \ B : Finset V) : Set V))
      (((B \ A : Finset V) : Set V)) := by
    rw [Set.disjoint_left]
    intro v hvAB hvBA
    have hvAB' := Finset.mem_sdiff.mp hvAB
    have hvBA' := Finset.mem_sdiff.mp hvBA
    exact hvAB'.2 hvBA'.1
  rcases hA with hpackA | hdeleteA
  · exact Or.inl
      (hasOddCyclePacking_succ_of_disjoint_induces
        G hdisj hpackA hoddB)
  · rcases hB with hpackB | hdeleteB
    · exact Or.inl
        (hasOddCyclePacking_succ_of_disjoint_induces
          G hdisj.symm hpackB hoddA)
    · exact Or.inr
        (bipartiteAfterDeletingAtMost_of_separation
          G A B C C hsep hdeleteA hdeleteB)

/-- Contrapositive form used for a minimal counterexample: if the host has
neither outcome at parameter `p+1` and the induction dichotomy holds on both
sides, no low-order separation can have odd cycles on both exclusive sides. -/
theorem not_twoSidedOddSeparation_of_counterexample
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C : ℕ) (hsep : IsVertexSeparation G A B)
    (hnoPack : ¬ HasHalfIntegralOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost
      (C + C + (A ∩ B).card) G)
    (hA : HasHalfIntegralOddCyclePacking p
        (G.induce (((A \ B : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((A \ B : Finset V) : Set V))))
    (hB : HasHalfIntegralOddCyclePacking p
        (G.induce (((B \ A : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((B \ A : Finset V) : Set V)))) :
    ¬ ((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) := by
  rintro ⟨hoddA, hoddB⟩
  rcases halfIntegralPacking_or_delete_of_twoSidedOddSeparation
      G A B p C hsep hoddA hoddB hA hB with hpack | hdelete
  · exact hnoPack hpack
  · exact hnoDelete hdelete

/-- Quantitative form matching the published recurrence
`F(p+1) ≥ 2 F(p) + ℓ(p+1)`: a counterexample to the larger deletion bound
cannot have a two-sided odd separation of order at most `ℓ`. -/
theorem not_twoSidedOddSeparation_of_bounded_counterexample
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C ℓ D : ℕ)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasHalfIntegralOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hA : HasHalfIntegralOddCyclePacking p
        (G.induce (((A \ B : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((A \ B : Finset V) : Set V))))
    (hB : HasHalfIntegralOddCyclePacking p
        (G.induce (((B \ A : Finset V) : Set V))) ∨
      BipartiteAfterDeletingAtMost C
        (G.induce (((B \ A : Finset V) : Set V)))) :
    ¬ ((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) := by
  apply not_twoSidedOddSeparation_of_counterexample
    G A B p C hsep hnoPack
  · intro hsmall
    apply hnoDelete
    apply hsmall.mono
    exact (Nat.add_le_add_left hsepCard (C + C)).trans hrec
  · exact hA
  · exact hB

/-- Published property (1) in the Kawarabayashi--Reed induction, with the
side dichotomies obtained directly from the induction hypothesis. -/
theorem no_twoSidedOddSeparation_of_inductionHypothesis
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C ℓ D : ℕ)
    (hInd : HalfIntegralOddCycleDichotomy.{u} p C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasHalfIntegralOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G) :
    ¬ ((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) := by
  exact not_twoSidedOddSeparation_of_bounded_counterexample
    G A B p C ℓ D hsep hsepCard hrec hnoPack hnoDelete
      (hInd _ (G.induce (((A \ B : Finset V) : Set V))))
      (hInd _ (G.induce (((B \ A : Finset V) : Set V))))

/-- Every separation covered by the low-order induction is oriented by its
unique odd exclusive side.  At most one side is odd by the preceding
two-sided-separation lemma.  At least one side is odd because, otherwise,
both exclusive induced graphs are bipartite and the separation gluing lemma
would delete only the separator, contradicting the chosen counterexample.

This is the exact orientation used to construct the bramble in the
Kawarabayashi--Reed proof. -/
theorem exactly_one_odd_side_of_inductionHypothesis
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C ℓ D : ℕ)
    (hInd : HalfIntegralOddCycleDichotomy.{u} p C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasHalfIntegralOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G) :
    (((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∨
      ((∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H)) := by
  let GA : SimpleGraph {v : V // v ∈ (((A \ B : Finset V) : Set V))} :=
    G.induce (((A \ B : Finset V) : Set V))
  let GB : SimpleGraph {v : V // v ∈ (((B \ A : Finset V) : Set V))} :=
    G.induce (((B \ A : Finset V) : Set V))
  have hnotBoth := no_twoSidedOddSeparation_of_inductionHypothesis
    G A B p C ℓ D hInd hsep hsepCard hrec hnoPack hnoDelete
  by_cases hoddA : ∃ H : GA.Subgraph, IsOddCycleSubgraph H
  · by_cases hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H
    · exact (hnotBoth ⟨hoddA, hoddB⟩).elim
    · exact Or.inl ⟨hoddA, hoddB⟩
  · have hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H := by
      by_contra hnotB
      have hbipA : GA.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GA).2 hoddA
      have hbipB : GB.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GB).2 hnotB
      have hdelete : BipartiteAfterDeletingAtMost
          (0 + 0 + (A ∩ B).card) G :=
        bipartiteAfterDeletingAtMost_of_separation G A B 0 0 hsep
          ((bipartiteAfterDeletingAtMost_zero_iff GA).2 hbipA)
          ((bipartiteAfterDeletingAtMost_zero_iff GB).2 hbipB)
      apply hnoDelete
      apply hdelete.mono
      omega
    exact Or.inr ⟨hoddB, hoddA⟩

/-- The normalized Reed bramble: a member is a connected odd side whose
external neighborhood has order at most `ℓ`, and whose opposite exclusive
side is bipartite.  Using the full external neighborhood makes the implicit
minimal-separator normalization in the published proof explicit. -/
def lowOrderOddSides {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : ℕ) : Finset (Finset V) :=
  Finset.univ.filter fun T ↦
    (G.induce (T : Set V)).Connected ∧
      (∃ H : (G.induce (T : Set V)).Subgraph,
        IsOddCycleSubgraph H) ∧
      (externalNeighborhood G T).card ≤ ℓ ∧
      (G.induce (((Finset.univ \ (T ∪ externalNeighborhood G T) :
        Finset V) : Set V))).IsBipartite

lemma mem_lowOrderOddSides {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : ℕ) (T : Finset V) :
    T ∈ lowOrderOddSides G ℓ ↔
      (G.induce (T : Set V)).Connected ∧
        (∃ H : (G.induce (T : Set V)).Subgraph,
          IsOddCycleSubgraph H) ∧
        (externalNeighborhood G T).card ≤ ℓ ∧
        (G.induce (((Finset.univ \ (T ∪ externalNeighborhood G T) :
          Finset V) : Set V))).IsBipartite := by
  simp [lowOrderOddSides]

/-- The normalized low-order odd sides pairwise touch.  If two did not,
the second would lie wholly in the bipartite opposite side of the first,
contradicting its odd cycle. -/
theorem lowOrderOddSides_isFiniteBramble
    {V : Type*} [Fintype V] (G : SimpleGraph V) (ℓ : ℕ) :
    IsFiniteBramble G (lowOrderOddSides G ℓ) := by
  constructor
  · intro A hA
    exact (mem_lowOrderOddSides G ℓ A).1 hA |>.1
  · intro A hA B hB _
    have hAd := (mem_lowOrderOddSides G ℓ A).1 hA
    have hBd := (mem_lowOrderOddSides G ℓ B).1 hB
    by_contra htouch
    have hdisj : Disjoint A B := by
      by_contra h
      exact htouch (Or.inl h)
    have hnoAdj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
      intro a ha b hb hab
      exact htouch (Or.inr ⟨a, ha, b, hb, hab⟩)
    have hBsub : B ⊆
        Finset.univ \ (A ∪ externalNeighborhood G A) := by
      intro b hb
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, not_or]
      constructor
      · exact fun hbA ↦ Finset.disjoint_left.mp hdisj hbA hb
      · intro hbN
        obtain ⟨-, a, ha, hba⟩ :=
          (mem_externalNeighborhood G A b).1 hbN
        exact hnoAdj a ha b hb hba.symm
    let S : Finset V :=
      Finset.univ \ (A ∪ externalNeighborhood G A)
    let f : G.induce (B : Set V) ↪g G.induce (S : Set V) :=
      { toFun := fun b ↦ ⟨b.1, hBsub b.2⟩
        inj' := by
          intro b c hbc
          apply Subtype.ext
          exact congrArg (fun q : {v : V // v ∈ (S : Set V)} ↦ q.1) hbc
        map_rel_iff' := by rfl }
    have hbipB : (G.induce (B : Set V)).IsBipartite := by
      obtain ⟨color⟩ := hAd.2.2.2
      exact ⟨color.comp f.toHom⟩
    exact ((isBipartite_iff_no_oddCycleSubgraph
      (G.induce (B : Set V))).1 hbipB) hBd.2.1

/-- In a counterexample covered by the parameter recurrence, the normalized
odd-side bramble has order at least `ℓ`.  Given a smaller set `X`, choose a
non-bipartite component of `G-X`; its external neighborhood is contained in
`X`, and the separation orientation makes the opposite side bipartite. -/
theorem lowOrderOddSides_brambleOrderAtLeast
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (p C ℓ D : ℕ)
    (hInd : HalfIntegralOddCycleDichotomy.{u} p C)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasHalfIntegralOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G) :
    BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) := by
  apply brambleOrderAtLeast_of_small_set_misses
  intro X hXcard
  have hXD : X.card ≤ D := by omega
  have hnBip : ¬ (G.induce (X : Set V)ᶜ).IsBipartite := by
    intro hbip
    exact hnoDelete ⟨X, hXD, hbip⟩
  have hodd : ∃ H : (G.induce (X : Set V)ᶜ).Subgraph,
      IsOddCycleSubgraph H := by
    by_contra hno
    exact hnBip
      ((isBipartite_iff_no_oddCycleSubgraph
        (G.induce (X : Set V)ᶜ)).2 hno)
  obtain ⟨H, hH⟩ := hodd
  obtain ⟨c, K, hK⟩ := exists_odd_componentVertices G X H hH
  let T := componentVertices G X c
  let N := externalNeighborhood G T
  have hTN : N = externalNeighborhood G T := rfl
  have hTconn : (G.induce (T : Set V)).Connected :=
    componentVertices_connected G X c
  have hTX : Disjoint T X := componentVertices_disjoint_delete G X c
  have hNX : N ⊆ X := component_externalNeighborhood_subset_delete G X c
  have hNcard : N.card ≤ ℓ := by
    exact (Finset.card_le_card hNX).trans (Nat.le_of_lt hXcard)
  have horient := exactly_one_odd_side_of_inductionHypothesis
    G (Finset.univ \ T) (T ∪ N) p C ℓ D hInd
      (by simpa only [hTN] using separation_externalNeighborhood G T)
      (by simpa only [hTN, inter_externalNeighborhood] using hNcard)
      hrec hnoPack hnoDelete
  dsimp [N] at horient
  have hleftEq := leftDiff_externalNeighborhood G T
  have hrightEq := rightDiff_externalNeighborhood G T
  rw [hleftEq, hrightEq] at horient
  have horient' :
      (((∃ H : (G.induce (((Finset.univ \
          (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∨
        ((∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (((Finset.univ \
            (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
              IsOddCycleSubgraph H)) := by
    exact horient
  have hTcycle : ∃ H : (G.induce (T : Set V)).Subgraph,
      IsOddCycleSubgraph H := ⟨K, hK⟩
  have hotherNoOdd :
      ¬ ∃ H : (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H := by
    rcases horient' with hleft | hright
    · exact (hleft.2 hTcycle).elim
    · exact hright.2
  have hotherBip :
      (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).IsBipartite :=
    (isBipartite_iff_no_oddCycleSubgraph _).2 hotherNoOdd
  refine ⟨T, (mem_lowOrderOddSides G ℓ T).2
    ⟨hTconn, hTcycle, ?_, hotherBip⟩, hTX.symm⟩
  simpa only [hTN] using hNcard

/-- A subfamily of a half-integral odd-cycle family is half-integral. -/
lemma IsHalfIntegralOddCycleFamily.mono {V : Type*} [Fintype V]
    {G : SimpleGraph V} {P Q : Finset G.Subgraph}
    (hP : IsHalfIntegralOddCycleFamily P) (hQP : Q ⊆ P) :
    IsHalfIntegralOddCycleFamily Q := by
  constructor
  · intro H hHQ
    exact hP.1 H (hQP hHQ)
  · intro v
    apply (Finset.card_le_card ?_).trans (hP.2 v)
    intro H hH
    rw [Finset.mem_filter] at hH ⊢
    exact ⟨hQP hH.1, hH.2⟩

/-- Half-integral packing is downward closed in the requested family size. -/
lemma HasHalfIntegralOddCyclePacking.mono {V : Type*} [Fintype V]
    {G : SimpleGraph V} {p q : ℕ} (hqp : q ≤ p)
    (hP : HasHalfIntegralOddCyclePacking p G) :
    HasHalfIntegralOddCyclePacking q G := by
  obtain ⟨P, hPcard, hP⟩ := hP
  have hqP : q ≤ P.card := by simpa [hPcard]
  obtain ⟨Q, hQP, hQcard⟩ := Finset.exists_subset_card_eq hqP
  exact ⟨Q, hQcard, hP.mono hQP⟩

/-- Every graph has the empty half-integral packing. -/
lemma hasHalfIntegralOddCyclePacking_zero {V : Type*} [Fintype V]
    (G : SimpleGraph V) : HasHalfIntegralOddCyclePacking 0 G := by
  refine ⟨∅, by simp, ?_⟩
  constructor
  · simp
  · simp

/-- Reed's half-integral Erdős--Pósa theorem for odd cycles, stated on the
canonical finite vertex types used by `Problem73`.  The bound is uniform in
the graph: either there are `p` odd cycles with vertex congestion at most
two, or deleting at most `C` vertices makes the graph bipartite. -/
def HalfIntegralOddCycleErdosPosaStatement : Prop :=
  ∀ p : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    HasHalfIntegralOddCyclePacking p G ∨
      BipartiteAfterDeletingAtMost C G

/-- The literature's hitting-set presentation of the same half-integral
Erdős--Pósa statement. -/
def HalfIntegralOddCycleHittingStatement : Prop :=
  ∀ p : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    HasHalfIntegralOddCyclePacking p G ∨
      ∃ X : Finset (Fin n), X.card ≤ C ∧
        MeetsEveryOddCycleSubgraph X G

/-- The deletion and hitting-set presentations of Reed's half-integral
theorem are definitionally different but mathematically identical. -/
theorem halfIntegralOddCycleErdosPosa_iff_hitting :
    HalfIntegralOddCycleErdosPosaStatement ↔
      HalfIntegralOddCycleHittingStatement := by
  constructor
  · intro h p
    obtain ⟨C, hC⟩ := h p
    refine ⟨C, ?_⟩
    intro n G
    rcases hC n G with hpack | ⟨X, hXC, hbip⟩
    · exact Or.inl hpack
    · exact Or.inr ⟨X, hXC,
        (bipartite_induce_compl_iff_meetsEveryOddCycleSubgraph G X).mp hbip⟩
  · intro h p
    obtain ⟨C, hC⟩ := h p
    refine ⟨C, ?_⟩
    intro n G
    rcases hC n G with hpack | ⟨X, hXC, hhit⟩
    · exact Or.inl hpack
    · exact Or.inr ⟨X, hXC,
        (bipartite_induce_compl_iff_meetsEveryOddCycleSubgraph G X).mpr hhit⟩

/-- The second structural ingredient in the half-integral route: for each
near-bipartite parameter, one sufficiently large half-integral odd-cycle
packing is impossible, uniformly over all finite graphs.  The elementary
incidence inequality below is weighted and does not by itself prove this
statement; controlling overlaps is part of Reed's deep argument. -/
def NearBipartiteHalfIntegralPackingBound : Prop :=
  ∀ k : ℕ, ∃ p : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    IsKNearBipartite k G → ¬ HasHalfIntegralOddCyclePacking p G

/-- The two half-integral structural statements compose directly to Reed's
near-bipartite conclusion.  This theorem contains no graph-theoretic input:
it only makes the quantifier order and the logical assembly explicit. -/
theorem reedNearBipartiteStatement_of_halfIntegral
    (hep : HalfIntegralOddCycleErdosPosaStatement)
    (hbound : NearBipartiteHalfIntegralPackingBound) :
    ReedNearBipartiteStatement := by
  intro k
  obtain ⟨p, hp⟩ := hbound k
  obtain ⟨C, hC⟩ := hep p
  refine ⟨C, ?_⟩
  intro n G hnear
  rcases hC n G with hpack | hdelete
  · exact (hp n G hnear hpack).elim
  · exact hdelete

/-- Conditional assembly of the exact Problem 73 formulation from the two
precise half-integral interfaces.  The hypotheses here are propositions to
be proved by the structural layer, not axioms or theorem parameters in the
final result. -/
theorem problem73_of_halfIntegral
    (hep : HalfIntegralOddCycleErdosPosaStatement)
    (hbound : NearBipartiteHalfIntegralPackingBound) : Problem73 := by
  apply problem73_iff_reedNearBipartiteStatement.mpr
  exact reedNearBipartiteStatement_of_halfIntegral hep hbound

lemma oddCycleSubgraph_independent_inter_defect
    {V : Type*} [Finite V] {G : SimpleGraph V}
    {H : G.Subgraph} (hH : IsOddCycleSubgraph H)
    (I : Finset V) (hI : H.spanningCoe.IsIndepSet (I : Set V)) :
    2 * (I.filter fun v ↦ v ∈ H.verts).card + 1 ≤ H.verts.ncard := by
  let _ : DecidablePred H.verts := Classical.decPred H.verts
  let J : Finset H.verts := I.subtype H.verts
  have hJ : H.coe.IsIndepSet (J : Set H.verts) := by
    intro v hv w hw hvw hadj
    apply hI
    · exact Finset.mem_subtype.mp hv
    · exact Finset.mem_subtype.mp hw
    · exact fun h ↦ hvw (Subtype.ext h)
    · exact hadj
  have hJcard : J.card ≤ H.coe.indepNum := hJ.card_le_indepNum
  have hdef := oddCycleSubgraph_defect hH
  have hcard : J.card = (I.filter fun v ↦ v ∈ H.verts).card := by
    exact Finset.card_subtype H.verts I
  rw [← hcard]
  omega

/-- Summing the odd-cycle inequalities in a finite family gives the exact
incidence-weighted stable-set inequality. -/
theorem sum_oddCycleSubgraph_independent_inter_defect
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (P : Finset G.Subgraph)
    (hP : ∀ H ∈ P, IsOddCycleSubgraph H)
    (I : Finset V)
    (hI : ∀ H ∈ P, H.spanningCoe.IsIndepSet (I : Set V)) :
    2 * ∑ H ∈ P, (I.filter fun v ↦ v ∈ H.verts).card + P.card ≤
      ∑ H ∈ P, H.verts.ncard := by
  have hsum : ∑ H ∈ P,
      (2 * (I.filter fun v ↦ v ∈ H.verts).card + 1) ≤
      ∑ H ∈ P, H.verts.ncard := by
    exact Finset.sum_le_sum fun H hHP ↦
      oddCycleSubgraph_independent_inter_defect (hP H hHP) I (hI H hHP)
  calc
    2 * ∑ H ∈ P, (I.filter fun v ↦ v ∈ H.verts).card + P.card =
        ∑ H ∈ P, (2 * (I.filter fun v ↦ v ∈ H.verts).card + 1) := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
        Nat.mul_one]
    _ ≤ ∑ H ∈ P, H.verts.ncard := hsum

/-- A weighted collection of odd cycles and host edges whose total incidence
load is constant on `S` and zero outside it.  This is the stable-set dual
certificate naturally produced by parity corrections in a subdivided
Escher wall: cycle inequalities contribute the positive defect, while edge
inequalities make the vertex load uniform. -/
def IsUniformOddCycleEdgeCertificate {V : Type*} [Fintype V]
    {G : SimpleGraph V} (q : ℕ) (S : Finset V)
    (P : Finset G.Subgraph) (cycleWeight : G.Subgraph → ℕ)
    (M : Finset (Sym2 V)) (edgeWeight : Sym2 V → ℕ) : Prop :=
  (∀ H ∈ P, IsOddCycleSubgraph H) ∧
    M ⊆ G.edgeFinset ∧
    ∀ v : V,
      (∑ H ∈ P.filter fun H ↦ v ∈ H.verts, cycleWeight H) +
        (∑ e ∈ M.filter fun e ↦ v ∈ e, edgeWeight e) =
          if v ∈ S then q else 0

lemma weighted_cycle_inter_double_count {V : Type*} [Fintype V]
    {G : SimpleGraph V} (I : Finset V) (P : Finset G.Subgraph)
    (w : G.Subgraph → ℕ) :
    (∑ H ∈ P, w H * (I.filter fun v ↦ v ∈ H.verts).card) =
      ∑ v ∈ I, ∑ H ∈ P.filter (fun H ↦ v ∈ H.verts), w H := by
  simp_rw [Finset.card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_filter]

lemma weighted_cycle_verts_double_count {V : Type*} [Fintype V]
    {G : SimpleGraph V} (P : Finset G.Subgraph)
    (w : G.Subgraph → ℕ) :
    (∑ H ∈ P, w H * H.verts.ncard) =
      ∑ v ∈ (Finset.univ : Finset V),
        ∑ H ∈ P.filter (fun H ↦ v ∈ H.verts), w H := by
  have hncard (H : G.Subgraph) :
      H.verts.ncard =
        ((Finset.univ : Finset V).filter fun v ↦ v ∈ H.verts).card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext v
    simp
  simp_rw [hncard, Finset.card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_filter]

lemma weighted_edge_inter_double_count {V : Type*} [Fintype V]
    (I : Finset V) (M : Finset (Sym2 V)) (w : Sym2 V → ℕ) :
    (∑ e ∈ M, w e * (I.filter fun v ↦ v ∈ e).card) =
      ∑ v ∈ I, ∑ e ∈ M.filter (fun e ↦ v ∈ e), w e := by
  simp_rw [Finset.card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_filter]

lemma weighted_edge_verts_double_count {V : Type*} [Fintype V]
    {G : SimpleGraph V} (M : Finset (Sym2 V)) (w : Sym2 V → ℕ)
    (hM : M ⊆ G.edgeFinset) :
    2 * ∑ e ∈ M, w e =
      ∑ v ∈ (Finset.univ : Finset V),
        ∑ e ∈ M.filter (fun e ↦ v ∈ e), w e := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e heM
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          hM heM
      have hne : a ≠ b := hab.ne
      simp only [Sym2.mem_iff]
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : V ↦ x = a ∨ x = b) = {a, b} := by
        ext x
        simp [eq_comm]
      rw [hfilter]
      simp [hne]

lemma independent_edge_inter_card_le_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} {I : Finset V} (hI : G.IsIndepSet (I : Set V))
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (I.filter fun v ↦ v ∈ e).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxe := Finset.mem_filter.mp hx
  have hye := Finset.mem_filter.mp hy
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      simp only [Sym2.mem_iff] at hxe hye
      rcases hxe.2 with rfl | rfl <;> rcases hye.2 with rfl | rfl
      · rfl
      · exact (hI hxe.1 hye.1 hab.ne hab).elim
      · exact (hI hxe.1 hye.1 hab.ne.symm hab.symm).elim
      · rfl

lemma weighted_sum_oddCycleSubgraph_independent_inter_defect
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (P : Finset G.Subgraph) (w : G.Subgraph → ℕ)
    (hP : ∀ H ∈ P, IsOddCycleSubgraph H)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    2 * (∑ H ∈ P, w H * (I.filter fun v ↦ v ∈ H.verts).card) +
        (∑ H ∈ P, w H) ≤
      ∑ H ∈ P, w H * H.verts.ncard := by
  have hterm : ∀ H ∈ P,
      2 * (w H * (I.filter fun v ↦ v ∈ H.verts).card) + w H ≤
        w H * H.verts.ncard := by
    intro H hHP
    have hIH : H.spanningCoe.IsIndepSet (I : Set V) := by
      intro a ha b hb hab hadj
      exact hI ha hb hab (H.adj_sub hadj)
    have hcycle := oddCycleSubgraph_independent_inter_defect
      (hP H hHP) I hIH
    have hmul := Nat.mul_le_mul_left (w H) hcycle
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hsum :
      (∑ H ∈ P,
        (2 * (w H * (I.filter fun v ↦ v ∈ H.verts).card) + w H)) ≤
      ∑ H ∈ P, w H * H.verts.ncard :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  exact hsum

lemma weighted_sum_edge_independent_inter
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : Finset (Sym2 V)) (w : Sym2 V → ℕ)
    (hM : M ⊆ G.edgeFinset)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    ∑ e ∈ M, w e * (I.filter fun v ↦ v ∈ e).card ≤
      ∑ e ∈ M, w e := by
  apply Finset.sum_le_sum
  intro e heM
  have hcard := independent_edge_inter_card_le_one hI (hM heM)
  have hmul := Nat.mul_le_mul_left (w e) hcard
  simpa using hmul

lemma IsUniformOddCycleEdgeCertificate.independent_load
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {q : ℕ} {S I : Finset V} {P : Finset G.Subgraph}
    {cycleWeight : G.Subgraph → ℕ} {M : Finset (Sym2 V)}
    {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformOddCycleEdgeCertificate q S P cycleWeight M edgeWeight)
    (hIS : I ⊆ S) :
    (∑ H ∈ P,
        cycleWeight H * (I.filter fun v ↦ v ∈ H.verts).card) +
      (∑ e ∈ M,
        edgeWeight e * (I.filter fun v ↦ v ∈ e).card) =
      q * I.card := by
  rw [weighted_cycle_inter_double_count I P cycleWeight,
    weighted_edge_inter_double_count I M edgeWeight]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v ∈ I,
        ((∑ H ∈ P.filter (fun H ↦ v ∈ H.verts), cycleWeight H) +
          ∑ e ∈ M.filter (fun e ↦ v ∈ e), edgeWeight e) =
        ∑ v ∈ I, q := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa [hIS hv] using hcert.2.2 v
    _ = q * I.card := by simp [Nat.mul_comm]

lemma IsUniformOddCycleEdgeCertificate.total_load
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {q : ℕ} {S : Finset V} {P : Finset G.Subgraph}
    {cycleWeight : G.Subgraph → ℕ} {M : Finset (Sym2 V)}
    {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformOddCycleEdgeCertificate q S P cycleWeight M edgeWeight) :
    (∑ H ∈ P, cycleWeight H * H.verts.ncard) +
        2 * (∑ e ∈ M, edgeWeight e) =
      q * S.card := by
  rw [weighted_cycle_verts_double_count P cycleWeight,
    weighted_edge_verts_double_count M edgeWeight hcert.2.1]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v ∈ (Finset.univ : Finset V),
        ((∑ H ∈ P.filter (fun H ↦ v ∈ H.verts), cycleWeight H) +
          ∑ e ∈ M.filter (fun e ↦ v ∈ e), edgeWeight e) =
        ∑ v ∈ (Finset.univ : Finset V), if v ∈ S then q else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact hcert.2.2 v
    _ = q * S.card := by simp [Nat.mul_comm]

/-- A uniform weighted cycle-edge certificate gives an ordinary stable-set
defect: the sum of its odd-cycle weights is the additive gain. -/
theorem uniformOddCycleEdgeCertificate_defect
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {q : ℕ} {S : Finset V} {P : Finset G.Subgraph}
    {cycleWeight : G.Subgraph → ℕ} {M : Finset (Sym2 V)}
    {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformOddCycleEdgeCertificate q S P cycleWeight M edgeWeight) :
    2 * q * (G.induce (S : Set V)).indepNum +
        (∑ H ∈ P, cycleWeight H) ≤ q * S.card := by
  obtain ⟨I, hIind, hIcard⟩ :=
    (G.induce (S : Set V)).exists_isNIndepSet_indepNum
  let Ihost : Finset V := I.image Subtype.val
  have hIhostcard : Ihost.card = I.card := by
    rw [Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hIhostS : Ihost ⊆ S := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hv
    exact u.property
  have hIhostIndep : G.IsIndepSet (Ihost : Set V) := by
    intro u hu v hv huv hadj
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact hIind hu' hv' (fun h ↦ huv (congrArg Subtype.val h)) hadj
  have hcycles := weighted_sum_oddCycleSubgraph_independent_inter_defect
    P cycleWeight hcert.1 Ihost hIhostIndep
  have hedges := weighted_sum_edge_independent_inter
    M edgeWeight hcert.2.1 Ihost hIhostIndep
  have hindload := hcert.independent_load hIhostS
  have htotload := hcert.total_load
  rw [hIhostcard, hIcard] at hindload
  have hedges2 := Nat.mul_le_mul_left 2 hedges
  rw [Nat.mul_assoc, ← hindload, ← htotload]
  omega

/-- In a graph of hereditary independence defect at most `k`, the total odd
cycle weight of a uniform certificate of load `q` is at most `q*k`. -/
theorem uniformOddCycleEdgeCertificate_cycleWeight_le
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k q : ℕ}
    {S : Finset V} {P : Finset G.Subgraph}
    {cycleWeight : G.Subgraph → ℕ} {M : Finset (Sym2 V)}
    {edgeWeight : Sym2 V → ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G)
    (hcert : IsUniformOddCycleEdgeCertificate q S P cycleWeight M edgeWeight) :
    (∑ H ∈ P, cycleWeight H) ≤ q * k := by
  have hupper := (everySubgraph_iff_everyInducedSubgraph k G).mp hG (S : Set V)
  have hlower := uniformOddCycleEdgeCertificate_defect hcert
  rw [← SimpleGraph.induce_eq_coe_induce_top] at hupper
  have hcard : (S : Set V).ncard = S.card := by simp
  rw [hcard] at hupper
  let a := (G.induce (S : Set V)).indepNum
  change S.card ≤ 2 * a + k at hupper
  change 2 * q * a + (∑ H ∈ P, cycleWeight H) ≤ q * S.card at hlower
  have hmul : q * S.card ≤ q * (2 * a + k) :=
    Nat.mul_le_mul_left q hupper
  have hmul' : q * S.card ≤ 2 * (q * a) + q * k := by
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  simp only [Nat.mul_assoc] at hlower
  omega

theorem not_uniformOddCycleEdgeCertificate_of_large_cycleWeight
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k q : ℕ}
    {S : Finset V} {P : Finset G.Subgraph}
    {cycleWeight : G.Subgraph → ℕ} {M : Finset (Sym2 V)}
    {edgeWeight : Sym2 V → ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G)
    (hlarge : q * k < ∑ H ∈ P, cycleWeight H) :
    ¬ IsUniformOddCycleEdgeCertificate q S P cycleWeight M edgeWeight := by
  intro hcert
  exact (Nat.not_lt_of_ge
    (uniformOddCycleEdgeCertificate_cycleWeight_le hG hcert)) hlarge

/-- Indexed version of a uniform certificate.  The index type permits
distinct indexed cycles to determine the same underlying subgraph. -/
def IsUniformIndexedOddCycleEdgeCertificate
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (ι : Type*) [Fintype ι] (q : ℕ) (S : Finset V)
    (C : ι → G.Subgraph) (cycleWeight : ι → ℕ)
    (M : Finset (Sym2 V)) (edgeWeight : Sym2 V → ℕ) : Prop :=
  (∀ i, IsOddCycleSubgraph (C i)) ∧
    M ⊆ G.edgeFinset ∧
    ∀ v : V,
      (∑ i : ι, if v ∈ (C i).verts then cycleWeight i else 0) +
        (∑ e ∈ M.filter fun e ↦ v ∈ e, edgeWeight e) =
          if v ∈ S then q else 0

lemma weighted_indexed_cycle_inter_double_count
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] (I : Finset V)
    (C : ι → G.Subgraph) (w : ι → ℕ) :
    (∑ i : ι, w i * (I.filter fun v ↦ v ∈ (C i).verts).card) =
      ∑ v ∈ I, ∑ i : ι, if v ∈ (C i).verts then w i else 0 := by
  simp_rw [Finset.card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_filter]

lemma weighted_indexed_cycle_verts_double_count
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] (C : ι → G.Subgraph) (w : ι → ℕ) :
    (∑ i : ι, w i * (C i).verts.ncard) =
      ∑ v : V, ∑ i : ι, if v ∈ (C i).verts then w i else 0 := by
  have hncard (i : ι) :
      (C i).verts.ncard =
        ((Finset.univ : Finset V).filter fun v ↦ v ∈ (C i).verts).card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext v
    simp
  simp_rw [hncard, Finset.card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_filter]

lemma weighted_sum_indexed_oddCycleSubgraph_independent_inter_defect
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] (C : ι → G.Subgraph) (w : ι → ℕ)
    (hC : ∀ i, IsOddCycleSubgraph (C i))
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    2 * (∑ i : ι, w i * (I.filter fun v ↦ v ∈ (C i).verts).card) +
        (∑ i : ι, w i) ≤
      ∑ i : ι, w i * (C i).verts.ncard := by
  have hterm : ∀ i : ι,
      2 * (w i * (I.filter fun v ↦ v ∈ (C i).verts).card) + w i ≤
        w i * (C i).verts.ncard := by
    intro i
    have hIC : (C i).spanningCoe.IsIndepSet (I : Set V) := by
      intro a ha b hb hab hadj
      exact hI ha hb hab ((C i).adj_sub hadj)
    have hcycle := oddCycleSubgraph_independent_inter_defect (hC i) I hIC
    have hmul := Nat.mul_le_mul_left (w i) hcycle
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hsum :
      (∑ i : ι,
        (2 * (w i * (I.filter fun v ↦ v ∈ (C i).verts).card) + w i)) ≤
        ∑ i : ι, w i * (C i).verts.ncard :=
    Finset.sum_le_sum fun i _ ↦ hterm i
  rw [Finset.sum_add_distrib] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  exact hsum

lemma IsUniformIndexedOddCycleEdgeCertificate.independent_load
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] {q : ℕ} {S I : Finset V}
    {C : ι → G.Subgraph} {cycleWeight : ι → ℕ}
    {M : Finset (Sym2 V)} {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformIndexedOddCycleEdgeCertificate ι q S C cycleWeight M edgeWeight)
    (hIS : I ⊆ S) :
    (∑ i : ι,
        cycleWeight i * (I.filter fun v ↦ v ∈ (C i).verts).card) +
      (∑ e ∈ M,
        edgeWeight e * (I.filter fun v ↦ v ∈ e).card) =
      q * I.card := by
  rw [weighted_indexed_cycle_inter_double_count I C cycleWeight,
    weighted_edge_inter_double_count I M edgeWeight]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v ∈ I,
        ((∑ i : ι, if v ∈ (C i).verts then cycleWeight i else 0) +
          ∑ e ∈ M.filter (fun e ↦ v ∈ e), edgeWeight e) =
        ∑ v ∈ I, q := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa [hIS hv] using hcert.2.2 v
    _ = q * I.card := by simp [Nat.mul_comm]

lemma IsUniformIndexedOddCycleEdgeCertificate.total_load
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] {q : ℕ} {S : Finset V}
    {C : ι → G.Subgraph} {cycleWeight : ι → ℕ}
    {M : Finset (Sym2 V)} {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformIndexedOddCycleEdgeCertificate ι q S C cycleWeight M edgeWeight) :
    (∑ i : ι, cycleWeight i * (C i).verts.ncard) +
        2 * (∑ e ∈ M, edgeWeight e) =
      q * S.card := by
  rw [weighted_indexed_cycle_verts_double_count C cycleWeight,
    weighted_edge_verts_double_count M edgeWeight hcert.2.1]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ v : V,
        ((∑ i : ι, if v ∈ (C i).verts then cycleWeight i else 0) +
          ∑ e ∈ M.filter (fun e ↦ v ∈ e), edgeWeight e) =
        ∑ v : V, if v ∈ S then q else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact hcert.2.2 v
    _ = q * S.card := by simp [Nat.mul_comm]

/-- Defect inequality for indexed uniform certificates. -/
theorem uniformIndexedOddCycleEdgeCertificate_defect
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {ι : Type*} [Fintype ι] {q : ℕ} {S : Finset V}
    {C : ι → G.Subgraph} {cycleWeight : ι → ℕ}
    {M : Finset (Sym2 V)} {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformIndexedOddCycleEdgeCertificate ι q S C cycleWeight M edgeWeight) :
    2 * q * (G.induce (S : Set V)).indepNum +
        (∑ i : ι, cycleWeight i) ≤ q * S.card := by
  obtain ⟨I, hIind, hIcard⟩ :=
    (G.induce (S : Set V)).exists_isNIndepSet_indepNum
  let Ihost : Finset V := I.image Subtype.val
  have hIhostcard : Ihost.card = I.card := by
    rw [Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hIhostS : Ihost ⊆ S := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hv
    exact u.property
  have hIhostIndep : G.IsIndepSet (Ihost : Set V) := by
    intro u hu v hv huv hadj
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact hIind hu' hv' (fun h ↦ huv (congrArg Subtype.val h)) hadj
  have hcycles := weighted_sum_indexed_oddCycleSubgraph_independent_inter_defect
    C cycleWeight hcert.1 Ihost hIhostIndep
  have hedges := weighted_sum_edge_independent_inter
    M edgeWeight hcert.2.1 Ihost hIhostIndep
  have hindload := hcert.independent_load hIhostS
  have htotload := hcert.total_load
  rw [hIhostcard, hIcard] at hindload
  have hedges2 := Nat.mul_le_mul_left 2 hedges
  rw [Nat.mul_assoc, ← hindload, ← htotload]
  omega

/-- Under hereditary independence defect `k`, an indexed certificate has
total odd-cycle weight at most `q*k`. -/
theorem uniformIndexedOddCycleEdgeCertificate_cycleWeight_le
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k q : ℕ}
    {ι : Type*} [Fintype ι] {S : Finset V}
    {C : ι → G.Subgraph} {cycleWeight : ι → ℕ}
    {M : Finset (Sym2 V)} {edgeWeight : Sym2 V → ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G)
    (hcert : IsUniformIndexedOddCycleEdgeCertificate ι q S C cycleWeight M edgeWeight) :
    (∑ i : ι, cycleWeight i) ≤ q * k := by
  have hupper := (everySubgraph_iff_everyInducedSubgraph k G).mp hG (S : Set V)
  have hlower := uniformIndexedOddCycleEdgeCertificate_defect hcert
  rw [← SimpleGraph.induce_eq_coe_induce_top] at hupper
  have hcard : (S : Set V).ncard = S.card := by simp
  rw [hcard] at hupper
  let a := (G.induce (S : Set V)).indepNum
  change S.card ≤ 2 * a + k at hupper
  change 2 * q * a + (∑ i : ι, cycleWeight i) ≤ q * S.card at hlower
  have hmul : q * S.card ≤ q * (2 * a + k) := Nat.mul_le_mul_left q hupper
  have hmul' : q * S.card ≤ 2 * (q * a) + q * k := by
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  simp only [Nat.mul_assoc] at hlower
  omega

/-- The injective map on unordered vertex pairs induced by a vertex
embedding.  This is the edge map used to transport the auxiliary edge
weights in a uniform certificate. -/
def sym2Embedding {V W : Type*} (f : V ↪ W) : Sym2 V ↪ Sym2 W :=
  ⟨Sym2.map f, Sym2.map.injective f.injective⟩

lemma mem_sym2Embedding_iff {V W : Type*} (f : V ↪ W)
    (x : V) (e : Sym2 V) :
    f x ∈ sym2Embedding f e ↔ x ∈ e := by
  change f x ∈ Sym2.map f e ↔ x ∈ e
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact (f.injective hfy).symm ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Extend an edge-weight function by zero along an injective map of
vertices.  Writing this as a finite preimage sum avoids choosing a partial
inverse and is convenient for later composition. -/
def mapEdgeWeight {V W : Type*} (f : V ↪ W)
    (M : Finset (Sym2 V)) (edgeWeight : Sym2 V → ℕ) : Sym2 W → ℕ :=
  fun z ↦ ∑ e ∈ M, if sym2Embedding f e = z then edgeWeight e else 0

@[simp] lemma mapEdgeWeight_apply_map {V W : Type*} (f : V ↪ W)
    (M : Finset (Sym2 V)) (edgeWeight : Sym2 V → ℕ) (e : Sym2 V)
    (he : e ∈ M) :
    mapEdgeWeight f M edgeWeight (sym2Embedding f e) = edgeWeight e := by
  unfold mapEdgeWeight
  rw [Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    simp [hbe, (sym2Embedding f).injective.eq_iff]
  · simp [he]

lemma sum_mapEdgeWeight_incident {V W : Type*} (f : V ↪ W)
    (M : Finset (Sym2 V)) (edgeWeight : Sym2 V → ℕ) (x : V) :
    (∑ e ∈ (M.map (sym2Embedding f)).filter fun e ↦ f x ∈ e,
        mapEdgeWeight f M edgeWeight e) =
      ∑ e ∈ M.filter fun e ↦ x ∈ e, edgeWeight e := by
  rw [Finset.sum_filter, Finset.sum_map, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [mapEdgeWeight_apply_map f M edgeWeight e he]
  simp only [mem_sym2Embedding_iff]

/-- Indexed uniform certificates, including their auxiliary edge weights,
transport along graph embeddings without changing their load or total cycle
weight. -/
lemma IsUniformIndexedOddCycleEdgeCertificate.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W}
    {ι : Type*} [Fintype ι] {q : ℕ} {S : Finset V}
    {C : ι → G.Subgraph} {cycleWeight : ι → ℕ}
    {M : Finset (Sym2 V)} {edgeWeight : Sym2 V → ℕ}
    (hcert : IsUniformIndexedOddCycleEdgeCertificate
      ι q S C cycleWeight M edgeWeight)
    (f : G ↪g G') :
    IsUniformIndexedOddCycleEdgeCertificate ι q
      (S.map f.toEmbedding) (fun i ↦ (C i).map f.toHom) cycleWeight
      (M.map (sym2Embedding f.toEmbedding))
      (mapEdgeWeight f.toEmbedding M edgeWeight) := by
  refine ⟨fun i ↦ (hcert.1 i).map_embedding f, ?_, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he
    have heG : e0 ∈ G.edgeFinset := hcert.2.1 he0
    rw [SimpleGraph.mem_edgeFinset] at heG ⊢
    induction e0 using Sym2.inductionOn with
    | _ x y =>
      simpa [sym2Embedding] using f.map_rel_iff.mpr heG
  · intro w
    by_cases hw : w ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hw
      have hcycle (i : ι) :
          f x ∈ ((C i).map f.toHom).verts ↔ x ∈ (C i).verts := by
        constructor
        · rintro ⟨y, hy, hfy⟩
          exact (f.injective hfy).symm ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      simp_rw [hcycle]
      have hedge := sum_mapEdgeWeight_incident
        f.toEmbedding M edgeWeight x
      have hedge' :
          (∑ e ∈ (M.map (sym2Embedding f.toEmbedding)).filter fun e ↦ f x ∈ e,
            mapEdgeWeight f.toEmbedding M edgeWeight e) =
            ∑ e ∈ M.filter (fun e ↦ x ∈ e), edgeWeight e := by
        simpa using hedge
      rw [hedge']
      simpa using hcert.2.2 x
    · have hcyclezero :
          (∑ i : ι,
            if w ∈ ((C i).map f.toHom).verts then cycleWeight i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        rintro ⟨x, -, hxw⟩
        exact hw ⟨x, hxw⟩
      have hedgezero :
          (∑ e ∈ (M.map (sym2Embedding f.toEmbedding)).filter fun e ↦ w ∈ e,
            mapEdgeWeight f.toEmbedding M edgeWeight e) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [Finset.mem_filter] at he
        obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he.1
        exfalso
        have hew := he.2
        change w ∈ Sym2.map f.toEmbedding e0 at hew
        rw [Sym2.mem_map] at hew
        obtain ⟨x, -, hxw⟩ := hew
        exact hw ⟨x, hxw⟩
      have hwS : w ∉ S.map f.toEmbedding := by
        intro hws
        obtain ⟨x, -, hxw⟩ := Finset.mem_map.mp hws
        exact hw ⟨x, hxw⟩
      rw [hcyclezero, hedgezero]
      simp [hwS]

/-- A bundled certificate whose total odd-cycle weight is strictly larger
than `r` times its uniform load.  The index type is normalized to `Fin t`,
which keeps this proposition in the same universe as the host graph while
still representing arbitrary finite indexed families. -/
def HasLargeUniformIndexedOddCycleEdgeCertificate
    {V : Type*} [Fintype V] (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (t q : ℕ) (S : Finset V) (C : Fin t → G.Subgraph)
      (cycleWeight : Fin t → ℕ) (M : Finset (Sym2 V))
      (edgeWeight : Sym2 V → ℕ),
    IsUniformIndexedOddCycleEdgeCertificate
      (Fin t) q S C cycleWeight M edgeWeight ∧
      q * r < ∑ i : Fin t, cycleWeight i

/-- Large uniform certificates transport along graph embeddings. -/
lemma HasLargeUniformIndexedOddCycleEdgeCertificate.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {r : ℕ}
    (hcert : HasLargeUniformIndexedOddCycleEdgeCertificate r G)
    (f : G ↪g G') :
    HasLargeUniformIndexedOddCycleEdgeCertificate r G' := by
  obtain ⟨t, q, S, C, cycleWeight, M, edgeWeight, huniform, hlarge⟩ := hcert
  exact ⟨t, q, S.map f.toEmbedding, (fun i ↦ (C i).map f.toHom),
    cycleWeight, M.map (sym2Embedding f.toEmbedding),
    mapEdgeWeight f.toEmbedding M edgeWeight,
    huniform.map_embedding f, hlarge⟩

/-- The hereditary defect-`k` hypothesis excludes every certificate whose
cycle weight is larger than `k` times its uniform load. -/
theorem not_hasLargeUniformIndexedOddCycleEdgeCertificate
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G) :
    ¬ HasLargeUniformIndexedOddCycleEdgeCertificate k G := by
  rintro ⟨t, q, S, C, cycleWeight, M, edgeWeight, huniform, hlarge⟩
  exact (Nat.not_lt_of_ge
    (uniformIndexedOddCycleEdgeCertificate_cycleWeight_le hG huniform)) hlarge

/-- A concrete hereditary stable-set obstruction: some subgraph has additive
independence defect at least `r`.  Unlike a particular weighted certificate,
this is the intrinsic obstruction that an odd subdivision must preserve. -/
def HasIndependenceDefectAtLeast {V : Type*} [Fintype V]
    (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ H : G.Subgraph, 2 * H.coe.indepNum + r ≤ H.verts.ncard

/-- Independence-defect witnesses transport through ordinary subgraph
copies; extra edges in the host are discarded in the copied subgraph. -/
lemma HasIndependenceDefectAtLeast.map_copy
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {r : ℕ}
    (h : HasIndependenceDefectAtLeast r G) (f : SimpleGraph.Copy G G') :
    HasIndependenceDefectAtLeast r G' := by
  obtain ⟨H, hH⟩ := h
  let hcopy : SimpleGraph.Copy H.coe G := ⟨H.hom, H.hom_injective⟩
  let c : SimpleGraph.Copy H.coe G' := f.comp hcopy
  let K : G'.Subgraph := c.toSubgraph
  let e : H.coe ≃g K.coe := c.isoToSubgraph
  refine ⟨K, ?_⟩
  have hindep : H.coe.indepNum = K.coe.indepNum := indepNum_eq_of_iso e
  have hcard : H.verts.ncard = K.verts.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e.toEquiv
  simpa only [← hindep, ← hcard] using hH

/-- Independence-defect witnesses transport along graph embeddings. -/
lemma HasIndependenceDefectAtLeast.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {r : ℕ}
    (h : HasIndependenceDefectAtLeast r G) (f : G ↪g G') :
    HasIndependenceDefectAtLeast r G' := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H.map f.toHom, ?_⟩
  let e : H.coe ≃g (H.map f.toHom).coe := f.toCopy.isoSubgraphMap H
  have hindep : H.coe.indepNum = (H.map f.toHom).coe.indepNum :=
    indepNum_eq_of_iso e
  have hcard : H.verts.ncard = (H.map f.toHom).verts.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e.toEquiv
  simpa only [← hindep, ← hcard] using hH

/-- A parameter-`k` graph has no subgraph of defect `k+1`. -/
theorem not_hasIndependenceDefectAtLeast_succ
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G) :
    ¬ HasIndependenceDefectAtLeast (k + 1) G := by
  rintro ⟨H, hH⟩
  have hupper := hG H
  omega

/-- Every large uniform cycle-edge certificate yields the corresponding
intrinsic independence-defect witness.  This lets the structural layer
forget the certificate after its local counting work is complete. -/
theorem hasIndependenceDefectAtLeast_succ_of_largeCertificate
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    (h : HasLargeUniformIndexedOddCycleEdgeCertificate r G) :
    HasIndependenceDefectAtLeast (r + 1) G := by
  obtain ⟨t, q, S, C, cycleWeight, M, edgeWeight, hcert, hlarge⟩ := h
  have hdef := uniformIndexedOddCycleEdgeCertificate_defect hcert
  have hq : 0 < q := by
    by_contra hq0
    have : q = 0 := Nat.eq_zero_of_not_pos hq0
    subst q
    simp only [Nat.zero_mul] at hdef hlarge
    omega
  have hmul_lt : q * (2 * (G.induce (S : Set V)).indepNum + r) <
      q * S.card := by
    calc
      q * (2 * (G.induce (S : Set V)).indepNum + r) =
          2 * q * (G.induce (S : Set V)).indepNum + q * r := by
        rw [Nat.mul_add]
        congr 1
        ac_rfl
      _ < 2 * q * (G.induce (S : Set V)).indepNum +
          ∑ i : Fin t, cycleWeight i := Nat.add_lt_add_left hlarge _
      _ ≤ q * S.card := hdef
  have hbase : 2 * (G.induce (S : Set V)).indepNum + r < S.card :=
    (Nat.mul_lt_mul_left hq).mp hmul_lt
  let f : SimpleGraph.Copy (G.induce (S : Set V)) G :=
    SimpleGraph.Copy.induce G (S : Set V)
  refine ⟨f.toSubgraph, ?_⟩
  let e : G.induce (S : Set V) ≃g f.toSubgraph.coe := f.isoToSubgraph
  have hindep : (G.induce (S : Set V)).indepNum = f.toSubgraph.coe.indepNum :=
    indepNum_eq_of_iso e
  have hcard : f.toSubgraph.verts.ncard = S.card := by
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card f.toSubgraph.verts = Nat.card {v : V // v ∈ (S : Set V)} :=
        (Nat.card_congr e.toEquiv).symm
      _ = S.card := by simp
  rw [← hindep, hcard]
  omega

/-- An exact twofold odd-cycle cover of a vertex set: there are `2r` odd
cycles and every vertex of `S` occurs in exactly two of them, while vertices
outside `S` occur in none.  This is a particularly clean special case of
`IsUniformOddCycleEdgeCertificate`; the general weighted cycle-edge form is
the one robust under arbitrary path subdivisions. -/
def IsExactDoubleOddCycleCover {V : Type*} [Fintype V]
    {G : SimpleGraph V} (r : ℕ) (S : Finset V)
    (P : Finset G.Subgraph) : Prop :=
  (∀ H ∈ P, IsOddCycleSubgraph H) ∧ P.card = 2 * r ∧
    ∀ v : V, (P.filter fun H ↦ v ∈ H.verts).card =
      if v ∈ S then 2 else 0

/-- A fixed-parameter instance of the integral packing/deletion/exact-cover
trichotomy, quantified over every finite vertex type. -/
def ExactDoubleCoverDichotomy (p r C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ G : SimpleGraph V,
    HasOddCyclePacking p G ∨ BipartiteAfterDeletingAtMost C G ∨
      ∃ (S : Finset V) (P : Finset G.Subgraph),
        IsExactDoubleOddCycleCover r S P

/-- Exact double-cover certificates transport along graph embeddings without
changing their rank or incidence multiplicities. -/
lemma IsExactDoubleOddCycleCover.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {r : ℕ}
    {S : Finset V} {P : Finset G.Subgraph}
    (hcov : IsExactDoubleOddCycleCover r S P) (f : G ↪g G') :
    IsExactDoubleOddCycleCover r (S.map f.toEmbedding)
      (P.image fun H ↦ H.map f.toHom) := by
  let mapSub : G.Subgraph → G'.Subgraph := fun H ↦ H.map f.toHom
  have hmapinj : Function.Injective mapSub :=
    subgraphMap_injective_of_embedding f
  constructor
  · intro H hH
    obtain ⟨K, hKP, rfl⟩ := Finset.mem_image.mp hH
    exact (hcov.1 K hKP).map_embedding f
  constructor
  · rw [Finset.card_image_of_injective _ hmapinj]
    exact hcov.2.1
  · intro w
    by_cases hw : w ∈ Set.range f
    · obtain ⟨v, rfl⟩ := hw
      have hmem : ∀ K : G.Subgraph,
          f v ∈ (mapSub K).verts ↔ v ∈ K.verts := by
        intro K
        constructor
        · rintro ⟨u, huK, huv⟩
          exact (f.injective huv).symm ▸ huK
        · intro hvK
          exact ⟨v, hvK, rfl⟩
      have hfilter :
          (P.image mapSub).filter (fun K ↦ f v ∈ K.verts) =
            (P.filter fun K ↦ v ∈ K.verts).image mapSub := by
        ext K
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨L, hLP, hLK⟩, hfvK⟩
          subst K
          exact ⟨L, ⟨hLP, (hmem L).mp hfvK⟩, rfl⟩
        · rintro ⟨L, ⟨hLP, hvL⟩, hLK⟩
          subst K
          exact ⟨⟨L, hLP, rfl⟩, (hmem L).mpr hvL⟩
      rw [hfilter, Finset.card_image_of_injective _ hmapinj, hcov.2.2 v]
      simp
    · have hempty :
          (P.image mapSub).filter (fun K ↦ w ∈ K.verts) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro K hK
        obtain ⟨L, hLP, rfl⟩ := Finset.mem_image.mp hK
        intro hwmap
        obtain ⟨v, -, hvw⟩ := hwmap
        exact hw ⟨v, hvw⟩
      have hwS : w ∉ S.map f.toEmbedding := by
        intro hwmap
        obtain ⟨v, -, hvw⟩ := Finset.mem_map.mp hwmap
        exact hw ⟨v, hvw⟩
      rw [hempty]
      simp [hwS]

/-- The exact-cover trichotomy is stable under the low-separation induction
step.  A cover outcome on either induced side embeds into the host.  In the
remaining cases, an integral side packing is enlarged using the odd cycle
on the opposite exclusive side, while two deletion outcomes glue through
the separator. -/
theorem exactDoubleCoverDichotomy_step_of_twoSidedOddSeparation
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p r C : ℕ) (hsep : IsVertexSeparation G A B)
    (hoddA : ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hoddB : ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hA : HasOddCyclePacking p
          (G.induce (((A \ B : Finset V) : Set V))) ∨
        BipartiteAfterDeletingAtMost C
          (G.induce (((A \ B : Finset V) : Set V))) ∨
        ∃ (S : Finset {v // v ∈ (((A \ B : Finset V) : Set V))})
            (P : Finset
              (G.induce (((A \ B : Finset V) : Set V))).Subgraph),
          IsExactDoubleOddCycleCover r S P)
    (hB : HasOddCyclePacking p
          (G.induce (((B \ A : Finset V) : Set V))) ∨
        BipartiteAfterDeletingAtMost C
          (G.induce (((B \ A : Finset V) : Set V))) ∨
        ∃ (S : Finset {v // v ∈ (((B \ A : Finset V) : Set V))})
            (P : Finset
              (G.induce (((B \ A : Finset V) : Set V))).Subgraph),
          IsExactDoubleOddCycleCover r S P) :
    HasOddCyclePacking (p + 1) G ∨
      BipartiteAfterDeletingAtMost (C + C + (A ∩ B).card) G ∨
      ∃ (S : Finset V) (P : Finset G.Subgraph),
        IsExactDoubleOddCycleCover r S P := by
  let SA : Set V := ((A \ B : Finset V) : Set V)
  let SB : Set V := ((B \ A : Finset V) : Set V)
  have hdisj : Disjoint SA SB := by
    rw [Set.disjoint_left]
    intro v hvAB hvBA
    have hvAB' := Finset.mem_sdiff.mp hvAB
    have hvBA' := Finset.mem_sdiff.mp hvBA
    exact hvAB'.2 hvBA'.1
  let fA : G.induce SA ↪g G := SimpleGraph.Embedding.induce SA
  let fB : G.induce SB ↪g G := SimpleGraph.Embedding.induce SB
  rcases hA with hpackA | hdeleteA | ⟨S, P, hcovA⟩
  · exact Or.inl
      (hasOddCyclePacking_succ_of_disjoint_induces
        G hdisj hpackA hoddB)
  · rcases hB with hpackB | hdeleteB | ⟨S, P, hcovB⟩
    · exact Or.inl
        (hasOddCyclePacking_succ_of_disjoint_induces
          G hdisj.symm hpackB hoddA)
    · exact Or.inr (Or.inl
        (bipartiteAfterDeletingAtMost_of_separation
          G A B C C hsep hdeleteA hdeleteB))
    · exact Or.inr (Or.inr
        ⟨S.map fB.toEmbedding, P.image (fun H ↦ H.map fB.toHom),
          hcovB.map_embedding fB⟩)
  · exact Or.inr (Or.inr
      ⟨S.map fA.toEmbedding, P.image (fun H ↦ H.map fA.toHom),
        hcovA.map_embedding fA⟩)

/-- In a counterexample to all three outcomes at parameter `p+1`, the
induction hypothesis rules out a bounded-order separation with odd cycles
on both exclusive sides. -/
theorem no_twoSidedOddSeparation_of_exactDoubleCoverDichotomy
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p r C ℓ D : ℕ)
    (hInd : ExactDoubleCoverDichotomy.{u} p r C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoCover : ¬ ∃ (S : Finset V) (P : Finset G.Subgraph),
      IsExactDoubleOddCycleCover r S P) :
    ¬ ((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) := by
  rintro ⟨hoddA, hoddB⟩
  have hA := hInd _
    (G.induce (((A \ B : Finset V) : Set V)))
  have hB := hInd _
    (G.induce (((B \ A : Finset V) : Set V)))
  rcases exactDoubleCoverDichotomy_step_of_twoSidedOddSeparation
      G A B p r C hsep hoddA hoddB hA hB with
    hpack | hdelete | hcover
  · exact hnoPack hpack
  · apply hnoDelete
    apply hdelete.mono
    exact (Nat.add_le_add_left hsepCard (C + C)).trans hrec
  · exact hnoCover hcover

/-- Every bounded-order separation of a three-outcome counterexample is
oriented by its unique odd exclusive side.  This is the exact integral
orientation needed by the normalized Reed bramble. -/
theorem exactly_one_odd_side_of_exactDoubleCoverDichotomy
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p r C ℓ D : ℕ)
    (hInd : ExactDoubleCoverDichotomy.{u} p r C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoCover : ¬ ∃ (S : Finset V) (P : Finset G.Subgraph),
      IsExactDoubleOddCycleCover r S P) :
    (((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∨
      ((∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H)) := by
  let GA : SimpleGraph {v : V // v ∈ (((A \ B : Finset V) : Set V))} :=
    G.induce (((A \ B : Finset V) : Set V))
  let GB : SimpleGraph {v : V // v ∈ (((B \ A : Finset V) : Set V))} :=
    G.induce (((B \ A : Finset V) : Set V))
  have hnotBoth := no_twoSidedOddSeparation_of_exactDoubleCoverDichotomy
    G A B p r C ℓ D hInd hsep hsepCard hrec hnoPack hnoDelete hnoCover
  by_cases hoddA : ∃ H : GA.Subgraph, IsOddCycleSubgraph H
  · by_cases hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H
    · exact (hnotBoth ⟨hoddA, hoddB⟩).elim
    · exact Or.inl ⟨hoddA, hoddB⟩
  · have hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H := by
      by_contra hnotB
      have hbipA : GA.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GA).2 hoddA
      have hbipB : GB.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GB).2 hnotB
      have hdelete : BipartiteAfterDeletingAtMost
          (0 + 0 + (A ∩ B).card) G :=
        bipartiteAfterDeletingAtMost_of_separation G A B 0 0 hsep
          ((bipartiteAfterDeletingAtMost_zero_iff GA).2 hbipA)
          ((bipartiteAfterDeletingAtMost_zero_iff GB).2 hbipB)
      apply hnoDelete
      apply hdelete.mono
      omega
    exact Or.inr ⟨hoddB, hoddA⟩

/-- The normalized odd-side bramble of a three-outcome counterexample has
order at least `ℓ`.  The proof is the same component/separator
normalization used in Reed's induction, now with the exact-cover outcome
explicitly excluded. -/
theorem lowOrderOddSides_brambleOrderAtLeast_of_exactDoubleCoverDichotomy
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (p r C ℓ D : ℕ)
    (hInd : ExactDoubleCoverDichotomy.{u} p r C)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoCover : ¬ ∃ (S : Finset V) (P : Finset G.Subgraph),
      IsExactDoubleOddCycleCover r S P) :
    BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) := by
  apply brambleOrderAtLeast_of_small_set_misses
  intro X hXcard
  have hXD : X.card ≤ D := by omega
  have hnBip : ¬ (G.induce (X : Set V)ᶜ).IsBipartite := by
    intro hbip
    exact hnoDelete ⟨X, hXD, hbip⟩
  have hodd : ∃ H : (G.induce (X : Set V)ᶜ).Subgraph,
      IsOddCycleSubgraph H := by
    by_contra hno
    exact hnBip
      ((isBipartite_iff_no_oddCycleSubgraph
        (G.induce (X : Set V)ᶜ)).2 hno)
  obtain ⟨H, hH⟩ := hodd
  obtain ⟨c, K, hK⟩ := exists_odd_componentVertices G X H hH
  let T := componentVertices G X c
  let N := externalNeighborhood G T
  have hTN : N = externalNeighborhood G T := rfl
  have hTconn : (G.induce (T : Set V)).Connected :=
    componentVertices_connected G X c
  have hTX : Disjoint T X := componentVertices_disjoint_delete G X c
  have hNX : N ⊆ X := component_externalNeighborhood_subset_delete G X c
  have hNcard : N.card ≤ ℓ := by
    exact (Finset.card_le_card hNX).trans (Nat.le_of_lt hXcard)
  have horient := exactly_one_odd_side_of_exactDoubleCoverDichotomy
    G (Finset.univ \ T) (T ∪ N) p r C ℓ D hInd
      (by simpa only [hTN] using separation_externalNeighborhood G T)
      (by simpa only [hTN, inter_externalNeighborhood] using hNcard)
      hrec hnoPack hnoDelete hnoCover
  dsimp [N] at horient
  have hleftEq := leftDiff_externalNeighborhood G T
  have hrightEq := rightDiff_externalNeighborhood G T
  rw [hleftEq, hrightEq] at horient
  have horient' :
      (((∃ H : (G.induce (((Finset.univ \
          (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∨
        ((∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (((Finset.univ \
            (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
              IsOddCycleSubgraph H)) := by
    exact horient
  have hTcycle : ∃ H : (G.induce (T : Set V)).Subgraph,
      IsOddCycleSubgraph H := ⟨K, hK⟩
  have hotherNoOdd :
      ¬ ∃ H : (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H := by
    rcases horient' with hleft | hright
    · exact (hleft.2 hTcycle).elim
    · exact hright.2
  have hotherBip :
      (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).IsBipartite :=
    (isBipartite_iff_no_oddCycleSubgraph _).2 hotherNoOdd
  refine ⟨T, (mem_lowOrderOddSides G ℓ T).2
    ⟨hTconn, hTcycle, ?_, hotherBip⟩, hTX.symm⟩
  simpa only [hTN] using hNcard

/-- A recursive two-colour Ramsey bound.  No quantitative sharpness is
needed in the perimeter-path argument; only finiteness and uniformity matter.
The off-diagonal recursion is the usual proof by choosing one point and
partitioning the remaining points according to its colour. -/
def twoColorRamseyBound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _, 0 => 0
  | a + 1, b + 1 =>
      twoColorRamseyBound a (b + 1) +
        twoColorRamseyBound (a + 1) b + 1
termination_by a b => a + b

/-- Finite two-colour Ramsey theorem for an arbitrary symmetric relation.
Applied to crossing of disjoint perimeter endpoint-pairs, this supplies the
homogeneous crossing/noncrossing family in the source proof of
Kawarabayashi--Reed Lemma 6.3. -/
theorem exists_pairwise_or_pairwise_compl
    {α : Type*} (R : α → α → Prop) (hR : Std.Symm R)
    (a b : ℕ) (s : Finset α)
    (hs : twoColorRamseyBound a b ≤ s.card) :
    ∃ t : Finset α, t ⊆ s ∧
      ((a ≤ t.card ∧ (t : Set α).Pairwise R) ∨
        (b ≤ t.card ∧ (t : Set α).Pairwise fun x y ↦ ¬ R x y)) := by
  match a, b with
  | 0, b =>
      exact ⟨∅, by simp, Or.inl ⟨by simp, by simp⟩⟩
  | a + 1, 0 =>
      exact ⟨∅, by simp, Or.inr ⟨by simp, by simp⟩⟩
  | a + 1, b + 1 =>
      have hspos : 0 < s.card := by
        rw [twoColorRamseyBound] at hs
        omega
      obtain ⟨x, hxs⟩ := Finset.card_pos.mp hspos
      let u := s.erase x
      let n := u.filter fun y ↦ R x y
      let m := u.filter fun y ↦ ¬ R x y
      have hcardu : u.card + 1 = s.card := Finset.card_erase_add_one hxs
      have hpartition : n.card + m.card = u.card := by
        exact Finset.card_filter_add_card_filter_not (s := u) (fun y ↦ R x y)
      have hlarge :
          twoColorRamseyBound a (b + 1) ≤ n.card ∨
            twoColorRamseyBound (a + 1) b ≤ m.card := by
        by_contra h
        push Not at h
        rw [twoColorRamseyBound] at hs
        omega
      rcases hlarge with hn | hm
      · obtain ⟨t, htn, ht⟩ :=
          exists_pairwise_or_pairwise_compl R hR a (b + 1) n hn
        rcases ht with htred | htblue
        · refine ⟨insert x t, ?_, Or.inl ⟨?_, ?_⟩⟩
          · intro y hy
            simp only [Finset.mem_insert] at hy
            rcases hy with rfl | hyt
            · exact hxs
            · have hyn := htn hyt
              simp only [n, Finset.mem_filter] at hyn
              exact Finset.mem_of_mem_erase hyn.1
          · have hxt : x ∉ t := by
              intro hxt
              have hyn := htn hxt
              simp only [n, Finset.mem_filter] at hyn
              exact Finset.notMem_erase x s hyn.1
            rw [Finset.card_insert_of_notMem hxt]
            exact Nat.succ_le_succ htred.1
          · rw [Finset.coe_insert, Set.pairwise_insert]
            refine ⟨htred.2, ?_⟩
            intro y hyt hxy
            have hyn : y ∈ n := htn hyt
            have hxyR : R x y := Finset.mem_filter.mp hyn |>.2
            exact ⟨hxyR, hR.symm x y hxyR⟩
        · exact ⟨t, htn.trans (by
              intro y hyn
              simp only [n, Finset.mem_filter] at hyn
              exact Finset.mem_of_mem_erase hyn.1),
            Or.inr htblue⟩
      · obtain ⟨t, htm, ht⟩ :=
          exists_pairwise_or_pairwise_compl R hR (a + 1) b m hm
        rcases ht with htred | htblue
        · exact ⟨t, htm.trans (by
              intro y hym
              simp only [m, Finset.mem_filter] at hym
              exact Finset.mem_of_mem_erase hym.1),
            Or.inl htred⟩
        · refine ⟨insert x t, ?_, Or.inr ⟨?_, ?_⟩⟩
          · intro y hy
            simp only [Finset.mem_insert] at hy
            rcases hy with rfl | hyt
            · exact hxs
            · have hym := htm hyt
              simp only [m, Finset.mem_filter] at hym
              exact Finset.mem_of_mem_erase hym.1
          · have hxt : x ∉ t := by
              intro hxt
              have hym := htm hxt
              simp only [m, Finset.mem_filter] at hym
              exact Finset.notMem_erase x s hym.1
            rw [Finset.card_insert_of_notMem hxt]
            exact Nat.succ_le_succ htblue.1
          · rw [Finset.coe_insert, Set.pairwise_insert]
            refine ⟨htblue.2, ?_⟩
            intro y hyt hxy
            have hym : y ∈ m := htm hyt
            have hxyN : ¬ R x y := Finset.mem_filter.mp hym |>.2
            exact ⟨hxyN, fun hyxR ↦ hxyN (hR.symm y x hyxR)⟩
termination_by a + b
decreasing_by all_goals omega

/-- The high-connectivity input isolated by the Reed induction.  Once the
normalized odd-side bramble has order at least `ℓ`, the controlled-wall
argument must produce the requested integral packing, a deletion set of
size `D`, or an exact double-cover certificate. -/
def HighOrderOddSideBrambleTrichotomy
    (q r ℓ D : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ G : SimpleGraph V,
    IsFiniteBramble G (lowOrderOddSides G ℓ) →
    BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) →
    HasOddCyclePacking q G ∨ BipartiteAfterDeletingAtMost D G ∨
      ∃ (S : Finset V) (P : Finset G.Subgraph),
        IsExactDoubleOddCycleCover r S P

/-- All low-order-separation work in the induction is discharged by the
normalized bramble theorem.  Thus one high-order bramble trichotomy at
parameter `p+1`, together with the numerical recurrence, advances the
fixed-parameter exact-cover dichotomy from `p` to `p+1`. -/
theorem exactDoubleCoverDichotomy_succ_of_highOrderBramble
    (p r C ℓ D : ℕ)
    (hInd : ExactDoubleCoverDichotomy.{u} p r C)
    (hrec : C + C + ℓ ≤ D)
    (hhigh : HighOrderOddSideBrambleTrichotomy.{u} (p + 1) r ℓ D) :
    ExactDoubleCoverDichotomy.{u} (p + 1) r D := by
  intro V _ G
  by_cases hpack : HasOddCyclePacking (p + 1) G
  · exact Or.inl hpack
  by_cases hdelete : BipartiteAfterDeletingAtMost D G
  · exact Or.inr (Or.inl hdelete)
  by_cases hcover : ∃ (S : Finset V) (P : Finset G.Subgraph),
      IsExactDoubleOddCycleCover r S P
  · exact Or.inr (Or.inr hcover)
  have hbramble : IsFiniteBramble G (lowOrderOddSides G ℓ) :=
    lowOrderOddSides_isFiniteBramble G ℓ
  have horder : BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) :=
    lowOrderOddSides_brambleOrderAtLeast_of_exactDoubleCoverDichotomy
      G p r C ℓ D hInd hrec hpack hdelete hcover
  rcases hhigh V G hbramble horder with hp | hd | hc
  · exact (hpack hp).elim
  · exact (hdelete hd).elim
  · exact (hcover hc).elim

/-- Uniform controlled-wall input required to run every successor stage of
the induction.  The bound `D` may depend on the previous deletion bound as
well as on `p` and `r`; only its independence of the host graph matters. -/
def ReedHighOrderBrambleStatement : Prop :=
  ∀ p r C : ℕ, ∃ ℓ D : ℕ,
    C + C + ℓ ≤ D ∧
      HighOrderOddSideBrambleTrichotomy.{u} (p + 1) r ℓ D

lemma IsExactDoubleOddCycleCover.sum_inter_eq_double
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    {S I : Finset V} {P : Finset G.Subgraph}
    (hcov : IsExactDoubleOddCycleCover r S P) (hIS : I ⊆ S) :
    ∑ H ∈ P, (I.filter fun v ↦ v ∈ H.verts).card = 2 * I.card := by
  have hdouble :
      ∑ H ∈ P, (I.filter fun v ↦ v ∈ H.verts).card =
        ∑ v ∈ I, (P.filter fun H ↦ v ∈ H.verts).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hdouble]
  calc
    ∑ v ∈ I, (P.filter fun H ↦ v ∈ H.verts).card =
        ∑ v ∈ I, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hcov.2.2 v, if_pos (hIS hv)]
    _ = 2 * I.card := by simp [Nat.mul_comm]

lemma IsExactDoubleOddCycleCover.sum_verts_eq_double
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    {S : Finset V} {P : Finset G.Subgraph}
    (hcov : IsExactDoubleOddCycleCover r S P) :
    ∑ H ∈ P, H.verts.ncard = 2 * S.card := by
  have hncard (H : G.Subgraph) :
      H.verts.ncard =
        ((Finset.univ : Finset V).filter fun v ↦ v ∈ H.verts).card := by
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext v
    simp
  have hdouble :
      ∑ H ∈ P, H.verts.ncard =
        ∑ v ∈ (Finset.univ : Finset V),
          (P.filter fun H ↦ v ∈ H.verts).card := by
    simp_rw [hncard, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hdouble]
  calc
    ∑ v ∈ (Finset.univ : Finset V),
        (P.filter fun H ↦ v ∈ H.verts).card =
        ∑ v ∈ (Finset.univ : Finset V), if v ∈ S then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      exact hcov.2.2 v
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- An exact twofold cover by `2r` odd cycles forces ordinary hereditary
independence defect at least `r` on its support. -/
theorem exactDoubleOddCycleCover_defect
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r : ℕ}
    {S : Finset V} {P : Finset G.Subgraph}
    (hcov : IsExactDoubleOddCycleCover r S P) :
    2 * (G.induce (S : Set V)).indepNum + r ≤ S.card := by
  obtain ⟨I, hIind, hIcard⟩ :=
    (G.induce (S : Set V)).exists_isNIndepSet_indepNum
  let Ihost : Finset V := I.image Subtype.val
  have hIhostcard : Ihost.card = I.card := by
    rw [Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hIhostS : Ihost ⊆ S := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hv
    exact u.property
  have hIhostIndep : ∀ H ∈ P,
      H.spanningCoe.IsIndepSet (Ihost : Set V) := by
    intro H _ u hu v hv huv hadj
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    apply hIind hu' hv'
    · exact fun h ↦ huv (congrArg Subtype.val h)
    · change G.Adj u'.1 v'.1
      exact H.adj_sub hadj
  have hsum := sum_oddCycleSubgraph_independent_inter_defect
    P hcov.1 Ihost hIhostIndep
  rw [hcov.sum_inter_eq_double hIhostS,
    hcov.sum_verts_eq_double, hcov.2.1] at hsum
  rw [hIhostcard, hIcard] at hsum
  omega

/-- Consequently, a parameter-`k` graph has no exact double odd-cycle cover
of rank greater than `k`.  This is the stable-set obstruction needed after
extracting such a cover from a tall Escher wall. -/
theorem not_exactDoubleOddCycleCover_of_large_rank
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k r : ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G) (hkr : k < r) :
    ¬ ∃ (S : Finset V) (P : Finset G.Subgraph),
      IsExactDoubleOddCycleCover r S P := by
  rintro ⟨S, P, hcov⟩
  have hupper := (everySubgraph_iff_everyInducedSubgraph k G).mp hG (S : Set V)
  have hlower := exactDoubleOddCycleCover_defect hcov
  rw [← SimpleGraph.induce_eq_coe_induce_top] at hupper
  have hcard : (S : Set V).ncard = S.card := by simp
  rw [hcard] at hupper
  let a := (G.induce (S : Set V)).indepNum
  change S.card ≤ 2 * a + k at hupper
  change 2 * a + r ≤ S.card at hlower
  omega

/-- A certificate-level form of Reed's structural trichotomy.  For fixed
packing size `p` and stable-defect rank `r`, every finite graph either has
`p` disjoint odd cycles, has a uniformly bounded odd-cycle transversal, or
contains an exact double-cover certificate of rank `r`.  The controlled-wall
layer is responsible for proving this proposition. -/
def ReedExactDoubleCoverTrichotomyStatement : Prop :=
  ∀ p r : ℕ, ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    HasOddCyclePacking p G ∨ BipartiteAfterDeletingAtMost C G ∨
      ∃ (S : Finset (Fin n)) (P : Finset G.Subgraph),
        IsExactDoubleOddCycleCover r S P

/-- Every finite graph is bipartite or contains a one-member half-integral
odd-cycle packing.  This is the `p = 1` base case of Reed's half-integral
Erdős--Pósa theorem. -/
theorem hasHalfIntegralOddCyclePacking_one_or_bipartite
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    HasHalfIntegralOddCyclePacking 1 G ∨ G.IsBipartite := by
  by_cases hbip : G.IsBipartite
  · exact Or.inr hbip
  · left
    have hlengths : Erdos58.oddCycleLengths G ≠ ∅ := by
      intro hempty
      exact hbip (Erdos58.colorable_two_of_oddCycleLengths_eq_empty hempty)
    obtain ⟨n, hn⟩ := Set.nonempty_iff_ne_empty.mpr hlengths
    have hnodd : Odd n := Erdos58.odd_of_mem_oddCycleLengths hn
    have hn3 : 3 ≤ n := Erdos58.three_le_of_mem_oddCycleLengths hn
    have hcontained : SimpleGraph.cycleGraph n ⊑ G :=
      ((Erdos58.mem_oddCycleLengths_iff_cycleGraph_isContained hn3).1 hn).2
    let f : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G := hcontained.some
    let H : G.Subgraph := f.toSubgraph
    refine ⟨{H}, by simp, ?_⟩
    constructor
    · intro K hK
      have hKH : K = H := Finset.mem_singleton.mp hK
      subst K
      exact ⟨n, hn3, hnodd, ⟨f.isoToSubgraph⟩⟩
    · intro v
      calc
        (({H} : Finset G.Subgraph).filter fun K ↦ v ∈ K.verts).card ≤
            ({H} : Finset G.Subgraph).card :=
          Finset.card_filter_le _ _
        _ ≤ 2 := by simp

/-- Every finite graph is bipartite or contains one integral odd cycle.
This packages the usual odd-cycle characterization in the canonical
`HasOddCyclePacking` representation. -/
theorem hasOddCyclePacking_one_or_bipartite
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    HasOddCyclePacking 1 G ∨ G.IsBipartite := by
  rcases hasHalfIntegralOddCyclePacking_one_or_bipartite G with
    ⟨P, hPcard, hP⟩ | hbip
  · obtain ⟨H, hHP⟩ : ∃ H, H ∈ P := by
      rw [Finset.card_eq_one] at hPcard
      obtain ⟨H, rfl⟩ := hPcard
      exact ⟨H, by simp⟩
    left
    have hpack := hasOddCyclePacking_of_pairwise_oddCycleSubgraphs
      [H] (by
        intro K hK
        simp only [List.mem_singleton] at hK
        subst K
        exact hP.1 H hHP) (by simp)
    simpa using hpack
  · exact Or.inr hbip

/-- The `p = 1` base case of the integral
packing/deletion/exact-double-cover trichotomy has deletion bound zero; the
cover alternative is not needed. -/
theorem exactDoubleCoverDichotomy_one (r : ℕ) :
    ExactDoubleCoverDichotomy 1 r 0 := by
  intro V _ G
  rcases hasOddCyclePacking_one_or_bipartite G with hpack | hbip
  · exact Or.inl hpack
  · exact Or.inr (Or.inl
      ((bipartiteAfterDeletingAtMost_zero_iff G).2 hbip))

/-- Every graph contains the empty integral odd-cycle packing. -/
theorem hasOddCyclePacking_zero {V : Type*} (G : SimpleGraph V) :
    HasOddCyclePacking 0 G := by
  have h := hasOddCyclePacking_of_pairwise_cycleCopies
    (G := G) [] (by simp)
  simpa using h

/-- The high-order bramble theorem, together with the checked
low-separation recurrence, proves the full integral
packing/deletion/exact-cover trichotomy by induction on the requested
packing size. -/
theorem reedExactDoubleCoverTrichotomy_of_highOrderBramble
    (hhigh : ReedHighOrderBrambleStatement.{0}) :
    ReedExactDoubleCoverTrichotomyStatement := by
  intro p r
  have hall : ∀ q : ℕ, ∃ C : ℕ,
      ExactDoubleCoverDichotomy.{0} q r C := by
    intro q
    induction q with
    | zero =>
        refine ⟨0, ?_⟩
        intro V _ G
        exact Or.inl (hasOddCyclePacking_zero G)
    | succ q ih =>
        obtain ⟨C, hC⟩ := ih
        obtain ⟨ℓ, D, hrec, hstep⟩ := hhigh q r C
        exact ⟨D, exactDoubleCoverDichotomy_succ_of_highOrderBramble
          q r C ℓ D hC hrec hstep⟩
  obtain ⟨C, hC⟩ := hall p
  refine ⟨C, ?_⟩
  intro n G
  exact hC (Fin n) G

/-- The exact one-cycle instance of the half-integral Erdős--Pósa
alternative has deletion bound zero. -/
theorem halfIntegralOddCycleErdosPosa_one :
    ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      HasHalfIntegralOddCyclePacking 1 G ∨
        BipartiteAfterDeletingAtMost C G := by
  refine ⟨0, ?_⟩
  intro n G
  rcases hasHalfIntegralOddCyclePacking_one_or_bipartite G with
    hpack | hbip
  · exact Or.inl hpack
  · right
    refine ⟨∅, by simp, ?_⟩
    rw [SimpleGraph.induce_eq_coe_induce_top]
    exact hbip.subgraph _

/-- A graph satisfying the parameter-zero hypothesis has no one-member
half-integral odd-cycle packing. -/
theorem not_hasHalfIntegralOddCyclePacking_one_of_zero
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : EverySubgraphHasLargeIndepSet 0 G) :
    ¬ HasHalfIntegralOddCyclePacking 1 G := by
  rintro ⟨P, hPcard, hPodd, -⟩
  obtain ⟨H, hHP⟩ : ∃ H, H ∈ P := by
    rw [Finset.card_eq_one] at hPcard
    obtain ⟨H, rfl⟩ := hPcard
    exact ⟨H, by simp⟩
  have hbound := hG H
  have hdefect := oddCycleSubgraph_defect (hPodd H hHP)
  omega

/-- The parameter-zero slice of the uniform near-bipartite packing bound. -/
theorem nearBipartiteHalfIntegralPackingBound_zero :
    ∃ p : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      IsKNearBipartite 0 G →
        ¬ HasHalfIntegralOddCyclePacking p G := by
  refine ⟨1, ?_⟩
  intro n G hnear
  apply not_hasHalfIntegralOddCyclePacking_one_of_zero
  exact (everySubgraph_iff_isKNearBipartite 0 G).mpr hnear

/-- A disjoint union of `p` odd cycles has additive independence deficit at
least `p`. -/
lemma cycleUnionGraph_defect (ns : List ℕ)
    (hns : ∀ n ∈ ns, 3 ≤ n ∧ Odd n) :
    2 * (cycleUnionGraph ns).indepNum + ns.length ≤
      Nat.card (CycleUnionVerts ns) := by
  induction ns with
  | nil => rw [indepNum_cycleUnionGraph, natCard_cycleUnionVerts]; simp
  | cons n ns ih =>
      have hn := hns n (by simp)
      have htail : ∀ m ∈ ns, 3 ≤ m ∧ Odd m := by
        intro m hm
        exact hns m (by simp [hm])
      have hcycle := two_mul_indepNum_cycleGraph_add_one_le hn.1 hn.2
      have hrest := ih htail
      rw [cycleUnionGraph, indepNum_sum, natCard_cycleUnionVerts,
        List.sum_cons, List.length_cons]
      rw [natCard_cycleUnionVerts] at hrest
      omega

/-- The hypothesis of Problem 73 rules out more than `k` vertex-disjoint
odd cycles.  This is the elementary input to Reed's odd-cycle-transversal
theorem. -/
theorem oddCyclePacking_card_le {V : Type*} [Finite V] {k p : ℕ}
    {G : SimpleGraph V} (hG : EverySubgraphHasLargeIndepSet k G)
    (hpack : HasOddCyclePacking p G) : p ≤ k := by
  obtain ⟨ns, hlen, hodd, hcontained⟩ := hpack
  let f : SimpleGraph.Copy (cycleUnionGraph ns) G := hcontained.some
  let H : G.Subgraph := f.toSubgraph
  let e : cycleUnionGraph ns ≃g H.coe := f.isoToSubgraph
  have hverts : H.verts.ncard = Nat.card (CycleUnionVerts ns) := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr e.toEquiv).symm
  have hindep : (cycleUnionGraph ns).indepNum = H.coe.indepNum :=
    indepNum_eq_of_iso e
  have hdefect := cycleUnionGraph_defect ns hodd
  have hbound := hG H
  rw [hverts, ← hindep] at hbound
  rw [hlen] at hdefect
  omega

/-- Under the Problem 73 hypothesis, every pairwise-disjoint subfamily of
bounded-length odd-cycle vertex sets has at most `k` members. -/
theorem disjoint_shortOddCycleVertexSets_card_lt_succ
    {V : Type*} [Fintype V] {G : SimpleGraph V} {L k : ℕ}
    (hG : EverySubgraphHasLargeIndepSet k G)
    (P : Finset (Finset V))
    (hPF : P ⊆ shortOddCycleVertexSets G L)
    (hPdisj : (P : Set (Finset V)).PairwiseDisjoint id) :
    P.card < k + 1 := by
  have hpack :=
    hasOddCyclePacking_of_disjoint_shortOddCycleVertexSets P hPF hPdisj
  exact Nat.lt_succ_iff.mpr (oddCyclePacking_card_le hG hpack)

/-- Elementary bounded-length reduction: after deleting fewer than
`(k+1)L` vertices, no odd-cycle subgraph of length at most `L` remains.
Equivalently, the displayed deletion set meets every such cycle in `G`.

This isolates the genuinely deep part of Reed's theorem: controlling the
remaining graph when all its odd cycles are long. -/
theorem exists_small_set_meeting_every_short_odd_cycle
    {V : Type*} [Fintype V] {G : SimpleGraph V} {L k : ℕ}
    (hL : 0 < L) (hG : EverySubgraphHasLargeIndepSet k G) :
    ∃ X : Finset V, X.card < (k + 1) * L ∧
      ∀ H : G.Subgraph, IsShortOddCycleSubgraph L H →
        ¬ Disjoint H.verts.toFinset X := by
  obtain ⟨X, hXcard, hXhit⟩ :=
    exists_small_hitting_set_of_no_disjoint_subfamily
      (shortOddCycleVertexSets G L) (k + 1) L hL
      (fun _ hA => shortOddCycleVertexSets_nonempty hA)
      (fun _ hA => shortOddCycleVertexSets_card_le hA)
      (fun P hPF hPdisj =>
        disjoint_shortOddCycleVertexSets_card_lt_succ hG P hPF hPdisj)
  refine ⟨X, hXcard, ?_⟩
  intro H hH
  apply hXhit H.verts.toFinset
  rw [shortOddCycleVertexSets, Finset.mem_image]
  exact ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ H, hH⟩, rfl⟩

/-- A graph has no odd-cycle subgraph whose length is at most `L`. -/
def HasNoOddCycleOfLengthAtMost {V : Type*}
    (L : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, ¬ IsShortOddCycleSubgraph L H

/-- Induced-graph form of the bounded-length reduction.  The hereditary
independence hypothesis yields a deletion set of size `< (k+1)L` after whose
removal every odd cycle has length greater than `L`. -/
theorem exists_small_deletion_no_short_odd_cycle
    {V : Type*} [Finite V] {G : SimpleGraph V} {L k : ℕ}
    (hL : 0 < L) (hG : EverySubgraphHasLargeIndepSet k G) :
    ∃ X : Finset V, X.card < (k + 1) * L ∧
      HasNoOddCycleOfLengthAtMost L (G.induce (X : Set V)ᶜ) := by
  let _ := Fintype.ofFinite V
  obtain ⟨X, hXcard, hXmeet⟩ :=
    exists_small_set_meeting_every_short_odd_cycle hL hG
  refine ⟨X, hXcard, ?_⟩
  intro H hH
  obtain ⟨n, hnL, hn3, hnodd, ⟨e⟩⟩ := hH
  let fH : SimpleGraph.Copy (SimpleGraph.cycleGraph n)
      (G.induce (X : Set V)ᶜ) :=
    ⟨H.hom.comp e.toHom, H.hom_injective.comp e.injective⟩
  let f : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G :=
    (SimpleGraph.Copy.induce G (X : Set V)ᶜ).comp fH
  let K : G.Subgraph := f.toSubgraph
  have hKshort : IsShortOddCycleSubgraph L K :=
    ⟨n, hnL, hn3, hnodd, ⟨f.isoToSubgraph⟩⟩
  apply hXmeet K hKshort
  rw [Finset.disjoint_left]
  intro v hvK hvX
  have hvRange : v ∈ Set.range f := by
    rw [← verts_copy_toSubgraph f]
    exact Set.mem_toFinset.mp hvK
  obtain ⟨u, rfl⟩ := hvRange
  change (fH u).1 ∈ X at hvX
  exact (fH u).2 hvX

/-- In particular, a graph satisfying the parameter-`k` hypothesis cannot
contain `k+1` vertex-disjoint odd cycles. -/
theorem not_hasOddCyclePacking_succ {V : Type*} [Finite V] {k : ℕ}
    {G : SimpleGraph V} (hG : EverySubgraphHasLargeIndepSet k G) :
    ¬ HasOddCyclePacking (k + 1) G := by
  intro hpack
  have := oddCyclePacking_card_le hG hpack
  omega

/-- An obstruction predicate that is stable under graph embeddings.  This
abstracts exactly the property needed by the low-separation part of Reed's
induction and lets that argument work with subdivision-robust weighted
certificates. -/
structure EmbeddingStableGraphObstruction where
  Holds : ∀ {V : Type u} [Fintype V], SimpleGraph V → Prop
  map_embedding : ∀ {V W : Type u} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W},
    Holds G → ∀ _f : G ↪g G', Holds G'

/-- The generic packing/deletion/obstruction alternative at one induction
stage. -/
def GraphObstructionDichotomy
    (O : EmbeddingStableGraphObstruction.{u}) (p C : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ G : SimpleGraph V,
    HasOddCyclePacking p G ∨ BipartiteAfterDeletingAtMost C G ∨ O.Holds G

theorem graphObstructionDichotomy_step_of_twoSidedOddSeparation
    (O : EmbeddingStableGraphObstruction.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C : ℕ) (hsep : IsVertexSeparation G A B)
    (hoddA : ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hoddB : ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
      IsOddCycleSubgraph H)
    (hA : HasOddCyclePacking p
          (G.induce (((A \ B : Finset V) : Set V))) ∨
        BipartiteAfterDeletingAtMost C
          (G.induce (((A \ B : Finset V) : Set V))) ∨
        O.Holds (G.induce (((A \ B : Finset V) : Set V))))
    (hB : HasOddCyclePacking p
          (G.induce (((B \ A : Finset V) : Set V))) ∨
        BipartiteAfterDeletingAtMost C
          (G.induce (((B \ A : Finset V) : Set V))) ∨
        O.Holds (G.induce (((B \ A : Finset V) : Set V)))) :
    HasOddCyclePacking (p + 1) G ∨
      BipartiteAfterDeletingAtMost (C + C + (A ∩ B).card) G ∨ O.Holds G := by
  let SA : Set V := ((A \ B : Finset V) : Set V)
  let SB : Set V := ((B \ A : Finset V) : Set V)
  have hdisj : Disjoint SA SB := by
    rw [Set.disjoint_left]
    intro v hvAB hvBA
    have hvAB' := Finset.mem_sdiff.mp hvAB
    have hvBA' := Finset.mem_sdiff.mp hvBA
    exact hvAB'.2 hvBA'.1
  let fA : G.induce SA ↪g G := SimpleGraph.Embedding.induce SA
  let fB : G.induce SB ↪g G := SimpleGraph.Embedding.induce SB
  rcases hA with hpackA | hdeleteA | hobsA
  · exact Or.inl
      (hasOddCyclePacking_succ_of_disjoint_induces G hdisj hpackA hoddB)
  · rcases hB with hpackB | hdeleteB | hobsB
    · exact Or.inl
        (hasOddCyclePacking_succ_of_disjoint_induces G hdisj.symm hpackB hoddA)
    · exact Or.inr (Or.inl
        (bipartiteAfterDeletingAtMost_of_separation
          G A B C C hsep hdeleteA hdeleteB))
    · exact Or.inr (Or.inr (O.map_embedding hobsB fB))
  · exact Or.inr (Or.inr (O.map_embedding hobsA fA))

theorem no_twoSidedOddSeparation_of_graphObstructionDichotomy
    (O : EmbeddingStableGraphObstruction.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C ℓ D : ℕ)
    (hInd : GraphObstructionDichotomy O p C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoObs : ¬ O.Holds G) :
    ¬ ((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) := by
  rintro ⟨hoddA, hoddB⟩
  have hA := hInd _ (G.induce (((A \ B : Finset V) : Set V)))
  have hB := hInd _ (G.induce (((B \ A : Finset V) : Set V)))
  rcases graphObstructionDichotomy_step_of_twoSidedOddSeparation
      O G A B p C hsep hoddA hoddB hA hB with hpack | hdelete | hobs
  · exact hnoPack hpack
  · apply hnoDelete
    apply hdelete.mono
    exact (Nat.add_le_add_left hsepCard (C + C)).trans hrec
  · exact hnoObs hobs

theorem exactly_one_odd_side_of_graphObstructionDichotomy
    (O : EmbeddingStableGraphObstruction.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (A B : Finset V) (p C ℓ D : ℕ)
    (hInd : GraphObstructionDichotomy O p C)
    (hsep : IsVertexSeparation G A B)
    (hsepCard : (A ∩ B).card ≤ ℓ)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoObs : ¬ O.Holds G) :
    (((∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∨
      ((∃ H : (G.induce (((B \ A : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H) ∧
        ¬ ∃ H : (G.induce (((A \ B : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H)) := by
  let GA := G.induce (((A \ B : Finset V) : Set V))
  let GB := G.induce (((B \ A : Finset V) : Set V))
  have hnotBoth := no_twoSidedOddSeparation_of_graphObstructionDichotomy
    O G A B p C ℓ D hInd hsep hsepCard hrec hnoPack hnoDelete hnoObs
  by_cases hoddA : ∃ H : GA.Subgraph, IsOddCycleSubgraph H
  · by_cases hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H
    · exact (hnotBoth ⟨hoddA, hoddB⟩).elim
    · exact Or.inl ⟨hoddA, hoddB⟩
  · have hoddB : ∃ H : GB.Subgraph, IsOddCycleSubgraph H := by
      by_contra hnotB
      have hbipA : GA.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GA).2 hoddA
      have hbipB : GB.IsBipartite :=
        (isBipartite_iff_no_oddCycleSubgraph GB).2 hnotB
      have hdelete : BipartiteAfterDeletingAtMost
          (0 + 0 + (A ∩ B).card) G :=
        bipartiteAfterDeletingAtMost_of_separation G A B 0 0 hsep
          ((bipartiteAfterDeletingAtMost_zero_iff GA).2 hbipA)
          ((bipartiteAfterDeletingAtMost_zero_iff GB).2 hbipB)
      apply hnoDelete
      apply hdelete.mono
      omega
    exact Or.inr ⟨hoddB, hoddA⟩

theorem lowOrderOddSides_brambleOrderAtLeast_of_graphObstructionDichotomy
    (O : EmbeddingStableGraphObstruction.{u})
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (p C ℓ D : ℕ)
    (hInd : GraphObstructionDichotomy O p C)
    (hrec : C + C + ℓ ≤ D)
    (hnoPack : ¬ HasOddCyclePacking (p + 1) G)
    (hnoDelete : ¬ BipartiteAfterDeletingAtMost D G)
    (hnoObs : ¬ O.Holds G) :
    BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) := by
  apply brambleOrderAtLeast_of_small_set_misses
  intro X hXcard
  have hXD : X.card ≤ D := by omega
  have hnBip : ¬ (G.induce (X : Set V)ᶜ).IsBipartite := by
    intro hbip
    exact hnoDelete ⟨X, hXD, hbip⟩
  have hodd : ∃ H : (G.induce (X : Set V)ᶜ).Subgraph,
      IsOddCycleSubgraph H := by
    by_contra hno
    exact hnBip ((isBipartite_iff_no_oddCycleSubgraph _).2 hno)
  obtain ⟨H, hH⟩ := hodd
  obtain ⟨c, K, hK⟩ := exists_odd_componentVertices G X H hH
  let T := componentVertices G X c
  let N := externalNeighborhood G T
  have hTN : N = externalNeighborhood G T := rfl
  have hTconn : (G.induce (T : Set V)).Connected :=
    componentVertices_connected G X c
  have hTX : Disjoint T X := componentVertices_disjoint_delete G X c
  have hNX : N ⊆ X := component_externalNeighborhood_subset_delete G X c
  have hNcard : N.card ≤ ℓ :=
    (Finset.card_le_card hNX).trans (Nat.le_of_lt hXcard)
  have horient := exactly_one_odd_side_of_graphObstructionDichotomy
    O G (Finset.univ \ T) (T ∪ N) p C ℓ D hInd
      (by simpa only [hTN] using separation_externalNeighborhood G T)
      (by simpa only [hTN, inter_externalNeighborhood] using hNcard)
      hrec hnoPack hnoDelete hnoObs
  dsimp [N] at horient
  rw [leftDiff_externalNeighborhood G T, rightDiff_externalNeighborhood G T]
    at horient
  have horient' :
      (((∃ H : (G.induce (((Finset.univ \
          (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∨
        ((∃ H : (G.induce (T : Set V)).Subgraph,
            IsOddCycleSubgraph H) ∧
          ¬ ∃ H : (G.induce (((Finset.univ \
            (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
              IsOddCycleSubgraph H)) := horient
  have hTcycle : ∃ H : (G.induce (T : Set V)).Subgraph,
      IsOddCycleSubgraph H := ⟨K, hK⟩
  have hotherNoOdd :
      ¬ ∃ H : (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).Subgraph,
          IsOddCycleSubgraph H := by
    rcases horient' with hleft | hright
    · exact (hleft.2 hTcycle).elim
    · exact hright.2
  have hotherBip :
      (G.induce (((Finset.univ \
        (T ∪ externalNeighborhood G T) : Finset V) : Set V))).IsBipartite :=
    (isBipartite_iff_no_oddCycleSubgraph _).2 hotherNoOdd
  refine ⟨T, (mem_lowOrderOddSides G ℓ T).2
    ⟨hTconn, hTcycle, ?_, hotherBip⟩, hTX.symm⟩
  simpa only [hTN] using hNcard

/-- The only remaining high-connectivity input for a generic stable
obstruction. -/
def HighOrderGraphObstructionTrichotomy
    (O : EmbeddingStableGraphObstruction.{u})
    (q ℓ D : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], ∀ G : SimpleGraph V,
    IsFiniteBramble G (lowOrderOddSides G ℓ) →
    BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) →
    HasOddCyclePacking q G ∨ BipartiteAfterDeletingAtMost D G ∨ O.Holds G

theorem graphObstructionDichotomy_succ_of_highOrderBramble
    (O : EmbeddingStableGraphObstruction.{u})
    (p C ℓ D : ℕ)
    (hInd : GraphObstructionDichotomy O p C)
    (hrec : C + C + ℓ ≤ D)
    (hhigh : HighOrderGraphObstructionTrichotomy O (p + 1) ℓ D) :
    GraphObstructionDichotomy O (p + 1) D := by
  intro V _ G
  by_cases hpack : HasOddCyclePacking (p + 1) G
  · exact Or.inl hpack
  by_cases hdelete : BipartiteAfterDeletingAtMost D G
  · exact Or.inr (Or.inl hdelete)
  by_cases hobs : O.Holds G
  · exact Or.inr (Or.inr hobs)
  have hbramble : IsFiniteBramble G (lowOrderOddSides G ℓ) :=
    lowOrderOddSides_isFiniteBramble G ℓ
  have horder : BrambleOrderAtLeast ℓ (lowOrderOddSides G ℓ) :=
    lowOrderOddSides_brambleOrderAtLeast_of_graphObstructionDichotomy
      O G p C ℓ D hInd hrec hpack hdelete hobs
  rcases hhigh V G hbramble horder with hp | hd | ho
  · exact (hpack hp).elim
  · exact (hdelete hd).elim
  · exact (hobs ho).elim

/-- Uniform high-order input for all successor stages. -/
def UniformHighOrderGraphObstructionStatement
    (O : EmbeddingStableGraphObstruction.{u}) : Prop :=
  ∀ p C : ℕ, ∃ ℓ D : ℕ,
    C + C + ℓ ≤ D ∧
      HighOrderGraphObstructionTrichotomy O (p + 1) ℓ D

theorem graphObstructionDichotomy_of_highOrderBramble
    (O : EmbeddingStableGraphObstruction.{u})
    (hhigh : UniformHighOrderGraphObstructionStatement O) :
    ∀ p : ℕ, ∃ C : ℕ, GraphObstructionDichotomy O p C := by
  intro p
  induction p with
  | zero =>
      refine ⟨0, ?_⟩
      intro V _ G
      exact Or.inl (hasOddCyclePacking_zero G)
  | succ p ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨ℓ, D, hrec, hstep⟩ := hhigh p C
      exact ⟨D, graphObstructionDichotomy_succ_of_highOrderBramble
        O p C ℓ D hC hrec hstep⟩

/-- Weighted cycle-edge certificates form an embedding-stable obstruction. -/
def largeCertificateObstruction (r : ℕ) :
    EmbeddingStableGraphObstruction.{u} where
  Holds := HasLargeUniformIndexedOddCycleEdgeCertificate r
  map_embedding h f := h.map_embedding f

/-- Intrinsic independence defect is itself an embedding-stable graph
obstruction. -/
def independenceDefectObstruction (r : ℕ) :
    EmbeddingStableGraphObstruction.{u} where
  Holds := HasIndependenceDefectAtLeast r
  map_embedding h f := h.map_embedding f

/-- Subdivision-robust form of the remaining Reed controlled-wall theorem. -/
def ReedWeightedHighOrderBrambleStatement : Prop :=
  ∀ r : ℕ, UniformHighOrderGraphObstructionStatement.{0}
    (largeCertificateObstruction.{0} r)

/-- The same remaining high-order theorem stated directly in terms of the
intrinsic defect witness.  This is the most economical target for odd
subdivisions, since subdivision paths change the order and independence
number by matched pairs and hence preserve their difference. -/
def ReedDefectHighOrderBrambleStatement : Prop :=
  ∀ r : ℕ, UniformHighOrderGraphObstructionStatement.{0}
    (independenceDefectObstruction.{0} (r + 1))

/-- The weighted certificate form implies the intrinsic defect form. -/
theorem reedDefectHighOrderBrambleStatement_of_weighted
    (h : ReedWeightedHighOrderBrambleStatement) :
    ReedDefectHighOrderBrambleStatement := by
  intro r p C
  obtain ⟨ℓ, D, hrec, hhigh⟩ := h r p C
  refine ⟨ℓ, D, hrec, ?_⟩
  intro V _ G hbramble horder
  rcases hhigh V G hbramble horder with hpack | hdelete | hcert
  · exact Or.inl hpack
  · exact Or.inr (Or.inl hdelete)
  · exact Or.inr (Or.inr
      (hasIndependenceDefectAtLeast_succ_of_largeCertificate hcert))

/-- The weighted high-order bramble theorem closes the exact unconditional
Problem 73 statement: disjoint cycles and a large weighted certificate are
both forbidden by the hereditary stable-set hypothesis. -/
theorem problem73_of_weightedHighOrderBramble
    (hhigh : ReedWeightedHighOrderBrambleStatement) : Problem73 := by
  intro k
  obtain ⟨C, hC⟩ :=
    graphObstructionDichotomy_of_highOrderBramble
      (largeCertificateObstruction k) (hhigh k) (k + 1)
  refine ⟨C, ?_⟩
  intro n G hG
  rcases hC (Fin n) G with hpack | hdelete | hcert
  · exact (not_hasOddCyclePacking_succ hG hpack).elim
  · exact hdelete
  · exact (not_hasLargeUniformIndexedOddCycleEdgeCertificate hG hcert).elim

/-- The intrinsic-defect high-order theorem also closes Problem 73
directly. -/
theorem problem73_of_defectHighOrderBramble
    (hhigh : ReedDefectHighOrderBrambleStatement) : Problem73 := by
  intro k
  obtain ⟨C, hC⟩ :=
    graphObstructionDichotomy_of_highOrderBramble
      (independenceDefectObstruction (k + 1)) (hhigh k) (k + 1)
  refine ⟨C, ?_⟩
  intro n G hG
  rcases hC (Fin n) G with hpack | hdelete | hdefect
  · exact (not_hasOddCyclePacking_succ hG hpack).elim
  · exact hdelete
  · exact (not_hasIndependenceDefectAtLeast_succ hG hdefect).elim

/-- Once the structural exact-double-cover trichotomy is proved, its two
obstruction outcomes are excluded by the hereditary hypothesis, yielding the
exact uniform statement of Problem 73. -/
theorem problem73_of_exactDoubleCoverTrichotomy
    (htrichotomy : ReedExactDoubleCoverTrichotomyStatement) : Problem73 := by
  intro k
  obtain ⟨C, hC⟩ := htrichotomy (k + 1) (k + 1)
  refine ⟨C, ?_⟩
  intro n G hG
  rcases hC n G with hpack | hdelete | hcover
  · exact (not_hasOddCyclePacking_succ hG hpack).elim
  · exact hdelete
  · exact (not_exactDoubleOddCycleCover_of_large_rank hG (by omega)
      hcover).elim

/-- Consequently, the controlled-wall/high-order bramble theorem alone is
enough to imply the exact statement of Problem 73. -/
theorem problem73_of_highOrderBramble
    (hhigh : ReedHighOrderBrambleStatement.{0}) : Problem73 :=
  problem73_of_exactDoubleCoverTrichotomy
    (reedExactDoubleCoverTrichotomy_of_highOrderBramble hhigh)

/-- The elementary `k = 0` case observed by Reed: a graph for which every
subgraph has an independent set containing at least half of its vertices is
bipartite. -/
theorem bipartite_of_everySubgraphHasLargeIndepSet_zero
    {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : EverySubgraphHasLargeIndepSet 0 G) : G.IsBipartite := by
  apply Erdos58.colorable_two_of_oddCycleLengths_eq_empty
  rw [Set.eq_empty_iff_forall_notMem]
  intro n hncycle
  have hnodd : Odd n := Erdos58.odd_of_mem_oddCycleLengths hncycle
  have hn3 : 3 ≤ n := Erdos58.three_le_of_mem_oddCycleLengths hncycle
  have hcontained : SimpleGraph.cycleGraph n ⊑ G :=
    ((Erdos58.mem_oddCycleLengths_iff_cycleGraph_isContained hn3).1 hncycle).2
  let f : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G := hcontained.some
  let H : G.Subgraph := f.toSubgraph
  let e : SimpleGraph.cycleGraph n ≃g H.coe := f.isoToSubgraph
  have hverts : H.verts.ncard = n := by
    rw [← Nat.card_coe_set_eq]
    calc
      Nat.card H.verts = Nat.card (Fin n) := (Nat.card_congr e.toEquiv).symm
      _ = n := Nat.card_fin n
  have hindep : (SimpleGraph.cycleGraph n).indepNum = H.coe.indepNum :=
    indepNum_eq_of_iso e
  have hlower : n ≤ 2 * H.coe.indepNum := by
    have := hG H
    simpa only [hverts, Nat.add_zero] using this
  have hupper : 2 * H.coe.indepNum ≤ n := by
    rw [← hindep]
    exact two_mul_indepNum_cycleGraph_le hn3
  have heq : n = 2 * H.coe.indepNum := Nat.le_antisymm hlower hupper
  exact (Nat.not_even_iff_odd.mpr hnodd) (heq ▸ even_two_mul H.coe.indepNum)

/-- Exact uniform conclusion of Problem 73 for `k = 0`, with no exceptional
vertices. -/
theorem erdos_73_zero :
    ∀ {V : Type*} [Finite V] (G : SimpleGraph V),
      EverySubgraphHasLargeIndepSet 0 G →
        BipartiteAfterDeletingAtMost 0 G := by
  intro V _ G hG
  refine ⟨∅, by simp, ?_⟩
  rw [SimpleGraph.induce_eq_coe_induce_top]
  exact (bipartite_of_everySubgraphHasLargeIndepSet_zero G hG).subgraph _

/-- The `k = 0` slice of the exact uniform assertion `Problem73`. -/
theorem problem73_zero :
    ∃ C : ℕ, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      EverySubgraphHasLargeIndepSet 0 G →
        BipartiteAfterDeletingAtMost C G := by
  exact ⟨0, fun _ G ↦ erdos_73_zero G⟩

/-- A column strictly left of its reflected column. -/
def TwistedLeftColumn (n : ℕ) := {c : ℕ // 2 * c + 1 < n}

def twistedRightColumn {n : ℕ} (c : TwistedLeftColumn n) : ℕ :=
  n - 1 - c.1

lemma twistedLeft_lt {n : ℕ} (c : TwistedLeftColumn n) : c.1 < n := by
  have hc := c.property
  omega

instance twistedLeftColumnFinite (n : ℕ) : Finite (TwistedLeftColumn n) :=
  Finite.of_injective
    (fun c : TwistedLeftColumn n ↦ (⟨c.1, twistedLeft_lt c⟩ : Fin n))
    (fun _ _ h ↦ Subtype.ext (Fin.ext_iff.mp h))

noncomputable instance twistedLeftColumnFintype (n : ℕ) :
    Fintype (TwistedLeftColumn n) := Fintype.ofFinite _

lemma twistedLeft_lt_right {n : ℕ} (c : TwistedLeftColumn n) :
    c.1 < twistedRightColumn c := by
  dsimp [twistedRightColumn]
  have hc := c.property
  omega

lemma twistedRight_lt {n : ℕ} (c : TwistedLeftColumn n) :
    twistedRightColumn c < n := by
  dsimp [twistedRightColumn]
  have hc := c.property
  omega

/-- Number of vertices in an L-shaped path from the top of `c` to the
bottom of its reflected column, hence also the length of the closing cycle. -/
def twistedLSpan {n : ℕ} (c : TwistedLeftColumn n) : ℕ :=
  twistedRightColumn c - c.1

lemma twistedLeft_add_span {n : ℕ} (c : TwistedLeftColumn n) :
    c.1 + twistedLSpan c = twistedRightColumn c := by
  rw [twistedLSpan, Nat.add_sub_of_le (Nat.le_of_lt (twistedLeft_lt_right c))]

def twistedLCycleLength {n : ℕ} (c : TwistedLeftColumn n) : ℕ :=
  n + twistedLSpan c

lemma twistedLCycleLength_eq {n : ℕ} (c : TwistedLeftColumn n) :
    twistedLCycleLength c = 2 * n - 1 - 2 * c.1 := by
  dsimp [twistedLCycleLength, twistedLSpan, twistedRightColumn]
  have hc := c.property
  omega

lemma twistedLCycleLength_odd {n : ℕ} (c : TwistedLeftColumn n) :
    Odd (twistedLCycleLength c) := by
  rw [twistedLCycleLength_eq]
  have hc := c.property
  have hpos : 2 * c.1 + 1 < 2 * n := by omega
  use n - c.1 - 1
  omega

lemma twistedLCycleLength_three_le {n : ℕ} (c : TwistedLeftColumn n) :
    3 ≤ twistedLCycleLength c := by
  rw [twistedLCycleLength_eq]
  have hc := c.property
  omega

/-- The ordered vertices of the left-to-right L-cycle: descend column `c`
to row `r`, cross that row, then descend the reflected column. -/
def twistedLVertex {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n)
    (i : Fin (twistedLCycleLength c)) : Fin n × Fin n :=
  if h₁ : i.1 ≤ r.1 then
    (⟨i.1, by
      rw [twistedLCycleLength_eq] at i
      have hc := c.property
      omega⟩,
     ⟨c.1, twistedLeft_lt c⟩)
  else if h₂ : i.1 ≤ r.1 + twistedLSpan c then
    (r,
     ⟨c.1 + (i.1 - r.1), by
       have hz := twistedRight_lt c
       have hspan := twistedLeft_add_span c
       omega⟩)
  else
    (⟨r.1 + (i.1 - (r.1 + twistedLSpan c)), by
       have hi : i.1 < n + twistedLSpan c := i.isLt
       omega⟩,
     ⟨twistedRightColumn c, twistedRight_lt c⟩)

lemma twistedLVertex_injective {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n) :
    Function.Injective (twistedLVertex c r) := by
  intro i j hij
  have hc := c.property
  have hcz := twistedLeft_lt_right c
  by_cases hi₁ : i.1 ≤ r.1
  · by_cases hj₁ : j.1 ≤ r.1
    · simp only [twistedLVertex, dif_pos hi₁, dif_pos hj₁] at hij
      apply Fin.ext
      exact congrArg (fun p : Fin n × Fin n ↦ p.1.1) hij
    · by_cases hj₂ : j.1 ≤ r.1 + twistedLSpan c
      · simp only [twistedLVertex, dif_pos hi₁, dif_neg hj₁, dif_pos hj₂] at hij
        have hcols : c.1 = c.1 + (j.1 - r.1) := by
          simpa using congrArg (fun p : Fin n × Fin n ↦ p.2.1) hij
        omega
      · simp only [twistedLVertex, dif_pos hi₁, dif_neg hj₁, dif_neg hj₂] at hij
        have hcols : c.1 = twistedRightColumn c := by
          simpa using congrArg (fun p : Fin n × Fin n ↦ p.2.1) hij
        omega
  · by_cases hi₂ : i.1 ≤ r.1 + twistedLSpan c
    · by_cases hj₁ : j.1 ≤ r.1
      · simp only [twistedLVertex, dif_neg hi₁, dif_pos hi₂, dif_pos hj₁] at hij
        have hcols : c.1 + (i.1 - r.1) = c.1 := by
          simpa using congrArg (fun p : Fin n × Fin n ↦ p.2.1) hij
        omega
      · by_cases hj₂ : j.1 ≤ r.1 + twistedLSpan c
        · simp only [twistedLVertex, dif_neg hi₁, dif_pos hi₂, dif_neg hj₁, dif_pos hj₂]
            at hij
          apply Fin.ext
          have hcols : c.1 + (i.1 - r.1) = c.1 + (j.1 - r.1) := by
            simpa using congrArg (fun p : Fin n × Fin n ↦ p.2.1) hij
          omega
        · simp only [twistedLVertex, dif_neg hi₁, dif_pos hi₂, dif_neg hj₁, dif_neg hj₂]
            at hij
          have hrows : r.1 = r.1 + (j.1 - (r.1 + twistedLSpan c)) := by
            simpa using congrArg (fun p : Fin n × Fin n ↦ p.1.1) hij
          omega
    · by_cases hj₁ : j.1 ≤ r.1
      · simp only [twistedLVertex, dif_neg hi₁, dif_neg hi₂, dif_pos hj₁] at hij
        have hcols : twistedRightColumn c = c.1 := by
          simpa using congrArg (fun p : Fin n × Fin n ↦ p.2.1) hij
        omega
      · by_cases hj₂ : j.1 ≤ r.1 + twistedLSpan c
        · simp only [twistedLVertex, dif_neg hi₁, dif_neg hi₂, dif_neg hj₁, dif_pos hj₂]
            at hij
          have hrows : r.1 + (i.1 - (r.1 + twistedLSpan c)) = r.1 := by
            simpa using congrArg (fun p : Fin n × Fin n ↦ p.1.1) hij
          omega
        · simp only [twistedLVertex, dif_neg hi₁, dif_neg hi₂, dif_neg hj₁, dif_neg hj₂]
            at hij
          apply Fin.ext
          have hrows :
              r.1 + (i.1 - (r.1 + twistedLSpan c)) =
                r.1 + (j.1 - (r.1 + twistedLSpan c)) := by
            simpa using congrArg (fun p : Fin n × Fin n ↦ p.1.1) hij
          omega

def twistedLEmbedding {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n) :
    Fin (twistedLCycleLength c) ↪ Fin n × Fin n :=
  ⟨twistedLVertex c r, twistedLVertex_injective c r⟩

lemma mem_range_twistedLEmbedding_iff {n : ℕ}
    (c : TwistedLeftColumn n) (r : Fin n) (v : Fin n × Fin n) :
    v ∈ Set.range (twistedLEmbedding c r) ↔
      (v.2.1 = c.1 ∧ v.1.1 ≤ r.1) ∨
      (v.1.1 = r.1 ∧ c.1 ≤ v.2.1 ∧ v.2.1 ≤ twistedRightColumn c) ∨
      (v.2.1 = twistedRightColumn c ∧ r.1 ≤ v.1.1) := by
  constructor
  · rintro ⟨i, rfl⟩
    have hspan := twistedLeft_add_span c
    dsimp only [twistedLEmbedding]
    dsimp [twistedLVertex]
    split <;> rename_i hi₁
    · exact Or.inl ⟨rfl, hi₁⟩
    · split <;> rename_i hi₂
      · right; left
        simp only [Fin.val_mk]
        refine ⟨trivial, ?_, ?_⟩ <;> omega
      · right; right
        simp only [Fin.val_mk]
        refine ⟨trivial, ?_⟩
        omega
  · intro hv
    have hc := c.property
    have hcz := twistedLeft_lt_right c
    have hz := twistedRight_lt c
    have hspan := twistedLeft_add_span c
    rcases hv with hleft | hmiddle | hright
    · let i : Fin (twistedLCycleLength c) := ⟨v.1.1, by
        rw [twistedLCycleLength_eq]
        omega⟩
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        simp [twistedLEmbedding, twistedLVertex, i, hleft.2]
      · apply Fin.ext
        simp [twistedLEmbedding, twistedLVertex, i, hleft.1, hleft.2]
    · let i : Fin (twistedLCycleLength c) := ⟨r.1 + (v.2.1 - c.1), by
        change r.1 + (v.2.1 - c.1) < n + twistedLSpan c
        omega⟩
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        change (twistedLVertex c r i).1.1 = v.1.1
        dsimp [twistedLVertex, i]
        split <;> rename_i hi₁
        · simp only [Prod.fst, Fin.val_mk]
          omega
        · split <;> rename_i hi₂
          · exact hmiddle.1.symm
          · omega
      · apply Fin.ext
        change (twistedLVertex c r i).2.1 = v.2.1
        dsimp [twistedLVertex, i]
        split <;> rename_i hi₁
        · simp only [Fin.val_mk]
          omega
        · split <;> rename_i hi₂
          · simp only [Fin.val_mk]
            omega
          · omega
    · let i : Fin (twistedLCycleLength c) :=
        ⟨r.1 + twistedLSpan c + (v.1.1 - r.1), by
          change r.1 + twistedLSpan c + (v.1.1 - r.1) < n + twistedLSpan c
          omega⟩
      refine ⟨i, ?_⟩
      apply Prod.ext
      · apply Fin.ext
        change (twistedLVertex c r i).1.1 = v.1.1
        dsimp [twistedLVertex, i]
        split <;> rename_i hi₁
        · omega
        · split <;> rename_i hi₂
          · simp only [Fin.val_mk]
            omega
          · simp only [Fin.val_mk]
            omega
      · apply Fin.ext
        change (twistedLVertex c r i).2.1 = v.2.1
        dsimp [twistedLVertex, i]
        split <;> rename_i hi₁
        · simp only [Fin.val_mk]
          omega
        · split <;> rename_i hi₂
          · simp only [Fin.val_mk]
            omega
          · exact hright.1.symm

/-- Reflection in the vertical axis of the square grid. -/
def twistedGridReflection (n : ℕ) : (Fin n × Fin n) ≃ (Fin n × Fin n) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) Fin.revPerm

@[simp] lemma twistedGridReflection_apply (n : ℕ) (v : Fin n × Fin n) :
    twistedGridReflection n v = (v.1, v.2.rev) := rfl

@[simp] lemma twistedGridReflection_involutive (n : ℕ) (v : Fin n × Fin n) :
    twistedGridReflection n (twistedGridReflection n v) = v := by
  apply Prod.ext <;> simp [twistedGridReflection]

def twistedCycleEmbedding {n : ℕ} (c : TwistedLeftColumn n) (r : Fin n)
    (reflected : Bool) : Fin (twistedLCycleLength c) ↪ Fin n × Fin n :=
  if reflected then
    (twistedLEmbedding c r).trans (twistedGridReflection n).toEmbedding
  else twistedLEmbedding c r

abbrev TwistedCycleIndex (n : ℕ) := TwistedLeftColumn n × Fin n × Bool

def twistedMappedCycleGraph {n : ℕ} (a : TwistedCycleIndex n) :
    SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.map (twistedCycleEmbedding a.1 a.2.1 a.2.2)
    (SimpleGraph.cycleGraph (twistedLCycleLength a.1))

/-- The canonical finite twisted grid is the union of all its indexed
left- and right-oriented L-cycles. -/
def twistedGridGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  ⨆ a : TwistedCycleIndex n, twistedMappedCycleGraph a

def twistedCycleCopy {n : ℕ} (a : TwistedCycleIndex n) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph (twistedLCycleLength a.1))
      (twistedGridGraph n) :=
  (SimpleGraph.Copy.ofLE (twistedMappedCycleGraph a) (twistedGridGraph n)
      (le_iSup (fun b : TwistedCycleIndex n ↦ twistedMappedCycleGraph b) a)).comp
    ((SimpleGraph.Embedding.map (twistedCycleEmbedding a.1 a.2.1 a.2.2)
      (SimpleGraph.cycleGraph (twistedLCycleLength a.1))).toCopy)

def twistedCycleSubgraph {n : ℕ} (a : TwistedCycleIndex n) :
    (twistedGridGraph n).Subgraph :=
  (twistedCycleCopy a).toSubgraph

lemma twistedCycleSubgraph_isOddCycle {n : ℕ} (a : TwistedCycleIndex n) :
    IsOddCycleSubgraph (twistedCycleSubgraph a) := by
  exact ⟨twistedLCycleLength a.1, twistedLCycleLength_three_le a.1,
    twistedLCycleLength_odd a.1, ⟨(twistedCycleCopy a).isoToSubgraph⟩⟩

lemma mem_twistedCycleSubgraph_verts_iff {n : ℕ} (a : TwistedCycleIndex n)
    (v : Fin n × Fin n) :
    v ∈ (twistedCycleSubgraph a).verts ↔
      v ∈ Set.range (twistedCycleEmbedding a.1 a.2.1 a.2.2) := by
  change v ∈ (twistedCycleCopy a).toSubgraph.verts ↔ _
  rw [verts_copy_toSubgraph]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change twistedCycleEmbedding a.1 a.2.1 a.2.2 i = v at hi
    exact hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change twistedCycleEmbedding a.1 a.2.1 a.2.2 i = v
    exact hi

lemma mem_range_twistedCycleEmbedding_false_iff {n : ℕ}
    (c : TwistedLeftColumn n) (r : Fin n) (v : Fin n × Fin n) :
    v ∈ Set.range (twistedCycleEmbedding c r false) ↔
      (v.2.1 = c.1 ∧ v.1.1 ≤ r.1) ∨
      (v.1.1 = r.1 ∧ c.1 ≤ v.2.1 ∧ v.2.1 ≤ twistedRightColumn c) ∨
      (v.2.1 = twistedRightColumn c ∧ r.1 ≤ v.1.1) := by
  simpa [twistedCycleEmbedding] using mem_range_twistedLEmbedding_iff c r v

lemma mem_range_twistedCycleEmbedding_true_iff {n : ℕ}
    (c : TwistedLeftColumn n) (r : Fin n) (v : Fin n × Fin n) :
    v ∈ Set.range (twistedCycleEmbedding c r true) ↔
      (v.2.1 = twistedRightColumn c ∧ v.1.1 ≤ r.1) ∨
      (v.1.1 = r.1 ∧ c.1 ≤ v.2.1 ∧ v.2.1 ≤ twistedRightColumn c) ∨
      (v.2.1 = c.1 ∧ r.1 ≤ v.1.1) := by
  have hc := c.property
  have hvn := v.2.isLt
  have hvr := v.1.isLt
  have hrn := r.isLt
  have hrange :
      v ∈ Set.range (twistedCycleEmbedding c r true) ↔
        twistedGridReflection n v ∈ Set.range (twistedLEmbedding c r) := by
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change twistedGridReflection n (twistedLEmbedding c r i) = v at hi
      rw [← hi]
      exact (twistedGridReflection_involutive n _).symm
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      change twistedGridReflection n (twistedLEmbedding c r i) = v
      rw [hi]
      exact twistedGridReflection_involutive n v
  rw [hrange, mem_range_twistedLEmbedding_iff]
  simp only [twistedGridReflection_apply, Prod.fst, Prod.snd]
  dsimp [Fin.rev, twistedRightColumn]
  have hrevadd : n - (v.2.1 + 1) + (v.2.1 + 1) = n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hvn)
  constructor
  · rintro (hleft | hmiddle | hright)
    · left
      refine ⟨?_, hleft.2⟩
      omega
    · right; left
      refine ⟨hmiddle.1, ?_, ?_⟩ <;> omega
    · right; right
      refine ⟨?_, hright.2⟩
      omega
  · rintro (hleft | hmiddle | hright)
    · left
      refine ⟨?_, hleft.2⟩
      omega
    · right; left
      refine ⟨hmiddle.1, ?_, ?_⟩ <;> omega
    · right; right
      refine ⟨?_, hright.2⟩
      omega

def twistedCyclePairLoad {n : ℕ} (c : TwistedLeftColumn n)
    (v : Fin n × Fin n) : ℕ :=
  ∑ r : Fin n, (
    (if v ∈ Set.range (twistedCycleEmbedding c r false) then (1 : ℕ) else 0) +
    (if v ∈ Set.range (twistedCycleEmbedding c r true) then (1 : ℕ) else 0))

lemma twistedCyclePairLoad_eq {n : ℕ} (c : TwistedLeftColumn n)
    (v : Fin n × Fin n) :
    twistedCyclePairLoad c v =
      if v.2.1 = c.1 ∨ v.2.1 = twistedRightColumn c then n + 1
      else if c.1 < v.2.1 ∧ v.2.1 < twistedRightColumn c then 2 else 0 := by
  have hc := c.property
  have hcz := twistedLeft_lt_right c
  have hz := twistedRight_lt c
  have hvrow := v.1.isLt
  have hvcol := v.2.isLt
  unfold twistedCyclePairLoad
  by_cases hvc : v.2.1 = c.1
  · have hfalse (r : Fin n) :
        (v ∈ Set.range (twistedCycleEmbedding c r false)) ↔ v.1 ≤ r := by
      rw [mem_range_twistedCycleEmbedding_false_iff]
      simp only [Fin.le_iff_val_le_val]
      omega
    have htrue (r : Fin n) :
        (v ∈ Set.range (twistedCycleEmbedding c r true)) ↔ r ≤ v.1 := by
      rw [mem_range_twistedCycleEmbedding_true_iff]
      simp only [Fin.le_iff_val_le_val]
      omega
    simp_rw [hfalse, htrue]
    rw [Finset.sum_add_distrib]
    have hupper : (∑ r : Fin n, if v.1 ≤ r then (1 : ℕ) else 0) =
        n - v.1.1 := by
      calc
        (∑ r : Fin n, if v.1 ≤ r then 1 else 0) = (Finset.Ici v.1).card := by
          have hfilter :
              ((Finset.univ : Finset (Fin n)).filter fun r => v.1 ≤ r) =
                Finset.Ici v.1 := by
            ext r
            simp
          rw [Finset.sum_boole, hfilter]
          simp
        _ = n - v.1 := by simp
    have hlower : (∑ r : Fin n, if r ≤ v.1 then (1 : ℕ) else 0) =
        v.1.1 + 1 := by
      calc
        (∑ r : Fin n, if r ≤ v.1 then 1 else 0) = (Finset.Iic v.1).card := by
          have hfilter :
              ((Finset.univ : Finset (Fin n)).filter fun r => r ≤ v.1) =
                Finset.Iic v.1 := by
            ext r
            simp
          rw [Finset.sum_boole, hfilter]
          simp
        _ = v.1.1 + 1 := by simp
    rw [hupper, hlower]
    simp only [hvc, true_or, if_true]
    omega
  · by_cases hvz : v.2.1 = twistedRightColumn c
    · have hfalse (r : Fin n) :
          (v ∈ Set.range (twistedCycleEmbedding c r false)) ↔ r ≤ v.1 := by
        rw [mem_range_twistedCycleEmbedding_false_iff]
        simp only [Fin.le_iff_val_le_val]
        omega
      have htrue (r : Fin n) :
          (v ∈ Set.range (twistedCycleEmbedding c r true)) ↔ v.1 ≤ r := by
        rw [mem_range_twistedCycleEmbedding_true_iff]
        simp only [Fin.le_iff_val_le_val]
        omega
      simp_rw [hfalse, htrue]
      rw [Finset.sum_add_distrib]
      have hlower : (∑ r : Fin n, if r ≤ v.1 then (1 : ℕ) else 0) =
          v.1.1 + 1 := by
        calc
          (∑ r : Fin n, if r ≤ v.1 then 1 else 0) = (Finset.Iic v.1).card := by
            have hfilter :
                ((Finset.univ : Finset (Fin n)).filter fun r => r ≤ v.1) =
                  Finset.Iic v.1 := by
              ext r
              simp
            rw [Finset.sum_boole, hfilter]
            simp
          _ = v.1.1 + 1 := by simp
      have hupper : (∑ r : Fin n, if v.1 ≤ r then (1 : ℕ) else 0) =
          n - v.1.1 := by
        calc
          (∑ r : Fin n, if v.1 ≤ r then 1 else 0) = (Finset.Ici v.1).card := by
            have hfilter :
                ((Finset.univ : Finset (Fin n)).filter fun r => v.1 ≤ r) =
                  Finset.Ici v.1 := by
              ext r
              simp
            rw [Finset.sum_boole, hfilter]
            simp
          _ = n - v.1 := by simp
      rw [hlower, hupper]
      simp only [hvc, hvz, or_true, if_true]
      omega
    · by_cases hinterior : c.1 < v.2.1 ∧ v.2.1 < twistedRightColumn c
      · have hfalse (r : Fin n) :
            (v ∈ Set.range (twistedCycleEmbedding c r false)) ↔ v.1 = r := by
          rw [mem_range_twistedCycleEmbedding_false_iff]
          omega
        have htrue (r : Fin n) :
            (v ∈ Set.range (twistedCycleEmbedding c r true)) ↔ v.1 = r := by
          rw [mem_range_twistedCycleEmbedding_true_iff]
          omega
        simp_rw [hfalse, htrue]
        simp only [hvc, hvz, or_self, false_or, if_false, hinterior, if_true]
        rw [Finset.sum_add_distrib]
        simp
      · have hfalse (r : Fin n) :
            ¬ v ∈ Set.range (twistedCycleEmbedding c r false) := by
          rw [mem_range_twistedCycleEmbedding_false_iff]
          omega
        have htrue (r : Fin n) :
            ¬ v ∈ Set.range (twistedCycleEmbedding c r true) := by
          rw [mem_range_twistedCycleEmbedding_true_iff]
          omega
        simp_rw [if_neg (hfalse _), if_neg (htrue _)]
        simp [hvc, hvz, hinterior]

def twistedLeftColumnEvenEquiv (m : ℕ) :
    TwistedLeftColumn (2 * m) ≃ Fin m where
  toFun c := ⟨c.1, by have hc := c.property; omega⟩
  invFun c := ⟨c.1, by have hc := c.isLt; omega⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Fin.ext; rfl

def twistedColumnDepth {m : ℕ} (v : Fin (2 * m) × Fin (2 * m)) : ℕ :=
  min v.2.1 (2 * m - 1 - v.2.1)

lemma twistedColumnDepth_lt {m : ℕ} (v : Fin (2 * m) × Fin (2 * m)) :
    twistedColumnDepth v < m := by
  have hv := v.2.isLt
  dsimp [twistedColumnDepth]
  omega

def twistedColumnDepthFin {m : ℕ} (v : Fin (2 * m) × Fin (2 * m)) : Fin m :=
  ⟨twistedColumnDepth v, twistedColumnDepth_lt v⟩

lemma twistedCyclePairLoad_even_eq (m : ℕ)
    (v : Fin (2 * m) × Fin (2 * m)) (c : Fin m) :
    twistedCyclePairLoad ((twistedLeftColumnEvenEquiv m).symm c) v =
      if c < twistedColumnDepthFin v then 2
      else if c = twistedColumnDepthFin v then 2 * m + 1 else 0 := by
  rw [twistedCyclePairLoad_eq]
  have hc := c.isLt
  have hv := v.2.isLt
  change
    (if v.2.1 = c.1 ∨ v.2.1 = 2 * m - 1 - c.1 then 2 * m + 1
      else if c.1 < v.2.1 ∧ v.2.1 < 2 * m - 1 - c.1 then 2 else 0) =
    if c < twistedColumnDepthFin v then 2
      else if c = twistedColumnDepthFin v then 2 * m + 1 else 0
  have hsub : 2 * m - 1 - v.2.1 + (v.2.1 + 1) = 2 * m := by
    omega
  by_cases hside : v.2.1 ≤ 2 * m - 1 - v.2.1
  · have hd : (twistedColumnDepthFin v).1 = v.2.1 := by
      dsimp [twistedColumnDepthFin, twistedColumnDepth]
      rw [Nat.min_eq_left hside]
    by_cases hendpoint : v.2.1 = c.1 ∨ v.2.1 = 2 * m - 1 - c.1 <;>
      by_cases hinterior : c.1 < v.2.1 ∧ v.2.1 < 2 * m - 1 - c.1 <;>
      by_cases hlt : c.1 < (twistedColumnDepthFin v).1 <;>
      by_cases heq : c.1 = (twistedColumnDepthFin v).1 <;>
      simp [hendpoint, hinterior, Fin.lt_def, Fin.ext_iff, hlt, heq] <;>
      omega
  · have hd : (twistedColumnDepthFin v).1 = 2 * m - 1 - v.2.1 := by
      dsimp [twistedColumnDepthFin, twistedColumnDepth]
      rw [Nat.min_eq_right (Nat.le_of_not_ge hside)]
    by_cases hendpoint : v.2.1 = c.1 ∨ v.2.1 = 2 * m - 1 - c.1 <;>
      by_cases hinterior : c.1 < v.2.1 ∧ v.2.1 < 2 * m - 1 - c.1 <;>
      by_cases hlt : c.1 < (twistedColumnDepthFin v).1 <;>
      by_cases heq : c.1 = (twistedColumnDepthFin v).1 <;>
      simp [hendpoint, hinterior, Fin.lt_def, Fin.ext_iff, hlt, heq] <;>
      omega

lemma sum_twistedCyclePairLoad_even (m : ℕ)
    (v : Fin (2 * m) × Fin (2 * m)) :
    (∑ c : TwistedLeftColumn (2 * m), twistedCyclePairLoad c v) =
      2 * m + 1 + 2 * twistedColumnDepth v := by
  let d : Fin m := twistedColumnDepthFin v
  rw [← (twistedLeftColumnEvenEquiv m).symm.sum_comp]
  have hterm (c : Fin m) :
      twistedCyclePairLoad ((twistedLeftColumnEvenEquiv m).symm c) v =
        if c < d then 2 else if c = d then 2 * m + 1 else 0 := by
    exact twistedCyclePairLoad_even_eq m v c
  simp_rw [hterm]
  calc
    (∑ c : Fin m, if c < d then 2 else if c = d then 2 * m + 1 else 0) =
        (∑ c : Fin m, ((if c < d then (2 : ℕ) else 0) +
          (if c = d then 2 * m + 1 else 0))) := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hlt : c < d <;> by_cases heq : c = d <;> simp [hlt, heq]
    _ = (∑ c : Fin m, if c < d then 2 else 0) +
        ∑ c : Fin m, if c = d then 2 * m + 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * d.1 + (2 * m + 1) := by
      have hlt : (∑ c : Fin m, if c < d then 2 else 0) = 2 * d.1 := by
        calc
          (∑ c : Fin m, if c < d then 2 else 0) =
              2 * ∑ c : Fin m, if c < d then 1 else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            by_cases hcd : c < d <;> simp [hcd]
          _ = 2 * d.1 := by
            congr 1
            calc
              (∑ c : Fin m, if c < d then (1 : ℕ) else 0) =
              (Finset.Iio d).card := by
                have hfilter :
                    ((Finset.univ : Finset (Fin m)).filter fun c => c < d) =
                      Finset.Iio d := by
                  ext c
                  simp
                rw [Finset.sum_boole, hfilter]
                simp
              _ = d.1 := by simp
      rw [hlt]
      simp
    _ = 2 * m + 1 + 2 * twistedColumnDepth v := by
      dsimp [d, twistedColumnDepthFin]
      omega

/-- Integral weights realizing an exactly uniform fractional packing of the
indexed L-cycles. -/
def twistedColumnWeight (m : ℕ) (c : TwistedLeftColumn (2 * m)) : ℕ :=
  (2 * m - 1) ^ c.1 * (2 * m + 1) ^ (m - 1 - c.1)

def twistedCycleWeight (m : ℕ) (a : TwistedCycleIndex (2 * m)) : ℕ :=
  twistedColumnWeight m a.1

lemma twistedWeight_prefix (m d : ℕ) (hd : d < m) :
    2 * (∑ i ∈ Finset.range d,
      (2 * m - 1) ^ i * (2 * m + 1) ^ (m - 1 - i)) +
      (2 * m + 1) *
        ((2 * m - 1) ^ d * (2 * m + 1) ^ (m - 1 - d)) =
      (2 * m + 1) ^ m := by
  let x := 2 * m - 1
  let y := 2 * m + 1
  have hm : 0 < m := by omega
  have hyx : 2 + x = y := by
    dsimp [x, y]
    omega
  have hgeom :
      ((∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)) * 2 + x ^ d) =
        y ^ d := by
    rw [← geom_sum₂_comm]
    simpa only [hyx] using geom_sum₂_mul_add (2 : ℕ) x d
  have hfactor (i : ℕ) (hi : i ∈ Finset.range d) :
      y ^ (m - 1 - i) = y ^ (d - 1 - i) * y ^ (m - d) := by
    rw [← pow_add]
    congr 1
    have hid := Finset.mem_range.mp hi
    omega
  have hend :
      y * (x ^ d * y ^ (m - 1 - d)) = x ^ d * y ^ (m - d) := by
    have he : 1 + (m - 1 - d) = m - d := by omega
    calc
      y * (x ^ d * y ^ (m - 1 - d)) =
          x ^ d * (y * y ^ (m - 1 - d)) := by ac_rfl
      _ = x ^ d * y ^ (1 + (m - 1 - d)) := by rw [pow_add, pow_one]
      _ = x ^ d * y ^ (m - d) := by rw [he]
  change
    2 * (∑ i ∈ Finset.range d, x ^ i * y ^ (m - 1 - i)) +
        y * (x ^ d * y ^ (m - 1 - d)) = y ^ m
  have hsum :
      (∑ i ∈ Finset.range d, x ^ i * y ^ (m - 1 - i)) =
        (∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)) * y ^ (m - d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfactor i hi]
    ac_rfl
  rw [hsum, hend]
  calc
    2 * ((∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)) * y ^ (m - d)) +
        x ^ d * y ^ (m - d) =
      (((∑ i ∈ Finset.range d, x ^ i * y ^ (d - 1 - i)) * 2 + x ^ d) *
        y ^ (m - d)) := by
      rw [add_mul]
      ac_rfl
    _ = y ^ d * y ^ (m - d) := by rw [hgeom]
    _ = y ^ m := by
      rw [← pow_add]
      congr 1
      omega

lemma sum_twistedColumnWeight_mul_pairLoad_even (m : ℕ)
    (v : Fin (2 * m) × Fin (2 * m)) :
    (∑ c : TwistedLeftColumn (2 * m),
      twistedColumnWeight m c * twistedCyclePairLoad c v) =
      (2 * m + 1) ^ m := by
  let d : Fin m := twistedColumnDepthFin v
  rw [← (twistedLeftColumnEvenEquiv m).symm.sum_comp]
  change
    (∑ c : Fin m,
      ((2 * m - 1) ^ c.1 * (2 * m + 1) ^ (m - 1 - c.1)) *
        twistedCyclePairLoad ((twistedLeftColumnEvenEquiv m).symm c) v) = _
  simp_rw [twistedCyclePairLoad_even_eq]
  change
    (∑ c : Fin m,
      ((2 * m - 1) ^ c.1 * (2 * m + 1) ^ (m - 1 - c.1)) *
        (if c < d then 2 else if c = d then 2 * m + 1 else 0)) = _
  let w : ℕ → ℕ := fun i ↦
    (2 * m - 1) ^ i * (2 * m + 1) ^ (m - 1 - i)
  have hprefix :
      (∑ c : Fin m, if c < d then w c.1 else 0) =
        ∑ i ∈ Finset.range d.1, w i := by
    change (∑ c : Fin m, if c.1 < d.1 then w c.1 else 0) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ if i < d.1 then w i else 0) m]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp
      omega
    · intro i hi
      simp only
  have hpoint :
      (∑ c : Fin m, if c = d then w c.1 else 0) = w d.1 := by
    simp
  calc
    (∑ c : Fin m, w c.1 *
        (if c < d then 2 else if c = d then 2 * m + 1 else 0)) =
      2 * (∑ c : Fin m, if c < d then w c.1 else 0) +
        (2 * m + 1) * (∑ c : Fin m, if c = d then w c.1 else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hlt : c < d <;> by_cases heq : c = d <;>
        simp [hlt, heq, Nat.mul_comm, Nat.mul_left_comm]
    _ = 2 * (∑ i ∈ Finset.range d.1, w i) + (2 * m + 1) * w d.1 := by
      rw [hprefix, hpoint]
    _ = (2 * m + 1) ^ m := by
      exact twistedWeight_prefix m d.1 d.isLt

lemma twistedCycleWeightedVertexLoad (m : ℕ)
    (v : Fin (2 * m) × Fin (2 * m)) :
    (∑ a : TwistedCycleIndex (2 * m),
      if v ∈ (twistedCycleSubgraph a).verts then twistedCycleWeight m a else 0) =
      (2 * m + 1) ^ m := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ c : TwistedLeftColumn (2 * m),
        ∑ rb : Fin (2 * m) × Bool,
          if v ∈ (twistedCycleSubgraph (c, rb)).verts
          then twistedCycleWeight m (c, rb) else 0) =
      ∑ c : TwistedLeftColumn (2 * m),
        twistedColumnWeight m c * twistedCyclePairLoad c v := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Fintype.sum_prod_type]
      unfold twistedCyclePairLoad
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fintype.sum_bool]
      rw [mem_twistedCycleSubgraph_verts_iff, mem_twistedCycleSubgraph_verts_iff]
      dsimp [twistedCycleWeight]
      by_cases ht : v ∈ Set.range (twistedCycleEmbedding c r true) <;>
        by_cases hf : v ∈ Set.range (twistedCycleEmbedding c r false) <;>
        simp [ht, hf, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_two]
    _ = (2 * m + 1) ^ m := sum_twistedColumnWeight_mul_pairLoad_even m v

/-- The full twisted grid carries a uniform indexed odd-cycle certificate
with no auxiliary edge weights. -/
lemma twistedGrid_uniformCertificate (m : ℕ) :
    IsUniformIndexedOddCycleEdgeCertificate
      (TwistedCycleIndex (2 * m)) ((2 * m + 1) ^ m)
      (Finset.univ : Finset (Fin (2 * m) × Fin (2 * m)))
      twistedCycleSubgraph (twistedCycleWeight m) ∅
      (fun _ : Sym2 (Fin (2 * m) × Fin (2 * m)) ↦ 0) := by
  refine ⟨twistedCycleSubgraph_isOddCycle, by simp, ?_⟩
  intro v
  simpa using twistedCycleWeightedVertexLoad m v

lemma twistedCycleSubgraph_verts_ncard {n : ℕ} (a : TwistedCycleIndex n) :
    (twistedCycleSubgraph a).verts.ncard = twistedLCycleLength a.1 := by
  have hset : (twistedCycleSubgraph a).verts =
      Set.range (twistedCycleEmbedding a.1 a.2.1 a.2.2) := by
    ext v
    exact mem_twistedCycleSubgraph_verts_iff a v
  rw [hset, Set.ncard_range_of_injective
    (twistedCycleEmbedding a.1 a.2.1 a.2.2).injective]
  simp

lemma twistedGrid_totalWeightedLength (m : ℕ) :
    (∑ a : TwistedCycleIndex (2 * m),
      twistedCycleWeight m a * twistedLCycleLength a.1) =
      (2 * m + 1) ^ m * ((2 * m) * (2 * m)) := by
  have htotal := (twistedGrid_uniformCertificate m).total_load
  simpa only [twistedCycleSubgraph_verts_ncard, Finset.sum_empty,
    Finset.sum_const_zero, Nat.mul_zero, Nat.add_zero, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] using htotal

lemma twistedGrid_cycleWeight_gt_mul (m : ℕ) (hm : 0 < m) :
    (2 * m + 1) ^ m * m <
      ∑ a : TwistedCycleIndex (2 * m), twistedCycleWeight m a := by
  let c0 : TwistedLeftColumn (2 * m) := ⟨0, by omega⟩
  let r0 : Fin (2 * m) := ⟨0, by omega⟩
  have hindex :
      (Finset.univ : Finset (TwistedCycleIndex (2 * m))).Nonempty := by
    exact ⟨(c0, r0, false), Finset.mem_univ _⟩
  have hsumlt :
      (∑ a : TwistedCycleIndex (2 * m),
        twistedCycleWeight m a * twistedLCycleLength a.1) <
      ∑ a : TwistedCycleIndex (2 * m), twistedCycleWeight m a * (4 * m) := by
    apply Finset.sum_lt_sum_of_nonempty hindex
    intro a ha
    have hlen : twistedLCycleLength a.1 < 4 * m := by
      rw [twistedLCycleLength_eq]
      have hc := a.1.property
      omega
    have hx : 0 < 2 * m - 1 := by omega
    have hy : 0 < 2 * m + 1 := by omega
    have hw : 0 < twistedCycleWeight m a := by
      exact Nat.mul_pos (Nat.pow_pos hx) (Nat.pow_pos hy)
    exact Nat.mul_lt_mul_of_pos_left hlen hw
  rw [twistedGrid_totalWeightedLength] at hsumlt
  rw [← Finset.sum_mul] at hsumlt
  have hrearrange :
      (((2 * m + 1) ^ m * m) * (4 * m)) =
        (2 * m + 1) ^ m * ((2 * m) * (2 * m)) := by
    change (((2 * m + 1) ^ m * m) * ((2 * 2) * m)) = _
    ac_rfl
  rw [← hrearrange] at hsumlt
  exact (Nat.mul_lt_mul_right (by omega : 0 < 4 * m)).mp hsumlt

/-- A twisted grid of order `2(k+1)` is an explicit obstruction to
hereditary independence defect `k`. -/
theorem twistedGrid_not_everySubgraphHasLargeIndepSet (k : ℕ) :
    ¬ EverySubgraphHasLargeIndepSet k (twistedGridGraph (2 * (k + 1))) := by
  intro hG
  have hle := uniformIndexedOddCycleEdgeCertificate_cycleWeight_le hG
    (twistedGrid_uniformCertificate (k + 1))
  have hgt := twistedGrid_cycleWeight_gt_mul (k + 1) (by omega)
  have hq : 0 < (2 * (k + 1) + 1) ^ (k + 1) :=
    Nat.pow_pos (by omega)
  have hklt :
      (2 * (k + 1) + 1) ^ (k + 1) * k <
        (2 * (k + 1) + 1) ^ (k + 1) * (k + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hq
  exact (Nat.not_lt_of_ge hle) (hklt.trans hgt)

/-- The weighted L-cycle certificate gives the whole twisted grid an
additive independence defect of at least `k+1`. -/
theorem twistedGrid_full_defect (k : ℕ) :
    2 * (twistedGridGraph (2 * (k + 1))).indepNum + (k + 1) ≤
      Fintype.card (Fin (2 * (k + 1)) × Fin (2 * (k + 1))) := by
  let m := k + 1
  let F := twistedGridGraph (2 * m)
  have hdef := uniformIndexedOddCycleEdgeCertificate_defect
    (twistedGrid_uniformCertificate m)
  have hgt := twistedGrid_cycleWeight_gt_mul m (by omega)
  have hq : 0 < (2 * m + 1) ^ m := Nat.pow_pos (by omega)
  let e : (F.induce (Set.univ : Set (Fin (2 * m) × Fin (2 * m)))) ≃g F :=
    { toEquiv := Equiv.Set.univ _
      map_rel_iff' := by simp [F] }
  have hinduce :
      (F.induce (Set.univ : Set (Fin (2 * m) × Fin (2 * m)))).indepNum =
        F.indepNum := indepNum_eq_of_iso e
  have hinduce' :
      ((twistedGridGraph (2 * m)).induce
        (↑(Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))) :
          Set (Fin (2 * m) × Fin (2 * m)))).indepNum = F.indepNum := by
    have hset :
        (↑(Finset.univ : Finset (Fin (2 * m) × Fin (2 * m))) :
          Set (Fin (2 * m) × Fin (2 * m))) = Set.univ := by
      ext v
      simp
    rw [hset]
    exact hinduce
  have hmul_lt :
      (2 * m + 1) ^ m * (2 * F.indepNum + m) <
        (2 * m + 1) ^ m * Fintype.card (Fin (2 * m) × Fin (2 * m)) := by
    calc
      (2 * m + 1) ^ m * (2 * F.indepNum + m) =
          2 * (2 * m + 1) ^ m * F.indepNum + (2 * m + 1) ^ m * m := by
        rw [Nat.mul_add]
        congr 1
        ac_rfl
      _ < 2 * (2 * m + 1) ^ m * F.indepNum +
          ∑ a : TwistedCycleIndex (2 * m), twistedCycleWeight m a :=
        Nat.add_lt_add_left hgt _
      _ ≤ (2 * m + 1) ^ m * Fintype.card (Fin (2 * m) × Fin (2 * m)) := by
        rw [hinduce'] at hdef
        simpa [F] using hdef
  have hbase : 2 * F.indepNum + m <
      Fintype.card (Fin (2 * m) × Fin (2 * m)) :=
    (Nat.mul_lt_mul_left hq).mp hmul_lt
  change 2 * F.indepNum + m ≤ _
  dsimp [m] at hbase ⊢
  omega

end

attribute [local instance] Classical.propDecidable Classical.decEq
noncomputable section

/-- A canonical order on any finite type, used only to orient the edges of
the explicit odd-subdivision model below. -/
local instance finiteLinearOrder (α : Type*) [Fintype α] : LinearOrder α :=
  LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective

variable {U : Type*} [Fintype U] [LinearOrder U]

/-- Each undirected edge, oriented by the ambient linear order. -/
def OrientedEdge (F : SimpleGraph U) :=
  {e : U × U // e.1 < e.2 ∧ F.Adj e.1 e.2}

instance orientedEdgeFinite (F : SimpleGraph U) : Finite (OrientedEdge F) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance orientedEdgeFintype (F : SimpleGraph U) :
    Fintype (OrientedEdge F) := Fintype.ofFinite _

namespace OrientedEdge

variable {F : SimpleGraph U}

def lo (e : OrientedEdge F) : U := e.1.1
def hi (e : OrientedEdge F) : U := e.1.2

lemma lo_lt_hi (e : OrientedEdge F) : e.lo < e.hi := e.2.1
lemma adj (e : OrientedEdge F) : F.Adj e.lo e.hi := e.2.2

end OrientedEdge

/-- Vertices of the odd subdivision with `2*t(e)` internal vertices on
edge `e`. -/
abbrev OddSubdivisionVertex (F : SimpleGraph U)
    (t : OrientedEdge F → ℕ) :=
  U ⊕ Σ e : OrientedEdge F, Fin (2 * t e)

/-- The ordered vertices of one subdivided edge-path. -/
def oddSubdivisionPathVertex {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) :
    Fin (2 * t e + 2) → OddSubdivisionVertex F t :=
  Fin.cases (Sum.inl e.lo) fun j : Fin (2 * t e + 1) ↦
    Fin.lastCases (Sum.inl e.hi)
      (fun i : Fin (2 * t e) ↦ Sum.inr ⟨e, i⟩) j

@[simp] lemma oddSubdivisionPathVertex_zero {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) :
    oddSubdivisionPathVertex t e 0 = Sum.inl e.lo := by
  simp [oddSubdivisionPathVertex]

@[simp] lemma oddSubdivisionPathVertex_last {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) :
    oddSubdivisionPathVertex t e (Fin.last (2 * t e + 1)) = Sum.inl e.hi := by
  rw [← Fin.succ_last]
  unfold oddSubdivisionPathVertex
  rw [Fin.cases_succ, Fin.lastCases_last]

@[simp] lemma oddSubdivisionPathVertex_internal {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F)
    (i : Fin (2 * t e)) :
    oddSubdivisionPathVertex t e i.castSucc.succ = Sum.inr ⟨e, i⟩ := by
  simp [oddSubdivisionPathVertex]

lemma oddSubdivisionPathVertex_injective {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) :
    Function.Injective (oddSubdivisionPathVertex t e) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
          induction j using Fin.lastCases with
          | last =>
              unfold oddSubdivisionPathVertex at hij
              rw [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last] at hij
              simp only [Sum.inl.injEq] at hij
              exact (ne_of_lt e.lo_lt_hi hij).elim
          | cast j => simp [oddSubdivisionPathVertex] at hij
  | succ i =>
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.cases with
          | zero =>
              unfold oddSubdivisionPathVertex at hij
              rw [Fin.cases_succ, Fin.lastCases_last, Fin.cases_zero] at hij
              simp only [Sum.inl.injEq] at hij
              exact (ne_of_gt e.lo_lt_hi hij).elim
          | succ j =>
              induction j using Fin.lastCases with
              | last => rfl
              | cast j =>
                  unfold oddSubdivisionPathVertex at hij
                  rw [Fin.cases_succ, Fin.lastCases_last,
                    Fin.cases_succ, Fin.lastCases_castSucc] at hij
                  simp at hij
      | cast i =>
          induction j using Fin.cases with
          | zero => simp [oddSubdivisionPathVertex] at hij
          | succ j =>
              induction j using Fin.lastCases with
              | last =>
                  unfold oddSubdivisionPathVertex at hij
                  rw [Fin.cases_succ, Fin.lastCases_castSucc,
                    Fin.cases_succ, Fin.lastCases_last] at hij
                  simp at hij
              | cast j =>
                  congr 2
                  simpa [oddSubdivisionPathVertex] using hij

/-- Replace every edge by a path of odd length `2*t(e)+1`. -/
def oddSubdivisionGraph (F : SimpleGraph U)
    (t : OrientedEdge F → ℕ) :
    SimpleGraph (OddSubdivisionVertex F t) :=
  ⨆ e : OrientedEdge F,
    SimpleGraph.map (oddSubdivisionPathVertex t e)
      (SimpleGraph.pathGraph (2 * t e + 2))

lemma oddSubdivisionGraph_adj_path_succ {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F)
    (i : Fin (2 * t e + 1)) :
    (oddSubdivisionGraph F t).Adj
      (oddSubdivisionPathVertex t e i.castSucc)
      (oddSubdivisionPathVertex t e i.succ) := by
  rw [oddSubdivisionGraph, SimpleGraph.iSup_adj]
  refine ⟨e, ?_⟩
  rw [SimpleGraph.map_adj']
  refine ⟨?_, i.castSucc, i.succ, ?_, rfl, rfl⟩
  · intro h
    have hij := oddSubdivisionPathVertex_injective t e h
    exact (Fin.ne_of_lt (by simp) hij).elim
  · rw [SimpleGraph.pathGraph_adj]
    exact Or.inl (by simp)

/-- Consecutive pairs enumerate `Fin (2*n)`. -/
def consecutivePairEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

@[simp] lemma consecutivePairEquiv_val (n : ℕ) (j : Fin n) (b : Fin 2) :
    (consecutivePairEquiv n (j, b)).1 = 2 * j.1 + b.1 := by
  simp [consecutivePairEquiv, finProdFinEquiv, finCongr]
  omega

/-- Any pairing of a finite type into `n` labelled pairs bounds a subset
which contains at most one member of every pair. -/
lemma card_le_of_pairing {α : Type*} [Fintype α] (n : ℕ)
    (E : Fin n × Fin 2 ≃ α) (J : Finset α)
    (hJ : ∀ j : Fin n, ¬ (E (j, 0) ∈ J ∧ E (j, 1) ∈ J)) :
    J.card ≤ n := by
  have hcard : J.card = ∑ i : α, if i ∈ J then (1 : ℕ) else 0 := by simp
  rw [hcard, ← E.sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin n, ∑ b : Fin 2,
        if E (j, b) ∈ J then (1 : ℕ) else 0) ≤
        ∑ _j : Fin n, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
      rw [huniv, Finset.sum_boole]
      norm_cast
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      fin_cases x <;> fin_cases y
      · rfl
      · exact (hJ j ⟨hx.2, hy.2⟩).elim
      · exact (hJ j ⟨hy.2, hx.2⟩).elim
      · rfl
    _ = n := by simp

/-- A subset of `2n` linearly ordered positions containing at most one
point from each consecutive pair has cardinality at most `n`. -/
lemma card_le_half_of_no_consecutive_pair (n : ℕ) (J : Finset (Fin (2 * n)))
    (hJ : ∀ j : Fin n,
      ¬ (consecutivePairEquiv n (j, 0) ∈ J ∧
          consecutivePairEquiv n (j, 1) ∈ J)) :
    J.card ≤ n := by
  exact card_le_of_pairing n (consecutivePairEquiv n) J hJ

/-- The same consecutive pairing, with the path's arithmetically equal
length `2*n+2` as codomain. -/
def oddPathPairEquiv (n : ℕ) : Fin (n + 1) × Fin 2 ≃ Fin (2 * n + 2) :=
  (consecutivePairEquiv (n + 1)).trans (finCongr (by omega))

@[simp] lemma oddPathPairEquiv_val (n : ℕ) (j : Fin (n + 1)) (b : Fin 2) :
    (oddPathPairEquiv n (j, b)).1 = 2 * j.1 + b.1 := by
  change (consecutivePairEquiv (n + 1) (j, b)).1 = _
  exact consecutivePairEquiv_val (n + 1) j b

lemma oddSubdivisionGraph_adj_internal_pair {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) (j : Fin (t e)) :
    (oddSubdivisionGraph F t).Adj
      (Sum.inr ⟨e, consecutivePairEquiv (t e) (j, 0)⟩)
      (Sum.inr ⟨e, consecutivePairEquiv (t e) (j, 1)⟩) := by
  let k : Fin (2 * t e + 1) := ⟨2 * j.1 + 1, by
    have hj := j.isLt
    omega⟩
  have h := oddSubdivisionGraph_adj_path_succ t e k
  convert h using 1
  · rw [← oddSubdivisionPathVertex_internal]
    congr 1
    apply Fin.ext
    simp [k]
  · rw [← oddSubdivisionPathVertex_internal]
    congr 1
    apply Fin.ext
    simp [k]

lemma oddSubdivisionGraph_adj_path_pair {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (e : OrientedEdge F) (j : Fin (t e + 1)) :
    (oddSubdivisionGraph F t).Adj
      (oddSubdivisionPathVertex t e (oddPathPairEquiv (t e) (j, 0)))
      (oddSubdivisionPathVertex t e (oddPathPairEquiv (t e) (j, 1))) := by
  let k : Fin (2 * t e + 1) := ⟨2 * j.1, by
    have hj := j.isLt
    omega⟩
  have h := oddSubdivisionGraph_adj_path_succ t e k
  convert h using 1 <;> congr 1 <;> apply Fin.ext <;> simp [k]

def subdivisionBranchPart {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) : Finset U :=
  Finset.univ.filter fun u ↦ Sum.inl u ∈ I

def subdivisionInternalPart {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) (e : OrientedEdge F) :
    Finset (Fin (2 * t e)) :=
  Finset.univ.filter fun i ↦ Sum.inr (Sigma.mk e i) ∈ I

def subdivisionPathPart {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) (e : OrientedEdge F) :
    Finset (Fin (2 * t e + 2)) :=
  Finset.univ.filter fun i ↦ oddSubdivisionPathVertex t e i ∈ I

@[simp] lemma mem_subdivisionBranchPart {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ} (I : Finset (OddSubdivisionVertex F t)) (u : U) :
    u ∈ subdivisionBranchPart I ↔ Sum.inl u ∈ I := by
  simp [subdivisionBranchPart]

@[simp] lemma mem_subdivisionInternalPart {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ} (I : Finset (OddSubdivisionVertex F t))
    (e : OrientedEdge F) (i : Fin (2 * t e)) :
    i ∈ subdivisionInternalPart I e ↔ Sum.inr (Sigma.mk e i) ∈ I := by
  simp [subdivisionInternalPart]

lemma subdivisionInternalPart_card_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (I : Finset (OddSubdivisionVertex F t))
    (hI : (oddSubdivisionGraph F t).IsIndepSet (I : Set _))
    (e : OrientedEdge F) :
    (subdivisionInternalPart I e).card ≤ t e := by
  apply card_le_of_pairing (t e) (consecutivePairEquiv (t e))
  intro j hj
  have hadj := oddSubdivisionGraph_adj_internal_pair t e j
  exact hI (by simpa using hj.1) (by simpa using hj.2) hadj.ne hadj

lemma subdivisionPathPart_card_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (I : Finset (OddSubdivisionVertex F t))
    (hI : (oddSubdivisionGraph F t).IsIndepSet (I : Set _))
    (e : OrientedEdge F) :
    (subdivisionPathPart I e).card ≤ t e + 1 := by
  apply card_le_of_pairing (t e + 1) (oddPathPairEquiv (t e))
  intro j hj
  have hadj := oddSubdivisionGraph_adj_path_pair t e j
  exact hI (by simpa [subdivisionPathPart] using hj.1)
    (by simpa [subdivisionPathPart] using hj.2) hadj.ne hadj

lemma subdivisionPathPart_card_eq_internal_add_two_of_endpoints
    {F : SimpleGraph U} (t : OrientedEdge F → ℕ)
    (I : Finset (OddSubdivisionVertex F t)) (e : OrientedEdge F)
    (hlo : Sum.inl e.lo ∈ I) (hhi : Sum.inl e.hi ∈ I) :
    (subdivisionPathPart I e).card =
      (subdivisionInternalPart I e).card + 2 := by
  have hpath :
      (subdivisionPathPart I e).card =
        ∑ i : Fin (2 * t e + 2),
          if oddSubdivisionPathVertex t e i ∈ I then (1 : ℕ) else 0 := by
    simp [subdivisionPathPart]
  have hinterior :
      (subdivisionInternalPart I e).card =
        ∑ i : Fin (2 * t e),
          if Sum.inr (Sigma.mk e i) ∈ I then (1 : ℕ) else 0 := by
    simp [subdivisionInternalPart]
  rw [hpath, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [oddSubdivisionPathVertex_zero,
    oddSubdivisionPathVertex_internal]
  rw [Fin.succ_last, oddSubdivisionPathVertex_last]
  rw [if_pos hlo, if_pos hhi, ← hinterior]
  omega

lemma subdivisionInternalPart_card_add_indicator_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (I : Finset (OddSubdivisionVertex F t))
    (hI : (oddSubdivisionGraph F t).IsIndepSet (I : Set _))
    (e : OrientedEdge F) :
    (subdivisionInternalPart I e).card +
        (if Sum.inl e.lo ∈ I ∧ Sum.inl e.hi ∈ I then 1 else 0) ≤ t e := by
  by_cases hb : Sum.inl e.lo ∈ I ∧ Sum.inl e.hi ∈ I
  · rw [if_pos hb]
    have hp := subdivisionPathPart_card_le t I hI e
    have heq := subdivisionPathPart_card_eq_internal_add_two_of_endpoints
      t I e hb.1 hb.2
    omega
  · rw [if_neg hb, Nat.add_zero]
    exact subdivisionInternalPart_card_le t I hI e

def subdivisionBadEdges {F : SimpleGraph U} {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) : Finset (OrientedEdge F) :=
  Finset.univ.filter fun e ↦ Sum.inl e.lo ∈ I ∧ Sum.inl e.hi ∈ I

def subdivisionBadHighVertices {F : SimpleGraph U} {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) : Finset U :=
  (subdivisionBadEdges I).image OrientedEdge.hi

def subdivisionBaseIndependent {F : SimpleGraph U} {t : OrientedEdge F → ℕ}
    (I : Finset (OddSubdivisionVertex F t)) : Finset U :=
  subdivisionBranchPart I \ subdivisionBadHighVertices I

lemma subdivisionBaseIndependent_isIndepSet {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ} (I : Finset (OddSubdivisionVertex F t)) :
    F.IsIndepSet (subdivisionBaseIndependent I : Set U) := by
  intro u hu v hv huv hadj
  have hu' := Finset.mem_sdiff.mp hu
  have hv' := Finset.mem_sdiff.mp hv
  have huB : Sum.inl u ∈ I := by simpa using hu'.1
  have hvB : Sum.inl v ∈ I := by simpa using hv'.1
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · let e : OrientedEdge F := ⟨(u, v), huvlt, hadj⟩
    have heBad : e ∈ subdivisionBadEdges I := by
      rw [subdivisionBadEdges, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change Sum.inl u ∈ I ∧ Sum.inl v ∈ I
      exact ⟨huB, hvB⟩
    have hvHigh : v ∈ subdivisionBadHighVertices I := by
      exact Finset.mem_image.mpr ⟨e, heBad, rfl⟩
    exact hv'.2 hvHigh
  · let e : OrientedEdge F := ⟨(v, u), hvult, hadj.symm⟩
    have heBad : e ∈ subdivisionBadEdges I := by
      rw [subdivisionBadEdges, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change Sum.inl v ∈ I ∧ Sum.inl u ∈ I
      exact ⟨hvB, huB⟩
    have huHigh : u ∈ subdivisionBadHighVertices I := by
      exact Finset.mem_image.mpr ⟨e, heBad, rfl⟩
    exact hu'.2 huHigh

lemma subdivisionBranchPart_card_le_indepNum_add_badEdges {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ} (I : Finset (OddSubdivisionVertex F t)) :
    (subdivisionBranchPart I).card ≤
      F.indepNum + (subdivisionBadEdges I).card := by
  let B := subdivisionBranchPart I
  let R := subdivisionBadHighVertices I
  let A := subdivisionBaseIndependent I
  have hAind : F.IsIndepSet (A : Set U) :=
    subdivisionBaseIndependent_isIndepSet I
  have hAcard : A.card ≤ F.indepNum := hAind.card_le_indepNum
  have hRcard : R.card ≤ (subdivisionBadEdges I).card := by
    exact Finset.card_image_le
  have hinter : (B ∩ R).card ≤ R.card :=
    Finset.card_le_card (Finset.inter_subset_right)
  have hsplit : (B \ R).card + (B ∩ R).card = B.card :=
    Finset.card_sdiff_add_card_inter B R
  have hAeq : A = B \ R := rfl
  calc
    (subdivisionBranchPart I).card = B.card := rfl
    _ = (B \ R).card + (B ∩ R).card := hsplit.symm
    _ = A.card + (B ∩ R).card := by rw [hAeq]
    _ ≤ F.indepNum + (subdivisionBadEdges I).card :=
      Nat.add_le_add hAcard (hinter.trans hRcard)

lemma card_eq_branch_add_sum_internal {F : SimpleGraph U}
    {t : OrientedEdge F → ℕ} (I : Finset (OddSubdivisionVertex F t)) :
    I.card = (subdivisionBranchPart I).card +
      ∑ e : OrientedEdge F, (subdivisionInternalPart I e).card := by
  have hcard : I.card =
      ∑ v : OddSubdivisionVertex F t, if v ∈ I then (1 : ℕ) else 0 := by
    simp
  rw [hcard]
  have hbranch : (subdivisionBranchPart I).card =
      ∑ u : U, if Sum.inl u ∈ I then (1 : ℕ) else 0 := by
    simp [subdivisionBranchPart]
  have hinter (e : OrientedEdge F) : (subdivisionInternalPart I e).card =
      ∑ i : Fin (2 * t e),
        if Sum.inr (Sigma.mk e i) ∈ I then (1 : ℕ) else 0 := by
    simp [subdivisionInternalPart]
  calc
    (∑ v : OddSubdivisionVertex F t, if v ∈ I then (1 : ℕ) else 0) =
        (∑ u : U, if Sum.inl u ∈ I then (1 : ℕ) else 0) +
          ∑ z : (Σ e : OrientedEdge F, Fin (2 * t e)),
            if Sum.inr z ∈ I then (1 : ℕ) else 0 :=
      Fintype.sum_sum_type _
    _ = (∑ u : U, if Sum.inl u ∈ I then (1 : ℕ) else 0) +
          ∑ e : OrientedEdge F, ∑ i : Fin (2 * t e),
            if Sum.inr (Sigma.mk e i) ∈ I then (1 : ℕ) else 0 := by
      rw [Fintype.sum_sigma]
    _ = (subdivisionBranchPart I).card +
          ∑ e : OrientedEdge F, (subdivisionInternalPart I e).card := by
      rw [hbranch]
      simp_rw [← hinter]

lemma sum_internal_add_badEdges_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (I : Finset (OddSubdivisionVertex F t))
    (hI : (oddSubdivisionGraph F t).IsIndepSet (I : Set _)) :
    (∑ e : OrientedEdge F, (subdivisionInternalPart I e).card) +
        (subdivisionBadEdges I).card ≤ ∑ e : OrientedEdge F, t e := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (OrientedEdge F)))
    (fun e _ ↦ subdivisionInternalPart_card_add_indicator_le t I hI e)
  rw [Finset.sum_add_distrib] at hsum
  have hbad :
      (∑ e : OrientedEdge F,
        if Sum.inl e.lo ∈ I ∧ Sum.inl e.hi ∈ I then 1 else 0) =
        (subdivisionBadEdges I).card := by
    simp [subdivisionBadEdges]
  rw [hbad] at hsum
  exact hsum

/-- Every independent set in an odd subdivision is bounded by a base
independent set plus one vertex for each inserted pair. -/
theorem oddSubdivision_isIndepSet_card_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (I : Finset (OddSubdivisionVertex F t))
    (hI : (oddSubdivisionGraph F t).IsIndepSet (I : Set _)) :
    I.card ≤ F.indepNum + ∑ e : OrientedEdge F, t e := by
  have hdecomp := card_eq_branch_add_sum_internal I
  have hbranch := subdivisionBranchPart_card_le_indepNum_add_badEdges I
  have hinternal := sum_internal_add_badEdges_le t I hI
  omega

theorem oddSubdivision_indepNum_le {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) :
    (oddSubdivisionGraph F t).indepNum ≤
      F.indepNum + ∑ e : OrientedEdge F, t e := by
  obtain ⟨I, hI, hIcard⟩ :=
    (oddSubdivisionGraph F t).exists_isNIndepSet_indepNum
  rw [← hIcard]
  exact oddSubdivision_isIndepSet_card_le t I hI

@[simp] lemma card_oddSubdivisionVertex (F : SimpleGraph U)
    (t : OrientedEdge F → ℕ) :
    Fintype.card (OddSubdivisionVertex F t) =
      Fintype.card U + ∑ e : OrientedEdge F, 2 * t e := by
  rw [Fintype.card_sum, Fintype.card_sigma]
  simp

/-- Odd subdivision preserves every additive independence defect of the
base graph. -/
theorem oddSubdivision_hasIndependenceDefectAtLeast {F : SimpleGraph U}
    (t : OrientedEdge F → ℕ) (r : ℕ)
    (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r (oddSubdivisionGraph F t) := by
  let S := oddSubdivisionGraph F t
  refine ⟨(⊤ : S.Subgraph), ?_⟩
  have hindepIso : (⊤ : S.Subgraph).coe.indepNum = S.indepNum :=
    indepNum_eq_of_iso SimpleGraph.Subgraph.topIso
  have hindep := oddSubdivision_indepNum_le t
  have hcard : (⊤ : S.Subgraph).verts.ncard = Fintype.card U +
      ∑ e : OrientedEdge F, 2 * t e := by
    change Set.univ.ncard = _
    rw [Set.ncard_univ, Nat.card_eq_fintype_card,
      card_oddSubdivisionVertex]
  rw [hindepIso, hcard]
  have htwosum :
      2 * (∑ e : OrientedEdge F, t e) =
        ∑ e : OrientedEdge F, 2 * t e := by
    rw [Finset.mul_sum]
  change 2 * (oddSubdivisionGraph F t).indepNum + r ≤
    Fintype.card U + ∑ e : OrientedEdge F, 2 * t e
  calc
    2 * (oddSubdivisionGraph F t).indepNum + r ≤
        2 * (F.indepNum + ∑ e : OrientedEdge F, t e) + r :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hindep) r
    _ = (2 * F.indepNum + r) +
        2 * (∑ e : OrientedEdge F, t e) := by omega
    _ ≤ Fintype.card U + 2 * (∑ e : OrientedEdge F, t e) :=
      Nat.add_le_add_right hF _
    _ = Fintype.card U + ∑ e : OrientedEdge F, 2 * t e := by rw [htwosum]

/-- Every odd subdivision of the canonical twisted grid remains a
hereditary defect obstruction. -/
theorem oddSubdivision_twistedGrid_hasIndependenceDefectAtLeast (k : ℕ)
    (t : OrientedEdge (twistedGridGraph (2 * (k + 1))) → ℕ) :
    HasIndependenceDefectAtLeast (k + 1)
      (oddSubdivisionGraph (twistedGridGraph (2 * (k + 1))) t) := by
  apply oddSubdivision_hasIndependenceDefectAtLeast t (k + 1)
  exact twistedGrid_full_defect k

/-- One of the two outer ports of a three-vertex replacement path. -/
def splitPort : Bool → Fin 3
  | false => 0
  | true => 2

def threeSplitGraph {U : Type*} (F : SimpleGraph U)
    (port : U → U → Bool) : SimpleGraph (U × Fin 3) where
  Adj a b :=
    (a.1 = b.1 ∧ (SimpleGraph.pathGraph 3).Adj a.2 b.2) ∨
      (F.Adj a.1 b.1 ∧ a.2 = splitPort (port a.1 b.1) ∧
        b.2 = splitPort (port b.1 a.1))
  symm := by
    constructor
    intro a b h
    rcases h with ⟨hab, hij⟩ | ⟨hab, ha, hb⟩
    · exact Or.inl ⟨hab.symm, hij.symm⟩
    · exact Or.inr ⟨hab.symm, hb, ha⟩
  loopless := by
    constructor
    intro a h
    rcases h with ⟨_, h⟩ | ⟨h, _, _⟩
    · exact (SimpleGraph.pathGraph 3).irrefl h
    · exact F.irrefl h

def threeSplitHigh {U : Type*} [Fintype U]
    (I : Finset (U × Fin 3)) : Finset U :=
  Finset.univ.filter fun u ↦ (u, 0) ∈ I ∧ (u, 2) ∈ I

def threeSplitFiber {U : Type*} (I : Finset (U × Fin 3))
    (u : U) : Finset (Fin 3) :=
  Finset.univ.filter fun i ↦ (u, i) ∈ I

lemma threeSplitHigh_isIndepSet {U : Type*} [Fintype U]
    {F : SimpleGraph U} {port : U → U → Bool}
    {I : Finset (U × Fin 3)}
    (hI : (threeSplitGraph F port).IsIndepSet (I : Set _)) :
    F.IsIndepSet (threeSplitHigh I : Set U) := by
  intro u hu v hv huv hadj
  have hu' : (u, 0) ∈ I ∧ (u, 2) ∈ I := (Finset.mem_filter.mp hu).2
  have hv' : (v, 0) ∈ I ∧ (v, 2) ∈ I := (Finset.mem_filter.mp hv).2
  have hpu : (u, splitPort (port u v)) ∈ I := by
    cases port u v <;> simp_all [splitPort]
  have hpv : (v, splitPort (port v u)) ∈ I := by
    cases port v u <;> simp_all [splitPort]
  have hne : (u, splitPort (port u v)) ≠ (v, splitPort (port v u)) := by
    intro h
    exact huv (congrArg Prod.fst h)
  exact hI hpu hpv hne (Or.inr ⟨hadj, rfl, rfl⟩)

lemma threeSplitFiber_card_le {U : Type*} [Fintype U]
    {F : SimpleGraph U} {port : U → U → Bool}
    {I : Finset (U × Fin 3)}
    (hI : (threeSplitGraph F port).IsIndepSet (I : Set _)) (u : U) :
    (threeSplitFiber I u).card ≤ 1 + if u ∈ threeSplitHigh I then 1 else 0 := by
  have h01 : ¬ ((u, 0) ∈ I ∧ (u, 1) ∈ I) := by
    rintro ⟨h0, h1⟩
    exact hI h0 h1 (by simp) (Or.inl ⟨rfl, by
      change (SimpleGraph.pathGraph 3).Adj (0 : Fin 3) 1
      simp [SimpleGraph.pathGraph_adj]⟩)
  have h12 : ¬ ((u, 1) ∈ I ∧ (u, 2) ∈ I) := by
    rintro ⟨h1, h2⟩
    exact hI h1 h2 (by simp) (Or.inl ⟨rfl, by
      change (SimpleGraph.pathGraph 3).Adj (1 : Fin 3) 2
      simp [SimpleGraph.pathGraph_adj]⟩)
  rw [threeSplitFiber, Finset.card_filter]
  simp only [Fin.sum_univ_succ]
  by_cases h0 : (u, 0) ∈ I <;> by_cases h1 : (u, 1) ∈ I <;>
    by_cases h2 : (u, 2) ∈ I <;>
    simp_all [threeSplitHigh]

lemma threeSplit_card_eq_sum {U : Type*} [Fintype U]
    (I : Finset (U × Fin 3)) :
    I.card = ∑ u : U, (threeSplitFiber I u).card := by
  have hcard : I.card = ∑ z : U × Fin 3, if z ∈ I then (1 : ℕ) else 0 := by
    simp
  rw [hcard, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [threeSplitFiber, Finset.card_filter]

theorem threeSplit_isIndepSet_card_le {U : Type*} [Fintype U]
    {F : SimpleGraph U} {port : U → U → Bool}
    {I : Finset (U × Fin 3)}
    (hI : (threeSplitGraph F port).IsIndepSet (I : Set _)) :
    I.card ≤ Fintype.card U + F.indepNum := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset U))
    (fun u _ ↦ threeSplitFiber_card_le hI u)
  rw [← threeSplit_card_eq_sum I, Finset.sum_add_distrib] at hsum
  have hsum' : I.card ≤ Fintype.card U + (threeSplitHigh I).card := by
    simpa using hsum
  exact hsum'.trans (Nat.add_le_add_left (threeSplitHigh_isIndepSet hI).card_le_indepNum _)

theorem threeSplit_indepNum_le {U : Type*} [Fintype U]
    (F : SimpleGraph U) (port : U → U → Bool) :
    (threeSplitGraph F port).indepNum ≤ Fintype.card U + F.indepNum := by
  obtain ⟨I, hI, hIcard⟩ := (threeSplitGraph F port).exists_isNIndepSet_indepNum
  rw [← hIcard]
  exact threeSplit_isIndepSet_card_le hI

theorem threeSplit_full_defect {U : Type*} [Fintype U]
    (F : SimpleGraph U) (port : U → U → Bool) (r : ℕ)
    (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    2 * (threeSplitGraph F port).indepNum + r ≤ Fintype.card (U × Fin 3) := by
  have hi := threeSplit_indepNum_le F port
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega


/-- Splitting every grid vertex into a three-vertex path preserves the
whole-graph defect, for every assignment of incident edges to outer ports. -/
theorem threeSplit_twistedGrid_full_defect (k : ℕ)
    (port : (Fin (2 * (k + 1)) × Fin (2 * (k + 1))) →
      (Fin (2 * (k + 1)) × Fin (2 * (k + 1))) → Bool) :
    2 * (threeSplitGraph (twistedGridGraph (2 * (k + 1))) port).indepNum +
      (k + 1) ≤ Fintype.card
        ((Fin (2 * (k + 1)) × Fin (2 * (k + 1))) × Fin 3) :=
  threeSplit_full_defect _ port (k + 1) (twistedGrid_full_defect k)

/-- The wall-compatible three-vertex expansion and arbitrary odd edge
subdivisions retain the canonical twisted-grid defect. -/
theorem oddSubdivision_threeSplit_twistedGrid_hasIndependenceDefectAtLeast
    (k : ℕ)
    (port : (Fin (2 * (k + 1)) × Fin (2 * (k + 1))) →
      (Fin (2 * (k + 1)) × Fin (2 * (k + 1))) → Bool)
    (t : OrientedEdge
      (threeSplitGraph (twistedGridGraph (2 * (k + 1))) port) → ℕ) :
    HasIndependenceDefectAtLeast (k + 1)
      (oddSubdivisionGraph
        (threeSplitGraph (twistedGridGraph (2 * (k + 1))) port) t) :=
  oddSubdivision_hasIndependenceDefectAtLeast t (k + 1)
    (threeSplit_twistedGrid_full_defect k port)

/-- A host graph contains an arbitrary odd subdivision of the canonical
twisted grid of order `2*m`. -/
def HasOddSubdivisionTwistedGrid {V : Type*} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ t : OrientedEdge (twistedGridGraph (2 * m)) → ℕ,
    Nonempty (SimpleGraph.Copy
      (oddSubdivisionGraph (twistedGridGraph (2 * m)) t) G)

/-- A path-routing presentation of an odd subdivision.  The vertex map is
injective globally, while `map_path_adj` says that the vertices assigned to
each oriented base edge follow a path in the host.  This is the convenient
output interface for wall and perimeter-routing arguments. -/
structure OddSubdivisionRouting {V : Type*} [Fintype V]
    (F : SimpleGraph U) (G : SimpleGraph V) where
  t : OrientedEdge F → ℕ
  vertex : OddSubdivisionVertex F t → V
  vertex_injective : Function.Injective vertex
  map_path_adj : ∀ (e : OrientedEdge F) ⦃i j : Fin (2 * t e + 2)⦄,
    (SimpleGraph.pathGraph (2 * t e + 2)).Adj i j →
      G.Adj (vertex (oddSubdivisionPathVertex t e i))
        (vertex (oddSubdivisionPathVertex t e j))

namespace OddSubdivisionRouting

variable {V W : Type*} [Fintype V] [Fintype W]
  {F : SimpleGraph U} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- A routing really is an ordinary subgraph copy of the corresponding odd
subdivision.  Extra host edges are deliberately harmless. -/
def toCopy (R : OddSubdivisionRouting F G) :
    SimpleGraph.Copy (oddSubdivisionGraph F R.t) G := by
  refine ⟨{ toFun := R.vertex, map_rel' := ?_ }, R.vertex_injective⟩
  intro a b hab
  rw [oddSubdivisionGraph, SimpleGraph.iSup_adj] at hab
  obtain ⟨e, he⟩ := hab
  rw [SimpleGraph.map_adj'] at he
  obtain ⟨-, i, j, hij, rfl, rfl⟩ := he
  exact R.map_path_adj e hij

/-- A host-graph copy transports every odd-subdivision routing. -/
def mapCopy (R : OddSubdivisionRouting F G) (f : SimpleGraph.Copy G G') :
    OddSubdivisionRouting F G' where
  t := R.t
  vertex := f ∘ R.vertex
  vertex_injective := f.injective.comp R.vertex_injective
  map_path_adj e _ _ hij := f.toHom.map_adj (R.map_path_adj e hij)

lemma hasOddSubdivisionTwistedGrid (m : ℕ)
    (R : OddSubdivisionRouting (twistedGridGraph (2 * m)) G) :
    HasOddSubdivisionTwistedGrid m G :=
  ⟨R.t, ⟨R.toCopy⟩⟩

end OddSubdivisionRouting

lemma HasOddSubdivisionTwistedGrid.map_embedding
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {m : ℕ}
    (h : HasOddSubdivisionTwistedGrid m G) (f : G ↪g G') :
    HasOddSubdivisionTwistedGrid m G' := by
  obtain ⟨t, ⟨g⟩⟩ := h
  let fcopy : SimpleGraph.Copy G G' := ⟨f.toHom, f.injective⟩
  exact ⟨t, ⟨fcopy.comp g⟩⟩

lemma HasOddSubdivisionTwistedGrid.hasIndependenceDefectAtLeast
    {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : HasOddSubdivisionTwistedGrid (k + 1) G) :
    HasIndependenceDefectAtLeast (k + 1) G := by
  obtain ⟨t, ⟨f⟩⟩ := h
  exact (oddSubdivision_twistedGrid_hasIndependenceDefectAtLeast k t).map_copy f

/-- Embedded odd subdivisions of a fixed twisted grid form an
embedding-stable obstruction. -/
def oddSubdivisionTwistedGridObstruction (m : ℕ) :
    EmbeddingStableGraphObstruction.{0} where
  Holds := HasOddSubdivisionTwistedGrid m
  map_embedding h f := h.map_embedding f

/-- A stronger sufficient high-order condition with a square-grid
subdivision outcome.  This is not the source Escher-wall theorem: subcubic
walls require splitting degree-four grid vertices before this containment
can be used.  It is retained as a proved conditional interface only. -/
def ReedOddSubdivisionHighOrderBrambleStatement : Prop :=
  ∀ m : ℕ, UniformHighOrderGraphObstructionStatement.{0}
    (oddSubdivisionTwistedGridObstruction m)

/-- The odd-subdivision structural outcome implies the intrinsic-defect
high-order theorem. -/
theorem reedDefectHighOrderBrambleStatement_of_oddSubdivision
    (h : ReedOddSubdivisionHighOrderBrambleStatement) :
    ReedDefectHighOrderBrambleStatement := by
  intro r p C
  obtain ⟨ell, D, hrec, hhigh⟩ := h (r + 1) p C
  refine ⟨ell, D, hrec, ?_⟩
  intro V _ G hbramble horder
  rcases hhigh V G hbramble horder with hpack | hdelete | hmodel
  · exact Or.inl hpack
  · exact Or.inr (Or.inl hdelete)
  · exact Or.inr (Or.inr hmodel.hasIndependenceDefectAtLeast)

/-- The stronger square-grid sufficient condition implies Problem 73.
This conditional reduction is not the unconditional final theorem. -/
theorem problem73_of_oddSubdivisionHighOrderBramble
    (h : ReedOddSubdivisionHighOrderBrambleStatement) : Problem73 :=
  problem73_of_defectHighOrderBramble
    (reedDefectHighOrderBrambleStatement_of_oddSubdivision h)

end

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma IsVertexSeparation.flip {A B : Finset V}
    (h : IsVertexSeparation G A B) : IsVertexSeparation G B A := by
  refine ⟨by rw [Finset.union_comm]; exact h.1, ?_⟩
  intro a b haB haA hbA hbB hab
  exact h.2 hbA hbB haB haA hab.symm

lemma connected_finset_subset_side_of_disjoint_separator
    {A B T : Finset V} (hsep : IsVertexSeparation G A B)
    (hconn : (G.induce (T : Set V)).Connected)
    (hTS : Disjoint T (A ∩ B)) : T ⊆ A \ B ∨ T ⊆ B \ A := by
  have hside : ∀ v ∈ T, (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
    intro v hvT
    have hvnot : v ∉ A ∩ B := Finset.disjoint_left.mp hTS hvT
    have hvcover : v ∈ A ∪ B := by rw [hsep.1]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hvcover with hvA | hvB
    · exact Or.inl ⟨hvA, fun hvB ↦ hvnot (Finset.mem_inter.mpr ⟨hvA, hvB⟩)⟩
    · exact Or.inr ⟨hvB, fun hvA ↦ hvnot (Finset.mem_inter.mpr ⟨hvA, hvB⟩)⟩
  have closed : ∀ {a b : T}, (G.induce (T : Set V)).Adj a b →
      a.1 ∈ A → b.1 ∈ A := by
    intro a b hab ha
    have haB : a.1 ∉ B := by
      rcases hside a.1 a.2 with h | h
      · exact h.2
      · exact (h.2 ha).elim
    by_contra hb
    have hbB : b.1 ∈ B := by
      rcases hside b.1 b.2 with h | h
      · exact (hb h.1).elim
      · exact h.1
    exact hsep.2 ha haB hbB hb hab
  have reach_closed : ∀ {a b : T}, (G.induce (T : Set V)).Reachable a b →
      a.1 ∈ A → b.1 ∈ A := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun ha ↦ ih (closed hab ha)
  by_cases hTA : ∃ a ∈ T, a ∈ A
  · obtain ⟨a, haT, haA⟩ := hTA
    left
    intro b hbT
    have hbA := reach_closed (hconn.preconnected ⟨a, haT⟩ ⟨b, hbT⟩) haA
    rcases hside b hbT with h | h
    · exact Finset.mem_sdiff.mpr h
    · exact (h.2 hbA).elim
  · right
    intro b hbT
    rcases hside b hbT with h | h
    · exact (hTA ⟨b, hbT, h.1⟩).elim
    · exact Finset.mem_sdiff.mpr h

lemma not_finsetTouches_of_separation_sides {A B S T : Finset V}
    (hsep : IsVertexSeparation G A B) (hS : S ⊆ A \ B) (hT : T ⊆ B \ A) :
    ¬ FinsetTouches G S T := by
  rintro (hinter | ⟨s, hs, t, ht, hst⟩)
  · apply hinter
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp (hS hvS)).2 (Finset.mem_sdiff.mp (hT hvT)).1
  · exact hsep.2 (Finset.mem_sdiff.mp (hS hs)).1
      (Finset.mem_sdiff.mp (hS hs)).2
      (Finset.mem_sdiff.mp (hT ht)).1
      (Finset.mem_sdiff.mp (hT ht)).2 hst

def IsBrambleHittingSet (β : Finset (Finset V)) (X : Finset V) : Prop :=
  ∀ T ∈ β, ¬ Disjoint X T

def IsMinimumBrambleHittingSet (β : Finset (Finset V)) (X : Finset V) : Prop :=
  IsBrambleHittingSet β X ∧
    ∀ Y : Finset V, IsBrambleHittingSet β Y → X.card ≤ Y.card

lemma exists_minimumBrambleHittingSet {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) :
    ∃ X : Finset V, IsMinimumBrambleHittingSet β X := by
  let P : ℕ → Prop := fun n ↦
    ∃ X : Finset V, IsBrambleHittingSet β X ∧ X.card = n
  have hex : ∃ n, P n := by
    refine ⟨Fintype.card V, Finset.univ, ?_, by simp⟩
    intro T hT hdisj
    obtain ⟨v⟩ := (hβ.1 T hT).nonempty
    exact Finset.disjoint_left.mp hdisj (Finset.mem_univ v.1) v.2
  obtain ⟨X, hX, hcard⟩ := Nat.find_spec hex
  refine ⟨X, hX, ?_⟩
  intro Y hY
  have hmin := Nat.find_min' hex ⟨Y, hY, rfl⟩
  simpa only [hcard] using hmin

lemma bramble_avoiding_separator_one_side {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {A B : Finset V}
    (hsep : IsVertexSeparation G A B) :
    (∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ A \ B) ∨
      (∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ B \ A) := by
  by_cases hleft : ∃ T ∈ β, Disjoint T (A ∩ B) ∧ T ⊆ A \ B
  · obtain ⟨T₀, hT₀, hT₀disj, hT₀A⟩ := hleft
    left
    intro T hT hTdisj
    rcases connected_finset_subset_side_of_disjoint_separator
      hsep (hβ.1 T hT) hTdisj with hTA | hTB
    · exact hTA
    · by_cases hEq : T₀ = T
      · subst T
        exact hT₀A
      · exact (not_finsetTouches_of_separation_sides hsep hT₀A hTB
          (hβ.2 T₀ hT₀ T hT hEq)).elim
  · right
    intro T hT hTdisj
    rcases connected_finset_subset_side_of_disjoint_separator
      hsep (hβ.1 T hT) hTdisj with hTA | hTB
    · exact (hleft ⟨T, hT, hTdisj, hTA⟩).elim
    · exact hTB

lemma bramble_replacement_hits {β : Finset (Finset V)}
    {A B X : Finset V} (hX : IsBrambleHittingSet β X)
    (hside : ∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ A \ B) :
    IsBrambleHittingSet β ((X ∩ (A \ B)) ∪ (A ∩ B)) := by
  intro T hT hdisj
  by_cases hTS : Disjoint T (A ∩ B)
  · obtain ⟨v, hvX, hvT⟩ := Finset.not_disjoint_iff.mp (hX T hT)
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvX, hside T hT hTS hvT⟩)) hvT
  · obtain ⟨v, hvT, hvS⟩ := Finset.not_disjoint_iff.mp hTS
    exact Finset.disjoint_left.mp hdisj (Finset.mem_union_right _ hvS) hvT

lemma card_inter_exclusive_add_inter {A B X : Finset V}
    (hcover : A ∪ B = Finset.univ) :
    (X ∩ (A \ B)).card + (X ∩ B).card = X.card := by
  have hdisj : Disjoint (X ∩ (A \ B)) (X ∩ B) := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvA).2).2
      (Finset.mem_inter.mp hvB).2
  have hunion : (X ∩ (A \ B)) ∪ (X ∩ B) = X := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hvX
      have hvAB : v ∈ A ∪ B := by rw [hcover]; exact Finset.mem_univ _
      by_cases hvB : v ∈ B
      · exact Or.inr ⟨hvX, hvB⟩
      · exact Or.inl ⟨hvX, (Finset.mem_union.mp hvAB).resolve_right hvB, hvB⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

theorem minimumBrambleHittingSet_cutLinked {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {X : Finset V}
    (hX : IsMinimumBrambleHittingSet β X) {A B : Finset V}
    (hsep : IsVertexSeparation G A B) :
    (X ∩ A).card ≤ (A ∩ B).card ∨ (X ∩ B).card ≤ (A ∩ B).card := by
  have one_side (A B : Finset V) (hcover : A ∪ B = Finset.univ)
      (hside : ∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ A \ B) :
      (X ∩ B).card ≤ (A ∩ B).card := by
    have hhit := bramble_replacement_hits hX.1 hside
    have hmin := hX.2 _ hhit
    have hcard := Finset.card_union_le (X ∩ (A \ B)) (A ∩ B)
    have hsplit := card_inter_exclusive_add_inter (X := X) hcover
    omega
  rcases bramble_avoiding_separator_one_side hβ hsep with hleft | hright
  · exact Or.inr (one_side A B hsep.1 hleft)
  · left
    have hright' : ∀ T ∈ β, Disjoint T (B ∩ A) → T ⊆ B \ A := by
      simpa only [Finset.inter_comm] using hright
    simpa only [Finset.inter_comm] using one_side B A hsep.flip.1 hright'


end

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The separation form of node well-linkedness. -/
def IsCutLinkedSet (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ A B : Finset V, IsVertexSeparation G A B →
    (X ∩ A).card ≤ (A ∩ B).card ∨ (X ∩ B).card ≤ (A ∩ B).card

theorem exists_cutLinkedSet_of_bramble {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ} (horder : BrambleOrderAtLeast q β) :
    ∃ X : Finset V, q ≤ X.card ∧ IsCutLinkedSet G X := by
  obtain ⟨X, hX⟩ := exists_minimumBrambleHittingSet hβ
  exact ⟨X, horder X hX.1, fun _ _ hsep ↦ minimumBrambleHittingSet_cutLinked hβ hX hsep⟩

/-- A finite vertex-separation tangle.  The non-covering condition on the
three small vertex sides implies the usual non-covering condition on their
induced subgraphs. -/
structure VertexTangle (G : SimpleGraph V) (q : ℕ) where
  towards : Finset V → Finset V → Prop
  valid : ∀ {A B}, towards A B → IsVertexSeparation G A B ∧ (A ∩ B).card < q
  orients : ∀ {A B}, IsVertexSeparation G A B → (A ∩ B).card < q →
    (towards A B ∧ ¬ towards B A) ∨ (towards B A ∧ ¬ towards A B)
  no_triple_cover : ∀ {A₁ B₁ A₂ B₂ A₃ B₃},
    towards A₁ B₁ → towards A₂ B₂ → towards A₃ B₃ →
      (A₁ ∪ A₂) ∪ A₃ ≠ Finset.univ

def cutLinkedOrientation (G : SimpleGraph V) (q : ℕ) (X : Finset V)
    (A B : Finset V) : Prop :=
  IsVertexSeparation G A B ∧ (A ∩ B).card < q ∧ (X ∩ A).card < q

lemma card_le_inter_add_inter_of_cover (X A B : Finset V)
    (hcover : A ∪ B = Finset.univ) :
    X.card ≤ (X ∩ A).card + (X ∩ B).card := by
  have hunion : X ∩ A ∪ X ∩ B = X := by
    rw [← Finset.inter_union_distrib_left, hcover, Finset.inter_univ]
  have hcard := Finset.card_union_le (X ∩ A) (X ∩ B)
  rwa [hunion] at hcard

lemma cutLinkedOrientation_orients {q : ℕ} {X : Finset V}
    (hX : IsCutLinkedSet G X) (hcard : 3 * q ≤ X.card)
    {A B : Finset V} (hsep : IsVertexSeparation G A B) (hsmall : (A ∩ B).card < q) :
    (cutLinkedOrientation G q X A B ∧ ¬ cutLinkedOrientation G q X B A) ∨
      (cutLinkedOrientation G q X B A ∧ ¬ cutLinkedOrientation G q X A B) := by
  have hsum := card_le_inter_add_inter_of_cover X A B hsep.1
  rcases hX A B hsep with hA | hB
  · left
    refine ⟨⟨hsep, hsmall, hA.trans_lt hsmall⟩, ?_⟩
    intro hBA
    have hBsmall := hBA.2.2
    omega
  · right
    refine ⟨⟨hsep.flip, by simpa only [Finset.inter_comm] using hsmall,
      hB.trans_lt hsmall⟩, ?_⟩
    intro hAB
    have hAsmall := hAB.2.2
    omega

lemma cutLinkedOrientation_no_triple_cover {q : ℕ} {X : Finset V}
    (hcard : 3 * q ≤ X.card)
    {A₁ B₁ A₂ B₂ A₃ B₃ : Finset V}
    (h₁ : cutLinkedOrientation G q X A₁ B₁)
    (h₂ : cutLinkedOrientation G q X A₂ B₂)
    (h₃ : cutLinkedOrientation G q X A₃ B₃) :
    (A₁ ∪ A₂) ∪ A₃ ≠ Finset.univ := by
  intro hcover
  have hsum := card_le_inter_add_inter_of_cover X (A₁ ∪ A₂) A₃ hcover
  have hsub : (X ∩ (A₁ ∪ A₂)).card ≤ (X ∩ A₁).card + (X ∩ A₂).card := by
    rw [Finset.inter_union_distrib_left]
    exact Finset.card_union_le _ _
  have hsmall₁ := h₁.2.2
  have hsmall₂ := h₂.2.2
  have hsmall₃ := h₃.2.2
  omega

def vertexTangleOfCutLinkedSet {q : ℕ} {X : Finset V}
    (hX : IsCutLinkedSet G X) (hcard : 3 * q ≤ X.card) : VertexTangle G q where
  towards := cutLinkedOrientation G q X
  valid h := ⟨h.1, h.2.1⟩
  orients := cutLinkedOrientation_orients hX hcard
  no_triple_cover := cutLinkedOrientation_no_triple_cover hcard

theorem exists_vertexTangle_of_bramble {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ}
    (horder : BrambleOrderAtLeast (3 * q) β) : Nonempty (VertexTangle G q) := by
  obtain ⟨X, hcard, hX⟩ := exists_cutLinkedSet_of_bramble hβ horder
  exact ⟨vertexTangleOfCutLinkedSet hX hcard⟩

lemma minimumBrambleHittingSet_oppositeSide_card_le {β : Finset (Finset V)}
    {X A B : Finset V} (hX : IsMinimumBrambleHittingSet β X)
    (hcover : A ∪ B = Finset.univ)
    (hside : ∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ A \ B) :
    (X ∩ B).card ≤ (A ∩ B).card := by
  have hhit := bramble_replacement_hits hX.1 hside
  have hmin := hX.2 _ hhit
  have hcard := Finset.card_union_le (X ∩ (A \ B)) (A ∩ B)
  have hsplit := card_inter_exclusive_add_inter (X := X) hcover
  omega

/-- The tangle points toward every bramble member which avoids its
separator.  This retains the controlling information of the source bramble,
not just its numerical order. -/
theorem exists_vertexTangle_controlling_bramble {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ}
    (horder : BrambleOrderAtLeast (3 * q) β) :
    ∃ τ : VertexTangle G q, ∀ A B : Finset V, τ.towards A B →
      ∀ T ∈ β, Disjoint T (A ∩ B) → T ⊆ B \ A := by
  obtain ⟨X, hX⟩ := exists_minimumBrambleHittingSet hβ
  have hcard : 3 * q ≤ X.card := horder X hX.1
  have hcut : IsCutLinkedSet G X :=
    fun _ _ hsep ↦ minimumBrambleHittingSet_cutLinked hβ hX hsep
  let τ := vertexTangleOfCutLinkedSet hcut hcard
  refine ⟨τ, ?_⟩
  intro A B hτ
  change cutLinkedOrientation G q X A B at hτ
  rcases bramble_avoiding_separator_one_side hβ hτ.1 with hleft | hright
  · have hB := minimumBrambleHittingSet_oppositeSide_card_le hX hτ.1.1 hleft
    have hsum := card_le_inter_add_inter_of_cover X A B hτ.1.1
    have hA := hτ.2.2
    have hS := hτ.2.1
    omega
  · exact hright


end

end Erdos73

#print axioms Erdos73.problem73_zero
#print axioms Erdos73.problem73_iff_reedNearBipartiteStatement
#print axioms Erdos73.problem73_iff_generalProblem73
#print axioms Erdos73.not_hasOddCyclePacking_succ
#print axioms Erdos73.oddSubdivision_threeSplit_twistedGrid_hasIndependenceDefectAtLeast
#print axioms Erdos73.exists_vertexTangle_controlling_bramble
