/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 926

For `k ≥ 4`, let `Hₖ` be the graph formed by the first three levels of the
Boolean lattice: one center, `k` branch vertices, and one subdividing vertex
for every pair of branches.  We prove an explicit Füredi-type estimate for
every finite `Hₖ`-free graph and deduce
`ex(n, Hₖ) = Oₖ(n ^ (3 / 2))`.

The detailed mathematical proof and declaration map are in `tex/926.tex`.
-/

open Finset Fintype Filter Asymptotics
open scoped SimpleGraph

namespace Erdos926

noncomputable section

syntax (name := answerSyntax926) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-! ## The forbidden graph -/

/-- An index for an unordered pair, represented in increasing order. -/
def PairIndex (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
  deriving DecidableEq, Fintype

/-- The vertices of `Hₖ`: center, branches, and pair-subdivision vertices. -/
abbrev HVertex (k : ℕ) := Unit ⊕ (Fin k ⊕ PairIndex k)

/-- The center vertex of `Hₖ`. -/
def center (k : ℕ) : HVertex k := Sum.inl ()

/-- Branch vertex `i` of `Hₖ`. -/
def branch {k : ℕ} (i : Fin k) : HVertex k := Sum.inr (Sum.inl i)

/-- The subdivision vertex belonging to pair `p`. -/
def subdiv {k : ℕ} (p : PairIndex k) : HVertex k := Sum.inr (Sum.inr p)

/-- Adjacency in the graph from Problem 926. -/
def HAdj {k : ℕ} : HVertex k → HVertex k → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inl _ => True
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1.1 ∨ i = p.1.2
  | _, _ => False

instance {k : ℕ} : DecidableRel (@HAdj k) := fun a b => by
  classical
  exact inferInstance

/-- The graph `Hₖ` in Erdős Problem 926. -/
def Hk (k : ℕ) : SimpleGraph (HVertex k) where
  Adj := HAdj
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) <;> simp_all [HAdj]⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) <;> simp [HAdj]⟩

instance (k : ℕ) : DecidableRel (Hk k).Adj := by
  classical
  exact inferInstance

@[simp] lemma Hk_center_branch {k : ℕ} (i : Fin k) :
    (Hk k).Adj (center k) (branch i) := by trivial

@[simp] lemma Hk_branch_center {k : ℕ} (i : Fin k) :
    (Hk k).Adj (branch i) (center k) := by trivial

@[simp] lemma Hk_branch_subdiv_iff {k : ℕ} (i : Fin k) (p : PairIndex k) :
    (Hk k).Adj (branch i) (subdiv p) ↔ i = p.1.1 ∨ i = p.1.2 := by
  rfl

@[simp] lemma Hk_subdiv_branch_iff {k : ℕ} (p : PairIndex k) (i : Fin k) :
    (Hk k).Adj (subdiv p) (branch i) ↔ i = p.1.1 ∨ i = p.1.2 := by
  rfl

/-- Number of pair-subdivision vertices. -/
abbrev pairCount (k : ℕ) : ℕ := Fintype.card (PairIndex k)

/-- Richness threshold: the number of vertices of `Hₖ`. -/
abbrev threshold (k : ℕ) : ℕ := 1 + k + pairCount k

lemma card_HVertex (k : ℕ) : Fintype.card (HVertex k) = threshold k := by
  simp [HVertex, threshold, pairCount]
  omega

lemma pairIndex_card (k : ℕ) : pairCount k = Nat.choose k 2 := by
  classical
  change Fintype.card {p : Fin k × Fin k // p.1 < p.2} = Nat.choose k 2
  rw [Fintype.card_subtype]
  simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin k))))

lemma threshold_eq (k : ℕ) : threshold k = 1 + k + Nat.choose k 2 := by
  change 1 + k + pairCount k = 1 + k + Nat.choose k 2
  rw [pairIndex_card]

/-! ## Common degrees and rich pairs -/

variable {V : Type*} [Fintype V]

/-- The number of common neighbors of two vertices. -/
noncomputable def commonDegree (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  Fintype.card (G.commonNeighbors u v)

lemma commonDegree_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    commonDegree G u v = commonDegree G v u := by
  unfold commonDegree
  exact Fintype.card_congr (Equiv.setCongr (G.commonNeighbors_symm u v))

/-- The graph whose edges are the pairs having at least `q` common neighbors. -/
def richGraph (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ q ≤ commonDegree G u v
  symm := ⟨by
    rintro u v ⟨huv, hq⟩
    exact ⟨huv.symm, by simpa [commonDegree_comm] using hq⟩⟩
  loopless := ⟨by simp⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    DecidableRel (richGraph G q).Adj := by
  classical
  exact inferInstance

@[simp] lemma richGraph_adj_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (u v : V) :
    (richGraph G q).Adj u v ↔ u ≠ v ∧ q ≤ commonDegree G u v := Iff.rfl

/-- The rich-pair graph induced on the neighborhood of `x`. -/
def richAt (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    SimpleGraph (G.neighborSet x) :=
  (richGraph G q).induce (G.neighborSet x)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    DecidableRel (richAt G q x).Adj := by
  classical
  exact inferInstance

lemma card_neighborSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Fintype.card (G.neighborSet x) = G.degree x := by
  exact G.card_neighborSet_eq_degree x

/-! ## A rich clique contains `Hₖ` -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- A `k`-clique of rich pairs in one neighborhood supplies all vertices of `Hₖ`.
The pair-subdivision vertices are selected simultaneously by finite Hall. -/
lemma contained_Hk_of_richClique (x : V)
    (f : SimpleGraph.Copy (⊤ : SimpleGraph (Fin k)) (richAt G (threshold k) x)) :
    Hk k ⊑ G := by
  classical
  let y : Fin k → V := fun i ↦ (f.toHom i).1
  have hy_inj : Function.Injective y := by
    intro i j hij
    apply f.injective
    exact Subtype.ext hij
  have hy_adj (i : Fin k) : G.Adj x (y i) := (f.toHom i).2
  let forbidden : Finset V := insert x (Finset.univ.image y)
  let common (p : PairIndex k) : Finset V :=
    (G.commonNeighbors (y p.1.1) (y p.1.2)).toFinset
  let eligible (p : PairIndex k) : Finset V := common p \ forbidden
  have hrich (p : PairIndex k) : threshold k ≤ commonDegree G (y p.1.1) (y p.1.2) := by
    have hpne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
    have hf := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin k)).Adj p.1.1 p.1.2 by
      simpa using hpne)
    have hf' : (richGraph G (threshold k)).Adj (y p.1.1) (y p.1.2) := by
      simpa only [richAt, SimpleGraph.comap_adj, Function.Embedding.subtype_apply,
        SimpleGraph.Copy.toHom_apply, y] using hf
    exact hf'.2
  have hforbidden : #forbidden ≤ k + 1 := by
    calc
      #forbidden ≤ #(Finset.univ.image y) + 1 := card_insert_le _ _
      _ = k + 1 := by
        rw [card_image_of_injective _ hy_inj, card_univ, Fintype.card_fin]
  have heligible (p : PairIndex k) : pairCount k ≤ #(eligible p) := by
    have hcommon : threshold k ≤ #(common p) := by
      simpa [common, commonDegree] using hrich p
    have hsplit : #(common p) ≤ #(eligible p) + #forbidden := by
      simpa [eligible] using card_le_card_sdiff_add_card (s := common p) (t := forbidden)
    change Fintype.card (PairIndex k) ≤ #(eligible p)
    change 1 + k + Fintype.card (PairIndex k) ≤ #(common p) at hcommon
    omega
  have hHall : ∀ A : Finset (PairIndex k), #A ≤ #(A.biUnion eligible) := by
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hA
      calc
        #A ≤ pairCount k := by simpa using A.card_le_univ
        _ ≤ #(eligible p) := heligible p
        _ ≤ #(A.biUnion eligible) := card_le_card (subset_biUnion_of_mem eligible hp)
  obtain ⟨z, hz_inj, hz_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' eligible).mp hHall
  have hz_common (p : PairIndex k) :
      z p ∈ G.commonNeighbors (y p.1.1) (y p.1.2) := by
    have hm : z p ∈ common p ∧ z p ∉ forbidden := by
      simpa [eligible] using hz_mem p
    simpa [common] using hm.1
  have hz_not_forbidden (p : PairIndex k) : z p ∉ forbidden := by
    have hm : z p ∈ common p ∧ z p ∉ forbidden := by
      simpa [eligible] using hz_mem p
    exact hm.2
  have hxy (i : Fin k) : x ≠ y i := (hy_adj i).ne
  have hzx (p : PairIndex k) : z p ≠ x := by
    intro h
    exact hz_not_forbidden p (by simp [forbidden, h])
  have hzy (p : PairIndex k) (i : Fin k) : z p ≠ y i := by
    intro h
    exact hz_not_forbidden p (by simp [forbidden, h, y])
  let φ : HVertex k → V
    | Sum.inl _ => x
    | Sum.inr (Sum.inl i) => y i
    | Sum.inr (Sum.inr p) => z p
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    rcases a with _ | a
    · rcases b with _ | b
      · rfl
      · rcases b with i | p
        · exact (hxy i hab).elim
        · exact (hzx p hab.symm).elim
    · rcases a with i | p
      · rcases b with _ | b
        · exact (hxy i hab.symm).elim
        · rcases b with j | q
          · exact congrArg (fun t ↦ Sum.inr (Sum.inl t)) (hy_inj hab)
          · exact (hzy q i hab.symm).elim
      · rcases b with _ | b
        · exact (hzx p hab).elim
        · rcases b with i | q
          · exact (hzy p i hab).elim
          · exact congrArg (fun t ↦ Sum.inr (Sum.inr t)) (hz_inj hab)
  refine ⟨{
    toHom := {
      toFun := φ
      map_rel' := ?_ }
    injective' := hφ_inj }⟩
  intro a b hab
  rcases a with _ | a
  · rcases b with _ | b
    · exact False.elim hab
    · rcases b with i | p
      · exact hy_adj i
      · exact False.elim hab
  · rcases a with i | p
    · rcases b with _ | b
      · exact (hy_adj i).symm
      · rcases b with j | q
        · exact False.elim hab
        · change i = q.1.1 ∨ i = q.1.2 at hab
          rcases hab with rfl | rfl
          · exact (G.mem_commonNeighbors.mp (hz_common q)).1
          · exact (G.mem_commonNeighbors.mp (hz_common q)).2
    · rcases b with _ | b
      · exact False.elim hab
      · rcases b with i | q
        · change i = p.1.1 ∨ i = p.1.2 at hab
          rcases hab with rfl | rfl
          · exact (G.mem_commonNeighbors.mp (hz_common p)).1.symm
          · exact (G.mem_commonNeighbors.mp (hz_common p)).2.symm
        · exact False.elim hab

/-- In an `Hₖ`-free graph, the rich-pair graph in every neighborhood is `Kₖ`-free. -/
lemma richAt_cliqueFree (hfree : (Hk k).Free G) (x : V) :
    (richAt G (threshold k) x).CliqueFree k := by
  by_contra h
  exact hfree (contained_Hk_of_richClique x
    (SimpleGraph.topEmbeddingOfNotCliqueFree h).toCopy)

/-! ## Rich/poor ordered-pair counts -/

/-- Ordered poor pairs inside the neighborhood of `x`, represented in the ambient type. -/
def poorPairsAt (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p ↦
    G.Adj x p.1 ∧ G.Adj x p.2 ∧ p.1 ≠ p.2 ∧ commonDegree G p.1 p.2 < q

/-- The same ordered poor pairs, represented directly on the neighborhood subtype. -/
def poorPairsWithin (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    Finset (G.neighborSet x × G.neighborSet x) := by
  classical
  exact Finset.univ.filter fun p ↦
    p.1 ≠ p.2 ∧ commonDegree G p.1.1 p.2.1 < q

lemma card_poorPairsWithin_eq_card_poorPairsAt
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    #(poorPairsWithin G q x) = #(poorPairsAt G q x) := by
  classical
  apply Finset.card_bij (fun p _ ↦ (p.1.1, p.2.1))
  · intro p hp
    simp only [poorPairsWithin, mem_filter, mem_univ, true_and] at hp
    simp only [poorPairsAt, mem_filter, mem_univ, true_and]
    exact ⟨p.1.2, p.2.2, fun h ↦ hp.1 (Subtype.ext h), hp.2⟩
  · intro a ha b hb hab
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun r : V × V ↦ r.1) hab
    · apply Subtype.ext
      exact congrArg (fun r : V × V ↦ r.2) hab
  · intro p hp
    simp only [poorPairsAt, mem_filter, mem_univ, true_and] at hp
    let a : G.neighborSet x := ⟨p.1, hp.1⟩
    let b : G.neighborSet x := ⟨p.2, hp.2.1⟩
    refine ⟨(a, b), ?_, rfl⟩
    simp only [poorPairsWithin, mem_filter, mem_univ, true_and]
    exact ⟨fun h ↦ hp.2.2.1
      (congrArg (fun t : G.neighborSet x ↦ (t : V)) h), hp.2.2.2⟩

/-- The ordered distinct pairs in a neighborhood split into rich darts and poor pairs. -/
lemma twice_rich_edges_add_poorPairsAt
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (x : V) :
    2 * #(richAt G q x).edgeFinset + #(poorPairsAt G q x) =
      G.degree x * (G.degree x - 1) := by
  classical
  let W := G.neighborSet x
  let R : SimpleGraph W := richAt G q x
  let s : Finset (W × W) := (Finset.univ : Finset W).offDiag
  have hrich :
      #{p : W × W | R.Adj p.1 p.2} = #(s.filter fun p ↦ R.Adj p.1 p.2) := by
    apply congrArg Finset.card
    ext p
    simp only [mem_filter, mem_univ, true_and, s, mem_offDiag, ne_eq]
    constructor
    · intro h
      exact ⟨R.ne_of_adj h, h⟩
    · exact fun h ↦ h.2
  have hpoor :
      #(poorPairsWithin G q x) = #(s.filter fun p ↦ ¬R.Adj p.1 p.2) := by
    congr 1
    ext p
    simp only [poorPairsWithin, mem_filter, mem_univ, true_and, s, mem_offDiag,
      R, richAt, SimpleGraph.comap_adj, Function.Embedding.subtype_apply,
      richGraph_adj_iff, not_and_or, not_le]
    constructor
    · rintro ⟨hne, hq⟩
      exact ⟨hne, Or.inr hq⟩
    · rintro ⟨hne, heq | hq⟩
      · exact False.elim (hne (Subtype.ext (not_ne_iff.mp heq)))
      · exact ⟨hne, hq⟩
  have hpartition :
      #(s.filter fun p ↦ R.Adj p.1 p.2) + #(s.filter fun p ↦ ¬R.Adj p.1 p.2) = #s := by
    exact card_filter_add_card_filter_not _
  rw [R.two_mul_card_edgeFinset, hrich, ← card_poorPairsWithin_eq_card_poorPairsAt,
    hpoor, hpartition]
  simp only [s, offDiag_card, card_univ, W, card_neighborSet]
  grind [Nat.mul_sub_one]

lemma turan_bound_richAt (hk : 2 ≤ k) (hfree : (Hk k).Free G) (x : V) :
    2 * (k - 1) * #(richAt G (threshold k) x).edgeFinset ≤
      (k - 2) * G.degree x ^ 2 := by
  let R := richAt G (threshold k) x
  have hcf : R.CliqueFree ((k - 1) + 1) := by
    simpa [R, Nat.sub_add_cancel (by omega : 1 ≤ k)] using richAt_cliqueFree hfree x
  have hT := hcf.card_edgeFinset_le
  dsimp only at hT
  rw [← SimpleGraph.card_edgeFinset_turanGraph] at hT
  have hT' := SimpleGraph.mul_card_edgeFinset_turanGraph_le
    (n := Fintype.card (G.neighborSet x)) (r := k - 1)
  calc
    2 * (k - 1) * #R.edgeFinset ≤
        2 * (k - 1) * #(SimpleGraph.turanGraph (Fintype.card (G.neighborSet x)) (k - 1)).edgeFinset :=
      Nat.mul_le_mul_left _ hT
    _ ≤ ((k - 1) - 1) * Fintype.card (G.neighborSet x) ^ 2 := hT'
    _ = (k - 2) * G.degree x ^ 2 := by
      rw [card_neighborSet]
      have : (k - 1) - 1 = k - 2 := by omega
      rw [this]

/-- The local rich/poor estimate.  This is the point at which Turán's theorem
is converted into a bound for the square of a degree. -/
lemma degree_sq_le_mul_add_poor (hk : 2 ≤ k) (hfree : (Hk k).Free G) (x : V) :
    G.degree x ^ 2 ≤ (k - 1) * (G.degree x + #(poorPairsAt G (threshold k) x)) := by
  let d := G.degree x
  let r := #(richAt G (threshold k) x).edgeFinset
  let ell := #(poorPairsAt G (threshold k) x)
  have hsplit : 2 * r + ell = d * (d - 1) := by
    simpa [d, r, ell] using twice_rich_edges_add_poorPairsAt G (threshold k) x
  have hturan : 2 * (k - 1) * r ≤ (k - 2) * d ^ 2 := by
    simpa [d, r] using turan_bound_richAt hk hfree x
  change d ^ 2 ≤ (k - 1) * (d + ell)
  by_cases hd : d = 0
  · simp [hd]
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  have hsplitZ :
      (2 : ℤ) * (r : ℤ) + (ell : ℤ) = (d : ℤ) * ((d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hsplit
  have hturanZ :
      (2 : ℤ) * ((k - 1 : ℕ) : ℤ) * (r : ℤ) ≤
        ((k - 2 : ℕ) : ℤ) * (d : ℤ) ^ 2 := by
    exact_mod_cast hturan
  have hdsub : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  have hksub : ((k - 2 : ℕ) : ℤ) = ((k - 1 : ℕ) : ℤ) - 1 := by omega
  rw [hdsub] at hsplitZ
  rw [hksub] at hturanZ
  have hz :
      (d : ℤ) ^ 2 ≤ ((k - 1 : ℕ) : ℤ) * ((d : ℤ) + (ell : ℤ)) := by
    nlinarith
  exact_mod_cast hz

/-! ## Double-counting poor pairs -/

/-- All ordered poor pairs in the host graph. -/
def poorPairs (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p ↦ p.1 ≠ p.2 ∧ commonDegree G p.1 p.2 < q

/-- Double-counting incidences between centers and ordered poor pairs. -/
lemma sum_card_poorPairsAt (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) :
    (∑ x, #(poorPairsAt G q x)) =
      ∑ p ∈ poorPairs G q, commonDegree G p.1 p.2 := by
  classical
  let P := poorPairs G q
  let I : V → V × V → Prop := fun x p ↦ G.Adj x p.1 ∧ G.Adj x p.2
  have hx (x : V) :
      #(P.bipartiteAbove I x) = #(poorPairsAt G q x) := by
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_bipartiteAbove, mem_univ, true_and, P, poorPairs,
      poorPairsAt, mem_filter, I]
    tauto
  have hp (p : V × V) :
      #((Finset.univ : Finset V).bipartiteBelow I p) = commonDegree G p.1 p.2 := by
    change #((Finset.univ : Finset V).bipartiteBelow I p) =
      Fintype.card (G.commonNeighbors p.1 p.2)
    rw [← Set.toFinset_card]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_bipartiteBelow, mem_univ, true_and, Set.mem_toFinset,
      SimpleGraph.mem_commonNeighbors, I]
    simp only [G.adj_comm]
  calc
    (∑ x, #(poorPairsAt G q x)) =
        ∑ x ∈ (Finset.univ : Finset V), #(P.bipartiteAbove I x) := by
      simp_rw [hx]
    _ = ∑ p ∈ P, #((Finset.univ : Finset V).bipartiteBelow I p) :=
      by simpa using (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := I) (s := (Finset.univ : Finset V)) (t := P))
    _ = ∑ p ∈ poorPairs G q, commonDegree G p.1 p.2 := by
      simp_rw [hp]
      rfl

/-- Every poor ordered pair contributes fewer than `q` common neighbors. -/
lemma sum_card_poorPairsAt_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 1 ≤ q) :
    (∑ x, #(poorPairsAt G q x)) ≤ (q - 1) * Fintype.card V ^ 2 := by
  classical
  rw [sum_card_poorPairsAt]
  calc
    (∑ p ∈ poorPairs G q, commonDegree G p.1 p.2) ≤
        ∑ _p ∈ poorPairs G q, (q - 1) := by
      apply sum_le_sum
      intro p hp
      simp only [poorPairs, mem_filter, mem_univ, true_and] at hp
      omega
    _ = #(poorPairs G q) * (q - 1) := by simp
    _ ≤ Fintype.card V ^ 2 * (q - 1) := by
      apply Nat.mul_le_mul_right
      calc
        #(poorPairs G q) ≤ Fintype.card (V × V) := by simpa using (poorPairs G q).card_le_univ
        _ = Fintype.card V ^ 2 := by simp [pow_two]
    _ = (q - 1) * Fintype.card V ^ 2 := by ac_rfl

/-! ## The global quadratic estimate -/

lemma two_mul_card_edges_le_card_sq (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * #G.edgeFinset ≤ Fintype.card V ^ 2 := by
  rw [G.two_mul_card_edgeFinset]
  calc
    #((Finset.univ : Finset (V × V)).filter fun p ↦ G.Adj p.1 p.2) ≤
        #(Finset.univ : Finset (V × V)) := card_le_card (filter_subset _ _)
    _ = Fintype.card V ^ 2 := by simp [pow_two]

lemma sum_degree_sq_le (hk : 2 ≤ k) (hfree : (Hk k).Free G) :
    (∑ x, G.degree x ^ 2) ≤
      (k - 1) * threshold k * Fintype.card V ^ 2 := by
  have hq : 1 ≤ threshold k := by
    change 1 ≤ 1 + k + pairCount k
    omega
  calc
    (∑ x, G.degree x ^ 2) ≤
        ∑ x, (k - 1) * (G.degree x + #(poorPairsAt G (threshold k) x)) := by
      apply sum_le_sum
      intro x _hx
      exact degree_sq_le_mul_add_poor hk hfree x
    _ = (k - 1) * ((∑ x, G.degree x) + ∑ x, #(poorPairsAt G (threshold k) x)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ = (k - 1) *
        (2 * #G.edgeFinset + ∑ x, #(poorPairsAt G (threshold k) x)) := by
      rw [G.sum_degrees_eq_twice_card_edges]
    _ ≤ (k - 1) *
        (2 * #G.edgeFinset + (threshold k - 1) * Fintype.card V ^ 2) := by
      gcongr
      exact sum_card_poorPairsAt_le G (threshold k) hq
    _ ≤ (k - 1) *
        (Fintype.card V ^ 2 + (threshold k - 1) * Fintype.card V ^ 2) := by
      gcongr
      exact two_mul_card_edges_le_card_sq G
    _ = (k - 1) * threshold k * Fintype.card V ^ 2 := by
      have hq' : 1 + (threshold k - 1) = threshold k := by omega
      calc
        (k - 1) * (Fintype.card V ^ 2 +
            (threshold k - 1) * Fintype.card V ^ 2) =
            (k - 1) * ((1 + (threshold k - 1)) * Fintype.card V ^ 2) := by ring
        _ = (k - 1) * threshold k * Fintype.card V ^ 2 := by rw [hq', mul_assoc]

/-- The central natural-number estimate: `4m² ≤ (k-1)|Hₖ|n³`. -/
theorem four_mul_card_edges_sq_le (hk : 2 ≤ k) (hfree : (Hk k).Free G) :
    4 * #G.edgeFinset ^ 2 ≤
      (k - 1) * threshold k * Fintype.card V ^ 3 := by
  have hcauchy :
      (∑ x, G.degree x) ^ 2 ≤
        Fintype.card V * ∑ x, G.degree x ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset V)) (f := fun x ↦ G.degree x))
  calc
    4 * #G.edgeFinset ^ 2 = (∑ x, G.degree x) ^ 2 := by
      rw [G.sum_degrees_eq_twice_card_edges]
      ring
    _ ≤ Fintype.card V * ∑ x, G.degree x ^ 2 := hcauchy
    _ ≤ Fintype.card V *
        ((k - 1) * threshold k * Fintype.card V ^ 2) := by
      gcongr
      exact sum_degree_sq_le hk hfree
    _ = (k - 1) * threshold k * Fintype.card V ^ 3 := by ring

/-! ## The real-valued extremal estimate -/

lemma natCast_rpow_three_halves_sq (n : ℕ) :
    (((n : ℝ) ^ (3 / 2 : ℝ)) ^ 2) = (n : ℝ) ^ 3 := by
  have hrpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add'] <;> norm_num
  rw [hrpow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
  ring

/-- A uniform all-`n` bound, with a deliberately simple (non-optimal) constant. -/
theorem card_edgeFinset_le_rpow (hk : 2 ≤ k) (hfree : (Hk k).Free G) :
    (#G.edgeFinset : ℝ) ≤
      (((k - 1) * threshold k : ℕ) : ℝ) *
        (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) := by
  let m := #G.edgeFinset
  let n := Fintype.card V
  let A := (k - 1) * threshold k
  let t : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)
  have hnat : 4 * m ^ 2 ≤ A * n ^ 3 := by
    simpa [m, n, A] using four_mul_card_edges_sq_le hk hfree
  have hreal : (4 : ℝ) * (m : ℝ) ^ 2 ≤ (A : ℝ) * (n : ℝ) ^ 3 := by
    exact_mod_cast hnat
  have hq : 1 ≤ threshold k := by
    change 1 ≤ 1 + k + pairCount k
    omega
  have hA_nat : 1 ≤ A := by
    dsimp only [A]
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (by omega) (by omega)
  have hA : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA_nat
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hAt0 : 0 ≤ (A : ℝ) * t := mul_nonneg (by positivity) ht0
  change (m : ℝ) ≤ (A : ℝ) * t
  rw [← sq_le_sq₀ hm0 hAt0]
  calc
    (m : ℝ) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith [sq_nonneg (m : ℝ)]
    _ ≤ (A : ℝ) * (n : ℝ) ^ 3 := hreal
    _ = (A : ℝ) * t ^ 2 := by rw [natCast_rpow_three_halves_sq n]
    _ ≤ (A : ℝ) ^ 2 * t ^ 2 := by
      gcongr
      nlinarith [sq_nonneg ((A : ℝ) - 1)]
    _ = ((A : ℝ) * t) ^ 2 := by ring

/-- The sharper constant obtained by taking the square root of the natural core estimate. -/
theorem card_edgeFinset_le_sharp (hk : 2 ≤ k) (hfree : (Hk k).Free G) :
    (#G.edgeFinset : ℝ) ≤
      Real.sqrt (((k - 1) * threshold k : ℕ) : ℝ) / 2 *
        (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) := by
  let m := #G.edgeFinset
  let n := Fintype.card V
  let A := (k - 1) * threshold k
  let t : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)
  have hnat : 4 * m ^ 2 ≤ A * n ^ 3 := by
    simpa [m, n, A] using four_mul_card_edges_sq_le hk hfree
  have hreal : (4 : ℝ) * (m : ℝ) ^ 2 ≤ (A : ℝ) * (n : ℝ) ^ 3 := by
    exact_mod_cast hnat
  have hcore : (4 : ℝ) * (m : ℝ) ^ 2 ≤ (A : ℝ) * t ^ 2 := by
    simpa [t, natCast_rpow_three_halves_sq] using hreal
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hright0 : 0 ≤ Real.sqrt (A : ℝ) / 2 * t := by positivity
  change (m : ℝ) ≤ Real.sqrt (A : ℝ) / 2 * t
  rw [← sq_le_sq₀ hm0 hright0]
  calc
    (m : ℝ) ^ 2 ≤ (A : ℝ) * t ^ 2 / 4 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    _ = (Real.sqrt (A : ℝ) / 2 * t) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hA0]
      norm_num
      ring

/-- The explicit estimate transferred to Mathlib's extremal number. -/
theorem extremalNumber_le_rpow (k n : ℕ) (hk : 2 ≤ k) :
    (SimpleGraph.extremalNumber n (Hk k) : ℝ) ≤
      Real.sqrt (((k - 1) * threshold k : ℕ) : ℝ) / 2 *
        (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [← Fintype.card_fin n]
  refine (SimpleGraph.extremalNumber_le_iff_of_nonneg (V := Fin n) (Hk k)
    (by positivity)).2 ?_
  intro G _inst hfree
  exact card_edgeFinset_le_sharp hk hfree

/-- For each fixed `k ≥ 2`, the extremal number of `Hₖ` is `O(n^(3/2))`. -/
theorem extremalNumber_isBigO (k : ℕ) (hk : 2 ≤ k) :
    (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (Hk k) : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ)) := by
  let C : ℝ := Real.sqrt (((k - 1) * threshold k : ℕ) : ℝ) / 2
  refine IsBigO.of_bound C (Filter.Eventually.of_forall fun n ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact extremalNumber_le_rpow k n hk

/-- Erdős Problem 926 has a positive answer. -/
theorem erdos_926 :
    answer(True) ↔ ∀ k : ℕ, 4 ≤ k →
      (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (Hk k) : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ)) := by
  constructor
  · intro _ k hk
    exact extremalNumber_isBigO k (by omega)
  · intro _
    trivial

end

end Erdos926

#print axioms Erdos926.erdos_926
