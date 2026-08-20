import ErdosProblems.Erdos746.Model
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm

/-!
# Random edge orderings and uniform injective prefixes

This file supplies the exact finite counting facts behind the random-order
coupling.  An ordered prefix of length `m` is an embedding from `Fin m` into
the finite type of possible edges.  Forgetting its order gives an element of
the fixed-edge sample space.  The fiber over every `m`-edge set has exactly
`m!` elements, so a uniform ordered prefix induces the uniform `G(n,m)`
distribution.

The last section records restriction, extension, and next-edge fibers.  In
particular, after any admissible history, every unused edge is represented by
exactly the same number of continuations.  These are the finite conditional
counting statements used by adaptive sprinkling.
-/

namespace Erdos746

noncomputable section

/-- An ordered sample of `m` distinct potential edges. -/
abbrev EdgePrefix (n m : ℕ) := Fin m ↪ Edge n

/-- Forget the order of an injective edge prefix. -/
def edgePrefixSet {n m : ℕ} (p : EdgePrefix n m) : Finset (Edge n) :=
  Finset.univ.map p

@[simp]
theorem card_edgePrefixSet {n m : ℕ} (p : EdgePrefix n m) :
    (edgePrefixSet p).card = m := by
  simp [edgePrefixSet]

/-- The fixed-edge graph obtained by forgetting the order of a prefix. -/
def edgePrefixFixedGraph {n m : ℕ} (p : EdgePrefix n m) :
    FixedEdgeGraph n m :=
  ⟨edgePrefixSet p, card_edgePrefixSet p⟩

@[simp]
theorem val_edgePrefixFixedGraph {n m : ℕ} (p : EdgePrefix n m) :
    (edgePrefixFixedGraph p).1 = edgePrefixSet p := rfl

@[simp]
theorem graph_edgePrefixFixedGraph {n m : ℕ} (p : EdgePrefix n m) :
    FixedEdgeGraph.graph (edgePrefixFixedGraph p) = graphOfEdges (edgePrefixSet p) :=
  rfl

/-- Every entry of an ordered prefix belongs to its underlying edge set. -/
theorem mem_edgePrefixSet {n m : ℕ} (p : EdgePrefix n m) (i : Fin m) :
    p i ∈ edgePrefixSet p := by
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The ordered prefix enumerates its underlying edge set bijectively. -/
def edgePrefixRangeEquiv {n m : ℕ} (p : EdgePrefix n m) :
    Fin m ≃ edgePrefixSet p :=
  Equiv.ofBijective
    (fun i ↦ ⟨p i, mem_edgePrefixSet p i⟩)
    ⟨by
      intro i j hij
      apply p.injective
      exact congrArg Subtype.val hij,
    by
      rintro ⟨e, he⟩
      rcases Finset.mem_map.mp he with ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩⟩

@[simp]
theorem coe_edgePrefixRangeEquiv {n m : ℕ} (p : EdgePrefix n m) (i : Fin m) :
    (edgePrefixRangeEquiv p i : Edge n) = p i := rfl

/-- The fiber of `edgePrefixFixedGraph` over a fixed edge set. -/
abbrev EdgePrefixFiber {n m : ℕ} (G : FixedEdgeGraph n m) :=
  {p : EdgePrefix n m // edgePrefixFixedGraph p = G}

/-- Forget the codomain subtype of an enumeration of a fixed edge set. -/
def edgePrefixOfEquiv {n m : ℕ} {G : FixedEdgeGraph n m}
    (e : Fin m ≃ G.1) : EdgePrefix n m :=
  e.toEmbedding.trans (Function.Embedding.subtype _)

@[simp]
theorem edgePrefixOfEquiv_apply {n m : ℕ} {G : FixedEdgeGraph n m}
    (e : Fin m ≃ G.1) (i : Fin m) :
    edgePrefixOfEquiv e i = (e i : Edge n) := rfl

theorem edgePrefixSet_edgePrefixOfEquiv {n m : ℕ} {G : FixedEdgeGraph n m}
    (e : Fin m ≃ G.1) :
    edgePrefixSet (edgePrefixOfEquiv e) = G.1 := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨i, _hi, rfl⟩
    exact (e i).property
  · intro ha
    obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val hi

@[simp]
theorem edgePrefixFixedGraph_edgePrefixOfEquiv {n m : ℕ}
    {G : FixedEdgeGraph n m} (e : Fin m ≃ G.1) :
    edgePrefixFixedGraph (edgePrefixOfEquiv e) = G := by
  apply Subtype.ext
  exact edgePrefixSet_edgePrefixOfEquiv e

/-- A fiber over an `m`-edge set is canonically the type of enumerations of
that set. -/
def edgePrefixFiberEquiv {n m : ℕ} (G : FixedEdgeGraph n m) :
    EdgePrefixFiber G ≃ (Fin m ≃ G.1) where
  toFun p :=
    let hset : edgePrefixSet p.1 = G.1 := congrArg Subtype.val p.2
    (edgePrefixRangeEquiv p.1).trans
      (Equiv.setCongr (by simpa only [hset]))
  invFun e := ⟨edgePrefixOfEquiv e, edgePrefixFixedGraph_edgePrefixOfEquiv e⟩
  left_inv p := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

/-- Every fixed `m`-edge graph has exactly `m!` ordered prefixes above it. -/
@[simp]
theorem card_edgePrefixFiber {n m : ℕ} (G : FixedEdgeGraph n m) :
    Fintype.card (EdgePrefixFiber G) = m.factorial := by
  rw [Fintype.card_congr (edgePrefixFiberEquiv G),
    Fintype.card_equiv ((G.1.equivFinOfCardEq G.2).symm)]
  simp

/-- Fiberwise summation form of uniformity: every unordered sample occurs
with the same multiplicity `m!`. -/
theorem sum_edgePrefix_comp {n m : ℕ} {M : Type*} [AddCommMonoid M]
    (w : FixedEdgeGraph n m → M) :
    (∑ p : EdgePrefix n m, w (edgePrefixFixedGraph p)) =
      m.factorial • (∑ G : FixedEdgeGraph n m, w G) := by
  classical
  rw [← Equiv.sum_comp
    (Equiv.sigmaFiberEquiv (@edgePrefixFixedGraph n m))
    (fun p ↦ w (edgePrefixFixedGraph p))]
  rw [Fintype.sum_sigma]
  calc
    (∑ G : FixedEdgeGraph n m,
        ∑ p : EdgePrefixFiber G, w (edgePrefixFixedGraph p.1)) =
        ∑ G : FixedEdgeGraph n m, ∑ _p : EdgePrefixFiber G, w G := by
          apply Fintype.sum_congr
          intro G
          apply Fintype.sum_congr
          intro p
          rw [p.2]
    _ = ∑ G : FixedEdgeGraph n m, m.factorial • w G := by
          apply Fintype.sum_congr
          intro G
          simp [card_edgePrefixFiber]
    _ = m.factorial • (∑ G : FixedEdgeGraph n m, w G) := by
          rw [Finset.sum_nsmul]

/-- Counting formulation of the fact that a uniform ordered prefix induces
the uniform fixed-edge distribution. -/
theorem card_edgePrefix_event {n m : ℕ}
    (event : FixedEdgeGraph n m → Prop) [DecidablePred event] :
    (Finset.univ.filter (fun p : EdgePrefix n m ↦
      event (edgePrefixFixedGraph p))).card =
      m.factorial * (Finset.univ.filter event).card := by
  classical
  simpa only [Finset.card_filter, Nat.nsmul_eq_mul] using
    (sum_edgePrefix_comp (n := n) (m := m)
      (M := ℕ) (fun G ↦ if event G then 1 else 0))

/-- Uniformly ordering an exact fixed-edge sample does not change the
probability of any event depending only on its underlying edge set. -/
theorem uniformProbability_edgePrefix_comp {n m : ℕ}
    (event : FixedEdgeGraph n m → Prop) :
    uniformProbability (fun p : EdgePrefix n m ↦
      event (edgePrefixFixedGraph p)) = uniformProbability event := by
  classical
  unfold uniformProbability
  have hnum :
      (((Finset.univ.filter (fun p : EdgePrefix n m ↦
          event (edgePrefixFixedGraph p))).card : ℕ) : ℝ) =
        (m.factorial : ℝ) *
          ((Finset.univ.filter event).card : ℝ) := by
    exact_mod_cast card_edgePrefix_event event
  rw [hnum]
  have hcard : Fintype.card (EdgePrefix n m) =
      m.factorial * (edgeCount n).choose m := by
    rw [Fintype.card_embedding_eq, card_edge,
      Fintype.card_fin, Nat.descFactorial_eq_factorial_mul_choose]
  rw [hcard]
  rw [Nat.cast_mul]
  rw [card_fixedEdgeGraph]
  have hfactorial : (m.factorial : ℝ) ≠ 0 := by
    exact_mod_cast m.factorial_ne_zero
  rw [mul_div_mul_left _ _ hfactorial]

/-- Uniform probability is invariant under a bijective reindexing of a
finite sample space. -/
theorem uniformProbability_equiv {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (event : Ω → Prop) :
    uniformProbability event =
      uniformProbability (fun y : Ω' ↦ event (e.symm y)) := by
  classical
  unfold uniformProbability
  have hden : Fintype.card Ω = Fintype.card Ω' := Fintype.card_congr e
  have hev :
      Fintype.card {x : Ω // event x} =
        Fintype.card {y : Ω' // event (e.symm y)} := by
    apply Fintype.card_congr
    exact
      { toFun := fun x ↦ ⟨e x.1, by simpa using x.2⟩
        invFun := fun y ↦ ⟨e.symm y.1, y.2⟩
        left_inv := fun x ↦ by apply Subtype.ext; simp
        right_inv := fun y ↦ by apply Subtype.ext; simp }
  have hnum :
      (Finset.univ.filter event).card =
        (Finset.univ.filter (fun y : Ω' ↦ event (e.symm y))).card := by
    simpa only [Fintype.card_subtype] using hev
  rw [hnum, hden]

/-! ## Nested prefixes and one-step continuations -/

/-- Restrict a longer ordered prefix to its first `m` entries. -/
def restrictEdgePrefix {n m k : ℕ} (hmk : m ≤ k) (p : EdgePrefix n k) :
    EdgePrefix n m :=
  (Fin.castLEEmb hmk).trans p

@[simp]
theorem restrictEdgePrefix_apply {n m k : ℕ} (hmk : m ≤ k)
    (p : EdgePrefix n k) (i : Fin m) :
    restrictEdgePrefix hmk p i = p (Fin.castLE hmk i) := rfl

theorem edgePrefixSet_restrict_subset {n m k : ℕ} (hmk : m ≤ k)
    (p : EdgePrefix n k) :
    edgePrefixSet (restrictEdgePrefix hmk p) ⊆ edgePrefixSet p := by
  intro e he
  rcases Finset.mem_map.mp he with ⟨i, _hi, rfl⟩
  exact Finset.mem_map.mpr ⟨Fin.castLE hmk i, Finset.mem_univ _, rfl⟩

theorem restrictEdgePrefix_trans {n ℓ m k : ℕ} (hm : ℓ ≤ m) (hk : m ≤ k)
    (p : EdgePrefix n k) :
    restrictEdgePrefix hm (restrictEdgePrefix hk p) =
      restrictEdgePrefix (hm.trans hk) p := by
  ext i
  rfl

/-- The injective prefix cut out of a full edge ordering. -/
def edgePrefixOfOrdering {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) : EdgePrefix n m :=
  (Fin.castLEEmb hm).trans order.toEmbedding

@[simp]
theorem edgePrefixOfOrdering_apply {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) (i : Fin m) :
    edgePrefixOfOrdering order hm i = order (Fin.castLE hm i) := rfl

theorem edgePrefixSet_ofOrdering {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) :
    edgePrefixSet (edgePrefixOfOrdering order hm) = prefixEdges order m := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨i, _hi, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨Fin.castLE hm i, ?_, rfl⟩
    simp
  · intro he
    rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
    have hjlt : (j : ℕ) < m := by simpa using hj
    let i : Fin m := ⟨j, hjlt⟩
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change order (Fin.castLE hm i) = order j
    exact congrArg order (Fin.ext rfl)

@[simp]
theorem edgePrefixFixedGraph_ofOrdering {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) :
    edgePrefixFixedGraph (edgePrefixOfOrdering order hm) =
      prefixFixedEdgeGraph order hm := by
  apply Subtype.ext
  exact edgePrefixSet_ofOrdering order hm

@[simp]
theorem graph_edgePrefixOfOrdering {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) :
    FixedEdgeGraph.graph (edgePrefixFixedGraph (edgePrefixOfOrdering order hm)) =
      orderedGraph order m := by
  rw [edgePrefixFixedGraph_ofOrdering, graph_prefixFixedEdgeGraph]

theorem restrict_edgePrefixOfOrdering {n m k : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) (hk : k ≤ edgeCount n) (hmk : m ≤ k) :
    restrictEdgePrefix hmk (edgePrefixOfOrdering order hk) =
      edgePrefixOfOrdering order hm := by
  ext i
  rfl

/-- An edge not yet present in an ordered prefix. -/
abbrev UnusedEdge {n m : ℕ} (p : EdgePrefix n m) :=
  {e : Edge n // e ∉ edgePrefixSet p}

theorem mem_edgePrefixSet_iff_range {n m : ℕ} (p : EdgePrefix n m)
    (e : Edge n) :
    e ∈ edgePrefixSet p ↔ e ∈ Set.range p := by
  simp [edgePrefixSet]

@[simp]
theorem card_unusedEdge {n m : ℕ} (p : EdgePrefix n m) :
    Fintype.card (UnusedEdge p) = edgeCount n - m := by
  rw [Fintype.card_subtype_compl (fun e : Edge n ↦ e ∈ edgePrefixSet p)]
  rw [card_edge]
  simp

/-- Extensions of `p` by one further ordered edge. -/
abbrev OneStepExtension {n m : ℕ} (p : EdgePrefix n m) :=
  {q : EdgePrefix n (m + 1) // Fin.Embedding.init q = p}

/-- Append one unused edge to the end of a prefix. -/
def snocEdgePrefix {n m : ℕ} (p : EdgePrefix n m) (e : UnusedEdge p) :
    EdgePrefix n (m + 1) :=
  Fin.Embedding.snoc p (by
    intro he
    exact e.2 ((mem_edgePrefixSet_iff_range p e.1).2 he))

@[simp]
theorem init_snocEdgePrefix {n m : ℕ} (p : EdgePrefix n m)
    (e : UnusedEdge p) :
    Fin.Embedding.init (snocEdgePrefix p e) = p := by
  unfold snocEdgePrefix
  apply Fin.Embedding.init_snoc

@[simp]
theorem snocEdgePrefix_last {n m : ℕ} (p : EdgePrefix n m)
    (e : UnusedEdge p) :
    snocEdgePrefix p e (Fin.last m) = e.1 := by
  simp [snocEdgePrefix, Fin.Embedding.snoc_last]

@[simp]
theorem snocEdgePrefix_castSucc {n m : ℕ} (p : EdgePrefix n m)
    (e : UnusedEdge p) (i : Fin m) :
    snocEdgePrefix p e i.castSucc = p i := by
  unfold snocEdgePrefix
  apply Fin.Embedding.snoc_castSucc

/-- The final edge of a one-step extension is unused by the old prefix. -/
def lastUnusedEdge {n m : ℕ} {p : EdgePrefix n m}
    (q : OneStepExtension p) : UnusedEdge p :=
  ⟨q.1 (Fin.last m), by
    intro hmem
    rcases (mem_edgePrefixSet_iff_range p _).1 hmem with ⟨i, hi⟩
    have hinit : q.1 i.castSucc = p i := by
      change Fin.Embedding.init q.1 i = p i
      rw [q.2]
    have heq : q.1 i.castSucc = q.1 (Fin.last m) := hinit.trans hi
    exact Fin.castSucc_ne_last i (q.1.injective heq)⟩

@[simp]
theorem coe_lastUnusedEdge {n m : ℕ} {p : EdgePrefix n m}
    (q : OneStepExtension p) :
    (lastUnusedEdge q : Edge n) = q.1 (Fin.last m) := rfl

/-- One-step extensions are in bijection with the currently unused edges. -/
def oneStepExtensionEquiv {n m : ℕ} (p : EdgePrefix n m) :
    OneStepExtension p ≃ UnusedEdge p where
  toFun := lastUnusedEdge
  invFun e := ⟨snocEdgePrefix p e, init_snocEdgePrefix p e⟩
  left_inv q := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact snocEdgePrefix_last p (lastUnusedEdge q)
    ·
      rw [snocEdgePrefix_castSucc]
      have h := congrArg (fun r : EdgePrefix n m ↦ r i) q.2
      exact h.symm
  right_inv e := by
    apply Subtype.ext
    exact snocEdgePrefix_last p e

/-- The number of possible next steps after a fixed ordered history. -/
@[simp]
theorem card_oneStepExtension {n m : ℕ} (p : EdgePrefix n m) :
    Fintype.card (OneStepExtension p) = edgeCount n - m := by
  rw [Fintype.card_congr (oneStepExtensionEquiv p), card_unusedEdge]

/-- For each unused edge there is exactly one one-step extension having that
edge as its next entry. -/
theorem existsUnique_oneStepExtension_last {n m : ℕ}
    (p : EdgePrefix n m) (e : UnusedEdge p) :
    ∃! q : OneStepExtension p, q.1 (Fin.last m) = e.1 := by
  refine ⟨(oneStepExtensionEquiv p).symm e, ?_, ?_⟩
  · exact snocEdgePrefix_last p e
  · intro q hq
    apply Subtype.ext
    apply Function.Embedding.ext
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · exact hq.trans (snocEdgePrefix_last p e).symm
    ·
      change q.1 i.castSucc = snocEdgePrefix p e i.castSucc
      rw [snocEdgePrefix_castSucc]
      have h := congrArg (fun r : EdgePrefix n m ↦ r i) q.2
      exact h

/-! ## Arbitrary continuations -/

/-- An ordered continuation of length `r`, taking values among the unused
edges after `p`. -/
abbrev EdgeContinuation {n m : ℕ} (p : EdgePrefix n m) (r : ℕ) :=
  Fin r ↪ UnusedEdge p

/-- Regard a continuation as an embedding into all potential edges. -/
def continuationAsEdges {n m r : ℕ} {p : EdgePrefix n m}
    (c : EdgeContinuation p r) : Fin r ↪ Edge n :=
  c.trans (Function.Embedding.subtype _)

theorem disjoint_range_continuation {n m r : ℕ} (p : EdgePrefix n m)
    (c : EdgeContinuation p r) :
    Disjoint (Set.range p) (Set.range (continuationAsEdges c)) := by
  rw [Set.disjoint_range_iff]
  intro i j hij
  exact (c j).2 ((mem_edgePrefixSet_iff_range p _).2 ⟨i, hij⟩)

/-- Append an ordered continuation to its history. -/
def appendEdgeContinuation {n m r : ℕ} (p : EdgePrefix n m)
    (c : EdgeContinuation p r) : EdgePrefix n (m + r) :=
  Fin.Embedding.append (disjoint_range_continuation p c)

@[simp]
theorem appendEdgeContinuation_castAdd {n m r : ℕ} (p : EdgePrefix n m)
    (c : EdgeContinuation p r) (i : Fin m) :
    appendEdgeContinuation p c (Fin.castAdd r i) = p i := by
  unfold appendEdgeContinuation
  rw [Fin.Embedding.coe_append, Fin.append_left]

@[simp]
theorem appendEdgeContinuation_natAdd {n m r : ℕ} (p : EdgePrefix n m)
    (c : EdgeContinuation p r) (j : Fin r) :
    appendEdgeContinuation p c (Fin.natAdd m j) = (c j : Edge n) := by
  unfold appendEdgeContinuation
  change Fin.append p (continuationAsEdges c) (Fin.natAdd m j) = (c j : Edge n)
  rw [Fin.append_right]
  rfl

/-- Prefixes of length `m+r` extending a specified length-`m` prefix. -/
abbrev AddExtension {n m : ℕ} (p : EdgePrefix n m) (r : ℕ) :=
  {q : EdgePrefix n (m + r) // (Fin.castAddEmb r).trans q = p}

def appendedContinuationExtension {n m r : ℕ} (p : EdgePrefix n m)
    (c : EdgeContinuation p r) : AddExtension p r :=
  ⟨appendEdgeContinuation p c, by
    apply Function.Embedding.ext
    intro i
    exact appendEdgeContinuation_castAdd p c i⟩

/-- Read the final `r` entries of an extension as an ordered continuation. -/
def extensionContinuation {n m r : ℕ} {p : EdgePrefix n m}
    (q : AddExtension p r) : EdgeContinuation p r where
  toFun j := ⟨q.1 (Fin.natAdd m j), by
    intro hmem
    rcases (mem_edgePrefixSet_iff_range p _).1 hmem with ⟨i, hi⟩
    have hfirst : q.1 (Fin.castAdd r i) = p i := by
      have h := congrArg (fun f : EdgePrefix n m ↦ f i) q.2
      exact h
    have hindices : Fin.natAdd m j = Fin.castAdd r i :=
      q.1.injective (hi.symm.trans hfirst.symm)
    have hvals := congrArg Fin.val hindices
    simp [Fin.natAdd, Fin.castAdd] at hvals
    omega⟩
  inj' i j hij := by
    apply Fin.natAdd_injective r m
    apply q.1.injective
    exact congrArg Subtype.val hij

/-- A continuation and a longer prefix extending the history contain exactly
the same finite data. -/
def addExtensionEquivContinuation {n m r : ℕ} (p : EdgePrefix n m) :
    AddExtension p r ≃ EdgeContinuation p r where
  toFun := extensionContinuation
  invFun := appendedContinuationExtension p
  left_inv q := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · change appendEdgeContinuation p (extensionContinuation q) (Fin.castAdd r i) = _
      rw [appendEdgeContinuation_castAdd]
      have h := congrArg (fun f : EdgePrefix n m ↦ f i) q.2
      exact h.symm
    · change appendEdgeContinuation p (extensionContinuation q) (Fin.natAdd m j) = _
      rw [appendEdgeContinuation_natAdd]
      rfl
  right_inv c := by
    apply Function.Embedding.ext
    intro j
    apply Subtype.ext
    exact appendEdgeContinuation_natAdd p c j

/-- Every length-`m` history has the same number of `r`-edge ordered
continuations, namely the falling factorial of the number of unused edges. -/
@[simp]
theorem card_addExtension {n m r : ℕ} (p : EdgePrefix n m) :
    Fintype.card (AddExtension p r) =
      (edgeCount n - m).descFactorial r := by
  rw [Fintype.card_congr (addExtensionEquivContinuation p),
    Fintype.card_embedding_eq, card_unusedEdge]
  simp

/-! ## Equal continuation counts after prescribing the next edge -/

/-- Embeddings whose first value is a prescribed element. -/
abbrev FixedFirstEmbedding (A : Type*) (a : A) (r : ℕ) :=
  {f : Fin (r + 1) ↪ A // f 0 = a}

/-- The tail of a fixed-first embedding takes values away from its first
element. -/
def fixedFirstTail {A : Type*} {a : A} {r : ℕ}
    (f : FixedFirstEmbedding A a r) : Fin r ↪ {x : A // x ≠ a} where
  toFun i := ⟨f.1 i.succ, by
    intro hi
    have heq : f.1 i.succ = f.1 0 := hi.trans f.2.symm
    exact Fin.succ_ne_zero i (f.1.injective heq)⟩
  inj' i j hij := by
    apply Fin.succ_injective r
    apply f.1.injective
    exact congrArg Subtype.val hij

/-- Put a prescribed first value in front of an embedding avoiding it. -/
def consAvoiding {A : Type*} {a : A} {r : ℕ}
    (g : Fin r ↪ {x : A // x ≠ a}) : FixedFirstEmbedding A a r :=
  ⟨Fin.Embedding.cons
      (g.trans (Function.Embedding.subtype _))
      (by
        rintro ⟨i, hi⟩
        exact (g i).2 hi),
    by simp [Fin.Embedding.cons]⟩

/-- Once the first value is fixed, the remaining entries are precisely an
embedding into its complement. -/
def fixedFirstEmbeddingEquiv {A : Type*} (a : A) (r : ℕ) :
    FixedFirstEmbedding A a r ≃ (Fin r ↪ {x : A // x ≠ a}) where
  toFun := fixedFirstTail
  invFun := consAvoiding
  left_inv f := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact f.2.symm
    · rfl
  right_inv g := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    rfl

@[simp]
theorem card_avoiding_element (A : Type*) [Fintype A] [DecidableEq A] (a : A) :
    Fintype.card {x : A // x ≠ a} = Fintype.card A - 1 := by
  rw [Fintype.card_subtype_compl (fun x : A ↦ x = a)]
  simp

/-- Exact number of injections with a prescribed first entry. -/
@[simp]
theorem card_fixedFirstEmbedding (A : Type*) [Fintype A] [DecidableEq A]
    (a : A) (r : ℕ) :
    Fintype.card (FixedFirstEmbedding A a r) =
      (Fintype.card A - 1).descFactorial r := by
  rw [Fintype.card_congr (fixedFirstEmbeddingEquiv a r),
    Fintype.card_embedding_eq, card_avoiding_element]
  simp

/-- Continuations of length `r+1` whose next edge is prescribed. -/
abbrev ContinuationFirstFiber {n m : ℕ} (p : EdgePrefix n m)
    (e : UnusedEdge p) (r : ℕ) :=
  {c : EdgeContinuation p (r + 1) // c 0 = e}

/-- Conditional on any fixed history, every unused choice of the next edge
has the same number of length-`r+1` continuations. -/
@[simp]
theorem card_continuationFirstFiber {n m r : ℕ} (p : EdgePrefix n m)
    (e : UnusedEdge p) :
    Fintype.card (ContinuationFirstFiber p e r) =
      (edgeCount n - m - 1).descFactorial r := by
  rw [card_fixedFirstEmbedding, card_unusedEdge]

theorem card_continuationFirstFiber_eq {n m r : ℕ}
    (p : EdgePrefix n m) (e f : UnusedEdge p) :
    Fintype.card (ContinuationFirstFiber p e r) =
      Fintype.card (ContinuationFirstFiber p f r) := by
  rw [card_continuationFirstFiber, card_continuationFirstFiber]

end

end Erdos746
