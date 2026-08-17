import ErdosProblems.Erdos59.AffinePolarity
import ErdosProblems.Erdos59.Blowup
import ErdosProblems.Erdos59.Core
import ErdosProblems.Erdos59.Duplication

/-!
# Cycle and relabelling adapters for Erdős Problem 59

The construction files use several convenient pointwise presentations of
triangles, quadrilaterals, and hexagons.  This file identifies all of them with
Mathlib's standard forbidden-subgraph predicates.  It also packages transport
of graphs, free graphs, and edge counts across a finite relabelling.
-/

namespace Erdos59.CycleAdapters

open SimpleGraph

/-- The cyclic successor on `Fin n`.  The input itself witnesses that `n` is
positive, so this definition needs no extra positivity hypothesis. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A simple `n`-cycle presented by cyclically adjacent indexed vertices. -/
def IndexedCycle {V : Type*} (n : ℕ) (G : SimpleGraph V) (v : Fin n → V) : Prop :=
  Function.Injective v ∧ ∀ i, G.Adj (v i) (v (cyclicSucc i))

private theorem exists_indexedCycle_iff_isContained_of_adj
    {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (hadj : ∀ i j : Fin n,
      (SimpleGraph.cycleGraph n).Adj i j ↔
        j = cyclicSucc i ∨ i = cyclicSucc j) :
    (∃ v : Fin n → V, IndexedCycle n G v) ↔
      SimpleGraph.cycleGraph n ⊑ G := by
  constructor
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hcycle⟩
    refine ⟨{
      toHom := {
        toFun := v
        map_rel' := ?_ }
      injective' := hinj }⟩
    intro i j hij
    rcases (hadj i j).mp hij with h | h
    · subst j
      exact hcycle i
    · subst i
      exact (hcycle j).symm
  · rintro ⟨f⟩
    refine ⟨f, ?_⟩
    rw [IndexedCycle]
    exact ⟨f.injective, fun i ↦
      f.toHom.map_rel ((hadj i (cyclicSucc i)).mpr (Or.inl rfl))⟩

private theorem cycleGraph_three_adj_succ_iff (i j : Fin 3) :
    (SimpleGraph.cycleGraph 3).Adj i j ↔
      j = cyclicSucc i ∨ i = cyclicSucc j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cycleGraph_four_adj_succ_iff (i j : Fin 4) :
    (SimpleGraph.cycleGraph 4).Adj i j ↔
      j = cyclicSucc i ∨ i = cyclicSucc j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cycleGraph_six_adj_succ_iff (i j : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i j ↔
      j = cyclicSucc i ∨ i = cyclicSucc j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem cyclicSucc_fin_four (i : Fin 4) : cyclicSucc i = i + 1 := by
  fin_cases i <;> decide

private theorem cyclicSucc_fin_six (i : Fin 6) : cyclicSucc i = i + 1 := by
  fin_cases i <;> decide

/-- Indexed triangles are exactly copies of the standard triangle. -/
theorem exists_indexedCycle_three_iff_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 3 → V, IndexedCycle 3 G v) ↔
      SimpleGraph.cycleGraph 3 ⊑ G :=
  exists_indexedCycle_iff_isContained_of_adj G cycleGraph_three_adj_succ_iff

/-- Indexed quadrilaterals are exactly copies of the standard quadrilateral. -/
theorem exists_indexedCycle_four_iff_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 4 → V, IndexedCycle 4 G v) ↔
      SimpleGraph.cycleGraph 4 ⊑ G :=
  exists_indexedCycle_iff_isContained_of_adj G cycleGraph_four_adj_succ_iff

/-- Indexed hexagons are exactly copies of the standard hexagon. -/
theorem exists_indexedCycle_six_iff_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IndexedCycle 6 G v) ↔
      SimpleGraph.cycleGraph 6 ⊑ G :=
  exists_indexedCycle_iff_isContained_of_adj G cycleGraph_six_adj_succ_iff

/-- The indexed and closed-walk presentations of a triangle agree. -/
theorem exists_indexedCycle_three_iff_exists_isCycle_walk {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 3 → V, IndexedCycle 3 G v) ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 3 :=
  (exists_indexedCycle_three_iff_isContained G).trans
    (SimpleGraph.cycleGraph_isContained_iff (by omega))

/-- The indexed and closed-walk presentations of a quadrilateral agree. -/
theorem exists_indexedCycle_four_iff_exists_isCycle_walk {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 4 → V, IndexedCycle 4 G v) ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 4 :=
  (exists_indexedCycle_four_iff_isContained G).trans
    (SimpleGraph.cycleGraph_isContained_iff (by omega))

/-- The indexed and closed-walk presentations of a hexagon agree. -/
theorem exists_indexedCycle_six_iff_exists_isCycle_walk {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IndexedCycle 6 G v) ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 6 :=
  (exists_indexedCycle_six_iff_isContained G).trans
    (SimpleGraph.cycleGraph_isContained_iff (by omega))

/-- Mathlib triangle-freeness is the absence of indexed triangles. -/
theorem cycleGraph_three_free_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 3).Free G ↔
      ∀ v : Fin 3 → V, ¬IndexedCycle 3 G v := by
  rw [SimpleGraph.Free, SimpleGraph.cycleGraph_isContained_iff (by omega),
    ← exists_indexedCycle_three_iff_exists_isCycle_walk]
  simp only [not_exists]

/-- Mathlib quadrilateral-freeness is the absence of indexed quadrilaterals. -/
theorem cycleGraph_four_free_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 4).Free G ↔
      ∀ v : Fin 4 → V, ¬IndexedCycle 4 G v := by
  rw [SimpleGraph.Free, SimpleGraph.cycleGraph_isContained_iff (by omega),
    ← exists_indexedCycle_four_iff_exists_isCycle_walk]
  simp only [not_exists]

/-- Mathlib hexagon-freeness is the absence of indexed hexagons. -/
theorem cycleGraph_six_free_iff {V : Type*} (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 6).Free G ↔
      ∀ v : Fin 6 → V, ¬IndexedCycle 6 G v := by
  rw [SimpleGraph.Free, SimpleGraph.cycleGraph_isContained_iff (by omega),
    ← exists_indexedCycle_six_iff_exists_isCycle_walk]
  simp only [not_exists]

/-- For three vertices, cycle-freeness and clique-freeness coincide. -/
theorem cycleGraph_three_free_iff_cliqueFree_three {V : Type*}
    (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 3).Free G ↔ G.CliqueFree 3 := by
  rw [SimpleGraph.cycleGraph_three_eq_top]
  simpa using
    (SimpleGraph.cliqueFree_iff_top_free (G := G) (β := Fin 3)).symm

private theorem affine_exists_c3_iff_indexed {V : Type*} (G : SimpleGraph V) :
    (∃ v₀ v₁ v₂, AffinePolarity.IsC3 G v₀ v₁ v₂) ↔
      ∃ v : Fin 3 → V, IndexedCycle 3 G v := by
  constructor
  · rintro ⟨v₀, v₁, v₂, h₀₁, h₁₂, h₂₀, e₀₁, e₁₂, e₂₀⟩
    refine ⟨![v₀, v₁, v₂], ?_⟩
    rw [IndexedCycle]
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simpa [cyclicSucc] using e₀₁
      · simpa [cyclicSucc] using e₁₂
      · simpa [cyclicSucc] using e₂₀
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hadj⟩
    refine ⟨v 0, v 1, v 2, hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), ?_, ?_, ?_⟩
    · simpa [cyclicSucc] using hadj 0
    · simpa [cyclicSucc] using hadj 1
    · simpa [cyclicSucc] using hadj 2

private theorem affine_exists_c4_iff_indexed {V : Type*} (G : SimpleGraph V) :
    (∃ v₀ v₁ v₂ v₃, AffinePolarity.IsC4 G v₀ v₁ v₂ v₃) ↔
      ∃ v : Fin 4 → V, IndexedCycle 4 G v := by
  constructor
  · rintro ⟨v₀, v₁, v₂, v₃, h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃,
      e₀₁, e₁₂, e₂₃, e₃₀⟩
    refine ⟨![v₀, v₁, v₂, v₃], ?_⟩
    rw [IndexedCycle]
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simpa [cyclicSucc] using e₀₁
      · simpa [cyclicSucc] using e₁₂
      · simpa [cyclicSucc] using e₂₃
      · simpa [cyclicSucc] using e₃₀
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hadj⟩
    refine ⟨v 0, v 1, v 2, v 3,
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      ?_, ?_, ?_, ?_⟩
    · simpa [cyclicSucc] using hadj 0
    · simpa [cyclicSucc] using hadj 1
    · simpa [cyclicSucc] using hadj 2
    · simpa [cyclicSucc] using hadj 3

private theorem affine_exists_c6_iff_indexed {V : Type*} (G : SimpleGraph V) :
    (∃ v₀ v₁ v₂ v₃ v₄ v₅,
      AffinePolarity.IsC6 G v₀ v₁ v₂ v₃ v₄ v₅) ↔
      ∃ v : Fin 6 → V, IndexedCycle 6 G v := by
  constructor
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, v₅,
      h₀₁, h₀₂, h₀₃, h₀₄, h₀₅,
      h₁₂, h₁₃, h₁₄, h₁₅,
      h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅,
      e₀₁, e₁₂, e₂₃, e₃₄, e₄₅, e₅₀⟩
    refine ⟨![v₀, v₁, v₂, v₃, v₄, v₅], ?_⟩
    rw [IndexedCycle]
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simpa [cyclicSucc] using e₀₁
      · simpa [cyclicSucc] using e₁₂
      · simpa [cyclicSucc] using e₂₃
      · simpa [cyclicSucc] using e₃₄
      · simpa [cyclicSucc] using e₄₅
      · simpa [cyclicSucc] using e₅₀
  · rintro ⟨v, hv⟩
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hadj⟩
    refine ⟨v 0, v 1, v 2, v 3, v 4, v 5,
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [cyclicSucc] using hadj 0
    · simpa [cyclicSucc] using hadj 1
    · simpa [cyclicSucc] using hadj 2
    · simpa [cyclicSucc] using hadj 3
    · simpa [cyclicSucc] using hadj 4
    · simpa [cyclicSucc] using hadj 5

/-- The affine-polarity explicit triangle exclusion is Mathlib triangle-freeness. -/
theorem affine_no_c3_iff_cliqueFree_three {V : Type*} (G : SimpleGraph V) :
    (¬ ∃ v₀ v₁ v₂, AffinePolarity.IsC3 G v₀ v₁ v₂) ↔
      G.CliqueFree 3 := by
  rw [← cycleGraph_three_free_iff_cliqueFree_three,
    cycleGraph_three_free_iff, ← not_exists, affine_exists_c3_iff_indexed]

/-- The affine-polarity explicit quadrilateral exclusion is Mathlib `C₄`-freeness. -/
theorem affine_no_c4_iff_cycleGraph_four_free {V : Type*} (G : SimpleGraph V) :
    (¬ ∃ v₀ v₁ v₂ v₃, AffinePolarity.IsC4 G v₀ v₁ v₂ v₃) ↔
      (SimpleGraph.cycleGraph 4).Free G := by
  rw [cycleGraph_four_free_iff, ← not_exists, affine_exists_c4_iff_indexed]

/-- The affine-polarity explicit hexagon exclusion is Mathlib `C₆`-freeness. -/
theorem affine_no_c6_iff_cycleGraph_six_free {V : Type*} (G : SimpleGraph V) :
    (¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅,
      AffinePolarity.IsC6 G v₀ v₁ v₂ v₃ v₄ v₅) ↔
      (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff, ← not_exists, affine_exists_c6_iff_indexed]

/-- The duplication file's indexed quadrilateral predicate is Mathlib `C₄`-freeness. -/
theorem duplication_c4Free_iff_cycleGraph_four_free {V : Type*}
    (G : SimpleGraph V) :
    FNV.C4Free G ↔ (SimpleGraph.cycleGraph 4).Free G := by
  rw [cycleGraph_four_free_iff]
  constructor
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_four] using hadj i⟩
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    rw [IndexedCycle]
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_four] using hadj i⟩

/-- The duplication file's indexed hexagon predicate is Mathlib `C₆`-freeness. -/
theorem duplication_c6Free_iff_cycleGraph_six_free {V : Type*}
    (G : SimpleGraph V) :
    FNV.C6Free G ↔ (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff]
  constructor
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_six] using hadj i⟩
  · intro h v hv
    apply h v
    rcases hv with ⟨hinj, hadj⟩
    rw [IndexedCycle]
    exact ⟨hinj, fun i ↦ by simpa only [cyclicSucc_fin_six] using hadj i⟩

/-- The duplication file's triangle predicate is Mathlib triangle-freeness. -/
theorem duplication_triangleFree_iff_cliqueFree_three {V : Type*}
    (G : SimpleGraph V) : FNV.TriangleFree G ↔ G.CliqueFree 3 :=
  Iff.rfl

/-- The duplication file's triangle predicate is also standard `C₃`-freeness. -/
theorem duplication_triangleFree_iff_cycleGraph_three_free {V : Type*}
    (G : SimpleGraph V) :
    FNV.TriangleFree G ↔ (SimpleGraph.cycleGraph 3).Free G :=
  (cycleGraph_three_free_iff_cliqueFree_three G).symm

/-- The blowup file's edge-oriented triangle predicate is clique-freeness. -/
theorem blowup_triangleFree_iff_cliqueFree_three {V : Type*}
    (G : SimpleGraph V) : Erdos59.TriangleFree G ↔ G.CliqueFree 3 := by
  classical
  constructor
  · intro h s hs
    rw [SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    exact False.elim (h hab hbc hac.symm)
  · intro h a b c hab hbc hca
    exact h {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hca.symm, hbc⟩)

/-- The blowup file's edge-oriented triangle predicate is standard `C₃`-freeness. -/
theorem blowup_triangleFree_iff_cycleGraph_three_free {V : Type*}
    (G : SimpleGraph V) :
    Erdos59.TriangleFree G ↔ (SimpleGraph.cycleGraph 3).Free G :=
  (blowup_triangleFree_iff_cliqueFree_three G).trans
    (cycleGraph_three_free_iff_cliqueFree_three G).symm

/-- The blowup file's explicit six-tuple predicate is Mathlib `C₆`-freeness. -/
theorem blowup_c6Free_iff_cycleGraph_six_free {V : Type*}
    (G : SimpleGraph V) :
    Erdos59.C6Free G ↔ (SimpleGraph.cycleGraph 6).Free G := by
  rw [cycleGraph_six_free_iff]
  constructor
  · intro h v hv
    rw [IndexedCycle] at hv
    rcases hv with ⟨hinj, hadj⟩
    apply h (by simpa [cyclicSucc] using hadj 0)
      (by simpa [cyclicSucc] using hadj 1)
      (by simpa [cyclicSucc] using hadj 2)
      (by simpa [cyclicSucc] using hadj 3)
      (by simpa [cyclicSucc] using hadj 4)
      (by simpa [cyclicSucc] using hadj 5)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      or_false, not_or]
    exact ⟨⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
      hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide),
        hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide), hinj.ne (by decide)⟩,
      ⟨hinj.ne (by decide), hinj.ne (by decide)⟩,
      hinj.ne (by decide), trivial, List.nodup_nil⟩
  · intro h a b c d e f hab hbc hcd hde hef hfa hnodup
    apply h ![a, b, c, d, e, f]
    rw [IndexedCycle]
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i
      · simpa [cyclicSucc] using hab
      · simpa [cyclicSucc] using hbc
      · simpa [cyclicSucc] using hcd
      · simpa [cyclicSucc] using hde
      · simpa [cyclicSucc] using hef
      · simpa [cyclicSucc] using hfa

section Relabelling

variable {V W : Type*} [Fintype V]

/-- The canonical equivalence from a finite vertex type to its labelled `Fin` type. -/
noncomputable def vertexEquivFin : V ≃ Fin (Fintype.card V) :=
  Fintype.equivFin V

/-- Relabel a graph on a finite type by `Fin (card V)`. -/
noncomputable def relabelGraph (G : SimpleGraph V) :
    SimpleGraph (Fin (Fintype.card V)) :=
  (vertexEquivFin (V := V)).simpleGraph G

/-- Relabelling is an equivalence on the full type of graphs. -/
noncomputable def graphEquivFin :
    SimpleGraph V ≃ SimpleGraph (Fin (Fintype.card V)) :=
  (vertexEquivFin (V := V)).simpleGraph

@[simp] theorem graphEquivFin_apply (G : SimpleGraph V) :
    graphEquivFin G = relabelGraph G :=
  rfl

/-- A graph is isomorphic to its canonical finite relabelling. -/
noncomputable def relabelGraphIso (G : SimpleGraph V) :
    G ≃g relabelGraph G :=
  (SimpleGraph.Iso.comap (vertexEquivFin (V := V)).symm G).symm

/-- Relabelling preserves every forbidden-subgraph predicate. -/
theorem relabelGraph_free_iff (H : SimpleGraph W) (G : SimpleGraph V) :
    H.Free (relabelGraph G) ↔ H.Free G :=
  (SimpleGraph.free_congr_right (relabelGraphIso G)).symm

/-- Relabelling preserves the exact number of edges. -/
theorem relabelGraph_edgeCard (G : SimpleGraph V) :
    Nat.card (relabelGraph G).edgeSet = Nat.card G.edgeSet :=
  (Nat.card_congr (relabelGraphIso G).mapEdgeSet).symm

/-- Relabelling restricts to an equivalence of free-graph families. -/
noncomputable def freeGraphsEquivFin (H : SimpleGraph W) :
    {G : SimpleGraph V // H.Free G} ≃
      LabelledFreeGraphs H (Fintype.card V) :=
  graphEquivFin.subtypeEquiv fun G ↦ (relabelGraph_free_iff H G).symm

/-- Consequently the arbitrary finite and canonically labelled free families
have the same cardinality. -/
theorem card_freeGraphs_eq_labelledFreeGraphCount (H : SimpleGraph W) :
    Nat.card {G : SimpleGraph V // H.Free G} =
      labelledFreeGraphCount H (Fintype.card V) := by
  rw [labelledFreeGraphCount_eq_card]
  exact Nat.card_congr (freeGraphsEquivFin H)

end Relabelling

section ThreeFoldRelabelling

/-- The standard three-fold fibre labelling, ordered with fibre coordinate
varying fastest. -/
def finThreeEquiv (n : ℕ) : Fin n × Fin 3 ≃ Fin (3 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 3))

/-- Relabel a graph on `Fin n × Fin 3` by `Fin (3 * n)`. -/
def relabelFinThreeGraph {n : ℕ} (G : SimpleGraph (Fin n × Fin 3)) :
    SimpleGraph (Fin (3 * n)) :=
  (finThreeEquiv n).simpleGraph G

/-- Three-fold fibre relabelling is an equivalence on graphs. -/
def graphFinThreeEquiv (n : ℕ) :
    SimpleGraph (Fin n × Fin 3) ≃ SimpleGraph (Fin (3 * n)) :=
  (finThreeEquiv n).simpleGraph

@[simp] theorem graphFinThreeEquiv_apply {n : ℕ}
    (G : SimpleGraph (Fin n × Fin 3)) :
    graphFinThreeEquiv n G = relabelFinThreeGraph G :=
  rfl

/-- A three-fold graph is isomorphic to its `Fin (3 * n)` relabelling. -/
def relabelFinThreeGraphIso {n : ℕ} (G : SimpleGraph (Fin n × Fin 3)) :
    G ≃g relabelFinThreeGraph G :=
  (SimpleGraph.Iso.comap (finThreeEquiv n).symm G).symm

/-- Three-fold relabelling preserves every forbidden-subgraph predicate. -/
theorem relabelFinThreeGraph_free_iff {W : Type*} (H : SimpleGraph W)
    {n : ℕ} (G : SimpleGraph (Fin n × Fin 3)) :
    H.Free (relabelFinThreeGraph G) ↔ H.Free G :=
  (SimpleGraph.free_congr_right (relabelFinThreeGraphIso G)).symm

/-- In particular, three-fold relabelling preserves `C₆`-freeness. -/
theorem relabelFinThreeGraph_c6Free_iff {n : ℕ}
    (G : SimpleGraph (Fin n × Fin 3)) :
    (SimpleGraph.cycleGraph 6).Free (relabelFinThreeGraph G) ↔
      (SimpleGraph.cycleGraph 6).Free G :=
  relabelFinThreeGraph_free_iff _ G

/-- Three-fold relabelling preserves the exact number of edges. -/
theorem relabelFinThreeGraph_edgeCard {n : ℕ}
    (G : SimpleGraph (Fin n × Fin 3)) :
    Nat.card (relabelFinThreeGraph G).edgeSet = Nat.card G.edgeSet :=
  (Nat.card_congr (relabelFinThreeGraphIso G).mapEdgeSet).symm

/-- Relabelling by `Fin (3 * n)` restricts to an equivalence of free families. -/
def freeGraphsFinThreeEquiv {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    {G : SimpleGraph (Fin n × Fin 3) // H.Free G} ≃
      LabelledFreeGraphs H (3 * n) :=
  (graphFinThreeEquiv n).subtypeEquiv fun G ↦
    (relabelFinThreeGraph_free_iff H G).symm

/-- The three-fold free family therefore has the canonical labelled count. -/
theorem card_freeGraphs_finThree_eq_labelledFreeGraphCount {W : Type*}
    (H : SimpleGraph W) (n : ℕ) :
    Nat.card {G : SimpleGraph (Fin n × Fin 3) // H.Free G} =
      labelledFreeGraphCount H (3 * n) := by
  rw [labelledFreeGraphCount_eq_card]
  exact Nat.card_congr (freeGraphsFinThreeEquiv H n)

/-- The family of `C₆`-free graphs on three-fold fibres has exactly the
canonical labelled `C₆`-free graph count on `Fin (3 * n)`. -/
theorem card_c6FreeGraphs_finThree_eq_labelledFreeGraphCount (n : ℕ) :
    Nat.card {G : SimpleGraph (Fin n × Fin 3) //
      (SimpleGraph.cycleGraph 6).Free G} =
      labelledFreeGraphCount (SimpleGraph.cycleGraph 6) (3 * n) :=
  card_freeGraphs_finThree_eq_labelledFreeGraphCount _ n

end ThreeFoldRelabelling

end Erdos59.CycleAdapters
