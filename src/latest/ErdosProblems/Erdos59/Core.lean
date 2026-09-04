import Mathlib

/-!
# Erdős Problem 59: counting labelled forbidden-subgraph-free graphs

This file packages the finite counting statement and the two asymptotic
properties used in Erdős Problem 59.  All graphs counted here are labelled:
their vertex type is literally `Fin n`.
-/

namespace Erdos59

open SimpleGraph

/-- The finite type of labelled `H`-free graphs on the vertex set `Fin n`. -/
abbrev LabelledFreeGraphs {W : Type*} (H : SimpleGraph W) (n : ℕ) :=
  {G : SimpleGraph (Fin n) // H.Free G}

/-- The exact number of labelled `H`-free graphs on `Fin n`. -/
noncomputable def labelledFreeGraphCount {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℕ :=
  Nat.card (LabelledFreeGraphs H n)

@[simp]
theorem labelledFreeGraphCount_eq_card {W : Type*} (H : SimpleGraph W) (n : ℕ) :
    labelledFreeGraphCount H n = Nat.card (LabelledFreeGraphs H n) := by
  rfl

/-- The Erdős--Frankl--Rödl type upper bound asked for in Problem 59. -/
def HasErdos59UpperBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (labelledFreeGraphCount H n : ℝ) ≤
      Real.rpow 2 ((1 + ε) * (SimpleGraph.extremalNumber n H : ℝ))

/-- The indices at which a fixed multiplicative improvement over the
`2 ^ extremalNumber` exponent holds. -/
def lowerBoundIndices {W : Type*} (H : SimpleGraph W) (c : ℝ) : Set ℕ :=
  {n | Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ)}

/-- A Morris--Saxton type counterexample lower bound: one fixed positive
constant improves the exponent for infinitely many orders. -/
def HasMorrisSaxtonLowerBound {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (lowerBoundIndices H c).Infinite

/-- The mild nondegeneracy condition needed to separate the exponents in the
upper and lower bounds. -/
def EventuallyPositiveExtremalNumber {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < SimpleGraph.extremalNumber n H

/-- A six-cycle written as six distinct, cyclically adjacent indexed
vertices.  This is the convenient pointwise form of containment of
`cycleGraph 6`. -/
def IsC6 {V : Type*} (G : SimpleGraph V) (v : Fin 6 → V) : Prop :=
  Function.Injective v ∧ ∀ i, G.Adj (v i) (v (i + 1))

private theorem cycleGraph_six_adj_succ (i : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i (i + 1) := by
  fin_cases i <;> decide

private theorem cycleGraph_six_adj_iff (i j : Fin 6) :
    (SimpleGraph.cycleGraph 6).Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  fin_cases i <;> fin_cases j <;> decide

/-- The indexed definition of a six-cycle is exactly containment of the
standard six-cycle graph. -/
theorem exists_isC6_iff_cycleGraph_six_isContained {V : Type*}
    (G : SimpleGraph V) :
    (∃ v : Fin 6 → V, IsC6 G v) ↔ SimpleGraph.cycleGraph 6 ⊑ G := by
  constructor
  · rintro ⟨v, hv_injective, hv_adj⟩
    refine ⟨{
      toHom := {
        toFun := v
        map_rel' := ?_ }
      injective' := hv_injective }⟩
    intro i j hij
    rcases (cycleGraph_six_adj_iff i j).mp hij with h | h
    · subst j
      exact hv_adj i
    · subst i
      exact (hv_adj j).symm
  · rintro ⟨f⟩
    refine ⟨f, f.injective, fun i ↦ ?_⟩
    exact f.toHom.map_rel (cycleGraph_six_adj_succ i)

/-- Pointwise six-cycle-freeness is exactly Mathlib's `Free` predicate for
the standard six-cycle graph. -/
theorem cycleGraph_six_free_iff_forall_not_isC6 {V : Type*}
    (G : SimpleGraph V) :
    (SimpleGraph.cycleGraph 6).Free G ↔ ∀ v : Fin 6 → V, ¬ IsC6 G v := by
  rw [SimpleGraph.Free, ← not_exists]
  exact not_congr (exists_isC6_iff_cycleGraph_six_isContained G).symm

private theorem cycleGraph_six_card_edgeFinset :
    (SimpleGraph.cycleGraph 6).edgeFinset.card = 6 := by
  have h := (SimpleGraph.cycleGraph 6).sum_degrees_eq_twice_card_edges
  simp [SimpleGraph.cycleGraph_degree_three_le] at h
  omega

private theorem cycleGraph_six_free_edge {V : Type*} [Fintype V]
    {u v : V} (huv : u ≠ v) :
    (SimpleGraph.cycleGraph 6).Free (SimpleGraph.edge u v) := by
  classical
  rintro ⟨f⟩
  have hcard := Fintype.card_le_of_embedding f.mapEdgeSet
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet,
    cycleGraph_six_card_edgeFinset] at hcard
  have hedge : (SimpleGraph.edge u v).edgeFinset.card = 1 := by
    simp [SimpleGraph.edgeFinset, SimpleGraph.edgeSet_edge_of_ne huv]
  rw [hedge] at hcard
  omega

/-- The extremal number for `C₆` is positive from order two onward: a single
edge is already `C₆`-free. -/
theorem eventuallyPositiveExtremalNumber_cycleGraph_six :
    EventuallyPositiveExtremalNumber (SimpleGraph.cycleGraph 6) := by
  refine ⟨2, fun n hn ↦ ?_⟩
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by
    intro h
    have hval := congrArg Fin.val h
    simp [u, v] at hval
  have hpositive :
      0 < SimpleGraph.extremalNumber (Fintype.card (Fin n))
        (SimpleGraph.cycleGraph 6) := by
    rw [SimpleGraph.lt_extremalNumber_iff]
    refine ⟨SimpleGraph.edge u v, inferInstance,
      cycleGraph_six_free_edge huv, ?_⟩
    simp [SimpleGraph.edgeFinset, SimpleGraph.edgeSet_edge_of_ne huv]
  simpa using hpositive

/-- If `H` has an edge, the empty graph witnesses positivity of the exact
labelled count. -/
theorem labelledFreeGraphCount_pos {W : Type*} {H : SimpleGraph W} (hH : H ≠ ⊥) (n : ℕ) :
    0 < labelledFreeGraphCount H n := by
  rw [labelledFreeGraphCount_eq_card, Nat.card_pos_iff]
  exact ⟨⟨⟨⊥, SimpleGraph.free_bot hH⟩⟩, inferInstance⟩

/-- Interpret a finite subset of the edges of `G` as a spanning subgraph. -/
private noncomputable def graphOfEdgeSubset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : Finset G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (s : Set G.edgeSet))

private theorem graphOfEdgeSubset_edgeSet {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : Finset G.edgeSet) :
    (graphOfEdgeSubset G s).edgeSet = Subtype.val '' (s : Set G.edgeSet) := by
  classical
  rw [graphOfEdgeSubset, SimpleGraph.edgeSet_fromEdgeSet]
  apply sdiff_eq_left.mpr
  rw [Set.disjoint_left]
  rintro e ⟨e', _, rfl⟩ he'
  exact (G.not_isDiag_of_mem_edgeSet e'.property) he'

private theorem graphOfEdgeSubset_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : Finset G.edgeSet) : graphOfEdgeSubset G s ≤ G := by
  classical
  rw [← SimpleGraph.edgeSet_subset_edgeSet, graphOfEdgeSubset_edgeSet]
  rintro _ ⟨e, _, rfl⟩
  exact e.property

private theorem graphOfEdgeSubset_injective {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Function.Injective (graphOfEdgeSubset G) := by
  classical
  intro s t hst
  apply Finset.ext
  intro e
  have himage : Subtype.val '' (s : Set G.edgeSet) =
      Subtype.val '' (t : Set G.edgeSet) := by
    rw [← graphOfEdgeSubset_edgeSet G s, ← graphOfEdgeSubset_edgeSet G t, hst]
  constructor
  · intro he
    have he' : (e : Sym2 V) ∈ Subtype.val '' (s : Set G.edgeSet) := ⟨e, he, rfl⟩
    rw [himage] at he'
    rcases he' with ⟨e', he't, he'e⟩
    have : e' = e := Subtype.ext he'e
    simpa [this] using he't
  · intro he
    have he' : (e : Sym2 V) ∈ Subtype.val '' (t : Set G.edgeSet) := ⟨e, he, rfl⟩
    rw [← himage] at he'
    rcases he' with ⟨e', he's, he'e⟩
    have : e' = e := Subtype.ext he'e
    simpa [this] using he's

/-- Every choice of a subset of the edges of an `H`-free graph gives a
different labelled `H`-free graph. -/
private noncomputable def edgeSubsetEmbedding {W : Type*} {H : SimpleGraph W}
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : H.Free G) :
    Finset G.edgeSet ↪ LabelledFreeGraphs H n where
  toFun s := ⟨graphOfEdgeSubset G s, fun hcopy ↦
    hG (hcopy.mono_right (graphOfEdgeSubset_le G s))⟩
  inj' s t h := graphOfEdgeSubset_injective G (Subtype.ext_iff.mp h)

/-- The elementary lower bound: all spanning subgraphs of an extremal
`H`-free graph are again `H`-free. -/
theorem two_pow_extremalNumber_le_labelledFreeGraphCount {W : Type*}
    {H : SimpleGraph W} (hH : H ≠ ⊥) (n : ℕ) :
    2 ^ SimpleGraph.extremalNumber n H ≤ labelledFreeGraphCount H n := by
  classical
  obtain ⟨G, inst, hG⟩ :=
    (SimpleGraph.exists_isExtremal_free (V := Fin n) hH)
  let : DecidableRel G.Adj := inst
  have hfree : H.Free G := hG.prop
  have hedges : G.edgeFinset.card = SimpleGraph.extremalNumber n H := by
    simpa using SimpleGraph.card_edgeFinset_of_isExtremal_free hG
  calc
    2 ^ SimpleGraph.extremalNumber n H = 2 ^ G.edgeFinset.card := by rw [hedges]
    _ = Nat.card (Finset G.edgeSet) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_finset, SimpleGraph.card_edgeSet]
    _ ≤ Nat.card (LabelledFreeGraphs H n) :=
      by simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_le_of_embedding (edgeSubsetEmbedding G hfree)
    _ = labelledFreeGraphCount H n := (labelledFreeGraphCount_eq_card H n).symm

/-- `Set.Infinite` in the Morris--Saxton packaging is equivalent to the more
explicit assertion that witnesses occur arbitrarily far out. -/
theorem hasMorrisSaxtonLowerBound_iff_arbitrarilyLarge {W : Type*}
    {H : SimpleGraph W} :
    HasMorrisSaxtonLowerBound H ↔
      ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
          (labelledFreeGraphCount H n : ℝ) := by
  constructor
  · rintro ⟨c, hc, hinf⟩
    refine ⟨c, hc, fun N ↦ ?_⟩
    obtain ⟨n, hnmem, hn⟩ := hinf.exists_gt N
    exact ⟨n, hn.le, hnmem⟩
  · rintro ⟨c, hc, hlarge⟩
    refine ⟨c, hc, Set.infinite_of_forall_exists_gt ?_⟩
    intro N
    obtain ⟨n, hn, hnmem⟩ := hlarge (N + 1)
    exact ⟨n, hnmem, by omega⟩

/-- A fixed positive improvement in the exponent on infinitely many indices
contradicts the Problem 59 upper bound as soon as the extremal number is
eventually positive. -/
theorem fixed_c_frequently_lowerBound_contradicts_upperBound {W : Type*}
    {H : SimpleGraph W} {c : ℝ} (hc : 0 < c)
    (hlower : (lowerBoundIndices H c).Infinite)
    (hpositive : EventuallyPositiveExtremalNumber H) :
    ¬ HasErdos59UpperBound H := by
  intro hupper
  obtain ⟨Nupper, hNupper⟩ := hupper (c / 2) (by linarith)
  obtain ⟨Npositive, hNpositive⟩ := hpositive
  obtain ⟨n, hnmem, hn⟩ := hlower.exists_gt (max Nupper Npositive)
  change Real.rpow 2 ((1 + c) * (SimpleGraph.extremalNumber n H : ℝ)) ≤
    (labelledFreeGraphCount H n : ℝ) at hnmem
  have hnupper : Nupper ≤ n := (le_max_left _ _).trans hn.le
  have hnpositive : Npositive ≤ n := (le_max_right _ _).trans hn.le
  have hexpos : (0 : ℝ) < SimpleGraph.extremalNumber n H := by
    exact_mod_cast hNpositive n hnpositive
  have hexponent :
      (1 + c / 2) * (SimpleGraph.extremalNumber n H : ℝ) <
        (1 + c) * (SimpleGraph.extremalNumber n H : ℝ) := by
    nlinarith
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexponent
  exact (not_lt_of_ge hnmem) ((hNupper n hnupper).trans_lt hrpow)

/-- Packaged form of the logical incompatibility between the two asymptotic
properties. -/
theorem hasMorrisSaxtonLowerBound_not_hasErdos59UpperBound {W : Type*}
    {H : SimpleGraph W} (hlower : HasMorrisSaxtonLowerBound H)
    (hpositive : EventuallyPositiveExtremalNumber H) :
    ¬ HasErdos59UpperBound H := by
  obtain ⟨c, hc, hinf⟩ := hlower
  exact fixed_c_frequently_lowerBound_contradicts_upperBound hc hinf hpositive

end Erdos59
