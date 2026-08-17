/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos182.Lower

/-!
# The Janzer--Steiner--Sudakov layered graph

This file defines the finite product probability space used for Erdős Problem
641.  A coordinate consists of a source vertex and a strictly later layer;
its value is one uniformly available target in that later layer.
-/

open Finset Fintype Filter
open scoped BigOperators Classical

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

/-- Vertices in all active JSS layers. -/
abbrev JSSVertex (n : ℕ) :=
  Σ i : Fin (prsLayerCount n), Fin (prsLayerSize n i)

/-- One independent random coordinate: a source vertex and a strictly later
target layer. -/
@[ext]
structure JSSCoordinate (n : ℕ) where
  source : JSSVertex n
  targetLayer : Fin (prsLayerCount n)
  isLt : source.1 < targetLayer
deriving DecidableEq, Fintype

/-- The canonical embedding of one layer into all vertices. -/
def jssLayerEmbedding (n : ℕ) (i : Fin (prsLayerCount n)) :
    Fin (prsLayerSize n i) ↪ JSSVertex n where
  toFun v := ⟨i, v⟩
  inj' := by
    intro v w h
    exact Fin.ext (congrArg (fun z : JSSVertex n ↦ z.2.val) h)

/-- The vertices in one layer. -/
def jssLayer (n : ℕ) (i : Fin (prsLayerCount n)) : Finset (JSSVertex n) :=
  Finset.univ.map (jssLayerEmbedding n i)

@[simp] lemma card_jssLayer (n : ℕ) (i : Fin (prsLayerCount n)) :
    (jssLayer n i).card = prsLayerSize n i := by
  simp [jssLayer]

@[simp] lemma mem_jssLayer_iff {n : ℕ} {i : Fin (prsLayerCount n)}
    {v : JSSVertex n} :
    v ∈ jssLayer n i ↔ v.1 = i := by
  classical
  constructor
  · intro hv
    obtain ⟨w, _hw, hwv⟩ := Finset.mem_map.mp hv
    exact (congrArg Sigma.fst hwv).symm
  · intro hvi
    subst i
    exact Finset.mem_map.mpr ⟨v.2, Finset.mem_univ _, rfl⟩

/-- The allowed target set of a coordinate. -/
def jssAllowed {n : ℕ} (c : JSSCoordinate n) : Finset (JSSVertex n) :=
  jssLayer n c.targetLayer

@[simp] lemma card_jssAllowed {n : ℕ} (c : JSSCoordinate n) :
    (jssAllowed c).card = prsLayerSize n c.targetLayer := by
  simp [jssAllowed]

/-- An outcome chooses one target at every coordinate. -/
abbrev JSSOutcome (n : ℕ) :=
  FiniteChoiceOutcome (JSSCoordinate n) (JSSVertex n)

/-- The finite sample space of admissible outcomes. -/
def jssOutcomeSpace (n : ℕ) : Finset (JSSOutcome n) :=
  finiteChoiceSpace jssAllowed

@[simp] lemma mem_jssOutcomeSpace {n : ℕ} {ω : JSSOutcome n} :
    ω ∈ jssOutcomeSpace n ↔
      ∀ c, ω c (Finset.mem_univ c) ∈ jssAllowed c := by
  simp [jssOutcomeSpace]

lemma exists_jssTargetIndex {n : ℕ} {ω : JSSOutcome n}
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    ∃ x : Fin (prsLayerSize n c.targetLayer),
      (⟨c.targetLayer, x⟩ : JSSVertex n) = ω c (Finset.mem_univ c) := by
  have ht := (mem_jssLayer_iff.mp ((mem_jssOutcomeSpace.mp hω) c))
  generalize hy : ω c (Finset.mem_univ c) = y at ht ⊢
  rcases y with ⟨i, x⟩
  dsimp only at ht
  subst i
  exact ⟨x, rfl⟩

/-- The target index selected by an admissible outcome. -/
def jssTargetIndex {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    Fin (prsLayerSize n c.targetLayer) :=
  Classical.choose (exists_jssTargetIndex hω c)

@[simp] lemma jssTargetIndex_spec {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    (⟨c.targetLayer, jssTargetIndex ω hω c⟩ : JSSVertex n) =
      ω c (Finset.mem_univ c) :=
  Classical.choose_spec (exists_jssTargetIndex hω c)

/-- The chosen target vertex. -/
def jssTarget {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) : JSSVertex n :=
  ⟨c.targetLayer, jssTargetIndex ω hω c⟩

@[simp] lemma fst_jssTarget {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    (jssTarget ω hω c).1 = c.targetLayer := rfl

@[simp] lemma jssTarget_eq_outcome {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    jssTarget ω hω c = ω c (Finset.mem_univ c) :=
  jssTargetIndex_spec ω hω c

/-- The random layered graph attached to an admissible outcome. -/
def jssGraph {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) : SimpleGraph (JSSVertex n) where
  Adj a b :=
    (∃ c : JSSCoordinate n, c.source = a ∧ jssTarget ω hω c = b) ∨
    (∃ c : JSSCoordinate n, c.source = b ∧ jssTarget ω hω c = a)
  symm := ⟨by
    intro a b hab
    exact hab.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro a haa
    rcases haa with ⟨c, hca, hta⟩ | ⟨c, hca, hta⟩
    · have hfirst : c.source.1 = c.targetLayer := by
        calc
          c.source.1 = a.1 := congrArg Sigma.fst hca
          _ = (jssTarget ω hω c).1 := congrArg Sigma.fst hta.symm
          _ = c.targetLayer := rfl
      exact (ne_of_lt c.isLt) hfirst
    · have hfirst : c.source.1 = c.targetLayer := by
        calc
          c.source.1 = a.1 := congrArg Sigma.fst hca
          _ = (jssTarget ω hω c).1 := congrArg Sigma.fst hta.symm
          _ = c.targetLayer := rfl
      exact (ne_of_lt c.isLt) hfirst⟩

lemma jssGraph_adj_source_target {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (c : JSSCoordinate n) :
    (jssGraph ω hω).Adj c.source (jssTarget ω hω c) := by
  exact Or.inl ⟨c, rfl, rfl⟩

lemma jssGraph_adj_iff {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {a b : JSSVertex n} :
    (jssGraph ω hω).Adj a b ↔
      (∃ c : JSSCoordinate n, c.source = a ∧ jssTarget ω hω c = b) ∨
      (∃ c : JSSCoordinate n, c.source = b ∧ jssTarget ω hω c = a) :=
  Iff.rfl

/-- Every edge points from a strictly earlier layer to a later one, in one
of its two orientations. -/
lemma layer_lt_or_gt_of_jssGraph_adj {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {a b : JSSVertex n}
    (hab : (jssGraph ω hω).Adj a b) : a.1 < b.1 ∨ b.1 < a.1 := by
  rcases hab with ⟨c, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
  · exact Or.inl c.isLt
  · exact Or.inr c.isLt

/-- A source has at most one neighbor in any fixed later layer. -/
lemma unique_neighbor_in_later_layer {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {u v w : JSSVertex n}
    (huv : (jssGraph ω hω).Adj u v) (huw : (jssGraph ω hω).Adj u w)
    (huvLayer : u.1 < v.1) (huwLayer : u.1 < w.1) (hvw : v.1 = w.1) :
    v = w := by
  rcases huv with ⟨c, hcu, hcv⟩ | ⟨c, hcv, hcu⟩
  · rcases huw with ⟨d, hdu, hdw⟩ | ⟨d, hdw, hdu⟩
    · have hcsrc : c.source = d.source := hcu.trans hdu.symm
      have hctgt : c.targetLayer = d.targetLayer := by
        calc
          c.targetLayer = v.1 := congrArg Sigma.fst hcv
          _ = w.1 := hvw
          _ = d.targetLayer := (congrArg Sigma.fst hdw).symm
      have hcd : c = d := JSSCoordinate.ext hcsrc hctgt
      subst d
      exact hcv.symm.trans hdw
    · have : w.1 < u.1 := by
        calc
          w.1 = d.source.1 := congrArg Sigma.fst hdw.symm
          _ < (jssTarget ω hω d).1 := d.isLt
          _ = u.1 := congrArg Sigma.fst hdu
      exact ((not_lt_of_ge (Nat.le_of_lt huwLayer)) this).elim
  · have : v.1 < u.1 := by
      calc
        v.1 = c.source.1 := congrArg Sigma.fst hcv.symm
        _ < (jssTarget ω hω c).1 := c.isLt
        _ = u.1 := congrArg Sigma.fst hcu
    exact ((not_lt_of_ge (Nat.le_of_lt huvLayer)) this).elim

/-- The vertex type has the expected cardinality. -/
lemma card_JSSVertex (n : ℕ) :
    Fintype.card (JSSVertex n) =
      ∑ i ∈ Finset.range (prsLayerCount n), prsLayerSize n i := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ prsLayerSize n i) (prsLayerCount n)

/-- Eventually the construction uses at most `n` vertices. -/
lemma eventually_card_JSSVertex_le :
    ∀ᶠ n : ℕ in atTop, Fintype.card (JSSVertex n) ≤ n := by
  filter_upwards [eventually_prsLayer_sum_le] with n hn
  rw [card_JSSVertex]
  exact hn

end

end Erdos641
