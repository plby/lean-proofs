/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.Graph
import ErdosProblems.Erdos565.CopyHypergraph
import ErdosProblems.Erdos565.Janson
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Bad-copy and induction events

This file gives the exact finite events used in the descent proof for Erdős problem 565.
The number of colors is arbitrary.  All density parameters are represented as quotients of
natural numbers, and the lower bound on a descended vertex set is cleared of denominators in
`ℕ`.  Thus no rounding convention is hidden in the definition of the induction event.
-/

@[expose] public section

open scoped BigOperators SimpleGraph

namespace Erdos565
namespace Events

/-- A vector of labelled target graphs, one for each of `r` colors. -/
abbrev TargetVector (r : ℕ) (order : Fin r → ℕ) :=
  (i : Fin r) → SimpleGraph (Fin (order i))

/-- The color-`i` subgraph of an edge-labelled graph. -/
def colorClassGraph {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (coloring : G.EdgeLabeling (Fin r)) (i : Fin r) : SimpleGraph V :=
  coloring.labelGraph i

@[simp] theorem colorClassGraph_eq_labelGraph {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (coloring : G.EdgeLabeling (Fin r)) (i : Fin r) :
    colorClassGraph coloring i = coloring.labelGraph i := rfl

/-- A nonnegative rational parameter, kept in numerator/denominator form. -/
noncomputable def rationalParameter (num den : ℕ) : ℝ := (num : ℝ) / (den : ℝ)

/-- The radius `p m` when `p = pNum / pDen`. -/
noncomputable def jansonRadius (pNum pDen m : ℕ) : ℝ :=
  rationalParameter pNum pDen * (m : ℝ)

lemma rationalParameter_nonneg (num den : ℕ) : 0 ≤ rationalParameter num den := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma rationalParameter_pos {num den : ℕ} (hnum : 0 < num) (hden : 0 < den) :
    0 < rationalParameter num den := by
  exact div_pos (Nat.cast_pos.2 hnum) (Nat.cast_pos.2 hden)

lemma jansonRadius_pos {pNum pDen m : ℕ} (hnum : 0 < pNum) (hden : 0 < pDen)
    (hm : 0 < m) : 0 < jansonRadius pNum pDen m := by
  exact mul_pos (rationalParameter_pos hnum hden) (Nat.cast_pos.2 hm)

/-- The coloring `coloring` of an arbitrary finite host is bad for `targets` if no color-copy
hypergraph has the required Janson property at radius `p |V(G)|`. -/
def BadForColoringOn {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph V)
    (coloring : G.EdgeLabeling (Fin r)) : Prop :=
  ∀ i : Fin r,
    ¬ (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsJanson
      (rationalParameter pNum pDen) (jansonRadius pNum pDen (Fintype.card V))

/-- The bad-coloring predicate specialized to a labelled `N`-vertex host. -/
def BadForColoring {N r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph (Fin N))
    (coloring : G.EdgeLabeling (Fin r)) : Prop :=
  BadForColoringOn pNum pDen targets G coloring

@[simp] theorem badForColoring_eq_badForColoringOn {N r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph (Fin N))
    (coloring : G.EdgeLabeling (Fin r)) :
    BadForColoring pNum pDen targets G coloring ↔
      BadForColoringOn pNum pDen targets G coloring := Iff.rfl

/-- The bad event on an arbitrary finite host. -/
def BadForTargetsOn {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph V) : Prop :=
  ∃ coloring : G.EdgeLabeling (Fin r), BadForColoringOn pNum pDen targets G coloring

/-- The bad event `B(targets)`: the host admits a coloring which is bad in every color. -/
def BadForTargets {N r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph (Fin N)) : Prop :=
  BadForTargetsOn pNum pDen targets G

@[simp] theorem badForTargets_eq_badForTargetsOn {N r : ℕ} {order : Fin r → ℕ}
    (pNum pDen : ℕ) (targets : TargetVector r order) (G : SimpleGraph (Fin N)) :
    BadForTargets pNum pDen targets G ↔ BadForTargetsOn pNum pDen targets G := Iff.rfl

/-- Exact denominator-cleared form of `actual ≥ (num / den) * base`. -/
def MeetsFractionalSize (num den base actual : ℕ) : Prop :=
  num * base ≤ den * actual

/-- The localized Janson radius
`radiusDen⁻¹ r⁻¹ delta p N`, with `p` and `delta` both supplied as exact
natural-number quotients.  In the key lemma `radiusDen = 2^9`. -/
noncomputable def localizedJansonRadius
    (radiusDen r pNum pDen deltaNum deltaDen N : ℕ) : ℝ :=
  rationalParameter (pNum * deltaNum * N) (radiusDen * r * pDen * deltaDen)

/-- The localized bad event used after the double-counting step.

It records a sufficiently large set `S` and a coloring of the induced host on `S` for which
every target-copy hypergraph fails to be Janson at radius
`radiusDen⁻¹ r⁻¹ delta p N`.  The size lower bound is the exact natural inequality
`sampleNum * N ≤ sampleDen * |S|`.  The ACDFM parameters are `sampleNum = deltaNum = 1`,
`sampleDen = r^34`, `deltaDen = r^50`, and `radiusDen = 2^9`. -/
def LocalizedBadForTargetsOn {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    (pNum pDen deltaNum deltaDen radiusDen sampleNum sampleDen : ℕ)
    (targets : TargetVector r order) (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V,
    MeetsFractionalSize sampleNum sampleDen (Fintype.card V) S.card ∧
      ∃ coloring : (G.induce (↑S : Set V)).EdgeLabeling (Fin r),
        ∀ i : Fin r,
          ¬ (copyHypergraph (targets i) (colorClassGraph coloring i)
            (G.induce (↑S : Set V))).IsJanson
              (rationalParameter pNum pDen)
              (localizedJansonRadius radiusDen r pNum pDen deltaNum deltaDen
                (Fintype.card V))

/-- The localized bad event specialized to a labelled `N`-vertex host. -/
def LocalizedBadForTargets {N r : ℕ} {order : Fin r → ℕ}
    (pNum pDen deltaNum deltaDen radiusDen sampleNum sampleDen : ℕ)
    (targets : TargetVector r order) (G : SimpleGraph (Fin N)) : Prop :=
  LocalizedBadForTargetsOn pNum pDen deltaNum deltaDen radiusDen sampleNum sampleDen targets G

/-- Denominator-cleared form of
`actual ≥ (deltaNum / (shrinkDen * deltaDen))^gap * base`.

The inequality lives entirely in `ℕ`; it is therefore also meaningful when a denominator is
zero, although applications assume all denominators are positive. -/
def MeetsDescendedSize (deltaNum deltaDen shrinkDen gap base actual : ℕ) : Prop :=
  deltaNum ^ gap * base ≤ (shrinkDen * deltaDen) ^ gap * actual

@[simp] theorem meetsDescendedSize_zero_gap
    (deltaNum deltaDen shrinkDen base actual : ℕ) :
    MeetsDescendedSize deltaNum deltaDen shrinkDen 0 base actual ↔ base ≤ actual := by
  simp [MeetsDescendedSize]

/-- Total order of a vector of targets. -/
def totalOrder {r : ℕ} (order : Fin r → ℕ) : ℕ := ∑ i, order i

/-- The strong-induction event `E(order)`.

For every coordinatewise-smaller vector whose total order strictly drops, every corresponding
target vector, every sufficiently large induced vertex set, and every coloring of that induced
host, at least one color-copy hypergraph is `(p,p|W|)`-Janson.  The lower bound on `|W|` is the
exact natural-number inequality `MeetsDescendedSize`; in the ACDFM application one takes
`deltaNum = 1`, `deltaDen = r^50`, and `shrinkDen = 8*r`. -/
def StrongInductionEventOn {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (pNum pDen deltaNum deltaDen shrinkDen : ℕ)
    (order : Fin r → ℕ) (G : SimpleGraph V) : Prop :=
  ∀ (smaller : Fin r → ℕ),
    (∀ i, smaller i ≤ order i) →
    totalOrder smaller < totalOrder order →
    ∀ targets : TargetVector r smaller,
    ∀ W : Finset V,
      MeetsDescendedSize deltaNum deltaDen shrinkDen
        (totalOrder order - totalOrder smaller) (Fintype.card V) W.card →
      ∀ coloring : (G.induce (↑W : Set V)).EdgeLabeling (Fin r),
        ∃ i : Fin r,
          (copyHypergraph (targets i) (colorClassGraph coloring i)
            (G.induce (↑W : Set V))).IsJanson
              (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card)

/-- The strong-induction event specialized to a labelled `N`-vertex host. -/
def StrongInductionEvent {N r : ℕ}
    (pNum pDen deltaNum deltaDen shrinkDen : ℕ)
    (order : Fin r → ℕ) (G : SimpleGraph (Fin N)) : Prop :=
  StrongInductionEventOn pNum pDen deltaNum deltaDen shrinkDen order G

/-- Global-coordinate form of the strong-induction event.

This is mathematically equivalent to the induced-subtype formulation after relabelling, but it
is the form consumed by localization and the maximal-seed argument: the coloring lives on the
current host and each copy hypergraph is merely restricted to `W`. -/
def StrongInductionEventGlobalOn
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (pNum pDen deltaNum deltaDen shrinkDen : ℕ)
    (order : Fin r → ℕ) (G : SimpleGraph V) : Prop :=
  ∀ (smaller : Fin r → ℕ),
    (∀ i, smaller i ≤ order i) →
    totalOrder smaller < totalOrder order →
    ∀ targets : TargetVector r smaller,
    ∀ W : Finset V,
      MeetsDescendedSize deltaNum deltaDen shrinkDen
        (totalOrder order - totalOrder smaller) (Fintype.card V) W.card →
      ∀ coloring : G.EdgeLabeling (Fin r),
        ∃ i : Fin r,
          ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict W).IsJanson
            (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card)

/-- Labelled-vertex specialization of the global-coordinate induction event. -/
def StrongInductionEventGlobal {N r : ℕ}
    (pNum pDen deltaNum deltaDen shrinkDen : ℕ)
    (order : Fin r → ℕ) (G : SimpleGraph (Fin N)) : Prop :=
  StrongInductionEventGlobalOn pNum pDen deltaNum deltaDen shrinkDen order G

/-- Failure of the global-coordinate event yields one smaller target vector and one restricted
bad family, with all quantifiers exposed for the minimal-descent argument. -/
theorem exists_restricted_bad_of_not_strongInductionEventGlobalOn
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {pNum pDen deltaNum deltaDen shrinkDen : ℕ}
    {order : Fin r → ℕ} {G : SimpleGraph V}
    (h : ¬ StrongInductionEventGlobalOn
      pNum pDen deltaNum deltaDen shrinkDen order G) :
    ∃ smaller : Fin r → ℕ,
      (∀ i, smaller i ≤ order i) ∧
      totalOrder smaller < totalOrder order ∧
      ∃ (targets : TargetVector r smaller) (W : Finset V),
        MeetsDescendedSize deltaNum deltaDen shrinkDen
          (totalOrder order - totalOrder smaller) (Fintype.card V) W.card ∧
        ∃ coloring : G.EdgeLabeling (Fin r),
          ∀ i : Fin r,
            ¬ ((copyHypergraph (targets i) (colorClassGraph coloring i) G).restrict W).IsJanson
              (rationalParameter pNum pDen) (jansonRadius pNum pDen W.card) := by
  classical
  unfold StrongInductionEventGlobalOn at h
  push Not at h
  exact h

/-- Failure of the strong-induction event supplies exactly a bad coloring on an induced finite
host.  This is the typing bridge used by minimal descent: no relabelling of the subtype `↥W`
to `Fin W.card` is necessary. -/
theorem exists_badForColoringOn_of_not_strongInductionEventOn
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {pNum pDen deltaNum deltaDen shrinkDen : ℕ}
    {order : Fin r → ℕ} {G : SimpleGraph V}
    (h : ¬ StrongInductionEventOn pNum pDen deltaNum deltaDen shrinkDen order G) :
    ∃ smaller : Fin r → ℕ,
      (∀ i, smaller i ≤ order i) ∧
      totalOrder smaller < totalOrder order ∧
      ∃ (targets : TargetVector r smaller) (W : Finset V),
        MeetsDescendedSize deltaNum deltaDen shrinkDen
          (totalOrder order - totalOrder smaller) (Fintype.card V) W.card ∧
        ∃ coloring : (G.induce (↑W : Set V)).EdgeLabeling (Fin r),
          BadForColoringOn pNum pDen targets (G.induce (↑W : Set V)) coloring := by
  classical
  unfold StrongInductionEventOn at h
  push Not at h
  rcases h with ⟨smaller, hle, hlt, targets, W, hW, coloring, hbad⟩
  refine ⟨smaller, hle, hlt, targets, W, hW, coloring, ?_⟩
  simpa [BadForColoringOn] using hbad

/-! ## Leaving the bad event gives an induced monochromatic copy -/

/-- Generic finite-host form: outside the fixed-coloring bad predicate, one color-copy
hypergraph is Janson. -/
theorem exists_janson_of_not_badForColoringOn
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    {coloring : G.EdgeLabeling (Fin r)}
    (h : ¬ BadForColoringOn pNum pDen targets G coloring) :
    ∃ i : Fin r,
      (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsJanson
        (rationalParameter pNum pDen) (jansonRadius pNum pDen (Fintype.card V)) := by
  classical
  by_contra hnone
  push Not at hnone
  exact h hnone

/-- If a fixed coloring is not bad, then some color-copy hypergraph is Janson. -/
theorem exists_janson_of_not_badForColoring {N r : ℕ} {order : Fin r → ℕ}
    {pNum pDen : ℕ} {targets : TargetVector r order} {G : SimpleGraph (Fin N)}
    {coloring : G.EdgeLabeling (Fin r)}
    (h : ¬ BadForColoring pNum pDen targets G coloring) :
    ∃ i : Fin r,
      (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsJanson
        (rationalParameter pNum pDen) (jansonRadius pNum pDen N) := by
  classical
  by_contra hnone
  push Not at hnone
  exact h (by simpa [BadForColoring, BadForColoringOn] using hnone)

/-- At positive density and positive host order, a coloring outside the fixed-coloring bad
predicate contains a color whose copy hypergraph is nonempty. -/
theorem exists_copyHypergraph_nonempty_of_not_badForColoring
    {N r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph (Fin N)}
    {coloring : G.EdgeLabeling (Fin r)}
    (hnum : 0 < pNum) (hden : 0 < pDen) (hN : 0 < N)
    (h : ¬ BadForColoring pNum pDen targets G coloring) :
    ∃ i : Fin r,
      (copyHypergraph (targets i) (colorClassGraph coloring i) G).Nonempty := by
  obtain ⟨i, hi⟩ := exists_janson_of_not_badForColoring h
  exact ⟨i, hi.nonempty (rationalParameter_nonneg _ _)
    (jansonRadius_pos hnum hden hN)⟩

/-- A host outside the target bad event has a nonempty copy hypergraph in some color for every
edge coloring. -/
theorem exists_copyHypergraph_nonempty_of_not_badForTargets
    {N r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph (Fin N)}
    (hnum : 0 < pNum) (hden : 0 < pDen) (hN : 0 < N)
    (h : ¬ BadForTargets pNum pDen targets G) :
    ∀ coloring : G.EdgeLabeling (Fin r),
      ∃ i : Fin r,
        (copyHypergraph (targets i) (colorClassGraph coloring i) G).Nonempty := by
  intro coloring
  apply exists_copyHypergraph_nonempty_of_not_badForColoring hnum hden hN
  intro hbad
  exact h ⟨coloring, hbad⟩

/-- Two-color specialization: leaving the bad event for a constant target gives exactly the
graph-theoretic monochromatic induced copy used by the induced Ramsey number. -/
theorem monochromaticInducedCopy_of_not_badForTargets
    {n N : ℕ} {pNum pDen : ℕ} (F : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin N)) (hnum : 0 < pNum) (hden : 0 < pDen) (hN : 0 < N)
    (h : ¬ BadForTargets (r := 2) (order := fun _ ↦ n)
      pNum pDen (fun _ ↦ F) G) :
    ∀ coloring : G.EdgeLabeling (Fin 2), MonochromaticInducedCopy F G coloring := by
  intro coloring
  rw [monochromaticInducedCopy_iff_exists_copyHypergraph_nonempty]
  simpa [colorClassGraph] using
    (exists_copyHypergraph_nonempty_of_not_badForTargets hnum hden hN h coloring)

/-- Consequently a host outside the constant-target bad event is an induced Ramsey witness. -/
theorem isInducedRamseyWitness_of_not_badForTargets
    {n N : ℕ} {pNum pDen : ℕ} (F : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin N)) (hnum : 0 < pNum) (hden : 0 < pDen) (hN : 0 < N)
    (h : ¬ BadForTargets (r := 2) (order := fun _ ↦ n)
      pNum pDen (fun _ ↦ F) G) :
    IsInducedRamseyWitness F G :=
  monochromaticInducedCopy_of_not_badForTargets F G hnum hden hN h

/-! ## Targets of order one -/

/-- A nonempty hypergraph whose edges have at most one vertex is Janson at every positive
radius.  Its witness is a
point mass on one edge; all sets entering `Lambda` have cardinality at least two and hence have
weighted degree zero. -/
theorem isJanson_of_nonempty_isBounded_one {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} (hH : H.Nonempty) (hbounded : H.IsBounded 1)
    (p R : ℝ) (hR : 0 < R) : H.IsJanson p R := by
  classical
  obtain ⟨E, hE⟩ := hH
  let nu : Hypergraph.EdgeWeight H := fun A ↦ if A = E then 1 else 0
  right
  refine ⟨nu, ?_⟩
  have hmass : H.mass nu = 1 := by
    simp only [Hypergraph.mass, nu]
    rw [Finset.sum_eq_single E]
    · simp
    · intro A hAH hAE
      simp [hAE]
    · exact fun hEnot ↦ (hEnot hE).elim
  have hdegree : ∀ L ∈ Hypergraph.jansonSets, H.weightedDegree nu L = 0 := by
    intro L hL
    rw [Hypergraph.weightedDegree]
    apply Finset.sum_eq_zero
    intro A hA
    obtain ⟨hAH, hLA⟩ := Finset.mem_filter.mp hA
    have hLcard : 2 ≤ L.card := by
      simpa [Hypergraph.jansonSets] using hL
    have hAcard : A.card ≤ 1 := hbounded A hAH
    have hne : A ≠ E := by
      intro hAE
      subst A
      have : L.card ≤ E.card := Finset.card_le_card hLA
      omega
    simp [nu, hne]
  have hlambda : H.Lambda p nu = 0 := by
    simp only [Hypergraph.Lambda]
    apply Finset.sum_eq_zero
    intro L hL
    simp [hdegree L hL]
  rw [hlambda, hmass]
  simpa using (one_div_pos.mpr hR)

/-- Uniform rank one is the main special case of the preceding bounded-rank lemma. -/
theorem isJanson_of_nonempty_isUniform_one {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} (hH : H.Nonempty) (huniform : H.IsUniform 1)
    (p R : ℝ) (hR : 0 < R) : H.IsJanson p R :=
  isJanson_of_nonempty_isBounded_one hH huniform.isBounded p R hR

/-- The same point-mass argument, including the radius-zero convention. -/
theorem isJanson_of_nonempty_isBounded_one_of_nonneg_radius
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} (hH : H.Nonempty) (hbounded : H.IsBounded 1)
    (p : ℝ) {R : ℝ} (hR : 0 ≤ R) : H.IsJanson p R := by
  rcases hR.eq_or_lt with rfl | hRpos
  · exact Hypergraph.IsJanson.radius_zero H p
  · exact isJanson_of_nonempty_isBounded_one hH hbounded p R hRpos

/-- A target of order zero has the empty set as a copy in every finite host. -/
theorem copyHypergraph_order_zero_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (hn : n = 0) (F : SimpleGraph (Fin n)) (G' G : SimpleGraph V) :
    (copyHypergraph F G' G).Nonempty := by
  classical
  refine ⟨∅, (mem_copyHypergraph F G' G ∅).2 ?_⟩
  have hF : F = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x _ _ ↦ by
    exact Fin.elim0 (Fin.cast hn x)
  have hG' : G'.induce (↑(∅ : Finset V) : Set V) = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x _ _ ↦ by
      simpa using x.2
  have hG : G.induce (↑(∅ : Finset V) : Set V) = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x _ _ ↦ by
      simpa using x.2
  constructor
  · rw [hF, hG']
    let e : Fin n ≃ ↑(∅ : Finset V) := Fintype.equivOfCardEq (by simp [hn])
    exact ⟨by simpa using
      SimpleGraph.Iso.comap e (⊥ : SimpleGraph ↑(∅ : Finset V))⟩
  · exact hG'.trans hG.symm

/-- On an arbitrary finite host, a zero-order target makes a bad coloring impossible. -/
theorem not_badForColoringOn_of_target_order_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    (i : Fin r) (hi : order i = 0) (coloring : G.EdgeLabeling (Fin r)) :
    ¬ BadForColoringOn pNum pDen targets G coloring := by
  intro hbad
  have hcopy : (copyHypergraph (targets i) (colorClassGraph coloring i) G).Nonempty :=
    copyHypergraph_order_zero_nonempty hi (targets i) (colorClassGraph coloring i) G
  have huniform := copyHypergraph_isUniform (targets i) (colorClassGraph coloring i) G
  have hbounded :
      (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsBounded 1 := by
    intro E hE
    calc
      E.card = Fintype.card (Fin (order i)) := huniform E hE
      _ = 0 := by simp [hi]
      _ ≤ 1 := by omega
  apply hbad i
  exact isJanson_of_nonempty_isBounded_one_of_nonneg_radius hcopy hbounded
    (rationalParameter pNum pDen)
    (mul_nonneg (rationalParameter_nonneg _ _) (Nat.cast_nonneg _))

/-- Hence a zero-order target makes the bad event empty on every finite host. -/
theorem not_badForTargetsOn_of_target_order_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    (i : Fin r) (hi : order i = 0) : ¬ BadForTargetsOn pNum pDen targets G := by
  rintro ⟨coloring, hcoloring⟩
  exact not_badForColoringOn_of_target_order_zero i hi coloring hcoloring

/-- On an arbitrary finite host, a one-vertex target makes a bad coloring impossible.  For an
empty host the Janson radius is zero; otherwise a singleton copy supplies the point mass. -/
theorem not_badForColoringOn_of_target_order_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    (i : Fin r) (hi : order i = 1) (coloring : G.EdgeLabeling (Fin r)) :
    ¬ BadForColoringOn pNum pDen targets G coloring := by
  classical
  intro hbad
  by_cases hV : Nonempty V
  · let v : V := Classical.choice hV
    have hcopy : (copyHypergraph (targets i) (colorClassGraph coloring i) G).Nonempty := by
      refine ⟨{v}, (mem_copyHypergraph (targets i) (colorClassGraph coloring i) G {v}).2 ?_⟩
      have hclass : (colorClassGraph coloring i).induce
          (↑({v} : Finset V) : Set V) = ⊥ :=
        SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
          have hx : x.1 = v := by simpa using x.2
          have hy : y.1 = v := by simpa using y.2
          have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
          subst y
          exact ((colorClassGraph coloring i).induce _).loopless.irrefl x hxy
      have hhost : G.induce (↑({v} : Finset V) : Set V) = ⊥ :=
        SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
          have hx : x.1 = v := by simpa using x.2
          have hy : y.1 = v := by simpa using y.2
          have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
          subst y
          exact (G.induce _).loopless.irrefl x hxy
      constructor
      · rw [hclass]
        have htarget : targets i = ⊥ :=
          SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
            have hxyEq : x = y := Fin.eq_of_val_eq (by omega)
            subst y
            exact (targets i).loopless.irrefl x hxy
        rw [htarget]
        let e : Fin (order i) ≃ ↑({v} : Finset V) :=
          Fintype.equivOfCardEq (by simp [hi])
        exact ⟨by simpa using
          SimpleGraph.Iso.comap e (⊥ : SimpleGraph ↑({v} : Finset V))⟩
      · exact hclass.trans hhost.symm
    have huniform := copyHypergraph_isUniform (targets i) (colorClassGraph coloring i) G
    have hbounded :
        (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsBounded 1 := by
      intro E hE
      calc
        E.card = Fintype.card (Fin (order i)) := huniform E hE
        _ = 1 := by simp [hi]
        _ ≤ 1 := le_rfl
    apply hbad i
    exact isJanson_of_nonempty_isBounded_one_of_nonneg_radius hcopy hbounded
      (rationalParameter pNum pDen)
      (mul_nonneg (rationalParameter_nonneg _ _) (Nat.cast_nonneg _))
  · have hcard : Fintype.card V = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hV (Fintype.card_pos_iff.mp hpos)
    apply hbad i
    simpa [jansonRadius, hcard] using
      (Hypergraph.IsJanson.radius_zero
        (copyHypergraph (targets i) (colorClassGraph coloring i) G)
        (rationalParameter pNum pDen))

/-- Consequently, any target of order at most one makes the bad event empty. -/
theorem not_badForTargetsOn_of_target_order_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph V}
    (i : Fin r) (hi : order i ≤ 1) : ¬ BadForTargetsOn pNum pDen targets G := by
  rcases Nat.eq_zero_or_pos (order i) with hzero | hpos
  · exact not_badForTargetsOn_of_target_order_zero i hzero
  · have hone : order i = 1 := by omega
    rintro ⟨coloring, hcoloring⟩
    exact not_badForColoringOn_of_target_order_one i hone coloring hcoloring

/-- A copy hypergraph of a one-vertex target in a nonempty host is nonempty. -/
theorem copyHypergraph_one_nonempty {N : ℕ} (hN : 0 < N)
    (F : SimpleGraph (Fin 1)) (G' G : SimpleGraph (Fin N)) :
    (copyHypergraph F G' G).Nonempty := by
  classical
  let v : Fin N := ⟨0, hN⟩
  refine ⟨{v}, (mem_copyHypergraph F G' G {v}).2 ?_⟩
  have hF : F = ⊥ := SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
    have hxyEq : x = y := Subsingleton.elim _ _
    subst y
    exact F.loopless.irrefl x hxy
  have hG' : G'.induce (↑({v} : Finset (Fin N)) : Set (Fin N)) = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
      have hx : x.1 = v := by simpa using x.2
      have hy : y.1 = v := by simpa using y.2
      have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
      subst y
      exact (G'.induce _).loopless.irrefl x hxy
  have hG : G.induce (↑({v} : Finset (Fin N)) : Set (Fin N)) = ⊥ :=
    SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
      have hx : x.1 = v := by simpa using x.2
      have hy : y.1 = v := by simpa using y.2
      have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
      subst y
      exact (G.induce _).loopless.irrefl x hxy
  constructor
  · rw [hF, hG']
    let e : Fin 1 ≃ ↑({v} : Finset (Fin N)) :=
      Fintype.equivOfCardEq (by simp)
    exact ⟨by simpa using
      SimpleGraph.Iso.comap e (⊥ : SimpleGraph ↑({v} : Finset (Fin N)))⟩
  · exact hG'.trans hG.symm

/-- If one color target has one vertex and the host is nonempty, no coloring can be bad at a
positive radius. -/
theorem not_badForColoring_of_target_order_one
    {N r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph (Fin N)}
    (i : Fin r) (hi : order i = 1) (hN : 0 < N)
    (hnum : 0 < pNum) (hden : 0 < pDen)
    (coloring : G.EdgeLabeling (Fin r)) :
    ¬ BadForColoring pNum pDen targets G coloring := by
  intro hbad
  have hcopy : (copyHypergraph (targets i) (colorClassGraph coloring i) G).Nonempty := by
    -- A direct singleton copy avoids transporting the entire hypergraph along `e`.
    classical
    let v : Fin N := ⟨0, hN⟩
    refine ⟨{v}, (mem_copyHypergraph (targets i) (colorClassGraph coloring i) G {v}).2 ?_⟩
    have hclass : (colorClassGraph coloring i).induce
        (↑({v} : Finset (Fin N)) : Set (Fin N)) = ⊥ :=
      SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
        have hx : x.1 = v := by simpa using x.2
        have hy : y.1 = v := by simpa using y.2
        have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
        subst y
        exact ((colorClassGraph coloring i).induce _).loopless.irrefl x hxy
    have hhost : G.induce (↑({v} : Finset (Fin N)) : Set (Fin N)) = ⊥ :=
      SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
        have hx : x.1 = v := by simpa using x.2
        have hy : y.1 = v := by simpa using y.2
        have hxyEq : x = y := Subtype.ext (hx.trans hy.symm)
        subst y
        exact (G.induce _).loopless.irrefl x hxy
    constructor
    · rw [hclass]
      have htarget : targets i = ⊥ :=
        SimpleGraph.eq_bot_iff_forall_not_adj.mpr fun x y hxy ↦ by
          have hxyEq : x = y := Fin.eq_of_val_eq (by omega)
          subst y
          exact (targets i).loopless.irrefl x hxy
      rw [htarget]
      let e : Fin (order i) ≃ ↑({v} : Finset (Fin N)) :=
        Fintype.equivOfCardEq (by simp [hi])
      exact ⟨by simpa using
        SimpleGraph.Iso.comap e (⊥ : SimpleGraph ↑({v} : Finset (Fin N)))⟩
    · exact hclass.trans hhost.symm
  have huniform := copyHypergraph_isUniform (targets i) (colorClassGraph coloring i) G
  have huniformOne : (copyHypergraph (targets i) (colorClassGraph coloring i) G).IsUniform 1 := by
    simpa [hi] using huniform
  apply hbad i
  simpa [BadForColoring, BadForColoringOn] using
    (isJanson_of_nonempty_isUniform_one hcopy huniformOne
      (rationalParameter pNum pDen) (jansonRadius pNum pDen N)
      (jansonRadius_pos hnum hden hN))

/-- Therefore the bad event is empty whenever one target has exactly one vertex. -/
theorem not_badForTargets_of_target_order_one
    {N r : ℕ} {order : Fin r → ℕ} {pNum pDen : ℕ}
    {targets : TargetVector r order} {G : SimpleGraph (Fin N)}
    (i : Fin r) (hi : order i = 1) (hN : 0 < N)
    (hnum : 0 < pNum) (hden : 0 < pDen) :
    ¬ BadForTargets pNum pDen targets G := by
  rintro ⟨coloring, hcoloring⟩
  exact not_badForColoring_of_target_order_one i hi hN hnum hden coloring hcoloring

end Events
end Erdos565
