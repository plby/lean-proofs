/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.KeyStructure
import ErdosProblems.Erdos565.Events
import ErdosProblems.Erdos565.MaximalSeed
import ErdosProblems.Erdos565.ExtensionAux
import ErdosProblems.Erdos565.RandomGraph
import ErdosProblems.Erdos565.Chernoff
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
# Fixed structural tuples in the ACDFM key lemma

This file supplies the deterministic bookkeeping between the maximal-seed
argument and the product estimate over independent random stars.  In
particular it does four things which should not be hidden in the final union
bound.

* A coloring and a maximal seed determine one of the dependent structural
  tuples counted in `KeyStructure`.
* The color graphs recorded on the seed determine the ambient graph on the
  seed (their supremum is the ambient restriction).
* The high ambient-degree vertices contain a single color class of the
  required size, with the exact cross-multiplied degree bound.
* Bad ambient stars are lifted bijectively to the edge-coordinate blocks used
  by `RandomGraph.card_uniform_fixed_internal_star_family_event`.

The last construction lets the extension estimate be inserted into the
conditional product formula without identifying a random graph with a tuple
of Boolean coordinates by an unstated convention.
-/

open scoped BigOperators SimpleGraph

namespace Erdos565
namespace KeyFixedTuple

/-! ## Accessors and realization of a dependent structural tuple -/

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Structure (V : Type*) [Fintype V] [DecidableEq V]
    (r N : ℕ) (Small : Finset V → Prop) :=
  KeyStructure.RestrictedStructure V r N Small

def vertexSet {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) : Finset V := sigma.1

def seedSet {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) : Finset V := sigma.2.1.1

def radii {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) : Fin r → ℕ :=
  fun i ↦ (sigma.2.2.1 i).1

def colorOnSeed {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) (i : Fin r) :
    SimpleGraph ↑(seedSet sigma) := sigma.2.2.2 i

def ambientOnSeed {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) : SimpleGraph ↑(seedSet sigma) :=
  ⨆ i, colorOnSeed sigma i

theorem seedSet_small {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) : Small (seedSet sigma) :=
  sigma.2.1.2

private lemma coordinate_le_sum {r : ℕ} (R : Fin r → ℕ) (i : Fin r) :
    R i ≤ ∑ j, R j := by
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Every radius of a maximal seed is bounded by the cardinality of the
ambient finite vertex type.  This is the bound needed to store it in the
finite vector `RVector r N`. -/
theorem result_radius_le_card {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (result : MaximalSeed.Result r N S Good) (i : Fin r) :
    result.R i ≤ Fintype.card V := by
  calc
    result.R i ≤ ∑ j, result.R j := coordinate_le_sum result.R i
    _ ≤ result.U.card := by
      rw [result.candidate.2.1]
      exact Nat.le_add_left _ _
    _ ≤ Fintype.card V := Finset.card_le_univ _

/-- The structural tuple canonically extracted from a coloring and a maximal
seed.  The color data is the vector of color-class graphs induced on `U`.
The proof `hV` only converts the intrinsic radius bound to the external
parameter `N`. -/
def ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) : Structure V r N Small :=
  ⟨S, ⟨⟨result.U, hSmall⟩,
    ⟨(fun i ↦ ⟨result.R i, by
        apply Nat.lt_succ_of_le
        exact (result_radius_le_card result i).trans_eq hV⟩),
      fun i ↦ (Events.colorClassGraph coloring i).induce
        (↑result.U : Set V)⟩⟩⟩

@[simp] theorem vertexSet_ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) :
    vertexSet (ofSeed G coloring result Small hSmall hV) = S := rfl

@[simp] theorem seedSet_ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) :
    seedSet (ofSeed G coloring result Small hSmall hV) = result.U := rfl

@[simp] theorem radii_ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) :
    radii (ofSeed G coloring result Small hSmall hV) = result.R := rfl

@[simp] theorem colorOnSeed_ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) (i : Fin r) :
    colorOnSeed (ofSeed G coloring result Small hSmall hV) i =
      (Events.colorClassGraph coloring i).induce (↑result.U : Set V) := rfl

/-- Exact realization predicate for a fixed tuple.  It records the seed-size
identity and the restriction of every color graph, so no global coloring is
included among the objects in the outer union bound. -/
def Realizes {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) (G : SimpleGraph V)
    (coloring : G.EdgeLabeling (Fin r)) : Prop :=
  seedSet sigma ⊆ vertexSet sigma ∧
    (seedSet sigma).card = seedThreshold r N + ∑ i, radii sigma i ∧
    ∀ i, colorOnSeed sigma i =
      (Events.colorClassGraph coloring i).induce (↑(seedSet sigma) : Set V)

theorem realizes_ofSeed {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N) :
    Realizes (ofSeed G coloring result Small hSmall hV) G coloring := by
  exact ⟨result.candidate.1, result.candidate.2.1, fun _ ↦ rfl⟩

/-- The bad-graph event belonging to one fixed structural tuple.  The
application supplies `Failure`; in the key lemma it is the failure of the
`(p,R_i+1)` Janson condition after adjoining `v`.  Quantifying the coloring
*inside* this event is essential: the outer union is only over the finite
structural tuple, never over all global colorings. -/
def FixedTupleBadGraph {r N : ℕ} {Small : Finset V → Prop}
    (sigma : Structure V r N Small) (G : SimpleGraph V)
    (Failure : G.EdgeLabeling (Fin r) → V → Fin r → Prop) : Prop :=
  ∃ coloring : G.EdgeLabeling (Fin r),
    Realizes sigma G coloring ∧
      ∀ v ∈ vertexSet sigma \ seedSet sigma, ∀ i, Failure coloring v i

/-- A coloring together with a maximal seed and all its extension failures
maps to one of the finite structural tuples.  This is the deterministic
covering statement used before the fixed-tuple probability estimate. -/
theorem exists_fixedTuple_of_seedFailures
    {r N : ℕ} {S : Finset V}
    {Good : Fin r → Finset V → ℕ → Prop}
    (G : SimpleGraph V) (coloring : G.EdgeLabeling (Fin r))
    (result : MaximalSeed.Result r N S Good)
    (Small : Finset V → Prop) (hSmall : Small result.U)
    (hV : Fintype.card V = N)
    (Failure : G.EdgeLabeling (Fin r) → V → Fin r → Prop)
    (hFailure : ∀ v ∈ S \ result.U, ∀ i, Failure coloring v i) :
    ∃ sigma : Structure V r N Small,
      vertexSet sigma = S ∧ seedSet sigma = result.U ∧
        radii sigma = result.R ∧ FixedTupleBadGraph sigma G Failure := by
  let sigma := ofSeed G coloring result Small hSmall hV
  refine ⟨sigma, rfl, rfl, rfl, coloring, realizes_ofSeed G coloring result Small hSmall hV, ?_⟩
  simpa [sigma] using hFailure

/-- On a realized tuple the color graphs recover the full ambient graph on
the seed.  This is why the tuple need not carry a separate ambient graph. -/
theorem ambientOnSeed_eq_induce {r N : ℕ} {Small : Finset V → Prop}
    {sigma : Structure V r N Small} {G : SimpleGraph V}
    {coloring : G.EdgeLabeling (Fin r)} (h : Realizes sigma G coloring) :
    ambientOnSeed sigma = G.induce (↑(seedSet sigma) : Set V) := by
  ext x y
  simp only [ambientOnSeed, SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.2.2 i] at hi
    exact (SimpleGraph.EdgeLabeling.labelGraph_le coloring) hi
  · intro hxy
    have hxyG : G.Adj x.1 y.1 := hxy
    let e : G.edgeSet := ⟨s(x.1, y.1), hxyG⟩
    refine ⟨coloring e, ?_⟩
    rw [h.2.2 (coloring e)]
    exact (SimpleGraph.EdgeLabeling.labelGraph_adj x.1 y.1).2 ⟨hxyG, rfl⟩

/-! ## Pigeonholing a common high-degree color -/

/-- Neighbors in `U` joined to `v` by a color-`i` edge. -/
noncomputable def colorNeighbors {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U : Finset V) (v : V) (i : Fin r) :
    Finset V := by
  classical
  exact U.filter fun u ↦ (Events.colorClassGraph coloring i).Adj v u

noncomputable def ambientNeighbors (G : SimpleGraph V) (U : Finset V) (v : V) : Finset V := by
  classical
  exact U.filter fun u ↦ G.Adj v u

theorem pairwiseDisjoint_colorNeighbors {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U : Finset V) (v : V) :
    (Set.univ : Set (Fin r)).PairwiseDisjoint (colorNeighbors coloring U v) := by
  classical
  intro i _hi j _hj hij
  change Disjoint (colorNeighbors coloring U v i) (colorNeighbors coloring U v j)
  rw [Finset.disjoint_left]
  intro u hui huj
  have hi := (Finset.mem_filter.1 hui).2
  have hj := (Finset.mem_filter.1 huj).2
  exact (SimpleGraph.disjoint_left.1
    (SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph hij) v u hi) hj

theorem biUnion_colorNeighbors {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U : Finset V) (v : V) :
    Finset.univ.biUnion (colorNeighbors coloring U v) = ambientNeighbors G U v := by
  classical
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, colorNeighbors,
    ambientNeighbors, Finset.mem_filter]
  constructor
  · rintro ⟨i, hu, hi⟩
    exact ⟨hu, (SimpleGraph.EdgeLabeling.labelGraph_le coloring) hi⟩
  · rintro ⟨hu, hG⟩
    let e : G.edgeSet := ⟨s(v, u), hG⟩
    exact ⟨coloring e, hu,
      (SimpleGraph.EdgeLabeling.labelGraph_adj v u).2 ⟨hG, rfl⟩⟩

theorem sum_card_colorNeighbors {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U : Finset V) (v : V) :
    ∑ i, (colorNeighbors coloring U v i).card = (ambientNeighbors G U v).card := by
  classical
  rw [← biUnion_colorNeighbors coloring U v,
    Finset.card_biUnion (by simpa using pairwiseDisjoint_colorNeighbors coloring U v)]

/-- A vertex of ambient degree greater than `|U|/4` has color degree greater
than `|U|/(4r)` in at least one color. -/
theorem exists_highColor {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U : Finset V) (v : V)
    (hr : 0 < r)
    (hdegree : U.card < 4 * (ambientNeighbors G U v).card) :
    ∃ i : Fin r, U.card < 4 * r * (colorNeighbors coloring U v i).card := by
  by_contra hnot
  push Not at hnot
  have hsum : ∑ i : Fin r, 4 * r * (colorNeighbors coloring U v i).card ≤
      ∑ _i : Fin r, U.card :=
    Finset.sum_le_sum fun i _ ↦ hnot i
  have hsum' : r * (4 * (ambientNeighbors G U v).card) ≤ r * U.card := by
    calc
      r * (4 * (ambientNeighbors G U v).card) =
          ∑ i : Fin r, 4 * r * (colorNeighbors coloring U v i).card := by
        calc
          r * (4 * (ambientNeighbors G U v).card) =
              4 * r * (∑ i : Fin r, (colorNeighbors coloring U v i).card) := by
            rw [sum_card_colorNeighbors]
            ring
          _ = ∑ i : Fin r, 4 * r * (colorNeighbors coloring U v i).card := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin r, U.card := hsum
      _ = r * U.card := by simp
  have hcancel : 4 * (ambientNeighbors G U v).card ≤ U.card := by
    exact Nat.le_of_mul_le_mul_left hsum' hr
  omega

/-- Pigeonhole the high-degree vertices once more, this time by their chosen
high color.  The output `A` satisfies the exact bounds used in the key lemma.
-/
theorem exists_common_highColor {r : ℕ} {G : SimpleGraph V}
    (coloring : G.EdgeLabeling (Fin r)) (U T : Finset V)
    (hr : 0 < r)
    (hdegree : ∀ v ∈ T, U.card < 4 * (ambientNeighbors G U v).card) :
    ∃ (i : Fin r) (A : Finset V),
      A ⊆ T ∧ T.card ≤ r * A.card ∧
        ∀ v ∈ A, U.card < 4 * r * (colorNeighbors coloring U v i).card := by
  classical
  let chosen : (v : ↑T) → Fin r := fun v ↦
    Classical.choose (exists_highColor coloring U v.1 hr (hdegree v.1 v.2))
  let choiceOn : V → Fin r := fun v ↦
    if hv : v ∈ T then chosen ⟨v, hv⟩ else ⟨0, hr⟩
  let fiberCard : Fin r → ℕ := fun i ↦ (T.filter fun v ↦ choiceOn v = i).card
  obtain ⟨i, _hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin r)) fiberCard
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  let A := T.filter fun v ↦ choiceOn v = i
  refine ⟨i, A, Finset.filter_subset _ _, ?_, ?_⟩
  · have hpartition : T.card = ∑ j : Fin r, fiberCard j := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := T) (t := Finset.univ) (f := choiceOn) (by simp)]
    calc
      T.card = ∑ j : Fin r, fiberCard j := hpartition
      _ ≤ ∑ _j : Fin r, fiberCard i :=
        Finset.sum_le_sum fun j hj ↦ hmax j (Finset.mem_univ j)
      _ = r * A.card := by simp [fiberCard, A]
  · intro v hvA
    have hvT : v ∈ T := (Finset.mem_filter.1 hvA).1
    have hchoice : choiceOn v = i := (Finset.mem_filter.1 hvA).2
    have hchosen := Classical.choose_spec
      (exists_highColor coloring U v hr (hdegree v hvT))
    have heq : chosen ⟨v, hvT⟩ = i := by
      simpa [choiceOn, hvT] using hchoice
    rw [← heq]
    simpa [chosen] using hchosen

/-! ## Gluing rooted one-vertex graphs -/

/-- The copy of `Option U` in `U ⊕ A` whose new vertex is `a`. -/
def rootedEmbedding {U A : Type*} (a : A) : Option U ↪ U ⊕ A where
  toFun
    | none => Sum.inr a
    | some u => Sum.inl u
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

/-- Glue a family of one-new-vertex graphs along their common old graph.
No edges are placed between two new vertices, since the key-lemma product
event only exposes the independent stars from `A` to `U`. -/
def glueRooted {U A : Type*} (old : SimpleGraph U)
    (locals : A → SimpleGraph (Option U)) : SimpleGraph (U ⊕ A) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl w => old.Adj u w
    | Sum.inr a, Sum.inl u => (locals a).Adj none (some u)
    | Sum.inl u, Sum.inr a => (locals a).Adj (some u) none
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact hxy.symm
      | inr y => exact hxy.symm
    | inr x =>
      cases y with
      | inl y => exact hxy.symm
      | inr y => exact hxy⟩
  loopless := ⟨by
    intro x hxx
    cases x with
    | inl x => exact old.loopless.irrefl x hxx
    | inr x => exact hxx⟩

@[simp] theorem glueRooted_adj_old {U A : Type*} (old : SimpleGraph U)
    (locals : A → SimpleGraph (Option U)) (u w : U) :
    (glueRooted old locals).Adj (Sum.inl u) (Sum.inl w) ↔ old.Adj u w := Iff.rfl

@[simp] theorem glueRooted_adj_star {U A : Type*} (old : SimpleGraph U)
    (locals : A → SimpleGraph (Option U)) (a : A) (u : U) :
    (glueRooted old locals).Adj (Sum.inr a) (Sum.inl u) ↔
      (locals a).Adj none (some u) := Iff.rfl

/-- Pulling the glued graph back to a root recovers its local graph, provided
all local graphs have the prescribed common old part. -/
theorem comap_glueRooted {U A : Type*} (old : SimpleGraph U)
    (locals : A → SimpleGraph (Option U))
    (hOld : ∀ a, oldPart (locals a) = old) (a : A) :
    (glueRooted old locals).comap (rootedEmbedding a) = locals a := by
  ext x y
  cases x <;> cases y
  · change False ↔ (locals a).Adj none none
    simp only [(locals a).loopless.irrefl none]
  · rfl
  · rfl
  · change old.Adj _ _ ↔ (locals a).Adj (some _) (some _)
    rw [← hOld a]
    rfl

/-- Gluing respects containment, hence independently selected color-star
graphs can be glued below their ambient-star graphs. -/
theorem glueRooted_mono {U A : Type*}
    {oldColor oldAmbient : SimpleGraph U}
    {localColor localAmbient : A → SimpleGraph (Option U)}
    (hOld : oldColor ≤ oldAmbient)
    (hLocal : ∀ a, localColor a ≤ localAmbient a) :
    glueRooted oldColor localColor ≤ glueRooted oldAmbient localAmbient := by
  intro x y hxy
  cases x <;> cases y
  · exact hOld hxy
  · exact hLocal _ hxy
  · exact hLocal _ hxy
  · exact hxy

/-! ## Coordinate realization of extension-star bad sets -/

section StarCoordinates

variable (v : V) (U : Finset V) (hv : v ∉ U)

/-- The natural embedding of vertices of `U` into the edge-coordinate star
rooted at `v`. -/
def starEdgeEmbedding : ↑U ↪ RandomGraph.Edge V where
  toFun u := ⟨s(v, u.1), by
    rw [Sym2.mk_isDiag_iff]
    exact fun h ↦ hv (by simpa [h] using u.2)⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    apply Sym2.congr_right.mp
    exact congrArg Subtype.val hxy

def liftStar (B : Finset ↑U) : Finset (RandomGraph.Edge V) :=
  B.map (starEdgeEmbedding v U hv)

@[simp] theorem liftStar_univ :
    liftStar v U hv Finset.univ = RandomGraph.starEdges v U hv := by
  ext e
  unfold liftStar
  rw [Finset.mem_map, RandomGraph.mem_starEdges_iff]
  constructor
  · rintro ⟨u, _hu, rfl⟩
    exact ⟨u.1, u.2, rfl⟩
  · rintro ⟨u, hu, he⟩
    refine ⟨⟨u, hu⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact he.symm

theorem liftStar_injective : Function.Injective (liftStar v U hv) := by
  intro B C h
  exact Finset.map_injective (starEdgeEmbedding v U hv) h

/-- Lift a set of bad stars on `U` to the actual unordered-edge coordinate
block rooted at `v`. -/
def liftedBadStars (bad : Finset (Finset ↑U)) :
    Finset (Finset (RandomGraph.Edge V)) :=
  bad.image (liftStar v U hv)

@[simp] theorem card_liftedBadStars (bad : Finset (Finset ↑U)) :
    (liftedBadStars v U hv bad).card = bad.card := by
  rw [liftedBadStars, Finset.card_image_iff.mpr]
  intro B _ C _ h
  exact liftStar_injective v U hv h

theorem mem_liftedBadStars_iff {bad : Finset (Finset ↑U)}
    {S : Finset (RandomGraph.Edge V)} :
    S ∈ liftedBadStars v U hv bad ↔
      ∃ B ∈ bad, liftStar v U hv B = S := by
  simp [liftedBadStars]

theorem liftedBadStars_subset_powerset (bad : Finset (Finset ↑U)) :
    liftedBadStars v U hv bad ⊆ (RandomGraph.starEdges v U hv).powerset := by
  intro S hS
  obtain ⟨B, _hB, rfl⟩ := (mem_liftedBadStars_iff
    (v := v) (U := U) (hv := hv)).1 hS
  rw [Finset.mem_powerset, ← liftStar_univ v U hv]
  exact Finset.map_subset_map.2 (Finset.subset_univ B)

/-- Any one-vertex bad-star family (in particular
`Extension.graphExtensionBadStars`) has exactly the same cardinality after
being transported to the unordered-edge block seen by `RandomGraph`. -/
theorem card_liftedBadStars_mul_pow_le
    (bad : Finset (Finset ↑U)) (t : ℕ)
    (h : bad.card * 2 ^ t ≤ 2 ^ U.card) :
    (liftedBadStars v U hv bad).card * 2 ^ t ≤ 2 ^ U.card := by
  simpa using h

end StarCoordinates

end KeyFixedTuple
end Erdos565
