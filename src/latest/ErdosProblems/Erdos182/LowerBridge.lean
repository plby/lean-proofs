/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/

import ErdosProblems.Erdos182.LowerCounting
import ErdosProblems.Erdos182.LowerGraph
import ErdosProblems.Erdos182.LowerUnion
import ErdosProblems.Erdos182.Factor
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib

/-!
# The counting/graph bridge for the layered lower construction

This file identifies a choice in the finite product space of
`LowerCounting` with the dependent choice used to define `layeredGraph`.
It also encodes possible graph edges as coordinate demands.  Thus the
abstract cylinder count becomes the concrete binomial estimate used in the
Pyber--Rödl--Szemerédi union bound.
-/

open Finset Fintype

namespace Erdos182

open scoped BigOperators Classical

noncomputable section

/-! ## The canonical product space -/

/-- A source/later-layer coordinate. -/
abbrev LayerCoordinate {L : ℕ} (b : Option (Fin L) → ℕ) :=
  Fin (b none) × Fin L

/-- A target vertex, with its later-layer index retained. -/
abbrev LaterLayerVertex {L : ℕ} (b : Option (Fin L) → ℕ) :=
  Σ j : Fin L, Fin (b (some j))

/-- The target set at later layer `j`. -/
noncomputable def laterLayerFinset {L : ℕ} (b : Option (Fin L) → ℕ)
    (j : Fin L) : Finset (LaterLayerVertex b) :=
  Finset.univ.map
    ⟨fun w : Fin (b (some j)) ↦ ⟨j, w⟩, fun _ _ h ↦ by simpa using h⟩

@[simp]
lemma mem_laterLayerFinset {L : ℕ} {b : Option (Fin L) → ℕ}
    {j : Fin L} {w : LaterLayerVertex b} :
    w ∈ laterLayerFinset b j ↔ w.1 = j := by
  classical
  constructor
  · intro hw
    obtain ⟨v, _hv, hv⟩ := Finset.mem_map.mp hw
    exact congrArg Sigma.fst hv.symm
  · intro hw
    rcases w with ⟨j', v⟩
    simp only at hw
    subst j'
    apply Finset.mem_map.mpr
    exact ⟨v, Finset.mem_univ _, rfl⟩

@[simp]
lemma card_laterLayerFinset {L : ℕ} (b : Option (Fin L) → ℕ) (j : Fin L) :
    (laterLayerFinset b j).card = b (some j) := by
  classical
  simp [laterLayerFinset]

/-- Allowed targets at each source/layer coordinate. -/
noncomputable def layerAllowed {L : ℕ} (b : Option (Fin L) → ℕ)
    (c : LayerCoordinate b) : Finset (LaterLayerVertex b) :=
  laterLayerFinset b c.2

@[simp]
lemma card_layerAllowed {L : ℕ} (b : Option (Fin L) → ℕ)
    (c : LayerCoordinate b) :
    (layerAllowed b c).card = b (some c.2) := by
  simp [layerAllowed]

/-- An admissible outcome has a uniquely typed target at every coordinate. -/
lemma exists_laterTarget_of_outcome {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    (v : Fin (b none)) (j : Fin L) :
    ∃ x : Fin (b (some j)),
      (⟨j, x⟩ : LaterLayerVertex b) = ω (v, j) (Finset.mem_univ _) := by
  have hwmem : ω (v, j) (Finset.mem_univ _) ∈ laterLayerFinset b j := by
    have := (mem_finiteChoiceSpace.mp hω) (v, j)
    simpa [layerAllowed] using this
  obtain ⟨x, _hx, hx⟩ := Finset.mem_map.mp hwmem
  exact ⟨x, hx⟩

/-- Extract the dependent layered choice represented by an admissible
finite-product outcome. -/
noncomputable def layeredChoiceOfOutcome {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    (v : Fin (b none)) (j : Fin L) : Fin (b (some j)) :=
  Classical.choose (exists_laterTarget_of_outcome ω hω v j)

lemma laterVertex_layeredChoiceOfOutcome {L : ℕ}
    {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    (v : Fin (b none)) (j : Fin L) :
    (⟨j, layeredChoiceOfOutcome ω hω v j⟩ : LaterLayerVertex b) =
      ω (v, j) (Finset.mem_univ _) :=
  Classical.choose_spec (exists_laterTarget_of_outcome ω hω v j)

/-! ## Possible edges and their cylinders -/

/-- A potential layered edge, before the random target is chosen. -/
abbrev LayerDemand {L : ℕ} (b : Option (Fin L) → ℕ) :=
  Σ c : LayerCoordinate b, Fin (b (some c.2))

/-- The coordinate fixed by a potential edge. -/
def layerDemandCoord {L : ℕ} {b : Option (Fin L) → ℕ}
    (d : LayerDemand b) : LayerCoordinate b := d.1

/-- Its target, regarded as a member of the common later-vertex type. -/
def layerDemandTarget {L : ℕ} {b : Option (Fin L) → ℕ}
    (d : LayerDemand b) : LaterLayerVertex b := ⟨d.1.2, d.2⟩

/-- Its corresponding unordered graph edge. -/
def layerDemandEdge {L : ℕ} {b : Option (Fin L) → ℕ}
    (d : LayerDemand b) : Sym2 (LayerVertex b) :=
  s(baseVertex d.1.1, laterVertex d.1.2 d.2)

lemma layerDemandEdge_injective {L : ℕ} {b : Option (Fin L) → ℕ} :
    Function.Injective (layerDemandEdge (b := b)) := by
  rintro ⟨⟨v, j⟩, x⟩ ⟨⟨v', j'⟩, x'⟩ h
  rw [layerDemandEdge, layerDemandEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have hv : v = v' := by
      apply Fin.ext
      exact congrArg (fun z : LayerVertex b ↦ z.2.val) h.1
    have hj : j = j' := by
      simpa [laterVertex] using congrArg Sigma.fst h.2
    subst v'
    subst j'
    have hx : x = x' := by
      apply Fin.ext
      exact congrArg (fun z : LayerVertex b ↦ z.2.val) h.2
    subst x'
    rfl
  · have := congrArg Sigma.fst h.1
    simp [baseVertex, laterVertex] at this

lemma layerDemandEdge_mem_layeredGraph_iff
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (choice : (v : Fin (b none)) → (j : Fin L) → Fin (b (some j)))
    (d : LayerDemand b) :
    layerDemandEdge d ∈ (layeredGraph choice).edgeFinset ↔
      choice d.1.1 d.1.2 = d.2 := by
  classical
  rw [SimpleGraph.mem_edgeFinset, edgeSet_layeredGraph]
  constructor
  · rintro ⟨⟨v, j⟩, h⟩
    rw [layerDemandEdge, layerEdge, Sym2.eq_iff] at h
    rcases h with h | h
    · have hv : d.1.1 = v := by
        apply Fin.ext
        exact congrArg (fun z : LayerVertex b ↦ z.2.val) h.1.symm
      have hj : d.1.2 = j := by
        simpa [laterVertex] using (congrArg Sigma.fst h.2).symm
      subst v
      subst j
      apply Fin.ext
      exact congrArg (fun z : LayerVertex b ↦ z.2.val) h.2
    · have hbad := congrArg Sigma.fst h.1
      simp [baseVertex, laterVertex] at hbad
  · intro h
    refine ⟨d.1, ?_⟩
    simp [layerDemandEdge, layerEdge, h]

/-- All potential layered edges whose two endpoints lie in `S`. -/
noncomputable def candidateLayerDemands {L : ℕ} {b : Option (Fin L) → ℕ}
    (S : Finset (LayerVertex b)) : Finset (LayerDemand b) :=
  Finset.univ.filter fun d ↦
    baseVertex d.1.1 ∈ S ∧ laterVertex d.1.2 d.2 ∈ S

@[simp]
lemma mem_candidateLayerDemands {L : ℕ} {b : Option (Fin L) → ℕ}
    {S : Finset (LayerVertex b)} {d : LayerDemand b} :
    d ∈ candidateLayerDemands S ↔
      baseVertex d.1.1 ∈ S ∧ laterVertex d.1.2 d.2 ∈ S := by
  simp [candidateLayerDemands]

/-- A finite set of potential edges is compatible when no two of its edges
ask the same source/layer coordinate to choose different targets. -/
def CompatibleLayerDemands {L : ℕ} {b : Option (Fin L) → ℕ}
    (R : Finset (LayerDemand b)) : Prop :=
  Set.InjOn layerDemandCoord (↑R : Set (LayerDemand b))

/-- Turn a compatible set of potential layered edges into the corresponding
cylinder event.  An arbitrary outcome supplies irrelevant values away from
the fixed coordinates. -/
noncomputable def coordinateDemandOfLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (R : Finset (LayerDemand b)) :
    CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b) where
  coords := R.image layerDemandCoord
  value c := if h : ∃ d ∈ R, layerDemandCoord d = c then
      layerDemandTarget (Classical.choose h)
    else default c (Finset.mem_univ c)

/-- Candidate internal edges which are actually selected by an admissible
outcome. -/
noncomputable def realizedCandidateLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (S : Finset (LayerVertex b)) : Finset (LayerDemand b) :=
  (candidateLayerDemands S).filter fun d ↦
    ω (layerDemandCoord d) (Finset.mem_univ _) = layerDemandTarget d

@[simp]
lemma mem_realizedCandidateLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    {ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b)}
    {S : Finset (LayerVertex b)} {d : LayerDemand b} :
    d ∈ realizedCandidateLayerDemands ω S ↔
      d ∈ candidateLayerDemands S ∧
        ω (layerDemandCoord d) (Finset.mem_univ _) = layerDemandTarget d := by
  simp [realizedCandidateLayerDemands]

lemma compatible_of_subset_realizedCandidateLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    {ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b)}
    {S : Finset (LayerVertex b)} {R : Finset (LayerDemand b)}
    (hR : R ⊆ realizedCandidateLayerDemands ω S) :
    CompatibleLayerDemands R := by
  classical
  intro d hd e he hcoord
  have hd' := (mem_realizedCandidateLayerDemands.mp (hR hd)).2
  have he' := (mem_realizedCandidateLayerDemands.mp (hR he)).2
  rcases d with ⟨⟨v, j⟩, x⟩
  rcases e with ⟨⟨v', j'⟩, x'⟩
  simp only [layerDemandCoord] at hcoord
  cases hcoord
  have htarget :
      (⟨j, x⟩ : LaterLayerVertex b) = ⟨j, x'⟩ := hd'.symm.trans he'
  have hx : x = x' := by
    apply Fin.ext
    exact congrArg (fun z : LaterLayerVertex b ↦ z.2.val) htarget
  subst x'
  rfl

/-- Every compatible realized edge set gives a cylinder containing the
realizing outcome. -/
lemma mem_coordinateDemand_outcomes_of_subset_realized
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    {S : Finset (LayerVertex b)} {R : Finset (LayerDemand b)}
    (hR : R ⊆ realizedCandidateLayerDemands ω S) :
    ω ∈ (coordinateDemandOfLayerDemands default R).outcomes (layerAllowed b) := by
  classical
  rw [CoordinateDemand.outcomes, mem_fixedChoiceSpace]
  constructor
  · intro c hc
    obtain ⟨d, hdR, hdc⟩ := Finset.mem_image.mp hc
    have hex : ∃ e ∈ R, layerDemandCoord e = c := ⟨d, hdR, hdc⟩
    change ω c (Finset.mem_univ _) =
      (if h : ∃ e ∈ R, layerDemandCoord e = c then
        layerDemandTarget (Classical.choose h) else default c (Finset.mem_univ _))
    rw [dif_pos hex]
    have heSpec := Classical.choose_spec hex
    have hcomp := compatible_of_subset_realizedCandidateLayerDemands hR
    have hed : Classical.choose hex = d :=
      hcomp heSpec.1 hdR (heSpec.2.trans hdc.symm)
    rw [hed]
    rw [← hdc]
    exact (mem_realizedCandidateLayerDemands.mp (hR hdR)).2
  · intro c _hc
    exact (mem_finiteChoiceSpace.mp hω) c

/-- Ambient edges of `G` whose two endpoints lie in `S`.  This finset has
the same cardinality as the edge finset of the induced graph on `S`. -/
def internalLayerEdges {L : ℕ} {b : Option (Fin L) → ℕ}
    (G : SimpleGraph (LayerVertex b)) (S : Finset (LayerVertex b)) :
    Finset (Sym2 (LayerVertex b)) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_internalLayerEdges {L : ℕ} {b : Option (Fin L) → ℕ}
    (G : SimpleGraph (LayerVertex b)) (S : Finset (LayerVertex b)) :
    (internalLayerEdges G S).card =
      (G.induce (S : Set (LayerVertex b))).edgeFinset.card := by
  classical
  simpa [internalLayerEdges] using G.card_filter_edgeFinset_toFinset_subset S

/-- Realized demands are in bijection with the actual internal edges of the
layered graph. -/
lemma image_realizedCandidateLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    (S : Finset (LayerVertex b)) :
    (realizedCandidateLayerDemands ω S).image layerDemandEdge =
      internalLayerEdges (layeredGraph (layeredChoiceOfOutcome ω hω)) S := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hdS, hdreal⟩ := mem_realizedCandidateLayerDemands.mp hd
    apply Finset.mem_filter.mpr
    constructor
    · rw [layerDemandEdge_mem_layeredGraph_iff]
      apply Fin.ext
      have hchosen := laterVertex_layeredChoiceOfOutcome ω hω d.1.1 d.1.2
      exact congrArg (fun z : LaterLayerVertex b ↦ z.2.val)
        (hchosen.trans hdreal)
    · intro z hz
      have hz' : z = baseVertex d.1.1 ∨ z = laterVertex d.1.2 d.2 := by
        simpa [layerDemandEdge, Sym2.mem_toFinset] using hz
      rcases hz' with rfl | rfl
      · exact (mem_candidateLayerDemands.mp hdS).1
      · exact (mem_candidateLayerDemands.mp hdS).2
  · intro he
    obtain ⟨heG, heS⟩ := Finset.mem_filter.mp he
    rw [SimpleGraph.mem_edgeFinset, edgeSet_layeredGraph] at heG
    obtain ⟨⟨v, j⟩, rfl⟩ := heG
    let d : LayerDemand b := ⟨⟨v, j⟩, layeredChoiceOfOutcome ω hω v j⟩
    apply Finset.mem_image.mpr
    refine ⟨d, ?_, ?_⟩
    · rw [mem_realizedCandidateLayerDemands]
      constructor
      · rw [mem_candidateLayerDemands]
        constructor
        · change baseVertex v ∈ S
          apply heS
          rw [Sym2.mem_toFinset]
          simp [layerEdge]
        · change laterVertex j (layeredChoiceOfOutcome ω hω v j) ∈ S
          apply heS
          rw [Sym2.mem_toFinset]
          simp [layerEdge]
      · exact (laterVertex_layeredChoiceOfOutcome ω hω v j).symm
    · simp [d, layerDemandEdge, layerEdge]

lemma card_realizedCandidateLayerDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b))
    (S : Finset (LayerVertex b)) :
    (realizedCandidateLayerDemands ω S).card =
      ((layeredGraph (layeredChoiceOfOutcome ω hω)).induce
        (S : Set (LayerVertex b))).edgeFinset.card := by
  classical
  rw [← card_internalLayerEdges,
    ← image_realizedCandidateLayerDemands ω hω S,
    Finset.card_image_of_injective _ layerDemandEdge_injective]

/-- All compatible `r`-edge prescriptions supported on a candidate vertex
set. -/
noncomputable def candidateCoordinateDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (S : Finset (LayerVertex b)) (r : ℕ) :
    Finset (CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b)) :=
  (((candidateLayerDemands S).powersetCard r).filter CompatibleLayerDemands).image
    (coordinateDemandOfLayerDemands default)

/-- The scale-`i` family is empty unless the candidate set lies in the strict
prefix.  This condition is what makes every demanded target layer at least as
large as the denominator layer used in the PRS count. -/
noncomputable def prefixCandidateCoordinateDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (i : Fin L) (r : ℕ) (S : Finset (LayerVertex b)) :
    Finset (CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b)) :=
  if S ⊆ layerPrefix b i then candidateCoordinateDemands default S r else ∅

/-- A potential edge whose source and target both lie in `S`, regarded as an
edge of the complete graph on the subtype `S`. -/
noncomputable def candidateDemandEdgeIn
    {L : ℕ} {b : Option (Fin L) → ℕ} (S : Finset (LayerVertex b))
    (d : {d : LayerDemand b // d ∈ candidateLayerDemands S}) :
    (⊤ : SimpleGraph (S : Set (LayerVertex b))).edgeFinset := by
  let u : (S : Set (LayerVertex b)) :=
    ⟨baseVertex d.1.1.1, (mem_candidateLayerDemands.mp d.2).1⟩
  let v : (S : Set (LayerVertex b)) :=
    ⟨laterVertex d.1.1.2 d.1.2, (mem_candidateLayerDemands.mp d.2).2⟩
  refine ⟨s(u, v), ?_⟩
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.top_adj, ne_eq]
  intro huv
  have hbad := congrArg (fun z : (S : Set (LayerVertex b)) ↦
    (z.1 : LayerVertex b).1) huv
  simp [u, v, baseVertex, laterVertex] at hbad

lemma candidateDemandEdgeIn_injective
    {L : ℕ} {b : Option (Fin L) → ℕ} (S : Finset (LayerVertex b)) :
    Function.Injective (candidateDemandEdgeIn S) := by
  intro d e hde
  apply Subtype.ext
  apply layerDemandEdge_injective
  have h := congrArg (fun z :
      (⊤ : SimpleGraph (S : Set (LayerVertex b))).edgeFinset ↦
        Sym2.map ((Function.Embedding.subtype (fun x ↦ x ∈ S))) z.1) hde
  simpa [candidateDemandEdgeIn, layerDemandEdge] using h

/-- The number of potential layered edges internal to an `x`-vertex set is
at most `x.choose 2`. -/
lemma card_candidateLayerDemands_le_choose
    {L : ℕ} {b : Option (Fin L) → ℕ} (S : Finset (LayerVertex b)) :
    (candidateLayerDemands S).card ≤ S.card.choose 2 := by
  classical
  have hinj := Fintype.card_le_of_injective (candidateDemandEdgeIn S)
    (candidateDemandEdgeIn_injective S)
  calc
    (candidateLayerDemands S).card =
        Fintype.card {d // d ∈ candidateLayerDemands S} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
        ((⊤ : SimpleGraph (S : Set (LayerVertex b))).edgeFinset) := hinj
    _ = ((⊤ : SimpleGraph (S : Set (LayerVertex b))).edgeFinset).card :=
      Fintype.card_coe _
    _ ≤ (Fintype.card (S : Set (LayerVertex b))).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = S.card.choose 2 := by simp

lemma card_candidateCoordinateDemands_le_choose
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (S : Finset (LayerVertex b)) (r : ℕ) :
    (candidateCoordinateDemands default S r).card ≤
      (S.card.choose 2).choose r := by
  classical
  calc
    (candidateCoordinateDemands default S r).card ≤
        (((candidateLayerDemands S).powersetCard r).filter
          CompatibleLayerDemands).card := Finset.card_image_le
    _ ≤ ((candidateLayerDemands S).powersetCard r).card := Finset.card_filter_le _ _
    _ = (candidateLayerDemands S).card.choose r := Finset.card_powersetCard _ _
    _ ≤ (S.card.choose 2).choose r :=
      Nat.choose_le_choose r (card_candidateLayerDemands_le_choose S)

lemma coords_card_of_mem_candidateCoordinateDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (S : Finset (LayerVertex b)) (r : ℕ)
    {d : CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b)}
    (hd : d ∈ candidateCoordinateDemands default S r) :
    d.coords.card = r := by
  classical
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hRpowerset, hRcompatible⟩ := Finset.mem_filter.mp hR
  rw [coordinateDemandOfLayerDemands]
  have himage : (R.image layerDemandCoord).card = R.card :=
    Finset.card_image_iff.mpr hRcompatible
  rw [himage]
  exact (Finset.mem_powersetCard.mp hRpowerset).2

/-- A semantic sparse-prefix bad event supplies one of the concrete
coordinate-demand cylinders used by the all-scales union bound. -/
lemma mem_prsDemandUnion_of_sparseEarlierSetBadAt
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (ω default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (hω : ω ∈ finiteChoiceSpace (layerAllowed b)) (i : Fin L)
    (hbad : SparseEarlierSetBadAt b
      (layeredGraph (layeredChoiceOfOutcome ω hω)) i) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 1000 * b (some i) ∧
      ω ∈ prsDemandUnion (layerAllowed b) x
        (fun S ↦ prefixCandidateCoordinateDemands default i
          (prsBadEdgeCount x) S) := by
  classical
  obtain ⟨S, hSne, hSprefix, hSsmall, hdense⟩ := hbad
  let r := prsBadEdgeCount S.card
  have hr : r ≤
      ((layeredGraph (layeredChoiceOfOutcome ω hω)).induce
        (S : Set (LayerVertex b))).edgeFinset.card := by
    dsimp only [r, prsBadEdgeCount]
    omega
  have hr' : r ≤ (realizedCandidateLayerDemands ω S).card := by
    rwa [card_realizedCandidateLayerDemands ω hω S]
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hr'
  have hRcandidate : R ⊆ candidateLayerDemands S := by
    intro d hd
    exact (mem_realizedCandidateLayerDemands.mp (hRsub hd)).1
  have hRcompatible : CompatibleLayerDemands R :=
    compatible_of_subset_realizedCandidateLayerDemands hRsub
  refine ⟨S.card, Finset.card_pos.mpr hSne, hSsmall, ?_⟩
  simp only [prsDemandUnion, Finset.mem_biUnion]
  refine ⟨S, ?_, coordinateDemandOfLayerDemands default R, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩
  · simp only [prefixCandidateCoordinateDemands, if_pos hSprefix,
      candidateCoordinateDemands]
    apply Finset.mem_image.mpr
    refine ⟨R, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard.mpr ⟨hRcandidate, hRcard⟩, hRcompatible⟩
  · exact mem_coordinateDemand_outcomes_of_subset_realized
      ω default hω hRsub

/-! ## Passing regular factors back to the ambient graph -/

/-- A regular subgraph found inside the coefficient graph of an ambient
subgraph is also a regular subgraph of the ambient graph. -/
lemma containsRegularSubgraph_of_subgraph_coe
    {V : Type*} [Fintype V] {G : SimpleGraph V} (H : G.Subgraph) {r : ℕ}
    (h : ContainsRegularSubgraph H.coe r) : ContainsRegularSubgraph G r := by
  classical
  obtain ⟨K, hKne, hKreg⟩ := h
  let f : SimpleGraph.Copy H.coe G :=
    ⟨H.hom, SimpleGraph.Subgraph.hom_injective⟩
  let K' : G.Subgraph := K.map f.toHom
  let e : K.coe ≃g K'.coe := f.isoSubgraphMap K
  refine ⟨K', ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hKne
    exact ⟨f v, Set.mem_image_of_mem f hv⟩
  · intro v
    obtain ⟨u, hu, huv⟩ := v.2
    let uK : K.verts := ⟨u, hu⟩
    have hev : e uK = v := by
      apply Subtype.ext
      exact huv
    rw [← hev]
    have hncard := Set.ncard_congr' (e.mapNeighborSet uK)
    exact hncard.symm.trans (hKreg uK)

/-- Any `q`-regular subgraph of a finite bipartite graph, with `3 ≤ q`,
contains a `3`-regular subgraph. -/
lemma containsThreeRegular_of_containsRegular_of_bipartite
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hbip : G.IsBipartite)
    {q : ℕ} (hq : 3 ≤ q) (h : ContainsRegularSubgraph G q) :
    ContainsRegularSubgraph G 3 := by
  classical
  obtain ⟨H, hHne, hHreg⟩ := h
  let : Nonempty H.verts := Set.nonempty_coe_sort.mpr hHne
  have hHbip : H.coe.IsBipartite := by
    obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
    let s' : Set H.verts := {v | (v : V) ∈ s}
    let t' : Set H.verts := {v | (v : V) ∈ t}
    refine (show H.coe.IsBipartiteWith s' t' from ?_).isBipartite
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hvs hvt
      change (v : V) ∈ s at hvs
      change (v : V) ∈ t at hvt
      exact Set.disjoint_left.mp hst.disjoint hvs hvt
    · intro u v huv
      exact hst.mem_of_adj (H.coe_adj_sub u v huv)
  exact containsRegularSubgraph_of_subgraph_coe H
    (containsRegularSubgraph_of_bipartite_regular H.coe hHbip (by
      intro v
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact hHreg v) hq)

/-- The layered construction is simultaneously free of every regular degree
at least three as soon as it is free of degree three. -/
lemma isRegularSubgraphFree_layered_of_three
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (choice : (v : Fin (b none)) → (j : Fin L) → Fin (b (some j)))
    (hthree : IsRegularSubgraphFree (layeredGraph choice) 3) {q : ℕ}
    (hq : 3 ≤ q) : IsRegularSubgraphFree (layeredGraph choice) q := by
  intro hqreg
  exact hthree (containsThreeRegular_of_containsRegular_of_bipartite
    (layeredGraph_isBipartite choice) hq hqreg)

end

end Erdos182
