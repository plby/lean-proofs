/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 705

The exact statement below uses the faithful/induced unit-distance graph on a
finite point set.  The development reconstructs O'Donnell's attached-cycle
construction and supplies an explicit finite generic perturbation proving that
the realization can be chosen injective with no accidental unit nonedges.
-/

open scoped EuclideanGeometry

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

syntax (name := answerSyntax705) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace SimpleGraph

/-- The faithful unit-distance graph on a set of points in the Euclidean plane. -/
def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := Dist.dist x y = 1
  symm := ⟨by
    intro x y hxy
    simpa [PseudoMetricSpace.dist_comm] using hxy⟩
  loopless := ⟨by
    intro x hxx
    simpa using hxx⟩

end SimpleGraph

namespace Erdos705

open SimpleGraph
open scoped RealInnerProductSpace

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- An injective plane realization with no missing or accidental unit edges. -/
def FaithfulUnitDistanceEmbedding {X : Type*} (G : SimpleGraph X) : Prop :=
  ∃ p : X ↪ Plane, ∀ x y, Dist.dist (p x) (p y) = 1 ↔ G.Adj x y

/-- A faithful realization identifies an abstract finite graph with the
unit-distance graph on the range of its realizing map. -/
theorem faithfulUnitDistanceEmbedding_range {X : Type*} [Finite X]
    {G : SimpleGraph X} (hG : FaithfulUnitDistanceEmbedding G) :
    ∃ V : Set Plane, V.Finite ∧
      G.girth = (UnitDistancePlaneGraph V).girth ∧
      G.chromaticNumber = (UnitDistancePlaneGraph V).chromaticNumber := by
  obtain ⟨p, hp⟩ := hG
  let V : Set Plane := Set.range p
  have hV : V.Finite := Set.finite_range p
  let e : X ≃ V := Equiv.ofInjective p p.injective
  have he_apply (x : X) : ((e x : V) : Plane) = p x := rfl
  let iso : G ≃g UnitDistancePlaneGraph V :=
    { e with
      map_rel_iff' := by
        intro x y
        change Dist.dist (e x) (e y) = 1 ↔ G.Adj x y
        simpa only [Subtype.dist_eq, he_apply] using hp x y }
  refine ⟨V, hV, iso.girth_eq, ?_⟩
  exact le_antisymm (chromaticNumber_mono_of_hom iso.toHom)
    (chromaticNumber_mono_of_hom iso.symm.toHom)

/-! ## O'Donnell's attached-cycle graph -/

/-- A finite `r`-uniform hypergraph with a chosen ordering of every edge.
The edge type itself is used as an index, so different edge occurrences remain
distinguishable when cycles are attached. -/
structure OrderedUniformHypergraph (X : Type*) (r : ℕ) where
  Edge : Type*
  edgeFinite : Finite Edge
  vertex : Edge → Fin r ↪ X

namespace OrderedUniformHypergraph

variable {X : Type*} {r : ℕ} (H : OrderedUniformHypergraph X r)

instance : Finite H.Edge := H.edgeFinite

/-- Every three-coloring of the foundation has a monochromatic hyperedge. -/
def NotThreeColorable : Prop :=
  ∀ c : X → Fin 3, ∃ e : H.Edge, ∃ a : Fin 3, ∀ i, c (H.vertex e i) = a

/-- Deleting any one hyperedge from an edge-minimal obstruction leaves a
three-colorable hypergraph. -/
def EdgeMinimalNotThreeColorable : Prop :=
  H.NotThreeColorable ∧
    ∀ e : H.Edge, ∃ c : X → Fin 3,
      ∀ f : H.Edge, f ≠ e → ∃ i j, c (H.vertex f i) ≠ c (H.vertex f j)

/-- The four small regions used in the plane realization: every edge meets at
least two regions, and the exceptional fourth region contains at most one
foundation vertex. -/
def SupportsFourClusters : Prop :=
  ∃ cluster : X → Fin 4,
    Set.Subsingleton {x | cluster x = 3} ∧
    ∀ e : H.Edge, ∃ i j, cluster (H.vertex e i) ≠ cluster (H.vertex e j)

/-- Incidence of a foundation vertex with an ordered hyperedge. -/
def Incident (x : X) (e : H.Edge) : Prop := ∃ i, H.vertex e i = x

private def incidenceAdj : X ⊕ H.Edge → X ⊕ H.Edge → Prop
  | .inl x, .inr e => H.Incident x e
  | .inr e, .inl x => H.Incident x e
  | _, _ => False

/-- The bipartite incidence graph of the hypergraph.  A graph cycle of length
`2s` is exactly a Berge cycle of length `s`. -/
def incidenceGraph : SimpleGraph (X ⊕ H.Edge) where
  Adj := H.incidenceAdj
  symm := ⟨by intro u v; cases u <;> cases v <;> simp [incidenceAdj]⟩
  loopless := ⟨by intro u; cases u <;> simp [incidenceAdj]⟩

/-- A short incidence cycle, packaged through the finite type of bounded-length
walks so that all such cycles can be enumerated. -/
abbrev ShortIncidenceCycle [Finite X] (K : ℕ) :=
  Σ u : X,
    {p : {w : H.incidenceGraph.Walk (.inl u) (.inl u) // w.length < 2 * K} //
      p.1.IsCycle}

private noncomputable def incidenceCycleEdges [Finite X] {K : ℕ}
    (C : H.ShortIncidenceCycle K) : Finset H.Edge := by
  classical
  exact (C.2.1.1.support.filterMap fun
    | .inl _ => none
    | .inr e => some e).toFinset

private theorem mem_incidenceCycleEdges [Finite X] {K : ℕ}
    {C : H.ShortIncidenceCycle K} {e : H.Edge} :
    e ∈ H.incidenceCycleEdges C ↔ Sum.inr e ∈ C.2.1.1.support := by
  classical
  unfold incidenceCycleEdges
  constructor
  · intro he
    rw [List.mem_toFinset, List.mem_filterMap] at he
    obtain ⟨z, hz, hze⟩ := he
    cases z with
    | inl x => simp at hze
    | inr f =>
        have hfe : f = e := Option.some.inj hze
        simpa [hfe] using hz
  · intro he
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨Sum.inr e, he, rfl⟩

/-- All edge occurrences lying on an incidence cycle shorter than `2K`. -/
noncomputable def shortCycleEdges [Finite X] (K : ℕ) : Finset H.Edge := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype H.Edge := Fintype.ofFinite H.Edge
  exact Finset.univ.biUnion
    (fun C : H.ShortIncidenceCycle K ↦ H.incidenceCycleEdges C)

private theorem mem_shortCycleEdges [Finite X] {K : ℕ} {e : H.Edge} :
    e ∈ H.shortCycleEdges K ↔
      ∃ C : H.ShortIncidenceCycle K, e ∈ H.incidenceCycleEdges C := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype H.Edge := Fintype.ofFinite H.Edge
  unfold shortCycleEdges
  simp

private theorem incidenceCycle_has_edge [Finite X] {K : ℕ}
    (C : H.ShortIncidenceCycle K) :
    ∃ e : H.Edge, Sum.inr e ∈ C.2.1.1.support := by
  rcases C with ⟨u, ⟨⟨c, hlength⟩, hc⟩⟩
  have hadj := c.adj_snd hc.not_nil
  cases hsnd : c.snd with
  | inl y =>
      rw [hsnd] at hadj
      exact hadj.elim
  | inr e =>
      refine ⟨e, ?_⟩
      rw [← hsnd]
      exact List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil)

/-- Every incidence cycle contains a foundation vertex, so it may be rotated
to the normalized form used by `ShortIncidenceCycle`. -/
private theorem incidenceCycle_has_foundation {u : X ⊕ H.Edge}
    {c : H.incidenceGraph.Walk u u} (hc : c.IsCycle) :
    ∃ x : X, Sum.inl x ∈ c.support := by
  cases u with
  | inl x => exact ⟨x, c.start_mem_support⟩
  | inr e =>
      have hadj := c.adj_snd hc.not_nil
      cases hsnd : c.snd with
      | inl x =>
          exact ⟨x, by
            rw [← hsnd]
            exact List.mem_of_mem_tail (c.snd_mem_tail_support hc.not_nil)⟩
      | inr f =>
          rw [hsnd] at hadj
          exact hadj.elim

/-- The incidence-graph formulation of Berge girth at least `g`. -/
def BergeGirthAtLeast (g : ℕ) : Prop :=
  (2 * g : ℕ∞) ≤ H.incidenceGraph.egirth

/-- Berge girth at least three makes the hypergraph linear: two distinct edge
occurrences cannot share two distinct foundation vertices.  This is the exact
intersection fact needed by the faithful-realization rigidity analysis. -/
theorem edge_intersection_subsingleton (hberge : H.BergeGirthAtLeast 3)
    {e f : H.Edge} (hef : e ≠ f) {i i' j j' : Fin r}
    (hij : H.vertex e i = H.vertex f j)
    (hij' : H.vertex e i' = H.vertex f j') : i = i' := by
  by_contra hii'
  let x : X := H.vertex e i
  let y : X := H.vertex e i'
  have hxy : x ≠ y := by
    intro h
    exact hii' ((H.vertex e).injective (by simpa [x, y] using h))
  have hxe : H.incidenceGraph.Adj (.inl x) (.inr e) := by
    exact ⟨i, rfl⟩
  have hey : H.incidenceGraph.Adj (.inr e) (.inl y) := by
    exact ⟨i', rfl⟩
  have hyf : H.incidenceGraph.Adj (.inl y) (.inr f) := by
    exact ⟨j', hij'.symm⟩
  have hfx : H.incidenceGraph.Adj (.inr f) (.inl x) := by
    exact ⟨j, hij.symm⟩
  let w : H.incidenceGraph.Walk (.inl x) (.inl x) :=
    .cons hxe (.cons hey (.cons hyf (.cons hfx .nil)))
  have hwcycle : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [SimpleGraph.Walk.isPath_def]
      simp [w, hxy.symm, hef]
    · simp [w]
  have hshort : H.incidenceGraph.egirth ≤ (4 : ℕ) := by
    simpa [w] using SimpleGraph.egirth_le_length hwcycle
  have hlarge : (6 : ℕ∞) ≤ H.incidenceGraph.egirth := by
    change (↑(2 * 3 : ℕ) : ℕ∞) ≤ H.incidenceGraph.egirth
    exact hberge
  have : (6 : ℕ∞) ≤ 4 := hlarge.trans hshort
  norm_num at this

theorem edge_intersection_indices (hberge : H.BergeGirthAtLeast 3)
    {e f : H.Edge} (hef : e ≠ f) {i i' j j' : Fin r}
    (hij : H.vertex e i = H.vertex f j)
    (hij' : H.vertex e i' = H.vertex f j') : i = i' ∧ j = j' := by
  refine ⟨H.edge_intersection_subsingleton hberge hef hij hij', ?_⟩
  exact H.edge_intersection_subsingleton hberge hef.symm hij.symm hij'.symm

/-- An edge-minimal non-three-colorable uniform hypergraph has O'Donnell's
required four-cluster partition: recolor one vertex of the deleted edge with
the exceptional fourth color. -/
theorem supportsFourClusters_of_edgeMinimal (hr : 2 ≤ r)
    (hmin : H.EdgeMinimalNotThreeColorable) : H.SupportsFourClusters := by
  classical
  have hedge : Nonempty H.Edge := by
    obtain ⟨e, _, _⟩ := hmin.1 (fun _ ↦ 0)
    exact ⟨e⟩
  let e₀ : H.Edge := Classical.choice hedge
  obtain ⟨c, hc⟩ := hmin.2 e₀
  let x₀ : X := H.vertex e₀ ⟨0, by omega⟩
  let cluster : X → Fin 4 := fun x ↦ if x = x₀ then 3 else (c x).castSucc
  refine ⟨cluster, ?_, ?_⟩
  · intro x hx y hy
    have hx₀ : x = x₀ := by
      by_contra hne
      have hval : (cluster x).val < 3 := by simp [cluster, hne]
      rw [hx] at hval
      omega
    have hy₀ : y = x₀ := by
      by_contra hne
      have hval : (cluster y).val < 3 := by simp [cluster, hne]
      rw [hy] at hval
      omega
    exact hx₀.trans hy₀.symm
  · intro e
    by_cases he : e = e₀
    · subst e
      let i : Fin r := ⟨0, by omega⟩
      let j : Fin r := ⟨1, by omega⟩
      refine ⟨i, j, ?_⟩
      have hvertex : H.vertex e₀ j ≠ x₀ := by
        intro h
        have hji : j = i := (H.vertex e₀).injective (by simpa [x₀, i] using h)
        have := congrArg Fin.val hji
        simp [i, j] at this
      simp only [cluster, x₀, i, if_pos, hvertex, if_false]
      exact (Fin.castSucc_ne_last _).symm
    · obtain ⟨i, j, hij⟩ := hc e he
      refine ⟨i, j, ?_⟩
      change (if H.vertex e i = x₀ then (3 : Fin 4) else (c (H.vertex e i)).castSucc) ≠
        (if H.vertex e j = x₀ then (3 : Fin 4) else (c (H.vertex e j)).castSucc)
      split_ifs with hi hj
      · exact False.elim (hij (congrArg c (hi.trans hj.symm)))
      · intro h
        exact Fin.castSucc_ne_last _ h.symm
      · intro h
        exact Fin.castSucc_ne_last _ h
      · exact fun h ↦ hij (Fin.castSucc_injective 3 h)

/-- Keep only a finite set of edge occurrences. -/
def restrictEdges (s : Finset H.Edge) : OrderedUniformHypergraph X r where
  Edge := {e : H.Edge // e ∈ s}
  edgeFinite := inferInstance
  vertex e := H.vertex e.1

/-- The finite set of all edge occurrences. -/
noncomputable def edgeFinset : Finset H.Edge := Set.Finite.toFinset Set.finite_univ

@[simp] theorem mem_edgeFinset (e : H.Edge) : e ∈ H.edgeFinset := by
  simp [edgeFinset]

/-- Remove a finite set of edge occurrences.  Packaging the classical finite
set difference keeps downstream proposition signatures free of a chosen
`DecidableEq` instance. -/
noncomputable def deleteEdges (t : Finset H.Edge) : Finset H.Edge := by
  classical
  exact H.edgeFinset \ t

@[simp] theorem mem_deleteEdges {t : Finset H.Edge} {e : H.Edge} :
    e ∈ H.deleteEdges t ↔ e ∉ t := by
  classical
  simp [deleteEdges]

/-- More monochromatic edge occurrences survive than can be destroyed by
deleting any prescribed number of edge occurrences. -/
def DeletionRobustNotThreeColorable (B : ℕ) : Prop :=
  ∀ t : Finset H.Edge, t.card ≤ B →
    (H.restrictEdges (H.deleteEdges t)).NotThreeColorable

theorem incident_restrictEdges_iff (s : Finset H.Edge) (x : X)
    (e : (H.restrictEdges s).Edge) :
    (H.restrictEdges s).Incident x e ↔ H.Incident x e.1 :=
  Iff.rfl

/-- Edge restriction embeds the new incidence graph into the old one. -/
def restrictEdgesIncidenceEmbedding (s : Finset H.Edge) :
    (H.restrictEdges s).incidenceGraph ↪g H.incidenceGraph where
  toFun
    | .inl x => .inl x
    | .inr e => .inr e.1
  inj' := by
    intro u v huv
    cases u with
    | inl x => cases v <;> simp_all
    | inr e =>
        cases v with
        | inl y => simp at huv
        | inr f => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj huv))
  map_rel_iff' := by
    intro u v
    cases u with
    | inl x =>
        cases v with
        | inl y => rfl
        | inr e => rfl
    | inr e =>
        cases v with
        | inl x => rfl
        | inr f => rfl

/-- Removing edge occurrences cannot create a Berge cycle. -/
theorem bergeGirthAtLeast_restrictEdges (s : Finset H.Edge) {g : ℕ}
    (hg : H.BergeGirthAtLeast g) : (H.restrictEdges s).BergeGirthAtLeast g := by
  exact hg.trans (H.restrictEdgesIncidenceEmbedding s).isContained.egirth_le

/-- Deleting every edge occurrence which lies on a short incidence cycle
destroys all such cycles.  This is the deterministic deletion step in the
Erdős--Hajnal argument. -/
theorem bergeGirthAtLeast_deleteShortCycles [Finite X] (K : ℕ) :
    (H.restrictEdges (H.deleteEdges (H.shortCycleEdges K))).BergeGirthAtLeast K := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype H.Edge := Fintype.ofFinite H.Edge
  rw [BergeGirthAtLeast, le_egirth]
  intro u c hc
  apply ENat.natCast_le_natCast.mpr
  by_contra hlength
  have hshortLength : c.length < 2 * K := Nat.lt_of_not_ge hlength
  let H' := H.restrictEdges (H.deleteEdges (H.shortCycleEdges K))
  obtain ⟨x, hx⟩ := H'.incidenceCycle_has_foundation hc
  let c' := c.rotate (Sum.inl x) hx
  have hc' : c'.IsCycle :=
    (SimpleGraph.Walk.isCycle_rotate (c := c) (u := Sum.inl x) hx).mpr hc
  have hc'Length : c'.length < 2 * K := by simpa [c'] using hshortLength
  let C' : H'.ShortIncidenceCycle K :=
    ⟨x, ⟨⟨c', hc'Length⟩, hc'⟩⟩
  obtain ⟨e, heSupport⟩ := H'.incidenceCycle_has_edge C'
  let f := H.restrictEdgesIncidenceEmbedding (H.deleteEdges (H.shortCycleEdges K))
  let d := c'.map f.toHom
  have hdCycle : d.IsCycle := hc'.map f.injective
  have hdLength : d.length < 2 * K := by simpa [d] using hc'Length
  let C : H.ShortIncidenceCycle K :=
    ⟨x, ⟨⟨d, hdLength⟩, hdCycle⟩⟩
  have heMapped : Sum.inr e.1 ∈ d.support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨Sum.inr e, heSupport, rfl⟩
  have heCycle : e.1 ∈ H.incidenceCycleEdges C := by
    change e.1 ∈ (d.support.filterMap (fun
      | .inl (_ : X) => none
      | .inr e => some e)).toFinset
    simp only [List.mem_toFinset, List.mem_filterMap]
    exact ⟨Sum.inr e.1, heMapped, rfl⟩
  have heShort : e.1 ∈ H.shortCycleEdges K := by
    unfold shortCycleEdges
    rw [Finset.mem_biUnion]
    exact ⟨C, Finset.mem_univ _, heCycle⟩
  exact (H.mem_deleteEdges.mp e.2) heShort

/-- If the random hypergraph is robust against deleting as many edge
occurrences as lie on short cycles, the standard deletion argument yields a
large-Berge-girth non-three-colorable restriction. -/
theorem exists_largeBergeGirth_restriction [Finite X] (K : ℕ)
    (hrobust : H.DeletionRobustNotThreeColorable (H.shortCycleEdges K).card) :
    ∃ s : Finset H.Edge,
      (H.restrictEdges s).BergeGirthAtLeast K ∧
      (H.restrictEdges s).NotThreeColorable := by
  let s := H.deleteEdges (H.shortCycleEdges K)
  refine ⟨s, H.bergeGirthAtLeast_deleteShortCycles K, ?_⟩
  exact hrobust (H.shortCycleEdges K) le_rfl

/-- Every finite non-three-colorable uniform hypergraph contains an
edge-minimal non-three-colorable restriction. -/
theorem exists_edgeMinimal_restriction (hr : 0 < r) (hH : H.NotThreeColorable) :
    ∃ s : Finset H.Edge, (H.restrictEdges s).EdgeMinimalNotThreeColorable := by
  classical
  letI : Fintype H.Edge := Fintype.ofFinite H.Edge
  let P : ℕ → Prop := fun m ↦
    ∃ s : Finset H.Edge, s.card = m ∧ (H.restrictEdges s).NotThreeColorable
  have hP : ∃ m, P m := by
    refine ⟨Fintype.card H.Edge, Finset.univ, Finset.card_univ, ?_⟩
    intro c
    obtain ⟨e, a, hea⟩ := hH c
    exact ⟨⟨e, Finset.mem_univ e⟩, a, hea⟩
  let m := Nat.find hP
  obtain ⟨s, hscard, hsnot⟩ := Nat.find_spec hP
  refine ⟨s, hsnot, ?_⟩
  intro e
  have hnotErase : ¬(H.restrictEdges (s.erase e.1)).NotThreeColorable := by
    intro herase
    have hmpos : 0 < m := by
      change 0 < Nat.find hP
      rw [← hscard]
      exact Finset.card_pos.mpr ⟨e.1, e.2⟩
    have hsmall : (s.erase e.1).card < m := by
      rw [Finset.card_erase_of_mem e.2, hscard]
      omega
    exact (Nat.find_min hP hsmall) ⟨s.erase e.1, rfl, herase⟩
  unfold NotThreeColorable at hnotErase
  push_neg at hnotErase
  obtain ⟨c, hc⟩ := hnotErase
  refine ⟨c, ?_⟩
  intro f hfe
  have hfmem : f.1 ∈ s.erase e.1 := Finset.mem_erase.mpr ⟨by
    intro h
    apply hfe
    exact Subtype.ext h, f.2⟩
  let f' : (H.restrictEdges (s.erase e.1)).Edge := ⟨f.1, hfmem⟩
  let i₀ : Fin r := ⟨0, hr⟩
  obtain ⟨i, hi⟩ := hc f' (c (H.vertex f.1 i₀))
  exact ⟨i, i₀, hi⟩

/-! ## The finite random hypergraph model

The probabilistic construction below samples the `r`-subsets of `Fin n` by
assigning each of them a uniform label in `Fin D` and retaining precisely the
labels below a threshold `C`.  The definitions in this subsection are entirely
finite; probability estimates are cardinality estimates on the label-function
type. -/

/-- The finite type of `r`-element subsets of `Fin n`. -/
abbrev UniformEdge (n r : ℕ) := {e : Finset (Fin n) // e.card = r}

instance uniformEdgeFinite (n r : ℕ) : Finite (UniformEdge n r) := inferInstance

/-- The canonical increasing ordering of a finite `r`-set. -/
def uniformEdgeVertex {n r : ℕ} (e : UniformEdge n r) : Fin r ↪ Fin n :=
  (e.1.orderEmbOfFin e.2).toEmbedding

/-- A label-threshold sample of the complete `r`-uniform hypergraph. -/
abbrev sampledHypergraph {n r D C : ℕ} (ω : UniformEdge n r → Fin D) :
    OrderedUniformHypergraph (Fin n) r where
  Edge := {e : UniformEdge n r // (ω e).val < C}
  edgeFinite := inferInstance
  vertex e := uniformEdgeVertex e.1

/-- A foundation coloring is constant on the vertices of an `r`-set. -/
def EdgeMonochromatic {n r q : ℕ} (c : Fin n → Fin q) (e : UniformEdge n r) : Prop :=
  ∃ a : Fin q, ∀ x ∈ e.1, c x = a

/-- Selected monochromatic edge occurrences for one coloring. -/
noncomputable def selectedMonochromaticEdges {n r q D : ℕ}
    (C : ℕ) (ω : UniformEdge n r → Fin D)
    (c : Fin n → Fin q) : Finset (UniformEdge n r) := by
  classical
  exact Finset.univ.filter fun e ↦ (ω e).val < C ∧ EdgeMonochromatic c e

@[simp] theorem mem_selectedMonochromaticEdges {n r q D C : ℕ}
    {ω : UniformEdge n r → Fin D} {c : Fin n → Fin q} {e : UniformEdge n r} :
    e ∈ selectedMonochromaticEdges C ω c ↔
      (ω e).val < C ∧ EdgeMonochromatic c e := by
  classical
  simp [selectedMonochromaticEdges]

/-- More than `B` selected monochromatic edges for every coloring is exactly
the robustness needed by the later short-cycle deletion. -/
theorem sampledHypergraph_deletionRobust {n r D C B : ℕ}
    (ω : UniformEdge n r → Fin D)
    (hmono : ∀ c : Fin n → Fin 3,
      B < (selectedMonochromaticEdges C ω c).card) :
    (sampledHypergraph (C := C) ω).DeletionRobustNotThreeColorable B := by
  classical
  intro t ht c
  let used : Finset (UniformEdge n r) := t.image (fun e ↦ e.1)
  have hused : used.card ≤ B :=
    (Finset.card_image_le.trans ht)
  obtain ⟨e, heMono, heNotUsed⟩ :
      ∃ e ∈ selectedMonochromaticEdges C ω c, e ∉ used := by
    by_contra h
    push Not at h
    have hsub : selectedMonochromaticEdges C ω c ⊆ used := by
      intro e he
      exact h e he
    exact (not_lt_of_ge ((Finset.card_le_card hsub).trans hused)) (hmono c)
  have heSelected : (ω e).val < C :=
    (mem_selectedMonochromaticEdges.mp heMono).1
  let e' : (sampledHypergraph (C := C) ω).Edge := ⟨e, heSelected⟩
  have heKept : e' ∈ (sampledHypergraph (C := C) ω).deleteEdges t := by
    rw [mem_deleteEdges]
    intro heT
    exact heNotUsed (Finset.mem_image.mpr ⟨e', heT, rfl⟩)
  refine ⟨⟨e', heKept⟩, ?_⟩
  obtain ⟨a, hea⟩ := (mem_selectedMonochromaticEdges.mp heMono).2
  refine ⟨a, fun i ↦ ?_⟩
  exact hea _ (Finset.orderEmbOfFin_mem e.1 e.2 i)

/-- Split a label function into the coordinates constrained below `C` and the
unconstrained complementary coordinates. -/
private def thresholdFunEquiv {I : Type*} [Fintype I] (p : I → Prop)
    [DecidablePred p] {C D : ℕ} (hCD : C ≤ D) :
    {f : I → Fin D // ∀ i, p i → (f i).val < C} ≃
      (({i : I // p i} → Fin C) × ({i : I // ¬p i} → Fin D)) where
  toFun f :=
    (fun i ↦ ⟨(f.1 i).val, f.2 i i.2⟩,
      fun i ↦ f.1 i)
  invFun f := ⟨fun i ↦ if hi : p i then
      Fin.castLE hCD (f.1 ⟨i, hi⟩) else f.2 ⟨i, hi⟩, by
    intro i hi
    simp [hi]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : p i <;> simp [hi]
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext
    · funext i
      apply Fin.ext
      simp [i.2]
    · funext i
      simp [i.2]

/-- Exact count for independent uniform labels satisfying a coordinatewise
threshold on a prescribed finite set of coordinates. -/
private theorem card_thresholdLabelings {I : Type*} [Fintype I]
    (p : I → Prop) [DecidablePred p] {C D : ℕ} (hCD : C ≤ D) :
    Nat.card {f : I → Fin D // ∀ i, p i → (f i).val < C} =
      C ^ Nat.card {i : I // p i} *
        D ^ Nat.card {i : I // ¬p i} := by
  rw [Nat.card_congr (thresholdFunEquiv p hCD), Nat.card_prod,
    Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]

/-- Finset form of `card_thresholdLabelings`. -/
private theorem card_labelings_selecting_finset {I : Type*} [Fintype I]
    (s : Finset I) {C D : ℕ} (hCD : C ≤ D) :
    Nat.card {f : I → Fin D // ∀ i ∈ s, (f i).val < C} =
      C ^ s.card * D ^ (Fintype.card I - s.card) := by
  classical
  rw [card_thresholdLabelings (fun i ↦ i ∈ s) hCD]
  congr 2
  · exact Nat.subtype_card s (fun _ ↦ Iff.rfl)
  · rw [Nat.subtype_card (Finset.univ \ s) (by simp),
      Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]

/-- The analogous coordinate split for labels constrained to lie in
`{C, ..., D-1}`. -/
private def upperThresholdFunEquiv {I : Type*} [Fintype I] (p : I → Prop)
    [DecidablePred p] {C D : ℕ} (hCD : C ≤ D) :
    {f : I → Fin D // ∀ i, p i → C ≤ (f i).val} ≃
      (({i : I // p i} → Fin (D - C)) × ({i : I // ¬p i} → Fin D)) where
  toFun f :=
    (fun i ↦ ⟨(f.1 i).val - C, by
        have := (f.1 i).isLt
        have := f.2 i i.2
        omega⟩,
      fun i ↦ f.1 i)
  invFun f := ⟨fun i ↦ if hi : p i then
      ⟨C + (f.1 ⟨i, hi⟩).val, by
        have := (f.1 ⟨i, hi⟩).isLt
        omega⟩ else f.2 ⟨i, hi⟩, by
    intro i hi
    dsimp only
    rw [dif_pos hi]
    change C ≤ C + (f.1 ⟨i, hi⟩).val
    omega⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : p i
    · apply Fin.ext
      dsimp only
      rw [dif_pos hi]
      change C + ((f.1 i).val - C) = (f.1 i).val
      have hlow := f.2 i hi
      omega
    · apply Fin.ext
      dsimp only
      rw [dif_neg hi]
  right_inv f := by
    rcases f with ⟨f, g⟩
    apply Prod.ext
    · funext i
      apply Fin.ext
      dsimp only
      rw [dif_pos i.2]
      change C + (f i).val - C = (f i).val
      omega
    · funext i
      apply Fin.ext
      dsimp only
      rw [dif_neg i.2]

private theorem card_upperThresholdLabelings {I : Type*} [Fintype I]
    (p : I → Prop) [DecidablePred p] {C D : ℕ} (hCD : C ≤ D) :
    Nat.card {f : I → Fin D // ∀ i, p i → C ≤ (f i).val} =
      (D - C) ^ Nat.card {i : I // p i} *
        D ^ Nat.card {i : I // ¬p i} := by
  rw [Nat.card_congr (upperThresholdFunEquiv p hCD), Nat.card_prod,
    Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]

private theorem card_labelings_avoiding_finset {I : Type*} [Fintype I]
    (s : Finset I) {C D : ℕ} (hCD : C ≤ D) :
    Nat.card {f : I → Fin D // ∀ i ∈ s, C ≤ (f i).val} =
      (D - C) ^ s.card * D ^ (Fintype.card I - s.card) := by
  classical
  rw [card_upperThresholdLabelings (fun i ↦ i ∈ s) hCD]
  congr 2
  · exact Nat.subtype_card s (fun _ ↦ Iff.rfl)
  · rw [Nat.subtype_card (Finset.univ \ s) (by simp),
      Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ]

/-- A finite binomial lower-tail bound.  If at most `B` coordinates of `s`
have labels below `C`, extend those coordinates to a `B`-subset `t` of `s`.
All coordinates of `s \ t` then have labels at least `C`.  Encoding the chosen
`t` gives the displayed union bound. -/
private theorem card_labelings_with_few_selected {I : Type*} [Fintype I]
    (s : Finset I) {B C D : ℕ} (hB : B ≤ s.card) (hCD : C ≤ D) :
    Nat.card {f : I → Fin D //
        (s.filter fun i ↦ (f i).val < C).card ≤ B} ≤
      (Nat.choose s.card B) *
        ((D - C) ^ (s.card - B) *
          D ^ (Fintype.card I - (s.card - B))) := by
  classical
  let Small := {f : I → Fin D //
    (s.filter fun i ↦ (f i).val < C).card ≤ B}
  let Choices := {t : Finset I // t ∈ s.powersetCard B}
  let Cover (t : Finset I) := {f : I → Fin D //
    ∀ i ∈ s \ t, C ≤ (f i).val}
  have hchoice (f : Small) : ∃ t : Finset I,
      t ∈ s.powersetCard B ∧ ∀ i ∈ s \ t, C ≤ (f.1 i).val := by
    let selected := s.filter fun i ↦ (f.1 i).val < C
    obtain ⟨t, hselected, hts, htcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.filter_subset _ _)
        f.2 hB
    refine ⟨t, Finset.mem_powersetCard.mpr ⟨hts, htcard⟩, ?_⟩
    intro i hi
    by_contra hilabel
    have hiSelected : i ∈ selected := by
      simp only [selected, Finset.mem_filter]
      exact ⟨(Finset.mem_sdiff.mp hi).1, Nat.lt_of_not_ge hilabel⟩
    exact (Finset.mem_sdiff.mp hi).2 (hselected hiSelected)
  let chosen (f : Small) : Finset I := Classical.choose (hchoice f)
  have hchosen (f : Small) :
      chosen f ∈ s.powersetCard B ∧
        ∀ i ∈ s \ chosen f, C ≤ (f.1 i).val :=
    Classical.choose_spec (hchoice f)
  let encode : Small → Σ t : Choices, Cover t.1 := fun f ↦
    ⟨⟨chosen f, (hchosen f).1⟩, ⟨f.1, (hchosen f).2⟩⟩
  have hencode : Function.Injective encode := by
    intro f g hfg
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hfg
  calc
    Nat.card Small ≤ Nat.card (Σ t : Choices, Cover t.1) :=
      Nat.card_le_card_of_injective encode hencode
    _ = ∑ t : Choices, Nat.card (Cover t.1) := Nat.card_sigma
    _ = ∑ _t : Choices,
        ((D - C) ^ (s.card - B) *
          D ^ (Fintype.card I - (s.card - B))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [show Nat.card (Cover t.1) =
          (D - C) ^ (s \ t.1).card *
            D ^ (Fintype.card I - (s \ t.1).card) by
        exact card_labelings_avoiding_finset (s \ t.1) hCD]
      have ht := Finset.mem_powersetCard.mp t.2
      rw [Finset.card_sdiff_of_subset ht.1, ht.2]
    _ = (Nat.choose s.card B) *
        ((D - C) ^ (s.card - B) *
          D ^ (Fintype.card I - (s.card - B))) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Fintype.card_coe, Finset.card_powersetCard]

/-- A color class containing `⌊n/3⌋` vertices, together with a fixed subset of
exactly that size. -/
private theorem exists_threeColorBlock {n : ℕ} (c : Fin n → Fin 3) :
    ∃ a : Fin 3, ∃ A : Finset (Fin n),
      A ⊆ Finset.univ.filter (fun x ↦ c x = a) ∧ A.card = n / 3 := by
  have hmul : Fintype.card (Fin 3) * (n / 3) ≤ Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ :=
    Fintype.exists_le_card_fiber_of_mul_le_card (f := c) hmul
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq ha
  exact ⟨a, A, hA, hAcard⟩

private noncomputable def threeColorBlockColor {n : ℕ} (c : Fin n → Fin 3) : Fin 3 :=
  Classical.choose (exists_threeColorBlock c)

private noncomputable def threeColorBlock {n : ℕ}
    (c : Fin n → Fin 3) : Finset (Fin n) :=
  Classical.choose (Classical.choose_spec (exists_threeColorBlock c))

private theorem threeColorBlock_spec {n : ℕ} (c : Fin n → Fin 3) :
    threeColorBlock c ⊆ Finset.univ.filter
        (fun x ↦ c x = threeColorBlockColor c) ∧
      (threeColorBlock c).card = n / 3 :=
  Classical.choose_spec (Classical.choose_spec (exists_threeColorBlock c))

private def blockEdgeEmbedding {n r : ℕ} (A : Finset (Fin n)) :
    {e : Finset (Fin n) // e ∈ A.powersetCard r} ↪ UniformEdge n r where
  toFun e := ⟨e.1, (Finset.mem_powersetCard.mp e.2).2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact congrArg (fun z : UniformEdge n r ↦ z.1) hef

/-- The `r`-sets contained in the chosen large color block. -/
private noncomputable def threeColorBlockEdges {n r : ℕ}
    (c : Fin n → Fin 3) : Finset (UniformEdge n r) := by
  classical
  exact (threeColorBlock c).powersetCard r |>.attach.map
    (blockEdgeEmbedding (threeColorBlock c))

private theorem mem_threeColorBlockEdges {n r : ℕ} {c : Fin n → Fin 3}
    {e : UniformEdge n r} :
    e ∈ threeColorBlockEdges c ↔ e.1 ⊆ threeColorBlock c := by
  classical
  constructor
  · intro he
    rw [threeColorBlockEdges, Finset.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact (Finset.mem_powersetCard.mp f.2).1
  · intro he
    rw [threeColorBlockEdges, Finset.mem_map]
    let f : {e : Finset (Fin n) // e ∈ (threeColorBlock c).powersetCard r} :=
      ⟨e.1, Finset.mem_powersetCard.mpr ⟨he, e.2⟩⟩
    exact ⟨f, Finset.mem_attach _ _, Subtype.ext rfl⟩

private theorem card_threeColorBlockEdges {n r : ℕ} (c : Fin n → Fin 3) :
    (threeColorBlockEdges (r := r) c).card = Nat.choose (n / 3) r := by
  classical
  rw [threeColorBlockEdges, Finset.card_map, Finset.card_attach,
    Finset.card_powersetCard, (threeColorBlock_spec c).2]

private theorem threeColorBlockEdges_monochromatic {n r : ℕ}
    (c : Fin n → Fin 3) {e : UniformEdge n r}
    (he : e ∈ threeColorBlockEdges c) : EdgeMonochromatic c e := by
  refine ⟨threeColorBlockColor c, ?_⟩
  intro x hx
  have hxBlock := (mem_threeColorBlockEdges.mp he) hx
  exact (Finset.mem_filter.mp ((threeColorBlock_spec c).1 hxBlock)).2

/-- Union bound over all three-colorings.  The right side is the number of
colorings times the lower-tail estimate on the fixed monochromatic block. -/
private theorem card_labelings_with_bad_threeColoring
    {n r B C D : ℕ} (hB : B ≤ Nat.choose (n / 3) r) (hCD : C ≤ D) :
    Nat.card {ω : UniformEdge n r → Fin D //
        ∃ c : Fin n → Fin 3,
          (selectedMonochromaticEdges C ω c).card ≤ B} ≤
      3 ^ n *
        (Nat.choose (Nat.choose (n / 3) r) B *
          ((D - C) ^ (Nat.choose (n / 3) r - B) *
            D ^ (Fintype.card (UniformEdge n r) -
              (Nat.choose (n / 3) r - B)))) := by
  classical
  let Bad := {ω : UniformEdge n r → Fin D //
    ∃ c : Fin n → Fin 3,
      (selectedMonochromaticEdges C ω c).card ≤ B}
  let Tail (c : Fin n → Fin 3) :=
    {ω : UniformEdge n r → Fin D //
      ((threeColorBlockEdges (r := r) c).filter
        fun e ↦ (ω e).val < C).card ≤ B}
  have htail (ω : Bad) : ∃ c : Fin n → Fin 3,
      ((threeColorBlockEdges (r := r) c).filter
        fun e ↦ (ω.1 e).val < C).card ≤ B := by
    obtain ⟨c, hc⟩ := ω.2
    refine ⟨c, ?_⟩
    have hsub : (threeColorBlockEdges (r := r) c).filter
          (fun e ↦ (ω.1 e).val < C) ⊆
        selectedMonochromaticEdges C ω.1 c := by
      intro e he
      have he' := Finset.mem_filter.mp he
      exact mem_selectedMonochromaticEdges.mpr
        ⟨he'.2, threeColorBlockEdges_monochromatic c he'.1⟩
    exact (Finset.card_le_card hsub).trans hc
  let chosenColor (ω : Bad) : Fin n → Fin 3 := Classical.choose (htail ω)
  have hchosen (ω : Bad) :
      ((threeColorBlockEdges (r := r) (chosenColor ω)).filter
        fun e ↦ (ω.1 e).val < C).card ≤ B :=
    Classical.choose_spec (htail ω)
  let encode : Bad → Σ c : Fin n → Fin 3, Tail c := fun ω ↦
    ⟨chosenColor ω, ⟨ω.1, hchosen ω⟩⟩
  have hencode : Function.Injective encode := by
    intro ω η hωη
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hωη
  let Q := Nat.choose (n / 3) r
  let R := Nat.choose Q B *
    ((D - C) ^ (Q - B) *
      D ^ (Fintype.card (UniformEdge n r) - (Q - B)))
  have hTailCard (c : Fin n → Fin 3) : Nat.card (Tail c) ≤ R := by
    have h := card_labelings_with_few_selected
      (threeColorBlockEdges (r := r) c) (B := B) (C := C) (D := D)
      (by simpa [card_threeColorBlockEdges c] using hB) hCD
    simpa [Tail, R, Q, card_threeColorBlockEdges c] using h
  calc
    Nat.card Bad ≤ Nat.card (Σ c : Fin n → Fin 3, Tail c) :=
      Nat.card_le_card_of_injective encode hencode
    _ = ∑ c : Fin n → Fin 3, Nat.card (Tail c) := Nat.card_sigma
    _ ≤ ∑ _c : Fin n → Fin 3, R := Finset.sum_le_sum fun c _ ↦ hTailCard c
    _ = 3 ^ n * R := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = 3 ^ n *
        (Nat.choose (Nat.choose (n / 3) r) B *
          ((D - C) ^ (Nat.choose (n / 3) r - B) *
            D ^ (Fintype.card (UniformEdge n r) -
              (Nat.choose (n / 3) r - B)))) := rfl

private noncomputable def colorBadLabelings (n r B C D : ℕ) :
    Finset (UniformEdge n r → Fin D) := by
  classical
  exact Finset.univ.filter fun ω ↦ ∃ c : Fin n → Fin 3,
    (selectedMonochromaticEdges C ω c).card ≤ B

@[simp] private theorem mem_colorBadLabelings {n r B C D : ℕ}
    {ω : UniformEdge n r → Fin D} :
    ω ∈ colorBadLabelings n r B C D ↔
      ∃ c : Fin n → Fin 3,
        (selectedMonochromaticEdges C ω c).card ≤ B := by
  classical
  simp [colorBadLabelings]

private theorem card_colorBadLabelings_le {n r B C D : ℕ}
    (hB : B ≤ Nat.choose (n / 3) r) (hCD : C ≤ D) :
    (colorBadLabelings n r B C D).card ≤
      3 ^ n *
        (Nat.choose (Nat.choose (n / 3) r) B *
          ((D - C) ^ (Nat.choose (n / 3) r - B) *
            D ^ (Fintype.card (UniformEdge n r) -
              (Nat.choose (n / 3) r - B)))) := by
  classical
  let Bad := {ω : UniformEdge n r → Fin D //
    ∃ c : Fin n → Fin 3,
      (selectedMonochromaticEdges C ω c).card ≤ B}
  have hcard : Nat.card Bad = (colorBadLabelings n r B C D).card := by
    exact Nat.subtype_card (colorBadLabelings n r B C D)
      (fun _ ↦ mem_colorBadLabelings)
  rw [← hcard]
  exact card_labelings_with_bad_threeColoring hB hCD

/-- The complete `r`-uniform hypergraph on `Fin n`, with the canonical ordering
of every edge. -/
abbrev completeUniformHypergraph (n r : ℕ) : OrderedUniformHypergraph (Fin n) r where
  Edge := UniformEdge n r
  edgeFinite := inferInstance
  vertex := uniformEdgeVertex

/-- A sampled incidence graph embeds in the incidence graph of the complete
uniform hypergraph by forgetting the proof that an edge label was selected. -/
def sampledToCompleteIncidenceEmbedding {n r D C : ℕ}
    (ω : UniformEdge n r → Fin D) :
    (sampledHypergraph (C := C) ω).incidenceGraph ↪g
      (completeUniformHypergraph n r).incidenceGraph where
  toFun
    | .inl x => .inl x
    | .inr e => .inr e.1
  inj' := by
    intro u v huv
    cases u with
    | inl x => cases v <;> simp_all
    | inr e =>
        cases v with
        | inl y => simp at huv
        | inr f => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj huv))
  map_rel_iff' := by
    intro u v
    cases u with
    | inl x => cases v <;> rfl
    | inr e => cases v <;> rfl

/-- Send a bounded incidence cycle of the sampled hypergraph to the complete
hypergraph. -/
private def mapSampledShortCycle {n r D C K : ℕ}
    (ω : UniformEdge n r → Fin D)
    (Z : (sampledHypergraph (C := C) ω).ShortIncidenceCycle K) :
    (completeUniformHypergraph n r).ShortIncidenceCycle K := by
  let f := sampledToCompleteIncidenceEmbedding (C := C) ω
  let d₀ := Z.2.1.1.map f.toHom
  have hstart : f (Sum.inl Z.1) = Sum.inl Z.1 := rfl
  let d : (completeUniformHypergraph n r).incidenceGraph.Walk
      (.inl Z.1) (.inl Z.1) := d₀.copy hstart hstart
  refine ⟨Z.1, ⟨⟨d, ?_⟩, ?_⟩⟩
  · simpa [d, d₀] using Z.2.1.2
  · simpa [d, d₀] using Z.2.2.map f.injective

private theorem mem_incidenceCycleEdges_mapSampledShortCycle
    {n r D C K : ℕ} {ω : UniformEdge n r → Fin D}
    {Z : (sampledHypergraph (C := C) ω).ShortIncidenceCycle K}
    {e : (sampledHypergraph (C := C) ω).Edge}
    (he : e ∈ (sampledHypergraph (C := C) ω).incidenceCycleEdges Z) :
    (e.1 : UniformEdge n r) ∈
      (completeUniformHypergraph n r).incidenceCycleEdges
        (mapSampledShortCycle ω Z) := by
  apply (mem_incidenceCycleEdges (H := completeUniformHypergraph n r)
    (C := mapSampledShortCycle ω Z) (e := e.1)).mpr
  let f := sampledToCompleteIncidenceEmbedding (C := C) ω
  let d := Z.2.1.1.map f.toHom
  change Sum.inr e.1 ∈ d.support
  rw [SimpleGraph.Walk.support_map]
  exact List.mem_map.mpr
    ⟨Sum.inr e,
      (mem_incidenceCycleEdges (H := sampledHypergraph (C := C) ω)
        (C := Z) (e := e)).mp he, rfl⟩

/-- A complete-hypergraph short cycle is active when every hyperedge occurring
on it was retained by the label sample. -/
def ShortCycleActive {n r D C K : ℕ} (ω : UniformEdge n r → Fin D)
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) : Prop :=
  ∀ e ∈ (completeUniformHypergraph n r).incidenceCycleEdges Z, (ω e).val < C

private theorem mapSampledShortCycle_active {n r D C K : ℕ}
    (ω : UniformEdge n r → Fin D)
    (Z : (sampledHypergraph (C := C) ω).ShortIncidenceCycle K) :
    ShortCycleActive (C := C) ω (mapSampledShortCycle ω Z) := by
  classical
  intro e he
  let f := sampledToCompleteIncidenceEmbedding (C := C) ω
  let d := Z.2.1.1.map f.toHom
  have heSupport : Sum.inr e ∈
      (mapSampledShortCycle ω Z).2.1.1.support :=
    (mem_incidenceCycleEdges (H := completeUniformHypergraph n r)
      (C := mapSampledShortCycle ω Z) (e := e)).mp he
  change Sum.inr e ∈ d.support at heSupport
  rw [SimpleGraph.Walk.support_map] at heSupport
  obtain ⟨z', hz'Support, hz⟩ := List.mem_map.mp heSupport
  have hz' : f z' = Sum.inr e := hz
  cases z' with
  | inl x => simp [f, sampledToCompleteIncidenceEmbedding] at hz'
  | inr e' =>
      have heq : (e'.1 : (completeUniformHypergraph n r).Edge) = e :=
        Sum.inr.inj hz'
      subst e
      exact e'.2

/-- The finite universe of normalized short cycles in the complete uniform
hypergraph. -/
noncomputable def allCompleteShortCycles (n r K : ℕ) :
    Finset ((completeUniformHypergraph n r).ShortIncidenceCycle K) := by
  classical
  letI : Fintype (Fin n) := inferInstance
  letI : Fintype (completeUniformHypergraph n r).Edge := Fintype.ofFinite _
  exact Finset.univ

@[simp] private theorem mem_allCompleteShortCycles {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    Z ∈ allCompleteShortCycles n r K := by
  classical
  simp [allCompleteShortCycles]

/-- Active complete short cycles in a label sample. -/
noncomputable def activeShortCycles {n r D C : ℕ}
    (ω : UniformEdge n r → Fin D) (K : ℕ) :
    Finset ((completeUniformHypergraph n r).ShortIncidenceCycle K) := by
  classical
  exact (allCompleteShortCycles n r K).filter (ShortCycleActive (C := C) ω)

@[simp] private theorem mem_activeShortCycles {n r D C K : ℕ}
    {ω : UniformEdge n r → Fin D}
    {Z : (completeUniformHypergraph n r).ShortIncidenceCycle K} :
    Z ∈ activeShortCycles (C := C) ω K ↔ ShortCycleActive (C := C) ω Z := by
  classical
  simp [activeShortCycles]

/-- The sampled short-cycle edge set injects into the union of the edge sets
of active complete-hypergraph cycles. -/
private theorem shortCycleEdges_card_le_active_sum {n r D C K : ℕ}
    (ω : UniformEdge n r → Fin D) :
    ((sampledHypergraph (C := C) ω).shortCycleEdges K).card ≤
      ∑ Z ∈ activeShortCycles (C := C) ω K,
        ((completeUniformHypergraph n r).incidenceCycleEdges Z).card := by
  classical
  let mapped : Finset (completeUniformHypergraph n r).Edge :=
    ((sampledHypergraph (C := C) ω).shortCycleEdges K).image
      (fun e : (sampledHypergraph (C := C) ω).Edge ↦
        (e.1 : (completeUniformHypergraph n r).Edge))
  let activeUnion : Finset (completeUniformHypergraph n r).Edge :=
    (activeShortCycles (C := C) ω K).biUnion
      (fun Z ↦ (completeUniformHypergraph n r).incidenceCycleEdges Z)
  have hmappedCard : mapped.card =
      ((sampledHypergraph (C := C) ω).shortCycleEdges K).card := by
    dsimp only [mapped]
    rw [Finset.card_image_iff.mpr]
    intro e he f hf hef
    exact Subtype.ext hef
  have hsubset : mapped ⊆ activeUnion := by
    intro e he
    dsimp only [mapped] at he
    rw [Finset.mem_image] at he
    obtain ⟨e', he'Short, rfl⟩ := he
    obtain ⟨Z, he'Cycle⟩ :=
      (mem_shortCycleEdges (H := sampledHypergraph (C := C) ω)
        (K := K) (e := e')).mp he'Short
    let W := mapSampledShortCycle ω Z
    have hWActive : W ∈ activeShortCycles (C := C) ω K :=
      mem_activeShortCycles.mpr (mapSampledShortCycle_active ω Z)
    dsimp only [activeUnion]
    apply Finset.mem_biUnion.mpr
    exact ⟨W, hWActive,
      mem_incidenceCycleEdges_mapSampledShortCycle he'Cycle⟩
  have hactiveUnion : activeUnion.card ≤
      ∑ Z ∈ activeShortCycles (C := C) ω K,
        ((completeUniformHypergraph n r).incidenceCycleEdges Z).card := by
    dsimp only [activeUnion]
    exact Finset.card_biUnion_le
  calc
    ((sampledHypergraph (C := C) ω).shortCycleEdges K).card = mapped.card :=
      hmappedCard.symm
    _ ≤ activeUnion.card := Finset.card_le_card hsubset
    _ ≤ ∑ Z ∈ activeShortCycles (C := C) ω K,
        ((completeUniformHypergraph n r).incidenceCycleEdges Z).card := hactiveUnion

/-- A short incidence cycle contains fewer than `2K` hyperedge vertices.  We
only need the coarser weak bound, obtained by comparing its deduplicated
hyperedge support with the whole walk support. -/
private theorem incidenceCycleEdges_card_le_twice {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    ((completeUniformHypergraph n r).incidenceCycleEdges Z).card ≤ 2 * K := by
  classical
  let s := (completeUniformHypergraph n r).incidenceCycleEdges Z
  let t := Z.2.1.1.support.toFinset
  have himage : (s.image (fun e : UniformEdge n r ↦
      (Sum.inr e : Fin n ⊕ UniformEdge n r))).card = s.card := by
    rw [Finset.card_image_iff.mpr]
    intro e _ f _ hef
    exact Sum.inr.inj hef
  have hsub : s.image (fun e : UniformEdge n r ↦
      (Sum.inr e : Fin n ⊕ UniformEdge n r)) ⊆ t := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨e, he, rfl⟩ := hz
    rw [List.mem_toFinset]
    exact (mem_incidenceCycleEdges (H := completeUniformHypergraph n r)
      (C := Z) (e := e)).mp he
  have hcard : s.card ≤ Z.2.1.1.support.length := by
    rw [← himage]
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have hsupport : Z.2.1.1.support.length = Z.2.1.1.length + 1 :=
    Z.2.1.1.length_support
  have hlength := Z.2.1.2
  change s.card ≤ 2 * K
  omega

/-- Quantitative form of the active-cycle comparison: deleting every sampled
short-cycle edge costs at most `2K` edges per active complete cycle. -/
private theorem shortCycleEdges_card_le_twice_mul_active {n r D C K : ℕ}
    (ω : UniformEdge n r → Fin D) :
    ((sampledHypergraph (C := C) ω).shortCycleEdges K).card ≤
      2 * K * (activeShortCycles (C := C) ω K).card := by
  classical
  calc
    ((sampledHypergraph (C := C) ω).shortCycleEdges K).card ≤
        ∑ Z ∈ activeShortCycles (C := C) ω K,
          ((completeUniformHypergraph n r).incidenceCycleEdges Z).card :=
      shortCycleEdges_card_le_active_sum ω
    _ ≤ ∑ _Z ∈ activeShortCycles (C := C) ω K, 2 * K := by
      exact Finset.sum_le_sum fun Z _ ↦ incidenceCycleEdges_card_le_twice Z
    _ = 2 * K * (activeShortCycles (C := C) ω K).card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]

/-- Swap the two coordinates in the finite incidence relation saying that a
complete-hypergraph short cycle is active in a label sample. -/
private def activeCyclePairEquiv {n r D C K : ℕ} :
    (Σ ω : UniformEdge n r → Fin D,
      {Z : (completeUniformHypergraph n r).ShortIncidenceCycle K //
        ShortCycleActive (C := C) ω Z}) ≃
    (Σ Z : (completeUniformHypergraph n r).ShortIncidenceCycle K,
      {ω : UniformEdge n r → Fin D // ShortCycleActive (C := C) ω Z}) where
  toFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  invFun p := ⟨p.2.1, ⟨p.1, p.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact finite double count for active short cycles.  A fixed cycle is
active precisely when the labels on all hyperedges in its support are below
the threshold. -/
private theorem sum_card_activeShortCycles {n r D C K : ℕ} (hCD : C ≤ D) :
    ∑ ω : UniformEdge n r → Fin D,
        (activeShortCycles (C := C) ω K).card =
      ∑ Z ∈ allCompleteShortCycles n r K,
        C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) := by
  classical
  letI : Fintype ((completeUniformHypergraph n r).ShortIncidenceCycle K) :=
    Fintype.ofFinite _
  calc
    ∑ ω : UniformEdge n r → Fin D,
        (activeShortCycles (C := C) ω K).card =
        ∑ ω : UniformEdge n r → Fin D,
          Nat.card {Z : (completeUniformHypergraph n r).ShortIncidenceCycle K //
            ShortCycleActive (C := C) ω Z} := by
      apply Finset.sum_congr rfl
      intro ω _
      symm
      exact Nat.subtype_card (activeShortCycles (C := C) ω K)
        (fun _ ↦ mem_activeShortCycles)
    _ = Nat.card (Σ ω : UniformEdge n r → Fin D,
          {Z : (completeUniformHypergraph n r).ShortIncidenceCycle K //
            ShortCycleActive (C := C) ω Z}) := Nat.card_sigma.symm
    _ = Nat.card (Σ Z : (completeUniformHypergraph n r).ShortIncidenceCycle K,
          {ω : UniformEdge n r → Fin D // ShortCycleActive (C := C) ω Z}) :=
      Nat.card_congr activeCyclePairEquiv
    _ = ∑ Z : (completeUniformHypergraph n r).ShortIncidenceCycle K,
          Nat.card {ω : UniformEdge n r → Fin D //
            ShortCycleActive (C := C) ω Z} := Nat.card_sigma
    _ = ∑ Z : (completeUniformHypergraph n r).ShortIncidenceCycle K,
        C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) := by
      apply Finset.sum_congr rfl
      intro Z _
      simpa only [ShortCycleActive] using
        card_labelings_selecting_finset
          ((completeUniformHypergraph n r).incidenceCycleEdges Z) hCD
    _ = ∑ Z ∈ allCompleteShortCycles n r K,
        C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) := by
      have hall :
          (Finset.univ : Finset
            ((completeUniformHypergraph n r).ShortIncidenceCycle K)) =
            allCompleteShortCycles n r K := by
        ext Z
        simp
      rw [hall]

/-! ### Counting normalized incidence cycles -/

/-- The evident bipartite two-coloring of an incidence graph. -/
private def incidenceBicoloring : H.incidenceGraph.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun
    | .inl _ => false
    | .inr _ => true) (by
      intro u v huv
      cases u <;> cases v <;> simp [incidenceGraph, incidenceAdj] at huv ⊢)

private theorem incidenceWalk_getVert_even {u : X} {v : X ⊕ H.Edge}
    (p : H.incidenceGraph.Walk (.inl u) v) {i : ℕ} (hi : i ≤ p.length)
    (heven : Even i) : ∃ x : X, p.getVert i = .inl x := by
  have htake : (p.take i).length = i := by simp [hi]
  have hcongr := (H.incidenceBicoloring.even_length_iff_congr (p.take i)).mp
    (htake.symm ▸ heven)
  cases hget : p.getVert i with
  | inl x => exact ⟨x, rfl⟩
  | inr e =>
      rw [hget] at hcongr
      have hleft : H.incidenceBicoloring (Sum.inl u) = false := rfl
      have hright : H.incidenceBicoloring (Sum.inr e) = true := rfl
      rw [hleft, hright] at hcongr
      have : False := by simpa using hcongr
      exact this.elim

private theorem incidenceWalk_getVert_odd {u : X} {v : X ⊕ H.Edge}
    (p : H.incidenceGraph.Walk (.inl u) v) {i : ℕ} (hi : i ≤ p.length)
    (hodd : Odd i) : ∃ e : H.Edge, p.getVert i = .inr e := by
  have htake : (p.take i).length = i := by simp [hi]
  have hcongr := (H.incidenceBicoloring.odd_length_iff_not_congr (p.take i)).mp
    (htake.symm ▸ hodd)
  cases hget : p.getVert i with
  | inl x =>
      rw [hget] at hcongr
      have hleft : H.incidenceBicoloring (Sum.inl u) = false := rfl
      have hright : H.incidenceBicoloring (Sum.inl x) = false := rfl
      rw [hleft, hright] at hcongr
      have : False := by simpa using hcongr
      exact this.elim
  | inr e => exact ⟨e, rfl⟩

/-- A normalized complete-hypergraph incidence cycle of exactly `2s` graph
edges. -/
abbrev CompleteIncidenceCycle (n r s : ℕ) :=
  Σ x : Fin n,
    {p : (completeUniformHypergraph n r).incidenceGraph.Walk (.inl x) (.inl x) //
      p.length = 2 * s ∧ p.IsCycle}

private noncomputable def cycleFoundation {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) : Fin n :=
  Classical.choose (incidenceWalk_getVert_even (H := completeUniformHypergraph n r)
    Z.2.1 (show 2 * i.val ≤ Z.2.1.length by rw [Z.2.2.1]; omega)
    ⟨i.val, by omega⟩)

private theorem cycleFoundation_spec {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    Z.2.1.getVert (2 * i.val) = .inl (cycleFoundation Z i) :=
  Classical.choose_spec (incidenceWalk_getVert_even
    (H := completeUniformHypergraph n r) Z.2.1
    (show 2 * i.val ≤ Z.2.1.length by rw [Z.2.2.1]; omega)
    ⟨i.val, by omega⟩)

private noncomputable def cycleEdge {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) : UniformEdge n r :=
  Classical.choose (incidenceWalk_getVert_odd (H := completeUniformHypergraph n r)
    Z.2.1 (show 2 * i.val + 1 ≤ Z.2.1.length by rw [Z.2.2.1]; omega)
    ⟨i.val, by omega⟩)

private theorem cycleEdge_spec {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    Z.2.1.getVert (2 * i.val + 1) = .inr (cycleEdge Z i) :=
  Classical.choose_spec (incidenceWalk_getVert_odd
    (H := completeUniformHypergraph n r) Z.2.1
    (show 2 * i.val + 1 ≤ Z.2.1.length by rw [Z.2.2.1]; omega)
    ⟨i.val, by omega⟩)

private def cycleSucc {s : ℕ} (hs : 0 < s) (i : Fin s) : Fin s :=
  if h : i.val + 1 < s then ⟨i.val + 1, h⟩ else ⟨0, hs⟩

private theorem cycleFoundation_succ_spec {n r s : ℕ} (hs : 0 < s)
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    Z.2.1.getVert (2 * i.val + 2) =
      .inl (cycleFoundation Z (cycleSucc hs i)) := by
  by_cases hnext : i.val + 1 < s
  · have hsucc : cycleSucc hs i = ⟨i.val + 1, hnext⟩ := by simp [cycleSucc, hnext]
    have hidx : 2 * i.val + 2 = 2 * (i.val + 1) := by omega
    rw [hsucc, hidx]
    exact cycleFoundation_spec Z ⟨i.val + 1, hnext⟩
  · have hilast : i.val + 1 = s := by omega
    have hsucc : cycleSucc hs i = ⟨0, hs⟩ := by simp [cycleSucc, hnext]
    have hidx : 2 * i.val + 2 = 2 * s := by omega
    rw [hsucc, hidx]
    calc
      Z.2.1.getVert (2 * s) = Z.2.1.getVert Z.2.1.length := by
        rw [Z.2.2.1]
      _ = Sum.inl Z.1 := SimpleGraph.Walk.getVert_length _
      _ = Z.2.1.getVert 0 := by rw [SimpleGraph.Walk.getVert_zero]
      _ = Sum.inl (cycleFoundation Z ⟨0, hs⟩) :=
        cycleFoundation_spec Z ⟨0, hs⟩

private theorem completeUniform_incident_iff {n r : ℕ} {x : Fin n}
    {e : UniformEdge n r} :
    (completeUniformHypergraph n r).Incident x e ↔ x ∈ e.1 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem e.1 e.2 i
  · intro hx
    have hxRange : x ∈ Set.range (uniformEdgeVertex e) := by
      rw [show Set.range (uniformEdgeVertex e) = (e.1 : Set (Fin n)) by
        exact Finset.range_orderEmbOfFin e.1 e.2]
      exact hx
    obtain ⟨i, hi⟩ := hxRange
    exact ⟨i, hi⟩

private theorem cycleFoundation_mem_edge {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    cycleFoundation Z i ∈ (cycleEdge Z i).1 := by
  have hadj := Z.2.1.adj_getVert_succ
    (i := 2 * i.val) (show 2 * i.val < Z.2.1.length by rw [Z.2.2.1]; omega)
  rw [cycleFoundation_spec, cycleEdge_spec] at hadj
  exact completeUniform_incident_iff.mp hadj

private theorem cycleFoundation_succ_mem_edge {n r s : ℕ} (hs : 0 < s)
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    cycleFoundation Z (cycleSucc hs i) ∈ (cycleEdge Z i).1 := by
  have hadj := Z.2.1.adj_getVert_succ
    (i := 2 * i.val + 1)
    (show 2 * i.val + 1 < Z.2.1.length by rw [Z.2.2.1]; omega)
  rw [cycleEdge_spec, cycleFoundation_succ_spec hs] at hadj
  exact completeUniform_incident_iff.mp hadj

private theorem cycleFoundation_ne_succ {n r s : ℕ} (hs : 0 < s)
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    cycleFoundation Z i ≠ cycleFoundation Z (cycleSucc hs i) := by
  have hne := Z.2.2.2.getVert_sub_one_ne_getVert_add_one
    (i := 2 * i.val + 1) (show 2 * i.val + 1 ≤ Z.2.1.length by
      rw [Z.2.2.1]
      omega)
  have hsub : 2 * i.val + 1 - 1 = 2 * i.val := by omega
  have hadd : 2 * i.val + 1 + 1 = 2 * i.val + 2 := by omega
  rw [hsub, hadd, cycleFoundation_spec, cycleFoundation_succ_spec hs] at hne
  exact fun h ↦ hne (congrArg Sum.inl h)

/-- The `r-2` vertices of a cycle hyperedge other than its two consecutive
foundation vertices. -/
private noncomputable def cycleRemainder {n r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s)
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) : UniformEdge n (r - 2) := by
  let x := cycleFoundation Z i
  let y := cycleFoundation Z (cycleSucc hs i)
  let e := cycleEdge Z i
  refine ⟨(e.1.erase x).erase y, ?_⟩
  have hx : x ∈ e.1 := cycleFoundation_mem_edge Z i
  have hy : y ∈ e.1 := cycleFoundation_succ_mem_edge hs Z i
  have hne : x ≠ y := cycleFoundation_ne_succ hs Z i
  have hyErase : y ∈ e.1.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  rw [Finset.card_erase_of_mem hyErase, Finset.card_erase_of_mem hx, e.2]
  omega

private theorem cycleEdge_reconstruct {n r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s)
    (Z : CompleteIncidenceCycle n r s) (i : Fin s) :
    (cycleEdge Z i).1 =
      insert (cycleFoundation Z i)
        (insert (cycleFoundation Z (cycleSucc hs i))
          (cycleRemainder hr hs Z i).1) := by
  let x := cycleFoundation Z i
  let y := cycleFoundation Z (cycleSucc hs i)
  let e := cycleEdge Z i
  have hx : x ∈ e.1 := cycleFoundation_mem_edge Z i
  have hy : y ∈ e.1 := cycleFoundation_succ_mem_edge hs Z i
  have hne : x ≠ y := cycleFoundation_ne_succ hs Z i
  have hyErase : y ∈ e.1.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  change e.1 = insert x (insert y ((e.1.erase x).erase y))
  rw [Finset.insert_erase hyErase, Finset.insert_erase hx]

private noncomputable def cycleCode {n r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s) :
    CompleteIncidenceCycle n r s →
      ((Fin s → Fin n) × (Fin s → UniformEdge n (r - 2))) :=
  fun Z ↦ (cycleFoundation Z, cycleRemainder hr hs Z)

private theorem cycleEdge_eq_of_code_eq {n r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s)
    {Z W : CompleteIncidenceCycle n r s}
    (hcode : cycleCode hr hs Z = cycleCode hr hs W) (i : Fin s) :
    cycleEdge Z i = cycleEdge W i := by
  have hfoundation : cycleFoundation Z = cycleFoundation W :=
    congrArg Prod.fst hcode
  have hremainder : cycleRemainder hr hs Z = cycleRemainder hr hs W :=
    congrArg Prod.snd hcode
  apply Subtype.ext
  rw [cycleEdge_reconstruct hr hs Z i, cycleEdge_reconstruct hr hs W i,
    congrFun hfoundation i,
    congrFun hfoundation (cycleSucc hs i),
    congrArg Subtype.val (congrFun hremainder i)]

private theorem cycleCode_injective {n r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    Function.Injective (cycleCode (n := n) hr (by omega : 0 < s)) := by
  intro Z W hcode
  let hs0 : 0 < s := by omega
  have hfoundation : cycleFoundation Z = cycleFoundation W :=
    congrArg Prod.fst hcode
  let i0 : Fin s := ⟨0, hs0⟩
  have hZ0 : Z.1 = cycleFoundation Z i0 := by
    apply Sum.inl.inj (β := UniformEdge n r)
    simpa [i0] using cycleFoundation_spec Z i0
  have hW0 : W.1 = cycleFoundation W i0 := by
    apply Sum.inl.inj (β := UniformEdge n r)
    simpa [i0] using cycleFoundation_spec W i0
  have hbase : Z.1 = W.1 :=
    hZ0.trans ((congrFun hfoundation i0).trans hW0.symm)
  rcases Z with ⟨x, ⟨p, hpLength, hpCycle⟩⟩
  rcases W with ⟨y, ⟨q, hqLength, hqCycle⟩⟩
  dsimp only at hbase
  subst y
  suffices hpq : p = q by subst q; rfl
  apply SimpleGraph.Walk.ext_getVert_le_length (hpLength.trans hqLength.symm)
  intro k hk
  by_cases heven : Even k
  · obtain ⟨j, hj⟩ := heven
    have hkform : k = 2 * j := by omega
    by_cases hend : k = 2 * s
    · have hpEnd : k = p.length := hend.trans hpLength.symm
      have hqEnd : k = q.length := hend.trans hqLength.symm
      calc
        p.getVert k = Sum.inl x := by rw [hpEnd, SimpleGraph.Walk.getVert_length]
        _ = q.getVert k := by rw [hqEnd, SimpleGraph.Walk.getVert_length]
    · have hjlt : j < s := by omega
      let i : Fin s := ⟨j, hjlt⟩
      calc
        p.getVert k = Sum.inl (cycleFoundation ⟨x, ⟨p, hpLength, hpCycle⟩⟩ i) := by
          rw [hkform]
          simpa [i] using
            (cycleFoundation_spec (⟨x, ⟨p, hpLength, hpCycle⟩⟩ :
              CompleteIncidenceCycle n r s) i)
        _ = Sum.inl (cycleFoundation ⟨x, ⟨q, hqLength, hqCycle⟩⟩ i) :=
          congrArg Sum.inl (congrFun hfoundation i)
        _ = q.getVert k := by
          rw [hkform]
          simpa [i] using
            (cycleFoundation_spec (⟨x, ⟨q, hqLength, hqCycle⟩⟩ :
              CompleteIncidenceCycle n r s) i).symm
  · have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    obtain ⟨j, hj⟩ := hodd
    have hkform : k = 2 * j + 1 := by omega
    have hjlt : j < s := by omega
    let i : Fin s := ⟨j, hjlt⟩
    have hedge :
        cycleEdge (⟨x, ⟨p, hpLength, hpCycle⟩⟩ : CompleteIncidenceCycle n r s) i =
          cycleEdge (⟨x, ⟨q, hqLength, hqCycle⟩⟩ : CompleteIncidenceCycle n r s) i :=
      cycleEdge_eq_of_code_eq hr hs0 hcode i
    calc
      p.getVert k = Sum.inr (cycleEdge ⟨x, ⟨p, hpLength, hpCycle⟩⟩ i) := by
        rw [hkform]
        simpa [i] using
          (cycleEdge_spec (⟨x, ⟨p, hpLength, hpCycle⟩⟩ :
            CompleteIncidenceCycle n r s) i)
      _ = Sum.inr (cycleEdge ⟨x, ⟨q, hqLength, hqCycle⟩⟩ i) :=
        congrArg Sum.inr hedge
      _ = q.getVert k := by
        rw [hkform]
        simpa [i] using
          (cycleEdge_spec (⟨x, ⟨q, hqLength, hqCycle⟩⟩ :
            CompleteIncidenceCycle n r s) i).symm

private theorem card_uniformEdge (n r : ℕ) :
    Fintype.card (UniformEdge n r) = Nat.choose n r := by
  calc
    Fintype.card (UniformEdge n r) = Nat.card (UniformEdge n r) :=
      Fintype.card_eq_nat_card
    _ = (Finset.univ.powersetCard r : Finset (Finset (Fin n))).card := by
      apply Nat.subtype_card
      intro e
      simp
    _ = Nat.choose n r := by simp

/-- Sharp enough cycle count: after its `s` foundation vertices are chosen,
each hyperedge is determined by the remaining `r-2` vertices. -/
private theorem card_completeIncidenceCycle_le {n r s : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) :
    Nat.card (CompleteIncidenceCycle n r s) ≤
      n ^ s * (Nat.choose n (r - 2)) ^ s := by
  calc
    Nat.card (CompleteIncidenceCycle n r s) ≤
        Nat.card ((Fin s → Fin n) × (Fin s → UniformEdge n (r - 2))) :=
      Nat.card_le_card_of_injective (cycleCode (n := n) hr (by omega))
        (cycleCode_injective hr hs)
    _ = n ^ s * (Nat.choose n (r - 2)) ^ s := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin,
        Nat.card_eq_fintype_card, card_uniformEdge]

private theorem card_completeIncidenceCycle_le_all {n r s : ℕ} (hr : 2 ≤ r) :
    Nat.card (CompleteIncidenceCycle n r s) ≤
      n ^ s * (Nat.choose n (r - 2)) ^ s := by
  by_cases hs : 2 ≤ s
  · exact card_completeIncidenceCycle_le hr hs
  · letI : IsEmpty (CompleteIncidenceCycle n r s) := ⟨fun Z ↦ by
      have hthree := Z.2.2.2.three_le_length
      rw [Z.2.2.1] at hthree
      omega⟩
    simp

private noncomputable def fixedCycleEdges {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) : Finset (UniformEdge n r) := by
  classical
  exact Finset.univ.image (cycleEdge Z)

private theorem cycleEdge_injective {n r s : ℕ} (Z : CompleteIncidenceCycle n r s) :
    Function.Injective (cycleEdge Z) := by
  intro i j hij
  have hget : Z.2.1.getVert (2 * i.val + 1) =
      Z.2.1.getVert (2 * j.val + 1) := by
    rw [cycleEdge_spec, cycleEdge_spec, hij]
  have hindex := Z.2.2.2.getVert_injOn
    (show 1 ≤ 2 * i.val + 1 ∧ 2 * i.val + 1 ≤ Z.2.1.length by
      rw [Z.2.2.1]
      omega)
    (show 1 ≤ 2 * j.val + 1 ∧ 2 * j.val + 1 ≤ Z.2.1.length by
      rw [Z.2.2.1]
      omega) hget
  apply Fin.ext
  omega

private theorem card_fixedCycleEdges {n r s : ℕ} (Z : CompleteIncidenceCycle n r s) :
    (fixedCycleEdges Z).card = s := by
  classical
  rw [fixedCycleEdges, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact cycleEdge_injective Z hij

private def fixedCycleToShort {n r s K : ℕ} (hsK : s < K)
    (Z : CompleteIncidenceCycle n r s) :
    (completeUniformHypergraph n r).ShortIncidenceCycle K :=
  ⟨Z.1, ⟨⟨Z.2.1, by rw [Z.2.2.1]; omega⟩, Z.2.2.2⟩⟩

private theorem fixedCycleToShort_injective {n r s K : ℕ} (hsK : s < K) :
    Function.Injective (fixedCycleToShort (n := n) (r := r) hsK) := by
  intro Z W hZW
  rcases Z with ⟨x, ⟨p, hp⟩⟩
  rcases W with ⟨y, ⟨q, hq⟩⟩
  have hxy : x = y := congrArg Sigma.fst hZW
  subst y
  have hsupp : p.support = q.support := congrArg
    (fun Z : (completeUniformHypergraph n r).ShortIncidenceCycle K ↦ Z.2.1.1.support) hZW
  have hpq : p = q := SimpleGraph.Walk.support_injective hsupp
  subst q
  rfl

private noncomputable def allCompleteIncidenceCycles (n r s : ℕ) :
    Finset (CompleteIncidenceCycle n r s) := by
  classical
  letI : Finite (CompleteIncidenceCycle n r s) :=
    Finite.of_injective (fixedCycleToShort (n := n) (r := r) (Nat.lt_succ_self s))
      (fixedCycleToShort_injective (Nat.lt_succ_self s))
  exact Set.Finite.toFinset Set.finite_univ

@[simp] private theorem mem_allCompleteIncidenceCycles {n r s : ℕ}
    (Z : CompleteIncidenceCycle n r s) :
    Z ∈ allCompleteIncidenceCycles n r s := by
  classical
  simp [allCompleteIncidenceCycles]

private theorem incidenceCycleEdges_fixedCycleToShort {n r s K : ℕ}
    (hsK : s < K) (Z : CompleteIncidenceCycle n r s) :
    (completeUniformHypergraph n r).incidenceCycleEdges
      (fixedCycleToShort hsK Z) = fixedCycleEdges Z := by
  classical
  ext e
  constructor
  · intro he
    have hsupp : Sum.inr e ∈ Z.2.1.support :=
      (mem_incidenceCycleEdges (H := completeUniformHypergraph n r)
        (C := fixedCycleToShort hsK Z) (e := e)).mp he
    obtain ⟨k, hget, hk⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hsupp
    rcases k.even_or_odd with heven | hodd
    · obtain ⟨x, hx⟩ := incidenceWalk_getVert_even
        (H := completeUniformHypergraph n r) Z.2.1 hk heven
      rw [hget] at hx
      simp at hx
    · obtain ⟨j, hj⟩ := hodd
      have hkform : k = 2 * j + 1 := by omega
      have hjlt : j < s := by rw [Z.2.2.1] at hk; omega
      let i : Fin s := ⟨j, hjlt⟩
      have hie : cycleEdge Z i = e := by
        apply Sum.inr.inj
        rw [← hget, hkform]
        simpa [i] using (cycleEdge_spec Z i).symm
      rw [fixedCycleEdges, Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, hie⟩
  · intro he
    rw [fixedCycleEdges, Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    apply (mem_incidenceCycleEdges (H := completeUniformHypergraph n r)
      (C := fixedCycleToShort hsK Z) (e := cycleEdge Z i)).mpr
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    refine ⟨2 * i.val + 1, cycleEdge_spec Z i, ?_⟩
    change 2 * i.val + 1 ≤ Z.2.1.length
    rw [Z.2.2.1]
    omega

private theorem card_incidenceCycleEdges_fixed {n r s K : ℕ}
    (hsK : s < K) (Z : CompleteIncidenceCycle n r s) :
    ((completeUniformHypergraph n r).incidenceCycleEdges
      (fixedCycleToShort hsK Z)).card = s := by
  rw [incidenceCycleEdges_fixedCycleToShort hsK Z, card_fixedCycleEdges]

private theorem shortIncidenceCycle_length_even {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    Even Z.2.1.1.length := by
  exact ((completeUniformHypergraph n r).incidenceBicoloring.even_length_iff_congr
    Z.2.1.1).mpr Iff.rfl

private noncomputable def shortCycleHalfLength {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) : ℕ :=
  Classical.choose (shortIncidenceCycle_length_even Z)

private theorem shortCycleHalfLength_spec {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    Z.2.1.1.length = 2 * shortCycleHalfLength Z := by
  have h := Classical.choose_spec (shortIncidenceCycle_length_even Z)
  unfold shortCycleHalfLength
  omega

private theorem shortCycleHalfLength_lt {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    shortCycleHalfLength Z < K := by
  have hlength := Z.2.1.2
  rw [shortCycleHalfLength_spec Z] at hlength
  omega

private def shortCycleToFixed {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    CompleteIncidenceCycle n r (shortCycleHalfLength Z) :=
  ⟨Z.1, ⟨Z.2.1.1, shortCycleHalfLength_spec Z, Z.2.2⟩⟩

/-- Place a normalized short cycle into the fiber indexed by half its even
length. -/
private noncomputable def shortCycleToSigma {n r K : ℕ} :
    (completeUniformHypergraph n r).ShortIncidenceCycle K →
      Σ s : Fin K, CompleteIncidenceCycle n r s.val :=
  fun Z ↦ ⟨⟨shortCycleHalfLength Z, shortCycleHalfLength_lt Z⟩,
    shortCycleToFixed Z⟩

private theorem shortCycleToSigma_injective {n r K : ℕ} :
    Function.Injective (shortCycleToSigma (n := n) (r := r) (K := K)) := by
  intro Z W hZW
  have h := congrArg (fun p : Σ s : Fin K, CompleteIncidenceCycle n r s.val ↦
    fixedCycleToShort p.1.2 p.2) hZW
  rcases Z with ⟨x, ⟨⟨p, hp⟩, hcycle⟩⟩
  rcases W with ⟨y, ⟨⟨q, hq⟩, hcycle'⟩⟩
  exact h

private theorem card_incidenceCycleEdges_eq_halfLength {n r K : ℕ}
    (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
    ((completeUniformHypergraph n r).incidenceCycleEdges Z).card =
      shortCycleHalfLength Z := by
  have hleft : fixedCycleToShort (shortCycleHalfLength_lt Z) (shortCycleToFixed Z) = Z := by
    rcases Z with ⟨x, ⟨⟨p, hp⟩, hcycle⟩⟩
    rfl
  have hcard := card_incidenceCycleEdges_fixed
    (shortCycleHalfLength_lt Z) (shortCycleToFixed Z)
  rw [hleft] at hcard
  exact hcard

/-- The weighted number of normalized short cycles is bounded by summing the
sharp cycle-code estimate over their possible half-lengths. -/
private theorem weighted_shortCycles_le {n r C D K : ℕ} (hr : 2 ≤ r) :
    ∑ Z ∈ allCompleteShortCycles n r K,
        C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) ≤
      ∑ s : Fin K,
        (n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
          (C ^ s.val *
            D ^ (Fintype.card (UniformEdge n r) - s.val)) := by
  classical
  let source := allCompleteShortCycles n r K
  let target : Finset (Σ s : Fin K, CompleteIncidenceCycle n r s.val) :=
    Finset.univ.sigma fun s ↦ allCompleteIncidenceCycles n r s.val
  let f := shortCycleToSigma (n := n) (r := r) (K := K)
  let weight : (Σ s : Fin K, CompleteIncidenceCycle n r s.val) → ℕ := fun p ↦
    C ^ p.1.val * D ^ (Fintype.card (UniformEdge n r) - p.1.val)
  have hweight (Z : (completeUniformHypergraph n r).ShortIncidenceCycle K) :
      C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) =
        weight (f Z) := by
    rw [card_incidenceCycleEdges_eq_halfLength]
    rfl
  have himage : source.image f ⊆ target := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨Z, hZ, rfl⟩ := hp
    simp [target]
  calc
    ∑ Z ∈ allCompleteShortCycles n r K,
        C ^ ((completeUniformHypergraph n r).incidenceCycleEdges Z).card *
          D ^ (Fintype.card (UniformEdge n r) -
            ((completeUniformHypergraph n r).incidenceCycleEdges Z).card) =
        ∑ Z ∈ source, weight (f Z) := by
      apply Finset.sum_congr rfl
      intro Z _
      exact hweight Z
    _ = ∑ p ∈ source.image f, weight p := by
      rw [Finset.sum_image]
      intro Z _ W _ hZW
      exact shortCycleToSigma_injective hZW
    _ ≤ ∑ p ∈ target, weight p := Finset.sum_le_sum_of_subset himage
    _ = ∑ s : Fin K, ∑ _Z ∈ allCompleteIncidenceCycles n r s.val,
          C ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val) := by
      dsimp only [target]
      rw [Finset.sum_sigma]
    _ = ∑ s : Fin K,
          Nat.card (CompleteIncidenceCycle n r s.val) *
            (C ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val)) := by
      apply Finset.sum_congr rfl
      intro s _
      letI : Finite (CompleteIncidenceCycle n r s.val) :=
        Finite.of_injective
          (fixedCycleToShort (n := n) (r := r) (Nat.lt_succ_self s.val))
          (fixedCycleToShort_injective (Nat.lt_succ_self s.val))
      letI : Fintype (CompleteIncidenceCycle n r s.val) := Fintype.ofFinite _
      have hAllCard : (allCompleteIncidenceCycles n r s.val).card =
          Nat.card (CompleteIncidenceCycle n r s.val) := by
        calc
          (allCompleteIncidenceCycles n r s.val).card =
              Fintype.card (CompleteIncidenceCycle n r s.val) := by
            have hall : allCompleteIncidenceCycles n r s.val = Finset.univ := by
              ext Z
              simp
            rw [hall, Finset.card_univ]
          _ = Nat.card (CompleteIncidenceCycle n r s.val) :=
            Fintype.card_eq_nat_card
      rw [Finset.sum_const, Nat.nsmul_eq_mul, hAllCard]
    _ ≤ ∑ s : Fin K,
        (n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
          (C ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val)) := by
      exact Finset.sum_le_sum fun s _ ↦ Nat.mul_le_mul_right _
        (card_completeIncidenceCycle_le_all hr)

private theorem sum_card_activeShortCycles_le {n r D C K : ℕ}
    (hr : 2 ≤ r) (hCD : C ≤ D) :
    ∑ ω : UniformEdge n r → Fin D,
        (activeShortCycles (C := C) ω K).card ≤
      ∑ s : Fin K,
        (n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
          (C ^ s.val *
            D ^ (Fintype.card (UniformEdge n r) - s.val)) := by
  rw [sum_card_activeShortCycles hCD]
  exact weighted_shortCycles_le hr

private theorem sampled_cycle_sum_le_geometric {n r C K : ℕ} (hr : 2 ≤ r)
    (hC : C ≤ n ^ (r - 1)) (hK : K ≤ Nat.choose n r) :
    ∑ ω : UniformEdge n r → Fin (n ^ (r - 1)),
        (activeShortCycles (C := C) ω K).card ≤
      (∑ s : Fin K, C ^ s.val) *
        (n ^ (r - 1)) ^ Fintype.card (UniformEdge n r) := by
  let D := n ^ (r - 1)
  calc
    ∑ ω : UniformEdge n r → Fin D,
        (activeShortCycles (C := C) ω K).card ≤
      ∑ s : Fin K,
        (n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
          (C ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val)) :=
      sum_card_activeShortCycles_le hr hC
    _ ≤ ∑ s : Fin K, C ^ s.val * D ^ Fintype.card (UniformEdge n r) := by
      apply Finset.sum_le_sum
      intro s _
      have hchoose : Nat.choose n (r - 2) ≤ n ^ (r - 2) :=
        Nat.choose_le_pow n (r - 2)
      have hbase : n * Nat.choose n (r - 2) ≤ D := by
        calc
          n * Nat.choose n (r - 2) ≤ n * n ^ (r - 2) :=
            Nat.mul_le_mul_left n hchoose
          _ = n ^ (r - 1) := by
            rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
            ac_rfl
      have hpow : n ^ s.val * (Nat.choose n (r - 2)) ^ s.val ≤ D ^ s.val := by
        rw [← mul_pow]
        exact Nat.pow_le_pow_left hbase s.val
      have hsE : s.val ≤ Fintype.card (UniformEdge n r) := by
        rw [card_uniformEdge]
        exact s.isLt.le.trans hK
      calc
        (n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
            (C ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val)) =
          C ^ s.val *
            ((n ^ s.val * (Nat.choose n (r - 2)) ^ s.val) *
              D ^ (Fintype.card (UniformEdge n r) - s.val)) := by ac_rfl
        _ ≤ C ^ s.val *
            (D ^ s.val * D ^ (Fintype.card (UniformEdge n r) - s.val)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
        _ = C ^ s.val * D ^ Fintype.card (UniformEdge n r) := by
          rw [← pow_add, Nat.add_sub_of_le hsE]
    _ = (∑ s : Fin K, C ^ s.val) * D ^ Fintype.card (UniformEdge n r) := by
      rw [Finset.sum_mul]

private noncomputable def cycleHeavyLabelings (n r C K : ℕ) :
    Finset (UniformEdge n r → Fin (n ^ (r - 1))) := by
  classical
  exact Finset.univ.filter fun ω ↦
    2 * (∑ s : Fin K, C ^ s.val) < (activeShortCycles (C := C) ω K).card

@[simp] private theorem mem_cycleHeavyLabelings {n r C K : ℕ}
    {ω : UniformEdge n r → Fin (n ^ (r - 1))} :
    ω ∈ cycleHeavyLabelings n r C K ↔
      2 * (∑ s : Fin K, C ^ s.val) <
        (activeShortCycles (C := C) ω K).card := by
  classical
  simp [cycleHeavyLabelings]

/-- Finite Markov inequality specialized to the active-cycle count. -/
private theorem twice_card_cycleHeavyLabelings_le {n r C K : ℕ} (hr : 2 ≤ r)
    (hC : C ≤ n ^ (r - 1)) (hK : K ≤ Nat.choose n r) :
    2 * (cycleHeavyLabelings n r C K).card ≤
      (n ^ (r - 1)) ^ Fintype.card (UniformEdge n r) := by
  classical
  let S := ∑ s : Fin K, C ^ s.val
  let D := n ^ (r - 1)
  let bad := cycleHeavyLabelings n r C K
  have hlower : (2 * S + 1) * bad.card ≤
      ∑ ω : UniformEdge n r → Fin D,
        (activeShortCycles (C := C) ω K).card := by
    calc
      (2 * S + 1) * bad.card = ∑ _ω ∈ bad, (2 * S + 1) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ω ∈ bad, (activeShortCycles (C := C) ω K).card := by
        apply Finset.sum_le_sum
        intro ω hω
        have := (mem_cycleHeavyLabelings (ω := ω)).mp hω
        change 2 * S < (activeShortCycles (C := C) ω K).card at this
        omega
      _ ≤ ∑ ω : UniformEdge n r → Fin D,
          (activeShortCycles (C := C) ω K).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
  have hupper :
      ∑ ω : UniformEdge n r → Fin D,
          (activeShortCycles (C := C) ω K).card ≤
        S * D ^ Fintype.card (UniformEdge n r) :=
    sampled_cycle_sum_le_geometric hr hC hK
  have hmaster : (2 * S + 1) * bad.card ≤
      S * D ^ Fintype.card (UniformEdge n r) := hlower.trans hupper
  change 2 * bad.card ≤ D ^ Fintype.card (UniformEdge n r)
  by_cases hS : S = 0
  · rw [hS] at hmaster
    simp only [zero_mul, zero_add, one_mul] at hmaster
    omega
  · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
    apply Nat.le_of_mul_le_mul_left (c := S) ?_ hSpos
    calc
      S * (2 * bad.card) = (2 * S) * bad.card := by ac_rfl
      _ ≤ (2 * S + 1) * bad.card :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ S * D ^ Fintype.card (UniformEdge n r) := hmaster

private theorem eventually_color_tail_exponential (a : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * (3 : ℝ) ^ n * (n : ℝ) ^ a * Real.exp (-3 * (n : ℝ)) < 1 := by
  have htend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ a * Real.exp (-(n : ℝ)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero a |>.comp
      tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ a * Real.exp (-(n : ℝ)) < (1 / 2 : ℝ) :=
    (tendsto_order.1 htend).2 (1 / 2 : ℝ) (by norm_num)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    have he := Real.exp_one_gt_two
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [hexp2]
    nlinarith
  filter_upwards [hsmall] with n hn
  have hpow : (3 : ℝ) ^ n ≤ (Real.exp 2) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hthree n
  have hexp : (Real.exp 2) ^ n * Real.exp (-3 * (n : ℝ)) =
      Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    2 * (3 : ℝ) ^ n * (n : ℝ) ^ a * Real.exp (-3 * (n : ℝ)) ≤
        2 * (Real.exp 2) ^ n * (n : ℝ) ^ a * Real.exp (-3 * (n : ℝ)) := by
      gcongr
    _ = 2 * ((n : ℝ) ^ a * Real.exp (-(n : ℝ))) := by
      calc
        2 * (Real.exp 2) ^ n * (n : ℝ) ^ a * Real.exp (-3 * (n : ℝ)) =
            2 * (n : ℝ) ^ a *
              ((Real.exp 2) ^ n * Real.exp (-3 * (n : ℝ))) := by ring
        _ = 2 * ((n : ℝ) ^ a * Real.exp (-(n : ℝ))) := by rw [hexp]; ring
    _ < 1 := by linarith

private theorem color_tail_core_bound {n r B C D Q L : ℕ}
    (hD : 0 < D) (hCD : C ≤ D) (hQ : Q ≤ n ^ r)
    (hCL : 3 * n * D ≤ C * L)
    (hexp : 2 * (3 : ℝ) ^ n * (n : ℝ) ^ (r * B) *
      Real.exp (-3 * (n : ℝ)) < 1) :
    2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L < D ^ L := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDreal
  have hbase : ((D - C : ℕ) : ℝ) / (D : ℝ) ≤
      Real.exp (-((C : ℝ) / (D : ℝ))) := by
    rw [Nat.cast_sub hCD]
    convert Real.one_sub_le_exp_neg ((C : ℝ) / (D : ℝ)) using 1 <;>
      field_simp
  have hratioPow : (((D - C : ℕ) : ℝ) / (D : ℝ)) ^ L ≤
      (Real.exp (-((C : ℝ) / (D : ℝ)))) ^ L := by
    exact pow_le_pow_left₀ (by positivity) hbase L
  have hCLreal : 3 * (n : ℝ) ≤ (C : ℝ) * (L : ℝ) / (D : ℝ) := by
    rw [le_div_iff₀ hDreal]
    exact_mod_cast hCL
  have hexpMono : (Real.exp (-((C : ℝ) / (D : ℝ)))) ^ L ≤
      Real.exp (-3 * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    calc
      (L : ℝ) * -((C : ℝ) / (D : ℝ)) =
          -((C : ℝ) * (L : ℝ) / (D : ℝ)) := by ring
      _ ≤ -(3 * (n : ℝ)) := neg_le_neg hCLreal
      _ = -3 * (n : ℝ) := by ring
  have hratio : (((D - C : ℕ) : ℝ) / (D : ℝ)) ^ L ≤
      Real.exp (-3 * (n : ℝ)) := hratioPow.trans hexpMono
  have hchoose : Nat.choose Q B ≤ n ^ (r * B) := by
    calc
      Nat.choose Q B ≤ Q ^ B := Nat.choose_le_pow Q B
      _ ≤ (n ^ r) ^ B := Nat.pow_le_pow_left hQ B
      _ = n ^ (r * B) := by rw [pow_mul]
  have hidentity :
      ((2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L : ℕ) : ℝ) /
          (D : ℝ) ^ L =
        2 * (3 : ℝ) ^ n * (Nat.choose Q B : ℝ) *
          (((D - C : ℕ) : ℝ) / (D : ℝ)) ^ L := by
    push_cast [Nat.cast_sub hCD]
    rw [div_pow]
    ring
  have hdiv :
      ((2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L : ℕ) : ℝ) /
          (D : ℝ) ^ L < 1 := by
    rw [hidentity]
    calc
      2 * (3 : ℝ) ^ n * (Nat.choose Q B : ℝ) *
          (((D - C : ℕ) : ℝ) / (D : ℝ)) ^ L ≤
        2 * (3 : ℝ) ^ n * (n : ℝ) ^ (r * B) *
          Real.exp (-3 * (n : ℝ)) := by
        have hchooseReal : (Nat.choose Q B : ℝ) ≤ (n : ℝ) ^ (r * B) := by
          exact_mod_cast hchoose
        gcongr
      _ < 1 := hexp
  have hreal :
      ((2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L : ℕ) : ℝ) <
        (D ^ L : ℕ) := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (D : ℝ) ^ L)] at hdiv
    exact_mod_cast hdiv
  exact_mod_cast hreal

/-- The lower-tail union bound is strictly less than half of the finite
label-function space once its exponential core is less than one. -/
private theorem twice_card_colorBadLabelings_lt {n r B C D : ℕ}
    (hD : 0 < D) (hCD : C ≤ D)
    (hB : B ≤ Nat.choose (n / 3) r)
    (hQ : Nat.choose (n / 3) r ≤ n ^ r)
    (hCL : 3 * n * D ≤ C * (Nat.choose (n / 3) r - B))
    (hexp : 2 * (3 : ℝ) ^ n * (n : ℝ) ^ (r * B) *
      Real.exp (-3 * (n : ℝ)) < 1) :
    2 * (colorBadLabelings n r B C D).card <
      D ^ Fintype.card (UniformEdge n r) := by
  let Q := Nat.choose (n / 3) r
  let L := Q - B
  let E := Fintype.card (UniformEdge n r)
  have hLE : L ≤ E := by
    dsimp only [L, Q, E]
    rw [card_uniformEdge]
    exact (Nat.sub_le _ _).trans (Nat.choose_le_choose r (Nat.div_le_self n 3))
  have hcore : 2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L < D ^ L :=
    color_tail_core_bound hD hCD hQ hCL hexp
  have hremaining : 0 < D ^ (E - L) := pow_pos hD _
  have hcount := card_colorBadLabelings_le hB hCD
  change (colorBadLabelings n r B C D).card ≤
      3 ^ n * (Nat.choose Q B * ((D - C) ^ L * D ^ (E - L))) at hcount
  calc
    2 * (colorBadLabelings n r B C D).card ≤
        2 * (3 ^ n * (Nat.choose Q B *
          ((D - C) ^ L * D ^ (E - L)))) := Nat.mul_le_mul_left 2 hcount
    _ = (2 * 3 ^ n * Nat.choose Q B * (D - C) ^ L) * D ^ (E - L) := by
      ac_rfl
    _ < D ^ L * D ^ (E - L) :=
      Nat.mul_lt_mul_of_pos_right hcore hremaining
    _ = D ^ E := by
      rw [← pow_add, Nat.add_sub_of_le hLE]

private def samplingThreshold (r : ℕ) : ℕ := 4 * 6 ^ r * r.factorial

private def cycleDeletionBudget (r K : ℕ) : ℕ :=
  4 * K * ∑ s : Fin K, (samplingThreshold r) ^ s.val

/-- On the convenient subsequence `n = 6rm`, the color block contains enough
`r`-sets for the fixed sampling threshold. -/
private theorem four_pow_le_threshold_mul_choose {r m : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) :
    4 * (6 * r * m) ^ r ≤
      samplingThreshold r * Nat.choose ((6 * r * m) / 3) r := by
  have hnDiv : (6 * r * m) / 3 = 2 * r * m := by
    calc
      (6 * r * m) / 3 = (3 * (2 * r * m)) / 3 := by congr 1 <;> ring
      _ = 2 * r * m := Nat.mul_div_cancel_left _ (by norm_num)
  have hrm : r ≤ r * m := by
    simpa using Nat.mul_le_mul_left r hm
  have hbase : r * m ≤ (6 * r * m) / 3 + 1 - r := by
    rw [hnDiv]
    apply Nat.le_sub_of_add_le
    calc
      r * m + r ≤ r * m + r * m := Nat.add_le_add_left hrm _
      _ = 2 * r * m := by ring
      _ ≤ 2 * r * m + 1 := Nat.le_succ _
  have hdesc : (r * m) ^ r ≤
      r.factorial * Nat.choose ((6 * r * m) / 3) r := by
    calc
      (r * m) ^ r ≤ (((6 * r * m) / 3) + 1 - r) ^ r :=
        Nat.pow_le_pow_left hbase r
      _ ≤ ((6 * r * m) / 3).descFactorial r :=
        Nat.pow_sub_le_descFactorial _ _
      _ = r.factorial * Nat.choose ((6 * r * m) / 3) r :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  have hmul := Nat.mul_le_mul_left (4 * 6 ^ r) hdesc
  calc
    4 * (6 * r * m) ^ r = (4 * 6 ^ r) * (r * m) ^ r := by
      rw [show 6 * r * m = 6 * (r * m) by ring, mul_pow]
      ring
    _ ≤ (4 * 6 ^ r) *
        (r.factorial * Nat.choose ((6 * r * m) / 3) r) := hmul
    _ = samplingThreshold r * Nat.choose ((6 * r * m) / 3) r := by
      simp only [samplingThreshold]
      ring

/-- All numerical hypotheses for the two finite bad-event estimates can be
met simultaneously by taking a sufficiently large member of `n = 6rm`. -/
private theorem exists_sampling_parameters (r K : ℕ) (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ n : ℕ,
      let C := samplingThreshold r
      let B := cycleDeletionBudget r K
      let D := n ^ (r - 1)
      let Q := Nat.choose (n / 3) r
      C ≤ D ∧ B ≤ Q ∧ K ≤ Nat.choose n r ∧
        3 * n * D ≤ C * (Q - B) ∧
        2 * (3 : ℝ) ^ n * (n : ℝ) ^ (r * B) *
          Real.exp (-3 * (n : ℝ)) < 1 := by
  let C := samplingThreshold r
  let S := ∑ s : Fin K, C ^ s.val
  let B := cycleDeletionBudget r K
  obtain ⟨N, hN⟩ :=
    (eventually_color_tail_exponential (r * B)).exists_forall_of_atTop
  let m := max 1 (max C (max (C * B) N))
  let n := 6 * r * m
  have hm1 : 1 ≤ m := le_max_left _ _
  have hCm : C ≤ m :=
    (le_max_left C (max (C * B) N)).trans (le_max_right 1 _)
  have hCBm : C * B ≤ m :=
    (le_max_left (C * B) N).trans
      ((le_max_right C (max (C * B) N)).trans (le_max_right 1 _))
  have hNm : N ≤ m :=
    (le_max_right (C * B) N).trans
      ((le_max_right C (max (C * B) N)).trans (le_max_right 1 _))
  have hmn : m ≤ n := by
    dsimp only [n]
    have hfac : 1 ≤ 6 * r := by omega
    simpa [mul_assoc] using Nat.mul_le_mul_right m hfac
  have hnpos : 0 < n := hm1.trans hmn
  have hCn : C ≤ n := hCm.trans hmn
  have hCBn : C * B ≤ n := hCBm.trans hmn
  have hn_le_pow_r : n ≤ n ^ r := by
    simpa using (Nat.pow_le_pow_right hnpos (show 1 ≤ r by omega))
  have hn_le_D : n ≤ n ^ (r - 1) := by
    have : 1 ≤ r - 1 := by omega
    simpa using (Nat.pow_le_pow_right hnpos this)
  have hCD : C ≤ n ^ (r - 1) := hCn.trans hn_le_D
  have hCBpow : C * B ≤ n ^ r := hCBn.trans hn_le_pow_r
  have hCpos : 0 < C := by
    dsimp only [C, samplingThreshold]
    positivity
  have hfour : 4 * n ^ r ≤ C * Nat.choose (n / 3) r := by
    dsimp only [n]
    exact four_pow_le_threshold_mul_choose (by omega) hm1
  have hBQ : B ≤ Nat.choose (n / 3) r := by
    apply Nat.le_of_mul_le_mul_left (c := C) ?_ hCpos
    exact hCBpow.trans (le_trans (by omega) hfour)
  have hSone : 1 ≤ S := by
    dsimp only [S]
    have hzero : (⟨0, hK⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) :=
      Finset.mem_univ _
    simpa using (Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin K)))
      (f := fun s : Fin K ↦ C ^ s.val)
      (fun _ _ ↦ Nat.zero_le _) hzero :
        C ^ (⟨0, hK⟩ : Fin K).val ≤ ∑ s : Fin K, C ^ s.val)
  have hKB : K ≤ B := by
    dsimp only [B, cycleDeletionBudget]
    change K ≤ 4 * K * S
    calc
      K = 1 * K := by simp
      _ ≤ (4 * S) * K := Nat.mul_le_mul_right K (by omega)
      _ = 4 * K * S := by ring
  have hKnThird : K ≤ Nat.choose (n / 3) r := hKB.trans hBQ
  have hKn : K ≤ Nat.choose n r :=
    hKnThird.trans (Nat.choose_le_choose r (Nat.div_le_self n 3))
  have hCL : 3 * n * (n ^ (r - 1)) ≤
      C * (Nat.choose (n / 3) r - B) := by
    have hnMul : n * n ^ (r - 1) = n ^ r := by
      calc
        n * n ^ (r - 1) = n ^ (r - 1) * n := by ac_rfl
        _ = n ^ ((r - 1) + 1) := (pow_succ n (r - 1)).symm
        _ = n ^ r := by congr 1 <;> omega
    have hsplit : C * B + C * (Nat.choose (n / 3) r - B) =
        C * Nat.choose (n / 3) r := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hBQ]
    calc
      3 * n * n ^ (r - 1) = 3 * (n * n ^ (r - 1)) := by ring
      _ = 3 * n ^ r := by rw [hnMul]
      _ ≤ C * (Nat.choose (n / 3) r - B) := by omega
  refine ⟨n, hCD, hBQ, hKn, hCL, ?_⟩
  exact hN n (hNm.trans hmn)

/-- Finite avoidance of the two bad events supplies the hypergraph required
by the Erdős--Hajnal deletion argument. -/
private theorem exists_highBergeGirth_notThreeColorable (r K : ℕ)
    (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ n : ℕ, ∃ H : OrderedUniformHypergraph.{0, 0} (Fin n) r,
      H.BergeGirthAtLeast K ∧ H.NotThreeColorable := by
  let C := samplingThreshold r
  let S := ∑ s : Fin K, C ^ s.val
  let B := cycleDeletionBudget r K
  obtain ⟨n, hCD, hBQ, hKn, hCL, hexp⟩ :=
    exists_sampling_parameters r K hr hK
  let D := n ^ (r - 1)
  let cycleBad := cycleHeavyLabelings n r C K
  let colorBad := colorBadLabelings n r B C D
  have hCpos : 0 < C := by
    dsimp only [C, samplingThreshold]
    positivity
  have hDpos : 0 < D := lt_of_lt_of_le hCpos hCD
  have hcycle : 2 * cycleBad.card ≤
      D ^ Fintype.card (UniformEdge n r) := by
    dsimp only [cycleBad, D]
    exact twice_card_cycleHeavyLabelings_le hr hCD hKn
  have hcolor : 2 * colorBad.card <
      D ^ Fintype.card (UniformEdge n r) := by
    dsimp only [colorBad]
    exact twice_card_colorBadLabelings_lt hDpos hCD hBQ
      ((Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_left (Nat.div_le_self n 3) r)) hCL hexp
  have hsum : cycleBad.card + colorBad.card <
      D ^ Fintype.card (UniformEdge n r) := by omega
  let bad := cycleBad ∪ colorBad
  have hbadCard : bad.card < D ^ Fintype.card (UniformEdge n r) :=
    (Finset.card_union_le cycleBad colorBad).trans_lt hsum
  have hunivCard :
      (Finset.univ : Finset (UniformEdge n r → Fin D)).card =
        D ^ Fintype.card (UniformEdge n r) := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hbadNe : bad ≠ (Finset.univ : Finset (UniformEdge n r → Fin D)) := by
    intro h
    rw [h, hunivCard] at hbadCard
    exact (Nat.lt_irrefl _ hbadCard)
  obtain ⟨ω, hω⟩ : ∃ ω : UniformEdge n r → Fin D, ω ∉ bad := by
    by_contra h
    apply hbadNe
    apply Finset.eq_univ_of_forall
    intro ω
    by_contra hω
    exact h ⟨ω, hω⟩
  have hωCycle : ω ∉ cycleBad := by
    intro hmem
    exact hω (Finset.mem_union_left colorBad hmem)
  have hωColor : ω ∉ colorBad := by
    intro hmem
    exact hω (Finset.mem_union_right cycleBad hmem)
  have hactive : (activeShortCycles (C := C) ω K).card ≤ 2 * S := by
    dsimp only [cycleBad] at hωCycle
    have hnlt := (not_congr (mem_cycleHeavyLabelings (ω := ω))).mp hωCycle
    dsimp only [S]
    omega
  have hshort : ((sampledHypergraph (C := C) ω).shortCycleEdges K).card ≤ B := by
    calc
      ((sampledHypergraph (C := C) ω).shortCycleEdges K).card ≤
          2 * K * (activeShortCycles (C := C) ω K).card :=
        shortCycleEdges_card_le_twice_mul_active ω
      _ ≤ 2 * K * (2 * S) := Nat.mul_le_mul_left (2 * K) hactive
      _ = B := by
        dsimp only [B, cycleDeletionBudget, S, C]
        ring
  have hmono : ∀ c : Fin n → Fin 3,
      B < (selectedMonochromaticEdges C ω c).card := by
    intro c
    apply Nat.lt_of_not_ge
    intro hc
    apply hωColor
    exact mem_colorBadLabelings.mpr ⟨c, hc⟩
  have hrobustB :
      (sampledHypergraph (C := C) ω).DeletionRobustNotThreeColorable B :=
    sampledHypergraph_deletionRobust ω hmono
  have hrobustShort :
      (sampledHypergraph (C := C) ω).DeletionRobustNotThreeColorable
        ((sampledHypergraph (C := C) ω).shortCycleEdges K).card := by
    intro t ht
    exact hrobustB t (ht.trans hshort)
  obtain ⟨s, hsGirth, hsNotThree⟩ :=
    (sampledHypergraph (C := C) ω).exists_largeBergeGirth_restriction K
      hrobustShort
  exact ⟨n, (sampledHypergraph (C := C) ω).restrictEdges s,
    hsGirth, hsNotThree⟩

/-- The final restriction supplies precisely O'Donnell's four-cluster
hypergraph while preserving its Berge-girth lower bound. -/
theorem exists_fourClusterHypergraph (r K : ℕ) (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ n : ℕ, ∃ H : OrderedUniformHypergraph.{0, 0} (Fin n) r,
      H.BergeGirthAtLeast K ∧ H.EdgeMinimalNotThreeColorable ∧
        H.SupportsFourClusters := by
  obtain ⟨n, H, hGirth, hNotThree⟩ :=
    exists_highBergeGirth_notThreeColorable r K hr hK
  obtain ⟨s, hsMinimal⟩ := H.exists_edgeMinimal_restriction (by omega) hNotThree
  refine ⟨n, H.restrictEdges s, H.bergeGirthAtLeast_restrictEdges s hGirth,
    hsMinimal, ?_⟩
  exact (H.restrictEdges s).supportsFourClusters_of_edgeMinimal hr hsMinimal

/-! ## A pair-cluster refinement

For the geometric realization it is convenient to retain only edges having
`r-1` vertices in one of four equal blocks and one vertex in another block.
The next definitions isolate that finite subfamily. -/

private def fourBlockCluster {n : ℕ} (x : Fin (4 * n)) : Fin 4 :=
  (finProdFinEquiv.symm x).1

private def fourBlockIndex {n : ℕ} (x : Fin (4 * n)) : Fin n :=
  (finProdFinEquiv.symm x).2

private def inFourBlock {n : ℕ} (a : Fin 4) (x : Fin (4 * n)) : Prop :=
  fourBlockCluster x = a

/-- An `r`-set with multiplicity pattern `(r-1,1)` on two distinct blocks. -/
noncomputable def IsPairClusterEdge {n r : ℕ}
    (e : UniformEdge (4 * n) r) : Prop := by
  classical
  exact ∃ a b : Fin 4, a ≠ b ∧
    (e.1.filter (inFourBlock a)).card = r - 1 ∧
    (e.1.filter (inFourBlock b)).card = 1

def HasPairClusterPattern {Y : Type*} (J : OrderedUniformHypergraph Y r)
    (cluster : Y → Fin 4) : Prop :=
  ∀ e : J.Edge, ∃ a b : Fin 4, a ≠ b ∧
    ((Finset.univ : Finset (Fin r)).filter
      (fun i ↦ cluster (J.vertex e i) = a)).card = r - 1 ∧
    ((Finset.univ : Finset (Fin r)).filter
      (fun i ↦ cluster (J.vertex e i) = b)).card = 1

private theorem uniformEdgeVertex_filter_card {n r : ℕ}
    (e : UniformEdge n r) (p : Fin n → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin r)).filter
      (fun i ↦ p (uniformEdgeVertex e i))).card =
        (e.1.filter p).card := by
  rw [← Finset.card_map (uniformEdgeVertex e)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem e.1 e.2 i, hi⟩
  · rintro ⟨hxe, hpx⟩
    obtain ⟨i, hi⟩ := Set.mem_range.mp
      ((e.1.range_orderEmbOfFin e.2).ge hxe)
    refine ⟨i, ?_, hi⟩
    change p ((e.1.orderEmbOfFin e.2) i)
    simpa only [← hi] using hpx

private noncomputable def selectedPairMonochromaticEdges {n r q D : ℕ}
    (C : ℕ) (ω : UniformEdge (4 * n) r → Fin D)
    (c : Fin (4 * n) → Fin q) : Finset (UniformEdge (4 * n) r) := by
  classical
  exact Finset.univ.filter fun e ↦
    (ω e).val < C ∧ IsPairClusterEdge e ∧ EdgeMonochromatic c e

@[simp] private theorem mem_selectedPairMonochromaticEdges
    {n r q D C : ℕ} {ω : UniformEdge (4 * n) r → Fin D}
    {c : Fin (4 * n) → Fin q} {e : UniformEdge (4 * n) r} :
    e ∈ selectedPairMonochromaticEdges C ω c ↔
      (ω e).val < C ∧ IsPairClusterEdge e ∧ EdgeMonochromatic c e := by
  classical
  simp [selectedPairMonochromaticEdges]

private def clusterColoring {n q : ℕ}
    (c : Fin (4 * n) → Fin q) (a : Fin 4) : Fin n → Fin q :=
  fun x ↦ c (finProdFinEquiv (a, x))

private noncomputable def clusterMajorityColor {n : ℕ}
    (c : Fin (4 * n) → Fin 3) (a : Fin 4) : Fin 3 :=
  threeColorBlockColor (clusterColoring c a)

private noncomputable def clusterMajorityBlock {n : ℕ}
    (c : Fin (4 * n) → Fin 3) (a : Fin 4) : Finset (Fin n) :=
  threeColorBlock (clusterColoring c a)

private theorem clusterMajorityBlock_spec {n : ℕ}
    (c : Fin (4 * n) → Fin 3) (a : Fin 4) :
    clusterMajorityBlock c a ⊆ Finset.univ.filter
      (fun x ↦ c (finProdFinEquiv (a, x)) = clusterMajorityColor c a) ∧
      (clusterMajorityBlock c a).card = n / 3 := by
  exact threeColorBlock_spec (clusterColoring c a)

private theorem exists_equal_clusterMajorities {n : ℕ}
    (c : Fin (4 * n) → Fin 3) :
    ∃ a b : Fin 4, a ≠ b ∧ clusterMajorityColor c a = clusterMajorityColor c b := by
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (clusterMajorityColor c) (by simp)
  exact ⟨a, b, hab, heq⟩

private noncomputable def firstMajorityCluster {n : ℕ}
    (c : Fin (4 * n) → Fin 3) : Fin 4 :=
  Classical.choose (exists_equal_clusterMajorities c)

private noncomputable def secondMajorityCluster {n : ℕ}
    (c : Fin (4 * n) → Fin 3) : Fin 4 :=
  Classical.choose (Classical.choose_spec (exists_equal_clusterMajorities c))

private theorem majorityClusters_spec {n : ℕ}
    (c : Fin (4 * n) → Fin 3) :
    firstMajorityCluster c ≠ secondMajorityCluster c ∧
      clusterMajorityColor c (firstMajorityCluster c) =
        clusterMajorityColor c (secondMajorityCluster c) :=
  by
    simpa [firstMajorityCluster, secondMajorityCluster] using
      Classical.choose_spec (Classical.choose_spec (exists_equal_clusterMajorities c))

private def fourBlockPoint {n : ℕ} (a : Fin 4) (x : Fin n) : Fin (4 * n) :=
  finProdFinEquiv (a, x)

@[simp] private theorem fourBlockCluster_point {n : ℕ} (a : Fin 4) (x : Fin n) :
    fourBlockCluster (fourBlockPoint a x) = a := by
  simp [fourBlockCluster, fourBlockPoint]

@[simp] private theorem fourBlockIndex_point {n : ℕ} (a : Fin 4) (x : Fin n) :
    fourBlockIndex (fourBlockPoint a x) = x := by
  simp [fourBlockIndex, fourBlockPoint]

private def fourBlockEmbedding {n : ℕ} (a : Fin 4) : Fin n ↪ Fin (4 * n) where
  toFun := fourBlockPoint a
  inj' := by
    intro x y h
    have := congrArg fourBlockIndex h
    simpa using this

@[simp] private theorem fourBlockCluster_embedding {n : ℕ}
    (a : Fin 4) (x : Fin n) :
    fourBlockCluster ((fourBlockEmbedding a) x) = a := by
  exact fourBlockCluster_point a x

private def liftFourBlock {n : ℕ} (a : Fin 4) (S : Finset (Fin n)) :
    Finset (Fin (4 * n)) := S.map (fourBlockEmbedding a)

@[simp] private theorem mem_liftFourBlock {n : ℕ} {a : Fin 4}
    {S : Finset (Fin n)} {x : Fin n} :
    fourBlockPoint a x ∈ liftFourBlock a S ↔ x ∈ S := by
  rw [liftFourBlock, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := (fourBlockEmbedding a).injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem fourBlockPoint_ne_of_ne {n : ℕ} {a b : Fin 4}
    (hab : a ≠ b) (x y : Fin n) : fourBlockPoint a x ≠ fourBlockPoint b y := by
  intro h
  exact hab (by simpa using congrArg fourBlockCluster h)

private def PairBlockIndex {n r : ℕ} (c : Fin (4 * n) → Fin 3) :=
  {S : Finset (Fin n) //
      S ∈ (clusterMajorityBlock c (firstMajorityCluster c)).powersetCard (r - 1)} ×
    {y : Fin n // y ∈ clusterMajorityBlock c (secondMajorityCluster c)}

private noncomputable def pairBlockEdge {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) (p : PairBlockIndex (r := r) c) :
    UniformEdge (4 * n) r := by
  let a := firstMajorityCluster c
  let b := secondMajorityCluster c
  let S := p.1.1
  let y := p.2.1
  have hab : a ≠ b := (majorityClusters_spec c).1
  refine ⟨liftFourBlock a S ∪ {fourBlockPoint b y}, ?_⟩
  have hy : fourBlockPoint b y ∉ liftFourBlock a S := by
    intro h
    rw [liftFourBlock, Finset.mem_map] at h
    obtain ⟨x, _, hxy⟩ := h
    exact fourBlockPoint_ne_of_ne hab x y hxy
  rw [Finset.card_union_of_disjoint]
  · change (S.map (fourBlockEmbedding a)).card +
      ({fourBlockPoint b y} : Finset (Fin (4 * n))).card = r
    rw [Finset.card_map, Finset.card_singleton,
      (Finset.mem_powersetCard.mp p.1.2).2]
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
    omega
  · rw [Finset.disjoint_singleton_right]
    exact hy

private theorem mem_pairBlockEdge_first {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) (p : PairBlockIndex (r := r) c) (x : Fin n) :
    fourBlockPoint (firstMajorityCluster c) x ∈ (pairBlockEdge c p).1 ↔
      x ∈ p.1.1 := by
  have hab := (majorityClusters_spec c).1
  change fourBlockPoint (firstMajorityCluster c) x ∈
    liftFourBlock (firstMajorityCluster c) p.1.1 ∪
      {fourBlockPoint (secondMajorityCluster c) p.2.1} ↔ _
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hS | hy
    · exact mem_liftFourBlock.mp hS
    · have hpoints : fourBlockPoint (firstMajorityCluster c) x =
          fourBlockPoint (secondMajorityCluster c) p.2.1 := by simpa using hy
      exact (fourBlockPoint_ne_of_ne hab x p.2.1 hpoints).elim
  · intro hx
    exact Finset.mem_union_left _ (mem_liftFourBlock.mpr hx)

private theorem mem_pairBlockEdge_second {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) (p : PairBlockIndex (r := r) c) (y : Fin n) :
    fourBlockPoint (secondMajorityCluster c) y ∈ (pairBlockEdge c p).1 ↔
      y = p.2.1 := by
  have hab := (majorityClusters_spec c).1
  change fourBlockPoint (secondMajorityCluster c) y ∈
    liftFourBlock (firstMajorityCluster c) p.1.1 ∪
      {fourBlockPoint (secondMajorityCluster c) p.2.1} ↔ _
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hS | hy
    · rw [liftFourBlock, Finset.mem_map] at hS
      obtain ⟨x, _, hpoints⟩ := hS
      have hclusters := congrArg fourBlockCluster hpoints
      have : firstMajorityCluster c = secondMajorityCluster c := by simpa using hclusters
      exact (hab this).elim
    · have hpoints : fourBlockPoint (secondMajorityCluster c) y =
          fourBlockPoint (secondMajorityCluster c) p.2.1 := by simpa using hy
      simpa using congrArg fourBlockIndex hpoints
  · intro hy
    subst y
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

private theorem pairBlockEdge_injective {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) :
    Function.Injective (pairBlockEdge (r := r) c) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    ext x
    rw [← mem_pairBlockEdge_first c p x, ← mem_pairBlockEdge_first c q x, hpq]
  · apply Subtype.ext
    have hpMem : fourBlockPoint (secondMajorityCluster c) p.2.1 ∈
        (pairBlockEdge (r := r) c p).1 :=
      (mem_pairBlockEdge_second c p p.2.1).2 rfl
    have hqMem : fourBlockPoint (secondMajorityCluster c) p.2.1 ∈
        (pairBlockEdge (r := r) c q).1 := hpq ▸ hpMem
    exact (mem_pairBlockEdge_second c q p.2.1).1 hqMem

private noncomputable def pairBlockEdgeEmbedding {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) :
    PairBlockIndex (r := r) c ↪ UniformEdge (4 * n) r where
  toFun := pairBlockEdge c
  inj' := pairBlockEdge_injective c

private noncomputable def pairColorBlockEdges {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) : Finset (UniformEdge (4 * n) r) := by
  classical
  letI : Finite (PairBlockIndex (r := r) c) := by
    dsimp [PairBlockIndex]
    infer_instance
  letI : Fintype (PairBlockIndex (r := r) c) := Fintype.ofFinite _
  exact Finset.univ.map (pairBlockEdgeEmbedding (r := r) c)

private theorem card_pairColorBlockEdges {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) :
    (pairColorBlockEdges (r := r) c).card =
      Nat.choose (n / 3) (r - 1) * (n / 3) := by
  classical
  letI : Finite (PairBlockIndex (r := r) c) := by
    dsimp [PairBlockIndex]
    infer_instance
  letI : Fintype (PairBlockIndex (r := r) c) := Fintype.ofFinite _
  rw [pairColorBlockEdges, Finset.card_map, Finset.card_univ]
  let T :=
    ({S : Finset (Fin n) // S ∈
        (clusterMajorityBlock c (firstMajorityCluster c)).powersetCard (r - 1)} ×
      {y : Fin n // y ∈ clusterMajorityBlock c (secondMajorityCluster c)})
  let e : PairBlockIndex (r := r) c ≃ T :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (PairBlockIndex (r := r) c) = Fintype.card T :=
      Fintype.card_congr e
    _ = Nat.choose (n / 3) (r - 1) * (n / 3) := by
      dsimp only [T]
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard, (clusterMajorityBlock_spec c _).2,
        (clusterMajorityBlock_spec c _).2]

private theorem pairColorBlockEdges_good {n r : ℕ} [NeZero r]
    (c : Fin (4 * n) → Fin 3) {e : UniformEdge (4 * n) r}
    (he : e ∈ pairColorBlockEdges (r := r) c) :
    IsPairClusterEdge e ∧ EdgeMonochromatic c e := by
  classical
  rw [pairColorBlockEdges, Finset.mem_map] at he
  obtain ⟨p, _, rfl⟩ := he
  change IsPairClusterEdge (pairBlockEdge (r := r) c p) ∧
    EdgeMonochromatic c (pairBlockEdge (r := r) c p)
  let a := firstMajorityCluster c
  let b := secondMajorityCluster c
  have hab : a ≠ b := (majorityClusters_spec c).1
  have hcolor : clusterMajorityColor c a = clusterMajorityColor c b :=
    (majorityClusters_spec c).2
  constructor
  · refine ⟨a, b, hab, ?_, ?_⟩
    · have hfilter :
          ((pairBlockEdge (r := r) c p).1.filter (inFourBlock a)) =
            liftFourBlock a p.1.1 := by
        ext z
        constructor
        · intro hz
          have hzmem := (Finset.mem_filter.mp hz).1
          rcases Finset.mem_union.mp hzmem with hzS | hzy
          · exact hzS
          · have hzb : z = fourBlockPoint b p.2.1 := by simpa using hzy
            have hza := (Finset.mem_filter.mp hz).2
            rw [hzb] at hza
            have hba : b = a := by simpa [inFourBlock] using hza
            exact (hab hba.symm).elim
        · intro hz
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_union_left _ hz, by
            rw [liftFourBlock, Finset.mem_map] at hz
            obtain ⟨x, _, rfl⟩ := hz
            change fourBlockCluster (fourBlockPoint a x) = a
            exact fourBlockCluster_point a x⟩
      change ((pairBlockEdge (r := r) c p).1.filter (inFourBlock a)).card = r - 1
      rw [hfilter, liftFourBlock, Finset.card_map,
        (Finset.mem_powersetCard.mp p.1.2).2]
    · have hfilter :
          ((pairBlockEdge (r := r) c p).1.filter (inFourBlock b)) =
            {fourBlockPoint b p.2.1} := by
        ext z
        constructor
        · intro hz
          have hzmem := (Finset.mem_filter.mp hz).1
          rcases Finset.mem_union.mp hzmem with hzS | hzy
          · rw [liftFourBlock, Finset.mem_map] at hzS
            obtain ⟨x, _, rfl⟩ := hzS
            have hba := (Finset.mem_filter.mp hz).2
            have hab' : a = b := by
              change fourBlockCluster (fourBlockPoint a x) = b at hba
              simpa using hba
            exact (hab hab').elim
          · exact hzy
        · intro hz
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_union_right _ hz, by
            simpa [inFourBlock] using congrArg fourBlockCluster
              (Finset.mem_singleton.mp hz)⟩
      change ((pairBlockEdge (r := r) c p).1.filter (inFourBlock b)).card = 1
      rw [hfilter, Finset.card_singleton]
  · refine ⟨clusterMajorityColor c a, ?_⟩
    intro z hz
    rcases Finset.mem_union.mp hz with hzS | hzy
    · rw [liftFourBlock, Finset.mem_map] at hzS
      obtain ⟨x, hx, rfl⟩ := hzS
      exact (Finset.mem_filter.mp ((clusterMajorityBlock_spec c a).1
        ((Finset.mem_powersetCard.mp p.1.2).1 hx))).2
    · have hzy' : z = fourBlockPoint b p.2.1 := by simpa using hzy
      subst z
      rw [hcolor]
      exact (Finset.mem_filter.mp ((clusterMajorityBlock_spec c b).1 p.2.2)).2

private theorem card_labelings_with_bad_pairColoring
    {n r B C D : ℕ} [NeZero r]
    (hB : B ≤ Nat.choose (n / 3) (r - 1) * (n / 3)) (hCD : C ≤ D) :
    Nat.card {ω : UniformEdge (4 * n) r → Fin D //
        ∃ c : Fin (4 * n) → Fin 3,
          (selectedPairMonochromaticEdges C ω c).card ≤ B} ≤
      3 ^ (4 * n) *
        (Nat.choose (Nat.choose (n / 3) (r - 1) * (n / 3)) B *
          ((D - C) ^ (Nat.choose (n / 3) (r - 1) * (n / 3) - B) *
            D ^ (Fintype.card (UniformEdge (4 * n) r) -
              (Nat.choose (n / 3) (r - 1) * (n / 3) - B)))) := by
  classical
  let Bad := {ω : UniformEdge (4 * n) r → Fin D //
    ∃ c : Fin (4 * n) → Fin 3,
      (selectedPairMonochromaticEdges C ω c).card ≤ B}
  let Tail (c : Fin (4 * n) → Fin 3) :=
    {ω : UniformEdge (4 * n) r → Fin D //
      ((pairColorBlockEdges (r := r) c).filter
        fun e ↦ (ω e).val < C).card ≤ B}
  have htail (ω : Bad) : ∃ c : Fin (4 * n) → Fin 3,
      ((pairColorBlockEdges (r := r) c).filter
        fun e ↦ (ω.1 e).val < C).card ≤ B := by
    obtain ⟨c, hc⟩ := ω.2
    refine ⟨c, ?_⟩
    have hsub : (pairColorBlockEdges (r := r) c).filter
          (fun e ↦ (ω.1 e).val < C) ⊆
        selectedPairMonochromaticEdges C ω.1 c := by
      intro e he
      have he' := Finset.mem_filter.mp he
      have hgood := pairColorBlockEdges_good c he'.1
      exact mem_selectedPairMonochromaticEdges.mpr
        ⟨he'.2, hgood.1, hgood.2⟩
    exact (Finset.card_le_card hsub).trans hc
  let chosenColor (ω : Bad) : Fin (4 * n) → Fin 3 := Classical.choose (htail ω)
  have hchosen (ω : Bad) :
      ((pairColorBlockEdges (r := r) (chosenColor ω)).filter
        fun e ↦ (ω.1 e).val < C).card ≤ B :=
    Classical.choose_spec (htail ω)
  let encode : Bad → Σ c : Fin (4 * n) → Fin 3, Tail c := fun ω ↦
    ⟨chosenColor ω, ⟨ω.1, hchosen ω⟩⟩
  have hencode : Function.Injective encode := by
    intro ω η hωη
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hωη
  let Q := Nat.choose (n / 3) (r - 1) * (n / 3)
  let R := Nat.choose Q B *
    ((D - C) ^ (Q - B) *
      D ^ (Fintype.card (UniformEdge (4 * n) r) - (Q - B)))
  have hTailCard (c : Fin (4 * n) → Fin 3) : Nat.card (Tail c) ≤ R := by
    have h := card_labelings_with_few_selected
      (pairColorBlockEdges (r := r) c) (B := B) (C := C) (D := D)
      (by simpa [card_pairColorBlockEdges c] using hB) hCD
    simpa [Tail, R, Q, card_pairColorBlockEdges c] using h
  calc
    Nat.card Bad ≤ Nat.card (Σ c : Fin (4 * n) → Fin 3, Tail c) :=
      Nat.card_le_card_of_injective encode hencode
    _ = ∑ c : Fin (4 * n) → Fin 3, Nat.card (Tail c) := Nat.card_sigma
    _ ≤ ∑ _c : Fin (4 * n) → Fin 3, R :=
      Finset.sum_le_sum fun c _ ↦ hTailCard c
    _ = 3 ^ (4 * n) * R := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = 3 ^ (4 * n) *
        (Nat.choose (Nat.choose (n / 3) (r - 1) * (n / 3)) B *
          ((D - C) ^ (Nat.choose (n / 3) (r - 1) * (n / 3) - B) *
            D ^ (Fintype.card (UniformEdge (4 * n) r) -
              (Nat.choose (n / 3) (r - 1) * (n / 3) - B)))) := rfl

private noncomputable def pairColorBadLabelings (n r B C D : ℕ) :
    Finset (UniformEdge (4 * n) r → Fin D) := by
  classical
  exact Finset.univ.filter fun ω ↦ ∃ c : Fin (4 * n) → Fin 3,
    (selectedPairMonochromaticEdges C ω c).card ≤ B

@[simp] private theorem mem_pairColorBadLabelings {n r B C D : ℕ}
    {ω : UniformEdge (4 * n) r → Fin D} :
    ω ∈ pairColorBadLabelings n r B C D ↔
      ∃ c : Fin (4 * n) → Fin 3,
        (selectedPairMonochromaticEdges C ω c).card ≤ B := by
  classical
  simp [pairColorBadLabelings]

private theorem card_pairColorBadLabelings_le {n r B C D : ℕ} [NeZero r]
    (hB : B ≤ Nat.choose (n / 3) (r - 1) * (n / 3)) (hCD : C ≤ D) :
    (pairColorBadLabelings n r B C D).card ≤
      3 ^ (4 * n) *
        (Nat.choose (Nat.choose (n / 3) (r - 1) * (n / 3)) B *
          ((D - C) ^ (Nat.choose (n / 3) (r - 1) * (n / 3) - B) *
            D ^ (Fintype.card (UniformEdge (4 * n) r) -
              (Nat.choose (n / 3) (r - 1) * (n / 3) - B)))) := by
  classical
  let Bad := {ω : UniformEdge (4 * n) r → Fin D //
    ∃ c : Fin (4 * n) → Fin 3,
      (selectedPairMonochromaticEdges C ω c).card ≤ B}
  have hcard : Nat.card Bad = (pairColorBadLabelings n r B C D).card := by
    exact Nat.subtype_card (pairColorBadLabelings n r B C D)
      (fun _ ↦ mem_pairColorBadLabelings)
  rw [← hcard]
  exact card_labelings_with_bad_pairColoring hB hCD

private theorem twice_card_pairColorBadLabelings_lt {n r B C D : ℕ} [NeZero r]
    (hD : 0 < D) (hCD : C ≤ D)
    (hB : B ≤ Nat.choose (n / 3) (r - 1) * (n / 3))
    (hQ : Nat.choose (n / 3) (r - 1) * (n / 3) ≤ (4 * n) ^ r)
    (hCL : 3 * (4 * n) * D ≤
      C * (Nat.choose (n / 3) (r - 1) * (n / 3) - B))
    (hexp : 2 * (3 : ℝ) ^ (4 * n) * (4 * n : ℝ) ^ (r * B) *
      Real.exp (-3 * (4 * n : ℝ)) < 1) :
    2 * (pairColorBadLabelings n r B C D).card <
      D ^ Fintype.card (UniformEdge (4 * n) r) := by
  let Q := Nat.choose (n / 3) (r - 1) * (n / 3)
  let L := Q - B
  let E := Fintype.card (UniformEdge (4 * n) r)
  have hLE : L ≤ E := by
    dsimp only [L, Q, E]
    have hcandidate : Nat.choose (n / 3) (r - 1) * (n / 3) ≤
        Fintype.card (UniformEdge (4 * n) r) := by
      let c : Fin (4 * n) → Fin 3 := fun _ => 0
      rw [← card_pairColorBlockEdges (r := r) c]
      exact Finset.card_le_univ _
    exact (Nat.sub_le _ _).trans hcandidate
  have hexp' : 2 * (3 : ℝ) ^ (4 * n) * (((4 * n : ℕ) : ℝ)) ^ (r * B) *
      Real.exp (-3 * (((4 * n : ℕ) : ℝ))) < 1 := by
    convert hexp using 1 <;> norm_num
  have hcore : 2 * 3 ^ (4 * n) * Nat.choose Q B * (D - C) ^ L < D ^ L :=
    color_tail_core_bound hD hCD hQ hCL hexp'
  have hremaining : 0 < D ^ (E - L) := pow_pos hD _
  have hcount := card_pairColorBadLabelings_le hB hCD
  change (pairColorBadLabelings n r B C D).card ≤
    3 ^ (4 * n) * (Nat.choose Q B * ((D - C) ^ L * D ^ (E - L))) at hcount
  calc
    2 * (pairColorBadLabelings n r B C D).card ≤
        2 * (3 ^ (4 * n) * (Nat.choose Q B *
          ((D - C) ^ L * D ^ (E - L)))) := Nat.mul_le_mul_left 2 hcount
    _ = (2 * 3 ^ (4 * n) * Nat.choose Q B * (D - C) ^ L) * D ^ (E - L) := by
      ac_rfl
    _ < D ^ L * D ^ (E - L) := Nat.mul_lt_mul_of_pos_right hcore hremaining
    _ = D ^ E := by rw [← pow_add, Nat.add_sub_of_le hLE]

private def pairSamplingThreshold (r : ℕ) : ℕ :=
  3 * 24 ^ r * (r - 1).factorial

private def pairCycleDeletionBudget (r K : ℕ) : ℕ :=
  4 * K * ∑ s : Fin K, (pairSamplingThreshold r) ^ s.val

private theorem six_four_pow_le_pairThreshold_mul_candidates
    {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) :
    6 * (4 * (6 * r * m)) ^ r ≤
      pairSamplingThreshold r *
        (Nat.choose ((6 * r * m) / 3) (r - 1) * ((6 * r * m) / 3)) := by
  have hnDiv : (6 * r * m) / 3 = 2 * r * m := by
    calc
      (6 * r * m) / 3 = (3 * (2 * r * m)) / 3 := by congr 1 <;> ring
      _ = 2 * r * m := Nat.mul_div_cancel_left _ (by norm_num)
  have hbase : r * m ≤ (6 * r * m) / 3 + 1 - (r - 1) := by
    rw [hnDiv]
    apply Nat.le_sub_of_add_le
    calc
      r * m + (r - 1) ≤ r * m + r * m := by
        gcongr
        have : r ≤ r * m := by simpa using Nat.mul_le_mul_left r hm
        omega
      _ = 2 * r * m := by ring
      _ ≤ 2 * r * m + 1 := Nat.le_succ _
  have hdesc : (r * m) ^ (r - 1) ≤
      (r - 1).factorial * Nat.choose ((6 * r * m) / 3) (r - 1) := by
    calc
      (r * m) ^ (r - 1) ≤
          (((6 * r * m) / 3) + 1 - (r - 1)) ^ (r - 1) :=
        Nat.pow_le_pow_left hbase _
      _ ≤ ((6 * r * m) / 3).descFactorial (r - 1) :=
        Nat.pow_sub_le_descFactorial _ _
      _ = (r - 1).factorial * Nat.choose ((6 * r * m) / 3) (r - 1) :=
        Nat.descFactorial_eq_factorial_mul_choose _ _
  have hmul := Nat.mul_le_mul_left (6 * 24 ^ r * (r * m)) hdesc
  have hrpow : (r * m) ^ r = (r * m) * (r * m) ^ (r - 1) := by
    calc
      (r * m) ^ r = (r * m) ^ ((r - 1) + 1) := by congr 1 <;> omega
      _ = (r * m) ^ (r - 1) * (r * m) := pow_succ _ _
      _ = (r * m) * (r * m) ^ (r - 1) := by ac_rfl
  rw [hnDiv]
  dsimp only [pairSamplingThreshold]
  calc
    6 * (4 * (6 * r * m)) ^ r =
        6 * 24 ^ r * (r * m) ^ r := by
      rw [show 4 * (6 * r * m) = 24 * (r * m) by ring, mul_pow]
      ring
    _ = (6 * 24 ^ r * (r * m)) * (r * m) ^ (r - 1) := by
      rw [hrpow]
      ring
    _ ≤ (6 * 24 ^ r * (r * m)) *
        ((r - 1).factorial * Nat.choose (2 * r * m) (r - 1)) := by
      simpa [hnDiv] using hmul
    _ = (3 * 24 ^ r * (r - 1).factorial) *
        (Nat.choose (2 * r * m) (r - 1) * (2 * r * m)) := by ring

private theorem exists_pair_sampling_parameters (r K : ℕ)
    (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ n : ℕ,
      let C := pairSamplingThreshold r
      let B := pairCycleDeletionBudget r K
      let D := (4 * n) ^ (r - 1)
      let Q := Nat.choose (n / 3) (r - 1) * (n / 3)
      C ≤ D ∧ B ≤ Q ∧ K ≤ Nat.choose (4 * n) r ∧
        3 * (4 * n) * D ≤ C * (Q - B) ∧
        2 * (3 : ℝ) ^ (4 * n) * (4 * n : ℝ) ^ (r * B) *
          Real.exp (-3 * (4 * n : ℝ)) < 1 := by
  letI : NeZero r := ⟨by omega⟩
  let C := pairSamplingThreshold r
  let S := ∑ s : Fin K, C ^ s.val
  let B := pairCycleDeletionBudget r K
  obtain ⟨N, hN⟩ :=
    (eventually_color_tail_exponential (r * B)).exists_forall_of_atTop
  let m := max 1 (max C (max (C * B) N))
  let n := 6 * r * m
  have hm1 : 1 ≤ m := le_max_left _ _
  have hCm : C ≤ m :=
    (le_max_left C (max (C * B) N)).trans (le_max_right 1 _)
  have hCBm : C * B ≤ m :=
    (le_max_left (C * B) N).trans
      ((le_max_right C (max (C * B) N)).trans (le_max_right 1 _))
  have hNm : N ≤ m :=
    (le_max_right (C * B) N).trans
      ((le_max_right C (max (C * B) N)).trans (le_max_right 1 _))
  have hmn : m ≤ n := by
    dsimp only [n]
    have hfac : 1 ≤ 6 * r := by omega
    simpa [mul_assoc] using Nat.mul_le_mul_right m hfac
  have hnpos : 0 < n := hm1.trans hmn
  have hfourNpos : 0 < 4 * n := by positivity
  have hCn : C ≤ n := hCm.trans hmn
  have hCfourN : C ≤ 4 * n := hCn.trans (by omega)
  have hDpow : 4 * n ≤ (4 * n) ^ (r - 1) := by
    have : 1 ≤ r - 1 := by omega
    simpa using Nat.pow_le_pow_right hfourNpos this
  have hCD : C ≤ (4 * n) ^ (r - 1) := hCfourN.trans hDpow
  have hCpos : 0 < C := by
    dsimp only [C, pairSamplingThreshold]
    have : 0 < (r - 1).factorial := Nat.factorial_pos _
    positivity
  let Q := Nat.choose (n / 3) (r - 1) * (n / 3)
  have hlower : 6 * (4 * n) ^ r ≤ C * Q := by
    dsimp only [n, C, Q]
    exact six_four_pow_le_pairThreshold_mul_candidates hr hm1
  have hCBsmall : C * B ≤ 3 * (4 * n) ^ r := by
    calc
      C * B ≤ m := hCBm
      _ ≤ n := hmn
      _ ≤ (4 * n) ^ r := by
        have : 1 ≤ r := by omega
        exact (by omega : n ≤ 4 * n) |>.trans
          (by simpa using Nat.pow_le_pow_right hfourNpos this)
      _ ≤ 3 * (4 * n) ^ r := by omega
  have hBQ : B ≤ Q := by
    apply Nat.le_of_mul_le_mul_left (c := C) ?_ hCpos
    exact hCBsmall.trans (le_trans (by omega) hlower)
  have hSone : 1 ≤ S := by
    dsimp only [S]
    have hzero : (⟨0, hK⟩ : Fin K) ∈ (Finset.univ : Finset (Fin K)) :=
      Finset.mem_univ _
    simpa using (Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin K)))
      (f := fun s : Fin K ↦ C ^ s.val)
      (fun _ _ ↦ Nat.zero_le _) hzero :
        C ^ (⟨0, hK⟩ : Fin K).val ≤ ∑ s : Fin K, C ^ s.val)
  have hKB : K ≤ B := by
    dsimp only [B, pairCycleDeletionBudget]
    change K ≤ 4 * K * S
    calc
      K = 1 * K := by simp
      _ ≤ (4 * S) * K := Nat.mul_le_mul_right K (by omega)
      _ = 4 * K * S := by ring
  have hQcard : Q ≤ Nat.choose (4 * n) r := by
    let c : Fin (4 * n) → Fin 3 := fun _ => 0
    dsimp only [Q]
    rw [← card_pairColorBlockEdges (r := r) c, ← card_uniformEdge]
    exact Finset.card_le_univ _
  have hKn : K ≤ Nat.choose (4 * n) r := hKB.trans (hBQ.trans hQcard)
  have hsplit : C * B + C * (Q - B) = C * Q := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hBQ]
  have hCL : 3 * (4 * n) * (4 * n) ^ (r - 1) ≤ C * (Q - B) := by
    have hpow : (4 * n) * (4 * n) ^ (r - 1) = (4 * n) ^ r := by
      calc
        (4 * n) * (4 * n) ^ (r - 1) = (4 * n) ^ (r - 1) * (4 * n) := by ac_rfl
        _ = (4 * n) ^ ((r - 1) + 1) := (pow_succ _ _).symm
        _ = (4 * n) ^ r := by congr 1 <;> omega
    calc
      3 * (4 * n) * (4 * n) ^ (r - 1) =
          3 * ((4 * n) * (4 * n) ^ (r - 1)) := by ring
      _ = 3 * (4 * n) ^ r := by rw [hpow]
      _ ≤ C * (Q - B) := by omega
  refine ⟨n, hCD, hBQ, hKn, hCL, ?_⟩
  have hNfour : N ≤ 4 * n := hNm.trans (hmn.trans (by omega))
  convert hN (4 * n) hNfour using 1 <;> norm_num <;> rfl

/-- A high-Berge-girth non-three-colorable hypergraph all of whose edges have
the geometrically uniform `(r-1,1)` four-block pattern. -/
theorem exists_pairClusterHypergraph (r K : ℕ) (hr : 2 ≤ r) (hK : 1 ≤ K) :
    ∃ n : ℕ, ∃ H : OrderedUniformHypergraph.{0, 0} (Fin (4 * n)) r,
      H.BergeGirthAtLeast K ∧ H.NotThreeColorable ∧
        H.HasPairClusterPattern fourBlockCluster := by
  classical
  letI : NeZero r := ⟨by omega⟩
  let C := pairSamplingThreshold r
  let S := ∑ s : Fin K, C ^ s.val
  let B := pairCycleDeletionBudget r K
  obtain ⟨n, hCD, hBQ, hKn, hCL, hexp⟩ :=
    exists_pair_sampling_parameters r K hr hK
  let D := (4 * n) ^ (r - 1)
  let cycleBad := cycleHeavyLabelings (4 * n) r C K
  let colorBad := pairColorBadLabelings n r B C D
  have hCpos : 0 < C := by
    dsimp only [C, pairSamplingThreshold]
    positivity
  have hDpos : 0 < D := lt_of_lt_of_le hCpos hCD
  have hcycle : 2 * cycleBad.card ≤
      D ^ Fintype.card (UniformEdge (4 * n) r) := by
    dsimp only [cycleBad, D]
    exact twice_card_cycleHeavyLabelings_le hr hCD hKn
  have hQpow : Nat.choose (n / 3) (r - 1) * (n / 3) ≤ (4 * n) ^ r := by
    calc
      Nat.choose (n / 3) (r - 1) * (n / 3) ≤
          (n / 3) ^ (r - 1) * (n / 3) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
      _ = (n / 3) ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ ≤ (4 * n) ^ r := Nat.pow_le_pow_left (by omega) _
  have hcolor : 2 * colorBad.card <
      D ^ Fintype.card (UniformEdge (4 * n) r) := by
    dsimp only [colorBad]
    exact twice_card_pairColorBadLabelings_lt hDpos hCD hBQ hQpow hCL hexp
  have hsum : cycleBad.card + colorBad.card <
      D ^ Fintype.card (UniformEdge (4 * n) r) := by omega
  let bad := cycleBad ∪ colorBad
  have hbadCard : bad.card < D ^ Fintype.card (UniformEdge (4 * n) r) :=
    (Finset.card_union_le cycleBad colorBad).trans_lt hsum
  have hunivCard :
      (Finset.univ : Finset (UniformEdge (4 * n) r → Fin D)).card =
        D ^ Fintype.card (UniformEdge (4 * n) r) := by
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hbadNe : bad ≠ (Finset.univ : Finset (UniformEdge (4 * n) r → Fin D)) := by
    intro h
    rw [h, hunivCard] at hbadCard
    exact (Nat.lt_irrefl _ hbadCard)
  obtain ⟨ω, hω⟩ : ∃ ω : UniformEdge (4 * n) r → Fin D, ω ∉ bad := by
    by_contra h
    apply hbadNe
    apply Finset.eq_univ_of_forall
    intro ω
    by_contra hω'
    exact h ⟨ω, hω'⟩
  have hωCycle : ω ∉ cycleBad := by
    intro hmem
    exact hω (Finset.mem_union_left colorBad hmem)
  have hωColor : ω ∉ colorBad := by
    intro hmem
    exact hω (Finset.mem_union_right cycleBad hmem)
  have hactive : (activeShortCycles (C := C) ω K).card ≤ 2 * S := by
    dsimp only [cycleBad] at hωCycle
    have hnlt := (not_congr (mem_cycleHeavyLabelings (ω := ω))).mp hωCycle
    dsimp only [S]
    omega
  let H₀ := sampledHypergraph (C := C) ω
  have hshort : (H₀.shortCycleEdges K).card ≤ B := by
    calc
      (H₀.shortCycleEdges K).card ≤
          2 * K * (activeShortCycles (C := C) ω K).card :=
        shortCycleEdges_card_le_twice_mul_active ω
      _ ≤ 2 * K * (2 * S) := Nat.mul_le_mul_left (2 * K) hactive
      _ = B := by
        dsimp only [B, pairCycleDeletionBudget, S, C]
        ring
  have hmono : ∀ c : Fin (4 * n) → Fin 3,
      B < (selectedPairMonochromaticEdges C ω c).card := by
    intro c
    apply Nat.lt_of_not_ge
    intro hc
    apply hωColor
    exact mem_pairColorBadLabelings.mpr ⟨c, hc⟩
  let deleted := H₀.deleteEdges (H₀.shortCycleEdges K)
  let Hdel := H₀.restrictEdges deleted
  letI : Fintype Hdel.Edge := Fintype.ofFinite _
  let pairEdges : Finset Hdel.Edge := Finset.univ.filter fun e ↦
    IsPairClusterEdge e.1.1
  let H := Hdel.restrictEdges pairEdges
  refine ⟨n, H, ?_, ?_, ?_⟩
  · exact Hdel.bergeGirthAtLeast_restrictEdges pairEdges
      (H₀.bergeGirthAtLeast_deleteShortCycles K)
  · intro c
    let used : Finset (UniformEdge (4 * n) r) :=
      (H₀.shortCycleEdges K).image fun e ↦ e.1
    have hused : used.card ≤ B := Finset.card_image_le.trans hshort
    obtain ⟨e, heMono, heNotUsed⟩ :
        ∃ e ∈ selectedPairMonochromaticEdges C ω c,
          e ∉ used := by
      by_contra h
      push Not at h
      have hsub : selectedPairMonochromaticEdges C ω c ⊆
          used := by
        intro e he
        exact h e he
      exact (not_lt_of_ge ((Finset.card_le_card hsub).trans hused)) (hmono c)
    have heSelected : (ω e).val < C :=
      (mem_selectedPairMonochromaticEdges.mp heMono).1
    let e₀ : H₀.Edge := ⟨e, heSelected⟩
    have heDeleted : e₀ ∈ deleted := by
      apply H₀.mem_deleteEdges.mpr
      intro heShort
      exact heNotUsed (Finset.mem_image.mpr ⟨e₀, heShort, rfl⟩)
    let ed : Hdel.Edge := ⟨e₀, heDeleted⟩
    have hePair : IsPairClusterEdge e :=
      (mem_selectedPairMonochromaticEdges.mp heMono).2.1
    have hedPair : ed ∈ pairEdges := by
      dsimp only [pairEdges]
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hePair⟩
    let ef : H.Edge := ⟨ed, hedPair⟩
    obtain ⟨a, hea⟩ :=
      (mem_selectedPairMonochromaticEdges.mp heMono).2.2
    refine ⟨ef, a, fun i ↦ ?_⟩
    exact hea _ (Finset.orderEmbOfFin_mem e.1 e.2 i)
  · intro ef
    have hePair : IsPairClusterEdge ef.1.1.1 := by
      exact (Finset.mem_filter.mp ef.2).2
    obtain ⟨a, b, hab, ha, hb⟩ := hePair
    refine ⟨a, b, hab, ?_, ?_⟩
    · change ((Finset.univ : Finset (Fin r)).filter
        (fun i ↦ fourBlockCluster (uniformEdgeVertex ef.1.1.1 i) = a)).card = r - 1
      calc
        _ = ((Finset.univ : Finset (Fin r)).filter
            (fun i ↦ inFourBlock a (uniformEdgeVertex ef.1.1.1 i))).card := by
          apply congrArg Finset.card
          apply Finset.ext
          intro i
          constructor
          · intro hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp hi).2⟩
          · intro hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp hi).2⟩
        _ = r - 1 := (uniformEdgeVertex_filter_card ef.1.1.1 (inFourBlock a)).trans ha
    · change ((Finset.univ : Finset (Fin r)).filter
        (fun i ↦ fourBlockCluster (uniformEdgeVertex ef.1.1.1 i) = b)).card = 1
      calc
        _ = ((Finset.univ : Finset (Fin r)).filter
            (fun i ↦ inFourBlock b (uniformEdgeVertex ef.1.1.1 i))).card := by
          apply congrArg Finset.card
          apply Finset.ext
          intro i
          constructor
          · intro hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp hi).2⟩
          · intro hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp hi).2⟩
        _ = 1 := (uniformEdgeVertex_filter_card ef.1.1.1 (inFourBlock b)).trans hb

/-- A pair-pattern edge has a unique singleton position; every other ordered
position lies in the majority cluster. -/
private theorem ordered_pairCluster_pattern {Y : Type*} {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (cluster : Y → Fin 4)
    (hr : 1 ≤ r) (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    ∃ a b : Fin 4, ∃ q : Fin r, a ≠ b ∧
      ∀ i, cluster (J.vertex e i) = if i = q then b else a := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := hpattern e
  let Sb := (Finset.univ : Finset (Fin r)).filter
    (fun i ↦ cluster (J.vertex e i) = b)
  obtain ⟨q, hSb⟩ : ∃ q : Fin r, Sb = {q} := Finset.card_eq_one.mp (by
    simpa only [Sb] using hb)
  have hqb : cluster (J.vertex e q) = b := by
    have hqmem : q ∈ Sb := by rw [hSb]; simp
    exact (Finset.mem_filter.mp hqmem).2
  let Sa := (Finset.univ : Finset (Fin r)).filter
    (fun i ↦ cluster (J.vertex e i) = a)
  have hSaCard : Sa.card = r - 1 := by simpa only [Sa] using ha
  have hsub : Sa ⊆ (Finset.univ : Finset (Fin r)).erase q := by
    intro j hj
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro hjq
    subst j
    have hqa := (Finset.mem_filter.mp hj).2
    exact hab (hqa.symm.trans hqb)
  have heraseCard : ((Finset.univ : Finset (Fin r)).erase q).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ,
      Fintype.card_fin]
  have hSa : Sa = (Finset.univ : Finset (Fin r)).erase q := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [heraseCard, hSaCard]
  refine ⟨a, b, q, hab, ?_⟩
  intro i
  by_cases hi : i = q
  · subst i
    simp [hqb]
  · rw [if_neg hi]
    have hiErase : i ∈ (Finset.univ : Finset (Fin r)).erase q :=
      Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
    have hiSa : i ∈ Sa := by simpa only [hSa] using hiErase
    exact (Finset.mem_filter.mp hiSa).2

/-- Foundation vertices, together with one `r`-cycle over each hyperedge. -/
abbrev AttachedVertex := X ⊕ (H.Edge × Fin r)

private def attachedAdj : H.AttachedVertex → H.AttachedVertex → Prop
  | .inl _, .inl _ => False
  | .inl x, .inr (e, i) => H.vertex e i = x
  | .inr (e, i), .inl x => H.vertex e i = x
  | .inr (e, i), .inr (f, j) => e = f ∧ (cycleGraph r).Adj i j

/-- The graph obtained by attaching an `r`-cycle to every hyperedge by a
perfect matching, while leaving all foundation vertices independent. -/
def attachedGraph : SimpleGraph H.AttachedVertex where
  Adj := H.attachedAdj
  symm := ⟨by
    intro u v
    cases u with
    | inl x =>
        cases v <;> simp [attachedAdj]
    | inr ei =>
        cases v with
        | inl y => simp [attachedAdj]
        | inr fj =>
            rcases ei with ⟨e, i⟩
            rcases fj with ⟨f, j⟩
            change e = f ∧ (cycleGraph r).Adj i j →
              f = e ∧ (cycleGraph r).Adj j i
            rintro ⟨hef, hij⟩
            exact ⟨hef.symm, hij.symm⟩⟩
  loopless := ⟨by
    intro u
    cases u with
    | inl x => simp [attachedAdj]
    | inr ei =>
        rcases ei with ⟨e, i⟩
        simp [attachedAdj]⟩

@[simp]
theorem attachedGraph_adj_foundation_cycle (x : X) (e : H.Edge) (i : Fin r) :
    H.attachedGraph.Adj (.inl x) (.inr (e, i)) ↔ H.vertex e i = x :=
  Iff.rfl

@[simp]
theorem attachedGraph_adj_cycle_cycle (e f : H.Edge) (i j : Fin r) :
    H.attachedGraph.Adj (.inr (e, i)) (.inr (f, j)) ↔
      e = f ∧ (cycleGraph r).Adj i j :=
  Iff.rfl

/-- Contract every attached fiber to its hyperedge vertex. -/
private def projectVertex : H.AttachedVertex → X ⊕ H.Edge
  | .inl x => .inl x
  | .inr (e, _) => .inr e

/-- The corresponding partial map on graph edges.  Internal fiber edges are
discarded; matching edges become incidence edges. -/
private noncomputable def projectEdge (a : Sym2 H.AttachedVertex) :
    Option (Sym2 (X ⊕ H.Edge)) := by
  classical
  exact if a ∈ H.attachedGraph.edgeSet ∧ ¬(a.map H.projectVertex).IsDiag then
      some (a.map H.projectVertex) else none

private theorem projectEdge_pair_some (u v : H.AttachedVertex) :
    H.projectEdge s(u, v) = some s(H.projectVertex u, H.projectVertex v) ↔
      H.attachedGraph.Adj u v ∧ H.projectVertex u ≠ H.projectVertex v := by
  classical
  simp [projectEdge]

private theorem projectEdge_injective_matching {x : X} {e : H.Edge} {i : Fin r}
    {a' : Sym2 H.AttachedVertex} {b : Sym2 (X ⊕ H.Edge)}
    (ha : b ∈ H.projectEdge s(Sum.inl x, Sum.inr (e, i)))
    (ha' : b ∈ H.projectEdge a') :
    s(Sum.inl x, Sum.inr (e, i)) = a' := by
  classical
  simp only [Option.mem_def] at ha ha'
  simp [projectEdge, attachedGraph, attachedAdj, projectVertex] at ha
  revert ha'
  refine Sym2.inductionOn a' ?_
  intro u' v' ha'
  cases u' with
  | inl x' =>
      cases v' with
      | inl y' => simp [projectEdge, attachedGraph, attachedAdj] at ha'
      | inr fj =>
          rcases fj with ⟨f, j⟩
          simp [projectEdge, attachedGraph, attachedAdj, projectVertex] at ha'
          have heq : s(Sum.inl x, Sum.inr e) = s(Sum.inl x', Sum.inr f) :=
            ha.2.trans ha'.2.symm
          rcases Sym2.eq_iff.mp heq with h | h
          · have hxf : x = x' := Sum.inl.inj h.1
            have hef : e = f := Sum.inr.inj h.2
            subst x'; subst f
            have hij : i = j := (H.vertex e).injective (ha.1.trans ha'.1.symm)
            subst j
            rfl
          · simp at h
  | inr fj =>
      rcases fj with ⟨f, j⟩
      cases v' with
      | inl x' =>
          simp [projectEdge, attachedGraph, attachedAdj, projectVertex] at ha'
          have heq : s(Sum.inl x, Sum.inr e) = s(Sum.inr f, Sum.inl x') :=
            ha.2.trans ha'.2.symm
          rcases Sym2.eq_iff.mp heq with h | h
          · simp at h
          · have hxf : x = x' := Sum.inl.inj h.1
            have hef : e = f := Sum.inr.inj h.2
            subst x'; subst f
            have hij : i = j := (H.vertex e).injective (ha.1.trans ha'.1.symm)
            subst j
            exact Sym2.eq_swap
      | inr fk =>
          simp [projectEdge, attachedGraph, attachedAdj, projectVertex] at ha'
          exact (ha'.1.2 ha'.1.1.1).elim

private theorem projectEdge_injective_on_some {a a' : Sym2 H.AttachedVertex}
    {b : Sym2 (X ⊕ H.Edge)} (ha : b ∈ H.projectEdge a) (ha' : b ∈ H.projectEdge a') :
    a = a' := by
  classical
  revert ha ha'
  refine Sym2.inductionOn a ?_
  intro u v ha ha'
  cases u with
  | inl x =>
      cases v with
      | inl y => simp [projectEdge, attachedGraph, attachedAdj] at ha
      | inr ei =>
          rcases ei with ⟨e, i⟩
          exact projectEdge_injective_matching H ha ha'
  | inr ei =>
      rcases ei with ⟨e, i⟩
      cases v with
      | inl x =>
          exact Sym2.eq_swap.trans (projectEdge_injective_matching H (Sym2.eq_swap ▸ ha) ha')
      | inr fj =>
          simp [projectEdge, attachedGraph, attachedAdj, projectVertex] at ha
          exact (ha.1.2 ha.1.1.1).elim

private theorem incidence_adj_projectVertex_of_ne {u v : H.AttachedVertex}
    (huv : H.attachedGraph.Adj u v) (hne : H.projectVertex u ≠ H.projectVertex v) :
    H.incidenceGraph.Adj (H.projectVertex u) (H.projectVertex v) := by
  cases u with
  | inl x =>
      cases v with
      | inl y => simp [attachedGraph, attachedAdj] at huv
      | inr ei =>
          rcases ei with ⟨e, i⟩
          exact ⟨i, huv⟩
  | inr ei =>
      rcases ei with ⟨e, i⟩
      cases v with
      | inl x => exact ⟨i, huv⟩
      | inr fj =>
          rcases fj with ⟨f, j⟩
          exact (hne (congrArg Sum.inr huv.1)).elim

/-- Project an attached walk to the incidence graph, suppressing precisely the
steps internal to a fiber. -/
private def projectWalk [DecidableEq X] [DecidableEq H.Edge] {u v : H.AttachedVertex} :
    H.attachedGraph.Walk u v →
      H.incidenceGraph.Walk (H.projectVertex u) (H.projectVertex v)
  | .nil => .nil
  | @SimpleGraph.Walk.cons _ _ _ w _ huw p =>
      if h : H.projectVertex u = H.projectVertex w then
        (projectWalk p).copy h.symm rfl
      else
        .cons (H.incidence_adj_projectVertex_of_ne huw h) (projectWalk p)

private theorem edges_projectWalk [DecidableEq X] [DecidableEq H.Edge]
    {u v : H.AttachedVertex} (p : H.attachedGraph.Walk u v) :
    (projectWalk H p).edges = p.edges.filterMap H.projectEdge := by
  classical
  induction p with
  | nil => rfl
  | @cons u w v huw p ih =>
      simp only [projectWalk]
      split_ifs with heq
      · rw [SimpleGraph.Walk.edges_copy, ih, SimpleGraph.Walk.edges_cons,
          List.filterMap_cons]
        have hedge : H.projectEdge s(u, w) = none := by
          simp [projectEdge, huw, heq]
        rw [hedge]
      · rw [SimpleGraph.Walk.edges_cons, ih, SimpleGraph.Walk.edges_cons,
          List.filterMap_cons]
        rw [(H.projectEdge_pair_some u w).2 ⟨huw, heq⟩]

private theorem projectWalk_isTrail [DecidableEq X] [DecidableEq H.Edge]
    {u v : H.AttachedVertex} {p : H.attachedGraph.Walk u v} (hp : p.IsTrail) :
    (projectWalk H p).IsTrail := by
  constructor
  rw [edges_projectWalk]
  exact hp.edges_nodup.filterMap fun a a' b hb hb' ↦
    projectEdge_injective_on_some H hb hb'

private theorem projectWalk_length_le [DecidableEq X] [DecidableEq H.Edge]
    {u v : H.AttachedVertex} (p : H.attachedGraph.Walk u v) :
    (projectWalk H p).length ≤ p.length := by
  rw [← p.length_edges, ← (projectWalk H p).length_edges, edges_projectWalk]
  exact List.length_filterMap_le _ _

private theorem projectWalk_ne_nil_of_foundation_mem [DecidableEq X]
    [DecidableEq H.Edge] {u : H.AttachedVertex} {c : H.attachedGraph.Walk u u}
    (hc : c.IsCycle) {x : X} (hx : Sum.inl x ∈ c.support) :
    projectWalk H c ≠ .nil := by
  obtain ⟨a, ha, hxa⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hxa
  have hadj : H.attachedGraph.Adj (Sum.inl x) w := c.adj_of_mem_edges ha
  have hne : H.projectVertex (Sum.inl x) ≠ H.projectVertex w := by
    cases w with
    | inl y => simp [attachedGraph, attachedAdj] at hadj
    | inr ei => simp [projectVertex]
  have hproject : H.projectEdge s(Sum.inl x, w) =
      some s(H.projectVertex (Sum.inl x), H.projectVertex w) :=
    (H.projectEdge_pair_some _ _).2 ⟨hadj, hne⟩
  have hmem : s(H.projectVertex (Sum.inl x), H.projectVertex w) ∈
      (projectWalk H c).edges := by
    rw [edges_projectWalk, List.mem_filterMap]
    exact ⟨s(Sum.inl x, w), ha, hproject⟩
  intro hnil
  rw [hnil] at hmem
  simpa using hmem

private theorem cycleGraph_isCycles (hr : 3 ≤ r) : (cycleGraph r).IsCycles := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 3 :=
    ⟨r - 3, (Nat.sub_add_cancel hr).symm⟩
  intro v hv
  rw [cycleGraph_neighborSet]
  apply Set.ncard_pair
  intro h
  have hdegree := cycleGraph_degree_three_le (n := n) (v := v)
  rw [SimpleGraph.degree, cycleGraph_neighborFinset, h] at hdegree
  simpa using hdegree

/-- In a finite connected graph of degree two, every simple cycle uses all
vertices. -/
private theorem card_le_cycle_length {Y : Type*} [Fintype Y] {G : SimpleGraph Y}
    [G.LocallyFinite] (hconn : G.Connected) (hcycles : G.IsCycles)
    {u : Y} {c : G.Walk u u} (hc : c.IsCycle) : Fintype.card Y ≤ c.length := by
  classical
  have hclosed {a b : Y} (ha : a ∈ c.support) (hab : G.Adj a b) : b ∈ c.support := by
    rw [← c.mem_verts_toSubgraph]
    have ha' : a ∈ c.toSubgraph.verts := c.mem_verts_toSubgraph.mpr ha
    exact c.toSubgraph.edge_vert ((hc.adj_toSubgraph_iff_of_isCycles hcycles ha' b).2 hab).symm
  have hreached {a b : Y} (q : G.Walk a b) (ha : a ∈ c.support) : b ∈ c.support := by
    induction q with
    | nil => exact ha
    | cons hab q ih => exact ih (hclosed ha hab)
  have hall (v : Y) : v ∈ c.support := by
    obtain ⟨q⟩ := hconn u v
    exact hreached q c.start_mem_support
  have hallTail (v : Y) : v ∈ c.support.tail := by
    by_cases hv : v = u
    · subst v
      exact c.end_mem_tail_support hc.not_nil
    · rw [← c.cons_tail_support] at hall
      exact (List.mem_cons.mp (hall v)).resolve_left hv
  calc
    Fintype.card Y = Finset.univ.card := Finset.card_univ.symm
    _ ≤ c.support.tail.toFinset.card := Finset.card_le_card (by
      intro v hv
      simpa using hallTail v)
    _ = c.support.tail.length := List.toFinset_card_of_nodup hc.support_nodup
    _ = c.length := by rw [List.length_tail, c.length_support]; omega

private def fiberMap (e : H.Edge) (i : Fin r) : H.AttachedVertex := .inr (e, i)

private def fiberSet (e : H.Edge) : Set H.AttachedVertex := Set.range (H.fiberMap e)

private noncomputable def fiberEquiv (e : H.Edge) : Fin r ≃ H.fiberSet e :=
  Equiv.ofInjective (H.fiberMap e) (by
    intro i j hij
    simpa [fiberMap] using hij)

private noncomputable def fiberIso (e : H.Edge) :
    cycleGraph r ≃g H.attachedGraph.induce (H.fiberSet e) :=
  { H.fiberEquiv e with
    map_rel_iff' := by
      intro i j
      change (e = e ∧ (cycleGraph r).Adj i j) ↔ (cycleGraph r).Adj i j
      simp }

private theorem walk_support_subset_fiber {u v : H.AttachedVertex}
    (p : H.attachedGraph.Walk u v) {e : H.Edge} {i : Fin r}
    (hu : u = H.fiberMap e i) (hno : ∀ x : X, Sum.inl x ∉ p.support) :
    ∀ z ∈ p.support, z ∈ H.fiberSet e := by
  induction p generalizing e i with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact ⟨i, hu.symm⟩
  | @cons u w v huw p ih =>
      have hnoTail : ∀ x : X, Sum.inl x ∉ p.support := by
        intro x hx
        exact hno x (List.mem_cons_of_mem _ hx)
      have hwFiber : ∃ j : Fin r, w = H.fiberMap e j := by
        cases w with
        | inl x => exact (hno x (by simp)).elim
        | inr fj =>
            rcases fj with ⟨f, j⟩
            have huw' : H.attachedGraph.Adj (H.fiberMap e i) (Sum.inr (f, j)) := hu ▸ huw
            have hef : e = f := huw'.1
            subst f
            exact ⟨j, rfl⟩
      obtain ⟨j, rfl⟩ := hwFiber
      intro z hz
      rcases List.mem_cons.mp hz with hzu | hz
      · subst z
        exact ⟨i, hu.symm⟩
      · exact ih rfl hnoTail z hz

private theorem cycle_length_ge_uniformity_of_no_foundation
    {u : H.AttachedVertex} {c : H.attachedGraph.Walk u u} (hr : 3 ≤ r)
    (hc : c.IsCycle) (hno : ∀ x : X, Sum.inl x ∉ c.support) : r ≤ c.length := by
  classical
  cases u with
  | inl x => exact (hno x c.start_mem_support).elim
  | inr ei =>
      rcases ei with ⟨e, i⟩
      have hsupp : ∀ z ∈ c.support, z ∈ H.fiberSet e :=
        H.walk_support_subset_fiber c rfl hno
      let q := c.induce (H.fiberSet e) hsupp
      have hq : q.IsCycle := by
        apply SimpleGraph.Walk.IsCycle.of_map
          (f := (SimpleGraph.Embedding.induce (H.fiberSet e)).toHom)
        simpa [q] using hc
      let d := q.map (H.fiberIso e).symm.toHom
      have hd : d.IsCycle := hq.map (H.fiberIso e).symm.injective
      have hconn : (cycleGraph r).Connected := by
        rw [← Nat.sub_add_cancel (show 1 ≤ r by omega)]
        exact cycleGraph_connected
      have hcard : r ≤ d.length := by
        simpa using card_le_cycle_length hconn (cycleGraph_isCycles hr) hd
      calc
        r ≤ d.length := hcard
        _ = q.length := SimpleGraph.Walk.length_map _ _
        _ = c.length := by
          calc
            q.length = (q.map (SimpleGraph.Embedding.induce (H.fiberSet e)).toHom).length :=
              (SimpleGraph.Walk.length_map _ _).symm
            _ = c.length := by
              rw [show q.map (SimpleGraph.Embedding.induce (H.fiberSet e)).toHom = c by
                simpa [q] using c.map_induce hsupp]
              rfl

/-- O'Donnell's girth transfer.  A cycle avoiding the foundation lies in one
fiber and has length at least `r`.  Every other cycle projects to a nonempty
incidence circuit whose length cannot decrease. -/
theorem attachedGraph_girth_ge {K : ℕ} (hr : 3 ≤ r) (hKr : K ≤ r)
    (hberge : H.BergeGirthAtLeast K) (hcyclic : ¬H.attachedGraph.IsAcyclic) :
    K ≤ H.attachedGraph.girth := by
  classical
  obtain ⟨u, c, hc, hgirth⟩ := exists_girth_eq_length.mpr hcyclic
  rw [hgirth]
  by_cases hfoundation : ∃ x : X, Sum.inl x ∈ c.support
  · obtain ⟨x, hx⟩ := hfoundation
    let p := projectWalk H c
    have hpTrail : p.IsTrail := projectWalk_isTrail H hc.isCircuit.isTrail
    have hpNe : p ≠ .nil := projectWalk_ne_nil_of_foundation_mem H hc hx
    have hpCircuit : p.IsCircuit := ⟨hpTrail, hpNe⟩
    have htwoENat : (2 * K : ℕ∞) ≤ (p.length : ℕ∞) :=
      hberge.trans hpCircuit.egirth_le_length
    have htwo : 2 * K ≤ p.length := ENat.natCast_le_natCast.mp htwoENat
    have hplen : p.length ≤ c.length := projectWalk_length_le H c
    omega
  · have hno : ∀ x : X, Sum.inl x ∉ c.support := by simpa using hfoundation
    exact hKr.trans (cycle_length_ge_uniformity_of_no_foundation H hr hc hno)

/-- The cycle over one hyperedge maps homomorphically into the attached graph. -/
def fiberHom (e : H.Edge) : cycleGraph r →g H.attachedGraph where
  toFun i := .inr (e, i)
  map_rel' := by simp

/-- An odd attached cycle forbids a monochromatic foundation hyperedge in any
three-coloring. -/
theorem attachedGraph_not_colorable_three (hr : 3 ≤ r) (hodd : Odd r)
    (hH : H.NotThreeColorable) : ¬H.attachedGraph.Colorable 3 := by
  rintro ⟨C⟩
  obtain ⟨e, a, hea⟩ := hH (fun x ↦ C (.inl x))
  have havoid (i : Fin r) : C (.inr (e, i)) ≠ a := by
    have hne := C.valid (H.attachedGraph_adj_foundation_cycle (H.vertex e i) e i |>.2 rfl)
    rw [hea i] at hne
    exact hne.symm
  let A := {b : Fin 3 // b ≠ a}
  have hcard : Fintype.card A = 2 := by
    simp [A]
  let q : A ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  have cycleColoring : (cycleGraph r).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun i ↦ q ⟨C (.inr (e, i)), havoid i⟩) (by
      intro i j hij hsame
      have hsub : (⟨C (.inr (e, i)), havoid i⟩ : A) =
          ⟨C (.inr (e, j)), havoid j⟩ := q.injective hsame
      exact C.valid ((H.fiberHom e).map_rel hij) (congrArg Subtype.val hsub))
  have hle : (cycleGraph r).chromaticNumber ≤ 2 := cycleColoring.colorable.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd r (by omega) hodd] at hle
  norm_num at hle

theorem attachedGraph_chromaticNumber_not_le_three (hr : 3 ≤ r) (hodd : Odd r)
    (hH : H.NotThreeColorable) : ¬H.attachedGraph.chromaticNumber ≤ 3 := by
  intro hle
  exact H.attachedGraph_not_colorable_three hr hodd hH
    (chromaticNumber_le_iff_colorable.mp hle)

/-- Deleting hyperedges gives an induced embedding of attached graphs. -/
def restrictEdgesEmbedding (s : Finset H.Edge) :
    (H.restrictEdges s).attachedGraph ↪g H.attachedGraph where
  toFun
    | .inl x => .inl x
    | .inr (e, i) => .inr (e.1, i)
  inj' := by
    intro u v huv
    cases u with
    | inl x =>
        cases v with
        | inl y => simpa using huv
        | inr fj => simp at huv
    | inr ei =>
        cases v with
        | inl y => simp at huv
        | inr fj =>
            rcases ei with ⟨e, i⟩
            rcases fj with ⟨f, j⟩
            simp only [Sum.inr.injEq, Prod.mk.injEq] at huv ⊢
            exact ⟨Subtype.ext huv.1, huv.2⟩
  map_rel_iff' := by
    intro u v
    cases u with
    | inl x =>
        cases v with
        | inl y =>
            change False ↔ False
            simp
        | inr fj =>
            rcases fj with ⟨f, j⟩
            change H.vertex f.1 j = x ↔ H.vertex f.1 j = x
            rfl
    | inr ei =>
        cases v with
        | inl y =>
            rcases ei with ⟨e, i⟩
            change H.vertex e.1 i = y ↔ H.vertex e.1 i = y
            rfl
        | inr fj =>
            rcases ei with ⟨e, i⟩
            rcases fj with ⟨f, j⟩
            change e.1 = f.1 ∧ (cycleGraph r).Adj i j ↔
              e = f ∧ (cycleGraph r).Adj i j
            constructor
            · rintro ⟨hef, hij⟩
              exact ⟨Subtype.ext hef, hij⟩
            · rintro ⟨hef, hij⟩
              exact ⟨congrArg Subtype.val hef, hij⟩

/-- Edge restriction cannot lower girth once the restricted attached graph is
known to contain an odd fiber cycle. -/
theorem girth_le_restrictEdges (s : Finset H.Edge) (hr : 3 ≤ r) (hodd : Odd r)
    (hs : (H.restrictEdges s).NotThreeColorable) :
    H.attachedGraph.girth ≤ (H.restrictEdges s).attachedGraph.girth := by
  apply (H.restrictEdgesEmbedding s).isContained.girth_le
  intro hacyclic
  have hle : (H.restrictEdges s).attachedGraph.chromaticNumber ≤ 2 :=
    hacyclic.colorable_two.chromaticNumber_le
  exact (H.restrictEdges s).attachedGraph_chromaticNumber_not_le_three hr hodd hs
    (hle.trans (by norm_num))

end OrderedUniformHypergraph

/-! ## Exact geometric base certificate -/

/-- A finite collection of open dense conditions can be met inside any
nonempty open parameter region.  This is the topological selection step used
to exclude all accidental unit pairs after the attachment maps are built. -/
private theorem finite_open_dense_avoidance {α ι : Type*} [TopologicalSpace α]
    (U : Set α) (hUopen : IsOpen U) (hUne : U.Nonempty) (s : Finset ι)
    (good : ι → Set α) (hgoodOpen : ∀ i ∈ s, IsOpen (good i))
    (hgoodDense : ∀ i ∈ s, Dense (good i)) :
    ∃ x ∈ U, ∀ i ∈ s, x ∈ good i := by
  classical
  let allGood (t : Finset ι) : Set α := {x | ∀ i ∈ t, x ∈ good i}
  have hdenseOpen (t : Finset ι) (ht : t ⊆ s) :
      Dense (allGood t) ∧ IsOpen (allGood t) := by
    induction t using Finset.induction_on with
    | empty =>
        constructor
        · simpa [allGood] using (dense_univ : Dense (Set.univ : Set α))
        · simpa [allGood] using (isOpen_univ : IsOpen (Set.univ : Set α))
    | @insert a t ha ih =>
        have hat : a ∈ s := ht (Finset.mem_insert_self a t)
        have hts : t ⊆ s := fun i hi => ht (Finset.mem_insert_of_mem hi)
        obtain ⟨hdt, hot⟩ := ih hts
        have hset : allGood (insert a t) = good a ∩ allGood t := by
          ext x
          simp [allGood]
        rw [hset]
        exact ⟨(hgoodDense a hat).inter_of_isOpen_left hdt (hgoodOpen a hat),
          (hgoodOpen a hat).inter hot⟩
  obtain ⟨hds, _⟩ := hdenseOpen s (fun _ h => h)
  obtain ⟨x, hxU, hxgood⟩ := hds.inter_open_nonempty U hUopen hUne
  exact ⟨x, hxU, by simpa [allGood] using hxgood⟩

private theorem eventually_locally_of_eventually {α : Type*} [TopologicalSpace α]
    {a : α} {P : α → Prop} (hP : ∀ᶠ x in nhds a, P x) :
    ∀ᶠ x in nhds a, ∀ᶠ y in nhds x, P y := by
  obtain ⟨s, hsP, hsOpen, has⟩ := mem_nhds_iff.mp hP
  filter_upwards [hsOpen.mem_nhds has] with x hx
  exact Filter.mem_of_superset (hsOpen.mem_nhds hx) hsP

/-- Abstract faithful-selection lemma.  Once a parameterized family realizes
every intended edge, it suffices that injectivity and nonedge conditions are
open dense for each of the finitely many vertex pairs. -/
private theorem faithfulEmbedding_of_openDense_family {X α : Type*} [Fintype X]
    [TopologicalSpace α] (G : SimpleGraph X) (U : Set α) (hUopen : IsOpen U)
    (hUne : U.Nonempty) (p : α → X → Plane)
    (hedge : ∀ t ∈ U, ∀ x y, G.Adj x y → Dist.dist (p t x) (p t y) = 1)
    (hgoodOpen : ∀ x y, IsOpen {t |
      (x = y ∨ p t x ≠ p t y) ∧ (G.Adj x y ∨ Dist.dist (p t x) (p t y) ≠ 1)})
    (hgoodDense : ∀ x y, Dense {t |
      (x = y ∨ p t x ≠ p t y) ∧ (G.Adj x y ∨ Dist.dist (p t x) (p t y) ≠ 1)}) :
    FaithfulUnitDistanceEmbedding G := by
  classical
  let good : X × X → Set α := fun q => {t |
    (q.1 = q.2 ∨ p t q.1 ≠ p t q.2) ∧
      (G.Adj q.1 q.2 ∨ Dist.dist (p t q.1) (p t q.2) ≠ 1)}
  obtain ⟨t, htU, ht⟩ := finite_open_dense_avoidance U hUopen hUne
    (Finset.univ : Finset (X × X)) good
    (by intro q _; exact hgoodOpen q.1 q.2)
    (by intro q _; exact hgoodDense q.1 q.2)
  have htgood (x y : X) :
      (x = y ∨ p t x ≠ p t y) ∧
        (G.Adj x y ∨ Dist.dist (p t x) (p t y) ≠ 1) := by
    exact ht (x, y) (Finset.mem_univ _)
  have hinj : Function.Injective (p t) := by
    intro x y hxy
    by_contra hne
    exact (htgood x y).1.resolve_left hne hxy
  refine ⟨⟨p t, hinj⟩, ?_⟩
  intro x y
  constructor
  · intro hdist
    rcases (htgood x y).2 with hadj | hne
    · exact hadj
    · exact (hne hdist).elim
  · exact hedge t htU x y

/-- Continuous realization families automatically satisfy the openness half of
the faithful-selection criterion. -/
private theorem faithfulEmbedding_of_dense_continuous_family {X α : Type*} [Fintype X]
    [TopologicalSpace α] (G : SimpleGraph X) (U : Set α) (hUopen : IsOpen U)
    (hUne : U.Nonempty) (p : α → X → Plane)
    (hcont : ∀ x, Continuous fun t => p t x)
    (hedge : ∀ t ∈ U, ∀ x y, G.Adj x y → Dist.dist (p t x) (p t y) = 1)
    (hgoodDense : ∀ x y, Dense {t |
      (x = y ∨ p t x ≠ p t y) ∧ (G.Adj x y ∨ Dist.dist (p t x) (p t y) ≠ 1)}) :
    FaithfulUnitDistanceEmbedding G := by
  apply faithfulEmbedding_of_openDense_family G U hUopen hUne p hedge
  · intro x y
    have hinjectiveOpen : IsOpen {t : α | x = y ∨ p t x ≠ p t y} := by
      by_cases hxy : x = y
      · simp [hxy]
      · simpa [hxy] using isOpen_ne_fun (hcont x) (hcont y)
    have hnonedgeOpen :
        IsOpen {t : α | G.Adj x y ∨ Dist.dist (p t x) (p t y) ≠ 1} := by
      by_cases hxy : G.Adj x y
      · simp [hxy]
      · have hd : Continuous fun t : α => Dist.dist (p t x) (p t y) :=
          (hcont x).dist (hcont y)
        simpa [hxy] using isOpen_ne.preimage hd
    exact hinjectiveOpen.inter hnonedgeOpen
  · exact hgoodDense

/-- A regular scalar level set has empty interior.  This is the local calculus
criterion used to prove that every forbidden distance equation has dense
complement in the attachment parameter space. -/
private theorem interior_levelSet_eq_empty_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (c : ℝ)
    (hregular : ∀ x, f x = c → ∃ f' : E →L[ℝ] ℝ, HasFDerivAt f f' x ∧ f' ≠ 0) :
    interior {x | f x = c} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hlevel : f x = c := (show x ∈ {x : E | f x = c} from interior_subset hx)
  obtain ⟨f', hf', hf'ne⟩ := hregular x hlevel
  have hevent : f =ᶠ[nhds x] fun _ => c := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (show y ∈ {x : E | f x = c} from interior_subset hy)
  have hzero : HasFDerivAt f 0 x :=
    hasFDerivAt_zero_of_eventually_const (𝕜 := ℝ) c hevent
  exact hf'ne (hf'.unique hzero)

private theorem dense_ne_level_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (c : ℝ)
    (hregular : ∀ x, f x = c → ∃ f' : E →L[ℝ] ℝ, HasFDerivAt f f' x ∧ f' ≠ 0) :
    Dense {x | f x ≠ c} := by
  have h := interior_levelSet_eq_empty_of_fderiv_ne_zero f c hregular
  have hd : Dense ({x | f x = c} : Set E)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp h
  simpa only [Set.compl_setOf] using hd

/-- Relative version of regular-level avoidance.  The derivative is only
required on an open parameter region; its non-level locus is then dense in
that region's subtype topology. -/
private theorem dense_ne_level_on_open_of_fderiv_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : Set E) (hNopen : IsOpen N) (f : E → F) (c : F)
    (hregular : ∀ x ∈ N, f x = c →
      ∃ f' : E →L[ℝ] F, HasFDerivAt f f' x ∧ f' ≠ 0) :
    Dense {x : N | f x.1 ≠ c} := by
  have hinterior : interior ({x : E | f x = c} ∩ N) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxmem : x ∈ {x : E | f x = c} ∩ N := interior_subset hx
    obtain ⟨f', hf', hf'ne⟩ := hregular x hxmem.2 hxmem.1
    have hevent : f =ᶠ[nhds x] fun _ => c := by
      filter_upwards [isOpen_interior.mem_nhds hx] with y hy
      exact (interior_subset hy).1
    have hzero : HasFDerivAt f 0 x :=
      hasFDerivAt_zero_of_eventually_const (𝕜 := ℝ) c hevent
    exact hf'ne (hf'.unique hzero)
  have hd : Dense (({x : E | f x = c} ∩ N)ᶜ) :=
    interior_eq_empty_iff_dense_compl.mp hinterior
  have hpull := hd.preimage hNopen.isOpenMap_subtype_val
  have heq : ((Subtype.val : N → E) ⁻¹' (({x : E | f x = c} ∩ N)ᶜ)) =
      {x : N | f x.1 ≠ c} := by
    ext x
    simp [x.2]
  rwa [heq] at hpull

/-- Avoid finitely many regular levels while retaining a nonempty open ambient
region.  Keeping an open region, rather than merely choosing one point, lets
the argument impose collision-freeness, then general position, then the
faithful nonedge conditions in three successive passes. -/
private theorem finite_regular_avoidance_open_region
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
    (N : Set E) (hNopen : IsOpen N) (hNne : N.Nonempty)
    (f : ι → E → F) (c : ι → F)
    (hderiv : ∀ i x, x ∈ N → ∃ f' : E →L[ℝ] F, HasFDerivAt (f i) f' x)
    (hregular : ∀ i x, x ∈ N → f i x = c i →
      ∃ f' : E →L[ℝ] F, HasFDerivAt (f i) f' x ∧ f' ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ U.Nonempty ∧ U ⊆ N ∧
      ∀ x ∈ U, ∀ i, f i x ≠ c i := by
  classical
  let C : Set N := {x | ∀ i, f i x.1 ≠ c i}
  have hgoodOpen (i : ι) : IsOpen {x : N | f i x.1 ≠ c i} := by
    have hcont : Continuous (fun x : N => f i x.1) := by
      rw [continuous_iff_continuousAt]
      intro x
      obtain ⟨f', hf'⟩ := hderiv i x.1 x.2
      exact hf'.continuousAt.comp continuous_subtype_val.continuousAt
    simpa using isOpen_ne.preimage hcont
  have hCopen : IsOpen C := by
    have hCeq : C = ⋂ i, {x : N | f i x.1 ≠ c i} := by
      ext x
      simp [C]
    rw [hCeq]
    exact isOpen_iInter_of_finite hgoodOpen
  have hgoodDense (i : ι) : Dense {x : N | f i x.1 ≠ c i} :=
    dense_ne_level_on_open_of_fderiv_ne_zero N hNopen (f i) (c i)
      (hregular i)
  obtain ⟨x, _, hx⟩ := finite_open_dense_avoidance (Set.univ : Set N)
    isOpen_univ ⟨⟨hNne.some, hNne.some_mem⟩, Set.mem_univ _⟩
    (Finset.univ : Finset ι) (fun i => {x : N | f i x.1 ≠ c i})
    (fun i _ => hgoodOpen i) (fun i _ => hgoodDense i)
  have hxC : x ∈ C := by
    intro i
    exact hx i (Finset.mem_univ i)
  let U : Set E := Subtype.val '' C
  refine ⟨U, hNopen.isOpenMap_subtype_val C hCopen, ⟨x.1, ⟨x, hxC, rfl⟩⟩,
    ?_, ?_⟩
  · rintro y ⟨z, _, rfl⟩
    exact z.2
  · rintro y ⟨z, hzC, rfl⟩ i
    exact hzC i

/-- Local monotonicity for the degree-two paths occurring in the stress
argument: two collinear unit steps in an injective path must have the same
oriented step vector. -/
private theorem collinear_unit_steps_same_direction {a b c : Plane}
    (hab : Dist.dist a b = 1) (hbc : Dist.dist b c = 1) (hac : a ≠ c)
    (hcol : ∃ t : ℝ, c - b = t • (b - a)) :
    c - b = b - a := by
  obtain ⟨t, ht⟩ := hcol
  have hx : ‖b - a‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hab
  have hy : ‖c - b‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hbc
  have habs : |t| = 1 := by
    have hn := congrArg norm ht
    rw [norm_smul, Real.norm_eq_abs, hx, mul_one, hy] at hn
    exact hn.symm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with htOne | htNeg
  · simpa [htOne] using ht
  · have hcb : c - b = -(b - a) := by simpa [htNeg] using ht
    have hca : c = a := by
      apply sub_eq_zero.mp
      calc
        c - a = (c - b) + (b - a) := by abel
        _ = -(b - a) + (b - a) := by rw [hcb]
        _ = 0 := neg_add_cancel _
    exact (hac hca.symm).elim

/-- In particular, the endpoints of two such steps are distance two apart. -/
private theorem collinear_unit_steps_do_not_reverse {a b c : Plane}
    (hab : Dist.dist a b = 1) (hbc : Dist.dist b c = 1) (hac : a ≠ c)
    (hcol : ∃ t : ℝ, c - b = t • (b - a)) :
    Dist.dist a c = 2 := by
  have hdir := collinear_unit_steps_same_direction hab hbc hac hcol
  have hx : ‖b - a‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hab
  have hca : c - a = (2 : ℝ) • (b - a) := by
    calc
      c - a = (c - b) + (b - a) := by abel
      _ = (b - a) + (b - a) := by rw [hdir]
      _ = (2 : ℝ) • (b - a) := by module
  rw [dist_eq_norm, norm_sub_rev, hca, norm_smul, Real.norm_eq_abs, hx]
  norm_num

/-- Every step of an injective collinear unit chain has the same orientation
as its first step.  This is the propagation lemma used at the internal
degree-two vertices of a stressed path. -/
private theorem collinear_unit_chain_same_steps (p : ℕ → Plane) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hinj : Function.Injective p)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i)) :
    ∀ i < n, p (i + 1) - p i = p 1 - p 0 := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
      have hne : p i ≠ p (i + 2) := hinj.ne (by omega)
      have hdir := collinear_unit_steps_same_direction
        (hunit i (by omega)) (hunit (i + 1) hi) hne (hcol i (by omega))
      exact hdir.trans (ih (by omega))

/-- Hence an injective collinear chain of `n` unit edges has endpoint distance
exactly `n`. -/
private theorem dist_endpoints_of_collinear_unit_chain (p : ℕ → Plane) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hinj : Function.Injective p)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i)) :
    Dist.dist (p 0) (p n) = n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hstep := collinear_unit_chain_same_steps p n hunit hinj hcol
  have hpos : ∀ k ≤ n, p k - p 0 = (k : ℝ) • (p 1 - p 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          p (k + 1) - p 0 = (p (k + 1) - p k) + (p k - p 0) := by abel
          _ = (p 1 - p 0) + (p k - p 0) := by rw [hstep k (by omega)]
          _ = (p 1 - p 0) + (k : ℝ) • (p 1 - p 0) := by rw [ih (by omega)]
          _ = ((k + 1 : ℕ) : ℝ) • (p 1 - p 0) := by
            norm_num [Nat.cast_add, Nat.cast_one]
            module
  have hfirst : ‖p 1 - p 0‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hunit 0 hnpos
  rw [dist_eq_norm, norm_sub_rev, hpos n le_rfl, norm_smul, Real.norm_eq_abs, hfirst,
    mul_one]
  simp

/-- The bounded form needed for paths cut out of a cyclic indexing. -/
private theorem collinear_unit_chain_same_steps_on (p : ℕ → Plane) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i)) :
    ∀ i < n, p (i + 1) - p i = p 1 - p 0 := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
      have hne : p i ≠ p (i + 2) := by
        intro heq
        have := hinj i (by omega) (i + 2) (by omega) heq
        omega
      have hdir := collinear_unit_steps_same_direction
        (hunit i (by omega)) (hunit (i + 1) hi) hne (hcol i (by omega))
      exact hdir.trans (ih (by omega))

private theorem dist_endpoints_of_collinear_unit_chain_on (p : ℕ → Plane) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, p i = p j → i = j)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i)) :
    Dist.dist (p 0) (p n) = n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hstep := collinear_unit_chain_same_steps_on p n hunit hinj hcol
  have hpos : ∀ k ≤ n, p k - p 0 = (k : ℝ) • (p 1 - p 0) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          p (k + 1) - p 0 = (p (k + 1) - p k) + (p k - p 0) := by abel
          _ = (p 1 - p 0) + (p k - p 0) := by rw [hstep k (by omega)]
          _ = (p 1 - p 0) + (k : ℝ) • (p 1 - p 0) := by rw [ih (by omega)]
          _ = ((k + 1 : ℕ) : ℝ) • (p 1 - p 0) := by
            norm_num [Nat.cast_add, Nat.cast_one]
            module
  have hfirst : ‖p 1 - p 0‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hunit 0 hnpos
  rw [dist_eq_norm, norm_sub_rev, hpos n le_rfl, norm_smul, Real.norm_eq_abs,
    hfirst, mul_one]
  simp

/-- Two injective collinear unit chains with the same endpoints have the same
number of edges.  Therefore they cannot form an odd cycle. -/
private theorem no_odd_union_of_collinear_unit_chains
    (p q : ℕ → Plane) (m n : ℕ)
    (hpunit : ∀ i < m, Dist.dist (p i) (p (i + 1)) = 1)
    (hqunit : ∀ i < n, Dist.dist (q i) (q (i + 1)) = 1)
    (hpinj : Function.Injective p) (hqinj : Function.Injective q)
    (hpcol : ∀ i, i + 2 ≤ m →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i))
    (hqcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, q (i + 2) - q (i + 1) = t • (q (i + 1) - q i))
    (hstart : p 0 = q 0) (hend : p m = q n)
    (hodd : Odd (m + n)) : False := by
  have hpdist := dist_endpoints_of_collinear_unit_chain p m hpunit hpinj hpcol
  have hqdist := dist_endpoints_of_collinear_unit_chain q n hqunit hqinj hqcol
  have hmnReal : (m : ℝ) = n := by
    calc
      (m : ℝ) = Dist.dist (p 0) (p m) := hpdist.symm
      _ = Dist.dist (q 0) (q n) := by rw [hstart, hend]
      _ = n := hqdist
  have hmn : m = n := by exact_mod_cast hmnReal
  obtain ⟨k, hk⟩ := hodd
  omega

/-- A nonzero stress coefficient propagates along a unit path.  The balance
equation is written with consistently oriented edge vectors. -/
private theorem path_stress_coefficients_nonzero
    (p : ℕ → Plane) (a : ℕ → ℝ) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hbalance : ∀ i, i + 1 < n →
      a i • (p (i + 1) - p i) =
        a (i + 1) • (p (i + 2) - p (i + 1)))
    (ha0 : a 0 ≠ 0) :
    ∀ i < n, a i ≠ 0 := by
  intro i hi
  induction i with
  | zero => exact ha0
  | succ i ih =>
      have hprev : a i ≠ 0 := ih (by omega)
      have hstep : p (i + 1) - p i ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        have hu := hunit i (by omega)
        rw [heq] at hu
        simpa using hu
      intro hzero
      have hb := hbalance i hi
      rw [hzero, zero_smul] at hb
      rcases smul_eq_zero.mp hb with h | h
      · exact hprev h
      · exact hstep h

/-- Consequently every internal balance equation of a path carrying a
nonzero stress forces its two consecutive unit edges to be collinear. -/
private theorem path_stress_forces_collinear
    (p : ℕ → Plane) (a : ℕ → ℝ) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hbalance : ∀ i, i + 1 < n →
      a i • (p (i + 1) - p i) =
        a (i + 1) • (p (i + 2) - p (i + 1)))
    (ha0 : a 0 ≠ 0) :
    ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i) := by
  have hnonzero := path_stress_coefficients_nonzero p a n hunit hbalance ha0
  intro i hi
  have hnext : a (i + 1) ≠ 0 := hnonzero (i + 1) (by omega)
  refine ⟨a i / a (i + 1), ?_⟩
  calc
    p (i + 2) - p (i + 1) =
        (a (i + 1))⁻¹ • (a (i + 1) • (p (i + 2) - p (i + 1))) := by
      rw [inv_smul_smul₀ hnext]
    _ = (a (i + 1))⁻¹ • (a i • (p (i + 1) - p i)) := by
      rw [hbalance i (by omega)]
    _ = (a i / a (i + 1)) • (p (i + 1) - p i) := by
      simp [smul_smul, div_eq_mul_inv, mul_comm]

private theorem path_steps_collinear_with_first
    (p : ℕ → Plane) (n : ℕ)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i)) :
    ∀ i < n, ∃ t : ℝ, p (i + 1) - p i = t • (p 1 - p 0) := by
  intro i hi
  induction i with
  | zero => exact ⟨1, by simp⟩
  | succ i ih =>
      obtain ⟨a, ha⟩ := hcol i (by omega)
      obtain ⟨b, hb⟩ := ih (by omega)
      refine ⟨a * b, ?_⟩
      rw [ha, hb, smul_smul]

/-- A closed chain of unit segments which is contained in a line has even
length.  Backtracking is allowed; the proof counts forward and backward
unit steps. -/
private theorem closed_collinear_unit_chain_even
    (p : ℕ → Plane) (n : ℕ)
    (hunit : ∀ i < n, Dist.dist (p i) (p (i + 1)) = 1)
    (hcol : ∀ i, i + 2 ≤ n →
      ∃ t : ℝ, p (i + 2) - p (i + 1) = t • (p (i + 1) - p i))
    (hclosed : p n = p 0) : Even n := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨0, by simp⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hfirst : ‖p 1 - p 0‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hunit 0 hnpos
  have hparallel := path_steps_collinear_with_first p n hcol
  have hsign : ∀ i < n,
      p (i + 1) - p i = p 1 - p 0 ∨
        p (i + 1) - p i = -(p 1 - p 0) := by
    intro i hi
    obtain ⟨t, ht⟩ := hparallel i hi
    have hstepNorm : ‖p (i + 1) - p i‖ = 1 := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using hunit i hi
    have habs : |t| = 1 := by
      have hnorm := congrArg norm ht
      rw [norm_smul, Real.norm_eq_abs, hfirst, mul_one, hstepNorm] at hnorm
      exact hnorm.symm
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with ht1 | htm1
    · left
      simpa [ht1] using ht
    · right
      simpa [htm1] using ht
  let forward : Finset ℕ := (Finset.range n).filter fun i =>
    p (i + 1) - p i = p 1 - p 0
  have hstep (i : ℕ) (hi : i ∈ Finset.range n) :
      p (i + 1) - p i =
        (if i ∈ forward then (1 : ℝ) else -1) • (p 1 - p 0) := by
    have hil : i < n := Finset.mem_range.mp hi
    by_cases hif : i ∈ forward
    · rw [if_pos hif, one_smul]
      exact (Finset.mem_filter.mp hif).2
    · rw [if_neg hif]
      have hnforward : p (i + 1) - p i ≠ p 1 - p 0 := by
        intro heq
        exact hif (Finset.mem_filter.mpr ⟨hi, heq⟩)
      simpa using (hsign i hil).resolve_left hnforward
  have htel : (∑ i ∈ Finset.range n, (p (i + 1) - p i)) = p n - p 0 := by
    exact Finset.sum_range_sub p n
  have hvsum :
      (∑ i ∈ Finset.range n, (if i ∈ forward then (1 : ℝ) else -1)) •
          (p 1 - p 0) = 0 := by
    rw [Finset.sum_smul]
    calc
      ∑ i ∈ Finset.range n,
          (if i ∈ forward then (1 : ℝ) else -1) • (p 1 - p 0) =
          ∑ i ∈ Finset.range n, (p (i + 1) - p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hstep i hi).symm
      _ = p n - p 0 := htel
      _ = 0 := by rw [hclosed, sub_self]
  have hscalar :
      (∑ i ∈ Finset.range n, (if i ∈ forward then (1 : ℝ) else -1)) = 0 := by
    rcases smul_eq_zero.mp hvsum with h | h
    · exact h
    · have : ‖p 1 - p 0‖ = 0 := by rw [h, norm_zero]
      linarith
  have hforwardSub : forward ⊆ Finset.range n := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hcard : (2 : ℝ) * forward.card = n := by
    have hsumEval :
        (∑ i ∈ Finset.range n, (if i ∈ forward then (1 : ℝ) else -1)) =
          (forward.card : ℝ) - ((Finset.range n \ forward).card : ℝ) := by
      calc
        _ = (∑ i ∈ Finset.range n \ forward,
              (if i ∈ forward then (1 : ℝ) else -1)) +
            ∑ i ∈ forward, (if i ∈ forward then (1 : ℝ) else -1) :=
          (Finset.sum_sdiff hforwardSub).symm
        _ = (forward.card : ℝ) - ((Finset.range n \ forward).card : ℝ) := by
          have hfor : (∑ i ∈ forward,
              (if i ∈ forward then (1 : ℝ) else -1)) = forward.card := by
            calc
              _ = ∑ _i ∈ forward, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_pos hi]
              _ = forward.card := by simp
          have hback : (∑ i ∈ Finset.range n \ forward,
              (if i ∈ forward then (1 : ℝ) else -1)) =
                -((Finset.range n \ forward).card : ℝ) := by
            calc
              _ = ∑ _i ∈ Finset.range n \ forward, (-1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [if_neg (Finset.mem_sdiff.mp hi).2]
              _ = -((Finset.range n \ forward).card : ℝ) := by simp
          rw [hfor, hback]
          ring
    rw [hsumEval] at hscalar
    have hdiffCard : (Finset.range n \ forward).card = n - forward.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hforwardSub,
        Finset.card_range]
    rw [hdiffCard] at hscalar
    have hle : forward.card ≤ n := by
      simpa [Finset.card_range] using Finset.card_le_card hforwardSub
    norm_num [Nat.cast_sub hle] at hscalar ⊢
    linarith
  have hcardNat : 2 * forward.card = n := by exact_mod_cast hcard
  exact ⟨forward.card, by omega⟩

/-! The following finite-dimensional duality lemmas turn a hypothetical
hidden unit bar into a self-stress on the cycle. -/

private noncomputable def edgeFlexFunctional {r : ℕ} [NeZero r]
    (v : Fin r → Plane) (i : Fin r) : (Fin r → Plane) →ₗ[ℝ] ℝ :=
  (innerSL ℝ (v (i + 1) - v i)).toLinearMap.comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) (i + 1)) -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)

private noncomputable def chordFlexFunctional {r : ℕ}
    (v : Fin r → Plane) (i j : Fin r) : (Fin r → Plane) →ₗ[ℝ] ℝ :=
  (innerSL ℝ (v j - v i)).toLinearMap.comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) j) -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)

private noncomputable def relativeFlexFunctional {r : ℕ}
    (d : Plane) (i j : Fin r) : (Fin r → Plane) →ₗ[ℝ] ℝ :=
  (innerSL ℝ d).toLinearMap.comp
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) j) -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)

private theorem edgeFlexFunctional_apply {r : ℕ} [NeZero r]
    (v z : Fin r → Plane) (i : Fin r) :
    edgeFlexFunctional v i z =
      inner ℝ (v (i + 1) - v i) (z (i + 1) - z i) := rfl

private theorem chordFlexFunctional_apply {r : ℕ}
    (v z : Fin r → Plane) (i j : Fin r) :
    chordFlexFunctional v i j z = inner ℝ (v j - v i) (z j - z i) := rfl

private theorem relativeFlexFunctional_apply {r : ℕ}
    (d : Plane) (z : Fin r → Plane) (i j : Fin r) :
    relativeFlexFunctional d i j z = inner ℝ d (z j - z i) := rfl

private theorem relative_stress_coefficients {r : ℕ} [NeZero r]
    (v : Fin r → Plane) (d : Plane) (i j : Fin r)
    (hvanish : ∀ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) →
      relativeFlexFunctional d i j z = 0) :
    ∃ a : Fin r → ℝ,
      ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j := by
  have hker : ⨅ k, LinearMap.ker (edgeFlexFunctional v k) ≤
      LinearMap.ker (relativeFlexFunctional d i j) := by
    intro z hz
    rw [LinearMap.mem_ker]
    apply hvanish z
    have hz' : ∀ k, z ∈ LinearMap.ker (edgeFlexFunctional v k) := by
      simpa only [Submodule.mem_iInf] using hz
    intro k
    rw [← LinearMap.mem_ker]
    exact hz' k
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (mem_span_of_iInf_ker_le_ker hker)

private theorem chord_stress_coefficients {r : ℕ} [NeZero r]
    (v : Fin r → Plane) (i j : Fin r)
    (hvanish : ∀ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) →
      chordFlexFunctional v i j z = 0) :
    ∃ a : Fin r → ℝ,
      ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j := by
  have hker : ⨅ k, LinearMap.ker (edgeFlexFunctional v k) ≤
      LinearMap.ker (chordFlexFunctional v i j) := by
    intro z hz
    rw [LinearMap.mem_ker]
    apply hvanish z
    have hz' : ∀ k, z ∈ LinearMap.ker (edgeFlexFunctional v k) := by
      simpa only [Submodule.mem_iInf] using hz
    intro k
    rw [← LinearMap.mem_ker]
    exact hz' k
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (mem_span_of_iInf_ker_le_ker hker)

private theorem one_ne_zero_fin {r : ℕ} [NeZero r] (hr : 2 ≤ r) :
    (1 : Fin r) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < r)] using this

private theorem sum_edgeFlex_single {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (a : Fin r → ℝ) (k : Fin r) (q : Plane) :
    ∑ l, a l * edgeFlexFunctional v l (Pi.single k q) =
      a (k - 1) * inner ℝ (v k - v (k - 1)) q -
        a k * inner ℝ (v (k + 1) - v k) q := by
  have hpred : k - 1 ≠ k := by
    intro h
    exact one_ne_zero_fin (by omega) (sub_eq_self.mp h)
  have hpredSucc : k - 1 + 1 = k := by abel
  have hsucc : k + 1 ≠ k := by
    intro h
    have hone : (1 : Fin r) = 0 := by
      calc
        1 = (k + 1) - k := by simp
        _ = 0 := by rw [h]; simp
    exact one_ne_zero_fin (by omega) hone
  let f : Fin r → ℝ := fun l => a l * edgeFlexFunctional v l (Pi.single k q)
  have hzero : ∀ l ∈ (Finset.univ : Finset (Fin r)),
      l ∉ ({k - 1, k} : Finset (Fin r)) → f l = 0 := by
    intro l _ hl
    have hlpred : l ≠ k - 1 := by simpa using fun h => hl (by simp [h])
    have hlk : l ≠ k := by simpa using fun h => hl (by simp [h])
    have hnext : l + 1 ≠ k := by
      intro h
      exact hlpred ((eq_sub_iff_add_eq).2 h)
    simp [f, edgeFlexFunctional_apply, Pi.single_apply, hlk, hnext]
  rw [← Finset.sum_subset (by simp : ({k - 1, k} : Finset (Fin r)) ⊆
    (Finset.univ : Finset (Fin r))) hzero]
  simp [f, edgeFlexFunctional_apply, Pi.single_apply, hpred, hpredSucc, hsucc,
    inner_sub_right]
  ring

private theorem relative_stress_balance {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (d : Plane) (i j : Fin r) (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j)
    (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) :
    a (k - 1) • (v k - v (k - 1)) =
      a k • (v (k + 1) - v k) := by
  apply ext_inner_right ℝ
  intro q
  have heval := congrArg (fun L : (Fin r → Plane) →ₗ[ℝ] ℝ =>
    L (Pi.single k q)) hcoeff
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  rw [sum_edgeFlex_single hr] at heval
  simp [relativeFlexFunctional_apply, hki, hkj] at heval
  simpa only [real_inner_smul_left] using sub_eq_zero.mp heval

private theorem relative_stress_endpoint_balance {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (d : Plane) (i j : Fin r) (hij : i ≠ j)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j) :
    a (i - 1) • (v i - v (i - 1)) -
        a i • (v (i + 1) - v i) = -d := by
  apply ext_inner_right ℝ
  intro q
  have heval := congrArg (fun L : (Fin r → Plane) →ₗ[ℝ] ℝ =>
    L (Pi.single i q)) hcoeff
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  rw [sum_edgeFlex_single hr] at heval
  have hji : j ≠ i := hij.symm
  simp [relativeFlexFunctional_apply, hji, real_inner_smul_left,
    inner_sub_left, inner_neg_left] at heval ⊢
  exact heval

private theorem chord_stress_balance {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (i j : Fin r) (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) :
    a (k - 1) • (v k - v (k - 1)) =
      a k • (v (k + 1) - v k) := by
  apply ext_inner_right ℝ
  intro q
  have heval := congrArg (fun L : (Fin r → Plane) →ₗ[ℝ] ℝ =>
    L (Pi.single k q)) hcoeff
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  rw [sum_edgeFlex_single hr] at heval
  simp [chordFlexFunctional_apply, hki, hkj] at heval
  simpa only [real_inner_smul_left] using sub_eq_zero.mp heval

private theorem chord_stress_endpoint_nonzero {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (i j : Fin r) (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hij : Dist.dist (v i) (v j) = 1) :
    a (i - 1) ≠ 0 ∨ a i ≠ 0 := by
  by_contra h
  push_neg at h
  let d := v j - v i
  have heval := congrArg (fun L : (Fin r → Plane) →ₗ[ℝ] ℝ =>
    L (Pi.single i d)) hcoeff
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  rw [sum_edgeFlex_single hr] at heval
  rw [h.1, h.2] at heval
  simp only [zero_mul, zero_sub] at heval
  have hji : j ≠ i := by
    intro hji
    subst j
    simpa using hij
  simp [chordFlexFunctional_apply, hji, d] at heval
  have hnorm : ‖v j - v i‖ = 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hij
  have hself : inner ℝ d d = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num
  have hneg : inner ℝ (v j - v i) (v i - v j) = -1 := by
    rw [show v i - v j = -(v j - v i) by abel]
    rw [inner_neg_right, hself]
  rw [hneg] at heval
  norm_num at heval

private theorem chord_stress_endpoint_nonzero_of_ne {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (v : Fin r → Plane) (i j : Fin r) (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hij : v i ≠ v j) :
    a (i - 1) ≠ 0 ∨ a i ≠ 0 := by
  by_contra h
  push Not at h
  let d := v j - v i
  have heval := congrArg (fun L : (Fin r → Plane) →ₗ[ℝ] ℝ =>
    L (Pi.single i d)) hcoeff
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at heval
  rw [sum_edgeFlex_single hr, h.1, h.2] at heval
  simp only [zero_mul, zero_sub] at heval
  have hji : j ≠ i := by
    intro hji
    subst j
    exact hij rfl
  simp [chordFlexFunctional_apply, hji, d] at heval
  have hdne : d ≠ 0 := sub_ne_zero.mpr hij.symm
  have hself : inner ℝ d d = 0 := by
    rw [show v i - v j = -d by simp [d], inner_neg_right] at heval
    linarith
  exact (inner_self_ne_zero.mpr hdne) hself

private def forwardCyclePath {r : ℕ} [NeZero r]
    (v : Fin r → Plane) (i : Fin r) (k : ℕ) : Plane := v (i + Fin.ofNat r k)

private theorem forward_relative_stressed_arc_collinear {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (d : Plane) (i j : Fin r) (n : ℕ)
    (hncast : Fin.ofNat r n = j - i) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j)
    (hai : a i ≠ 0) :
    ∀ k, k + 2 ≤ n →
      ∃ t : ℝ,
        forwardCyclePath v i (k + 2) - forwardCyclePath v i (k + 1) =
          t • (forwardCyclePath v i (k + 1) - forwardCyclePath v i k) := by
  let p : ℕ → Plane := forwardCyclePath v i
  let b : ℕ → ℝ := fun k => a (i + Fin.ofNat r k)
  have hstepIndex (k : ℕ) :
      i + Fin.ofNat r (k + 1) = (i + Fin.ofNat r k) + 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, forwardCyclePath]
    rw [hstepIndex]
    exact hunit _
  have hneStart (k : ℕ) (hkpos : 0 < k) (hklt : k < r) :
      i + Fin.ofNat r k ≠ i := by
    intro h
    have hzero : Fin.ofNat r k = 0 := by
      apply add_left_cancel (a := i)
      simpa using h
    have hval := congrArg Fin.val hzero
    simp [Fin.ofNat, Nat.mod_eq_of_lt hklt] at hval
    omega
  have hneEnd (k : ℕ) (hklt : k < n) : i + Fin.ofNat r k ≠ j := by
    intro h
    have hcast : Fin.ofNat r k = Fin.ofNat r n := by
      rw [hncast]
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h)
    have hkR : k < r := lt_trans hklt hnlt
    have hval := congrArg Fin.val hcast
    simp [Fin.ofNat, Nat.mod_eq_of_lt hkR, Nat.mod_eq_of_lt hnlt] at hval
    omega
  have hbalance : ∀ k, k + 1 < n →
      b k • (p (k + 1) - p k) =
        b (k + 1) • (p (k + 2) - p (k + 1)) := by
    intro k hk
    let q : Fin r := i + Fin.ofNat r (k + 1)
    have hqneI : q ≠ i := hneStart (k + 1) (by omega) (by omega)
    have hqneJ : q ≠ j := hneEnd (k + 1) hk
    have hb := relative_stress_balance hr v d i j a hcoeff q hqneI hqneJ
    have hpred : q - 1 = i + Fin.ofNat r k := by
      dsimp only [q]
      rw [hstepIndex]
      abel
    have hnext : q + 1 = i + Fin.ofNat r (k + 2) := by
      dsimp only [q]
      rw [hstepIndex (k + 1)]
    rw [hpred, hnext] at hb
    dsimp only [q] at hb
    dsimp only [p, b, forwardCyclePath]
    exact hb
  have hb0 : b 0 ≠ 0 := by simpa [b] using hai
  exact path_stress_forces_collinear p b n hpunit hbalance hb0

private theorem forward_relative_stressed_arc_even_of_collision {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (d : Plane) (i j : Fin r) (n : ℕ) (hcollision : v i = v j)
    (hncast : Fin.ofNat r n = j - i) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j)
    (hai : a i ≠ 0) : Even n := by
  let p : ℕ → Plane := forwardCyclePath v i
  have hstepIndex (k : ℕ) :
      i + Fin.ofNat r (k + 1) = (i + Fin.ofNat r k) + 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, forwardCyclePath]
    rw [hstepIndex]
    exact hunit _
  have hpcol : ∀ k, k + 2 ≤ n →
      ∃ t : ℝ, p (k + 2) - p (k + 1) = t • (p (k + 1) - p k) :=
    forward_relative_stressed_arc_collinear hr v hunit d i j n hncast hnlt
      a hcoeff hai
  have hpclosed : p n = p 0 := by
    simp only [p, forwardCyclePath]
    rw [hncast, add_sub_cancel]
    simpa using hcollision.symm
  exact closed_collinear_unit_chain_even p n hpunit hpcol hpclosed

private theorem forward_stressed_arc_distance_eq_index {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r) (n : ℕ)
    (hncast : Fin.ofNat r n = j - i) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hai : a i ≠ 0) : Dist.dist (v i) (v j) = n := by
  let p : ℕ → Plane := forwardCyclePath v i
  let b : ℕ → ℝ := fun k => a (i + Fin.ofNat r k)
  have hstepIndex (k : ℕ) :
      i + Fin.ofNat r (k + 1) = (i + Fin.ofNat r k) + 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod, Nat.mod_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, forwardCyclePath]
    rw [hstepIndex]
    exact hunit _
  have hpInj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l := by
    intro k hk l hl hkl
    have hindex : i + Fin.ofNat r k = i + Fin.ofNat r l := hinj hkl
    have hcast : Fin.ofNat r k = Fin.ofNat r l := add_left_cancel hindex
    have hklt : k < r := lt_of_le_of_lt hk hnlt
    have hllt : l < r := lt_of_le_of_lt hl hnlt
    have hval := congrArg Fin.val hcast
    simpa [Fin.ofNat, Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] using hval
  have hneStart (k : ℕ) (hkpos : 0 < k) (hklt : k < r) :
      i + Fin.ofNat r k ≠ i := by
    intro h
    have hzero : Fin.ofNat r k = 0 := by
      apply add_left_cancel (a := i)
      simpa using h
    have hval := congrArg Fin.val hzero
    simp [Fin.ofNat, Nat.mod_eq_of_lt hklt] at hval
    omega
  have hneEnd (k : ℕ) (hklt : k < n) : i + Fin.ofNat r k ≠ j := by
    intro h
    have hcast : Fin.ofNat r k = Fin.ofNat r n := by
      rw [hncast]
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using h)
    have hkR : k < r := lt_trans hklt hnlt
    have hval := congrArg Fin.val hcast
    simp [Fin.ofNat, Nat.mod_eq_of_lt hkR, Nat.mod_eq_of_lt hnlt] at hval
    omega
  have hbalance : ∀ k, k + 1 < n →
      b k • (p (k + 1) - p k) =
        b (k + 1) • (p (k + 2) - p (k + 1)) := by
    intro k hk
    let q : Fin r := i + Fin.ofNat r (k + 1)
    have hqneI : q ≠ i := hneStart (k + 1) (by omega) (by omega)
    have hqneJ : q ≠ j := hneEnd (k + 1) hk
    have hb := chord_stress_balance hr v i j a hcoeff q hqneI hqneJ
    have hpred : q - 1 = i + Fin.ofNat r k := by
      dsimp only [q]
      rw [hstepIndex]
      abel
    have hnext : q + 1 = i + Fin.ofNat r (k + 2) := by
      dsimp only [q]
      rw [hstepIndex (k + 1)]
    rw [hpred, hnext] at hb
    dsimp only [q] at hb
    dsimp only [p, b, forwardCyclePath]
    exact hb
  have hb0 : b 0 ≠ 0 := by simpa [b] using hai
  have hpcol := path_stress_forces_collinear p b n hpunit hbalance hb0
  have hpdist := dist_endpoints_of_collinear_unit_chain_on p n hpunit hpInj hpcol
  have hpend : p n = v j := by
    simp only [p, forwardCyclePath]
    rw [hncast, add_sub_cancel]
  have hpstart : p 0 = v i := by simp [p, forwardCyclePath]
  simpa [hpstart, hpend] using hpdist

private theorem forward_stressed_arc_impossible {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r) (n : ℕ)
    (hij : Dist.dist (v i) (v j) = 1)
    (hncast : Fin.ofNat r n = j - i) (hnlt : n < r) (hn2 : 2 ≤ n)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hai : a i ≠ 0) : False := by
  have hd := forward_stressed_arc_distance_eq_index hr v hunit hinj i j n
    hncast hnlt a hcoeff hai
  rw [hij] at hd
  have hn : n = 1 := by exact_mod_cast hd.symm
  omega

private def backwardCyclePath {r : ℕ} [NeZero r]
    (v : Fin r → Plane) (i : Fin r) (k : ℕ) : Plane := v (i - Fin.ofNat r k)

private theorem backward_relative_stressed_arc_collinear {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (d : Plane) (i j : Fin r) (n : ℕ)
    (hncast : Fin.ofNat r n = i - j) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j)
    (hai : a (i - 1) ≠ 0) :
    ∀ k, k + 2 ≤ n →
      ∃ t : ℝ,
        backwardCyclePath v i (k + 2) - backwardCyclePath v i (k + 1) =
          t • (backwardCyclePath v i (k + 1) - backwardCyclePath v i k) := by
  let p : ℕ → Plane := backwardCyclePath v i
  let b : ℕ → ℝ := fun k => a (i - Fin.ofNat r (k + 1))
  have hstepIndex (k : ℕ) :
      i - Fin.ofNat r (k + 1) = (i - Fin.ofNat r k) - 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, backwardCyclePath]
    rw [hstepIndex]
    calc
      Dist.dist (v (i - Fin.ofNat r k)) (v (i - Fin.ofNat r k - 1)) =
          Dist.dist (v (i - Fin.ofNat r k - 1)) (v (i - Fin.ofNat r k)) :=
        dist_comm _ _
      _ = 1 := by simpa using hunit (i - Fin.ofNat r k - 1)
  have hneStart (k : ℕ) (hkpos : 0 < k) (hklt : k < r) :
      i - Fin.ofNat r k ≠ i := by
    intro h
    have hzero : Fin.ofNat r k = 0 := sub_eq_self.mp h
    have hval := congrArg Fin.val hzero
    simp [Fin.ofNat, Nat.mod_eq_of_lt hklt] at hval
    omega
  have hneEnd (k : ℕ) (hklt : k < n) : i - Fin.ofNat r k ≠ j := by
    intro h
    have hcast : Fin.ofNat r k = Fin.ofNat r n := by
      rw [hncast]
      calc
        Fin.ofNat r k = i - (i - Fin.ofNat r k) := by abel
        _ = i - j := by rw [h]
    have hkR : k < r := lt_trans hklt hnlt
    have hval := congrArg Fin.val hcast
    simp [Fin.ofNat, Nat.mod_eq_of_lt hkR, Nat.mod_eq_of_lt hnlt] at hval
    omega
  have hbalance : ∀ k, k + 1 < n →
      b k • (p (k + 1) - p k) =
        b (k + 1) • (p (k + 2) - p (k + 1)) := by
    intro k hk
    let q : Fin r := i - Fin.ofNat r (k + 1)
    have hqneI : q ≠ i := hneStart (k + 1) (by omega) (by omega)
    have hqneJ : q ≠ j := hneEnd (k + 1) hk
    have hb := relative_stress_balance hr v d i j a hcoeff q hqneI hqneJ
    have hpred : q - 1 = i - Fin.ofNat r (k + 2) := by
      dsimp only [q]
      rw [hstepIndex (k + 1)]
    have hnext : q + 1 = i - Fin.ofNat r k := by
      dsimp only [q]
      rw [hstepIndex k]
      abel
    rw [hpred, hnext] at hb
    dsimp only [q] at hb
    dsimp only [p, b, backwardCyclePath]
    rw [show v (i - Fin.ofNat r (k + 1)) - v (i - Fin.ofNat r k) =
        -(v (i - Fin.ofNat r k) - v (i - Fin.ofNat r (k + 1))) by abel]
    rw [show v (i - Fin.ofNat r (k + 2)) - v (i - Fin.ofNat r (k + 1)) =
        -(v (i - Fin.ofNat r (k + 1)) - v (i - Fin.ofNat r (k + 2))) by abel]
    simp only [smul_neg]
    exact congrArg Neg.neg hb.symm
  have hb0 : b 0 ≠ 0 := by
    have hone : Fin.ofNat r 1 = (1 : Fin r) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (show 1 < r by omega)]
    change a (i - Fin.ofNat r 1) ≠ 0
    rw [hone]
    exact hai
  exact path_stress_forces_collinear p b n hpunit hbalance hb0

private theorem backward_relative_stressed_arc_even_of_collision {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (d : Plane) (i j : Fin r) (n : ℕ) (hcollision : v i = v j)
    (hncast : Fin.ofNat r n = i - j) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = relativeFlexFunctional d i j)
    (hai : a (i - 1) ≠ 0) : Even n := by
  let p : ℕ → Plane := backwardCyclePath v i
  have hstepIndex (k : ℕ) :
      i - Fin.ofNat r (k + 1) = (i - Fin.ofNat r k) - 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, backwardCyclePath]
    rw [hstepIndex]
    calc
      Dist.dist (v (i - Fin.ofNat r k)) (v (i - Fin.ofNat r k - 1)) =
          Dist.dist (v (i - Fin.ofNat r k - 1)) (v (i - Fin.ofNat r k)) :=
        dist_comm _ _
      _ = 1 := by simpa using hunit (i - Fin.ofNat r k - 1)
  have hpcol : ∀ k, k + 2 ≤ n →
      ∃ t : ℝ, p (k + 2) - p (k + 1) = t • (p (k + 1) - p k) :=
    backward_relative_stressed_arc_collinear hr v hunit d i j n hncast hnlt
      a hcoeff hai
  have hpclosed : p n = p 0 := by
    simp only [p, backwardCyclePath]
    rw [hncast, sub_sub_cancel]
    simpa using hcollision.symm
  exact closed_collinear_unit_chain_even p n hpunit hpcol hpclosed

private noncomputable def planeAxisX : Plane := WithLp.toLp 2 ![(1 : ℝ), 0]

private noncomputable def planeAxisY : Plane := WithLp.toLp 2 ![(0 : ℝ), 1]

private theorem planeAxisX_ne_zero : planeAxisX ≠ 0 := by
  intro h
  have := congrArg (fun z : Plane => z.ofLp 0) h
  norm_num [planeAxisX] at this

private theorem plane_axes_not_common_line (e : Plane) (a b : ℝ)
    (hx : a • e = -planeAxisX) (hy : b • e = -planeAxisY) : False := by
  have hx0 := congrArg (fun z : Plane => z.ofLp 0) hx
  have hx1 := congrArg (fun z : Plane => z.ofLp 1) hx
  have hy1 := congrArg (fun z : Plane => z.ofLp 1) hy
  simp [planeAxisX, planeAxisY] at hx0 hx1 hy1
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hx0
    norm_num at hx0
  have he1 : e.ofLp 1 = 0 := hx1.resolve_left ha
  rw [he1, mul_zero] at hy1
  norm_num at hy1

/-- Distinct copies of the same point on an odd unit cycle can always be
separated by an infinitesimal flex of the cycle. -/
private theorem odd_cycle_collision_has_flex {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (hodd : Odd r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (i j : Fin r) (hij : i ≠ j) (hcollision : v i = v j) :
    ∃ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) ∧ z i ≠ z j := by
  by_contra hflex
  push Not at hflex
  have hvanish (d : Plane) : ∀ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) →
      relativeFlexFunctional d i j z = 0 := by
    intro z hz
    rw [relativeFlexFunctional_apply, hflex z hz, sub_self, inner_zero_right]
  obtain ⟨aX, haX⟩ := relative_stress_coefficients v planeAxisX i j (hvanish planeAxisX)
  obtain ⟨aY, haY⟩ := relative_stress_coefficients v planeAxisY i j (hvanish planeAxisY)
  have hbX := relative_stress_endpoint_balance hr v planeAxisX i j hij aX haX
  have hbY := relative_stress_endpoint_balance hr v planeAxisY i j hij aY haY
  have hforward : aX i ≠ 0 ∨ aY i ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1] at hbX
    rw [h.2] at hbY
    simp only [zero_smul, sub_zero] at hbX hbY
    exact plane_axes_not_common_line (v i - v (i - 1)) (aX (i - 1)) (aY (i - 1))
      hbX hbY
  have hbackward : aX (i - 1) ≠ 0 ∨ aY (i - 1) ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1] at hbX
    rw [h.2] at hbY
    simp only [zero_smul, zero_sub] at hbX hbY
    have hx : (-aX i) • (v (i + 1) - v i) = -planeAxisX := by
      rw [neg_smul]
      exact hbX
    have hy : (-aY i) • (v (i + 1) - v i) = -planeAxisY := by
      rw [neg_smul]
      exact hbY
    exact plane_axes_not_common_line (v (i + 1) - v i) (-aX i) (-aY i) hx hy
  have hforwardCast : Fin.ofNat r (j - i).val = j - i := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (j - i).isLt]
  have hbackwardCast : Fin.ofNat r (i - j).val = i - j := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (i - j).isLt]
  have hevenForward : Even (j - i).val := by
    rcases hforward with h | h
    · exact forward_relative_stressed_arc_even_of_collision hr v hunit planeAxisX i j
        (j - i).val hcollision hforwardCast (j - i).isLt aX haX h
    · exact forward_relative_stressed_arc_even_of_collision hr v hunit planeAxisY i j
        (j - i).val hcollision hforwardCast (j - i).isLt aY haY h
  have hevenBackward : Even (i - j).val := by
    rcases hbackward with h | h
    · exact backward_relative_stressed_arc_even_of_collision hr v hunit planeAxisX i j
        (i - j).val hcollision hbackwardCast (i - j).isLt aX haX h
    · exact backward_relative_stressed_arc_even_of_collision hr v hunit planeAxisY i j
        (i - j).val hcollision hbackwardCast (i - j).isLt aY haY h
  have hsumInt : ((j - i).val : ℤ) + ((i - j).val : ℤ) = r := by
    rw [Fin.intCast_val_sub_eq_sub_add_ite, Fin.intCast_val_sub_eq_sub_add_ite]
    by_cases hle : i ≤ j
    · have hnle : ¬j ≤ i := by
        intro hji
        exact hij (le_antisymm hle hji)
      simp [hle, hnle]
      ring
    · have hji : j ≤ i := le_of_not_ge hle
      simp [hle, hji]
      ring
  have hsum : (j - i).val + (i - j).val = r := by exact_mod_cast hsumInt
  obtain ⟨q, hq⟩ := hevenForward
  obtain ⟨s, hs⟩ := hevenBackward
  obtain ⟨t, ht⟩ := hodd
  omega

private noncomputable def quarterTurn (x : Plane) : Plane :=
  WithLp.toLp 2 ![-x.ofLp 1, x.ofLp 0]

private theorem quarterTurn_sub (x y : Plane) :
    quarterTurn (x - y) = quarterTurn x - quarterTurn y := by
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [quarterTurn] <;> ring

private noncomputable def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun := quarterTurn
  map_add' x y := by
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [quarterTurn] <;> ring
  map_smul' t x := by
    apply PiLp.ext
    intro k
    fin_cases k <;> simp [quarterTurn] <;> ring

private noncomputable def quarterTurnCLM : Plane →L[ℝ] Plane :=
  quarterTurnLinear.toContinuousLinearMap

@[simp] private theorem quarterTurnCLM_apply (x : Plane) :
    quarterTurnCLM x = quarterTurn x := rfl

private theorem quarterTurn_injective : Function.Injective quarterTurn := by
  intro x y hxy
  have h0 := congrArg (fun z : Plane => z.ofLp 0) hxy
  have h1 := congrArg (fun z : Plane => z.ofLp 1) hxy
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [quarterTurn] at h0 h1 ⊢
  · exact h1
  · linarith

private theorem inner_quarterTurn_self (x : Plane) :
    inner ℝ x (quarterTurn x) = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

private theorem inner_quarterTurn_quarterTurn (x y : Plane) :
    inner ℝ (quarterTurn x) (quarterTurn y) = inner ℝ x y := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

private theorem inner_quarterTurn_skew (x y : Plane) :
    inner ℝ x (quarterTurn y) = -inner ℝ y (quarterTurn x) := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

@[simp] private theorem quarterTurn_zero : quarterTurn (0 : Plane) = 0 := by
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [quarterTurn]

private theorem exists_smul_of_inner_quarterTurn_eq_zero {x y : Plane}
    (hx : x ≠ 0) (hxy : inner ℝ x (quarterTurn y) = 0) :
    ∃ t : ℝ, y = t • x := by
  have hdet : -y.ofLp 1 * x.ofLp 0 + y.ofLp 0 * x.ofLp 1 = 0 := by
    simpa [quarterTurn, PiLp.inner_apply, Fin.sum_univ_succ] using hxy
  by_cases hx0 : x.ofLp 0 = 0
  · have hx1 : x.ofLp 1 ≠ 0 := by
      intro hx1
      apply hx
      apply PiLp.ext
      intro k
      fin_cases k <;> simpa [hx0, hx1]
    have hy0 : y.ofLp 0 = 0 := by
      rw [hx0] at hdet
      simp only [mul_zero, neg_zero, zero_add] at hdet
      simpa using (mul_eq_zero.mp hdet).resolve_right hx1
    refine ⟨y.ofLp 1 / x.ofLp 1, ?_⟩
    apply PiLp.ext
    intro k
    fin_cases k
    · simp [hy0, hx0]
    · simp [hx1]
  · have hy1 : y.ofLp 1 = (y.ofLp 0 / x.ofLp 0) * x.ofLp 1 := by
      field_simp
      nlinarith [hdet]
    refine ⟨y.ofLp 0 / x.ofLp 0, ?_⟩
    apply PiLp.ext
    intro k
    fin_cases k
    · simp [hx0]
    · simpa [mul_comm] using hy1

private theorem inner_ne_zero_of_inner_quarterTurn_eq_zero {x y : Plane}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : inner ℝ x (quarterTurn y) = 0) :
    inner ℝ x y ≠ 0 := by
  obtain ⟨t, rfl⟩ := exists_smul_of_inner_quarterTurn_eq_zero hx hxy
  have ht : t ≠ 0 := by
    intro ht
    apply hy
    simp [ht]
  rw [inner_smul_right]
  exact mul_ne_zero ht (inner_self_ne_zero.mpr hx)

private theorem odd_cycle_indices_have_separating_flex {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (hodd : Odd r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (i j : Fin r) (hij : i ≠ j) :
    ∃ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) ∧ z i ≠ z j := by
  by_cases hpos : v i = v j
  · exact odd_cycle_collision_has_flex hr hodd v hunit i j hij hpos
  · let z : Fin r → Plane := fun k => quarterTurn (v k)
    refine ⟨z, ?_, ?_⟩
    · intro k
      rw [edgeFlexFunctional_apply]
      rw [← quarterTurn_sub]
      exact inner_quarterTurn_self _
    · intro hz
      exact hpos (quarterTurn_injective hz)

private theorem backward_stressed_arc_distance_eq_index {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r) (n : ℕ)
    (hncast : Fin.ofNat r n = i - j) (hnlt : n < r)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hai : a (i - 1) ≠ 0) : Dist.dist (v i) (v j) = n := by
  let p : ℕ → Plane := backwardCyclePath v i
  let b : ℕ → ℝ := fun k => a (i - Fin.ofNat r (k + 1))
  have hstepIndex (k : ℕ) :
      i - Fin.ofNat r (k + 1) = (i - Fin.ofNat r k) - 1 := by
    have hnat : Fin.ofNat r (k + 1) = Fin.ofNat r k + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
    rw [hnat]
    abel
  have hpunit : ∀ k < n, Dist.dist (p k) (p (k + 1)) = 1 := by
    intro k hk
    simp only [p, backwardCyclePath]
    rw [hstepIndex]
    calc
      Dist.dist (v (i - Fin.ofNat r k)) (v (i - Fin.ofNat r k - 1)) =
          Dist.dist (v (i - Fin.ofNat r k - 1)) (v (i - Fin.ofNat r k)) :=
        dist_comm _ _
      _ = 1 := by simpa using hunit (i - Fin.ofNat r k - 1)
  have hpInj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l := by
    intro k hk l hl hkl
    have hindex : i - Fin.ofNat r k = i - Fin.ofNat r l := hinj hkl
    have hcast : Fin.ofNat r k = Fin.ofNat r l := by
      apply sub_eq_zero.mp
      calc
        Fin.ofNat r k - Fin.ofNat r l =
            (i - Fin.ofNat r l) - (i - Fin.ofNat r k) := by abel
        _ = 0 := by rw [hindex]; simp
    have hklt : k < r := lt_of_le_of_lt hk hnlt
    have hllt : l < r := lt_of_le_of_lt hl hnlt
    have hval := congrArg Fin.val hcast
    simpa [Fin.ofNat, Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] using hval
  have hneStart (k : ℕ) (hkpos : 0 < k) (hklt : k < r) :
      i - Fin.ofNat r k ≠ i := by
    intro h
    have hzero : Fin.ofNat r k = 0 := by
      apply sub_eq_self.mp h
    have hval := congrArg Fin.val hzero
    simp [Fin.ofNat, Nat.mod_eq_of_lt hklt] at hval
    omega
  have hneEnd (k : ℕ) (hklt : k < n) : i - Fin.ofNat r k ≠ j := by
    intro h
    have hcast : Fin.ofNat r k = Fin.ofNat r n := by
      rw [hncast]
      calc
        Fin.ofNat r k = i - (i - Fin.ofNat r k) := by abel
        _ = i - j := by rw [h]
    have hkR : k < r := lt_trans hklt hnlt
    have hval := congrArg Fin.val hcast
    simp [Fin.ofNat, Nat.mod_eq_of_lt hkR, Nat.mod_eq_of_lt hnlt] at hval
    omega
  have hbalance : ∀ k, k + 1 < n →
      b k • (p (k + 1) - p k) =
        b (k + 1) • (p (k + 2) - p (k + 1)) := by
    intro k hk
    let q : Fin r := i - Fin.ofNat r (k + 1)
    have hqneI : q ≠ i := hneStart (k + 1) (by omega) (by omega)
    have hqneJ : q ≠ j := hneEnd (k + 1) hk
    have hb := chord_stress_balance hr v i j a hcoeff q hqneI hqneJ
    have hpred : q - 1 = i - Fin.ofNat r (k + 2) := by
      dsimp only [q]
      rw [hstepIndex (k + 1)]
    have hnext : q + 1 = i - Fin.ofNat r k := by
      dsimp only [q]
      rw [hstepIndex k]
      abel
    rw [hpred, hnext] at hb
    dsimp only [q] at hb
    dsimp only [p, b, backwardCyclePath]
    rw [show v (i - Fin.ofNat r (k + 1)) - v (i - Fin.ofNat r k) =
        -(v (i - Fin.ofNat r k) - v (i - Fin.ofNat r (k + 1))) by abel]
    rw [show v (i - Fin.ofNat r (k + 2)) - v (i - Fin.ofNat r (k + 1)) =
        -(v (i - Fin.ofNat r (k + 1)) - v (i - Fin.ofNat r (k + 2))) by abel]
    simp only [smul_neg]
    exact congrArg Neg.neg hb.symm
  have hb0 : b 0 ≠ 0 := by
    have hone : Fin.ofNat r 1 = (1 : Fin r) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (show 1 < r by omega)]
    change a (i - Fin.ofNat r 1) ≠ 0
    rw [hone]
    exact hai
  have hpcol := path_stress_forces_collinear p b n hpunit hbalance hb0
  have hpdist := dist_endpoints_of_collinear_unit_chain_on p n hpunit hpInj hpcol
  have hpend : p n = v j := by
    simp only [p, backwardCyclePath]
    rw [hncast, sub_sub_cancel]
  have hpstart : p 0 = v i := by simp [p, backwardCyclePath]
  simpa [hpstart, hpend] using hpdist

private theorem backward_stressed_arc_impossible {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r) (n : ℕ)
    (hij : Dist.dist (v i) (v j) = 1)
    (hncast : Fin.ofNat r n = i - j) (hnlt : n < r) (hn2 : 2 ≤ n)
    (a : Fin r → ℝ)
    (hcoeff : ∑ k, a k • edgeFlexFunctional v k = chordFlexFunctional v i j)
    (hai : a (i - 1) ≠ 0) : False := by
  have hd := backward_stressed_arc_distance_eq_index hr v hunit hinj i j n
    hncast hnlt a hcoeff hai
  rw [hij] at hd
  have hn : n = 1 := by exact_mod_cast hd.symm
  omega

/-- A unit chord which is not an edge of an injectively realized unit cycle
is separated, to first order, by some infinitesimal flex of that cycle.  The
proof is the finite-dimensional self-stress alternative followed by stress
propagation around one of the two cyclic arcs. -/
private theorem cycle_unit_chord_has_flex {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r)
    (hnadj : ¬(cycleGraph r).Adj i j)
    (hij : Dist.dist (v i) (v j) = 1) :
    ∃ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) ∧
        chordFlexFunctional v i j z ≠ 0 := by
  have hne : i ≠ j := by
    intro h
    subst j
    simpa using hij
  by_contra hflex
  push Not at hflex
  have hvanish : ∀ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) →
      chordFlexFunctional v i j z = 0 := by
    intro z hz
    exact hflex z hz
  obtain ⟨a, hcoeff⟩ := chord_stress_coefficients v i j hvanish
  have hnotone : (i - j).val ≠ 1 ∧ (j - i).val ≠ 1 := by
    rw [cycleGraph_adj'] at hnadj
    push Not at hnadj
    exact hnadj
  have hforwardCast : Fin.ofNat r (j - i).val = j - i := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (j - i).isLt]
  have hbackwardCast : Fin.ofNat r (i - j).val = i - j := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (i - j).isLt]
  have hforwardTwo : 2 ≤ (j - i).val := by
    have hpos : 0 < (j - i).val := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hzero : j - i = 0 := by exact Fin.ext hz
      exact hne (sub_eq_zero.mp hzero).symm
    omega
  have hbackwardTwo : 2 ≤ (i - j).val := by
    have hpos : 0 < (i - j).val := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hzero : i - j = 0 := by exact Fin.ext hz
      exact hne (sub_eq_zero.mp hzero)
    omega
  rcases chord_stress_endpoint_nonzero hr v i j a hcoeff hij with hback | hforward
  · exact backward_stressed_arc_impossible hr v hunit hinj i j (i - j).val hij
      hbackwardCast (i - j).isLt hbackwardTwo a hcoeff hback
  · exact forward_stressed_arc_impossible hr v hunit hinj i j (j - i).val hij
      hforwardCast (j - i).isLt hforwardTwo a hcoeff hforward

/-- A length-two chord of an injective unit cycle has a first-order changing
flex whenever its geometric midpoint is not another vertex of the cycle. -/
private theorem cycle_two_chord_has_flex_of_midpoint_off_cycle {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (i j : Fin r)
    (hij : Dist.dist (v i) (v j) = 2)
    (hmid : ∀ k, midpoint ℝ (v i) (v j) ≠ v k) :
    ∃ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) ∧
        chordFlexFunctional v i j z ≠ 0 := by
  have hne : i ≠ j := by
    intro h
    subst j
    simpa using hij
  by_contra hflex
  push Not at hflex
  have hvanish : ∀ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) →
      chordFlexFunctional v i j z = 0 := by
    intro z hz
    exact hflex z hz
  obtain ⟨a, hcoeff⟩ := chord_stress_coefficients v i j hvanish
  have hforwardCast : Fin.ofNat r (j - i).val = j - i := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (j - i).isLt]
  have hbackwardCast : Fin.ofNat r (i - j).val = i - j := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt (i - j).isLt]
  have hvne : v i ≠ v j := fun h => hne (hinj h)
  rcases chord_stress_endpoint_nonzero_of_ne hr v i j a hcoeff hvne with
      hback | hforward
  · have hd := backward_stressed_arc_distance_eq_index hr v hunit hinj i j
      (i - j).val hbackwardCast (i - j).isLt a hcoeff hback
    have hn : (i - j).val = 2 := by
      have : ((i - j).val : ℝ) = 2 := by simpa [hij] using hd.symm
      exact_mod_cast this
    have hcast2' : Fin.ofNat r 2 = i - j := by simpa [hn] using hbackwardCast
    have hcast2 : (2 : Fin r) = i - j := by
      rw [← hcast2']
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : 2 < r)]
    have hj : j = i - 2 := by
      calc
        j = i - (i - j) := by abel
        _ = i - 2 := by rw [← hcast2]
    have hstep1 : Dist.dist (v i) (v (i - 1)) = 1 := by
      calc
        Dist.dist (v i) (v (i - 1)) = Dist.dist (v (i - 1)) (v i) :=
          _root_.dist_comm _ _
        _ = 1 := by
          convert hunit (i - 1) using 1 <;> congr 1 <;> abel_nf
    have hstep2 : Dist.dist (v (i - 1)) (v j) = 1 := by
      rw [hj]
      have hidx : i - 2 + 1 = i - 1 := by
        have htwo : (2 : Fin r) = 1 + 1 := by
          apply Fin.ext
          simp [Fin.add_def, Nat.mod_eq_of_lt (by omega : 2 < r)]
        rw [htwo]
        abel
      calc
        Dist.dist (v (i - 1)) (v (i - 2)) =
            Dist.dist (v (i - 2)) (v (i - 1)) := _root_.dist_comm _ _
        _ = 1 := by
          rw [← hidx]
          exact hunit (i - 2)
    have hmidCycle : v (i - 1) = midpoint ℝ (v i) (v j) := by
      have hstep1' : Dist.dist (v (i - 1)) (v i) = 1 := by
        rw [_root_.dist_comm]
        exact hstep1
      have hAp := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
        (v (i - 1)) (v i) (v j)
      rw [hstep1', hstep2, hij] at hAp
      have hz : Dist.dist (v (i - 1)) (midpoint ℝ (v i) (v j)) = 0 := by
        nlinarith [sq_nonneg (Dist.dist (v (i - 1)) (midpoint ℝ (v i) (v j)))]
      exact dist_eq_zero.mp hz
    exact hmid (i - 1) (hmidCycle.symm)
  · have hd := forward_stressed_arc_distance_eq_index hr v hunit hinj i j
      (j - i).val hforwardCast (j - i).isLt a hcoeff hforward
    have hn : (j - i).val = 2 := by
      have : ((j - i).val : ℝ) = 2 := by simpa [hij] using hd.symm
      exact_mod_cast this
    have hcast2' : Fin.ofNat r 2 = j - i := by simpa [hn] using hforwardCast
    have hcast2 : (2 : Fin r) = j - i := by
      rw [← hcast2']
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : 2 < r)]
    have hj : j = i + 2 := by
      calc
        j = i + (j - i) := by abel
        _ = i + 2 := by rw [← hcast2]
    have hstep1 : Dist.dist (v i) (v (i + 1)) = 1 := hunit i
    have hstep2 : Dist.dist (v (i + 1)) (v j) = 1 := by
      rw [hj]
      have hidx : i + 1 + 1 = i + 2 := by
        have htwo : (2 : Fin r) = 1 + 1 := by
          apply Fin.ext
          simp [Fin.add_def, Nat.mod_eq_of_lt (by omega : 2 < r)]
        rw [htwo]
        abel
      rw [← hidx]
      exact hunit (i + 1)
    have hmidCycle : v (i + 1) = midpoint ℝ (v i) (v j) := by
      have hstep1' : Dist.dist (v (i + 1)) (v i) = 1 := by
        rw [_root_.dist_comm]
        exact hstep1
      have hAp := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
        (v (i + 1)) (v i) (v j)
      rw [hstep1', hstep2, hij] at hAp
      have hz : Dist.dist (v (i + 1)) (midpoint ℝ (v i) (v j)) = 0 := by
        nlinarith [sq_nonneg (Dist.dist (v (i + 1)) (midpoint ℝ (v i) (v j)))]
      exact dist_eq_zero.mp hz
    exact hmid (i + 1) (hmidCycle.symm)

/-- If an external point is joined by unit segments to two distinct vertices
of an injective unit cycle, then the second segment (unless it is the intended
spoke) changes to first order under some cycle flex while the external point
moves with the first cycle vertex. -/
private theorem cycle_external_unit_pair_has_flex {r : ℕ} [NeZero r]
    (hr : 3 ≤ r) (v : Fin r → Plane)
    (hunit : ∀ k, Dist.dist (v k) (v (k + 1)) = 1)
    (hinj : Function.Injective v) (a : Plane) (haoff : ∀ k, a ≠ v k)
    (i q : Fin r) (hiq : i ≠ q)
    (hai : Dist.dist a (v i) = 1) (haq : Dist.dist a (v q) = 1) :
    ∃ z : Fin r → Plane,
      (∀ k, edgeFlexFunctional v k z = 0) ∧
        inner ℝ (a - v i) (z q - z i) ≠ 0 := by
  let zrot : Fin r → Plane := fun k => quarterTurn (v k)
  have hzrot : ∀ k, edgeFlexFunctional v k zrot = 0 := by
    intro k
    rw [edgeFlexFunctional_apply]
    rw [← quarterTurn_sub]
    exact inner_quarterTurn_self _
  by_cases hrot : inner ℝ (a - v i) (zrot q - zrot i) ≠ 0
  · exact ⟨zrot, hzrot, hrot⟩
  · have hrot0 : inner ℝ (a - v i) (zrot q - zrot i) = 0 := not_ne_iff.mp hrot
    have hdne : a - v i ≠ 0 := by
      intro hzero
      have : a = v i := sub_eq_zero.mp hzero
      rw [this] at hai
      simpa using hai
    have hqturn : zrot q - zrot i = quarterTurn (v q - v i) := by
      dsimp only [zrot]
      rw [quarterTurn_sub]
    have hlinezero : inner ℝ (a - v i) (quarterTurn (v q - a)) = 0 := by
      have harg : v q - a = (v q - v i) - (a - v i) := by abel
      rw [harg, quarterTurn_sub, ← hqturn, inner_sub_right, hrot0,
        inner_quarterTurn_self, sub_self]
    obtain ⟨t, ht⟩ := exists_smul_of_inner_quarterTurn_eq_zero hdne hlinezero
    have hviq : v i ≠ v q := fun h => hiq (hinj h)
    have hdir : v q - a = a - v i :=
      collinear_unit_steps_same_direction
        (by simpa [_root_.dist_comm] using hai) haq hviq ⟨t, ht⟩
    have hvdiff : v q - v i = (2 : ℝ) • (a - v i) := by
      calc
        v q - v i = (v q - a) + (a - v i) := by abel
        _ = (a - v i) + (a - v i) := by rw [hdir]
        _ = (2 : ℝ) • (a - v i) := by rw [two_smul]
    have hnorm : ‖a - v i‖ = 1 := by
      simpa only [dist_eq_norm] using hai
    have hdistTwo : Dist.dist (v i) (v q) = 2 := by
      rw [dist_eq_norm, norm_sub_rev, hvdiff, norm_smul, hnorm]
      norm_num
    have hamid : a = midpoint ℝ (v i) (v q) := by
      have hAp :=
        EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
          a (v i) (v q)
      rw [hai, haq, hdistTwo] at hAp
      have hz : Dist.dist a (midpoint ℝ (v i) (v q)) = 0 := by
        nlinarith [sq_nonneg (Dist.dist a (midpoint ℝ (v i) (v q)))]
      exact dist_eq_zero.mp hz
    have hmidOff : ∀ k, midpoint ℝ (v i) (v q) ≠ v k := by
      intro k hmid
      exact haoff k (hamid.trans hmid)
    obtain ⟨z, hzflex, hzchord⟩ :=
      cycle_two_chord_has_flex_of_midpoint_off_cycle hr v hunit hinj i q
        hdistTwo hmidOff
    refine ⟨z, hzflex, ?_⟩
    intro hzero
    apply hzchord
    rw [chordFlexFunctional_apply, hvdiff, inner_smul_left]
    rw [hzero]
    simp

/-! ### The analytic attachment equation -/

/-- The `2r` squared-length equations for an `r`-cycle `v` attached by
spokes to an ordered foundation `u`.  The left summand records the spokes;
the right summand records the cyclic edges.  Squared lengths make this a
polynomial map, which is the convenient form of the implicit-function
argument. -/
private noncomputable def attachmentConstraints (r : ℕ) [NeZero r] :
    ((Fin r → Plane) × (Fin r → Plane)) → (Fin r ⊕ Fin r → ℝ)
  | (u, v), Sum.inl i => ‖v i - u i‖ ^ 2
  | (u, v), Sum.inr i => ‖v (i + 1) - v i‖ ^ 2

private theorem attachmentConstraints_contDiff (r : ℕ) [NeZero r] :
    ContDiff ℝ ⊤ (attachmentConstraints r) := by
  rw [contDiff_pi]
  intro i
  cases i with
  | inl i =>
      simp only [attachmentConstraints]
      exact (by fun_prop : ContDiff ℝ ⊤ (fun x :
        (Fin r → Plane) × (Fin r → Plane) => x.2 i - x.1 i)).norm_sq ℝ
  | inr i =>
      simp only [attachmentConstraints]
      exact (by fun_prop : ContDiff ℝ ⊤ (fun x :
        (Fin r → Plane) × (Fin r → Plane) => x.2 (i + 1) - x.2 i)).norm_sq ℝ

/-- The Jacobian of the attachment equations in the cycle variables. -/
private noncomputable def attachmentCycleDerivative {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    (Fin r → Plane) →L[ℝ] (Fin r ⊕ Fin r → ℝ) :=
  ContinuousLinearMap.pi fun q =>
    match q with
    | .inl i => 2 • (innerSL ℝ (v i - u i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)
    | .inr i => 2 • (innerSL ℝ (v (i + 1) - v i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) (i + 1) -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)

/-- The Jacobian of the attachment equations in the foundation variables.
Only the spoke equations depend on the foundation.  Keeping this map
separate from `attachmentCycleDerivative` is useful for the infinitesimal
stress calculation needed to rule out a hidden unit bar. -/
private noncomputable def attachmentFoundationDerivative {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    (Fin r → Plane) →L[ℝ] (Fin r ⊕ Fin r → ℝ) :=
  ContinuousLinearMap.pi fun q =>
    match q with
    | .inl i => 2 • (innerSL ℝ (u i - v i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Plane) i)
    | .inr _ => 0

private noncomputable def attachmentCycleDerivativeProd {r : ℕ} [NeZero r]
    (p : (Fin r → Plane) × (Fin r → Plane)) :
    (Fin r → Plane) →L[ℝ] (Fin r ⊕ Fin r → ℝ) :=
  attachmentCycleDerivative p.1 p.2

private theorem continuous_attachmentCycleDerivativeProd {r : ℕ} [NeZero r] :
    Continuous (attachmentCycleDerivativeProd (r := r)) := by
  unfold attachmentCycleDerivativeProd attachmentCycleDerivative
  apply (ContinuousLinearMap.piEquivL ℝ (Fin r → Plane)
    (fun _ : Fin r ⊕ Fin r => ℝ)).continuous.comp
  apply continuous_pi
  intro q
  cases q <;> fun_prop

private theorem hasFDerivAt_attachmentConstraints_left {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    HasFDerivAt (fun w => attachmentConstraints r (w, v))
      (attachmentFoundationDerivative u v) u := by
  apply hasFDerivAt_pi.mpr
  intro q
  cases q with
  | inl i =>
      simpa [attachmentConstraints, attachmentFoundationDerivative,
        innerSL_apply_apply, inner_sub_left] using
        ((hasFDerivAt_const (x := u) (v i)).sub (hasFDerivAt_apply i u)).norm_sq
  | inr i =>
      simpa [attachmentConstraints, attachmentFoundationDerivative] using
        (hasFDerivAt_const (x := u) (‖v (i + 1) - v i‖ ^ 2))

private theorem hasFDerivAt_attachmentConstraints_right {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    HasFDerivAt (fun w => attachmentConstraints r (u, w))
      (attachmentCycleDerivative u v) v := by
  apply hasFDerivAt_pi.mpr
  intro q
  cases q with
  | inl i =>
      simpa [attachmentConstraints, attachmentCycleDerivative] using
        ((hasFDerivAt_apply i v).sub_const (u i)).norm_sq
  | inr i =>
      simpa [attachmentConstraints, attachmentCycleDerivative] using
        ((hasFDerivAt_apply (i + 1) v).sub
          (hasFDerivAt_apply i v)).norm_sq

/-- The explicit Jacobian is definitionally the partial Fréchet derivative
used by Mathlib's implicit-function theorem. -/
private theorem attachmentCycleDerivative_eq_partialFDeriv {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    attachmentCycleDerivative u v =
      fderiv ℝ (attachmentConstraints r) (u, v) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane) := by
  apply HasFDerivAt.unique (hasFDerivAt_attachmentConstraints_right u v)
  exact ((attachmentConstraints_contDiff r).differentiable (by simp) (u, v)).hasFDerivAt.comp v
    (hasFDerivAt_prodMk_right u v)

private theorem attachmentFoundationDerivative_eq_partialFDeriv {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    attachmentFoundationDerivative u v =
      fderiv ℝ (attachmentConstraints r) (u, v) ∘L
        ContinuousLinearMap.inl ℝ (Fin r → Plane) (Fin r → Plane) := by
  apply HasFDerivAt.unique (hasFDerivAt_attachmentConstraints_left u v)
  exact ((attachmentConstraints_contDiff r).differentiable (by simp) (u, v)).hasFDerivAt.comp u
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) u v)

/-- The attachment Jacobian is square: both its domain and codomain have
real dimension `2r`.  Thus injectivity is enough for the IFT hypothesis. -/
private theorem attachmentCycleDerivative_isInvertible_of_injective {r : ℕ}
    (L : (Fin r → Plane) →L[ℝ] (Fin r ⊕ Fin r → ℝ))
    (hL : Function.Injective L) : L.IsInvertible := by
  have hdim : Module.finrank ℝ (Fin r → Plane) =
      Module.finrank ℝ (Fin r ⊕ Fin r → ℝ) := by
    have hp : Module.finrank ℝ Plane = 2 := by
      rw [(EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.finrank_eq]
      simp
    rw [Module.finrank_pi_fintype]
    simp [hp]
    omega
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL
  refine ⟨ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL) (LinearMap.range_eq_top.mpr hsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

private theorem spoke_inner_eq_zero_of_derivative_eq_zero {r : ℕ} [NeZero r]
    {u v w : Fin r → Plane}
    (h : attachmentCycleDerivative u v w = 0) (i : Fin r) :
    inner ℝ (v i - u i) (w i) = 0 := by
  have hi := congrFun h (Sum.inl i)
  simpa [attachmentCycleDerivative, innerSL_apply_apply, inner_sub_left] using hi

private theorem cycle_inner_eq_zero_of_derivative_eq_zero {r : ℕ} [NeZero r]
    {u v w : Fin r → Plane}
    (h : attachmentCycleDerivative u v w = 0) (i : Fin r) :
    inner ℝ (v (i + 1) - v i) (w (i + 1) - w i) = 0 := by
  have hi := congrFun h (Sum.inr i)
  simpa [attachmentCycleDerivative, innerSL_apply_apply, inner_sub_left,
    inner_sub_right] using hi

private theorem attachmentCycleDerivative_eq_zero_of_inner {r : ℕ} [NeZero r]
    {u v w : Fin r → Plane}
    (hspoke : ∀ i, inner ℝ (v i - u i) (w i) = 0)
    (hcycle : ∀ i,
      inner ℝ (v (i + 1) - v i) (w (i + 1) - w i) = 0) :
    attachmentCycleDerivative u v w = 0 := by
  funext q
  cases q with
  | inl i => simpa [attachmentCycleDerivative, innerSL_apply_apply,
      inner_sub_left] using hspoke i
  | inr i => simpa [attachmentCycleDerivative, innerSL_apply_apply,
      inner_sub_left, inner_sub_right] using hcycle i

/-- At a unit attachment the polynomial constraint vector is constantly
one. -/
private theorem attachmentConstraints_eq_one {r : ℕ} [NeZero r]
    {u v : Fin r → Plane}
    (hspoke : ∀ i, Dist.dist (u i) (v i) = 1)
    (hcycle : ∀ i, Dist.dist (v i) (v (i + 1)) = 1) :
    attachmentConstraints r (u, v) = 1 := by
  funext q
  cases q with
  | inl i =>
      simp only [attachmentConstraints, Pi.one_apply, dist_eq_norm] at hspoke ⊢
      rw [norm_sub_rev, hspoke i]
      norm_num
  | inr i =>
      simp only [attachmentConstraints, Pi.one_apply, dist_eq_norm] at hcycle ⊢
      rw [norm_sub_rev, hcycle i]
      norm_num

/-- Conversely, the squared equations equal to one give all intended unit
segments. -/
private theorem unit_attachment_of_constraints_eq_one {r : ℕ} [NeZero r]
    {u v : Fin r → Plane} (h : attachmentConstraints r (u, v) = 1) :
    (∀ i, Dist.dist (u i) (v i) = 1) ∧
      ∀ i, Dist.dist (v i) (v (i + 1)) = 1 := by
  constructor
  · intro i
    have hi := congrFun h (Sum.inl i)
    simp only [attachmentConstraints, Pi.one_apply] at hi
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [norm_nonneg (v i - u i)]
  · intro i
    have hi := congrFun h (Sum.inr i)
    simp only [attachmentConstraints, Pi.one_apply] at hi
    rw [norm_sub_rev] at hi
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v (i + 1))]

/-- The local cycle selected by the implicit-function theorem at a regular
attachment. -/
private noncomputable def localAttachedCycle {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    (Fin r → Plane) → (Fin r → Plane) :=
  (attachmentConstraints_contDiff r).contDiffAt.implicitFunction (by simp) hinv

private theorem partialDerivative_isInvertible_of_cycle {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
      ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible := by
  rw [← attachmentCycleDerivative_eq_partialFDeriv]
  exact hinv

/-- A version of the IFT solution whose interface exposes the explicit cycle
Jacobian rather than the much larger unfolded partial-derivative term. -/
private noncomputable def regularLocalAttachedCycle {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    (Fin r → Plane) → (Fin r → Plane) :=
  localAttachedCycle u₀ v₀ (partialDerivative_isInvertible_of_cycle u₀ v₀ hinv)

/-- Exact first-order response of the locally selected cycle to a motion of
its foundation.  This is Mathlib's implicit derivative formula, rewritten in
terms of the two explicit attachment Jacobians above. -/
private theorem localAttachedCycle_hasStrictFDerivAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    HasStrictFDerivAt (localAttachedCycle u₀ v₀ hinv)
      (-(attachmentCycleDerivative u₀ v₀).inverse ∘L
        attachmentFoundationDerivative u₀ v₀) u₀ := by
  simpa only [localAttachedCycle, attachmentCycleDerivative_eq_partialFDeriv,
    attachmentFoundationDerivative_eq_partialFDeriv] using
    (attachmentConstraints_contDiff r).contDiffAt.hasStrictFDerivAt_implicitFunction
      (by simp) hinv

/-- The implicit derivative really preserves every spoke and cycle equation
to first order.  This algebraic identity is the starting point for the
finite-dimensional stress argument. -/
private theorem attachment_linearization_localCycle {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible)
    (w : Fin r → Plane) :
    attachmentFoundationDerivative u₀ v₀ w +
      attachmentCycleDerivative u₀ v₀
        ((-(attachmentCycleDerivative u₀ v₀).inverse ∘L
          attachmentFoundationDerivative u₀ v₀) w) = 0 := by
  simp [ContinuousLinearMap.comp_apply, map_neg, hinv]

private theorem localAttachedCycle_apply_base {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    localAttachedCycle u₀ v₀ hinv u₀ = v₀ := by
  exact (attachmentConstraints_contDiff r).contDiffAt.implicitFunction_apply_self
    (by simp) hinv

/-- Every regular exact attachment persists under all sufficiently small
motions of its foundation. -/
private theorem eventually_localAttachedCycle_is_attachment {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hunit : (∀ i, Dist.dist (u₀ i) (v₀ i) = 1) ∧
      ∀ i, Dist.dist (v₀ i) (v₀ (i + 1)) = 1)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    ∀ᶠ u in nhds u₀,
      (∀ i, Dist.dist (u i) (localAttachedCycle u₀ v₀ hinv u i) = 1) ∧
        ∀ i, Dist.dist (localAttachedCycle u₀ v₀ hinv u i)
          (localAttachedCycle u₀ v₀ hinv u (i + 1)) = 1 := by
  have heq : attachmentConstraints r (u₀, v₀) = 1 :=
    attachmentConstraints_eq_one hunit.1 hunit.2
  filter_upwards [
    (attachmentConstraints_contDiff r).contDiffAt.eventually_apply_implicitFunction
      (by simp) hinv] with u hu
  apply unit_attachment_of_constraints_eq_one
  simpa [localAttachedCycle, heq] using hu

private theorem localAttachedCycle_continuousAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    ContinuousAt (localAttachedCycle u₀ v₀ hinv) u₀ := by
  exact ((attachmentConstraints_contDiff r).contDiffAt.contDiffAt_implicitFunction
    (by simp) hinv).continuousAt

private theorem eventually_localAttachedCycle_continuousAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    ∀ᶠ u in nhds u₀, ContinuousAt (localAttachedCycle u₀ v₀ hinv) u := by
  have hcd : ContDiffAt ℝ 1 (localAttachedCycle u₀ v₀ hinv) u₀ :=
    ((attachmentConstraints_contDiff r).contDiffAt.contDiffAt_implicitFunction
      (by simp) hinv).of_le (by simp)
  exact (hcd.eventually (by simp)).mono fun u hu ↦ hu.continuousAt

private theorem eventually_localAttachedCycle_contDiffAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv :
      (fderiv ℝ (attachmentConstraints r) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane)).IsInvertible) :
    ∀ᶠ u in nhds u₀, ContDiffAt ℝ 1 (localAttachedCycle u₀ v₀ hinv) u := by
  have hcd : ContDiffAt ℝ 1 (localAttachedCycle u₀ v₀ hinv) u₀ :=
    ((attachmentConstraints_contDiff r).contDiffAt.contDiffAt_implicitFunction
      (by simp) hinv).of_le (by simp)
  exact hcd.eventually (by simp)

private theorem eventually_injective_continuousLinearMap
    {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace A] (L : A → (E →L[ℝ] F)) (x : A)
    (hL : ContinuousAt L x) (hinv : (L x).IsInvertible) :
    ∀ᶠ y in nhds x, Function.Injective (L y) := by
  let e : E ≃L[ℝ] F := Classical.choose hinv
  have he : (e : E →L[ℝ] F) = L x := Classical.choose_spec hinv
  have hanti : AntilipschitzWith ‖(e.symm : F →L[ℝ] E)‖₊ (L x) := by
    rw [← he]
    exact e.antilipschitz
  have hKpos : 0 < ‖(e.symm : F →L[ℝ] E)‖₊ := e.nnnorm_symm_pos
  have hnorm : Filter.Tendsto (fun y => ‖L y - L x‖₊) (nhds x) (nhds 0) := by
    have hc : ContinuousAt (fun _ : A => L x) x := continuousAt_const
    have hc0 : ContinuousAt (fun y => ‖L y - L x‖₊) x := (hL.sub hc).nnnorm
    change Filter.Tendsto (fun y => ‖L y - L x‖₊) (nhds x)
      (nhds ‖L x - L x‖₊) at hc0
    simpa only [sub_self, nnnorm_zero] using hc0
  have hthreshold : 0 < ‖(e.symm : F →L[ℝ] E)‖₊⁻¹ := inv_pos.mpr hKpos
  filter_upwards [hnorm.eventually (gt_mem_nhds hthreshold)] with y hy
  exact (hanti.add_sub_lipschitzWith (L y - L x).lipschitz hy).injective

private theorem regularLocalAttachedCycle_continuousAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ContinuousAt (regularLocalAttachedCycle u₀ v₀ hinv) u₀ := by
  unfold regularLocalAttachedCycle
  exact localAttachedCycle_continuousAt (r := r) u₀ v₀ _

private theorem regularAttachmentDerivative_continuousAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ContinuousAt
      (fun u => attachmentCycleDerivativeProd
        (u, regularLocalAttachedCycle u₀ v₀ hinv u)) u₀ := by
  exact (continuous_attachmentCycleDerivativeProd (r := r)).continuousAt.comp
    (continuousAt_id.prodMk (regularLocalAttachedCycle_continuousAt u₀ v₀ hinv))

private theorem eventually_regularLocalAttachedCycle_derivativeInjective {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ∀ᶠ u in nhds u₀, Function.Injective
      (attachmentCycleDerivativeProd (u, regularLocalAttachedCycle u₀ v₀ hinv u)) := by
  apply eventually_injective_continuousLinearMap
    (E := Fin r → Plane) (F := Fin r ⊕ Fin r → ℝ)
    (fun u => attachmentCycleDerivativeProd
      (u, regularLocalAttachedCycle u₀ v₀ hinv u)) u₀
    (regularAttachmentDerivative_continuousAt u₀ v₀ hinv)
  unfold attachmentCycleDerivativeProd regularLocalAttachedCycle
  rw [localAttachedCycle_apply_base (r := r)]
  exact hinv

private theorem eventually_regularLocalAttachedCycle_is_attachment {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hunit : (∀ i, Dist.dist (u₀ i) (v₀ i) = 1) ∧
      ∀ i, Dist.dist (v₀ i) (v₀ (i + 1)) = 1)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ∀ᶠ u in nhds u₀,
      (∀ i, Dist.dist (u i) (regularLocalAttachedCycle u₀ v₀ hinv u i) = 1) ∧
        ∀ i, Dist.dist (regularLocalAttachedCycle u₀ v₀ hinv u i)
          (regularLocalAttachedCycle u₀ v₀ hinv u (i + 1)) = 1 := by
  unfold regularLocalAttachedCycle
  exact eventually_localAttachedCycle_is_attachment u₀ v₀ hunit _

private theorem eventually_regularLocalAttachedCycle_contDiffAt {r : ℕ} [NeZero r]
    (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ∀ᶠ u in nhds u₀, ContDiffAt ℝ 1 (regularLocalAttachedCycle u₀ v₀ hinv) u := by
  unfold regularLocalAttachedCycle
  exact eventually_localAttachedCycle_contDiffAt u₀ v₀ _

private theorem eventually_regularLocalAttachedCycle_derivativeIsInvertible
    {r : ℕ} [NeZero r] (u₀ v₀ : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u₀ v₀).IsInvertible) :
    ∀ᶠ u in nhds u₀,
      (attachmentCycleDerivativeProd
        (u, regularLocalAttachedCycle u₀ v₀ hinv u)).IsInvertible := by
  filter_upwards [eventually_regularLocalAttachedCycle_derivativeInjective u₀ v₀ hinv]
    with u hu
  exact attachmentCycleDerivative_isInvertible_of_injective _ hu

/-- Derivative formula for any differentiable local branch of the attachment
equations at a point where the cycle-variable Jacobian is invertible. -/
private theorem hasFDerivAt_of_attachment_solution {r : ℕ} [NeZero r]
    (ψ : (Fin r → Plane) → (Fin r → Plane)) (u : Fin r → Plane)
    (hψ : ContDiffAt ℝ 1 ψ u)
    (heq : ∀ᶠ w in nhds u, attachmentConstraints r (w, ψ w) = 1)
    (hinv : (attachmentCycleDerivative u (ψ u)).IsInvertible) :
    HasFDerivAt ψ
      (-(attachmentCycleDerivative u (ψ u)).inverse ∘L
        attachmentFoundationDerivative u (ψ u)) u := by
  let ψ' := fderiv ℝ ψ u
  have hψ' : HasFDerivAt ψ ψ' u := (hψ.differentiableAt (by norm_num)).hasFDerivAt
  have hpair : HasFDerivAt (fun w => (w, ψ w))
      ((ContinuousLinearMap.id ℝ (Fin r → Plane)).prod ψ') u :=
    (hasFDerivAt_id (𝕜 := ℝ) (x := u)).prodMk hψ'
  have hconstraint : HasFDerivAt
      (fun w => attachmentConstraints r (w, ψ w))
      (fderiv ℝ (attachmentConstraints r) (u, ψ u) ∘L
        ((ContinuousLinearMap.id ℝ (Fin r → Plane)).prod ψ')) u :=
    by
      have hF : HasFDerivAt (attachmentConstraints r)
          (fderiv ℝ (attachmentConstraints r) (u, ψ u)) (u, ψ u) :=
        ((attachmentConstraints_contDiff r).differentiable (by simp)
          (u, ψ u)).hasFDerivAt
      exact hF.comp u hpair
  have hzero : HasFDerivAt (fun w => attachmentConstraints r (w, ψ w)) 0 u :=
    hasFDerivAt_zero_of_eventually_const (𝕜 := ℝ) 1 heq
  have htotal : fderiv ℝ (attachmentConstraints r) (u, ψ u) ∘L
      ((ContinuousLinearMap.id ℝ (Fin r → Plane)).prod ψ') = 0 :=
    hconstraint.unique hzero
  have hderivEq : ψ' =
      -(attachmentCycleDerivative u (ψ u)).inverse ∘L
        attachmentFoundationDerivative u (ψ u) := by
    apply ContinuousLinearMap.ext
    intro w
    have hw := congrArg (fun L : (Fin r → Plane) →L[ℝ]
        (Fin r ⊕ Fin r → ℝ) => L w) htotal
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hw
    have hsplit :
        fderiv ℝ (attachmentConstraints r) (u, ψ u) (w, ψ' w) =
          attachmentFoundationDerivative u (ψ u) w +
            attachmentCycleDerivative u (ψ u) (ψ' w) := by
      rw [show (w, ψ' w) =
          ContinuousLinearMap.inl ℝ (Fin r → Plane) (Fin r → Plane) w +
            ContinuousLinearMap.inr ℝ (Fin r → Plane) (Fin r → Plane) (ψ' w) by
        ext <;> simp]
      rw [map_add, attachmentFoundationDerivative_eq_partialFDeriv,
        attachmentCycleDerivative_eq_partialFDeriv]
      rfl
    have hlin : attachmentFoundationDerivative u (ψ u) w +
        attachmentCycleDerivative u (ψ u) (ψ' w) = 0 := by
      rw [← hsplit]
      exact hw
    apply hinv.injective
    change attachmentCycleDerivative u (ψ u) (ψ' w) =
      attachmentCycleDerivative u (ψ u)
        (-((attachmentCycleDerivative u (ψ u)).inverse
          (attachmentFoundationDerivative u (ψ u) w)))
    rw [map_neg, hinv.self_apply_inverse]
    exact eq_neg_of_add_eq_zero_right hlin
  rw [← hderivEq]
  exact hψ'

private theorem attachment_derivatives_add_eq_zero_of_cycleFlex
    {r : ℕ} [NeZero r] (u v z : Fin r → Plane)
    (hz : ∀ i, edgeFlexFunctional v i z = 0) :
    attachmentFoundationDerivative u v z + attachmentCycleDerivative u v z = 0 := by
  funext q
  cases q with
  | inl i =>
      simp [attachmentFoundationDerivative, attachmentCycleDerivative,
        innerSL_apply_apply, inner_sub_left]
      ring
  | inr i =>
      have hi := hz i
      simp only [edgeFlexFunctional_apply] at hi
      simpa [attachmentFoundationDerivative, attachmentCycleDerivative,
        innerSL_apply_apply, inner_sub_left, inner_sub_right] using hi

private theorem attachment_response_eq_cycleFlex {r : ℕ} [NeZero r]
    (u v z : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u v).IsInvertible)
    (hz : ∀ i, edgeFlexFunctional v i z = 0) :
    (-(attachmentCycleDerivative u v).inverse ∘L
      attachmentFoundationDerivative u v) z = z := by
  have hsum := attachment_derivatives_add_eq_zero_of_cycleFlex u v z hz
  apply hinv.injective
  change attachmentCycleDerivative u v
      (-((attachmentCycleDerivative u v).inverse
        (attachmentFoundationDerivative u v z))) =
    attachmentCycleDerivative u v z
  rw [map_neg, hinv.self_apply_inverse]
  exact (eq_neg_of_add_eq_zero_right hsum).symm

private theorem attachment_response_eq_of_linearization {r : ℕ} [NeZero r]
    (u v w z : Fin r → Plane)
    (hinv : (attachmentCycleDerivative u v).IsInvertible)
    (hlin : attachmentFoundationDerivative u v w +
      attachmentCycleDerivative u v z = 0) :
    (-(attachmentCycleDerivative u v).inverse ∘L
      attachmentFoundationDerivative u v) w = z := by
  apply hinv.injective
  change attachmentCycleDerivative u v
      (-((attachmentCycleDerivative u v).inverse
        (attachmentFoundationDerivative u v w))) =
    attachmentCycleDerivative u v z
  rw [map_neg, hinv.self_apply_inverse]
  exact (eq_neg_of_add_eq_zero_right hlin).symm

private theorem attachment_rigid_rotation_linearization {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) (c : Plane) :
    attachmentFoundationDerivative u v (fun i => quarterTurn (u i - c)) +
      attachmentCycleDerivative u v (fun i => quarterTurn (v i - c)) = 0 := by
  funext q
  cases q with
  | inl i =>
      simp only [Pi.add_apply, attachmentFoundationDerivative,
        attachmentCycleDerivative, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, innerSL_apply_apply, smul_eq_mul]
      have hdiff : quarterTurn (v i - c) - quarterTurn (u i - c) =
          quarterTurn (v i - u i) := by
        rw [← quarterTurn_sub]
        congr 1
        abel
      have hinner : inner ℝ (u i - v i) (quarterTurn (u i - c)) +
          inner ℝ (v i - u i) (quarterTurn (v i - c)) =
          inner ℝ (v i - u i)
            (quarterTurn (v i - c) - quarterTurn (u i - c)) := by
        rw [inner_sub_right, show u i - v i = -(v i - u i) by abel,
          inner_neg_left]
        ring
      have hzero : inner ℝ (u i - v i) (quarterTurn (u i - c)) +
          inner ℝ (v i - u i) (quarterTurn (v i - c)) = 0 := by
        rw [hinner, hdiff, inner_quarterTurn_self]
      simp only [Pi.zero_apply, two_nsmul]
      linarith
  | inr i =>
      simp only [Pi.add_apply, attachmentFoundationDerivative,
        attachmentCycleDerivative, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.zero_apply, zero_add,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply,
        innerSL_apply_apply, smul_eq_mul]
      rw [← quarterTurn_sub]
      have harg : v (i + 1) - c - (v i - c) = v (i + 1) - v i := by abel
      rw [harg, inner_quarterTurn_self]
      simp

/-- Cartesian coordinates in the Euclidean plane. -/
private noncomputable def planePoint (x y : ℝ) : Plane :=
  WithLp.toLp 2 ![x, y]

/-- A sixty-degree rotation of the vector from `u` to `v`, based at `u`.
This is the third vertex used in the regular two-edge detour. -/
private noncomputable def equilateralThird (u v : Plane) : Plane :=
  planePoint
    (u.ofLp 0 + ((v - u).ofLp 0 / 2 - Real.sqrt 3 * (v - u).ofLp 1 / 2))
    (u.ofLp 1 + (Real.sqrt 3 * (v - u).ofLp 0 / 2 + (v - u).ofLp 1 / 2))

private theorem equilateralThird_is_unit {u v : Plane}
    (huv : Dist.dist u v = 1) :
    Dist.dist u (equilateralThird u v) = 1 ∧
      Dist.dist (equilateralThird u v) v = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hunit : (v - u).ofLp 0 ^ 2 + (v - u).ofLp 1 ^ 2 = 1 := by
    calc
      (v - u).ofLp 0 ^ 2 + (v - u).ofLp 1 ^ 2 = ‖v - u‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ]
      _ = Dist.dist u v ^ 2 := by rw [dist_eq_norm, norm_sub_rev]
      _ = 1 := by rw [huv]; norm_num
  change (v.ofLp 0 - u.ofLp 0) ^ 2 + (v.ofLp 1 - u.ofLp 1) ^ 2 = 1 at hunit
  constructor
  · have hsquare : Dist.dist u (equilateralThird u v) ^ 2 = 1 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
      simp [equilateralThird, planePoint, Fin.sum_univ_succ]
      ring_nf
      rw [h3]
      ring_nf
      nlinarith [hunit]
    have hnonneg : 0 ≤ Dist.dist u (equilateralThird u v) := dist_nonneg
    nlinarith
  · have hsquare : Dist.dist (equilateralThird u v) v ^ 2 = 1 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
      simp [equilateralThird, planePoint, Fin.sum_univ_succ]
      ring_nf
      rw [h3]
      ring_nf
      nlinarith [hunit]
    have hnonneg : 0 ≤ Dist.dist (equilateralThird u v) v := dist_nonneg
    nlinarith

/-- The elementary infinitesimal-rigidity calculation behind insertion of a
two-vertex equilateral detour.  The old and duplicate velocities agree; if
the old one vanishes, so does the middle velocity. -/
private theorem equilateral_detour_velocity
    (x y : ℝ) (hunit : x ^ 2 + y ^ 2 = 1) (a b c : Plane)
    (ha : x * a.ofLp 0 + y * a.ofLp 1 = 0)
    (hb : (x / 2 - Real.sqrt 3 * y / 2) * b.ofLp 0 +
      (Real.sqrt 3 * x / 2 + y / 2) * b.ofLp 1 = 0)
    (hab : (-x / 2 - Real.sqrt 3 * y / 2) * (b - a).ofLp 0 +
      (Real.sqrt 3 * x / 2 - y / 2) * (b - a).ofLp 1 = 0)
    (hc : x * c.ofLp 0 + y * c.ofLp 1 = 0)
    (hbc : (x / 2 + Real.sqrt 3 * y / 2) * (c - b).ofLp 0 +
      (-Real.sqrt 3 * x / 2 + y / 2) * (c - b).ofLp 1 = 0) :
    c = a ∧ (a = 0 → b = 0) := by
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  change (-x / 2 - Real.sqrt 3 * y / 2) * (b.ofLp 0 - a.ofLp 0) +
    (Real.sqrt 3 * x / 2 - y / 2) * (b.ofLp 1 - a.ofLp 1) = 0 at hab
  change (x / 2 + Real.sqrt 3 * y / 2) * (c.ofLp 0 - b.ofLp 0) +
    (-Real.sqrt 3 * x / 2 + y / 2) * (c.ofLp 1 - b.ofLp 1) = 0 at hbc
  have hdifference : x * (c.ofLp 0 - a.ofLp 0) +
      y * (c.ofLp 1 - a.ofLp 1) = 0 := by
    linear_combination hc - ha
  have hangled : (-x / 2 - Real.sqrt 3 * y / 2) * (c.ofLp 0 - a.ofLp 0) +
      (Real.sqrt 3 * x / 2 - y / 2) * (c.ofLp 1 - a.ofLp 1) = 0 := by
    linear_combination hab - hbc
  have hperp : -y * (c.ofLp 0 - a.ofLp 0) +
      x * (c.ofLp 1 - a.ofLp 1) = 0 := by
    nlinarith
  have hcx : c.ofLp 0 = a.ofLp 0 := by
    linear_combination x * hdifference - y * hperp -
      (c.ofLp 0 - a.ofLp 0) * hunit
  have hcy : c.ofLp 1 = a.ofLp 1 := by
    linear_combination y * hdifference + x * hperp -
      (c.ofLp 1 - a.ofLp 1) * hunit
  have hca : c = a := by
    apply PiLp.ext
    intro i
    fin_cases i
    · exact hcx
    · exact hcy
  refine ⟨hca, ?_⟩
  intro hazero
  have hax : a.ofLp 0 = 0 := by simp [hazero]
  have hay : a.ofLp 1 = 0 := by simp [hazero]
  rw [hax, hay] at hab
  have hbdot : x * b.ofLp 0 + y * b.ofLp 1 = 0 := by
    linear_combination hb - hab
  have hbperp : -y * b.ofLp 0 + x * b.ofLp 1 = 0 := by
    nlinarith
  have hbx : b.ofLp 0 = 0 := by
    linear_combination x * hbdot - y * hbperp - b.ofLp 0 * hunit
  have hby : b.ofLp 1 = 0 := by
    linear_combination y * hbdot + x * hbperp - b.ofLp 1 * hunit
  apply PiLp.ext
  intro i
  fin_cases i <;> simp_all

private def lastFin (r : ℕ) [NeZero r] : Fin r :=
  ⟨r - 1, Nat.sub_lt (Nat.zero_lt_of_ne_zero (NeZero.ne r)) (by omega)⟩

private def oldFin {r : ℕ} (i : Fin r) : Fin (r + 2) :=
  ⟨i.val, by omega⟩

private def detourFin (r : ℕ) : Fin (r + 2) := ⟨r, by omega⟩

private def duplicateFin (r : ℕ) : Fin (r + 2) := ⟨r + 1, by omega⟩

/-- Append a pair of shadows of the last foundation entry. -/
private def extendFoundationAtLast {r : ℕ} [NeZero r]
    (u : Fin r → Plane) : Fin (r + 2) → Plane := fun i =>
  if h : i.val < r then u ⟨i.val, h⟩ else u (lastFin r)

/-- Replace the closing edge after the old last cycle vertex by the detour
`v_last -- w -- v_last`, where `w` is the equilateral third point. -/
private noncomputable def extendCycleAtLast {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) : Fin (r + 2) → Plane := fun i =>
  if h : i.val < r then v ⟨i.val, h⟩
  else if i.val = r then equilateralThird (u (lastFin r)) (v (lastFin r))
  else v (lastFin r)

@[simp] private theorem extendFoundationAtLast_old {r : ℕ} [NeZero r]
    (u : Fin r → Plane) (i : Fin r) :
    extendFoundationAtLast u (oldFin i) = u i := by
  simp [extendFoundationAtLast, oldFin]

@[simp] private theorem extendFoundationAtLast_detour {r : ℕ} [NeZero r]
    (u : Fin r → Plane) :
    extendFoundationAtLast u (detourFin r) = u (lastFin r) := by
  simp [extendFoundationAtLast, detourFin]

@[simp] private theorem extendFoundationAtLast_duplicate {r : ℕ} [NeZero r]
    (u : Fin r → Plane) :
    extendFoundationAtLast u (duplicateFin r) = u (lastFin r) := by
  simp [extendFoundationAtLast, duplicateFin]

@[simp] private theorem extendCycleAtLast_old {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) (i : Fin r) :
    extendCycleAtLast u v (oldFin i) = v i := by
  simp [extendCycleAtLast, oldFin]

@[simp] private theorem extendCycleAtLast_detour {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    extendCycleAtLast u v (detourFin r) =
      equilateralThird (u (lastFin r)) (v (lastFin r)) := by
  simp [extendCycleAtLast, detourFin]

@[simp] private theorem extendCycleAtLast_duplicate {r : ℕ} [NeZero r]
    (u v : Fin r → Plane) :
    extendCycleAtLast u v (duplicateFin r) = v (lastFin r) := by
  simp [extendCycleAtLast, duplicateFin]

private theorem oldFin_succ_of_lt {r : ℕ} [NeZero r] (i : Fin r)
    (hi : i.val + 1 < r) :
    oldFin i + 1 = oldFin ⟨i.val + 1, hi⟩ := by
  apply Fin.ext
  rw [Fin.val_add]
  simp [oldFin, Nat.mod_eq_of_lt (by omega : i.val + 1 < r + 2)]

private theorem oldFin_last_succ {r : ℕ} [NeZero r] :
    oldFin (lastFin r) + 1 = detourFin r := by
  apply Fin.ext
  rw [Fin.val_add]
  simp [oldFin, lastFin, detourFin,
    Nat.sub_add_cancel (Nat.zero_lt_of_ne_zero (NeZero.ne r)),
    Nat.mod_eq_of_lt (by omega : r < r + 2)]

private theorem detourFin_succ (r : ℕ) :
    detourFin r + 1 = duplicateFin r := by
  apply Fin.ext
  rw [Fin.val_add]
  simp [detourFin, duplicateFin, Nat.mod_eq_of_lt (by omega : r + 1 < r + 2)]

private theorem duplicateFin_succ (r : ℕ) :
    duplicateFin r + 1 = (0 : Fin (r + 2)) := by
  apply Fin.ext
  rw [Fin.val_add]
  simp [duplicateFin]

/-- Exact unit attachments are preserved by the two-vertex detour. -/
private theorem extendAtLast_is_attachment {r : ℕ} [NeZero r]
    {u v : Fin r → Plane}
    (hunit : (∀ i, Dist.dist (u i) (v i) = 1) ∧
      ∀ i, Dist.dist (v i) (v (i + 1)) = 1) :
    (∀ i, Dist.dist (extendFoundationAtLast u i) (extendCycleAtLast u v i) = 1) ∧
      ∀ i, Dist.dist (extendCycleAtLast u v i)
        (extendCycleAtLast u v (i + 1)) = 1 := by
  have hlast := hunit.1 (lastFin r)
  have heq := equilateralThird_is_unit hlast
  constructor
  · intro i
    by_cases hi : i.val < r
    · let j : Fin r := ⟨i.val, hi⟩
      have hij : i = oldFin j := by apply Fin.ext; rfl
      rw [hij]
      simpa using hunit.1 j
    · by_cases hir : i.val = r
      · have hiDetour : i = detourFin r := by apply Fin.ext; exact hir
        rw [hiDetour]
        simpa using heq.1
      · have hiDuplicate : i = duplicateFin r := by
          apply Fin.ext
          change i.val = r + 1
          omega
        rw [hiDuplicate]
        simpa using hlast
  · intro i
    by_cases hi : i.val < r
    · let j : Fin r := ⟨i.val, hi⟩
      have hij : i = oldFin j := by apply Fin.ext; rfl
      by_cases hj : j.val + 1 < r
      · rw [hij, oldFin_succ_of_lt j hj]
        have hjnext : j + 1 = (⟨j.val + 1, hj⟩ : Fin r) := by
          apply Fin.ext
          rw [Fin.val_add]
          simp [Nat.mod_eq_of_lt hj]
        simpa [hjnext] using hunit.2 j
      · have hjlast : j = lastFin r := by
          apply Fin.ext
          change j.val = r - 1
          omega
        have hilast : i = oldFin (lastFin r) := hij.trans (congrArg oldFin hjlast)
        rw [hilast, oldFin_last_succ]
        rw [extendCycleAtLast_old, extendCycleAtLast_detour]
        rw [dist_eq_norm, norm_sub_rev]
        simpa only [dist_eq_norm] using heq.2
    · by_cases hir : i.val = r
      · have hiDetour : i = detourFin r := by apply Fin.ext; exact hir
        rw [hiDetour, detourFin_succ]
        simpa using heq.2
      · have hiDuplicate : i = duplicateFin r := by
          apply Fin.ext
          change i.val = r + 1
          omega
        rw [hiDuplicate, duplicateFin_succ]
        have hzero : (0 : Fin (r + 2)) = oldFin (0 : Fin r) := by
          apply Fin.ext
          rfl
        rw [hzero]
        have hnext : lastFin r + 1 = (0 : Fin r) := by
          apply Fin.ext
          rw [Fin.val_add]
          simp [lastFin, Nat.sub_add_cancel
            (Nat.zero_lt_of_ne_zero (NeZero.ne r))]
        simpa [hnext] using hunit.2 (lastFin r)

/-- The detour adds four equations and four cycle coordinates without adding
an infinitesimal flex. -/
private theorem extendAtLast_derivative_injective {r : ℕ} [NeZero r]
    {u v : Fin r → Plane}
    (hunit : ∀ i, Dist.dist (u i) (v i) = 1)
    (hinjective : Function.Injective (attachmentCycleDerivative u v)) :
    Function.Injective (attachmentCycleDerivative
      (extendFoundationAtLast u) (extendCycleAtLast u v)) := by
  let iLast := lastFin r
  let iOld := oldFin iLast
  let iMiddle := detourFin r
  let iDuplicate := duplicateFin r
  have hkernel : ∀ w : Fin (r + 2) → Plane,
      attachmentCycleDerivative (extendFoundationAtLast u) (extendCycleAtLast u v) w = 0 →
        w = 0 := by
    intro w hw
    have haInner := spoke_inner_eq_zero_of_derivative_eq_zero hw iOld
    have hbInner := spoke_inner_eq_zero_of_derivative_eq_zero hw iMiddle
    have hcInner := spoke_inner_eq_zero_of_derivative_eq_zero hw iDuplicate
    have habInner := cycle_inner_eq_zero_of_derivative_eq_zero hw iOld
    have hbcInner := cycle_inner_eq_zero_of_derivative_eq_zero hw iMiddle
    have hOldSucc : iOld + 1 = iMiddle := by
      dsimp only [iOld, iMiddle, iLast]
      exact oldFin_last_succ
    have hMiddleSucc : iMiddle + 1 = iDuplicate := by
      dsimp only [iMiddle, iDuplicate]
      exact detourFin_succ r
    rw [hOldSucc] at habInner
    rw [hMiddleSucc] at hbcInner
    have hxy : (v iLast - u iLast).ofLp 0 ^ 2 +
        (v iLast - u iLast).ofLp 1 ^ 2 = 1 := by
      calc
        (v iLast - u iLast).ofLp 0 ^ 2 + (v iLast - u iLast).ofLp 1 ^ 2 =
            ‖v iLast - u iLast‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_succ]
        _ = Dist.dist (u iLast) (v iLast) ^ 2 := by
          rw [dist_eq_norm, norm_sub_rev]
        _ = 1 := by rw [hunit iLast]; norm_num
    have ha : (v iLast - u iLast).ofLp 0 * (w iOld).ofLp 0 +
        (v iLast - u iLast).ofLp 1 * (w iOld).ofLp 1 = 0 := by
      simp [iOld, iLast, PiLp.inner_apply, Fin.sum_univ_succ] at haInner ⊢
      linear_combination haInner
    have hb : ((v iLast - u iLast).ofLp 0 / 2 -
          Real.sqrt 3 * (v iLast - u iLast).ofLp 1 / 2) * (w iMiddle).ofLp 0 +
        (Real.sqrt 3 * (v iLast - u iLast).ofLp 0 / 2 +
          (v iLast - u iLast).ofLp 1 / 2) * (w iMiddle).ofLp 1 = 0 := by
      simp [iMiddle, iLast, PiLp.inner_apply, Fin.sum_univ_succ,
        equilateralThird, planePoint] at hbInner ⊢
      linear_combination hbInner
    have hc : (v iLast - u iLast).ofLp 0 * (w iDuplicate).ofLp 0 +
        (v iLast - u iLast).ofLp 1 * (w iDuplicate).ofLp 1 = 0 := by
      simp [iDuplicate, iLast, PiLp.inner_apply, Fin.sum_univ_succ] at hcInner ⊢
      linear_combination hcInner
    have hab : (-(v iLast - u iLast).ofLp 0 / 2 -
          Real.sqrt 3 * (v iLast - u iLast).ofLp 1 / 2) *
          (w iMiddle - w iOld).ofLp 0 +
        (Real.sqrt 3 * (v iLast - u iLast).ofLp 0 / 2 -
          (v iLast - u iLast).ofLp 1 / 2) *
          (w iMiddle - w iOld).ofLp 1 = 0 := by
      simp [iOld, iMiddle, iLast, PiLp.inner_apply, Fin.sum_univ_succ,
        equilateralThird, planePoint] at habInner ⊢
      linear_combination habInner
    have hbc : ((v iLast - u iLast).ofLp 0 / 2 +
          Real.sqrt 3 * (v iLast - u iLast).ofLp 1 / 2) *
          (w iDuplicate - w iMiddle).ofLp 0 +
        (-Real.sqrt 3 * (v iLast - u iLast).ofLp 0 / 2 +
          (v iLast - u iLast).ofLp 1 / 2) *
          (w iDuplicate - w iMiddle).ofLp 1 = 0 := by
      simp [iMiddle, iDuplicate, iLast, PiLp.inner_apply, Fin.sum_univ_succ,
        equilateralThird, planePoint] at hbcInner ⊢
      linear_combination hbcInner
    have hlocal := equilateral_detour_velocity
      ((v iLast - u iLast).ofLp 0) ((v iLast - u iLast).ofLp 1) hxy
      (w iOld) (w iMiddle) (w iDuplicate) ha hb hab hc hbc
    let z : Fin r → Plane := fun i => w (oldFin i)
    have hzSpoke : ∀ i, inner ℝ (v i - u i) (z i) = 0 := by
      intro i
      have hi := spoke_inner_eq_zero_of_derivative_eq_zero hw (oldFin i)
      simpa [z] using hi
    have hzCycle : ∀ i,
        inner ℝ (v (i + 1) - v i) (z (i + 1) - z i) = 0 := by
      intro i
      by_cases hi : i = iLast
      · subst i
        have hwrap := cycle_inner_eq_zero_of_derivative_eq_zero hw iDuplicate
        rw [duplicateFin_succ] at hwrap
        have hzero : (0 : Fin (r + 2)) = oldFin (0 : Fin r) := by
          apply Fin.ext
          rfl
        rw [hzero] at hwrap
        have hnext : iLast + 1 = (0 : Fin r) := by
          dsimp only [iLast]
          apply Fin.ext
          rw [Fin.val_add]
          simp [lastFin, Nat.sub_add_cancel
            (Nat.zero_lt_of_ne_zero (NeZero.ne r))]
        rw [hnext]
        rw [hlocal.1] at hwrap
        simpa [z, iOld, iLast, iDuplicate] using hwrap
      · have hiVal : i.val + 1 < r := by
          have hilastVal : iLast.val = r - 1 := rfl
          by_contra h
          have : i.val = r - 1 := by omega
          exact hi (Fin.ext this)
        have hOld := cycle_inner_eq_zero_of_derivative_eq_zero hw (oldFin i)
        rw [oldFin_succ_of_lt i hiVal] at hOld
        have hinext : i + 1 = (⟨i.val + 1, hiVal⟩ : Fin r) := by
          apply Fin.ext
          rw [Fin.val_add]
          simp [Nat.mod_eq_of_lt hiVal]
        simpa [z, hinext] using hOld
    have hzZero : z = 0 := by
      apply hinjective
      simpa using attachmentCycleDerivative_eq_zero_of_inner hzSpoke hzCycle
    have hOldZero : w iOld = 0 := by
      have := congrFun hzZero iLast
      simpa [z, iOld, iLast] using this
    have hMiddleZero : w iMiddle = 0 := hlocal.2 hOldZero
    have hDuplicateZero : w iDuplicate = 0 := hlocal.1.trans hOldZero
    apply funext
    intro i
    by_cases hi : i.val < r
    · let j : Fin r := ⟨i.val, hi⟩
      have hij : i = oldFin j := by apply Fin.ext; rfl
      rw [hij]
      have := congrFun hzZero j
      simpa [z] using this
    · by_cases hir : i.val = r
      · have : i = iMiddle := by apply Fin.ext; exact hir
        simpa [this] using hMiddleZero
      · have : i = iDuplicate := by
          apply Fin.ext
          dsimp only [iDuplicate]
          have hlo : r < i.val :=
            lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm hir)
          have hupper : i.val ≤ r + 1 := by
            rw [← Nat.lt_succ_iff]
            simpa [Nat.add_assoc] using i.isLt
          exact Nat.le_antisymm hupper (Nat.succ_le_iff.mpr hlo)
        simpa [this] using hDuplicateZero
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel (a - b)
  rw [map_sub, hab, sub_self]

private def rotateFinFamily {r : ℕ} [NeZero r]
    (s : Fin r) (f : Fin r → Plane) : Fin r → Plane := fun i => f (i + s)

private theorem rotateFinFamily_is_attachment {r : ℕ} [NeZero r]
    {u v : Fin r → Plane}
    (hunit : (∀ i, Dist.dist (u i) (v i) = 1) ∧
      ∀ i, Dist.dist (v i) (v (i + 1)) = 1) (s : Fin r) :
    (∀ i, Dist.dist (rotateFinFamily s u i) (rotateFinFamily s v i) = 1) ∧
      ∀ i, Dist.dist (rotateFinFamily s v i)
        (rotateFinFamily s v (i + 1)) = 1 := by
  constructor
  · intro i
    exact hunit.1 (i + s)
  · intro i
    have hindex : (i + 1) + s = (i + s) + 1 := by ac_rfl
    rw [rotateFinFamily, rotateFinFamily, hindex]
    exact hunit.2 (i + s)

private theorem rotateFinFamily_derivative_injective {r : ℕ} [NeZero r]
    {u v : Fin r → Plane}
    (hinjective : Function.Injective (attachmentCycleDerivative u v)) (s : Fin r) :
    Function.Injective
      (attachmentCycleDerivative (rotateFinFamily s u) (rotateFinFamily s v)) := by
  have hkernel : ∀ w : Fin r → Plane,
      attachmentCycleDerivative (rotateFinFamily s u) (rotateFinFamily s v) w = 0 →
        w = 0 := by
    intro w hw
    let z : Fin r → Plane := fun i => w (i - s)
    have hzSpoke : ∀ i, inner ℝ (v i - u i) (z i) = 0 := by
      intro i
      have hi := spoke_inner_eq_zero_of_derivative_eq_zero hw (i - s)
      simpa [rotateFinFamily, z] using hi
    have hzCycle : ∀ i,
        inner ℝ (v (i + 1) - v i) (z (i + 1) - z i) = 0 := by
      intro i
      have hi := cycle_inner_eq_zero_of_derivative_eq_zero hw (i - s)
      have hnext : (i - s + 1) + s = i + 1 := by abel
      have hbase : (i - s) + s = i := sub_add_cancel i s
      have hznext : i + 1 - s = i - s + 1 := by abel
      simpa [rotateFinFamily, z, hnext, hbase, hznext] using hi
    have hzZero : z = 0 := by
      apply hinjective
      simpa using attachmentCycleDerivative_eq_zero_of_inner hzSpoke hzCycle
    apply funext
    intro i
    have hi := congrFun hzZero (i + s)
    simpa [z] using hi
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel (a - b)
  rw [map_sub, hab, sub_self]

/-- Rotate an attachment so that a prescribed entry becomes the last one. -/
private def rotateToLast {r : ℕ} [NeZero r]
    (q : Fin r) (f : Fin r → Plane) : Fin r → Plane :=
  rotateFinFamily (q - lastFin r) f

@[simp] private theorem rotateToLast_apply_last {r : ℕ} [NeZero r]
    (q : Fin r) (f : Fin r → Plane) :
    rotateToLast q f (lastFin r) = f q := by
  simp [rotateToLast, rotateFinFamily]

/-- A unit attachment together with the regularity certificate required by
the implicit-function theorem. -/
private structure RegularAttachment (r : ℕ) [NeZero r] where
  foundation : Fin r → Plane
  cycle : Fin r → Plane
  isAttachment : (∀ i, Dist.dist (foundation i) (cycle i) = 1) ∧
    ∀ i, Dist.dist (cycle i) (cycle (i + 1)) = 1
  derivativeInjective : Function.Injective
    (attachmentCycleDerivative foundation cycle)

private noncomputable def RegularAttachment.rotate {r : ℕ} [NeZero r]
    (A : RegularAttachment r) (s : Fin r) : RegularAttachment r where
  foundation := rotateFinFamily s A.foundation
  cycle := rotateFinFamily s A.cycle
  isAttachment := rotateFinFamily_is_attachment A.isAttachment s
  derivativeInjective := rotateFinFamily_derivative_injective A.derivativeInjective s

private noncomputable def RegularAttachment.rotateLast {r : ℕ} [NeZero r]
    (A : RegularAttachment r) (q : Fin r) : RegularAttachment r :=
  A.rotate (q - lastFin r)

private noncomputable def RegularAttachment.extendLast {r : ℕ} [NeZero r]
    (A : RegularAttachment r) : RegularAttachment (r + 2) where
  foundation := extendFoundationAtLast A.foundation
  cycle := extendCycleAtLast A.foundation A.cycle
  isAttachment := extendAtLast_is_attachment A.isAttachment
  derivativeInjective := extendAtLast_derivative_injective A.isAttachment.1
    A.derivativeInjective

/-- Three consecutive corners of the unit square. -/
private noncomputable def squareCornerFoundation : Fin 3 → Plane
  | 0 => planePoint 0 0
  | 1 => planePoint 1 0
  | 2 => planePoint 1 1

/-- An equilateral triangle attached to three consecutive unit-square corners. -/
private noncomputable def squareCornerTriangle : Fin 3 → Plane
  | 0 => planePoint 0 1
  | 1 => planePoint 1 1
  | 2 => planePoint (1 / 2) (1 + Real.sqrt 3 / 2)

private def nextFinThree : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

private theorem nextFinThree_eq_add_one (i : Fin 3) : nextFinThree i = i + 1 := by
  fin_cases i <;> rfl

/-- The exact algebraic base configuration replacing O'Donnell's decimal
short/long certificate for three occupied clusters. -/
private theorem squareCornerTriangle_is_attachment :
    (∀ i, Dist.dist (squareCornerFoundation i) (squareCornerTriangle i) = 1) ∧
      ∀ i, Dist.dist (squareCornerTriangle i)
        (squareCornerTriangle (nextFinThree i)) = 1 := by
  constructor
  · intro i
    fin_cases i <;>
      norm_num [squareCornerFoundation, squareCornerTriangle, planePoint, dist_eq_norm,
        EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;>
      ring_nf <;>
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
      norm_num
  · intro i
    fin_cases i <;>
      norm_num [nextFinThree, squareCornerTriangle, planePoint, dist_eq_norm,
        EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;>
      ring_nf <;>
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
      norm_num

/-- The three-corner attachment is a regular point of the attachment
equations. -/
private theorem squareCornerTriangle_derivative_injective :
    Function.Injective
      (attachmentCycleDerivative squareCornerFoundation squareCornerTriangle) := by
  have hkernel : ∀ w,
      attachmentCycleDerivative squareCornerFoundation squareCornerTriangle w = 0 → w = 0 := by
    intro w hw
    have hs0 := congrFun hw (Sum.inl (0 : Fin 3))
    have hs1 := congrFun hw (Sum.inl (1 : Fin 3))
    have hs2 := congrFun hw (Sum.inl (2 : Fin 3))
    have hc0 := congrFun hw (Sum.inr (0 : Fin 3))
    have hc1 := congrFun hw (Sum.inr (1 : Fin 3))
    have hc2 := congrFun hw (Sum.inr (2 : Fin 3))
    norm_num [attachmentCycleDerivative, innerSL_apply_apply, PiLp.inner_apply,
      squareCornerFoundation, squareCornerTriangle, planePoint,
      EuclideanSpace.norm_eq, Fin.sum_univ_succ] at hs0 hs1 hs2 hc0 hc1 hc2
    simp at hc1 hc2
    apply funext
    intro i
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hab, sub_self]

private noncomputable def squareCornerRegularAttachment : RegularAttachment 3 where
  foundation := squareCornerFoundation
  cycle := squareCornerTriangle
  isAttachment := ⟨squareCornerTriangle_is_attachment.1, by
    intro i
    rw [← nextFinThree_eq_add_one]
    exact squareCornerTriangle_is_attachment.2 i⟩
  derivativeInjective := squareCornerTriangle_derivative_injective

/-- A `(2,1)` shadow on two adjacent unit-square corners. -/
private noncomputable def sidePairFoundation : Fin 3 → Plane
  | 0 => planePoint 0 0
  | 1 => planePoint 0 0
  | 2 => planePoint 1 0

private noncomputable def sidePairTriangle : Fin 3 → Plane
  | 0 => planePoint 1 0
  | 1 => planePoint (1 / 2) (Real.sqrt 3 / 2)
  | 2 => planePoint (3 / 2) (Real.sqrt 3 / 2)

/-- Exact base attachment for adjacent cluster centers. -/
private theorem sidePairTriangle_is_attachment :
    (∀ i, Dist.dist (sidePairFoundation i) (sidePairTriangle i) = 1) ∧
      ∀ i, Dist.dist (sidePairTriangle i) (sidePairTriangle (nextFinThree i)) = 1 := by
  constructor <;> intro i <;>
    fin_cases i <;>
    norm_num [nextFinThree, sidePairFoundation, sidePairTriangle, planePoint, dist_eq_norm,
      EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;>
    ring_nf <;>
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] <;>
    norm_num

/-- The adjacent-corner `(2,1)` attachment is regular. -/
private theorem sidePairTriangle_derivative_injective :
    Function.Injective
      (attachmentCycleDerivative sidePairFoundation sidePairTriangle) := by
  have hkernel : ∀ w,
      attachmentCycleDerivative sidePairFoundation sidePairTriangle w = 0 → w = 0 := by
    intro w hw
    have hs0 := congrFun hw (Sum.inl (0 : Fin 3))
    have hs1 := congrFun hw (Sum.inl (1 : Fin 3))
    have hs2 := congrFun hw (Sum.inl (2 : Fin 3))
    have hc0 := congrFun hw (Sum.inr (0 : Fin 3))
    have hc1 := congrFun hw (Sum.inr (1 : Fin 3))
    have hc2 := congrFun hw (Sum.inr (2 : Fin 3))
    norm_num [attachmentCycleDerivative, innerSL_apply_apply, PiLp.inner_apply,
      sidePairFoundation, sidePairTriangle, planePoint,
      EuclideanSpace.norm_eq, Fin.sum_univ_succ] at hs0 hs1 hs2 hc0 hc1 hc2
    simp at hc1 hc2
    apply funext
    intro i
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;>
      simp <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hab, sub_self]

private noncomputable def sidePairRegularAttachment : RegularAttachment 3 where
  foundation := sidePairFoundation
  cycle := sidePairTriangle
  isAttachment := ⟨sidePairTriangle_is_attachment.1, by
    intro i
    rw [← nextFinThree_eq_add_one]
    exact sidePairTriangle_is_attachment.2 i⟩
  derivativeInjective := sidePairTriangle_derivative_injective

/-- A `(2,1)` shadow on opposite unit-square corners. -/
private noncomputable def diagonalPairFoundation : Fin 3 → Plane
  | 0 => planePoint 0 0
  | 1 => planePoint 0 0
  | 2 => planePoint 1 1

private noncomputable def diagonalTipX : ℝ := 1 + Real.sqrt 2 / 2
private noncomputable def diagonalTipY : ℝ := 1 - Real.sqrt 2 / 2

private noncomputable def diagonalPairTriangle : Fin 3 → Plane
  | 0 => planePoint
      (diagonalTipX / 2 - diagonalTipY * Real.sqrt 3 / 6)
      (diagonalTipY / 2 + diagonalTipX * Real.sqrt 3 / 6)
  | 1 => planePoint
      (diagonalTipX / 2 + diagonalTipY * Real.sqrt 3 / 6)
      (diagonalTipY / 2 - diagonalTipX * Real.sqrt 3 / 6)
  | 2 => planePoint diagonalTipX diagonalTipY

/-- Exact base attachment for diagonal cluster centers. -/
private theorem diagonalPairTriangle_is_attachment :
    (∀ i, Dist.dist (diagonalPairFoundation i) (diagonalPairTriangle i) = 1) ∧
      ∀ i, Dist.dist (diagonalPairTriangle i)
        (diagonalPairTriangle (nextFinThree i)) = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  constructor <;> intro i <;>
    fin_cases i <;>
    norm_num [nextFinThree, diagonalPairFoundation, diagonalPairTriangle,
      diagonalTipX, diagonalTipY, planePoint, dist_eq_norm, EuclideanSpace.norm_eq,
      Fin.sum_univ_succ] <;>
    ring_nf at * <;>
    nlinarith

/-- The diagonal-corner `(2,1)` attachment is regular. -/
private theorem diagonalPairTriangle_derivative_injective :
    Function.Injective
      (attachmentCycleDerivative diagonalPairFoundation diagonalPairTriangle) := by
  have hkernel : ∀ w,
      attachmentCycleDerivative diagonalPairFoundation diagonalPairTriangle w = 0 → w = 0 := by
    intro w hw
    have hs0 := congrFun hw (Sum.inl (0 : Fin 3))
    have hs1 := congrFun hw (Sum.inl (1 : Fin 3))
    have hs2 := congrFun hw (Sum.inl (2 : Fin 3))
    have hc0 := congrFun hw (Sum.inr (0 : Fin 3))
    have hc1 := congrFun hw (Sum.inr (1 : Fin 3))
    have hc2 := congrFun hw (Sum.inr (2 : Fin 3))
    norm_num [attachmentCycleDerivative, innerSL_apply_apply, PiLp.inner_apply,
      diagonalPairFoundation, diagonalPairTriangle, diagonalTipX, diagonalTipY,
      planePoint, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
      at hs0 hs1 hs2 hc0 hc1 hc2
    simp at hc1 hc2
    ring_nf at hs0 hs1 hs2 hc0 hc1 hc2
    let s : ℝ := Real.sqrt 2
    let t : ℝ := Real.sqrt 3
    have e0 : (s * t / 12 + s / 4 - t / 6 + 1 / 2) * (w 0).ofLp 0 +
        (s * t / 12 - s / 4 + t / 6 + 1 / 2) * (w 0).ofLp 1 = 0 := by
      dsimp [s, t]
      linear_combination (1 / 2 : ℝ) * hs0
    have e1 : (-s * t / 12 + s / 4 + t / 6 + 1 / 2) * (w 1).ofLp 0 +
        (-s * t / 12 - s / 4 - t / 6 + 1 / 2) * (w 1).ofLp 1 = 0 := by
      dsimp [s, t]
      linear_combination (1 / 2 : ℝ) * hs1
    have e2 : s / 2 * (w 2).ofLp 0 - s / 2 * (w 2).ofLp 1 = 0 := by
      dsimp [s]
      linear_combination hs2
    have e3 : (s * t / 6 - t / 3) * (w 0).ofLp 0 +
        (s * t / 6 + t / 3) * (w 0).ofLp 1 +
        (-s * t / 6 + t / 3) * (w 1).ofLp 0 +
        (-s * t / 6 - t / 3) * (w 1).ofLp 1 = 0 := by
      dsimp [s, t]
      linear_combination hc0
    have e4 : (-s * t / 12 - s / 4 + t / 6 - 1 / 2) * (w 1).ofLp 0 +
        (-s * t / 12 + s / 4 - t / 6 - 1 / 2) * (w 1).ofLp 1 +
        (s * t / 12 + s / 4 - t / 6 + 1 / 2) * (w 2).ofLp 0 +
        (s * t / 12 - s / 4 + t / 6 + 1 / 2) * (w 2).ofLp 1 = 0 := by
      dsimp [s, t]
      linear_combination hc1
    have e5 : (s * t / 12 - s / 4 - t / 6 - 1 / 2) * (w 0).ofLp 0 +
        (s * t / 12 + s / 4 + t / 6 - 1 / 2) * (w 0).ofLp 1 +
        (-s * t / 12 + s / 4 + t / 6 + 1 / 2) * (w 2).ofLp 0 +
        (-s * t / 12 - s / 4 - t / 6 + 1 / 2) * (w 2).ofLp 1 = 0 := by
      dsimp [s, t]
      linear_combination hc2
    have hx0 : 12 * s * t * (s ^ 2 + 4) * (w 0).ofLp 0 = 0 := by
      linear_combination
        (-s * (s ^ 2 * t ^ 2 - 3 * s ^ 2 * t + 2 * s * t ^ 2 - 12 * s * t -
          18 * s - 36 * t + 36)) * e0 +
        (-s * (s * t - 6) * (s * t - 3 * s + 2 * t + 6)) * e1 +
        (t * (s ^ 2 + 4) * (s * t - 3 * s + 2 * t + 6)) * e2 +
        (s * (s * t - 6) * (s * t - 3 * s + 2 * t + 6)) * e3 +
        (-s * (s * t - 6) * (s * t - 3 * s + 2 * t + 6)) * e4 +
        (-s * (s * t + 6) * (s * t - 3 * s + 2 * t + 6)) * e5
    have hy0 : 12 * s * t * (s ^ 2 + 4) * (w 0).ofLp 1 = 0 := by
      linear_combination
        (s * (s ^ 2 * t ^ 2 + 3 * s ^ 2 * t - 2 * s * t ^ 2 - 12 * s * t +
          18 * s + 36 * t + 36)) * e0 +
        (s * (s * t - 6) * (s * t + 3 * s - 2 * t + 6)) * e1 +
        (-t * (s ^ 2 + 4) * (s * t + 3 * s - 2 * t + 6)) * e2 +
        (-s * (s * t - 6) * (s * t + 3 * s - 2 * t + 6)) * e3 +
        (s * (s * t - 6) * (s * t + 3 * s - 2 * t + 6)) * e4 +
        (s * (s * t + 6) * (s * t + 3 * s - 2 * t + 6)) * e5
    have hx1 : 12 * s * t * (s ^ 2 + 4) * (w 1).ofLp 0 = 0 := by
      linear_combination
        (s * (s * t + 6) * (s * t + 3 * s + 2 * t - 6)) * e0 +
        (s * (s ^ 2 * t ^ 2 + 3 * s ^ 2 * t + 2 * s * t ^ 2 + 12 * s * t -
          18 * s + 36 * t + 36)) * e1 +
        (-t * (s ^ 2 + 4) * (s * t + 3 * s + 2 * t - 6)) * e2 +
        (-s * (s * t + 6) * (s * t + 3 * s + 2 * t - 6)) * e3 +
        (s * (s * t - 6) * (s * t + 3 * s + 2 * t - 6)) * e4 +
        (s * (s * t + 6) * (s * t + 3 * s + 2 * t - 6)) * e5
    have hy1 : 12 * s * t * (s ^ 2 + 4) * (w 1).ofLp 1 = 0 := by
      linear_combination
        (-s * (s * t + 6) * (s * t - 3 * s - 2 * t - 6)) * e0 +
        (-s * (s ^ 2 * t ^ 2 - 3 * s ^ 2 * t - 2 * s * t ^ 2 + 12 * s * t +
          18 * s - 36 * t + 36)) * e1 +
        (t * (s ^ 2 + 4) * (s * t - 3 * s - 2 * t - 6)) * e2 +
        (s * (s * t + 6) * (s * t - 3 * s - 2 * t - 6)) * e3 +
        (-s * (s * t - 6) * (s * t - 3 * s - 2 * t - 6)) * e4 +
        (-s * (s * t + 6) * (s * t - 3 * s - 2 * t - 6)) * e5
    have hx2 : 2 * s * (w 2).ofLp 0 = 0 := by
      linear_combination s * e0 + s * e1 - (s - 2) * e2 - s * e3 + s * e4 + s * e5
    have hy2 : 2 * s * (w 2).ofLp 1 = 0 := by
      linear_combination s * e0 + s * e1 - (s + 2) * e2 - s * e3 + s * e4 + s * e5
    have hlarge : 12 * s * t * (s ^ 2 + 4) ≠ 0 := by
      dsimp [s, t]
      positivity
    have hsmall : 2 * s ≠ 0 := by
      dsimp [s]
      positivity
    have zx0 : (w 0).ofLp 0 = 0 := (mul_eq_zero.mp hx0).resolve_left hlarge
    have zy0 : (w 0).ofLp 1 = 0 := (mul_eq_zero.mp hy0).resolve_left hlarge
    have zx1 : (w 1).ofLp 0 = 0 := (mul_eq_zero.mp hx1).resolve_left hlarge
    have zy1 : (w 1).ofLp 1 = 0 := (mul_eq_zero.mp hy1).resolve_left hlarge
    have zx2 : (w 2).ofLp 0 = 0 := (mul_eq_zero.mp hx2).resolve_left hsmall
    have zy2 : (w 2).ofLp 1 = 0 := (mul_eq_zero.mp hy2).resolve_left hsmall
    apply funext
    intro i
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp_all
  intro a b hab
  apply sub_eq_zero.mp
  apply hkernel
  rw [map_sub, hab, sub_self]

private noncomputable def diagonalPairRegularAttachment : RegularAttachment 3 where
  foundation := diagonalPairFoundation
  cycle := diagonalPairTriangle
  isAttachment := ⟨diagonalPairTriangle_is_attachment.1, by
    intro i
    rw [← nextFinThree_eq_add_one]
    exact diagonalPairTriangle_is_attachment.2 i⟩
  derivativeInjective := diagonalPairTriangle_derivative_injective

private def oddAttachmentSize : ℕ → ℕ
  | 0 => 3
  | m + 1 => oddAttachmentSize m + 2

private instance oddAttachmentSize_neZero (m : ℕ) : NeZero (oddAttachmentSize m) :=
  ⟨by cases m <;> simp [oddAttachmentSize]⟩

private noncomputable def RegularAttachment.iterateLast
    (A : RegularAttachment 3) : (m : ℕ) → RegularAttachment (oddAttachmentSize m)
  | 0 => A
  | m + 1 => (A.iterateLast m).extendLast

private theorem oddAttachmentSize_eq (m : ℕ) : oddAttachmentSize m = 2 * m + 3 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [oddAttachmentSize, ih]; omega

private def pairSingletonIndex (m : ℕ) : Fin (oddAttachmentSize m) :=
  ⟨1, by cases m <;> simp [oddAttachmentSize]⟩

@[simp] private theorem pairSingletonIndex_val (m : ℕ) :
    (pairSingletonIndex m).val = 1 := rfl

private theorem iterateLast_pair_foundation
    (A : RegularAttachment 3) (a b : Plane)
    (hbase : ∀ i, (A.rotateLast 0).foundation i = if i = 1 then b else a)
    (m : ℕ) (i : Fin (oddAttachmentSize m)) :
    ((A.rotateLast 0).iterateLast m).foundation i =
      if i = pairSingletonIndex m then b else a := by
  classical
  induction m with
  | zero =>
      change (A.rotateLast 0).foundation i =
        if i = pairSingletonIndex 0 then b else a
      rw [show pairSingletonIndex 0 = (1 : Fin 3) by rfl]
      exact hbase i
  | succ m ih =>
      change Fin (oddAttachmentSize m + 2) at i
      simp only [RegularAttachment.iterateLast, RegularAttachment.extendLast]
      by_cases hi : i.val < oddAttachmentSize m
      · let j : Fin (oddAttachmentSize m) := ⟨i.val, hi⟩
        have hij : i = oldFin j := by apply Fin.ext; rfl
        rw [hij, extendFoundationAtLast_old, ih]
        by_cases hj : j = pairSingletonIndex m
        · rw [if_pos hj]
          rw [if_pos]
          apply Fin.ext
          simp [oldFin, hj]
        · rw [if_neg hj]
          rw [if_neg]
          intro heq
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simpa [oldFin] using hv
      · rw [extendFoundationAtLast]
        simp only [hi, ↓reduceIte, ih]
        have hlastNe : lastFin (oddAttachmentSize m) ≠ pairSingletonIndex m := by
          intro h
          have hv := congrArg Fin.val h
          simp [lastFin, oddAttachmentSize_eq] at hv
        have hiNe : i ≠ oldFin (pairSingletonIndex m) := by
          intro heq
          have hv := congrArg Fin.val heq
          simp only [oldFin] at hv
          have hslt := (pairSingletonIndex m).isLt
          omega
        rw [if_neg hlastNe]
        rw [if_neg]
        · simp
        · intro heq
          apply hiNe
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simpa [oldFin] using hv

private noncomputable def sidePairOddAttachment (m : ℕ) :
    RegularAttachment (oddAttachmentSize m) :=
  (sidePairRegularAttachment.rotateLast 0).iterateLast m

private noncomputable def diagonalPairOddAttachment (m : ℕ) :
    RegularAttachment (oddAttachmentSize m) :=
  (diagonalPairRegularAttachment.rotateLast 0).iterateLast m

private theorem sidePairOddAttachment_foundation (m : ℕ)
    (i : Fin (oddAttachmentSize m)) :
    (sidePairOddAttachment m).foundation i =
      if i = pairSingletonIndex m then planePoint 1 0 else planePoint 0 0 := by
  apply iterateLast_pair_foundation
  have hshift : (0 : Fin 3) - lastFin 3 = 1 := by decide
  intro j
  fin_cases j <;>
    norm_num [RegularAttachment.rotateLast, RegularAttachment.rotate,
      rotateFinFamily, sidePairRegularAttachment, sidePairFoundation, hshift, Fin.add_def]

private theorem diagonalPairOddAttachment_foundation (m : ℕ)
    (i : Fin (oddAttachmentSize m)) :
    (diagonalPairOddAttachment m).foundation i =
      if i = pairSingletonIndex m then planePoint 1 1 else planePoint 0 0 := by
  apply iterateLast_pair_foundation
  have hshift : (0 : Fin 3) - lastFin 3 = 1 := by decide
  intro j
  fin_cases j <;>
    norm_num [RegularAttachment.rotateLast, RegularAttachment.rotate,
      rotateFinFamily, diagonalPairRegularAttachment, diagonalPairFoundation, hshift, Fin.add_def]

/-! ### Rigid motions of the square attachment models -/

/-- The orientation-preserving orthogonal map represented by the unit complex
number `α + β i`. -/
private noncomputable def rotatePlane (α β : ℝ) (z : Plane) : Plane :=
  planePoint (α * z.ofLp 0 - β * z.ofLp 1) (β * z.ofLp 0 + α * z.ofLp 1)

@[simp] private theorem rotatePlane_zero (α β : ℝ) :
    rotatePlane α β 0 = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [rotatePlane, planePoint]

private theorem rotatePlane_sub (α β : ℝ) (x y : Plane) :
    rotatePlane α β (x - y) = rotatePlane α β x - rotatePlane α β y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [rotatePlane, planePoint] <;> ring

private theorem rotatePlane_inner (α β : ℝ) (hunit : α ^ 2 + β ^ 2 = 1)
    (x y : Plane) :
    inner ℝ (rotatePlane α β x) (rotatePlane α β y) = inner ℝ x y := by
  simp [rotatePlane, planePoint, PiLp.inner_apply, Fin.sum_univ_succ]
  linear_combination
    (y.ofLp 0 * x.ofLp 0 + y.ofLp 1 * x.ofLp 1) * hunit

private theorem rotatePlane_inner_adjoint (α β : ℝ) (x y : Plane) :
    inner ℝ (rotatePlane α β x) y = inner ℝ x (rotatePlane α (-β) y) := by
  simp [rotatePlane, planePoint, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

private theorem rotatePlane_inverse (α β : ℝ) (hunit : α ^ 2 + β ^ 2 = 1)
    (x : Plane) : rotatePlane α (-β) (rotatePlane α β x) = x := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [rotatePlane, planePoint]
    linear_combination (x.ofLp 0) * hunit
  · simp [rotatePlane, planePoint]
    linear_combination (x.ofLp 1) * hunit

private theorem rotatePlane_injective (α β : ℝ) (hunit : α ^ 2 + β ^ 2 = 1) :
    Function.Injective (rotatePlane α β) := by
  intro x y hxy
  have h := congrArg (rotatePlane α (-β)) hxy
  simpa [rotatePlane_inverse α β hunit] using h

private theorem dist_add_rotatePlane (α β : ℝ) (hunit : α ^ 2 + β ^ 2 = 1)
    (t x y : Plane) :
    Dist.dist (t + rotatePlane α β x) (t + rotatePlane α β y) = Dist.dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub :
      t + rotatePlane α β x - (t + rotatePlane α β y) = rotatePlane α β (x - y) := by
    rw [rotatePlane_sub]
    abel
  rw [hsub]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show ‖rotatePlane α β (x - y)‖ ^ 2 = ‖x - y‖ ^ 2 by
        simpa [real_inner_self_eq_norm_sq] using
          rotatePlane_inner α β hunit (x - y) (x - y)) with h | h
  · exact h
  · have hnonneg1 := norm_nonneg (rotatePlane α β (x - y))
    have hnonneg2 := norm_nonneg (x - y)
    nlinarith

/-- Rigid motions preserve regular attachments, including nonsingularity of
the cycle-variable Jacobian. -/
private noncomputable def RegularAttachment.rigidMap {r : ℕ} [NeZero r]
    (A : RegularAttachment r) (α β : ℝ) (t : Plane)
    (hunit : α ^ 2 + β ^ 2 = 1) : RegularAttachment r where
  foundation i := t + rotatePlane α β (A.foundation i)
  cycle i := t + rotatePlane α β (A.cycle i)
  isAttachment := by
    constructor
    · intro i
      rw [dist_add_rotatePlane α β hunit, A.isAttachment.1 i]
    · intro i
      rw [dist_add_rotatePlane α β hunit, A.isAttachment.2 i]
  derivativeInjective := by
    have hunit' : α ^ 2 + (-β) ^ 2 = 1 := by nlinarith
    have hkernel : ∀ w : Fin r → Plane,
        attachmentCycleDerivative
          (fun i ↦ t + rotatePlane α β (A.foundation i))
          (fun i ↦ t + rotatePlane α β (A.cycle i)) w = 0 → w = 0 := by
      intro w hw
      let pull : Fin r → Plane := fun i ↦ rotatePlane α (-β) (w i)
      have hspoke (i : Fin r) :
          inner ℝ (A.cycle i - A.foundation i) (pull i) = 0 := by
        have hi := spoke_inner_eq_zero_of_derivative_eq_zero hw i
        rw [show t + rotatePlane α β (A.cycle i) -
              (t + rotatePlane α β (A.foundation i)) =
              rotatePlane α β (A.cycle i - A.foundation i) by
              rw [rotatePlane_sub]; abel] at hi
        simpa [pull, rotatePlane_inner_adjoint] using hi
      have hcycle (i : Fin r) :
          inner ℝ (A.cycle (i + 1) - A.cycle i)
            (pull (i + 1) - pull i) = 0 := by
        have hi := cycle_inner_eq_zero_of_derivative_eq_zero hw i
        have hpull : pull (i + 1) - pull i =
            rotatePlane α (-β) (w (i + 1) - w i) := by
          rw [rotatePlane_sub]
        rw [show t + rotatePlane α β (A.cycle (i + 1)) -
              (t + rotatePlane α β (A.cycle i)) =
              rotatePlane α β (A.cycle (i + 1) - A.cycle i) by
              rw [rotatePlane_sub]; abel] at hi
        rw [hpull]
        simpa [rotatePlane_inner_adjoint] using hi
      have hpullDeriv : attachmentCycleDerivative A.foundation A.cycle pull = 0 :=
        attachmentCycleDerivative_eq_zero_of_inner hspoke hcycle
      have hpullZero : pull = 0 := by
        apply A.derivativeInjective
        simpa using hpullDeriv
      apply funext
      intro i
      apply rotatePlane_injective α (-β) hunit'
      simpa [pull] using congrFun hpullZero i
    intro x y hxy
    apply sub_eq_zero.mp
    apply hkernel (x - y)
    rw [map_sub, hxy, sub_self]

/-- The four reference cluster centers, in cyclic order around the unit
square. -/
private noncomputable def squareCenter : Fin 4 → Plane
  | 0 => planePoint 0 0
  | 1 => planePoint 1 0
  | 2 => planePoint 1 1
  | 3 => planePoint 0 1

/-- Whether two distinct square corners are opposite. -/
private def squarePairDiagonal : Fin 4 → Fin 4 → Prop
  | a, b => (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
      (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1)

private noncomputable instance squarePairDiagonalDecidable (a b : Fin 4) :
    Decidable (squarePairDiagonal a b) := Classical.propDecidable _

/-- Rotation coefficients carrying the standard side or diagonal vector to
the ordered square-corner pair `(a,b)`. -/
private noncomputable def squarePairAlpha (a b : Fin 4) : ℝ :=
  if (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 3 ∧ b = 2) then 1
  else if (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 3) then -1
  else 0

private noncomputable def squarePairBeta (a b : Fin 4) : ℝ :=
  if (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) then 1
  else if (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 0) ∨ (a = 3 ∧ b = 1) then -1
  else 0

private theorem squarePair_coeff_unit (a b : Fin 4) (hab : a ≠ b) :
    squarePairAlpha a b ^ 2 + squarePairBeta a b ^ 2 = 1 := by
  fin_cases a <;> fin_cases b <;>
    simp_all [squarePairAlpha, squarePairBeta]

private noncomputable def squarePairTransform (a b : Fin 4) (z : Plane) : Plane :=
  squareCenter a + rotatePlane (squarePairAlpha a b) (squarePairBeta a b) z

private theorem squarePairTransform_origin (a b : Fin 4) :
    squarePairTransform a b (planePoint 0 0) = squareCenter a := by
  apply PiLp.ext
  intro i
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [squarePairTransform, squareCenter, rotatePlane, planePoint,
      squarePairAlpha, squarePairBeta]

private theorem squarePairTransform_side (a b : Fin 4) (hab : a ≠ b)
    (hside : ¬ squarePairDiagonal a b) :
    squarePairTransform a b (planePoint 1 0) = squareCenter b := by
  fin_cases a <;> fin_cases b <;>
    simp_all [squarePairDiagonal, squarePairTransform, squareCenter, rotatePlane,
      planePoint, squarePairAlpha, squarePairBeta] <;>
    apply PiLp.ext <;> intro i <;> fin_cases i <;> norm_num

private theorem squarePairTransform_diagonal (a b : Fin 4) (hab : a ≠ b)
    (hdiag : squarePairDiagonal a b) :
    squarePairTransform a b (planePoint 1 1) = squareCenter b := by
  fin_cases a <;> fin_cases b <;>
    simp_all [squarePairDiagonal, squarePairTransform, squareCenter, rotatePlane,
      planePoint, squarePairAlpha, squarePairBeta] <;>
    apply PiLp.ext <;> intro i <;> fin_cases i <;> norm_num

/-- The side/diagonal model transported to an arbitrary ordered pair of
distinct square corners. -/
private noncomputable def squarePairOddAttachment (m : ℕ) (a b : Fin 4)
    (hab : a ≠ b) : RegularAttachment (oddAttachmentSize m) :=
  let A := if squarePairDiagonal a b then
      diagonalPairOddAttachment m else sidePairOddAttachment m
  A.rigidMap (squarePairAlpha a b) (squarePairBeta a b) (squareCenter a)
    (squarePair_coeff_unit a b hab)

private theorem squarePairOddAttachment_foundation (m : ℕ) (a b : Fin 4)
    (hab : a ≠ b) (i : Fin (oddAttachmentSize m)) :
    (squarePairOddAttachment m a b hab).foundation i =
      if i = pairSingletonIndex m then squareCenter b else squareCenter a := by
  by_cases hd : squarePairDiagonal a b
  · simp only [squarePairOddAttachment, hd, if_pos,
      RegularAttachment.rigidMap, diagonalPairOddAttachment_foundation]
    by_cases hi : i = pairSingletonIndex m
    · rw [if_pos hi, if_pos hi]
      change squarePairTransform a b (planePoint 1 1) = squareCenter b
      exact squarePairTransform_diagonal a b hab hd
    · rw [if_neg hi, if_neg hi]
      change squarePairTransform a b (planePoint 0 0) = squareCenter a
      exact squarePairTransform_origin a b
  · simp only [squarePairOddAttachment, hd, if_neg,
      if_false, RegularAttachment.rigidMap, sidePairOddAttachment_foundation]
    by_cases hi : i = pairSingletonIndex m
    · rw [if_pos hi, if_pos hi]
      change squarePairTransform a b (planePoint 1 0) = squareCenter b
      exact squarePairTransform_side a b hab hd
    · rw [if_neg hi, if_neg hi]
      change squarePairTransform a b (planePoint 0 0) = squareCenter a
      exact squarePairTransform_origin a b

private theorem add_singletonShift_eq_iff {r : ℕ} [NeZero r]
    (i q q₀ : Fin r) : i + (q₀ - q) = q₀ ↔ i = q := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    calc
      i - q = (i + (q₀ - q)) - q₀ := by abel
      _ = 0 := by rw [h]; simp
  · rintro rfl
    simp

/-- Rotate an ordered pair attachment so that its unique singleton shadow is
at the prescribed cycle index. -/
private noncomputable def squarePairAttachmentAt (m : ℕ) (a b : Fin 4)
    (hab : a ≠ b) (q : Fin (oddAttachmentSize m)) :
    RegularAttachment (oddAttachmentSize m) :=
  (squarePairOddAttachment m a b hab).rotate (pairSingletonIndex m - q)

private theorem squarePairAttachmentAt_foundation (m : ℕ) (a b : Fin 4)
    (hab : a ≠ b) (q i : Fin (oddAttachmentSize m)) :
    (squarePairAttachmentAt m a b hab q).foundation i =
      if i = q then squareCenter b else squareCenter a := by
  rw [squarePairAttachmentAt, RegularAttachment.rotate]
  change (squarePairOddAttachment m a b hab).foundation
      (i + (pairSingletonIndex m - q)) = _
  rw [squarePairOddAttachment_foundation]
  by_cases hi : i = q
  · rw [if_pos hi, if_pos ((add_singletonShift_eq_iff i q
      (pairSingletonIndex m)).2 hi)]
  · rw [if_neg hi, if_neg (mt (add_singletonShift_eq_iff i q
      (pairSingletonIndex m)).1 hi)]

private structure PairPatternData {Y : Type*} {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (cluster : Y → Fin 4) (e : J.Edge) where
  majority : Fin 4
  singleton : Fin 4
  singletonIndex : Fin r
  distinct : majority ≠ singleton
  cluster_eq : ∀ i, cluster (J.vertex e i) =
    if i = singletonIndex then singleton else majority

private noncomputable def pairPatternData {Y : Type*} {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (cluster : Y → Fin 4)
    (hr : 1 ≤ r) (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    PairPatternData J cluster e := by
  classical
  let hex := OrderedUniformHypergraph.ordered_pairCluster_pattern
    J cluster hr hpattern e
  let a := Classical.choose hex
  let hexb := Classical.choose_spec hex
  let b := Classical.choose hexb
  let hexq := Classical.choose_spec hexb
  let q := Classical.choose hexq
  let hspec := Classical.choose_spec hexq
  exact ⟨a, b, q, hspec.1, hspec.2⟩

/-- The regular model attachment selected for a pair-pattern hyperedge. -/
private noncomputable def pairEdgeRegularAttachment {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    RegularAttachment (oddAttachmentSize m) :=
  let d := pairPatternData J cluster (by cases m <;> simp [oddAttachmentSize]) hpattern e
  squarePairAttachmentAt m d.majority d.singleton d.distinct d.singletonIndex

private theorem pairEdgeRegularAttachment_foundation {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge)
    (i : Fin (oddAttachmentSize m)) :
    (pairEdgeRegularAttachment m J cluster hpattern e).foundation i =
      squareCenter (cluster (J.vertex e i)) := by
  let d := pairPatternData J cluster (by cases m <;> simp [oddAttachmentSize]) hpattern e
  change (squarePairAttachmentAt m d.majority d.singleton d.distinct
    d.singletonIndex).foundation i = _
  rw [squarePairAttachmentAt_foundation, d.cluster_eq]
  split <;> rfl

/-! ### Simultaneous local realization of all attached cycles -/

private noncomputable def pairBaseFoundation {Y : Type*}
    (cluster : Y → Fin 4) : Y → Plane := fun x ↦ squareCenter (cluster x)

private def edgeFoundation {Y : Type*} {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (e : J.Edge) (u : Y → Plane) :
    Fin r → Plane := fun i ↦ u (J.vertex e i)

private noncomputable def edgeFoundationCLM {Y : Type*} [Fintype Y] {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (e : J.Edge) :
    (Y → Plane) →L[ℝ] (Fin r → Plane) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane) (J.vertex e i)

@[simp] private theorem edgeFoundationCLM_apply {Y : Type*} [Fintype Y] {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (e : J.Edge) (u : Y → Plane) :
    edgeFoundationCLM J e u = edgeFoundation J e u := rfl

private noncomputable def edgeVelocityExtension {Y : Type*} [Fintype Y] {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (e : J.Edge)
    (z : Fin r → Plane) : Y → Plane :=
  Function.extend (J.vertex e) z (fun _ => 0)

@[simp] private theorem edgeVelocityExtension_on_edge {Y : Type*} [Fintype Y]
    {r : ℕ} (J : OrderedUniformHypergraph Y r) (e : J.Edge)
    (z : Fin r → Plane) (i : Fin r) :
    edgeVelocityExtension J e z (J.vertex e i) = z i := by
  classical
  exact (J.vertex e).injective.extend_apply z (fun _ => 0) i

private theorem edgeVelocityExtension_off_edge {Y : Type*} [Fintype Y]
    {r : ℕ} (J : OrderedUniformHypergraph Y r) (e : J.Edge)
    (z : Fin r → Plane) (x : Y) (hx : ∀ i, J.vertex e i ≠ x) :
    edgeVelocityExtension J e z x = 0 := by
  classical
  exact Function.extend_apply' (f := J.vertex e) z (fun _ => 0) x
    (fun h => by obtain ⟨i, hi⟩ := h; exact hx i hi)

@[simp] private theorem edgeFoundation_edgeVelocityExtension {Y : Type*} [Fintype Y]
    {r : ℕ} (J : OrderedUniformHypergraph Y r) (e : J.Edge)
    (z : Fin r → Plane) :
    edgeFoundation J e (edgeVelocityExtension J e z) = z := by
  funext i
  exact edgeVelocityExtension_on_edge J e z i

private theorem edgeFoundation_extension_zero_of_disjoint {Y : Type*} [Fintype Y]
    {r : ℕ} (J : OrderedUniformHypergraph Y r) (e f : J.Edge)
    (z : Fin r → Plane)
    (hdisjoint : ∀ i j, J.vertex e i ≠ J.vertex f j) :
    edgeFoundation J f (edgeVelocityExtension J e z) = 0 := by
  funext j
  exact edgeVelocityExtension_off_edge J e z (J.vertex f j)
    (fun i => hdisjoint i j)

private theorem edgeFoundation_extension_zero_of_single_intersection
    {Y : Type*} [Fintype Y] {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (hberge : J.BergeGirthAtLeast 3)
    (e f : J.Edge) (hef : e ≠ f) (q s : Fin r)
    (hqs : J.vertex e q = J.vertex f s) (z : Fin r → Plane) (hzq : z q = 0) :
    edgeFoundation J f (edgeVelocityExtension J e z) = 0 := by
  funext j
  by_cases hjs : j = s
  · subst j
    change edgeVelocityExtension J e z (J.vertex f s) = 0
    rw [← hqs, edgeVelocityExtension_on_edge, hzq]
  · apply edgeVelocityExtension_off_edge J e z (J.vertex f j)
    intro k hkj
    have hindices := J.edge_intersection_indices hberge hef hqs hkj
    exact hjs hindices.2.symm

private theorem continuous_edgeFoundation {Y : Type*} [Fintype Y] {r : ℕ}
    (J : OrderedUniformHypergraph Y r) (e : J.Edge) :
    Continuous (edgeFoundation J e) := by
  apply continuous_pi
  intro i
  exact continuous_apply (J.vertex e i)

private noncomputable def pairEdgeInverse {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    (attachmentCycleDerivative
      (pairEdgeRegularAttachment m J cluster hpattern e).foundation
      (pairEdgeRegularAttachment m J cluster hpattern e).cycle).IsInvertible := by
  exact attachmentCycleDerivative_isInvertible_of_injective _
    (pairEdgeRegularAttachment m J cluster hpattern e).derivativeInjective

private noncomputable def pairEdgeLocalCycle {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge)
    (u : Y → Plane) : Fin (oddAttachmentSize m) → Plane :=
  let A := pairEdgeRegularAttachment m J cluster hpattern e
  regularLocalAttachedCycle A.foundation A.cycle
    (pairEdgeInverse m J cluster hpattern e) (edgeFoundation J e u)

private theorem edgeFoundation_pairBase {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    edgeFoundation J e (pairBaseFoundation cluster) =
      (pairEdgeRegularAttachment m J cluster hpattern e).foundation := by
  funext i
  exact (pairEdgeRegularAttachment_foundation m J cluster hpattern e i).symm

private theorem pairEdgeLocalCycle_apply_base {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (e : J.Edge) :
    pairEdgeLocalCycle m J cluster hpattern e (pairBaseFoundation cluster) =
      (pairEdgeRegularAttachment m J cluster hpattern e).cycle := by
  rw [pairEdgeLocalCycle, edgeFoundation_pairBase]
  unfold regularLocalAttachedCycle
  exact localAttachedCycle_apply_base _ _ _

private def pairFoundationValid {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (u : Y → Plane) : Prop :=
  ∀ e : J.Edge,
    ((∀ i, Dist.dist (u (J.vertex e i))
        (pairEdgeLocalCycle m J cluster hpattern e u i) = 1) ∧
      ∀ i, Dist.dist (pairEdgeLocalCycle m J cluster hpattern e u i)
        (pairEdgeLocalCycle m J cluster hpattern e u (i + 1)) = 1) ∧
    ContDiffAt ℝ 1
      (regularLocalAttachedCycle
        (pairEdgeRegularAttachment m J cluster hpattern e).foundation
        (pairEdgeRegularAttachment m J cluster hpattern e).cycle
        (pairEdgeInverse m J cluster hpattern e))
      (edgeFoundation J e u) ∧
    (attachmentCycleDerivative
      (edgeFoundation J e u)
      (pairEdgeLocalCycle m J cluster hpattern e u)).IsInvertible ∧
    ∀ᶠ v in nhds (edgeFoundation J e u),
      attachmentConstraints (oddAttachmentSize m)
        (v, regularLocalAttachedCycle
          (pairEdgeRegularAttachment m J cluster hpattern e).foundation
          (pairEdgeRegularAttachment m J cluster hpattern e).cycle
          (pairEdgeInverse m J cluster hpattern e) v) = 1

private theorem eventually_pairFoundationValid {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) :
    ∀ᶠ u in nhds (pairBaseFoundation cluster),
      pairFoundationValid m J cluster hpattern u := by
  letI : Fintype J.Edge := Fintype.ofFinite J.Edge
  change ∀ᶠ u in nhds (pairBaseFoundation cluster), ∀ e : J.Edge,
    ((∀ i, Dist.dist (u (J.vertex e i))
        (pairEdgeLocalCycle m J cluster hpattern e u i) = 1) ∧
      ∀ i, Dist.dist (pairEdgeLocalCycle m J cluster hpattern e u i)
        (pairEdgeLocalCycle m J cluster hpattern e u (i + 1)) = 1) ∧
    ContDiffAt ℝ 1
      (regularLocalAttachedCycle
        (pairEdgeRegularAttachment m J cluster hpattern e).foundation
        (pairEdgeRegularAttachment m J cluster hpattern e).cycle
        (pairEdgeInverse m J cluster hpattern e))
      (edgeFoundation J e u) ∧
    (attachmentCycleDerivative
      (edgeFoundation J e u)
      (pairEdgeLocalCycle m J cluster hpattern e u)).IsInvertible ∧
    ∀ᶠ v in nhds (edgeFoundation J e u),
      attachmentConstraints (oddAttachmentSize m)
        (v, regularLocalAttachedCycle
          (pairEdgeRegularAttachment m J cluster hpattern e).foundation
          (pairEdgeRegularAttachment m J cluster hpattern e).cycle
          (pairEdgeInverse m J cluster hpattern e) v) = 1
  rw [Filter.eventually_all]
  intro e
  let A := pairEdgeRegularAttachment m J cluster hpattern e
  have hbase : edgeFoundation J e (pairBaseFoundation cluster) = A.foundation :=
    edgeFoundation_pairBase m J cluster hpattern e
  have htend : Filter.Tendsto (edgeFoundation J e)
      (nhds (pairBaseFoundation cluster)) (nhds A.foundation) := by
    rw [← hbase]
    exact (continuous_edgeFoundation J e).continuousAt
  have hatt : ∀ᶠ v in nhds A.foundation,
      ((∀ i, Dist.dist (v i)
          (regularLocalAttachedCycle A.foundation A.cycle
            (pairEdgeInverse m J cluster hpattern e) v i) = 1) ∧
        ∀ i, Dist.dist
          (regularLocalAttachedCycle A.foundation A.cycle
            (pairEdgeInverse m J cluster hpattern e) v i)
          (regularLocalAttachedCycle A.foundation A.cycle
            (pairEdgeInverse m J cluster hpattern e) v (i + 1)) = 1) :=
    eventually_regularLocalAttachedCycle_is_attachment A.foundation A.cycle A.isAttachment
      (pairEdgeInverse m J cluster hpattern e)
  have hcont : ∀ᶠ v in nhds A.foundation,
      ContDiffAt ℝ 1
        (regularLocalAttachedCycle A.foundation A.cycle
          (pairEdgeInverse m J cluster hpattern e)) v :=
    eventually_regularLocalAttachedCycle_contDiffAt A.foundation A.cycle
      (pairEdgeInverse m J cluster hpattern e)
  have hinv : ∀ᶠ v in nhds A.foundation,
      (attachmentCycleDerivativeProd
        (v, regularLocalAttachedCycle A.foundation A.cycle
          (pairEdgeInverse m J cluster hpattern e) v)).IsInvertible :=
    eventually_regularLocalAttachedCycle_derivativeIsInvertible A.foundation A.cycle
      (pairEdgeInverse m J cluster hpattern e)
  have heq : ∀ᶠ v in nhds A.foundation,
      attachmentConstraints (oddAttachmentSize m)
        (v, regularLocalAttachedCycle A.foundation A.cycle
          (pairEdgeInverse m J cluster hpattern e) v) = 1 := by
    filter_upwards [hatt] with v hv
    exact attachmentConstraints_eq_one hv.1 hv.2
  have heqLocal : ∀ᶠ v in nhds A.foundation,
      ∀ᶠ w in nhds v,
        attachmentConstraints (oddAttachmentSize m)
          (w, regularLocalAttachedCycle A.foundation A.cycle
            (pairEdgeInverse m J cluster hpattern e) w) = 1 :=
    eventually_locally_of_eventually heq
  filter_upwards [htend.eventually hatt, htend.eventually hcont,
      htend.eventually hinv, htend.eventually heqLocal] with u hu hc hi he
  refine ⟨by simpa [pairEdgeLocalCycle, edgeFoundation, A] using hu,
    by simpa [A] using hc, ?_, by simpa [A] using he⟩
  simpa only [pairEdgeLocalCycle, attachmentCycleDerivativeProd, A] using hi

private def pairFoundationNeighborhood {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) : Set (Y → Plane) :=
  interior {u | pairFoundationValid m J cluster hpattern u}

private theorem pairBase_mem_pairFoundationNeighborhood {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) :
    pairBaseFoundation cluster ∈ pairFoundationNeighborhood m J cluster hpattern := by
  apply mem_interior_iff_mem_nhds.mpr
  exact eventually_pairFoundationValid m J cluster hpattern

private noncomputable def pairRealization {Y : Type*} (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) (u : Y → Plane) :
    J.AttachedVertex → Plane
  | .inl x => u x
  | .inr (e, i) => pairEdgeLocalCycle m J cluster hpattern e u i

private theorem pairFoundationNeighborhood_isOpen {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) :
    IsOpen (pairFoundationNeighborhood m J cluster hpattern) := isOpen_interior

private theorem pairFoundationNeighborhood_nonempty {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster) :
    (pairFoundationNeighborhood m J cluster hpattern).Nonempty :=
  ⟨pairBaseFoundation cluster,
    pairBase_mem_pairFoundationNeighborhood m J cluster hpattern⟩

private noncomputable def pairEdgeDerivative {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : Y → Plane) (e : J.Edge) :
    (Y → Plane) →L[ℝ] (Fin (oddAttachmentSize m) → Plane) :=
  (-(attachmentCycleDerivative
      (edgeFoundation J e u)
      (pairEdgeLocalCycle m J cluster hpattern e u)).inverse ∘L
    attachmentFoundationDerivative
      (edgeFoundation J e u)
      (pairEdgeLocalCycle m J cluster hpattern e u)) ∘L
    edgeFoundationCLM J e

private theorem pairEdgeLocalCycle_local_hasFDerivAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern) (e : J.Edge) :
    HasFDerivAt
      (regularLocalAttachedCycle
        (pairEdgeRegularAttachment m J cluster hpattern e).foundation
        (pairEdgeRegularAttachment m J cluster hpattern e).cycle
        (pairEdgeInverse m J cluster hpattern e))
      (-(attachmentCycleDerivative
          (edgeFoundation J e u.1)
          (pairEdgeLocalCycle m J cluster hpattern e u.1)).inverse ∘L
        attachmentFoundationDerivative
          (edgeFoundation J e u.1)
          (pairEdgeLocalCycle m J cluster hpattern e u.1))
      (edgeFoundation J e u.1) := by
  have hv := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  exact hasFDerivAt_of_attachment_solution _ _ hv.2.1 hv.2.2.2 hv.2.2.1

private theorem pairEdgeLocalCycle_hasFDerivAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern) (e : J.Edge) :
    HasFDerivAt
      (pairEdgeLocalCycle m J cluster hpattern e)
      (pairEdgeDerivative m J cluster hpattern u.1 e) u.1 := by
  exact (pairEdgeLocalCycle_local_hasFDerivAt m J cluster hpattern u e).comp u.1
    (edgeFoundationCLM J e).hasFDerivAt

private theorem pairEdgeDerivative_apply_of_flex {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern) (e : J.Edge)
    (w : Y → Plane) (z : Fin (oddAttachmentSize m) → Plane)
    (hw : edgeFoundation J e w = z)
    (hz : ∀ i, edgeFlexFunctional
      (pairEdgeLocalCycle m J cluster hpattern e u.1) i z = 0) :
    pairEdgeDerivative m J cluster hpattern u.1 e w = z := by
  have hinv := ((interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e).2.2.1
  simp only [pairEdgeDerivative, ContinuousLinearMap.comp_apply,
    edgeFoundationCLM_apply, hw]
  exact attachment_response_eq_cycleFlex _ _ _ hinv hz

private theorem pairEdgeDerivative_apply_of_linearization {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern) (e : J.Edge)
    (w : Y → Plane) (z : Fin (oddAttachmentSize m) → Plane)
    (hlin : attachmentFoundationDerivative
        (edgeFoundation J e u.1)
        (pairEdgeLocalCycle m J cluster hpattern e u.1)
        (edgeFoundation J e w) +
      attachmentCycleDerivative
        (edgeFoundation J e u.1)
        (pairEdgeLocalCycle m J cluster hpattern e u.1) z = 0) :
    pairEdgeDerivative m J cluster hpattern u.1 e w = z := by
  have hinv := ((interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e).2.2.1
  simp only [pairEdgeDerivative, ContinuousLinearMap.comp_apply,
    edgeFoundationCLM_apply]
  exact attachment_response_eq_of_linearization _ _ _ _ hinv hlin

private noncomputable def pairVertexDerivative {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : Y → Plane) : J.AttachedVertex → ((Y → Plane) →L[ℝ] Plane)
  | .inl x => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane) x
  | .inr (e, i) =>
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (oddAttachmentSize m) => Plane) i).comp
        (pairEdgeDerivative m J cluster hpattern u e)

private theorem pairRealization_hasFDerivAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern) (z : J.AttachedVertex) :
    HasFDerivAt (fun w => pairRealization m J cluster hpattern w z)
      (pairVertexDerivative m J cluster hpattern u.1 z) u.1 := by
  cases z with
  | inl x =>
      exact (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Y => Plane) x).hasFDerivAt
  | inr z =>
      rcases z with ⟨e, i⟩
      exact (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (oddAttachmentSize m) => Plane) i).hasFDerivAt.comp u.1
          (pairEdgeLocalCycle_hasFDerivAt m J cluster hpattern u e)

private noncomputable def pairCrossArea {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (c : Y) (e f : J.Edge) (i j : Fin (oddAttachmentSize m))
    (u : Y → Plane) : ℝ :=
  inner ℝ
    (pairRealization m J cluster hpattern u (.inr (e, i)) - u c)
    (quarterTurn
      (pairRealization m J cluster hpattern u (.inr (f, j)) - u c))

private theorem pairCrossArea_hasFDerivAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (c : Y) (e f : J.Edge) (i j : Fin (oddAttachmentSize m)) :
    HasFDerivAt (pairCrossArea m J cluster hpattern c e f i j)
      ((fderivInnerCLM ℝ
          (pairRealization m J cluster hpattern u.1 (.inr (e, i)) - u.1 c,
            quarterTurn
              (pairRealization m J cluster hpattern u.1 (.inr (f, j)) - u.1 c))).comp
        ((pairVertexDerivative m J cluster hpattern u.1 (.inr (e, i)) -
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane) c).prod
          (quarterTurnCLM.comp
            (pairVertexDerivative m J cluster hpattern u.1 (.inr (f, j)) -
              ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane) c)))) u.1 := by
  have hC : HasFDerivAt (fun w : Y → Plane => w c)
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Y => Plane) c) u.1 :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Y => Plane) c).hasFDerivAt
  have hE := pairRealization_hasFDerivAt m J cluster hpattern u (.inr (e, i))
  have hF := pairRealization_hasFDerivAt m J cluster hpattern u (.inr (f, j))
  have hX := hE.sub hC
  have hY := hF.sub hC
  have hQY := quarterTurnCLM.hasFDerivAt.comp u.1 hY
  change HasFDerivAt
    (fun w : Y → Plane => inner ℝ
      (pairRealization m J cluster hpattern w (.inr (e, i)) - w c)
      (quarterTurn
        (pairRealization m J cluster hpattern w (.inr (f, j)) - w c))) _ u.1
  simpa only [quarterTurnCLM_apply, Function.comp_apply,
    Pi.sub_apply] using hX.inner ℝ hQY

private theorem pairCrossArea_regular_at_injective_zero {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (hinj : Function.Injective (pairRealization m J cluster hpattern u.1))
    (e f : J.Edge) (hef : e ≠ f) (q s : Fin (oddAttachmentSize m))
    (hqs : J.vertex e q = J.vertex f s)
    (i j : Fin (oddAttachmentSize m))
    (hzero : pairCrossArea m J cluster hpattern (J.vertex e q) e f i j u.1 = 0) :
    ∃ A' : (Y → Plane) →L[ℝ] ℝ,
      HasFDerivAt
        (pairCrossArea m J cluster hpattern (J.vertex e q) e f i j) A' u.1 ∧
        A' ≠ 0 := by
  let c : Plane := u.1 (J.vertex e q)
  let uE := edgeFoundation J e u.1
  let vE := pairEdgeLocalCycle m J cluster hpattern e u.1
  let vF := pairEdgeLocalCycle m J cluster hpattern f u.1
  let wE : Fin (oddAttachmentSize m) → Plane := fun k => quarterTurn (uE k - c)
  let zE : Fin (oddAttachmentSize m) → Plane := fun k => quarterTurn (vE k - c)
  let w : Y → Plane := edgeVelocityExtension J e wE
  have hwEq : edgeFoundation J e w = wE := edgeFoundation_edgeVelocityExtension J e wE
  have hwEq0 : wE q = 0 := by simp [wE, uE, c, edgeFoundation, quarterTurn]
  have hwF : edgeFoundation J f w = 0 :=
    edgeFoundation_extension_zero_of_single_intersection J hberge e f hef q s hqs wE hwEq0
  have hwc : w (J.vertex e q) = 0 := by
    change edgeVelocityExtension J e wE (J.vertex e q) = 0
    rw [edgeVelocityExtension_on_edge, hwEq0]
  have hlin : attachmentFoundationDerivative uE vE wE +
      attachmentCycleDerivative uE vE zE = 0 :=
    attachment_rigid_rotation_linearization uE vE c
  have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = zE := by
    apply pairEdgeDerivative_apply_of_linearization m J cluster hpattern u e w zE
    simpa [uE, vE, hwEq] using hlin
  have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
    by simp [pairEdgeDerivative, hwF]
  let X : Plane := vE i - c
  let Yv : Plane := vF j - c
  have hXne : X ≠ 0 := by
    intro hX
    have heq : vE i = c := sub_eq_zero.mp hX
    have hv := hinj (show pairRealization m J cluster hpattern u.1 (.inr (e, i)) =
      pairRealization m J cluster hpattern u.1 (.inl (J.vertex e q)) from heq)
    simp at hv
  have hYne : Yv ≠ 0 := by
    intro hY
    have heq : vF j = c := sub_eq_zero.mp hY
    have hc : c = u.1 (J.vertex f s) := by
      dsimp only [c]
      rw [hqs]
    have hv := hinj (show pairRealization m J cluster hpattern u.1 (.inr (f, j)) =
      pairRealization m J cluster hpattern u.1 (.inl (J.vertex f s)) from heq.trans hc)
    simp at hv
  have harea0 : inner ℝ X (quarterTurn Yv) = 0 := by
    simpa [pairCrossArea, pairRealization, X, Yv, vE, vF, c] using hzero
  have hXY : inner ℝ X Yv ≠ 0 :=
    inner_ne_zero_of_inner_quarterTurn_eq_zero hXne hYne harea0
  let A' :=
    (fderivInnerCLM ℝ
      (pairRealization m J cluster hpattern u.1 (.inr (e, i)) - u.1 (J.vertex e q),
        quarterTurn
          (pairRealization m J cluster hpattern u.1 (.inr (f, j)) -
            u.1 (J.vertex e q)))).comp
      ((pairVertexDerivative m J cluster hpattern u.1 (.inr (e, i)) -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane)
            (J.vertex e q)).prod
        (quarterTurnCLM.comp
          (pairVertexDerivative m J cluster hpattern u.1 (.inr (f, j)) -
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Y => Plane)
              (J.vertex e q))))
  refine ⟨A', pairCrossArea_hasFDerivAt m J cluster hpattern u
    (J.vertex e q) e f i j, ?_⟩
  intro hA
  have happ := congrArg (fun L : (Y → Plane) →L[ℝ] ℝ => L w) hA
  simp only [A', ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.zero_apply] at happ
  change inner ℝ (vE i - c) (quarterTurn
      (pairEdgeDerivative m J cluster hpattern u.1 f w j - w (J.vertex e q))) +
    inner ℝ (pairEdgeDerivative m J cluster hpattern u.1 e w i - w (J.vertex e q))
      (quarterTurn (vF j - c)) = 0 at happ
  rw [hrespE, hrespF, hwc] at happ
  simp only [Pi.zero_apply, zero_sub, sub_zero, quarterTurn_zero,
    inner_zero_right, zero_add] at happ
  have hzEi : zE i = quarterTurn X := by rfl
  have hYv : vF j - c = Yv := by rfl
  rw [hzEi, hYv, inner_quarterTurn_quarterTurn] at happ
  exact hXY happ

private theorem pair_foundation_cycle_derivative_ne {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (x : Y) (e : J.Edge) (i : Fin (oddAttachmentSize m))
    (hcollision : u.1 x = pairEdgeLocalCycle m J cluster hpattern e u.1 i) :
    pairVertexDerivative m J cluster hpattern u.1 (.inl x) ≠
      pairVertexDerivative m J cluster hpattern u.1 (.inr (e, i)) := by
  have hr : 3 ≤ oddAttachmentSize m := by
    rw [oddAttachmentSize_eq]
    omega
  have hodd : Odd (oddAttachmentSize m) := by
    rw [oddAttachmentSize_eq]
    exact ⟨m + 1, by omega⟩
  have hvalid := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  let v := pairEdgeLocalCycle m J cluster hpattern e u.1
  by_cases hxinc : ∃ q, J.vertex e q = x
  · obtain ⟨q, hqx⟩ := hxinc
    have hiq : i ≠ q := by
      intro hiq
      subst i
      have hs := hvalid.1.1 q
      rw [hqx, ← hcollision] at hs
      simpa using hs
    obtain ⟨z, hzflex, hziq⟩ :=
      odd_cycle_indices_have_separating_flex hr hodd v hvalid.1.2 i q hiq
    let w : Y → Plane := edgeVelocityExtension J e z
    have hw : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hw hzflex
    have hwx : w x = z q := by
      rw [← hqx]
      exact edgeVelocityExtension_on_edge J e z q
    intro hder
    have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
    change w x = pairEdgeDerivative m J cluster hpattern u.1 e w i at happ
    rw [hwx, hresp] at happ
    exact hziq happ.symm
  · let z : Fin (oddAttachmentSize m) → Plane := fun _ => planeAxisX
    let w : Y → Plane := edgeVelocityExtension J e z
    have hzflex : ∀ k, edgeFlexFunctional v k z = 0 := by
      intro k
      simp [edgeFlexFunctional_apply, z]
    have hw : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hw hzflex
    have hwx : w x = 0 := by
      apply edgeVelocityExtension_off_edge J e z x
      intro q hq
      exact hxinc ⟨q, hq⟩
    intro hder
    have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
    change w x = pairEdgeDerivative m J cluster hpattern u.1 e w i at happ
    rw [hwx, hresp] at happ
    exact planeAxisX_ne_zero happ.symm

private theorem pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
    {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : Y → Plane) (e : J.Edge) (w : Y → Plane)
    (hw : edgeFoundation J e w = 0) :
    pairEdgeDerivative m J cluster hpattern u e w = 0 := by
  simp [pairEdgeDerivative, hw]

private theorem pair_same_cycle_derivative_ne {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (e : J.Edge) (i j : Fin (oddAttachmentSize m)) (hij : i ≠ j) :
    pairVertexDerivative m J cluster hpattern u.1 (.inr (e, i)) ≠
      pairVertexDerivative m J cluster hpattern u.1 (.inr (e, j)) := by
  have hr : 3 ≤ oddAttachmentSize m := by
    rw [oddAttachmentSize_eq]
    omega
  have hodd : Odd (oddAttachmentSize m) := by
    rw [oddAttachmentSize_eq]
    exact ⟨m + 1, by omega⟩
  have hvalid := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  let v := pairEdgeLocalCycle m J cluster hpattern e u.1
  obtain ⟨z, hzflex, hzij⟩ :=
    odd_cycle_indices_have_separating_flex hr hodd v hvalid.1.2 i j hij
  let w : Y → Plane := edgeVelocityExtension J e z
  have hw : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
  have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
    pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hw hzflex
  intro hder
  have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
  change pairEdgeDerivative m J cluster hpattern u.1 e w i =
    pairEdgeDerivative m J cluster hpattern u.1 e w j at happ
  rw [hresp] at happ
  exact hzij happ

private theorem pair_foundation_cycle_unit_variation {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (hinj : Function.Injective (pairRealization m J cluster hpattern u.1))
    (x : Y) (e : J.Edge) (i : Fin (oddAttachmentSize m))
    (hnadj : ¬J.attachedGraph.Adj (.inl x) (.inr (e, i)))
    (hunit : Dist.dist (u.1 x)
      (pairEdgeLocalCycle m J cluster hpattern e u.1 i) = 1) :
    ∃ w : Y → Plane,
      inner ℝ
        (u.1 x - pairEdgeLocalCycle m J cluster hpattern e u.1 i)
        (w x - pairEdgeDerivative m J cluster hpattern u.1 e w i) ≠ 0 := by
  have hr : 3 ≤ oddAttachmentSize m := by
    rw [oddAttachmentSize_eq]
    omega
  have hvalid := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  let v := pairEdgeLocalCycle m J cluster hpattern e u.1
  have hvInj : Function.Injective v := by
    intro k l hkl
    have h := hinj (show pairRealization m J cluster hpattern u.1 (.inr (e, k)) =
      pairRealization m J cluster hpattern u.1 (.inr (e, l)) from hkl)
    simpa using h
  by_cases hxinc : ∃ q, J.vertex e q = x
  · obtain ⟨q, hqx⟩ := hxinc
    have hiq : i ≠ q := by
      intro hiq
      subst i
      apply hnadj
      change J.vertex e q = x
      exact hqx
    have haoff : ∀ k, u.1 x ≠ v k := by
      intro k hxk
      have h := hinj (show pairRealization m J cluster hpattern u.1 (.inl x) =
        pairRealization m J cluster hpattern u.1 (.inr (e, k)) from hxk)
      simp at h
    have haq : Dist.dist (u.1 x) (v q) = 1 := by
      simpa [v, hqx] using hvalid.1.1 q
    obtain ⟨z, hzflex, hzchange⟩ :=
      cycle_external_unit_pair_has_flex hr v hvalid.1.2 hvInj (u.1 x) haoff
        i q hiq hunit haq
    let w : Y → Plane := edgeVelocityExtension J e z
    have hwx : w x = z q := by
      rw [← hqx]
      exact edgeVelocityExtension_on_edge J e z q
    have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
    refine ⟨w, ?_⟩
    simpa [v, hwx, hresp] using hzchange
  · let d : Plane := u.1 x - v i
    have hdne : d ≠ 0 := by
      intro hd
      have hxi : u.1 x = v i := sub_eq_zero.mp hd
      rw [hxi] at hunit
      simpa [v] using hunit
    let z : Fin (oddAttachmentSize m) → Plane := fun _ => d
    let w : Y → Plane := edgeVelocityExtension J e z
    have hzflex : ∀ k, edgeFlexFunctional v k z = 0 := by
      intro k
      simp [edgeFlexFunctional_apply, z]
    have hwx : w x = 0 := by
      apply edgeVelocityExtension_off_edge J e z x
      intro q hq
      exact hxinc ⟨q, hq⟩
    have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
    refine ⟨w, ?_⟩
    have hself : inner ℝ d d ≠ 0 := inner_self_ne_zero.mpr hdne
    have hnegself : inner ℝ d (-d) ≠ 0 := by
      rw [inner_neg_right]
      exact neg_ne_zero.mpr hself
    simpa [v, d, z, hwx, hresp] using hnegself

private theorem pair_same_cycle_unit_variation {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (hinj : Function.Injective (pairRealization m J cluster hpattern u.1))
    (e : J.Edge) (i j : Fin (oddAttachmentSize m))
    (hnadj : ¬J.attachedGraph.Adj (.inr (e, i)) (.inr (e, j)))
    (hunit : Dist.dist (pairEdgeLocalCycle m J cluster hpattern e u.1 i)
      (pairEdgeLocalCycle m J cluster hpattern e u.1 j) = 1) :
    ∃ w : Y → Plane,
      inner ℝ
        (pairEdgeLocalCycle m J cluster hpattern e u.1 i -
          pairEdgeLocalCycle m J cluster hpattern e u.1 j)
        (pairEdgeDerivative m J cluster hpattern u.1 e w i -
          pairEdgeDerivative m J cluster hpattern u.1 e w j) ≠ 0 := by
  have hr : 3 ≤ oddAttachmentSize m := by
    rw [oddAttachmentSize_eq]
    omega
  let v := pairEdgeLocalCycle m J cluster hpattern e u.1
  have hvalid := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  have hvInj : Function.Injective v := by
    intro k l hkl
    have h := hinj (show pairRealization m J cluster hpattern u.1 (.inr (e, k)) =
      pairRealization m J cluster hpattern u.1 (.inr (e, l)) from hkl)
    simpa using h
  have hcycleNadj : ¬(cycleGraph (oddAttachmentSize m)).Adj i j := by
    intro hij
    apply hnadj
    exact ⟨rfl, hij⟩
  obtain ⟨z, hzflex, hzchange⟩ :=
    cycle_unit_chord_has_flex hr v hvalid.1.2 hvInj i j hcycleNadj hunit
  let w : Y → Plane := edgeVelocityExtension J e z
  have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
  have hresp : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
    pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
  refine ⟨w, ?_⟩
  intro hzero
  apply hzchange
  rw [chordFlexFunctional_apply]
  rw [show v j - v i = -(v i - v j) by abel,
    show z j - z i = -(z i - z j) by abel,
    inner_neg_left, inner_neg_right]
  simpa [v, hresp] using hzero

private theorem pair_distinct_cycle_unit_variation {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (e f : J.Edge) (hef : e ≠ f)
    (i j : Fin (oddAttachmentSize m))
    (hgeneral : ∀ q s, J.vertex e q = J.vertex f s →
      pairCrossArea m J cluster hpattern (J.vertex e q) e f i j u.1 ≠ 0)
    (hunit : Dist.dist
      (pairEdgeLocalCycle m J cluster hpattern e u.1 i)
      (pairEdgeLocalCycle m J cluster hpattern f u.1 j) = 1) :
    ∃ w : Y → Plane,
      inner ℝ
        (pairEdgeLocalCycle m J cluster hpattern e u.1 i -
          pairEdgeLocalCycle m J cluster hpattern f u.1 j)
        (pairEdgeDerivative m J cluster hpattern u.1 e w i -
          pairEdgeDerivative m J cluster hpattern u.1 f w j) ≠ 0 := by
  let vE := pairEdgeLocalCycle m J cluster hpattern e u.1
  let vF := pairEdgeLocalCycle m J cluster hpattern f u.1
  by_cases hinter : ∃ q s, J.vertex e q = J.vertex f s
  · obtain ⟨q, s, hqs⟩ := hinter
    let c : Plane := u.1 (J.vertex e q)
    let uE := edgeFoundation J e u.1
    let wE : Fin (oddAttachmentSize m) → Plane := fun k => quarterTurn (uE k - c)
    let zE : Fin (oddAttachmentSize m) → Plane := fun k => quarterTurn (vE k - c)
    let w : Y → Plane := edgeVelocityExtension J e wE
    have hwEq : edgeFoundation J e w = wE :=
      edgeFoundation_edgeVelocityExtension J e wE
    have hwEq0 : wE q = 0 := by
      simp [wE, uE, c, edgeFoundation, quarterTurn]
    have hwF : edgeFoundation J f w = 0 :=
      edgeFoundation_extension_zero_of_single_intersection
        J hberge e f hef q s hqs wE hwEq0
    have hlin : attachmentFoundationDerivative uE vE wE +
        attachmentCycleDerivative uE vE zE = 0 :=
      attachment_rigid_rotation_linearization uE vE c
    have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = zE := by
      apply pairEdgeDerivative_apply_of_linearization m J cluster hpattern u e w zE
      simpa [uE, vE, hwEq] using hlin
    have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
      pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
        m J cluster hpattern u.1 f w hwF
    have harea : inner ℝ (vE i - c) (quarterTurn (vF j - c)) ≠ 0 := by
      simpa [pairCrossArea, pairRealization, vE, vF, c] using hgeneral q s hqs
    refine ⟨w, ?_⟩
    rw [hrespE, hrespF]
    simp only [Pi.zero_apply, sub_zero]
    have hdiff : vE i - vF j = (vE i - c) - (vF j - c) := by abel
    rw [hdiff]
    dsimp only [zE]
    rw [inner_sub_left, inner_quarterTurn_self, zero_sub,
      inner_quarterTurn_skew, neg_neg]
    exact harea
  · have hdisjoint : ∀ q s, J.vertex e q ≠ J.vertex f s := by
      intro q s hqs
      exact hinter ⟨q, s, hqs⟩
    let d : Plane := vE i - vF j
    have hdne : d ≠ 0 := by
      intro hd
      have heq : vE i = vF j := sub_eq_zero.mp hd
      change Dist.dist (vE i) (vF j) = 1 at hunit
      rw [heq] at hunit
      simpa using hunit
    let z : Fin (oddAttachmentSize m) → Plane := fun _ => d
    let w : Y → Plane := edgeVelocityExtension J e z
    have hzflex : ∀ k, edgeFlexFunctional vE k z = 0 := by
      intro k
      simp [edgeFlexFunctional_apply, z]
    have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hwF : edgeFoundation J f w = 0 :=
      edgeFoundation_extension_zero_of_disjoint J e f z hdisjoint
    have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
    have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
      pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
        m J cluster hpattern u.1 f w hwF
    refine ⟨w, ?_⟩
    have hself : inner ℝ d d ≠ 0 := inner_self_ne_zero.mpr hdne
    simpa [vE, vF, d, z, hrespE, hrespF] using hself

private theorem pair_distinct_cycle_derivative_ne {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (e f : J.Edge) (hef : e ≠ f)
    (i j : Fin (oddAttachmentSize m)) :
    pairVertexDerivative m J cluster hpattern u.1 (.inr (e, i)) ≠
      pairVertexDerivative m J cluster hpattern u.1 (.inr (f, j)) := by
  have hr : 3 ≤ oddAttachmentSize m := by
    rw [oddAttachmentSize_eq]
    omega
  have hodd : Odd (oddAttachmentSize m) := by
    rw [oddAttachmentSize_eq]
    exact ⟨m + 1, by omega⟩
  let uE := edgeFoundation J e u.1
  let vE := pairEdgeLocalCycle m J cluster hpattern e u.1
  have hvalidE := (interior_subset u.2 :
    pairFoundationValid m J cluster hpattern u.1) e
  by_cases hinter : ∃ q s, J.vertex e q = J.vertex f s
  · obtain ⟨q, s, hqs⟩ := hinter
    let c : Plane := uE q
    by_cases hic : vE i = c
    · have hiq : i ≠ q := by
        intro hiq
        subst i
        have hs := hvalidE.1.1 q
        change Dist.dist (uE q) (vE q) = 1 at hs
        rw [hic] at hs
        simp [c] at hs
      obtain ⟨z₀, hz₀flex, hz₀iq⟩ :=
        odd_cycle_indices_have_separating_flex hr hodd vE hvalidE.1.2 i q hiq
      let z : Fin (oddAttachmentSize m) → Plane := fun k => z₀ k - z₀ q
      have hzflex : ∀ k, edgeFlexFunctional vE k z = 0 := by
        intro k
        rw [edgeFlexFunctional_apply]
        have hk := hz₀flex k
        rw [edgeFlexFunctional_apply] at hk
        convert hk using 1
        congr 1
        dsimp only [z]
        abel
      have hzq : z q = 0 := by simp [z]
      have hzi : z i ≠ 0 := by
        simpa [z, sub_ne_zero] using hz₀iq
      let w : Y → Plane := edgeVelocityExtension J e z
      have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
      have hwF : edgeFoundation J f w = 0 :=
        edgeFoundation_extension_zero_of_single_intersection J hberge e f hef q s hqs z hzq
      have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
        pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
      have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
        pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
          m J cluster hpattern u.1 f w hwF
      intro hder
      have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
      change pairEdgeDerivative m J cluster hpattern u.1 e w i =
        pairEdgeDerivative m J cluster hpattern u.1 f w j at happ
      rw [hrespE, hrespF] at happ
      exact hzi (by simpa using happ)
    · let wE : Fin (oddAttachmentSize m) → Plane :=
        fun k => quarterTurn (uE k - c)
      let z : Fin (oddAttachmentSize m) → Plane :=
        fun k => quarterTurn (vE k - c)
      let w : Y → Plane := edgeVelocityExtension J e wE
      have hwEq : edgeFoundation J e w = wE := edgeFoundation_edgeVelocityExtension J e wE
      have hwEq0 : wE q = 0 := by simp [wE, c, quarterTurn]
      have hwF : edgeFoundation J f w = 0 :=
        edgeFoundation_extension_zero_of_single_intersection J hberge e f hef q s hqs wE hwEq0
      have hlin : attachmentFoundationDerivative uE vE wE +
          attachmentCycleDerivative uE vE z = 0 :=
        attachment_rigid_rotation_linearization uE vE c
      have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = z := by
        apply pairEdgeDerivative_apply_of_linearization m J cluster hpattern u e w z
        simpa [uE, vE, hwEq] using hlin
      have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
        pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
          m J cluster hpattern u.1 f w hwF
      have hzi : z i ≠ 0 := by
        intro hzero
        have hturn : quarterTurn (vE i - c) = quarterTurn 0 := by
          simpa [z, quarterTurn] using hzero
        exact hic (sub_eq_zero.mp (quarterTurn_injective hturn))
      intro hder
      have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
      change pairEdgeDerivative m J cluster hpattern u.1 e w i =
        pairEdgeDerivative m J cluster hpattern u.1 f w j at happ
      rw [hrespE, hrespF] at happ
      exact hzi (by simpa using happ)
  · have hdisjoint : ∀ q s, J.vertex e q ≠ J.vertex f s := by
      intro q s hqs
      exact hinter ⟨q, s, hqs⟩
    let z : Fin (oddAttachmentSize m) → Plane := fun _ => planeAxisX
    let w : Y → Plane := edgeVelocityExtension J e z
    have hzflex : ∀ k, edgeFlexFunctional vE k z = 0 := by
      intro k
      simp [edgeFlexFunctional_apply, z]
    have hwE : edgeFoundation J e w = z := edgeFoundation_edgeVelocityExtension J e z
    have hwF : edgeFoundation J f w = 0 :=
      edgeFoundation_extension_zero_of_disjoint J e f z hdisjoint
    have hrespE : pairEdgeDerivative m J cluster hpattern u.1 e w = z :=
      pairEdgeDerivative_apply_of_flex m J cluster hpattern u e w z hwE hzflex
    have hrespF : pairEdgeDerivative m J cluster hpattern u.1 f w = 0 :=
      pairEdgeDerivative_eq_zero_of_edgeFoundation_eq_zero
        m J cluster hpattern u.1 f w hwF
    intro hder
    have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
    change pairEdgeDerivative m J cluster hpattern u.1 e w i =
      pairEdgeDerivative m J cluster hpattern u.1 f w j at happ
    rw [hrespE, hrespF] at happ
    exact planeAxisX_ne_zero (by simpa [z] using happ)

private theorem pair_collision_derivative_ne {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (x y : J.AttachedVertex) (hxy : x ≠ y)
    (_hcollision : pairRealization m J cluster hpattern u.1 x =
      pairRealization m J cluster hpattern u.1 y) :
    pairVertexDerivative m J cluster hpattern u.1 x ≠
      pairVertexDerivative m J cluster hpattern u.1 y := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hxy' : x ≠ y := by simpa using hxy
          classical
          let w : Y → Plane := fun z => if z = x then planeAxisX else 0
          intro hder
          have happ := congrArg (fun L : (Y → Plane) →L[ℝ] Plane => L w) hder
          change w x = w y at happ
          simp [w, hxy', hxy'.symm] at happ
          exact planeAxisX_ne_zero happ
      | inr z =>
          rcases z with ⟨e, i⟩
          exact pair_foundation_cycle_derivative_ne m J cluster hpattern u x e i
            _hcollision
  | inr z =>
      rcases z with ⟨e, i⟩
      cases y with
      | inl y =>
          exact (pair_foundation_cycle_derivative_ne m J cluster hpattern u y e i
            _hcollision.symm).symm
      | inr z' =>
          rcases z' with ⟨f, j⟩
          by_cases hef : e = f
          · subst f
            have hij : i ≠ j := by simpa using hxy
            exact pair_same_cycle_derivative_ne m J cluster hpattern u e i j hij
          · exact pair_distinct_cycle_derivative_ne m J cluster hpattern hberge u e f hef i j

private noncomputable def pairDifference {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (x y : J.AttachedVertex) (u : Y → Plane) : Plane :=
  pairRealization m J cluster hpattern u x -
    pairRealization m J cluster hpattern u y

private theorem pairDifference_hasFDerivAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (x y : J.AttachedVertex) :
    HasFDerivAt (pairDifference m J cluster hpattern x y)
      (pairVertexDerivative m J cluster hpattern u.1 x -
        pairVertexDerivative m J cluster hpattern u.1 y) u.1 := by
  exact (pairRealization_hasFDerivAt m J cluster hpattern u x).sub
    (pairRealization_hasFDerivAt m J cluster hpattern u y)

private def pairGeneralPositionAt {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (u : Y → Plane) : Prop :=
  ∀ (e f : J.Edge) (hef : e ≠ f)
    (q s : Fin (oddAttachmentSize m)) (hqs : J.vertex e q = J.vertex f s)
    (i j : Fin (oddAttachmentSize m)),
    pairCrossArea m J cluster hpattern (J.vertex e q) e f i j u ≠ 0

private structure PairCrossDatum (E : Type*) (r : ℕ) where
  e : E
  f : E
  q : Fin r
  s : Fin r
  i : Fin r
  j : Fin r
deriving Fintype

private theorem pair_unit_nonedge_variation {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (hinj : Function.Injective (pairRealization m J cluster hpattern u.1))
    (hgeneral : pairGeneralPositionAt m J cluster hpattern u.1)
    (x y : J.AttachedVertex) (hnadj : ¬J.attachedGraph.Adj x y)
    (hunit : Dist.dist (pairRealization m J cluster hpattern u.1 x)
      (pairRealization m J cluster hpattern u.1 y) = 1) :
    ∃ w : Y → Plane,
      inner ℝ
        (pairRealization m J cluster hpattern u.1 x -
          pairRealization m J cluster hpattern u.1 y)
        ((pairVertexDerivative m J cluster hpattern u.1 x) w -
          (pairVertexDerivative m J cluster hpattern u.1 y) w) ≠ 0 := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          classical
          have hpos : u.1 x ≠ u.1 y := by
            intro hxy
            change Dist.dist (u.1 x) (u.1 y) = 1 at hunit
            rw [hxy] at hunit
            simpa using hunit
          have hxy : x ≠ y := fun h => hpos (congrArg u.1 h)
          let d : Plane := u.1 x - u.1 y
          let w : Y → Plane := fun z => if z = x then d else 0
          refine ⟨w, ?_⟩
          change inner ℝ d (w x - w y) ≠ 0
          have hdne : d ≠ 0 := sub_ne_zero.mpr hpos
          have hself : inner ℝ d d ≠ 0 := inner_self_ne_zero.mpr hdne
          simpa [w, hxy, hxy.symm] using hself
      | inr z =>
          rcases z with ⟨e, i⟩
          exact pair_foundation_cycle_unit_variation m J cluster hpattern u hinj x e i
            hnadj hunit
  | inr z =>
      rcases z with ⟨e, i⟩
      cases y with
      | inl y =>
          obtain ⟨w, hw⟩ := pair_foundation_cycle_unit_variation
            m J cluster hpattern u hinj y e i
            (fun h => hnadj h.symm)
            (by simpa [pairRealization, PseudoMetricSpace.dist_comm] using hunit)
          refine ⟨w, ?_⟩
          have hp : pairEdgeLocalCycle m J cluster hpattern e u.1 i - u.1 y =
              -(u.1 y - pairEdgeLocalCycle m J cluster hpattern e u.1 i) := by abel
          have hv : pairEdgeDerivative m J cluster hpattern u.1 e w i - w y =
              -(w y - pairEdgeDerivative m J cluster hpattern u.1 e w i) := by abel
          change inner ℝ
            (pairEdgeLocalCycle m J cluster hpattern e u.1 i - u.1 y)
            (pairEdgeDerivative m J cluster hpattern u.1 e w i - w y) ≠ 0
          rw [hp, hv, inner_neg_left, inner_neg_right]
          simpa using hw
      | inr z' =>
          rcases z' with ⟨f, j⟩
          by_cases hef : e = f
          · subst f
            exact pair_same_cycle_unit_variation m J cluster hpattern u hinj e i j
              hnadj hunit
          · exact pair_distinct_cycle_unit_variation m J cluster hpattern hberge u
              e f hef i j (fun q s hqs => hgeneral e f hef q s hqs i j) hunit

private noncomputable def pairSquaredDistance {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (x y : J.AttachedVertex) (u : Y → Plane) : ℝ :=
  ‖pairDifference m J cluster hpattern x y u‖ ^ 2

private theorem pairSquaredDistance_regular_at_unit_nonedge
    {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (hinj : Function.Injective (pairRealization m J cluster hpattern u.1))
    (hgeneral : pairGeneralPositionAt m J cluster hpattern u.1)
    (x y : J.AttachedVertex) (hnadj : ¬J.attachedGraph.Adj x y)
    (hlevel : pairSquaredDistance m J cluster hpattern x y u.1 = 1) :
    ∃ L : (Y → Plane) →L[ℝ] ℝ,
      HasFDerivAt (pairSquaredDistance m J cluster hpattern x y) L u.1 ∧ L ≠ 0 := by
  let d := pairDifference m J cluster hpattern x y u.1
  have hsq : ‖d‖ ^ 2 = 1 := by simpa [pairSquaredDistance, d] using hlevel
  have hnorm : ‖d‖ = 1 := by nlinarith [norm_nonneg d]
  have hunit : Dist.dist (pairRealization m J cluster hpattern u.1 x)
      (pairRealization m J cluster hpattern u.1 y) = 1 := by
    simpa [d, pairDifference, dist_eq_norm] using hnorm
  obtain ⟨w, hw⟩ := pair_unit_nonedge_variation m J cluster hpattern hberge
    u hinj hgeneral x y hnadj hunit
  let D := pairVertexDerivative m J cluster hpattern u.1 x -
    pairVertexDerivative m J cluster hpattern u.1 y
  let L : (Y → Plane) →L[ℝ] ℝ := 2 • (innerSL ℝ d).comp D
  refine ⟨L, ?_, ?_⟩
  · change HasFDerivAt
      (fun z : Y → Plane => ‖pairDifference m J cluster hpattern x y z‖ ^ 2) L u.1
    simpa only [L, d, D] using
      (pairDifference_hasFDerivAt m J cluster hpattern u x y).norm_sq
  · intro hL
    have happ := congrArg (fun A : (Y → Plane) →L[ℝ] ℝ => A w) hL
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, ContinuousLinearMap.zero_apply] at happ
    have hinner : inner ℝ d (D w) = 0 := by
      rw [two_smul] at happ
      linarith
    apply hw
    simpa [d, D, pairDifference] using hinner

private theorem dense_pairRealization_ne {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3)
    (x y : J.AttachedVertex) (hxy : x ≠ y) :
    Dense {u : pairFoundationNeighborhood m J cluster hpattern |
      pairRealization m J cluster hpattern u.1 x ≠
        pairRealization m J cluster hpattern u.1 y} := by
  let N := pairFoundationNeighborhood m J cluster hpattern
  let f := pairDifference m J cluster hpattern x y
  have hd := dense_ne_level_on_open_of_fderiv_ne_zero N
    (pairFoundationNeighborhood_isOpen m J cluster hpattern) f 0
    (fun u hu hzero => by
      let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, hu⟩
      have hcollision : pairRealization m J cluster hpattern u x =
          pairRealization m J cluster hpattern u y := sub_eq_zero.mp hzero
      refine ⟨pairVertexDerivative m J cluster hpattern u x -
          pairVertexDerivative m J cluster hpattern u y,
        pairDifference_hasFDerivAt m J cluster hpattern us x y, ?_⟩
      exact sub_ne_zero.mpr
        (pair_collision_derivative_ne m J cluster hpattern hberge us x y hxy hcollision))
  simpa only [N, f, pairDifference, sub_ne_zero] using hd

private theorem continuous_pairRealization_onNeighborhood {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (z : J.AttachedVertex) :
    Continuous (fun u : pairFoundationNeighborhood m J cluster hpattern ↦
      pairRealization m J cluster hpattern u.1 z) := by
  cases z with
  | inl x =>
      exact (continuous_apply x).comp continuous_subtype_val
  | inr z =>
      rcases z with ⟨e, i⟩
      rw [continuous_iff_continuousAt]
      intro u
      have hvalid : pairFoundationValid m J cluster hpattern u.1 :=
        interior_subset u.2
      have hlocal := (hvalid e).2.1
      have hfull : ContinuousAt
          (fun v : Y → Plane ↦
            regularLocalAttachedCycle
              (pairEdgeRegularAttachment m J cluster hpattern e).foundation
              (pairEdgeRegularAttachment m J cluster hpattern e).cycle
              (pairEdgeInverse m J cluster hpattern e)
              (edgeFoundation J e v)) u.1 :=
        hlocal.continuousAt.comp (continuous_edgeFoundation J e).continuousAt
      have hcycleCont : ContinuousAt
          (fun v : pairFoundationNeighborhood m J cluster hpattern ↦
            regularLocalAttachedCycle
              (pairEdgeRegularAttachment m J cluster hpattern e).foundation
              (pairEdgeRegularAttachment m J cluster hpattern e).cycle
              (pairEdgeInverse m J cluster hpattern e)
              (edgeFoundation J e v.1)) u :=
        hfull.comp continuous_subtype_val.continuousAt
      exact (continuous_apply i).continuousAt.comp hcycleCont

private theorem cycleGraph_adj_add_one {r : ℕ} [NeZero r] (hr : 2 ≤ r) (i j : Fin r)
    (h : (cycleGraph r).Adj i j) : j = i + 1 ∨ i = j + 1 := by
  rw [cycleGraph_adj'] at h
  rcases h with h | h
  · right
    have hs : i - j = (1 : Fin r) := by
      apply Fin.ext
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < r)] using h
    rw [sub_eq_iff_eq_add'] at hs
    simpa [add_comm] using hs
  · left
    have hs : j - i = (1 : Fin r) := by
      apply Fin.ext
      simpa [Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 < r)] using h
    rw [sub_eq_iff_eq_add'] at hs
    simpa [add_comm] using hs

private theorem pairRealization_edges_unit {Y : Type*} [Fintype Y] (m : ℕ)
    (J : OrderedUniformHypergraph Y (oddAttachmentSize m)) (cluster : Y → Fin 4)
    (hpattern : J.HasPairClusterPattern cluster)
    (u : pairFoundationNeighborhood m J cluster hpattern)
    (x y : J.AttachedVertex) (hxy : J.attachedGraph.Adj x y) :
    Dist.dist (pairRealization m J cluster hpattern u.1 x)
      (pairRealization m J cluster hpattern u.1 y) = 1 := by
  have hvalid : pairFoundationValid m J cluster hpattern u.1 :=
    interior_subset u.2
  cases x with
  | inl x =>
      cases y with
      | inl y => simp [OrderedUniformHypergraph.attachedGraph,
          OrderedUniformHypergraph.attachedAdj] at hxy
      | inr z =>
          rcases z with ⟨e, i⟩
          change J.vertex e i = x at hxy
          subst x
          exact (hvalid e).1.1 i
  | inr z =>
      rcases z with ⟨e, i⟩
      cases y with
      | inl y =>
          change J.vertex e i = y at hxy
          subst y
          simpa [pairRealization, PseudoMetricSpace.dist_comm] using (hvalid e).1.1 i
      | inr z' =>
          rcases z' with ⟨f, j⟩
          change e = f ∧ (cycleGraph (oddAttachmentSize m)).Adj i j at hxy
          obtain ⟨rfl, hij⟩ := hxy
          rcases cycleGraph_adj_add_one (by cases m <;> simp [oddAttachmentSize]) i j hij with h | h
          · subst j
            simpa [pairRealization] using (hvalid e).1.2 i
          · subst i
            simpa [pairRealization, PseudoMetricSpace.dist_comm] using (hvalid e).1.2 j

/-- O'Donnell's simultaneous attachment family contains a faithful
realization.  The proof performs three finite regular-level avoidances:
collisions, collinear pairs in intersecting fibers, and unintended unit
distances. -/
private theorem faithful_pairRealization {Y : Type*} [Fintype Y]
    (m : ℕ) (J : OrderedUniformHypergraph Y (oddAttachmentSize m))
    (cluster : Y → Fin 4) (hpattern : J.HasPairClusterPattern cluster)
    (hberge : J.BergeGirthAtLeast 3) :
    FaithfulUnitDistanceEmbedding J.attachedGraph := by
  classical
  letI : Fintype J.Edge := Fintype.ofFinite J.Edge
  let N := pairFoundationNeighborhood m J cluster hpattern
  have hNopen : IsOpen N := pairFoundationNeighborhood_isOpen m J cluster hpattern
  have hNne : N.Nonempty := pairFoundationNeighborhood_nonempty m J cluster hpattern

  -- First pass: separate every pair of abstract vertices.
  let CollisionIndex :=
    {p : J.AttachedVertex × J.AttachedVertex // p.1 ≠ p.2}
  letI : Fintype CollisionIndex := Fintype.ofFinite CollisionIndex
  let fcollision : CollisionIndex → (Y → Plane) → Plane := fun a =>
    pairDifference m J cluster hpattern a.1.1 a.1.2
  obtain ⟨C, hCopen, hCne, hCsub, hCavoid⟩ :=
    finite_regular_avoidance_open_region N hNopen hNne fcollision (fun _ => 0)
      (by
        intro a u hu
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, hu⟩
        exact ⟨pairVertexDerivative m J cluster hpattern u a.1.1 -
            pairVertexDerivative m J cluster hpattern u a.1.2,
          pairDifference_hasFDerivAt m J cluster hpattern us a.1.1 a.1.2⟩)
      (by
        intro a u hu hzero
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, hu⟩
        have hcollision : pairRealization m J cluster hpattern u a.1.1 =
            pairRealization m J cluster hpattern u a.1.2 := by
          exact sub_eq_zero.mp hzero
        refine ⟨pairVertexDerivative m J cluster hpattern u a.1.1 -
            pairVertexDerivative m J cluster hpattern u a.1.2,
          pairDifference_hasFDerivAt m J cluster hpattern us a.1.1 a.1.2,
          sub_ne_zero.mpr ?_⟩
        exact pair_collision_derivative_ne m J cluster hpattern hberge us
          a.1.1 a.1.2 a.2 hcollision)
  have hCinj {u : Y → Plane} (hu : u ∈ C) :
      Function.Injective (pairRealization m J cluster hpattern u) := by
    intro x y hxy
    by_contra hne
    have hav := hCavoid u hu (⟨(x, y), hne⟩ : CollisionIndex)
    apply hav
    exact sub_eq_zero.mpr hxy

  -- Second pass: at a shared foundation vertex, no two points from distinct
  -- fibers are collinear with that vertex.
  let CrossIndex := {a : PairCrossDatum J.Edge (oddAttachmentSize m) //
    a.e ≠ a.f ∧ J.vertex a.e a.q = J.vertex a.f a.s}
  letI : Fintype CrossIndex := Fintype.ofFinite CrossIndex
  let fcross : CrossIndex → (Y → Plane) → ℝ := fun a =>
    pairCrossArea m J cluster hpattern (J.vertex a.1.e a.1.q)
      a.1.e a.1.f a.1.i a.1.j
  obtain ⟨G, hGopen, hGne, hGsub, hGavoid⟩ :=
    finite_regular_avoidance_open_region C hCopen hCne fcross (fun _ => 0)
      (by
        intro a u hu
        have huN : u ∈ N := hCsub hu
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, huN⟩
        exact ⟨_, pairCrossArea_hasFDerivAt m J cluster hpattern us
          (J.vertex a.1.e a.1.q) a.1.e a.1.f a.1.i a.1.j⟩)
      (by
        intro a u hu hzero
        have huN : u ∈ N := hCsub hu
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, huN⟩
        exact pairCrossArea_regular_at_injective_zero m J cluster hpattern hberge us
          (hCinj hu) a.1.e a.1.f a.2.1 a.1.q a.1.s a.2.2
          a.1.i a.1.j hzero)
  have hGgeneral {u : Y → Plane} (hu : u ∈ G) :
      pairGeneralPositionAt m J cluster hpattern u := by
    intro e f hef q s hqs i j
    exact hGavoid u hu
      (⟨⟨e, f, q, s, i, j⟩, hef, hqs⟩ : CrossIndex)

  -- Third pass: exclude squared distance one for every graph nonedge.
  let NonedgeIndex :=
    {p : J.AttachedVertex × J.AttachedVertex // ¬J.attachedGraph.Adj p.1 p.2}
  letI : Fintype NonedgeIndex := Fintype.ofFinite NonedgeIndex
  let funit : NonedgeIndex → (Y → Plane) → ℝ := fun a =>
    pairSquaredDistance m J cluster hpattern a.1.1 a.1.2
  obtain ⟨U, _, hUne, hUsub, hUavoid⟩ :=
    finite_regular_avoidance_open_region G hGopen hGne funit (fun _ => 1)
      (by
        intro a u hu
        have huN : u ∈ N := hCsub (hGsub hu)
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, huN⟩
        exact ⟨_, (pairDifference_hasFDerivAt m J cluster hpattern us
          a.1.1 a.1.2).norm_sq⟩)
      (by
        intro a u hu hlevel
        have huC : u ∈ C := hGsub hu
        have huN : u ∈ N := hCsub huC
        let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, huN⟩
        exact pairSquaredDistance_regular_at_unit_nonedge m J cluster hpattern hberge
          us (hCinj huC) (hGgeneral hu) a.1.1 a.1.2 a.2 hlevel)
  obtain ⟨u, huU⟩ := hUne
  have huG : u ∈ G := hUsub huU
  have huC : u ∈ C := hGsub huG
  have huN : u ∈ N := hCsub huC
  let us : pairFoundationNeighborhood m J cluster hpattern := ⟨u, huN⟩
  refine ⟨⟨pairRealization m J cluster hpattern u, hCinj huC⟩, ?_⟩
  intro x y
  constructor
  · intro hdist
    change Dist.dist (pairRealization m J cluster hpattern u x)
      (pairRealization m J cluster hpattern u y) = 1 at hdist
    by_contra hnadj
    have hav := hUavoid u huU
      (⟨(x, y), hnadj⟩ : NonedgeIndex)
    change pairSquaredDistance m J cluster hpattern x y u ≠ 1 at hav
    apply hav
    have hnorm : ‖pairRealization m J cluster hpattern u x -
        pairRealization m J cluster hpattern u y‖ = 1 := by
      simpa only [dist_eq_norm] using hdist
    rw [pairSquaredDistance, pairDifference, hnorm]
    norm_num
  · intro hadj
    exact pairRealization_edges_unit m J cluster hpattern us x y hadj

/-- The faithful witness form needed for the repository's version of Erdős
Problem 705. -/
def HasHighGirthFourChromaticUnitDistanceWitness (K : ℕ) : Prop :=
  ∃ V : Set (EuclideanSpace ℝ (Fin 2)), V.Finite ∧
    K ≤ (UnitDistancePlaneGraph V).girth ∧
    ¬(UnitDistancePlaneGraph V).chromaticNumber ≤ 3

/-- Combinatorial data together with a faithful embedding produce the required
counterexample. -/
theorem witness_of_attachedGraph {X : Type*} [Finite X] {r K : ℕ}
    (H : OrderedUniformHypergraph X r) (hr : 3 ≤ r) (hodd : Odd r)
    (hnot3 : H.NotThreeColorable) (hgirth : K ≤ H.attachedGraph.girth)
    (hemb : FaithfulUnitDistanceEmbedding H.attachedGraph) :
    HasHighGirthFourChromaticUnitDistanceWitness K := by
  obtain ⟨V, hV, hgeq, hceq⟩ := faithfulUnitDistanceEmbedding_range hemb
  refine ⟨V, hV, ?_, ?_⟩
  · rwa [← hgeq]
  · rw [← hceq]
    exact H.attachedGraph_chromaticNumber_not_le_three hr hodd hnot3

/-- The high-girth hypergraph construction, odd cycle attachments, and the
faithful perturbation above give a counterexample for every girth bound. -/
private theorem high_girth_four_chromatic_witnesses :
    ∀ K, HasHighGirthFourChromaticUnitDistanceWitness K := by
  intro K
  let r := oddAttachmentSize K
  have hr2 : 2 ≤ r := by
    dsimp only [r]
    rw [oddAttachmentSize_eq]
    omega
  have hKmax : 1 ≤ max K 3 := by omega
  obtain ⟨n, J, hbergeMax, hnot3, hpattern⟩ :=
    OrderedUniformHypergraph.exists_pairClusterHypergraph r (max K 3) hr2 hKmax
  have hberge3 : J.BergeGirthAtLeast 3 := by
    unfold OrderedUniformHypergraph.BergeGirthAtLeast at hbergeMax ⊢
    exact le_trans (by exact_mod_cast (show 2 * 3 ≤ 2 * max K 3 by omega)) hbergeMax
  have hbergeK : J.BergeGirthAtLeast K := by
    unfold OrderedUniformHypergraph.BergeGirthAtLeast at hbergeMax ⊢
    exact le_trans (by exact_mod_cast (show 2 * K ≤ 2 * max K 3 by omega)) hbergeMax
  have hr3 : 3 ≤ r := by
    dsimp only [r]
    rw [oddAttachmentSize_eq]
    omega
  have hKr : K ≤ r := by
    dsimp only [r]
    rw [oddAttachmentSize_eq]
    omega
  have hodd : Odd r := by
    dsimp only [r]
    rw [oddAttachmentSize_eq]
    exact ⟨K + 1, by omega⟩
  letI : Fintype J.Edge := Fintype.ofFinite J.Edge
  have hemb : FaithfulUnitDistanceEmbedding J.attachedGraph :=
    faithful_pairRealization K J OrderedUniformHypergraph.fourBlockCluster hpattern hberge3
  have hcyclic : ¬J.attachedGraph.IsAcyclic := by
    intro hac
    have hle2 : J.attachedGraph.chromaticNumber ≤ 2 :=
      hac.colorable_two.chromaticNumber_le
    exact J.attachedGraph_chromaticNumber_not_le_three hr3 hodd hnot3
      (hle2.trans (by norm_num))
  have hgirth : K ≤ J.attachedGraph.girth :=
    J.attachedGraph_girth_ge hr3 hKr hbergeK hcyclic
  exact witness_of_attachedGraph J hr3 hodd hnot3 hgirth hemb

/-- Arbitrarily high-girth counterexamples formally imply the negative answer. -/
theorem erdos_705_of_witnesses
    (hO'Donnell : ∀ K, HasHighGirthFourChromaticUnitDistanceWitness K) :
    answer(False) ↔ ∃ k, ∀ V : Set (EuclideanSpace ℝ (Fin 2)), V.Finite →
      (UnitDistancePlaneGraph V).girth ≥ k →
      (UnitDistancePlaneGraph V).chromaticNumber ≤ 3 := by
  rw [false_iff]
  rintro ⟨k, hk⟩
  obtain ⟨V, hV, hgirth, hchrom⟩ := hO'Donnell k
  exact hchrom (hk V hV hgirth)

/-- Erdős Problem 705 has a negative answer. -/
theorem erdos_705 :
    answer(False) ↔ ∃ k, ∀ V : Set ℝ², V.Finite →
      (UnitDistancePlaneGraph V).girth ≥ k →
      (UnitDistancePlaneGraph V).chromaticNumber ≤ 3 :=
  erdos_705_of_witnesses high_girth_four_chromatic_witnesses

#print axioms Erdos705.erdos_705

end Erdos705
