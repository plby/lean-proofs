/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Removing isolated vertices from coded finite graphs

The induction for Erdős Problem 570 repeatedly takes induced subgraphs and
then discards their isolated vertices.  `supportCode H` is the canonical code
of the graph induced by the support of `H`; it has exactly the same edges as
`H`, has no isolated vertices, and is contained in `H`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- A graph induced on a finite vertex set, recoded on `Fin S.card`. -/
def inducedCode (H : GraphCode) (S : Finset (Fin H.vertexCount)) : GraphCode :=
  let G := H.graph.induce (S : Set (Fin H.vertexCount))
  ⟨S.card, G.overFin (by simp)⟩

@[simp] theorem inducedCode_vertexCount (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    (inducedCode H S).vertexCount = S.card := rfl

/-- The canonical isomorphism from an induced graph to its code. -/
def inducedCodeIso (H : GraphCode) (S : Finset (Fin H.vertexCount)) :
    H.graph.induce (S : Set (Fin H.vertexCount)) ≃g (inducedCode H S).graph := by
  change H.graph.induce (S : Set (Fin H.vertexCount)) ≃g
    (H.graph.induce (S : Set (Fin H.vertexCount))).overFin (by simp)
  exact SimpleGraph.overFinIso (G :=
    H.graph.induce (S : Set (Fin H.vertexCount))) (by simp)

/-- An induced code is ordinarily contained in its source graph. -/
theorem inducedCode_isContained (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) : IsContained (inducedCode H S) H := by
  let e := inducedCodeIso H S
  exact ⟨(SimpleGraph.Embedding.induce
      (S : Set (Fin H.vertexCount))).toCopy.comp e.symm.toCopy⟩

theorem inducedCode_edgeCount_le (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    (inducedCode H S).edgeCount ≤ H.edgeCount :=
  (inducedCode_isContained H S).edgeCount_le

/-- The code obtained by deleting one specified vertex. -/
def deleteVertexCode (H : GraphCode) (v : Fin H.vertexCount) : GraphCode :=
  inducedCode H (Finset.univ.erase v)

/-- The actual one-vertex deletion is canonically isomorphic to its code. -/
def deleteVertexCodeIso (H : GraphCode) (v : Fin H.vertexCount) :
    H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ≃g
      (deleteVertexCode H v).graph := by
  have hset : ({v} : Set (Fin H.vertexCount))ᶜ =
      ((Finset.univ.erase v : Finset (Fin H.vertexCount)) :
        Set (Fin H.vertexCount)) := by
    ext x
    simp
  let es : ↑(({v} : Set (Fin H.vertexCount))ᶜ) ≃
      ↑((Finset.univ.erase v : Finset (Fin H.vertexCount)) :
        Set (Fin H.vertexCount)) := Equiv.setCongr hset
  let eg : H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ≃g
      H.graph.induce
        ((Finset.univ.erase v : Finset (Fin H.vertexCount)) :
          Set (Fin H.vertexCount)) :=
    { toEquiv := es
      map_rel_iff' := by
        intro x y
        rfl }
  exact eg.trans (inducedCodeIso H (Finset.univ.erase v))

@[simp] theorem deleteVertexCode_vertexCount (H : GraphCode)
    (v : Fin H.vertexCount) :
    (deleteVertexCode H v).vertexCount = H.vertexCount - 1 := by
  simp [deleteVertexCode]

/-- Deleting a vertex removes exactly its incident edges. -/
theorem deleteVertexCode_edgeCount (H : GraphCode)
    (v : Fin H.vertexCount) [DecidableRel H.graph.Adj] :
    (deleteVertexCode H v).edgeCount = H.edgeCount - H.graph.degree v := by
  classical
  let : DecidableRel (deleteVertexCode H v).graph.Adj := Classical.decRel _
  rw [(deleteVertexCode H v).edgeCount_eq_card_edgeFinset,
    H.edgeCount_eq_card_edgeFinset]
  rw [← (deleteVertexCodeIso H v).card_edgeFinset_eq]
  calc
    (H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ).edgeFinset.card =
        (H.graph.deleteIncidenceSet v).edgeFinset.card :=
      H.graph.card_edgeFinset_induce_compl_singleton v
    _ = H.graph.edgeFinset.card - H.graph.degree v :=
      H.graph.card_edgeFinset_deleteIncidenceSet v

theorem deleteVertexGraph_isContained_of_code_isContained
    {H : GraphCode} (v : Fin H.vertexCount) {V : Type*}
    {C : SimpleGraph V} (h : (deleteVertexCode H v).graph ⊑ C) :
    H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑ C := by
  have he : H.graph.induce ({v} : Set (Fin H.vertexCount))ᶜ ⊑
      (deleteVertexCode H v).graph := ⟨(deleteVertexCodeIso H v).toCopy⟩
  exact SimpleGraph.IsContained.trans he h

/-- The graph obtained from `H` by deleting every isolated vertex, recoded on
a finite ordinal. -/
def supportCode (H : GraphCode) : GraphCode :=
  letI : Fintype H.graph.support := Fintype.ofFinite H.graph.support
  let G := H.graph.induce H.graph.support
  ⟨Nat.card H.graph.support,
    G.overFin Nat.card_eq_fintype_card.symm⟩

@[simp] theorem supportCode_vertexCount (H : GraphCode) :
    (supportCode H).vertexCount = Nat.card H.graph.support := rfl

/-- The canonical isomorphism between the support-induced graph and its code. -/
def supportCodeIso (H : GraphCode) :
    H.graph.induce H.graph.support ≃g (supportCode H).graph := by
  letI : Fintype H.graph.support := Fintype.ofFinite H.graph.support
  change H.graph.induce H.graph.support ≃g
    (H.graph.induce H.graph.support).overFin
      Nat.card_eq_fintype_card.symm
  exact SimpleGraph.overFinIso (G := H.graph.induce H.graph.support)
    Nat.card_eq_fintype_card.symm

/-- Deleting isolated vertices preserves every edge. -/
@[simp] theorem supportCode_edgeCount (H : GraphCode) :
    (supportCode H).edgeCount = H.edgeCount := by
  classical
  unfold GraphCode.edgeCount
  calc
    Nat.card (supportCode H).graph.edgeSet =
        Nat.card (H.graph.induce H.graph.support).edgeSet := by
      exact (Nat.card_congr (supportCodeIso H).mapEdgeSet).symm
    _ = Nat.card H.graph.edgeSet := by
      let : DecidableRel H.graph.Adj := Classical.decRel H.graph.Adj
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        SimpleGraph.card_edgeSet, SimpleGraph.card_edgeSet]
      exact H.graph.card_edgeFinset_induce_support

/-- The support code is an ordinary subgraph of the original graph. -/
theorem supportCode_isContained (H : GraphCode) :
    IsContained (supportCode H) H := by
  let e := supportCodeIso H
  exact ⟨(SimpleGraph.Embedding.induce
      H.graph.support).toCopy.comp
    e.symm.toCopy⟩

/-- After restricting to the support, no isolated vertices remain. -/
theorem supportCode_noIsolated (H : GraphCode) : NoIsolated (supportCode H) := by
  intro v
  apply (supportCode H).graph.exists_adj_iff_not_isIsolated.mp
  let e := supportCodeIso H
  let x : H.graph.support := e.symm v
  obtain ⟨w, hxw⟩ := H.graph.mem_support.mp x.property
  let y : H.graph.support := ⟨w, hxw.mem_support_right⟩
  refine ⟨e y, ?_⟩
  have hxy : (H.graph.induce H.graph.support).Adj x y := hxw
  have hmap := e.toHom.map_adj hxy
  have hex : e x = v := by
    dsimp only [x]
    exact e.apply_symm_apply v
  rw [← hex]
  exact hmap

/-- The isolate-free core of an induced subgraph. -/
def supportedInducedCode (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) : GraphCode :=
  supportCode (inducedCode H S)

@[simp] theorem supportedInducedCode_edgeCount (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    (supportedInducedCode H S).edgeCount = (inducedCode H S).edgeCount := by
  simp [supportedInducedCode]

theorem supportedInducedCode_edgeCount_le (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    (supportedInducedCode H S).edgeCount ≤ H.edgeCount := by
  simpa using inducedCode_edgeCount_le H S

theorem supportedInducedCode_noIsolated (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    NoIsolated (supportedInducedCode H S) :=
  supportCode_noIsolated (inducedCode H S)

theorem supportedInducedCode_isContained (H : GraphCode)
    (S : Finset (Fin H.vertexCount)) :
    IsContained (supportedInducedCode H S) H :=
  (supportCode_isContained (inducedCode H S)).trans
    (inducedCode_isContained H S)

/-- Every coded graph on at most `n` vertices is contained in `Kₙ`. -/
theorem isContained_completeCode_of_vertexCount_le {H : GraphCode} {n : ℕ}
    (hn : H.vertexCount ≤ n) : IsContained H (completeCode n) := by
  let f : Fin H.vertexCount ↪ Fin n := Fin.castLEEmb hn
  let htop : H.graph ⊑ (⊤ : SimpleGraph (Fin H.vertexCount)) :=
    SimpleGraph.IsContained.of_le le_top
  let e : (⊤ : SimpleGraph (Fin H.vertexCount)) ↪g
      (⊤ : SimpleGraph (Fin n)) :=
    SimpleGraph.Embedding.completeGraph f
  exact htop.trans ⟨e.toCopy⟩

/-- Replacing a target by the complete graph on the same or a larger vertex
set gives a valid Ramsey upper bound. -/
theorem graphRamseyNumber_le_complete_of_vertexCount_le
    (F H : GraphCode) {n : ℕ} (hn : H.vertexCount ≤ n) :
    graphRamseyNumber F H ≤ graphRamseyNumber F (completeCode n) := by
  apply graphRamseyNumber_le_of_ramseyAt
  exact (graphRamseyNumber_spec F (completeCode n)).mono_right
    (isContained_completeCode_of_vertexCount_le hn)

/-- A copy of the isolate-free core extends to a copy of the original graph
whenever the host region has room for all original vertices.  The extra
vertices are assigned injectively outside the range of the core copy; they
need preserve no edges because every endpoint of an edge lies in the support. -/
theorem isContained_induce_of_supportCode_isContained
    {H : GraphCode} {V : Type*} [Fintype V] (C : SimpleGraph V)
    (S : Finset V)
    (hcore : (supportCode H).graph ⊑ C.induce (S : Set V))
    (hcard : H.vertexCount ≤ S.card) :
    H.graph ⊑ C.induce (S : Set V) := by
  classical
  obtain ⟨copy⟩ := hcore
  let A : Set (Fin H.vertexCount) := H.graph.support
  let fA : A → S := fun x ↦ copy (supportCodeIso H x)
  have hfA : Function.Injective fA :=
    copy.injective.comp (supportCodeIso H).injective
  let used : Finset S := Finset.univ.image fA
  have hused : used.card = Fintype.card A := by
    change (Finset.univ.image fA).card = Fintype.card A
    rw [Finset.card_image_of_injective _ hfA]
    simp
  let D := {x : Fin H.vertexCount // x ∉ A}
  let R := {y : S // y ∉ used}
  have hcardD : Fintype.card D = H.vertexCount - Fintype.card A := by
    change Fintype.card {x : Fin H.vertexCount // ¬x ∈ A} = _
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hcardR : Fintype.card R = S.card - Fintype.card A := by
    calc
      Fintype.card R = Fintype.card S - Fintype.card {y : S // y ∈ used} := by
        change Fintype.card {y : S // ¬y ∈ used} = _
        exact Fintype.card_subtype_compl _
      _ = S.card - used.card := by simp
      _ = S.card - Fintype.card A := by rw [hused]
  have hcardRem : Fintype.card D ≤ Fintype.card R := by
    rw [hcardD, hcardR]
    exact Nat.sub_le_sub_right hcard _
  let eR : D ↪ R :=
    (Fintype.equivFin D).toEmbedding |>.trans
      ((Fin.castLEEmb hcardRem).trans (Fintype.equivFin R).symm.toEmbedding)
  let f : Fin H.vertexCount → S := fun x ↦
    if hx : x ∈ A then fA ⟨x, hx⟩ else (eR ⟨x, hx⟩).1
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · dsimp only [f] at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (hfA hxy)
    · dsimp only [f] at hxy
      rw [dif_pos hx, dif_neg hy] at hxy
      exfalso
      exact (eR ⟨y, hy⟩).2 (by
        rw [Finset.mem_image]
        exact ⟨⟨x, hx⟩, Finset.mem_univ _, hxy⟩)
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_pos hy] at hxy
      exfalso
      exact (eR ⟨x, hx⟩).2 (by
        rw [Finset.mem_image]
        exact ⟨⟨y, hy⟩, Finset.mem_univ _, hxy.symm⟩)
    · dsimp only [f] at hxy
      rw [dif_neg hx, dif_neg hy] at hxy
      exact congrArg Subtype.val
        (eR.injective (Subtype.ext hxy))
  let hom : H.graph →g C.induce (S : Set V) :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        have hx : x ∈ A := by
          exact H.graph.mem_support.mpr ⟨y, hxy⟩
        have hy : y ∈ A := by
          exact H.graph.mem_support.mpr ⟨x, hxy.symm⟩
        dsimp only [f]
        rw [dif_pos hx, dif_pos hy]
        apply copy.toHom.map_adj
        apply (supportCodeIso H).toHom.map_adj
        exact hxy }
  exact ⟨hom.toCopy hf⟩

end Erdos570
