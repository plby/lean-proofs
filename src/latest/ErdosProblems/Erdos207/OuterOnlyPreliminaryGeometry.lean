/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryInternalSafeCandidates
import ErdosProblems.Erdos207.SupportedOuterPreliminaryKernel

/-!
# Geometry for an outer-only preliminary phase

The preliminary greedy phase which sparsifies the outside--outside residual
graph must not use any crossing edge needed by the terminal link cover.  We
therefore expose only triangles disjoint from the next vortex level.  For
the residual-edge product estimate we replace the ambient graph by the
spanning graph whose edge set is exactly `internalOuterEdges G U`.  Its
complement is the auxiliary forbidden graph in `OutsideLeavePairsAlive`, so
that this invariant asks for live pair stars only on the outside--outside
edges actually tracked by the preliminary law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The subfamily of available triangles wholly outside `U`. -/
def outerOnlyAvailable
    {V : Type*} [DecidableEq V]
    (U : Finset V) (A : TripleSystemOn V) : TripleSystemOn V :=
  A.filter fun T ↦ Disjoint T.1 U

@[simp]
lemma mem_outerOnlyAvailable_iff
    {V : Type*} [DecidableEq V]
    {U : Finset V} {A : TripleSystemOn V} {T : TripleOn V} :
    T ∈ outerOnlyAvailable U A ↔ T ∈ A ∧ Disjoint T.1 U := by
  simp [outerOnlyAvailable]

lemma outerOnlyAvailable_subset
    {V : Type*} [DecidableEq V]
    (U : Finset V) (A : TripleSystemOn V) :
    outerOnlyAvailable U A ⊆ A :=
  filter_subset _ _

lemma trianglesDisjointFrom_outerOnlyAvailable
    {V : Type*} [DecidableEq V]
    (U : Finset V) (A : TripleSystemOn V) :
    TrianglesDisjointFrom U (outerOnlyAvailable U A) := by
  intro T hT
  exact (mem_outerOnlyAvailable_iff.mp hT).2

lemma ConsistsOfTriangles.outerOnlyAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A : TripleSystemOn V}
    (hA : ConsistsOfTriangles G A) :
    ConsistsOfTriangles G (outerOnlyAvailable U A) := by
  intro T hT
  exact hA T (outerOnlyAvailable_subset U A hT)

/-- The spanning graph containing exactly the edges of `G` whose two
displayed endpoints lie outside `U`. -/
def internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (internalOuterEdges G U : Set (Sym2 V))

lemma edgeSet_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    (internalOuterGraph G U).edgeSet =
      (internalOuterEdges G U : Set (Sym2 V)) := by
  ext e
  simp only [internalOuterGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    exact (G.not_isDiag_of_mem_edgeSet
      (mem_graphEdges_iff.mp
        (internalOuterEdges_subset_graphEdges G U he)))

lemma graphEdges_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    graphEdges (internalOuterGraph G U) = internalOuterEdges G U := by
  ext e
  rw [mem_graphEdges_iff, edgeSet_internalOuterGraph]
  rfl

lemma outerGraphEdges_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    outerGraphEdges (internalOuterGraph G U) U =
      internalOuterEdges G U := by
  ext e
  rw [mem_outerGraphEdges_iff, graphEdges_internalOuterGraph]
  constructor
  · exact fun h ↦ h.1
  · intro he
    refine ⟨he, ?_⟩
    intro hsub
    exact (mem_internalOuterEdges_iff.mp he).2.1
      (hsub (by simpa using Sym2.out_fst_mem e))

lemma preliminaryResidualOuterEdges_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    preliminaryResidualOuterEdges (internalOuterGraph G U) U P =
      preliminaryResidualInternalEdges G U P := by
  change
    outerGraphEdges (internalOuterGraph G U) U \
        graphEdges (coveredGraph P) =
      internalOuterEdges G U ∩
        (outerGraphEdges G U \ graphEdges (coveredGraph P))
  rw [outerGraphEdges_internalOuterGraph]
  ext e
  simp only [mem_sdiff, mem_inter]
  constructor
  · rintro ⟨he, hnotCovered⟩
    exact ⟨he, internalOuterEdges_subset_outerGraphEdges G U he,
      hnotCovered⟩
  · rintro ⟨he, _heOuter, hnotCovered⟩
    exact ⟨he, hnotCovered⟩

lemma outerIncidentEdges_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (v : V) :
    outerIncidentEdges (internalOuterGraph G U) U v =
      scheduledEdgesAt (internalOuterEdges G U) v := by
  ext e
  rw [mem_outerIncidentEdges_iff, mem_scheduledEdgesAt_iff,
    outerGraphEdges_internalOuterGraph]
  rw [Sym2.mem_toFinset]

/-- If all internal-outer graph edges have a live pair star, the complement
of that graph is exactly the auxiliary blocker graph needed by the existing
outside-pair-survival invariant. -/
lemma outsideLeavePairsAlive_compl_internalOuterGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {S : GreedyStateOn V}
    (halive : ∀ e ∈ internalOuterEdges G U, PairAlive e.toFinset S) :
    OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S := by
  intro u v hnotCompl _hnotBoth hleave
  have houter : (internalOuterGraph G U).Adj u v := by
    by_contra hnotOuter
    apply hnotCompl
    simp only [SimpleGraph.compl_adj]
    exact ⟨hleave.ne, hnotOuter⟩
  have he : s(u, v) ∈ internalOuterEdges G U := by
    rw [← graphEdges_internalOuterGraph G U, mem_graphEdges_iff]
    exact houter
  simpa [Sym2.toFinset_mk_eq] using halive s(u, v) he

/-- An ambient one-edge extension count exceeding the size of the next
vortex level leaves an extension vertex outside that level.  Consequently
the edge has a live pair star in the outer-only available family. -/
lemma IsIterationTypical.internalOuter_pairAlive_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (P : TripleSystemOn V) {e : Sym2 V}
    (he : e ∈ internalOuterEdges G (W.U i.succ)) :
    PairAlive e.toFinset
      (relativePreliminaryInitialState P
        (outerOnlyAvailable (W.U i.succ) A)) := by
  let u := e.out.1
  let v := e.out.2
  have heGraph : e ∈ graphEdges G :=
    internalOuterEdges_subset_graphEdges G (W.U i.succ) he
  have huv : u ≠ v := out_fst_ne_snd_of_mem_graphEdges heGraph
  have hadj : G.Adj u v := graph_adj_out_of_mem_graphEdges heGraph
  have hsupp := hGsupp hadj
  have hwindow := htyp.2 i hstage i.castSucc (Or.inl rfl)
    (SimpleGraph.edge u v)
    (SimpleGraph.edge_le_iff G |>.mpr (Or.inr hadj))
    (edge_graphSupportedOn hsupp.1 hsupp.2) (by
      rw [graphSupportFinset_edge huv, card_pair huv]
      exact hh)
  rw [graphSupportFinset_edge huv, card_pair huv,
    graphEdges_edge huv, card_singleton, pow_one] at hwindow
  have htargetCard : (W.U i.succ).card + 2 <
      (iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.castSucc)).card := by
    exact_mod_cast hgap.trans_le hwindow.1
  have huout : u ∉ W.U i.succ :=
    (mem_internalOuterEdges_iff.mp he).2.1
  have hvout : v ∉ W.U i.succ :=
    (mem_internalOuterEdges_iff.mp he).2.2
  let forbidden : Finset V := W.U i.succ ∪ {u, v}
  have hforbiddenCard : forbidden.card ≤ (W.U i.succ).card + 2 := by
    calc
      forbidden.card ≤ (W.U i.succ).card + ({u, v} : Finset V).card :=
        card_union_le _ _
      _ = (W.U i.succ).card + 2 := by rw [card_pair huv]
  have hcard : forbidden.card <
      (iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.castSucc)).card :=
    hforbiddenCard.trans_lt htargetCard
  obtain ⟨w, hw, hwforbidden⟩ :=
    exists_mem_notMem_of_card_lt_card hcard
  have hwout : w ∉ W.U i.succ := by
    intro hwU
    exact hwforbidden (mem_union_left _ hwU)
  have hwu : w ≠ u := by
    intro hwu
    apply hwforbidden
    exact mem_union_right _ (by simp [hwu])
  have hwv : w ≠ v := by
    intro hwv
    apply hwforbidden
    exact mem_union_right _ (by simp [hwv])
  let w' : ThirdVertex u v :=
    ⟨w, hwu, hwv⟩
  let T : TripleOn V := thirdVertexTriple huv w'
  have hTA : T ∈ A := by
    have hwdata := mem_iterationExtensionVertices_iff.mp hw
    have hedge : s(u, v) ∈ graphEdges (SimpleGraph.edge u v) := by
      rw [graphEdges_edge huv]
      simp
    obtain ⟨T₀, hT₀A, hwT₀, heT₀⟩ := hwdata.2 s(u, v) hedge
    have huvT₀ := mk_mem_tripleEdgeFinset_iff.mp heT₀
    have hsub : T.1 ⊆ T₀.1 := by
      intro x hx
      simp only [T, thirdVertexTriple, tripleOfThree, mem_insert,
        mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact huvT₀.1
      · exact huvT₀.2.1
      · exact hwT₀
    have hEq : T = T₀ := by
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by
        rw [T₀.2]
        exact T.2.ge)
    rw [hEq]
    exact hT₀A
  have hTdisj : Disjoint T.1 (W.U i.succ) := by
    rw [Finset.disjoint_left]
    intro x hxT hxU
    simp only [T, thirdVertexTriple, tripleOfThree, mem_insert,
      mem_singleton] at hxT
    rcases hxT with rfl | rfl | rfl
    · exact huout hxU
    · exact hvout hxU
    · exact hwout hxU
  refine ⟨T, mem_availableTrianglesContainingPair_iff.mpr ⟨?_, ?_⟩⟩
  · exact mem_outerOnlyAvailable_iff.mpr ⟨hTA, hTdisj⟩
  · intro x hx
    have hx' := Sym2.mem_toFinset.mp hx
    have hxpair : x ∈ s(u, v) := by
      simpa only [u, v, e.out_eq] using hx'
    rcases (Sym2.mem_iff.mp hxpair) with rfl | rfl
    · simp [T, thirdVertexTriple, tripleOfThree]
    · simp [T, thirdVertexTriple, tripleOfThree]

/-- Iteration typicality supplies the auxiliary outside-pair-survival
predicate for the graph that tracks only outside--outside edges. -/
theorem IsIterationTypical.outsideLeavePairsAlive_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (P : TripleSystemOn V) :
    OutsideLeavePairsAlive (internalOuterGraph G (W.U i.succ))ᶜ
      (W.U i.succ)
      (relativePreliminaryInitialState P
        (outerOnlyAvailable (W.U i.succ) A)) := by
  apply outsideLeavePairsAlive_compl_internalOuterGraph
  intro e he
  exact htyp.internalOuter_pairAlive_outerOnly i hstage hGsupp hh hgap P he

/-- If every member of `A` is already legal over the empty packing, then
reinitializing the absorber-greedy process on an outer-only restriction does
not delete any further triangle. -/
lemma absorberGreedyInitialState_outerOnly_eq_relative
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} (U : Finset V)
    (hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A)) :
    absorberGreedyInitialState F (outerOnlyAvailable U A) =
      relativePreliminaryInitialState ∅ (outerOnlyAvailable U A) := by
  have havailable : legalAvailable F ∅ (outerOnlyAvailable U A) =
      outerOnlyAvailable U A := by
    ext T
    rw [mem_legalAvailable_iff]
    constructor
    · exact fun hT ↦ hT.1
    · intro hT
      exact ⟨hT, hInv.2.2 T (outerOnlyAvailable_subset U A hT)⟩
  unfold absorberGreedyInitialState relativePreliminaryInitialState
  rw [havailable]

/-- The canonical outer-only initial state simultaneously has the absorber
invariant and the auxiliary outside-pair-survival invariant.  This is the
common deterministic input to the scheduled product and tracked-residual
laws. -/
theorem IsIterationTypical.absorberGreedyInitialState_outerOnly_ready
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A))
    (hFnonempty : ∀ S ∈ F, S.Nonempty) :
    let S₀ := absorberGreedyInitialState F
      (outerOnlyAvailable (W.U i.succ) A)
    AbsorberGreedyInvariant F (outerOnlyAvailable (W.U i.succ) A) S₀ ∧
      OutsideLeavePairsAlive
        (internalOuterGraph G (W.U i.succ))ᶜ (W.U i.succ) S₀ ∧
      S₀.chosen = ∅ := by
  dsimp only
  let S₀ := absorberGreedyInitialState F
    (outerOnlyAvailable (W.U i.succ) A)
  have hstate : S₀ = relativePreliminaryInitialState ∅
      (outerOnlyAvailable (W.U i.succ) A) := by
    exact absorberGreedyInitialState_outerOnly_eq_relative
      (W.U i.succ) hInv
  refine ⟨absorberGreedyInitialState_invariant F
    (outerOnlyAvailable (W.U i.succ) A) hFnonempty, ?_, ?_⟩
  · change OutsideLeavePairsAlive
      (internalOuterGraph G (W.U i.succ))ᶜ (W.U i.succ) S₀
    rw [hstate]
    exact htyp.outsideLeavePairsAlive_outerOnly i hstage hGsupp hh hgap ∅
  · rfl

/-- Restricting the available family of a greedy state preserves the greedy
invariant. -/
lemma GreedyInvariant.restrictAvailable
    {V : Type*} [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {A' : TripleSystemOn V} (hS : GreedyInvariant F S)
    (hsub : A' ⊆ S.available) :
    GreedyInvariant F { chosen := S.chosen, available := A' } := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  intro T hT
  exact hS.2.2 T (hsub hT)

/-- The existing supported preliminary product theorem specializes to the
outer-only family and tracks exactly the residual internal edge set. -/
theorem supportedConditionedOuterOnlyPreliminaryKernel_internalProductLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (G : SimpleGraph V) (A P : TripleSystemOn V)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    {p etaTypical xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p etaTypical xi h)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h)
    (hgap : (((W.U i.succ).card + 2 : ℕ) : ℝ≥0) <
      (1 - xi) *
        (p ^ 2 * etaTypical * (W.U i.castSucc).card))
    (hInv : GreedyInvariant F (relativePreliminaryInitialState P A))
    (hGleave : G ≤ leaveGraph P)
    (Kpair Kglobal Kinc Delta delta Icut Dcut M supply : ℕ)
    (hDcut : 0 < Dcut) (hsupplyM : supply ≤ M)
    (h3supply : 3 * supply ≤ delta)
    (alpha eta epsilon : ℝ≥0)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta Icut Dcut 0
        (relativePreliminaryInitialState P
          (outerOnlyAvailable (W.U i.succ) A)))
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta Icut Dcut j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - supply : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut)
        (relativePreliminaryInitialState P
          (outerOnlyAvailable (W.U i.succ) A))).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta Icut Dcut z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    let S₀ := relativePreliminaryInitialState P
      (outerOnlyAvailable (W.U i.succ) A)
    RelativePreliminaryReady n F Kpair Kglobal Kinc Delta delta Icut
        Dcut S₀ ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta Icut Dcut S₀).probability
            (fun z ↦ Q ⊆ z.2.chosen \ P ∧
              E ⊆ preliminaryResidualInternalEdges
                G (W.U i.succ) z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
  dsimp only
  let S₀ := relativePreliminaryInitialState P
    (outerOnlyAvailable (W.U i.succ) A)
  let Gout := internalOuterGraph G (W.U i.succ)
  have hInv₀ : GreedyInvariant F S₀ := by
    exact hInv.restrictAvailable (outerOnlyAvailable_subset _ _)
  have houtside : OutsideLeavePairsAlive Goutᶜ (W.U i.succ) S₀ := by
    simpa only [S₀, Gout] using
      htyp.outsideLeavePairsAlive_outerOnly i hstage hGsupp hh hgap P
  have hdisjoint : Disjoint Goutᶜ Gout := disjoint_compl_left
  have hGoutLeave : Gout ≤ leaveGraph P := by
    intro u v huv
    apply hGleave
    have he : s(u, v) ∈ Gout.edgeSet := huv
    rw [edgeSet_internalOuterGraph] at he
    have heG : s(u, v) ∈ G.edgeSet := mem_graphEdges_iff.mp
      (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)
    exact heG
  have hprod :=
    supportedConditionedRelativePreliminaryKernel_outerProductLaw
      n F Goutᶜ Gout (W.U i.succ) Kpair Kglobal Kinc Delta delta
      Icut Dcut M supply hDcut hsupplyM h3supply alpha eta epsilon S₀
      hInv₀ houtside hdisjoint hGoutLeave hsmall hactive₀ hupper
      hselected hsurvived hinactive hepsilon
  simpa only [S₀, Gout,
    preliminaryResidualOuterEdges_internalOuterGraph,
    relativePreliminaryInitialState_chosen] using hprod

end

end Erdos207
