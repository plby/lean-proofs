/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakReferenceCompletion
import ErdosProblems.Erdos599.ColouredSafeSpliceRealTerminalLedger
import ErdosProblems.Erdos599.ColouredSafeTouchedStrongSwitch
import ErdosProblems.Erdos599.ColouredSafeTouchedInfiniteSwitch

/-!
# Real-edge ledgers for the three local native transactions

This file is the exact graph-independent seam used by the native weak,
strong, and infinite blueprint transactions.  The predicate `R` selects the
edges later called real.  A scheduled source is assumed to be an old
`R`-terminal.  Consequently its represented outgoing cut edge is not real.

The one- and two-port constructors then retain every old real edge and every
old real terminal other than the scheduled source.  If the displayed finite
inserted path is nontrivial and consists of real edges, it also witnesses
that the scheduled source is no longer a real terminal.  The weak native
transaction has a separate exact constructor because it inserts one
connector and all touched-reference companions at once.

No fair scheduling or limit assertion is made here.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeLocalTransactionRealLedger

open DirectedPath Alternating Blueprint
open ColouredSafeAmbientOccurrence ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V}

abbrev RealEdges (R : V → V → Prop) (W : Set Gamma.DPath) :=
  ColouredSafeSpliceRealTerminalLedger.realFamilyEdges R W

abbrev IsRealTerminal (R : V → V → Prop)
    (W : Set Gamma.DPath) (x : V) :=
  ColouredSafeSpliceRealTerminalLedger.IsRealTerminal R W x

/-- The cut edge leaving an old real terminal cannot itself be real. -/
theorem cut_not_real {R : V → V → Prop} {W : Set Gamma.DPath}
    {s t : V} (hs : IsRealTerminal (Gamma := Gamma) R W s)
    (hedge : (s, t) ∈ familyEdges W) : ¬ R s t := by
  intro hreal
  exact hs.2 ⟨t, hedge, hreal⟩

/-- A nontrivial displayed path of real output edges removes real-terminal
status from its initial vertex. -/
theorem not_isRealTerminal_of_nontrivial_path
    {R : V → V → Prop} {U : Set Gamma.DPath}
    (p : FinitePath Gamma.graph)
    (hedges : p.edgeSet ⊆ familyEdges U)
    (hreal : ∀ e ∈ p.edgeSet, R e.1 e.2)
    (hne : p.start ≠ p.finish) :
    ¬ IsRealTerminal (Gamma := Gamma) R U p.start := by
  intro hs
  obtain ⟨y, hpy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      p p.start_mem_support hne
  exact hs.2 ⟨y, hedges hpy, hreal (p.start, y) hpy⟩

namespace Strong

variable {Y : Set Gamma.DPath} {s t : V}
variable {A : CurrentSafeOccurrence (Set.univ : Set Gamma.DPath) Y s}

/-- In the actual strong switch, source exposure from the touched reference
and the displayed reference-terminal endpoint make the source path
nontrivial. -/
theorem sourcePath_nontrivial_of_source_off
    (T : TouchedStrongSwitch A t)
    (hs : s ∉ Gamma.vertexSet A.touchedReference) :
    T.sourcePath.start ≠ T.sourcePath.finish := by
  intro he
  apply hs
  have hfinishV : T.sourcePath.finish ∈ Gamma.vertexSet A.touchedReference :=
    terminalFrontier_subset_vertexSet A.touchedReference T.source_finish
  have hfinish : T.sourcePath.finish = s := he.symm.trans T.source_start
  exact Set.mem_of_eq_of_mem hfinish.symm hfinishV

#print axioms sourcePath_nontrivial_of_source_off

end Strong

namespace Infinite

variable {Y : Set Gamma.DPath} {s : V}
variable {A : CurrentSafeOccurrence (Set.univ : Set Gamma.DPath) Y s}

/-- The same exposure argument for the finite source component selected from
an infinite native occurrence. -/
theorem sourcePath_nontrivial_of_source_off
    (T : TouchedInfiniteSwitch A)
    (hs : s ∉ Gamma.vertexSet A.touchedReference) :
    T.sourcePath.start ≠ T.sourcePath.finish := by
  intro he
  apply hs
  have hfinishV : T.sourcePath.finish ∈ Gamma.vertexSet A.touchedReference :=
    terminalFrontier_subset_vertexSet A.touchedReference T.source_finish
  have hfinish : T.sourcePath.finish = s := he.symm.trans T.source_start
  exact Set.mem_of_eq_of_mem hfinish.symm hfinishV

#print axioms sourcePath_nontrivial_of_source_off

end Infinite

namespace OnePort

variable {R : V → V → Prop} {W K : Set Gamma.DPath} {s : V}

/-- Exact one-port transaction with its real-edge and real-terminal ledger. -/
theorem exists_realLedger
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hsW : s ∈ Gamma.terminalFrontier W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V))
    (hsReal : IsRealTerminal (Gamma := Gamma) R W s)
    (hsourceReal : ∀ e ∈ sourcePath.edgeSet, R e.1 e.2)
    (hsourceNontrivial : sourcePath.start ≠ sourcePath.finish) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = familyEdges W ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        (Gamma.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      RealEdges (Gamma := Gamma) R W ⊆ RealEdges (Gamma := Gamma) R U ∧
      (∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R U x) ∧
      ¬ IsRealTerminal (Gamma := Gamma) R U s ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D, hDsource⟩ :=
    ColouredSafeOnePortSplice.exists_data_of_port_with_path hW hK hKfinite hsW
      sourcePath hsource hstart hinter
  have hsourceEdges : sourcePath.edgeSet ⊆ familyEdges D.paths := by
    simpa only [hDsource] using D.sourcePath_edgeSet_subset_familyEdges
  have hsNot := not_isRealTerminal_of_nontrivial_path sourcePath
    hsourceEdges hsourceReal hsourceNontrivial
  exact ⟨D.paths, D.paths_isWarp, D.familyEdges_paths, D.vertexSet_paths,
    D.initialSet_paths, D.terminalFrontier_paths, hsourceEdges,
    ColouredSafeSpliceRealTerminalLedger.OnePort.realFamilyEdges_subset D,
    fun x hx hxs ↦
      ColouredSafeSpliceRealTerminalLedger.OnePort.isRealTerminal_of_ne_port D hx hxs,
    hstart ▸ hsNot, D.finite_rayTrace⟩

#print axioms exists_realLedger

end OnePort

namespace TwoPort

variable {R : V → V → Prop} {W K : Set Gamma.DPath} {s t : V}

/-- Exact two-port transaction with its real-edge and real-terminal ledger.
The non-reality of the cut edge is derived from the scheduled source's old
real-terminal status rather than supplied independently. -/
theorem exists_realLedger
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (ps qt : FinitePath Gamma.graph)
    (hps : (Sum.inl ps : Gamma.DPath) ∈ K)
    (hqt : (Sum.inl qt : Gamma.DPath) ∈ K)
    (hpq : (Sum.inl ps : Gamma.DPath) ≠ Sum.inl qt)
    (hpsStart : ps.start = s) (hqtFinish : qt.finish = t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V))
    (htK : t ∈ Gamma.terminalFrontier K)
    (hsReal : IsRealTerminal (Gamma := Gamma) R W s)
    (hpsReal : ∀ e ∈ ps.edgeSet, R e.1 e.2)
    (hpsNontrivial : ps.start ≠ ps.finish) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      ps.edgeSet ⊆ familyEdges U ∧
      RealEdges (Gamma := Gamma) R W ⊆ RealEdges (Gamma := Gamma) R U ∧
      (∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R U x) ∧
      ¬ IsRealTerminal (Gamma := Gamma) R U s ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D⟩ :=
    ColouredSafeStrongTwoPortSplice.exists_data_of_familyEdge hW hK hKfinite hst
      ps qt hps hqt hpq hpsStart hqtFinish hinter
  have hpsEdges : ps.edgeSet ⊆ familyEdges D.paths := by
    intro e he
    rw [D.familyEdges_paths]
    exact Or.inr (Set.mem_iUnion.mpr ⟨(Sum.inl ps : Gamma.DPath),
      Set.mem_iUnion.mpr ⟨hps, he⟩⟩)
  have hsNot := not_isRealTerminal_of_nontrivial_path ps
    hpsEdges hpsReal hpsNontrivial
  have hcut : ¬ R s t := cut_not_real hsReal hst
  exact ⟨D.paths, D.paths_isWarp, D.familyEdges_paths, D.vertexSet_paths,
    D.initialSet_paths, D.terminalFrontier_paths, hpsEdges,
    ColouredSafeSpliceRealTerminalLedger.TwoPort.realFamilyEdges_subset D hcut,
    fun x hx hxs ↦
      ColouredSafeSpliceRealTerminalLedger.TwoPort.isRealTerminal_of_ne_source
        D htK hx hxs,
    hpsStart ▸ hsNot, D.finite_rayTrace⟩

#print axioms exists_realLedger

end TwoPort

namespace Weak

variable {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {R : V → V → Prop}

private abbrev NativeWeb (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa : Cardinal.{u}) : DWeb V :=
  _root_.Erdos599.Blueprint.ColouredSafeShortcutGraph.imaginaryWeb Y kappa

/-- The exact native weak transaction, now retaining the real-edge and
pending-real-terminal ledger.  In the intended application `R` is adjacency
in the original graph, and `hpathsReal` follows because `T.paths` is a real
switch family before lifting to the imaginary web. -/
theorem exists_realLedger
    {Z : Set Gamma.DPath} {s t : V} {A : Occurrence Z s}
    (T : TouchedWeakSwitch A t)
    (hs : s ∉ Gamma.vertexSet Z) (ht : t ∉ Gamma.vertexSet Z)
    {W : Set (NativeWeb Gamma Y kappa).DPath}
    (hW : (NativeWeb Gamma Y kappa).IsWarp W)
    (hedge : (s, t) ∈ familyEdges W)
    (hconnector : T.connector.support ∩
      (NativeWeb Gamma Y kappa).vertexSet W ⊆ {s, t})
    (hcompanions : Disjoint (Gamma.vertexSet T.companions)
      ((NativeWeb Gamma Y kappa).vertexSet W))
    (hsReal : IsRealTerminal (Gamma := NativeWeb Gamma Y kappa) R W s)
    (hpathsReal : ∀ e ∈ familyEdges T.paths, R e.1 e.2)
    (hne : s ≠ t) :
    ∃ U : Set (NativeWeb Gamma Y kappa).DPath,
      (NativeWeb Gamma Y kappa).IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges T.paths ∧
      (NativeWeb Gamma Y kappa).initialSet U =
        (NativeWeb Gamma Y kappa).initialSet W ∪ Gamma.initialSet A.touchedReference ∧
      (NativeWeb Gamma Y kappa).terminalFrontier U =
        (NativeWeb Gamma Y kappa).terminalFrontier W ∪
          Gamma.terminalFrontier A.touchedReference ∧
      (NativeWeb Gamma Y kappa).vertexSet U =
        (((NativeWeb Gamma Y kappa).vertexSet W ∪ T.connector.support) ∪
          Gamma.vertexSet T.companions) ∧
      RealEdges (Gamma := NativeWeb Gamma Y kappa) R W ⊆
        RealEdges (Gamma := NativeWeb Gamma Y kappa) R U ∧
      (∀ x : V, IsRealTerminal (Gamma := NativeWeb Gamma Y kappa) R W x →
        x ≠ s → IsRealTerminal (Gamma := NativeWeb Gamma Y kappa) R U x) ∧
      ¬ IsRealTerminal (Gamma := NativeWeb Gamma Y kappa) R U s ∧
      (∀ r : Ray (NativeWeb Gamma Y kappa).graph, Sum.inr r ∈ U →
        ∃ r0 : Ray (NativeWeb Gamma Y kappa).graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet) := by
  let D := NativeWeb Gamma Y kappa
  obtain ⟨U, hU, hUI, hUT, hUV, hUE, htrace⟩ :=
    _root_.Erdos599.Blueprint.ColouredSafeShortcutGraph.exists_weakSubdivision_with_companions_exact
      T hs ht hW hedge hconnector hcompanions
  have hcut : ¬ R s t := cut_not_real hsReal hedge
  have hrealEdges : RealEdges (Gamma := D) R W ⊆ RealEdges (Gamma := D) R U := by
    rintro e ⟨heW, heR⟩
    refine ⟨?_, heR⟩
    rw [hUE]
    apply Or.inl
    refine ⟨heW, ?_⟩
    intro he
    have heq : e = (s, t) := Set.mem_singleton_iff.mp he
    subst e
    exact hcut heR
  have hterminal : ∀ x : V, IsRealTerminal (Gamma := D) R W x → x ≠ s →
      IsRealTerminal (Gamma := D) R U x := by
    intro x hx hxs
    refine ⟨?_, ?_⟩
    · rw [hUV]
      exact Or.inl (Or.inl hx.1)
    · rintro ⟨y, hyU, hRxy⟩
      rw [hUE] at hyU
      rcases hyU with hyW | hyT
      · exact hx.2 ⟨y, hyW.1, hRxy⟩
      · have hxT : x ∈ Gamma.vertexSet T.paths :=
          (familyEdges_subset_vertexSet_prod T.paths hyT).1
        obtain ⟨p, hpT, hxp⟩ := hxT
        by_cases hp : p = Sum.inl T.connector
        · subst p
          have hxPorts := hconnector ⟨hxp, hx.1⟩
          rcases Set.mem_insert_iff.mp hxPorts with hxeq | hxeq
          · exact hxs hxeq
          · have hxt : x = t := Set.mem_singleton_iff.mp hxeq
            subst x
            have htTerminal : t ∈ Gamma.terminalFrontier T.paths := by
              rw [T.terminals]
              exact Or.inr (Set.mem_singleton t)
            exact (Alternating.not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
              T.isWarp htTerminal) ⟨y, hyT⟩
        · have hxComp : x ∈ Gamma.vertexSet T.companions :=
            by
              change ∃ q ∈ T.companions, x ∈ q.support
              refine ⟨p, ⟨hpT, ?_⟩, hxp⟩
              simpa only [Set.mem_singleton_iff] using hp
          exact Set.disjoint_left.mp hcompanions hxComp hx.1
  have hconnectorEdges : T.connector.edgeSet ⊆ familyEdges U := by
    intro e he
    rw [hUE]
    exact Or.inr (Set.mem_iUnion.mpr ⟨(Sum.inl T.connector : Gamma.DPath),
      Set.mem_iUnion.mpr ⟨T.connector_mem, he⟩⟩)
  have hsNot : ¬ IsRealTerminal (Gamma := D) R U s := by
    intro hsU
    have hstartNeFinish : T.connector.start ≠ T.connector.finish := by
      simpa only [T.connector_start, T.connector_finish] using hne
    obtain ⟨y, hsy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        T.connector T.connector.start_mem_support hstartNeFinish
    apply hsU.2
    refine ⟨y, ?_, ?_⟩
    · simpa only [T.connector_start] using hconnectorEdges hsy
    · apply hpathsReal (s, y)
      exact Set.mem_iUnion.mpr ⟨(Sum.inl T.connector : Gamma.DPath),
        Set.mem_iUnion.mpr ⟨T.connector_mem, by
          change (s, y) ∈ T.connector.edgeSet
          simpa only [T.connector_start] using hsy⟩⟩
  exact ⟨U, hU, hUE, hUI, hUT, hUV, hrealEdges, hterminal, hsNot, htrace⟩

#print axioms exists_realLedger

end Weak

end Erdos599.ColouredSafeLocalTransactionRealLedger
