import ErdosProblems.Erdos593.TripleSystem.ErdosRado.CanonicalLevelCode
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceTerminal
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceEndhomogeneous

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TraceIteration

/-- The coordinate of a terminal prefix represented by an ordinal below its
length. -/
noncomputable def terminalIndex (c : TraceColoring) (a : TraceCarrier)
    {eta : Ordinal} (heta : eta < (terminalPrefix c a).length) :
    (terminalPrefix c a).length.ToType :=
  Ordinal.ToType.mk ⟨eta, Set.mem_Iio.mpr heta⟩

@[simp]
theorem terminalIndex_toOrd (c : TraceColoring) (a : TraceCarrier)
    {eta : Ordinal} (heta : eta < (terminalPrefix c a).length) :
    ((terminalIndex c a heta).toOrd : Ordinal) = eta := by
  simp [terminalIndex]

/-- The coherent trace system obtained by taking the terminal source run at
every anchor. -/
noncomputable def sourceCoherentTraceSystem (c : TraceColoring) :
    CoherentTraceSystem c where
  height a := (terminalPrefix c a).length
  height_le a := (terminalPrefix c a).length_le
  node a eta heta := (terminalPrefix c a).node (terminalIndex c a heta)
  node_lt_anchor a eta heta :=
    (terminalPrefix c a).node_lt_anchor (terminalIndex c a heta)
  node_strict a eta zeta heta hzeta hetazeta := by
    apply (terminalPrefix c a).node_lt_node
    simpa [terminalIndex] using! hetazeta
  coherent_height a eta heta := by
    have hprefix := terminalPrefix_at_node c a (terminalIndex c a heta)
    have hlength := congrArg TracePrefix.length hprefix
    simpa only [TracePrefix.beforeAtNode_length, terminalIndex_toOrd] using! hlength
  coherent_prefix a eta zeta heta hzetaChild hzetaParent := by
    let xi := terminalIndex c a heta
    have hprefix := terminalPrefix_at_node c a xi
    let child := terminalPrefix c ((terminalPrefix c a).node xi)
    let childIndex := terminalIndex c ((terminalPrefix c a).node xi) hzetaChild
    have hmem : ((zeta : Ordinal), child.node childIndex) ∈ child.graph := by
      refine ⟨childIndex, ?_⟩
      apply Prod.ext
      · exact (terminalIndex_toOrd c ((terminalPrefix c a).node xi)
          hzetaChild).symm
      · rfl
    have hgraph : child.graph = ((terminalPrefix c a).before xi).graph := by
      rw [show child = terminalPrefix c ((terminalPrefix c a).node xi) from rfl,
        hprefix, TracePrefix.graph_beforeAtNode]
    rw [hgraph] at hmem
    rcases hmem with ⟨k, hk⟩
    have hkord : (k.toOrd : Ordinal) = zeta :=
      (congrArg Prod.fst hk).symm
    change child.node childIndex =
      (terminalPrefix c a).node (terminalIndex c a hzetaParent)
    calc
      child.node childIndex = ((terminalPrefix c a).before xi).node k :=
        congrArg Prod.snd hk
      _ = (terminalPrefix c a).node (terminalIndex c a hzetaParent) := by
        change (terminalPrefix c a).node
            ((terminalPrefix c a).restrictIndex (le_of_lt xi.toOrd.2) k) = _
        apply congrArg (terminalPrefix c a).node
        apply (Ordinal.ToType.mk
          (o := (terminalPrefix c a).length)).symm.injective
        apply Subtype.ext
        rw [(terminalPrefix c a).restrictIndex_toOrd,
          terminalIndex_toOrd]
        exact hkord

@[simp]
theorem sourceCoherentTraceSystem_height (c : TraceColoring) (a : TraceCarrier) :
    (sourceCoherentTraceSystem c).height a = (terminalPrefix c a).length :=
  rfl

/-- The prefix supplied by the packaged system is the terminal source prefix. -/
@[simp]
theorem sourceCoherentTraceSystem_tracePrefix
    (c : TraceColoring) (a : TraceCarrier) :
    (sourceCoherentTraceSystem c).tracePrefix a = terminalPrefix c a := by
  apply TracePrefix.graph_injective
  ext z
  constructor
  · rintro ⟨xi, rfl⟩
    refine ⟨xi, ?_⟩
    apply Prod.ext
    · rfl
    · apply congrArg (terminalPrefix c a).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a).length)).symm.injective
      apply Subtype.ext
      exact terminalIndex_toOrd c a (Set.mem_Iio.mp xi.toOrd.2)
  · rintro ⟨xi, rfl⟩
    refine ⟨xi, ?_⟩
    apply Prod.ext
    · rfl
    · apply congrArg (terminalPrefix c a).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a).length)).symm.injective
      apply Subtype.ext
      exact (terminalIndex_toOrd c a (Set.mem_Iio.mp xi.toOrd.2)).symm

/-- The packaged terminal source system is endhomogeneous. -/
theorem sourceCoherentTraceSystem_isEndhomogeneous (c : TraceColoring) :
    (sourceCoherentTraceSystem c).IsEndhomogeneous := by
  intro a eta zeta heta hzeta hetazeta
  let xi := terminalIndex c a heta
  let kappa := terminalIndex c a hzeta
  have hxikappa : xi < kappa := by
    simpa [xi, kappa, terminalIndex] using! hetazeta
  have hend := terminalPrefix_endhomogeneous c a hxikappa
  simpa only [sourceCoherentTraceSystem, xi, kappa] using! hend

/-- On a supplied level, the system's level prefix is the terminal source
prefix at that endpoint. -/
@[simp]
theorem sourceCoherentTraceSystem_levelTracePrefix
    (c : TraceColoring) (rho : Ordinal)
    (a : (sourceCoherentTraceSystem c).level rho) :
    (sourceCoherentTraceSystem c).levelTracePrefix rho a =
      terminalPrefix c a.1 := by
  have hrho : (terminalPrefix c a.1).length = rho := a.2
  apply TracePrefix.graph_injective
  ext z
  constructor
  · rintro ⟨xi, rfl⟩
    let xi' : (terminalPrefix c a.1).length.ToType :=
      Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal), by
        rw [hrho]
        exact Set.mem_Iio.mp xi.toOrd.2⟩
    have hxi' : (xi'.toOrd : Ordinal) = xi.toOrd := by
      exact congrArg Subtype.val
        ((Ordinal.ToType.mk
          (o := (terminalPrefix c a.1).length)).symm_apply_apply _)
    refine ⟨xi', ?_⟩
    apply Prod.ext
    · exact hxi'.symm
    · apply congrArg (terminalPrefix c a.1).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a.1).length)).symm.injective
      apply Subtype.ext
      rw [terminalIndex_toOrd]
      exact hxi'.symm
  · rintro ⟨xi, rfl⟩
    let xi' : rho.ToType := Ordinal.ToType.mk
      ⟨(xi.toOrd : Ordinal), by
        exact (Set.mem_Iio.mp xi.toOrd.2).trans_le (le_of_eq hrho)⟩
    have hxi' : (xi'.toOrd : Ordinal) = xi.toOrd := by
      exact congrArg Subtype.val
        ((Ordinal.ToType.mk (o := rho)).symm_apply_apply _)
    refine ⟨xi', ?_⟩
    apply Prod.ext
    · exact hxi'.symm
    · apply congrArg (terminalPrefix c a.1).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a.1).length)).symm.injective
      apply Subtype.ext
      rw [terminalIndex_toOrd]
      exact hxi'.symm

/-- Every level prefix in the packaged source system is genuinely stopped. -/
theorem sourceCoherentTraceSystem_stopped
    (c : TraceColoring) (rho : Ordinal)
    (a : (sourceCoherentTraceSystem c).level rho) :
    ¬ Nonempty
      (TraceCandidate c
        ((sourceCoherentTraceSystem c).levelTracePrefix rho a)) := by
  rw [sourceCoherentTraceSystem_levelTracePrefix]
  exact terminalPrefix_stopped c a.1

/-- Every coloring admits a stopped coherent endhomogeneous trace system. -/
theorem stoppedCoherentTraceSystemsForEveryColoring :
    ∀ c : TraceColoring,
      ∃ T : CoherentTraceSystem c, T.IsEndhomogeneous ∧
        ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
          ¬ Nonempty
            (TraceCandidate c (T.levelTracePrefix rho a)) := by
  intro c
  refine ⟨sourceCoherentTraceSystem c,
    sourceCoherentTraceSystem_isEndhomogeneous c, ?_⟩
  intro rho a _hrho
  exact sourceCoherentTraceSystem_stopped c rho a

end TraceIteration

end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
