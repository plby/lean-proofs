import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceRunInvariant
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceCoherence

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TracePrefix

/-- The part of a prefix strictly before a node, reanchored at that node. -/
noncomputable def beforeAtNode {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) : TracePrefix (p.node xi) :=
  (p.before xi).reanchor (p.node xi) (by
    intro eta
    change (xi.toOrd : Ordinal).ToType at eta
    apply p.node_lt_node
    have hetaXi : (eta.toOrd : Ordinal) < xi.toOrd :=
      Set.mem_Iio.mp eta.toOrd.2
    apply ((Ordinal.ToType.mk (o := p.length)).symm.lt_iff_lt).mp
    change ((p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp xi.toOrd.2)) eta).toOrd : Ordinal) < xi.toOrd
    rw [p.restrictIndex_toOrd]
    exact hetaXi)

@[simp]
theorem beforeAtNode_length {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) : (p.beforeAtNode xi).length = xi.toOrd :=
  rfl

@[simp]
theorem graph_beforeAtNode {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) :
    (p.beforeAtNode xi).graph = (p.before xi).graph :=
  rfl

end TracePrefix

namespace TraceIteration

/-- The source-run witness at the full construction height. -/
noncomputable def terminalPrefix (c : TraceColoring) (a : TraceCarrier) :
    TracePrefix a :=
  Classical.choose (sourceRun_spec c a TraceHeight le_rfl)

@[simp]
theorem terminalPrefix_graph (c : TraceColoring) (a : TraceCarrier) :
    sourceRun.{0} c a TraceHeight = (terminalPrefix c a).graph :=
  (Classical.choose_spec (sourceRun_spec c a TraceHeight le_rfl)).1

theorem terminalPrefix_canonical (c : TraceColoring) (a : TraceCarrier) :
    (terminalPrefix c a).IsSourceCanonicalFor c :=
  (Classical.choose_spec (sourceRun_spec c a TraceHeight le_rfl)).2.1

theorem terminalPrefix_length_le (c : TraceColoring) (a : TraceCarrier) :
    (terminalPrefix c a).length ≤ TraceHeight :=
  (Classical.choose_spec (sourceRun_spec c a TraceHeight le_rfl)).2.2.1

theorem terminalPrefix_status (c : TraceColoring) (a : TraceCarrier) :
    (terminalPrefix c a).length = TraceHeight ∨
      ((terminalPrefix c a).length < TraceHeight ∧
        ¬ Nonempty (TraceCandidate c (terminalPrefix c a))) :=
  (Classical.choose_spec (sourceRun_spec c a TraceHeight le_rfl)).2.2.2

theorem terminalPrefix_stopped (c : TraceColoring) (a : TraceCarrier) :
    ¬ Nonempty (TraceCandidate c (terminalPrefix c a)) := by
  rcases terminalPrefix_status c a with hfull | ⟨_, hstop⟩
  · exact TraceCandidate.not_nonempty_of_length_eq_traceHeight
      (terminalPrefix c a) hfull
  · exact hstop

/-- A source-canonical trace, viewed below one of its own nodes, has already
stopped by the full construction height. -/
theorem sourceRun_at_node_traceHeight
    {c : TraceColoring} {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) (xi : p.length.ToType) :
    sourceRun.{0} c (p.node xi) TraceHeight = (p.beforeAtNode xi).graph := by
  rcases hp xi with ⟨q, hqleast, hqvalue⟩
  let q' : TraceCandidate c (p.before xi) := {
    live := q.live
    value := p.node xi
    lt_anchor := by simpa only [← hqvalue] using! q.lt_anchor
    above_prefix := by
      intro eta
      simpa only [← hqvalue] using! q.above_prefix eta
    agrees := by
      intro eta
      simpa only [← hqvalue] using! q.agrees eta
  }
  have hq'least : q'.IsLeast := by
    intro r
    change p.node xi ≤ r.value
    rw [← hqvalue]
    exact hqleast r
  have hstopped :
      ¬ Nonempty (TraceCandidate c (p.beforeAtNode xi)) := by
    have hreanchor : p.beforeAtNode xi = (p.before xi).atCandidate q' := by
      apply TracePrefix.graph_injective
      rfl
    rw [hreanchor]
    exact TraceCandidate.not_nonempty_at_isLeast hq'least
  have hstage :
      sourceRun.{0} c (p.node xi) xi.toOrd = (p.beforeAtNode xi).graph := by
    rw [TracePrefix.graph_beforeAtNode]
    exact sourceRun_at_node_stage hp xi (le_refl xi.toOrd)
  exact sourceRun_eq_graph_of_stopped c (p.beforeAtNode xi) hstopped hstage
    (θ := TraceHeight)
    ((le_of_lt (Set.mem_Iio.mp xi.toOrd.2)).trans p.length_le)

@[simp]
theorem terminalPrefix_at_node (c : TraceColoring) (a : TraceCarrier)
    (xi : (terminalPrefix c a).length.ToType) :
    terminalPrefix c ((terminalPrefix c a).node xi) =
      (terminalPrefix c a).beforeAtNode xi := by
  apply TracePrefix.graph_injective
  rw [← terminalPrefix_graph]
  exact sourceRun_at_node_traceHeight (terminalPrefix_canonical c a) xi

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
