import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceRecursion
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceCanonical

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Coherence of the source recursion

This module proves that a source-canonical trace is replayed by the stopped
source recursion when the recursion is anchored above the trace.  In
particular, the run below a node of the trace agrees with every earlier stage
of that trace.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TraceIteration

/-- A source-canonical prefix is replayed by the source recursion below any
candidate lying above the whole prefix. -/
theorem sourceRun_at_candidate
    {c : TraceColoring} {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (q : TraceCandidate c p) {eta : Ordinal} (heta : eta ≤ p.length) :
    sourceRun c q.value eta = (p.restrict eta heta).graph := by
  classical
  induction eta using Ordinal.limitRecOn with
  | zero =>
      rw [sourceRun_zero, TracePrefix.graph_restrict]
      ext z
      simp
  | add_one eta ih =>
      have hbase : eta ≤ p.length :=
        (Order.le_succ eta).trans heta
      have hi : eta < p.length :=
        (Order.lt_succ eta).trans_le heta
      let i : p.length.ToType := Ordinal.ToType.mk ⟨eta, hi⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply ⟨eta, hi⟩)
      have hbefore : p.before i = p.restrict eta hbase := by
        apply TracePrefix.graph_injective
        unfold TracePrefix.before
        rw [TracePrefix.graph_restrict, TracePrefix.graph_restrict]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [hiord]
      have hcanonicalAt :
          ∃ r : TraceCandidate c (p.restrict eta hbase),
            r.IsLeast ∧ r.value = p.node i := by
        exact hbefore ▸ hcanonical i
      rcases hcanonicalAt with ⟨r, hrleast, hrvalue⟩
      let qeta : TraceCandidate c (p.restrict eta hbase) := q.restrict hbase
      have hrq : r.value < qeta.value := by
        rw [TraceCandidate.restrict_value, hrvalue]
        exact q.above_prefix i
      let rstep : TraceCandidate c
          ((p.restrict eta hbase).atCandidate qeta) :=
        TraceCandidate.atCandidateOfLt (p.restrict eta hbase) qeta r hrq
      have hrstepLeast : rstep.IsLeast :=
        hrleast.atCandidateOfLt hrq
      have hrstepValue : rstep.value = p.node i := by
        rw [TraceCandidate.atCandidateOfLt_value, hrvalue]
      have hextendable : Nonempty (TraceCandidate c
          ((p.restrict eta hbase).atCandidate qeta)) := ⟨rstep⟩
      have hleastValue :
          (TraceCandidate.least hextendable).value = p.node i := by
        rw [← hrstepValue]
        exact (TraceCandidate.least_isLeast hextendable).value_eq hrstepLeast
      calc
        sourceRun c q.value (eta + 1) =
            sourceRun c q.value (Order.succ eta) := by
          rw [Order.succ_eq_add_one]
        _ = sourceStep c q.value (sourceRun c q.value eta) :=
          sourceRun_succ c q.value eta
        _ = (p.restrict (eta + 1) heta).graph := by
          rw [ih hbase]
          rw [← TraceCandidate.restrict_value q hbase]
          change sourceStep c qeta.value
              ((p.restrict eta hbase).atCandidate qeta).graph = _
          rw [sourceStep_graph_of_extendable c
            ((p.restrict eta hbase).atCandidate qeta) hextendable]
          rw [TracePrefix.graph_snoc, hleastValue]
          change (p.restrict eta hbase).graph ∪
              {((eta : Ordinal), p.node i)} = _
          have hsucc : Order.succ eta ≤ p.length := by
            simpa only [Order.succ_eq_add_one] using! heta
          simpa only [Order.succ_eq_add_one] using!
            (TracePrefix.graph_restrict_succ p hsucc).symm
  | limit eta hlimit ih =>
      rw [sourceRun_limit c q.value eta hlimit]
      rw [TracePrefix.graph_restrict]
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨beta, hz⟩
        rw [ih beta.1 beta.2 ((le_of_lt beta.2).trans heta)] at hz
        rw [TracePrefix.graph_restrict] at hz
        exact ⟨hz.1, hz.2.trans beta.2⟩
      · rintro ⟨hz, hzeta⟩
        let beta : Set.Iio eta :=
          ⟨Order.succ z.1, hlimit.succ_lt hzeta⟩
        refine ⟨beta, ?_⟩
        rw [ih beta.1 beta.2 ((le_of_lt beta.2).trans heta)]
        rw [TracePrefix.graph_restrict]
        exact ⟨hz, Order.lt_succ z.1⟩

/-- Below a node of a source-canonical trace, every earlier source-run stage
is the corresponding restriction of that trace. -/
theorem sourceRun_at_node_stage
    {c : TraceColoring} {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (xi : p.length.ToType)
    {theta : Ordinal} (htheta : theta ≤ xi.toOrd) :
    sourceRun c (p.node xi) theta =
      (p.restrict theta
        (htheta.trans (le_of_lt xi.toOrd.2))).graph := by
  rcases hcanonical xi with ⟨qxi, _, hqxiValue⟩
  rw [← hqxiValue]
  have hbeforeCanonical : (p.before xi).IsSourceCanonicalFor c := by
    exact hcanonical.restrict (le_of_lt xi.toOrd.2)
  have hrun := sourceRun_at_candidate hbeforeCanonical qxi htheta
  rw [hrun, TracePrefix.graph_restrict, TracePrefix.before,
    TracePrefix.graph_restrict, TracePrefix.graph_restrict]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hz, _⟩, hztheta⟩
    exact ⟨hz, hztheta⟩
  · rintro ⟨hz, hztheta⟩
    exact ⟨⟨hz, hztheta.trans_le htheta⟩, hztheta⟩

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
