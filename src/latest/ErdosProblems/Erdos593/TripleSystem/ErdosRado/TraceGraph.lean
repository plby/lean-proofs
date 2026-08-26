import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TraceLimit
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TransfiniteIteration

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Graph representation of trace prefixes

The source recursion is most naturally iterated on sets of coordinate–value pairs,
whereas the local trace API uses dependent ordinal-indexed prefixes.  This
module is the small conversion layer between those representations.  It makes
no candidate-existence or global-coherence assertion.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TracePrefix

/-- The graph of a trace prefix, recording each ordinal coordinate and its
carrier value. -/
def graph {a : TraceCarrier} (p : TracePrefix a) :
    TraceIteration.TraceStageSet :=
  {z | ∃ ξ : p.length.ToType,
    z = ((ξ.toOrd : Ordinal), p.node ξ)}

@[simp]
theorem graph_empty (a : TraceCarrier) :
    (empty a).graph = ∅ := by
  ext z
  constructor
  · rintro ⟨ξ, _⟩
    have hξ : (ξ.toOrd : Ordinal) < 0 := Set.mem_Iio.mp ξ.toOrd.2
    exact (not_lt_of_ge bot_le hξ).elim
  · intro hz
    exact hz.elim

/-- Restricting a prefix cuts its graph off at the new ordinal length. -/
theorem graph_restrict {a : TraceCarrier} (p : TracePrefix a)
    {η : Ordinal} (hη : η ≤ p.length) :
    (p.restrict η hη).graph = p.graph ∩ {z | z.1 < η} := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨?_, Set.mem_setOf.mpr (Set.mem_Iio.mp ξ.toOrd.2)⟩
    refine ⟨p.restrictIndex hη ξ, ?_⟩
    apply Prod.ext
    · exact (p.restrictIndex_toOrd hη ξ).symm
    · rfl
  · rintro ⟨⟨ξ, rfl⟩, hξη⟩
    let ζ : η.ToType := Ordinal.ToType.mk ⟨ξ.toOrd, hξη⟩
    have hζOrd : (ζ.toOrd : Ordinal) = ξ.toOrd := by
      simp [ζ, Ordinal.ToType.toOrd]
    have hindex : p.restrictIndex hη ζ = ξ := by
      apply (Ordinal.ToType.mk (o := p.length)).symm.injective
      apply Subtype.ext
      rw [p.restrictIndex_toOrd hη]
      exact hζOrd
    refine ⟨ζ, ?_⟩
    apply Prod.ext
    · exact hζOrd.symm
    · simp only [restrict_node, hindex]

/-- Restricting through a successor coordinate consists of the preceding
restriction together with the value at that coordinate. -/
theorem graph_restrict_succ {a : TraceCarrier} (p : TracePrefix a)
    {eta : Ordinal} (heta : Order.succ eta ≤ p.length) :
    (p.restrict (Order.succ eta) heta).graph =
      (p.restrict eta ((Order.le_succ eta).trans heta)).graph ∪
        {((eta : Ordinal), p.node (Ordinal.ToType.mk
          ⟨eta, (Order.lt_succ eta).trans_le heta⟩))} := by
  rw [graph_restrict, graph_restrict]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hzsucc⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hzsucc) with hlt | heq
    · exact Or.inl ⟨hz, hlt⟩
    · right
      rcases hz with ⟨xi, rfl⟩
      let i : p.length.ToType := Ordinal.ToType.mk
        ⟨eta, (Order.lt_succ eta).trans_le heta⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply
            ⟨eta, (Order.lt_succ eta).trans_le heta⟩)
      have hxiord : (xi.toOrd : Ordinal) = eta := heq
      have hxi : xi = i := by
        apply (Ordinal.ToType.mk (o := p.length)).symm.injective
        apply Subtype.ext
        exact hxiord.trans hiord.symm
      subst xi
      apply Prod.ext
      · exact hiord
      · rfl
  · rintro (⟨hz, hlt⟩ | rfl)
    · exact ⟨hz, hlt.trans (Order.lt_succ eta)⟩
    · let i : p.length.ToType := Ordinal.ToType.mk
        ⟨eta, (Order.lt_succ eta).trans_le heta⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply
            ⟨eta, (Order.lt_succ eta).trans_le heta⟩)
      refine ⟨⟨i, ?_⟩, Order.lt_succ eta⟩
      apply Prod.ext
      · exact hiord.symm
      · rfl

/-- Appending a candidate adds exactly the stage at the old prefix length. -/
theorem graph_snoc {c : TraceColoring} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) :
    (p.snoc q).graph = p.graph ∪ {((p.length : Ordinal), q.value)} := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    by_cases hξ : (ξ.toOrd : Ordinal) < p.length
    · left
      refine ⟨Ordinal.ToType.mk ⟨ξ.toOrd, hξ⟩, ?_⟩
      apply Prod.ext
      · simp [Ordinal.ToType.toOrd]
      · exact p.snoc_node_of_lt q ξ hξ
    · right
      have hle : (ξ.toOrd : Ordinal) ≤ p.length :=
        Order.lt_succ_iff.mp ξ.toOrd.2
      have heq : (ξ.toOrd : Ordinal) = p.length :=
        le_antisymm hle (le_of_not_gt hξ)
      simp only [Set.mem_singleton_iff]
      apply Prod.ext
      · exact heq
      · exact p.snoc_node_of_not_lt q ξ hξ
  · rintro (hz | hz)
    · rcases hz with ⟨ξ, rfl⟩
      refine ⟨p.snocLift ξ, ?_⟩
      apply Prod.ext
      · exact (p.snocLift_toOrd ξ).symm
      · exact (p.snoc_node_lift q ξ).symm
    · rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨p.snocLast, ?_⟩
      apply Prod.ext
      · exact (p.snocLast_toOrd).symm
      · exact (p.snoc_node_last q).symm

/-- The graph of a coherent diagonal limit is exactly the union of the
graphs supplied at its proper stages. -/
theorem LimitChain.graph_limitPrefix {a : TraceCarrier} {o : Ordinal}
    (F : LimitChain a o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) :
    (F.limitPrefix ho hheight).graph =
      ⋃ η : o.ToType, (F.stage η).graph := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    rw [Set.mem_iUnion]
    refine ⟨F.nextStage ho ξ, ?_⟩
    refine ⟨F.diagonalIndex ho ξ, ?_⟩
    apply Prod.ext
    · exact (F.diagonalIndex_toOrd ho ξ).symm
    · rfl
  · rw [Set.mem_iUnion]
    rintro ⟨η, ξ, rfl⟩
    rcases F.stage_isInitialSegment_limitPrefix ho hheight η with
      ⟨hlen, hnode⟩
    refine ⟨liftIndex hlen ξ, ?_⟩
    apply Prod.ext
    · exact (liftIndex_toOrd hlen ξ).symm
    · exact (hnode ξ).symm

end TracePrefix

namespace TraceIteration

/-- The length represented by a stage graph is the supremum of the successors
of its coordinates.  The successor is essential: the raw supremum would give
the wrong answer for successor-length prefixes. -/
noncomputable def historyLength (s : TraceStageSet) : Ordinal :=
  sSup ((fun z : TraceStage => z.1 + 1) '' s)

/-- The graph representation remembers the exact length of a prefix. -/
@[simp]
theorem historyLength_graph {a : TraceCarrier} (p : TracePrefix a) :
    historyLength p.graph = p.length := by
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨z, ⟨ξ, rfl⟩, rfl⟩
    exact Order.succ_le_iff.mpr (Set.mem_Iio.mp ξ.toOrd.2)
  · refine le_of_forall_lt fun β hβ => ?_
    let ξ : p.length.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
    have hb : BddAbove ((fun z : TraceStage => z.1 + 1) '' p.graph) := by
      refine ⟨p.length, ?_⟩
      rintro _ ⟨z, ⟨ζ, rfl⟩, rfl⟩
      exact Order.succ_le_iff.mpr (Set.mem_Iio.mp ζ.toOrd.2)
    let z : TraceStage := (β, p.node ξ)
    have hz : z ∈ p.graph := by
      refine ⟨ξ, ?_⟩
      simp [z, ξ, Ordinal.ToType.toOrd]
    exact (lt_add_one β).trans_le (le_csSup hb ⟨z, hz, rfl⟩)

end TraceIteration

namespace TracePrefix

/-- The graph representation determines a trace prefix uniquely. -/
theorem graph_injective {a : TraceCarrier} :
    Function.Injective (@graph a) := by
  intro p q hgraph
  have hlength : p.length = q.length := by
    have h := congrArg TraceIteration.historyLength hgraph
    simpa using! h
  cases p with
  | mk plen ple pnode panchor pmono =>
    cases q with
    | mk qlen qle qnode qanchor qmono =>
      dsimp at hlength
      subst qlen
      congr 1
      apply funext
      intro xi
      have hz : (@graph a (TracePrefix.mk plen ple pnode panchor pmono))
          ((xi.toOrd : Ordinal), pnode xi) := Exists.intro xi rfl
      rw [hgraph] at hz
      cases hz with
      | intro zeta hzeta =>
        have hxizeta : xi = zeta := by
          apply (Ordinal.ToType.mk (o := plen)).symm.injective
          apply Subtype.ext
          exact congrArg Prod.fst hzeta
        subst zeta
        exact congrArg Prod.snd hzeta

/-- Inclusion between prefix graphs is exactly the usual initial-segment
relation.  This is the bridge used to recover coherent prefix chains from the
monotonicity of a set-valued transfinite run. -/
theorem isInitialSegment_of_graph_subset {a : TraceCarrier}
    {p q : TracePrefix a} (hgraph : p.graph ⊆ q.graph) :
    p.IsInitialSegment q := by
  have hlength : p.length ≤ q.length := by
    refine le_of_forall_lt fun β hβ ↦ ?_
    let ξ : p.length.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
    have hz : ((β : Ordinal), p.node ξ) ∈ p.graph := by
      refine ⟨ξ, ?_⟩
      apply Prod.ext
      · simp [ξ, Ordinal.ToType.toOrd]
      · rfl
    rcases hgraph hz with ⟨ζ, hζ⟩
    have hβζ : β = (ζ.toOrd : Ordinal) := congrArg Prod.fst hζ
    rw [hβζ]
    exact Set.mem_Iio.mp ζ.toOrd.2
  refine ⟨hlength, fun ξ ↦ ?_⟩
  have hz : ((ξ.toOrd : Ordinal), p.node ξ) ∈ p.graph := ⟨ξ, rfl⟩
  rcases hgraph hz with ⟨ζ, hζ⟩
  have hindex : liftIndex hlength ξ = ζ := by
    apply (Ordinal.ToType.mk (o := q.length)).symm.injective
    apply Subtype.ext
    rw [liftIndex_toOrd]
    exact congrArg Prod.fst hζ
  rw [hindex]
  exact (congrArg Prod.snd hζ).symm

theorem graph_subset_of_isInitialSegment {a : TraceCarrier}
    {p q : TracePrefix a} (hpq : p.IsInitialSegment q) :
    p.graph ⊆ q.graph := by
  rcases hpq with ⟨hlength, hnode⟩
  rintro z ⟨ξ, rfl⟩
  refine ⟨liftIndex hlength ξ, ?_⟩
  apply Prod.ext
  · exact (liftIndex_toOrd hlength ξ).symm
  · exact (hnode ξ).symm

theorem graph_subset_iff_isInitialSegment {a : TraceCarrier}
    {p q : TracePrefix a} :
    p.graph ⊆ q.graph ↔ p.IsInitialSegment q :=
  ⟨isInitialSegment_of_graph_subset, graph_subset_of_isInitialSegment⟩

end TracePrefix

end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
