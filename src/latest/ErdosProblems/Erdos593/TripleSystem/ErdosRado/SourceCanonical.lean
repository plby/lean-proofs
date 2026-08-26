import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TraceGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Source-canonical trace prefixes

A prefix is source-canonical when every node was chosen by the same local
rule: at coordinate `ξ`, take the least candidate available after the nodes
at earlier coordinates.  The invariant records a least-candidate witness at
each coordinate.  Candidate proof objects need not be equal, but two least
candidates have the same underlying value.

The closure lemmas below show that source-canonicality survives restriction,
one least-candidate extension, and coherent limits.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TracePrefix

/-- The strict initial segment of `p` before the coordinate `ξ`. -/
noncomputable def before {a : TraceCarrier} (p : TracePrefix a)
    (ξ : p.length.ToType) : TracePrefix a :=
  p.restrict ξ.toOrd (le_of_lt (Set.mem_Iio.mp ξ.toOrd.2))

@[simp]
theorem before_length {a : TraceCarrier} (p : TracePrefix a)
    (ξ : p.length.ToType) : (p.before ξ).length = ξ.toOrd :=
  rfl

/-- Every recorded node was chosen as a least candidate for the prefix
strictly before its coordinate. -/
def IsSourceCanonicalFor {a : TraceCarrier} (p : TracePrefix a)
    (c : TraceColoring) : Prop :=
  ∀ ξ : p.length.ToType,
    ∃ q : TraceCandidate c (p.before ξ),
      q.IsLeast ∧ q.value = p.node ξ

theorem isSourceCanonicalFor_empty (c : TraceColoring) (a : TraceCarrier) :
    (empty a).IsSourceCanonicalFor c := by
  intro ξ
  have hξ : (ξ.toOrd : Ordinal) < 0 := Set.mem_Iio.mp ξ.toOrd.2
  exact (not_lt_of_ge bot_le hξ).elim

private theorem before_restrict_eq {a : TraceCarrier} (p : TracePrefix a)
    {η : Ordinal} (hη : η ≤ p.length) (ξ : η.ToType) :
    (p.restrict η hη).before ξ = p.before (p.restrictIndex hη ξ) := by
  apply graph_injective
  unfold before
  rw [graph_restrict, graph_restrict, graph_restrict]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hord : ((p.restrictIndex hη ξ).toOrd : Ordinal) =
      (ξ.toOrd : Ordinal) := p.restrictIndex_toOrd hη ξ
  constructor
  · rintro ⟨⟨hz, hzη⟩, hzξ⟩
    rw [hord]
    exact ⟨hz, hzξ⟩
  · rintro ⟨hz, hzξ⟩
    have hξη : (ξ.toOrd : Ordinal) < η := Set.mem_Iio.mp ξ.toOrd.2
    rw [hord] at hzξ
    have hzη : z.1 < η := hzξ.trans hξη
    exact ⟨⟨hz, hzη⟩, hzξ⟩

theorem IsSourceCanonicalFor.restrict {c : TraceColoring}
    {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) {η : Ordinal} (hη : η ≤ p.length) :
    (p.restrict η hη).IsSourceCanonicalFor c := by
  intro ξ
  rcases hp (p.restrictIndex hη ξ) with ⟨q, hq, hvalue⟩
  rw [before_restrict_eq p hη ξ]
  exact ⟨q, hq, by simpa only [restrict_node] using! hvalue⟩

/-- Restricting the larger member of an initial-segment pair recovers the
smaller prefix. -/
theorem restrict_eq_of_isInitialSegment {a : TraceCarrier}
    (p q : TracePrefix a) (hseg : p.IsInitialSegment q) :
    q.restrict p.length hseg.choose = p := by
  apply graph_injective
  rw [graph_restrict]
  ext z
  constructor
  · rintro ⟨⟨ζ, rfl⟩, hζ⟩
    let ξ : p.length.ToType :=
      Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩
    refine ⟨ξ, ?_⟩
    apply Prod.ext
    · simp [ξ, Ordinal.ToType.toOrd]
    · have hnode := hseg.choose_spec ξ
      simpa [ξ, liftIndex, TracePrefix.restrictIndex] using! hnode
  · rintro ⟨ξ, rfl⟩
    refine ⟨?_, Set.mem_setOf.mpr (Set.mem_Iio.mp ξ.toOrd.2)⟩
    refine ⟨liftIndex hseg.choose ξ, ?_⟩
    apply Prod.ext
    · exact (liftIndex_toOrd hseg.choose ξ).symm
    · exact (hseg.choose_spec ξ).symm

private theorem before_snoc_of_lt_eq {c : TraceColoring}
    {a : TraceCarrier} (p : TracePrefix a) (q : TraceCandidate c p)
    (ζ : (p.snoc q).length.ToType) (hζ : (ζ.toOrd : Ordinal) < p.length) :
    (p.snoc q).before ζ =
      p.before (Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩) := by
  apply graph_injective
  unfold before
  rw [graph_restrict, graph_restrict, graph_snoc]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz | rfl, hzζ⟩
    · refine ⟨hz, ?_⟩
      simpa [Ordinal.ToType.toOrd] using! hzζ
    · exact (not_lt_of_ge (le_of_lt hζ) hzζ).elim
  · rintro ⟨hz, hzζ⟩
    refine ⟨Or.inl hz, ?_⟩
    simpa [Ordinal.ToType.toOrd] using! hzζ

private theorem before_snoc_of_not_lt_eq {c : TraceColoring}
    {a : TraceCarrier} (p : TracePrefix a) (q : TraceCandidate c p)
    (ζ : (p.snoc q).length.ToType)
    (hζ : ¬ (ζ.toOrd : Ordinal) < p.length) :
    (p.snoc q).before ζ = p := by
  have hbound : (ζ.toOrd : Ordinal) < Order.succ p.length := by
    have h := Set.mem_Iio.mp ζ.toOrd.2
    change (ζ.toOrd : Ordinal) < Order.succ p.length at h
    exact h
  have heq : (ζ.toOrd : Ordinal) = p.length :=
    le_antisymm (Order.lt_succ_iff.mp hbound) (le_of_not_gt hζ)
  apply graph_injective
  unfold before
  rw [graph_restrict, graph_snoc]
  rw [heq]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz | rfl, hzlt⟩
    · exact hz
    · exact (lt_irrefl p.length hzlt).elim
  · intro hz
    refine ⟨Or.inl hz, ?_⟩
    rcases hz with ⟨ξ, rfl⟩
    exact Set.mem_Iio.mp ξ.toOrd.2

theorem IsSourceCanonicalFor.snoc {c : TraceColoring}
    {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) (q : TraceCandidate c p)
    (hq : q.IsLeast) : (p.snoc q).IsSourceCanonicalFor c := by
  intro ζ
  rcases p.snoc_index_lt_or_eq_last ζ with hζ | rfl
  · let ξ : p.length.ToType :=
      Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩
    rcases hp ξ with ⟨r, hr, hvalue⟩
    rw [before_snoc_of_lt_eq p q ζ hζ]
    refine ⟨r, hr, ?_⟩
    rw [p.snoc_node_of_lt q ζ hζ]
    exact hvalue
  · have hnot : ¬
        (((p.snocLast : (p.snoc q).length.ToType).toOrd : Ordinal)) <
          p.length := by
      intro h
      have h' : ((p.snocLast).toOrd : Ordinal) < p.length := h
      rw [p.snocLast_toOrd] at h'
      exact (lt_irrefl p.length h').elim
    rw [before_snoc_of_not_lt_eq p q p.snocLast hnot]
    exact ⟨q, hq, (p.snoc_node_last q).symm⟩

/-- A coherent limit of source-canonical prefixes is source-canonical. -/
theorem IsSourceCanonicalFor.limitPrefix {c : TraceColoring}
    {a : TraceCarrier} {o : Ordinal} (F : LimitChain a o)
    (ho : Order.IsSuccLimit o) (hheight : o ≤ TraceHeight)
    (hcanonical : ∀ η, (F.stage η).IsSourceCanonicalFor c) :
    (F.limitPrefix ho hheight).IsSourceCanonicalFor c := by
  intro ξ
  let η := F.nextStage ho ξ
  let ζ := F.diagonalIndex ho ξ
  rcases hcanonical η ζ with ⟨q, hq, hvalue⟩
  have hseg := F.stage_isInitialSegment_limitPrefix ho hheight η
  have hstage :
      (F.limitPrefix ho hheight).restrict (F.stage η).length hseg.choose =
        F.stage η :=
    restrict_eq_of_isInitialSegment (F.stage η)
      (F.limitPrefix ho hheight) hseg
  have hstagegraph := congrArg TracePrefix.graph hstage
  rw [graph_restrict] at hstagegraph
  have hbefore : (F.stage η).before ζ =
      (F.limitPrefix ho hheight).before ξ := by
    apply graph_injective
    unfold before
    rw [graph_restrict, graph_restrict, ← hstagegraph]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    have hord : (ζ.toOrd : Ordinal) = ξ.toOrd :=
      F.diagonalIndex_toOrd ho ξ
    constructor
    · rintro ⟨⟨hz, hzη⟩, hzζ⟩
      exact ⟨hz, hzζ.trans_eq hord⟩
    · rintro ⟨hz, hzξ⟩
      refine ⟨⟨hz, ?_⟩, ?_⟩
      · rw [F.length_eq, F.nextStage_toOrd]
        exact hzξ.trans (Order.lt_succ _)
      · exact hzξ.trans_eq hord.symm
  rw [← hbefore]
  refine ⟨q, hq, ?_⟩
  change q.value = F.limitNode ho ξ
  simpa [η, ζ, LimitChain.limitNode] using! hvalue

end TracePrefix
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
