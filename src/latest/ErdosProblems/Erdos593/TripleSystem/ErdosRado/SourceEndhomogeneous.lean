import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceTerminal

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TracePrefix

private theorem tracePair_congr {x y x' y' : TraceCarrier}
    (hx : x = x') (hy : y = y') (hxy : x ≠ y) (hx'y' : x' ≠ y') :
    tracePair x y hxy = tracePair x' y' hx'y' := by
  subst x'
  subst y'
  rfl

/-- Source canonicity forces every earlier trace node to see the same color
at a later node as it sees at the anchor. -/
theorem IsSourceCanonicalFor.endhomogeneousTo
    {c : TraceColoring} {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) : p.EndhomogeneousTo c := by
  intro xi zeta hxiz
  rcases hp zeta with ⟨q, _hq, hqvalue⟩
  have hord : (xi.toOrd : Ordinal) < (zeta.toOrd : Ordinal) :=
    ((Ordinal.ToType.mk (o := p.length)).symm.lt_iff_lt).mpr hxiz
  let xi' : (zeta.toOrd : Ordinal).ToType :=
    Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal), Set.mem_Iio.mpr hord⟩
  have hindex : p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp zeta.toOrd.2)) xi' = xi := by
    apply (Ordinal.ToType.mk (o := p.length)).symm.injective
    apply Subtype.ext
    rw [p.restrictIndex_toOrd]
    unfold xi'
    exact congrArg Subtype.val
      ((Ordinal.ToType.mk (o := (zeta.toOrd : Ordinal))).symm_apply_apply
        ⟨(xi.toOrd : Ordinal), Set.mem_Iio.mpr hord⟩)
  have hnode : (p.before zeta).node xi' = p.node xi := by
    change p.node (p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp zeta.toOrd.2)) xi') = p.node xi
    rw [hindex]
  calc
    c (tracePair (p.node xi) (p.node zeta)
        (ne_of_lt (p.node_lt_node hxiz))) =
        c (tracePair ((p.before zeta).node xi') q.value
          (ne_of_lt (q.above_prefix xi'))) := by
            apply congrArg c
            exact tracePair_congr hnode.symm hqvalue.symm _ _
    _ = c (tracePair ((p.before zeta).node xi') a
          (ne_of_lt ((p.before zeta).node_lt_anchor xi'))) := q.agrees xi'
    _ = c (tracePair (p.node xi) a
          (ne_of_lt (p.node_lt_anchor xi))) := by
            apply congrArg c
            exact tracePair_congr hnode rfl _ _

end TracePrefix

namespace TraceIteration

theorem terminalPrefix_endhomogeneous (c : TraceColoring) (a : TraceCarrier) :
    (terminalPrefix c a).EndhomogeneousTo c :=
  (terminalPrefix_canonical c a).endhomogeneousTo

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
