import ErdosProblems.Erdos593.TripleSystem.Intrinsic
import ErdosProblems.Erdos593.TripleSystem.Isomorph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Isomorphism invariance of the intrinsic conditions

The finite reconstruction is naturally obtained only up to simultaneous
vertex and edge relabelling.  This file packages the corresponding Levi-graph
isomorphism and proves that each intrinsic condition is invariant.
-/

namespace Erdos593

universe u v u' v'

namespace TripleSystem
namespace Iso

variable {V : Type u} {E : Type v}
variable {V' : Type u'} {E' : Type v'}
variable {F : TripleSystem V E} {F' : TripleSystem V' E'}

/-- A triple-system isomorphism induces the canonical isomorphism of Levi
graphs, with point-nodes sent to point-nodes and edge-nodes to edge-nodes. -/
-- ARISTOTLE_ISO_TARGET I1
def leviIso (f : Iso F F') : F.levi ≃g F'.levi where
  toEquiv := Equiv.sumCongr f.vertexEquiv f.edgeEquiv
  map_rel_iff' := by
    rintro (x | e) (y | d) <;> simp [f.map_inc_iff]

/-- Linearity is invariant under simultaneous vertex and edge relabelling. -/
-- ARISTOTLE_ISO_TARGET I2
theorem linear_iff (f : Iso F F') : F.Linear ↔ F'.Linear := by
  constructor
  · intro h e' d' x' y' hed hx_e hx_d hy_e hy_d
    let e := f.edgeEquiv.symm e'
    let d := f.edgeEquiv.symm d'
    let x := f.vertexEquiv.symm x'
    let y := f.vertexEquiv.symm y'
    have hed' : e ≠ d := by
      intro heq
      apply hed
      simpa [e, d] using! congrArg f.edgeEquiv heq
    have hxy : x = y := h hed'
      ((f.map_inc_iff x e).mpr (by simpa [x, e] using! hx_e))
      ((f.map_inc_iff x d).mpr (by simpa [x, d] using! hx_d))
      ((f.map_inc_iff y e).mpr (by simpa [y, e] using! hy_e))
      ((f.map_inc_iff y d).mpr (by simpa [y, d] using! hy_d))
    simpa [x, y] using! congrArg f.vertexEquiv hxy
  · intro h e d x y hed hx_e hx_d hy_e hy_d
    have hed' : f.edgeEquiv e ≠ f.edgeEquiv d := f.edgeEquiv.injective.ne hed
    exact f.vertexEquiv.injective <| h hed'
      ((f.map_inc_iff x e).mp hx_e) ((f.map_inc_iff x d).mp hx_d)
      ((f.map_inc_iff y e).mp hy_e) ((f.map_inc_iff y d).mp hy_d)

private theorem isBridge_iff_of_iso {A B : Type*}
    {P : _root_.SimpleGraph A} {Q : _root_.SimpleGraph B}
    (g : P ≃g Q) (a b : A) :
    P.IsBridge s(a, b) ↔ Q.IsBridge s(g a, g b) := by
  let gd : P.deleteEdges {s(a, b)} ≃g
      Q.deleteEdges {s(g a, g b)} :=
    { toEquiv := g.toEquiv
      map_rel_iff' := by
        intro x y
        simp [g.map_adj_iff] }
  change (¬(P.deleteEdges {s(a, b)}).Reachable a b) ↔
    ¬(Q.deleteEdges {s(g a, g b)}).Reachable (g a) (g b)
  exact not_congr gd.reachable_iff.symm

/-- The incident-Levi-bridge condition is invariant under isomorphism. -/
-- ARISTOTLE_ISO_TARGET I3
theorem bridgeAtEveryEdge_iff (f : Iso F F') :
    F.BridgeAtEveryEdge ↔ F'.BridgeAtEveryEdge := by
  let g := leviIso f
  constructor
  · intro h e'
    obtain ⟨x, hx⟩ := h (f.edgeEquiv.symm e')
    refine ⟨f.vertexEquiv x, ?_⟩
    rcases hx with ⟨hadj, hbridge⟩
    constructor
    · simpa [g, leviIso] using! g.map_mem_edgeSet_iff.mpr hadj
    · simpa [g, leviIso] using!
        (isBridge_iff_of_iso g (Sum.inl x)
          (Sum.inr (f.edgeEquiv.symm e'))).mp hbridge
  · intro h e
    obtain ⟨x', hx⟩ := h (f.edgeEquiv e)
    refine ⟨f.vertexEquiv.symm x', ?_⟩
    rcases hx with ⟨hadj, hbridge⟩
    constructor
    · have hm := g.symm.map_mem_edgeSet_iff.mpr hadj
      simpa [g, leviIso] using! hm
    · have hb := (isBridge_iff_of_iso g.symm (Sum.inl x')
          (Sum.inr (f.edgeEquiv e))).mp hbridge
      simpa [g, leviIso] using! hb

/-- Divisibility by four of all Levi-cycle lengths is invariant under
isomorphism. -/
-- ARISTOTLE_ISO_TARGET I4
theorem evenBergeCycles_iff (f : Iso F F') :
    F.EvenBergeCycles ↔ F'.EvenBergeCycles := by
  let g := leviIso f
  constructor
  · intro h z c hc
    let d := c.map g.symm.toHom
    have hd : d.IsCycle := hc.map g.symm.injective
    have hdiv := h d hd
    simpa [d, _root_.SimpleGraph.Walk.length_map] using! hdiv
  · intro h z c hc
    let d := c.map g.toHom
    have hd : d.IsCycle := hc.map g.injective
    have hdiv := h d hd
    simpa [d, _root_.SimpleGraph.Walk.length_map] using! hdiv

/-- The full intrinsic predicate is invariant under triple-system
isomorphism. -/
-- ARISTOTLE_ISO_TARGET I5
theorem intrinsic_iff (f : Iso F F') : F.Intrinsic ↔ F'.Intrinsic := by
  simp only [Intrinsic, linear_iff f, bridgeAtEveryEdge_iff f,
    evenBergeCycles_iff f]

end Iso
end TripleSystem
end Erdos593
