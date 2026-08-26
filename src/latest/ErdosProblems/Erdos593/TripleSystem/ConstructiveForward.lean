import ErdosProblems.Erdos593.TripleSystem.Constructive
import ErdosProblems.Erdos593.TripleSystem.DisjointUnionForward
import ErdosProblems.Erdos593.TripleSystem.ForwardExpansion
import ErdosProblems.Erdos593.TripleSystem.IsomorphIntrinsic
import ErdosProblems.Erdos593.TripleSystem.OnePointAmalgamationIntrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Constructive systems satisfy the intrinsic conditions

This is the structural-induction endpoint for the forward half of the finite
classification.
-/

namespace Erdos593

universe w

namespace TripleSystem

/-- Every system in the finite constructive class is linear, has an incident
Levi bridge at every hyperedge-node, and has only even Berge cycles. -/
theorem Constructible.intrinsic {V E : Type w}
    {F : TripleSystem V E} (h : Constructible F) : F.Intrinsic := by
  induction h with
  | ofEdgeless V =>
      exact edgeless_intrinsic V
  | ofExpansion G hG =>
      exact privateVertexExpansion_intrinsic G hG
  | disjointUnion hF hG ihF ihG =>
      exact disjointUnion_intrinsic _ _ ihF ihG
  | amalgam h₀ h₁ r₀ r₁ ih₀ ih₁ =>
      exact OnePointAmalgamation.amalgam_intrinsic _ _ r₀ r₁ ih₀ ih₁
  | ofIso hF f ihF =>
      exact (f.intrinsic_iff).mp ihF

end TripleSystem
end Erdos593
