import Wikipedia.SmoothSixDPoincare.OpenGluing
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Bases

/-!
# Separation and countability for the actual open gluing

The quotient is always an open quotient and preserves second countability.
For Hausdorff patches, it is Hausdorff exactly when the prescribed overlap
has closed graph in the product of the two whole patches. The closed-graph
condition is explicit and is not asserted for arbitrary open gluings.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y)

theorem quotient_isOpenMap : IsOpenMap (Quotient.mk (setoid e)) :=
  isOpenMap_sum.mpr ⟨(left_isOpenEmbedding e).isOpenMap,
    (right_isOpenEmbedding e).isOpenMap⟩

theorem quotient_isOpenQuotientMap : IsOpenQuotientMap (Quotient.mk (setoid e)) :=
  ⟨Quotient.mk_surjective, continuous_quotient_mk', quotient_isOpenMap e⟩

instance secondCountableTopology [SecondCountableTopology X] [SecondCountableTopology Y] :
    SecondCountableTopology (Space e) :=
  TopologicalSpace.Quotient.secondCountableTopology (quotient_isOpenMap e)

private theorem isClosed_sum_prod_iff {Z : Type*} [TopologicalSpace Z]
    (s : Set ((X ⊕ Y) × Z)) :
    IsClosed s ↔ IsClosed {p : X × Z | (Sum.inl p.1, p.2) ∈ s} ∧
      IsClosed {p : Y × Z | (Sum.inr p.1, p.2) ∈ s} := by
  rw [← Homeomorph.sumProdDistrib.symm.isClosed_preimage, isClosed_sum_iff]
  rfl

private theorem isClosed_prod_sum_iff {Z : Type*} [TopologicalSpace Z]
    (s : Set (Z × (X ⊕ Y))) :
    IsClosed s ↔ IsClosed {p : Z × X | (p.1, Sum.inl p.2) ∈ s} ∧
      IsClosed {p : Z × Y | (p.1, Sum.inr p.2) ∈ s} := by
  rw [← Homeomorph.prodSumDistrib.symm.isClosed_preimage, isClosed_sum_iff]
  rfl

theorem t2Space_iff_closed_graph [T2Space X] [T2Space Y] :
    T2Space (Space e) ↔ IsClosed {p : X × Y | p.1 ∈ e.source ∧ e p.1 = p.2} := by
  rw [t2Space_iff_of_isOpenQuotientMap (quotient_isOpenQuotientMap e)]
  have hrel : {q : (X ⊕ Y) × (X ⊕ Y) |
      Quotient.mk (setoid e) q.1 = Quotient.mk (setoid e) q.2} =
      {q | Rel e q.1 q.2} := by
    ext q
    exact Quotient.eq
  rw [hrel, isClosed_sum_prod_iff, isClosed_prod_sum_iff, isClosed_prod_sum_iff]
  change (IsClosed {p : X × X | p.1 = p.2} ∧
      IsClosed {p : X × Y | p.1 ∈ e.source ∧ e p.1 = p.2}) ∧
      (IsClosed {p : Y × X | p.1 ∈ e.target ∧ e.symm p.1 = p.2} ∧
        IsClosed {p : Y × Y | p.1 = p.2}) ↔ _
  constructor
  · exact fun h => h.1.2
  · intro h
    refine ⟨⟨isClosed_eq continuous_fst continuous_snd, h⟩,
      ?_, isClosed_eq continuous_fst continuous_snd⟩
    have heq : {p : Y × X | p.1 ∈ e.target ∧ e.symm p.1 = p.2} =
        Prod.swap ⁻¹' {p : X × Y | p.1 ∈ e.source ∧ e p.1 = p.2} := by
      ext p
      change (p.1 ∈ e.target ∧ e.symm p.1 = p.2) ↔
        p.2 ∈ e.source ∧ e p.2 = p.1
      rw [← right_eq_left, ← left_eq_right]
      exact eq_comm
    rw [heq]
    exact h.preimage continuous_swap

end Wikipedia.SmoothSixDPoincare.OpenGluing
