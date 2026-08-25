import StackExchange.Puzzling139335.HalfTurnRemainder.InvariantHole
import StackExchange.Puzzling139335.JordanTransport

/-!
# Half-turn transport of bounded complementary components

A half-turn preserving a closed connected set containing its center cannot
fix a bounded complementary component. Its image is therefore a distinct
bounded complementary component.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

/-- Bounded complementary components occur in distinct half-turn pairs. -/
theorem exists_distinct_bounded_component_of_pointReflection
    {K : Set Plane} {c x : Plane} (hKclosed : IsClosed K) (hKconn : IsConnected K)
    (hcK : c ∈ K) (hsym : AffineIsometryEquiv.pointReflection ℝ c '' K = K)
    (hxK : x ∉ K) (hbounded : Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    ∃ y, y ∉ K ∧ Bornology.IsBounded (connectedComponentIn Kᶜ y) ∧
      connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ y := by
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  have heK : e '' K = K := hsym
  have hcomponent : e '' connectedComponentIn Kᶜ x =
      connectedComponentIn Kᶜ (e x) := by
    rw [e.image_connectedComponentIn hxK, e.image_compl, heK]
  have hyK : e x ∉ K := by
    intro hy
    rw [← heK] at hy
    obtain ⟨z, hz, hzx⟩ := hy
    exact hxK (e.injective hzx ▸ hz)
  refine ⟨e x, hyK, ?_, ?_⟩
  · rw [← hcomponent]
    exact (planeHomeomorph_isBounded_image e).2 hbounded
  · intro heq
    have hfixed : AffineIsometryEquiv.pointReflection ℝ c ''
        connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ x := by
      change e '' connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ x
      exact hcomponent.trans heq.symm
    exact not_isBounded_connectedComponentIn_compl_of_pointReflection
      hKclosed hKconn hcK hxK hfixed hbounded

end Puzzling139335.HalfTurnRemainder
