import Wikipedia.NoExoticSixSphere.CoefficientChainCarrierMap
import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives

/-!
# Persistence of relative chain vanishing on a support neighborhood

If a native chain vanishes relative to the complement of `K`, its
subspace preimage has a compact carrier disjoint from `K`. The complement
of that compact carrier is an open neighborhood of `K` on every subset
of which the same original chain still vanishes relatively.
-/

noncomputable section

open CategoryTheory Set

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X] [T2Space X]

/-- A relative zero-chain witness persists on a neighborhood of its support. -/
theorem quotientMap_zero_neighborhood (K : Set X) (n : ℕ)
    (c : CoefficientChains.Chains A X n) (hc : quotientMap A Kᶜ n c = 0) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ L : Set X, L ⊆ U → quotientMap A Lᶜ n c = 0 := by
  obtain ⟨b, hb⟩ := (quotientMap_eq_zero_iff A Kᶜ n c).mp hc
  obtain ⟨D, hD, hDK, d, hd⟩ :=
    CoefficientChains.exists_compactCarrier_subspace A Kᶜ n b
  refine ⟨Dᶜ, hD.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hxD
    exact hDK hxD hx
  · intro L hL
    have hDL : D ⊆ Lᶜ := fun x hxD hxL => hL hxL hxD
    apply (quotientMap_eq_zero_iff A Lᶜ n c).mpr
    exact CoefficientChains.inclusion_range_mono A hDL n ⟨d, hd.trans hb⟩

end NoExoticSixSphere.RelativeCoefficients
