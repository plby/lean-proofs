import Wikipedia.NoExoticSixSphere.SupportedRelativeCycleClass
import Wikipedia.NoExoticSixSphere.RelativeChainNeighborhood

/-!
# A zero local evaluation vanishes on a support neighborhood

The zero local class supplies a genuine ambient boundary witness.
Compactness of the complementary chain carrier preserves that witness
near the point. Thus every smaller support in that neighborhood has
zero restriction of the original class, not merely a prescribed value.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X] [T2Space X]

/-- Zero evaluation at a point gives zero restriction on all nearby smaller supports. -/
theorem exists_zero_restriction_neighborhood (K : Set X) (n : ℕ)
    (a : Homology A K n) (x : X) (hx : x ∈ K) (ha : evaluate A K x hx n a = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ (L : Set X) (hLK : L ⊆ K), L ⊆ U → restrict A hLK n a = 0 := by
  obtain ⟨c, hc, hca⟩ := RelativeCoefficients.exists_cycle_representative A Kᶜ n a
  change RelativeCoefficients.relativeClass A Kᶜ n c hc = a at hca
  rw [← hca] at ha ⊢
  have hs : {x} ⊆ K := singleton_subset_iff.mpr hx
  have hlocal : RelativeCoefficients.relativeClass A ({x}ᶜ : Set X) n c
      (relativeCycle_restrict A hs n c hc) = 0 :=
    (restrict_relativeClass A hs n c hc).symm.trans ha
  obtain ⟨b, hb⟩ := (RelativeCoefficients.relativeClass_eq_zero_iff
    A ({x}ᶜ : Set X) n c (relativeCycle_restrict A hs n c hc)).mp hlocal
  obtain ⟨U, hU, hxU, hzero⟩ := RelativeCoefficients.quotientMap_zero_neighborhood
    A {x} n _ hb
  refine ⟨U, hU, hxU (mem_singleton x), ?_⟩
  intro L hLK hLU
  rw [restrict_relativeClass]
  apply (RelativeCoefficients.relativeClass_eq_zero_iff A Lᶜ n c _).mpr
  exact ⟨b, hzero L hLU⟩

/-- A family of zero local values remains zero on an open neighborhood of that subset. -/
theorem exists_open_zero_evaluations {K L : Set X} (hKL : K ⊆ L) (n : ℕ)
    (a : Homology A L n) (ha : ∀ (x : X) (hx : x ∈ K), evaluate A L x (hKL hx) n a = 0) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ (x : X) (hx : x ∈ L), x ∈ U → evaluate A L x hx n a = 0 := by
  classical
  have hnear : ∀ x : K, ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧
      ∀ (T : Set X) (hTL : T ⊆ L), T ⊆ U → restrict A hTL n a = 0 :=
    fun x => exists_zero_restriction_neighborhood A L n a x (hKL x.property) (ha x x.property)
  choose U hU hxU hzero using hnear
  refine ⟨⋃ x : K, U x, isOpen_iUnion hU, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  · intro x hxL hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    exact hzero y {x} (singleton_subset_iff.mpr hxL) (singleton_subset_iff.mpr hy)

end NoExoticSixSphere.SupportedRelativeHomology
