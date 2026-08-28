import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedPullback
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedTrivialization
import Wikipedia.HopfProblem.HolomorphicCharacterBundlePowers
import Wikipedia.HopfProblem.HolomorphicCharacterBundleFinite

/-!
# Triviality and exact order of holomorphic character bundles

For a compact connected complex covering manifold, the actual associated
quotient admits a holomorphic fibrewise-linear product trivialization exactly
when the character is trivial. Equivalently, it has a nowhere-zero holomorphic
section. The same theorem for the associated character powers gives their
exact period, not merely an upper bound.

The final specialization constructs the covering from an actual finite free
holomorphic action; it does not assume a quotient covering or a bundle
triviality theorem. Identification of a particular canonical or normal bundle
with a character bundle is a separate geometric assertion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

section CoveringAction

variable {G A B E : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  [IsManifold (modelWithCornersSelf ℂ E) ω A]
  [CompactSpace A] [ConnectedSpace A]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

include hG

/-- Lemma 5.7(ii)'s character obstruction for actual analytic linear
trivializations of the associated quotient. -/
theorem analyticTrivialization_iff_character_eq_one :
    Nonempty (AnalyticAssociatedTrivialization (E := E) hq χ) ↔ χ = 1 := by
  constructor
  · rintro ⟨e⟩
    apply (exists_holomorphic_nowhereZero_section_iff_character_eq_one hq χ hG).mp
    exact ⟨e.unitSection hq χ, e.unitSection_isHolomorphic hq χ,
      e.unitSection_nowhereZero hq χ⟩
  · rintro rfl
    exact ⟨trivialCharacterTrivialization hq hG⟩

theorem analyticTrivialization_iff_nowhereZero_section :
    Nonempty (AnalyticAssociatedTrivialization (E := E) hq χ) ↔
      ∃ s : Section hq χ, s.IsHolomorphic (E := E) hq χ ∧ s.NowhereZero hq χ :=
  (analyticTrivialization_iff_character_eq_one hq χ hG).trans
    (exists_holomorphic_nowhereZero_section_iff_character_eq_one hq χ hG).symm

/-- The actual associated bundle of `χ^n` is trivial exactly at multiples of
the character's order, including `n=0` and the infinite-order convention. -/
theorem power_analyticTrivialization_iff_orderOf_dvd (n : ℕ) :
    Nonempty (AnalyticAssociatedTrivialization (E := E) hq (χ ^ n)) ↔ orderOf χ ∣ n :=
  (analyticTrivialization_iff_character_eq_one hq (χ ^ n) hG).trans
    orderOf_dvd_iff_pow_eq_one.symm

theorem zpower_analyticTrivialization_iff_orderOf_dvd (n : ℤ) :
    Nonempty (AnalyticAssociatedTrivialization (E := E) hq (χ ^ n)) ↔
      (orderOf χ : ℤ) ∣ n :=
  (analyticTrivialization_iff_character_eq_one hq (χ ^ n) hG).trans
    orderOf_dvd_iff_zpow_eq_one.symm

/-- For a finite acting group, the character order is precisely the least
positive trivial associated power, not just an annihilating exponent. -/
theorem orderOf_isLeast_trivial_power [Finite G] :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty (AnalyticAssociatedTrivialization (E := E) hq (χ ^ n))} (orderOf χ) := by
  refine ⟨⟨orderOf_character_pos χ,
    (power_analyticTrivialization_iff_orderOf_dvd hq χ hG _).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1
    ((power_analyticTrivialization_iff_orderOf_dvd hq χ hG n).mp hn.2)

theorem card_power_analyticTrivialization :
    Nonempty (AnalyticAssociatedTrivialization (E := E) hq (χ ^ Nat.card G)) :=
  (power_analyticTrivialization_iff_orderOf_dvd hq χ hG _).mpr
    (orderOf_character_dvd_card χ)

end CoveringAction

section FiniteAction

variable {G A E : Type*} [Group G] [Finite G] [MulAction G A]
  [TopologicalSpace A] [T2Space A] [ContinuousConstSMul G A] [IsCancelSMul G A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  [IsManifold (modelWithCornersSelf ℂ E) ω A] [CompactSpace A] [ConnectedSpace A]
  (χ : G →* ℂˣ)
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

include hG

/-- The same result on the actual orbit quotient of a finite free action;
the required covering and analytic atlases are constructed, not assumed. -/
theorem finite_quotient_analyticTrivialization_iff_character_eq_one :
    Nonempty (AnalyticAssociatedTrivialization (E := E)
      (FiniteQuotient.project_isQuotientCoveringMap G A) χ) ↔ χ = 1 :=
  analyticTrivialization_iff_character_eq_one
    (FiniteQuotient.project_isQuotientCoveringMap G A) χ hG

theorem finite_quotient_power_analyticTrivialization_iff_orderOf_dvd (n : ℕ) :
    Nonempty (AnalyticAssociatedTrivialization (E := E)
      (FiniteQuotient.project_isQuotientCoveringMap G A) (χ ^ n)) ↔ orderOf χ ∣ n :=
  power_analyticTrivialization_iff_orderOf_dvd
    (FiniteQuotient.project_isQuotientCoveringMap G A) χ hG n

theorem finite_quotient_orderOf_isLeast_trivial_power :
    IsLeast {n : ℕ | 0 < n ∧ Nonempty (AnalyticAssociatedTrivialization (E := E)
      (FiniteQuotient.project_isQuotientCoveringMap G A) (χ ^ n))} (orderOf χ) :=
  orderOf_isLeast_trivial_power (FiniteQuotient.project_isQuotientCoveringMap G A) χ hG

end FiniteAction

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
