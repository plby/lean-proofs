import Wikipedia.HopfProblem.HolomorphicCharacterBundle

/-!
# The character obstruction for the actual cocycle bundle

The independently constructed character `VectorBundleCore` is analytically
trivial exactly when its associated quotient is. Here the implication needed
for geometric canonical and normal bundles is proved through actual sections
and the analytic identification of the two total spaces.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.BundleCore

open HolomorphicCharacterBundle

variable {G A B : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

/-- Send a genuine section of the cocycle bundle to a genuine section of
the actual associated quotient. -/
def sectionToAssociated (s : ∀ b, (AssociatedCore.data hq χ).core.Fiber b) : Section hq χ where
  toFun b := AssociatedCore.toAssociated hq χ ⟨b, s b⟩
  projection_toFun _ := AssociatedCore.projection_toAssociated hq χ _

theorem zeroSection_eq_toAssociated (b : B) :
    zeroSection hq χ b = AssociatedCore.toAssociated hq χ ⟨b, 0⟩ := by
  calc
    zeroSection hq χ b = zeroSection hq χ
        (q (AssociatedCore.lift hq b b)) := congrArg (zeroSection hq χ)
          (AssociatedCore.lift_project hq b (AssociatedCore.mem_baseSet hq b)).symm
    _ = associatedMap χ (AssociatedCore.lift hq b b, 0) := zeroSection_apply_project hq χ _
    _ = AssociatedCore.toAssociated hq χ ⟨b, 0⟩ := rfl

theorem sectionToAssociated_nowhereZero
    (s : ∀ b, (AssociatedCore.data hq χ).core.Fiber b) (hs : ∀ b, s b ≠ 0) :
    (sectionToAssociated hq χ s).NowhereZero hq χ := by
  intro b hb
  apply hs b
  have he : AssociatedCore.toAssociated hq χ ⟨b, s b⟩ =
      AssociatedCore.toAssociated hq χ ⟨b, 0⟩ := hb.trans (zeroSection_eq_toAssociated hq χ b)
  have hp := AssociatedCore.toAssociated_injective hq χ he
  exact congrArg (fun p : (AssociatedCore.data hq χ).core.TotalSpace => id (α := ℂ) p.2) hp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E A]
  [IsManifold (modelWithCornersSelf ℂ E) ω A]
  (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (fun a : A => g • a))

local notation "IA" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ (E × ℂ)

include hG

theorem sectionToAssociated_holomorphic
    (s : ∀ b, (AssociatedCore.data hq χ).core.Fiber b)
    (hs : letI := CoveringQuotient.chartedSpace (E := E) hq
      ContMDiff IA ((IA).prod I₁) ω
        (fun b => (⟨b, s b⟩ : (AssociatedCore.data hq χ).core.TotalSpace))) :
    (sectionToAssociated hq χ s).IsHolomorphic (E := E) hq χ := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  let := associatedChartedSpace (E := E) hq χ
  exact (AssociatedCore.toAssociated_holomorphic hq χ hG).comp hs

variable [CompactSpace A] [ConnectedSpace A]

/-- Triviality here means an actual base-preserving fibre-linear analytic
product diffeomorphism of the `VectorBundleCore` total space. -/
theorem characterCore_analyticTrivialization_iff :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    Nonempty ((AssociatedCore.data hq χ).AnalyticTrivialization IA) ↔ χ = 1 := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  constructor
  · rintro ⟨e⟩
    apply (exists_holomorphic_nowhereZero_section_iff_character_eq_one hq χ hG).mp
    exact ⟨sectionToAssociated hq χ e.frame,
      sectionToAssociated_holomorphic hq χ hG e.frame e.frame_holomorphic,
      sectionToAssociated_nowhereZero hq χ e.frame e.frame_ne_zero⟩
  · rintro rfl
    have hcriterion :=
      TransitionData.exists_compatible_nonzero_localCoefficients_iff_analyticTrivialization
        (AssociatedCore.data hq (1 : G →* ℂˣ)) IA
    apply hcriterion.mp
    refine ⟨fun _ _ => 1, ?_, fun _ => contMDiffOn_const, fun _ _ _ => one_ne_zero⟩
    intro i j x hx
    simp [AssociatedCore.data_transition]

theorem characterCore_power_analyticTrivialization_iff (n : ℕ) :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    Nonempty ((AssociatedCore.data hq (χ ^ n)).AnalyticTrivialization IA) ↔ orderOf χ ∣ n :=
  (characterCore_analyticTrivialization_iff hq (χ ^ n) hG).trans
    orderOf_dvd_iff_pow_eq_one.symm

theorem characterCore_orderOf_isLeast [Finite G] :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((AssociatedCore.data hq (χ ^ n)).AnalyticTrivialization IA)} (orderOf χ) := by
  let := CoveringQuotient.chartedSpace (E := E) hq
  refine ⟨⟨orderOf_character_pos χ,
    (characterCore_power_analyticTrivialization_iff hq χ hG _).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((characterCore_power_analyticTrivialization_iff hq χ hG n).mp hn.2)

end Wikipedia.HopfProblem.Elliptic.BundleCore
