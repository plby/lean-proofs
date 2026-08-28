import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransportChain

/-!
# Independence of finite chart subdivisions

Cutting a genuinely subordinate chain at any intermediate time factors its
actual transport. A chain contained in one chart agrees with the actual
single-chart integral, and therefore any two chains on the same curve have
the same scalar. No compatibility of transport is supplied as data.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} {A : TransitionData ComplexPlane₂ ι} [A.IsHolomorphic Iℂ]
    {γ : ℝ → ComplexPlane₂} (hγ : ContDiff ℝ ∞ γ)

namespace ChartChain

include hγ

/-- A chain which is wholly in one chart equals that chart's integral
transport, regardless of all the intermediate charts in the chain. -/
theorem scalar_eq_segment {a b : ℝ} {n : ℕ} (C : ChartChain A γ a b n)
    (i : ι) (hi : MapsTo γ (Icc a b) (A.baseSet i)) :
    C.scalar = segmentScalar A γ i a b := by
  induction C with
  | nil a =>
      exact (segmentScalar_self A γ i a (hi (left_mem_Icc.mpr le_rfl))).symm
  | @cons a d b n j had hj C ih =>
      have hib : MapsTo γ (Icc d b) (A.baseSet i) :=
        hi.mono (Icc_subset_Icc had le_rfl) Subset.rfl
      have hid : MapsTo γ (Icc a d) (A.baseSet i) :=
        hi.mono (Icc_subset_Icc le_rfl C.ordered) Subset.rfl
      rw [scalar_cons, ih hib, segmentScalar_chart_eq A γ hγ j i had hj hid,
        ← segmentScalar_comp A γ hγ i had C.ordered hi]

/-- Cutting an actual chart chain factors its scalar transport into two
actual chart chains. A cut inside a segment uses the proved integral law. -/
theorem exists_split {a b : ℝ} {n : ℕ} (C : ChartChain A γ a b n)
    (d : ℝ) (had : a ≤ d) (hdb : d ≤ b) :
    ∃ n₁ n₂ : ℕ, ∃ C₁ : ChartChain A γ a d n₁,
      ∃ C₂ : ChartChain A γ d b n₂, C.scalar = C₂.scalar * C₁.scalar := by
  induction C with
  | nil a =>
      have hd : d = a := le_antisymm hdb had
      subst d
      exact ⟨0, 0, .nil a, .nil a, by simp⟩
  | @cons a c b n i hac hi C ih =>
      by_cases hdc : d ≤ c
      · have hid : MapsTo γ (Icc a d) (A.baseSet i) :=
          hi.mono (Icc_subset_Icc le_rfl hdc) Subset.rfl
        have hdi : MapsTo γ (Icc d c) (A.baseSet i) :=
          hi.mono (Icc_subset_Icc had le_rfl) Subset.rfl
        refine ⟨1, n + 1, .cons i had hid (.nil d), .cons i hdc hdi C, ?_⟩
        simp only [scalar_cons, scalar_nil, one_mul]
        rw [segmentScalar_comp A γ hγ i had hdc hi]
        ring
      · obtain ⟨n₁, n₂, C₁, C₂, heq⟩ := ih (le_of_not_ge hdc) hdb
        refine ⟨n₁ + 1, n₂, .cons i hac hi C₁, C₂, ?_⟩
        simp only [scalar_cons]
        rw [heq]
        ring

/-- Subdivision and chart choices do not change the actual scalar transport
along a fixed curve. -/
theorem scalar_eq {a b : ℝ} {n m : ℕ} (C : ChartChain A γ a b n)
    (D : ChartChain A γ a b m) : C.scalar = D.scalar := by
  induction C generalizing m with
  | nil a => exact (D.scalar_eq_one_of_eq rfl).symm
  | @cons a d b n i had hi C ih =>
      obtain ⟨n₁, n₂, D₁, D₂, hD⟩ := D.exists_split hγ d had C.ordered
      rw [scalar_cons, hD, ih D₂, D₁.scalar_eq_segment hγ i hi]

end ChartChain

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
