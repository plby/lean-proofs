import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

/-!
# Chart-independent transport on one subordinate segment

The scalar is expressed in the actual preferred fibre coordinates at both
endpoints. The proved chart-change law makes it independent of the chart
containing the segment. Adjacent segments in one chart compose exactly.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationTransport

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

theorem transition_mul (i j k : ι) (x : ComplexPlane₂)
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) (hk : x ∈ A.baseSet k) :
    (A.transition j k x : ℂ) * (A.transition i j x : ℂ) = (A.transition i k x : ℂ) :=
  congrArg (fun u : ℂˣ => (u : ℂ)) (A.transition_comp i j k x ⟨⟨hi, hj⟩, hk⟩)

theorem transition_inverse_mul (i j : ι) (x : ComplexPlane₂)
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    (A.transition j i x : ℂ) * (A.transition i j x : ℂ) = 1 := by
  rw [transition_mul A i j i x hi hj hi, A.transition_self i x hi]
  rfl

/-- The actual transport scalar in the preferred fibre coordinates of the
scalar-core bundle at the two endpoints. -/
def segmentScalar (γ : ℝ → ComplexPlane₂) (i : ι) (a b : ℝ) : ℂ :=
  (A.transition i (A.indexAt (γ b)) (γ b) : ℂ) * connectionTransport A i γ a b *
    (A.transition (A.indexAt (γ a)) i (γ a) : ℂ)

theorem segmentScalar_ne_zero (γ : ℝ → ComplexPlane₂) (i : ι) (a b : ℝ) :
    segmentScalar A γ i a b ≠ 0 :=
  mul_ne_zero (mul_ne_zero (A.transition_ne_zero _ _ _)
    (connectionTransport_ne_zero A i γ a b)) (A.transition_ne_zero _ _ _)

theorem segmentScalar_self (γ : ℝ → ComplexPlane₂) (i : ι) (a : ℝ)
    (ha : γ a ∈ A.baseSet i) : segmentScalar A γ i a a = 1 := by
  unfold segmentScalar
  rw [connectionTransport_self, mul_one]
  exact transition_inverse_mul A (A.indexAt (γ a)) i (γ a) (A.mem_baseSet_at _) ha

variable [A.IsHolomorphic Iℂ]

/-- One subordinate segment has the same transport in any chart containing
it. This is a theorem of the constructed connection, not coherence data. -/
theorem segmentScalar_chart_eq (γ : ℝ → ComplexPlane₂) (hγ : ContDiff ℝ ∞ γ)
    (i j : ι) {a b : ℝ} (hab : a ≤ b)
    (hi : MapsTo γ (Icc a b) (A.baseSet i))
    (hj : MapsTo γ (Icc a b) (A.baseSet j)) :
    segmentScalar A γ i a b = segmentScalar A γ j a b := by
  have hia := hi (left_mem_Icc.mpr hab)
  have hja := hj (left_mem_Icc.mpr hab)
  have hib := hi (right_mem_Icc.mpr hab)
  have hjb := hj (right_mem_Icc.mpr hab)
  have hc : MapsTo γ (uIcc a b) (A.baseSet i ∩ A.baseSet j) := by
    rw [uIcc_of_le hab]
    exact fun t ht => ⟨hi ht, hj ht⟩
  have ha := transition_mul A (A.indexAt (γ a)) i j (γ a)
    (A.mem_baseSet_at _) hia hja
  have hb := transition_mul A i j (A.indexAt (γ b)) (γ b)
    hib hjb (A.mem_baseSet_at _)
  symm
  unfold segmentScalar
  rw [connectionTransport_chart_change A i j γ hγ hc]
  calc
    _ = ((A.transition j (A.indexAt (γ b)) (γ b) : ℂ) * (A.transition i j (γ b) : ℂ)) *
        connectionTransport A i γ a b *
          ((A.transition i j (γ a) : ℂ)⁻¹ * (A.transition (A.indexAt (γ a)) j (γ a) : ℂ)) := by ring
    _ = _ := by
      rw [hb, ← ha, ← mul_assoc (A.transition i j (γ a) : ℂ)⁻¹,
        inv_mul_cancel₀ (A.transition_ne_zero i j (γ a)), one_mul]

/-- Splitting a subordinate segment does not change its actual transport. -/
theorem segmentScalar_comp (γ : ℝ → ComplexPlane₂) (hγ : ContDiff ℝ ∞ γ)
    (i : ι) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hchart : MapsTo γ (Icc a c) (A.baseSet i)) :
    segmentScalar A γ i a c = segmentScalar A γ i b c * segmentScalar A γ i a b := by
  have hb : γ b ∈ A.baseSet i := hchart ⟨hab, hbc⟩
  have hab' : MapsTo γ (uIcc a b) (A.baseSet i) := by
    rw [uIcc_of_le hab]
    exact hchart.mono (Icc_subset_Icc le_rfl hbc) Subset.rfl
  have hbc' : MapsTo γ (uIcc b c) (A.baseSet i) := by
    rw [uIcc_of_le hbc]
    exact hchart.mono (Icc_subset_Icc hab le_rfl) Subset.rfl
  have hc := transition_inverse_mul A i (A.indexAt (γ b)) (γ b) hb (A.mem_baseSet_at _)
  unfold segmentScalar
  rw [connectionTransport_comp A i γ hγ a b c hab' hbc']
  calc
    _ = (A.transition i (A.indexAt (γ c)) (γ c) : ℂ) * connectionTransport A i γ b c *
        ((A.transition (A.indexAt (γ b)) i (γ b) : ℂ) *
          (A.transition i (A.indexAt (γ b)) (γ b) : ℂ)) *
            connectionTransport A i γ a b * (A.transition (A.indexAt (γ a)) i (γ a) : ℂ) := by
      rw [hc]
      ring
    _ = _ := by ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalTransport
