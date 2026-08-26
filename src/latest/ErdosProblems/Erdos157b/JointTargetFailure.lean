import ErdosProblems.Erdos157b.TargetFailure
import ErdosProblems.Erdos157b.MaskPointFailure
import ErdosProblems.Erdos157b.GrowthBounds
import ErdosProblems.Erdos157b.ConditionalDensity

/-! The unconditional one-target estimate, integrating the masks and label choices together. -/

namespace Erdos157.Binary

open Elementary Filter

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def extendLevelMasks {k : ℕ} (τ : LevelMasks K k) : MaskChoice K :=
  fun i => if hi : i < k then τ ⟨i, hi⟩ else 0

theorem extendLevelMasks_prefix {k : ℕ} (τ : LevelMasks K k) :
    (fun i : Fin k => extendLevelMasks K τ i) = τ := by
  funext i
  simp only [extendLevelMasks, dif_pos i.2]

theorem localValue_congr_masks (τ σ : MaskChoice K) (k : ℕ)
    (h : ∀ i : Fin k, τ i = σ i) (f : LevelLabel K k) (c : LocalChoice K k) :
    localValue K τ k f c = localValue K σ k f c := by
  unfold localValue
  congr 1
  apply congrArg MixedRadix.encode
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [h i]

theorem locallyRepresented_congr_masks (τ σ : MaskChoice K) (k : ℕ)
    (h : ∀ i : Fin k, τ i = σ i) (ω : LevelParameters K k) (m : ℕ) :
    LocallyRepresented K τ k ω m ↔ LocallyRepresented K σ k ω m := by
  constructor <;> rintro ⟨f₁, f₂, f₃, he⟩ <;> refine ⟨f₁, f₂, f₃, ?_⟩ <;>
    simpa only [localValue_congr_masks K τ σ k h] using he

noncomputable def JointTargetFailure (k m : ℕ)
    (x : LevelMasks K k × LevelParameters K k) : Prop :=
  ¬LocallyRepresented K (extendLevelMasks K x.1) k x.2 m

noncomputable def targetFailureBound (k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 4 / 1024) + Real.exp (-(2 : ℝ) ^ k)

theorem targetFailureBound_nonneg (k : ℕ) : 0 ≤ targetFailureBound k := by
  unfold targetFailureBound
  positivity

theorem eventually_joint_target_failure :
    ∀ᶠ k in atTop, ∀ m : ℕ, 6 * blockPlace CoefficientField 0 k ≤ m →
      m < 6 * blockPlace CoefficientField 0 (k + 1) →
      finiteDensity (JointTargetFailure CoefficientField k m) ≤ targetFailureBound k := by
  filter_upwards [eventually_topCapacity, eventually_coverage_trial_mass,
    eventually_maskTarget_failure CoefficientField, eventually_ge_atTop 400]
      with k hcap hmass hmask hk m hmlo hmhi
  obtain ⟨d, z, he, hzlo⟩ := exists_level_target_expansion CoefficientField k m (by omega)
  have hB := blockPlace_pos CoefficientField 0 k
  rw [blockPlace_snoc] at hmhi
  have hzhi : z ≤ 3 * Fintype.card CoefficientField ^ (3 * k) := by
    have hzR : z < 6 * blockRadix CoefficientField k := by nlinarith
    omega
  have hc (τ : LevelMasks CoefficientField k)
      (hhit : MaskTargetHit CoefficientField τ (targetMoments CoefficientField d)) :
      finiteDensity (fun ω : LevelParameters CoefficientField k =>
        ¬LocallyRepresented CoefficientField (extendLevelMasks CoefficientField τ) k ω m) ≤
          Real.exp (-(2 : ℝ) ^ k) := by
    have hh : MaskTargetHit CoefficientField
        (fun i => extendLevelMasks CoefficientField τ i) (targetMoments CoefficientField d) := by
      rwa [extendLevelMasks_prefix]
    rw [he]
    calc
      _ ≤ _ := target_failure_density CoefficientField (extendLevelMasks CoefficientField τ)
        k (by omega) d hh z (by omega) hzhi
      _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hmass)
  have hb := finiteDensity_prod_condition
    (fun τ => MaskTargetHit CoefficientField τ (targetMoments CoefficientField d))
    (fun τ ω => ¬LocallyRepresented CoefficientField (extendLevelMasks CoefficientField τ) k ω m)
    (Real.exp (-(2 : ℝ) ^ k)) (Real.exp_nonneg _) hc
  exact hb.trans (add_le_add (hmask (targetMoments CoefficientField d)) le_rfl)

end Erdos157.Binary
