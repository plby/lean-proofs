import ErdosProblems.Erdos157b.MaskTrialFamilies

/-! A uniform failure bound for one prescribed logarithm and pair of tag moments. -/

namespace Erdos157.Binary

open Erdos157.Elementary

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem trial_failure_density_le {k h n : ℕ} {z : MaskTarget K k}
    (T : MaskTrialFamily K z h n) (hhk : h ≤ k) (hn : 0 < n) (ε : ℝ)
    (hd : ∀ u : LogVector K h,
      ε ≤ finiteDensity (fun v => GoodLogVector K k (joinLogVectors K hhk u v))) :
    finiteDensity (fun τ : LevelMasks K k => ∀ j, ¬ GoodLogVector K k (trialLogVector K T τ j)) ≤
      Real.exp (-(n : ℝ) * ε) := by
  classical
  let X (i : Fin k) := TagField i → LogDigit K i
  let p (i : Fin k) := i.1 < h
  let e := Equiv.piEquivPiSubtypeProd p X
  apply finiteDensity_split_le p
  intro a
  let j₀ : Fin n := ⟨0, hn⟩
  let u : LogVector K h := fun i =>
    z.logarithm ⟨i.1, lt_of_lt_of_le i.2 hhk⟩ -
      Masks.maskSum (T.triple ⟨i.1, lt_of_lt_of_le i.2 hhk⟩ j₀)
        (a ⟨⟨i.1, lt_of_lt_of_le i.2 hhk⟩, i.2⟩)
  let c : HighLogVector K h k := fun i => z.logarithm i.1
  let f : (∀ i : HighIndex h k, TagField i.1 → LogDigit K i.1) →+
      (Fin n → HighLogVector K h k) :=
    UniformTrials.varyingMaskSums (fun i : HighIndex h k => T.triple i.1)
  have hf : Function.Surjective f := UniformTrials.varyingMaskSums_surjective
    (fun i : HighIndex h k => T.triple i.1)
    (fun i j => T.nonconstant i.1 j) (fun i => T.high_disjoint i.1 i.2)
  let reflect : HighLogVector K h k ≃ HighLogVector K h k :=
    { toFun := fun w => c - w
      invFun := fun w => c - w
      left_inv := fun w => sub_sub_cancel c w
      right_inv := fun w => sub_sub_cancel c w }
  let good (w : HighLogVector K h k) := GoodLogVector K k (joinLogVectors K hhk u (c - w))
  have hg : ε ≤ finiteDensity good := by
    have heq := finiteDensity_equiv reflect
      (fun v => GoodLogVector K k (joinLogVectors K hhk u v))
    exact (hd u).trans_eq heq.symm
  have hv (b : ∀ i : HighIndex h k, TagField i.1 → LogDigit K i.1) (j : Fin n) :
      trialLogVector K T (e.symm (a, b)) j = joinLogVectors K hhk u (c - f b j) := by
    funext i
    by_cases hi : i.1 < h
    · change z.logarithm i - Masks.maskSum (T.triple i j)
          ((if hi' : p i then a ⟨i, hi'⟩ else b ⟨i, hi'⟩)) =
        (if hi' : i.1 < h then u ⟨i.1, hi'⟩ else (c - f b j) ⟨i, hi'⟩)
      rw [dif_pos hi, dif_pos hi]
      dsimp only [u]
      rw [T.low_constant i hi j j₀]
    · change z.logarithm i - Masks.maskSum (T.triple i j)
          ((if hi' : p i then a ⟨i, hi'⟩ else b ⟨i, hi'⟩)) =
        (if hi' : i.1 < h then u ⟨i.1, hi'⟩ else (c - f b j) ⟨i, hi'⟩)
      rw [dif_neg hi, dif_neg hi]
      rfl
  have heq : finiteDensity (fun b => ∀ j, ¬ GoodLogVector K k
      (trialLogVector K T (e.symm (a, b)) j)) =
      finiteDensity (fun b => ∀ j, ¬ good (f b j)) := by
    apply finiteDensity_congr
    intro b
    simp only [hv, good]
  change finiteDensity (fun b => ∀ j, ¬ GoodLogVector K k
    (trialLogVector K T (e.symm (a, b)) j)) ≤ _
  rw [heq]
  calc
    _ ≤ Real.exp (-(n : ℝ) * finiteDensity good) :=
      UniformTrials.finiteDensity_missed_le_exp f hf good
    _ ≤ _ := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr (Nat.cast_nonneg n)))

theorem maskTarget_failure_density_le {k h n : ℕ} (z : MaskTarget K k)
    (hhk : h ≤ k) (hn : 1 ≤ n) (hsize : ∀ i, h ≤ i → 7 * n ≤ 7 ^ tagDimension i) (ε : ℝ)
    (hd : ∀ u : LogVector K h,
      ε ≤ finiteDensity (fun v => GoodLogVector K k (joinLogVectors K hhk u v))) :
    finiteDensity (fun τ : LevelMasks K k => ¬ MaskTargetHit K τ z) ≤
      Real.exp (-(n : ℝ) * ε) := by
  classical
  obtain ⟨T⟩ := exists_maskTrialFamily K z hn hsize
  calc
    _ ≤ finiteDensity (fun τ : LevelMasks K k => ∀ j, ¬ GoodLogVector K k (trialLogVector K T τ j)) :=
      finiteDensity_mono (fun τ hτ j hj => hτ (maskTargetHit_of_trial K T τ j hj))
    _ ≤ _ := trial_failure_density_le K T hhk hn ε hd

end Erdos157.Binary
