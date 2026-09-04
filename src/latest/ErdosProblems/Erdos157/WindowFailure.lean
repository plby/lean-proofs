import ErdosProblems.Erdos157.TargetFailure
import ErdosProblems.Erdos157.CoverageDecay

/-! Simultaneous integer coverage throughout one level window. -/

namespace Erdos157.Elementary

open AuxiliaryModuli Filter

noncomputable def WindowFailure (τ : MaskChoice CoefficientField) (k : ℕ)
    (ω : LevelParameters CoefficientField k) : Prop :=
  ∃ m : Fin (6 * blockPlace CoefficientField 0 (k + 1)),
    6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ ¬ LocallyRepresented CoefficientField τ k ω m.1

theorem window_target_failure (τ : MaskChoice CoefficientField) (k : ℕ) (hk : 400 ≤ k)
    (hhit : ∀ z : MaskTarget CoefficientField k, MaskTargetHit CoefficientField (fun i => τ i) z)
    (m : ℕ) (hmlo : 6 * blockPlace CoefficientField 0 k ≤ m)
    (hmhi : m < 6 * blockPlace CoefficientField 0 (k + 1)) :
    finiteDensity (fun ω : LevelParameters CoefficientField k =>
      ¬ LocallyRepresented CoefficientField τ k ω m) ≤ Real.exp (-(2 : ℝ) ^ (k ^ 2)) := by
  obtain ⟨d, z, he, hzlo⟩ := exists_level_target_expansion CoefficientField k m (by omega)
  have hB := blockPlace_pos CoefficientField 0 k
  have hcap := coefficientField_topCapacity k (by omega)
  rw [blockPlace_snoc] at hmhi
  have hzhi : z ≤ 3 * Fintype.card CoefficientField ^ (3 * k) := by
    have hzR : z < 6 * blockRadix CoefficientField k := by nlinarith
    omega
  rw [he]
  exact target_failure_coefficientField τ k hk d (hhit _) z (by omega) hzhi

theorem window_failure_density (τ : MaskChoice CoefficientField) (k : ℕ) (hk : 400 ≤ k)
    (hhit : ∀ z : MaskTarget CoefficientField k, MaskTargetHit CoefficientField (fun i => τ i) z) :
    finiteDensity (WindowFailure τ k) ≤
      (6 * blockPlace CoefficientField 0 (k + 1) : ℝ) * Real.exp (-(2 : ℝ) ^ (k ^ 2)) := by
  classical
  have hbound (m : Fin (6 * blockPlace CoefficientField 0 (k + 1))) :
      finiteDensity (fun ω : LevelParameters CoefficientField k =>
        6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ ¬ LocallyRepresented CoefficientField τ k ω m.1) ≤
        Real.exp (-(2 : ℝ) ^ (k ^ 2)) := by
    by_cases hm : 6 * blockPlace CoefficientField 0 k ≤ m.1
    · exact (finiteDensity_mono (fun _ h => h.2)).trans
        (window_target_failure τ k hk hhit m.1 hm m.2)
    · have heq : finiteDensity (fun ω : LevelParameters CoefficientField k =>
        6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ ¬ LocallyRepresented CoefficientField τ k ω m.1) = 0 := by
        let : IsEmpty {ω : LevelParameters CoefficientField k //
            6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ ¬ LocallyRepresented CoefficientField τ k ω m.1} :=
          ⟨fun ω => hm ω.2.1⟩
        unfold finiteDensity
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero, Nat.cast_zero, zero_div]
      rw [heq]
      exact (Real.exp_pos _).le
  have hb := finiteDensity_exists_le _ (Real.exp (-(2 : ℝ) ^ (k ^ 2))) hbound
  change finiteDensity (fun ω : LevelParameters CoefficientField k =>
    ∃ m : Fin (6 * blockPlace CoefficientField 0 (k + 1)),
      6 * blockPlace CoefficientField 0 k ≤ m.1 ∧ ¬ LocallyRepresented CoefficientField τ k ω m.1) ≤ _
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using hb

theorem eventually_window_failure_density (τ : MaskChoice CoefficientField)
    (hτ : ∀ᶠ k in atTop, ∀ z : MaskTarget CoefficientField k,
      MaskTargetHit CoefficientField (fun i => τ i) z) :
    ∀ᶠ k in atTop, finiteDensity (WindowFailure τ k) ≤ Real.exp (-(k : ℝ)) := by
  filter_upwards [hτ, eventually_ge_atTop 400, eventually_window_failure_decay] with k hk hk400 hdec
  exact (window_failure_density τ k hk400 hk).trans hdec

end Erdos157.Elementary
