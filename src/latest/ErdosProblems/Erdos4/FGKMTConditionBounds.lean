import ErdosProblems.Erdos4.FGKMTConditionalSurvival

/-! Conditioning costs at most the reciprocal of the conditioning mass. -/

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem condition_mean_nonneg_le (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (o₀ : Ω) (hE : 0 < ν.prob E) (f : Ω → ℝ) (hf : ∀ o, 0 ≤ f o) :
    (ν.condition E o₀).mean f ≤ ν.mean f / ν.prob E := by
  rw [condition_mean ν E o₀ (ne_of_gt hE)]
  apply div_le_div_of_nonneg_right _ hE.le
  apply ν.mean_mono
  intro o
  split_ifs
  · rfl
  · exact hf o

end Erdos4.FGKMT.FiniteLaw

namespace Erdos4.FGKMT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem conditionSurvival_support (ν : FiniteLaw (Finset V)) (T W : Finset V)
    (hT : survival ν T ≠ 0) (hW : 0 < (conditionSurvival ν T).weight W) : T ⊆ W :=
  ν.condition_support (fun W => T ⊆ W) ∅ W hT hW

theorem survival_lower (ν : FiniteLaw (Finset V)) (p : V → ℝ)
    {A : ℕ} {κ ε : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε : ε ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hacc : SurvivalAccurate ν p A ε)
    {T : Finset V} (hT : T.card ≤ A) : κ ^ A / 2 ≤ survival ν T := by
  have hp0 : ∀ v, 0 < p v := fun v => hκ0.trans_le (hp v)
  have hh := (abs_le.mp (hacc T hT)).1
  have hratio : 1 / 2 ≤ survival ν T / setProduct p T := by linarith
  have hprod := setProduct_lower p hκ0.le hκ1 hp hT
  have hmul := (le_div_iff₀ (setProduct_pos p hp0 T)).mp hratio
  linarith

theorem conditioned_error_le (ν : FiniteLaw (Finset V)) (p : V → ℝ)
    {A : ℕ} {κ ε b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε : ε ≤ 1 / 2)
    (hp : ∀ v, κ ≤ p v) (hacc : SurvivalAccurate ν p A ε)
    (T : Finset V) (hT : T.card ≤ A) (f : Finset V → ℝ) (hf : ∀ W, 0 ≤ f W)
    (hb : ν.mean f ≤ b) : (conditionSurvival ν T).mean f ≤ 2 * b / κ ^ A := by
  have hlower := survival_lower ν p hκ0 hκ1 hε hp hacc hT
  have hpos : 0 < survival ν T := (half_pos (pow_pos hκ0 A)).trans_le hlower
  have hb0 : 0 ≤ b := (ν.mean_nonneg hf).trans hb
  calc
    _ ≤ ν.mean f / survival ν T := ν.condition_mean_nonneg_le
      (fun W => T ⊆ W) ∅ hpos f hf
    _ ≤ b / survival ν T := div_le_div_of_nonneg_right hb hpos.le
    _ ≤ b / (κ ^ A / 2) := div_le_div_of_nonneg_left hb0
      (half_pos (pow_pos hκ0 A)) hlower
    _ = _ := by ring

end Erdos4.FGKMT
