import ErdosProblems.Erdos421.MixedCharacterMoments
import ErdosProblems.Erdos421.FiniteNormPower

/-! # Concentrating the free variables in one fiber of a finite partition -/

namespace Erdos421

variable {q k : ℕ} [NeZero q]

theorem vectorCharacterSum_fiber_partition {Y C : Type*} [Fintype C] [DecidableEq C]
    (T : Finset Y) (g : Y → Fin k → ZMod q) (ρ : Y → C) (a : Fin k → ZMod q) :
    (∑ c : C, vectorCharacterSum (T.filter (fun y ↦ ρ y = c)) g a) =
      vectorCharacterSum T g a :=
  Finset.sum_fiberwise T ρ (fun y ↦ vectorCharacter a (g y))

theorem exists_mixedCongruenceCount_fiber {X Y C : Type*}
    [Fintype C] [Nonempty C] [DecidableEq C] (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) (ρ : Y → C)
    {s : ℕ} (hs : 0 < s) :
    ∃ c : C, mixedCongruenceCount S T f g s ≤
      (Fintype.card C) ^ (2 * s) * mixedCongruenceCount S (T.filter (fun y ↦ ρ y = c)) f g s := by
  obtain ⟨c, _, hc⟩ := exists_weighted_norm_sum_concentration
    (Finset.univ : Finset (Fin k → ZMod q)) (Finset.univ : Finset C) Finset.univ_nonempty
    (fun a ↦ ‖vectorCharacterSum S f a‖ ^ 2)
    (fun c a ↦ vectorCharacterSum (T.filter (fun y ↦ ρ y = c)) g a)
    (fun a _ ↦ sq_nonneg _) (m := 2 * s) (Nat.mul_pos (by decide) hs)
  simp_rw [vectorCharacterSum_fiber_partition] at hc
  rw [mixedCharacterMoment_eq_count, mixedCharacterMoment_eq_count, Finset.card_univ] at hc
  have hq : (0 : ℝ) < (q : ℝ) ^ k :=
    pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) k
  have hreal : (mixedCongruenceCount S T f g s : ℝ) ≤
      (Fintype.card C : ℝ) ^ (2 * s) *
        (mixedCongruenceCount S (T.filter (fun y ↦ ρ y = c)) f g s : ℝ) := by
    apply (mul_le_mul_iff_right₀ hq).mp
    calc
      _ ≤ (Fintype.card C : ℝ) ^ (2 * s) *
          ((q : ℝ) ^ k * (mixedCongruenceCount S (T.filter (fun y ↦ ρ y = c)) f g s : ℝ)) := hc
      _ = _ := by ring
  refine ⟨c, ?_⟩
  exact_mod_cast hreal

end Erdos421
