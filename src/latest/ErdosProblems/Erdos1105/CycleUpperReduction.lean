import ErdosProblems.Erdos1105.Blocks
import ErdosProblems.Erdos1105.PrivateColors
import ErdosProblems.Erdos1105.WeakBlocks

/-!
The induction and analytic reduction for the cycle upper bound. The
combinatorial input `HighPrivateCycleBound` is proved in `CycleUpper.lean`.
-/

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/-- The high-private-color case of the cycle upper bound. -/
def HighPrivateCycleBound (k : ℕ) : Prop :=
  ∀ n q : ℕ, ∀ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q,
    Function.Surjective c →
    (∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) →
    (∀ v, ((k : ℝ) - 2) / 2 < ((privateColors c v).card : ℝ)) →
    (q : ℝ) ≤ (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n

/-- Deleting a vertex with few private colors reduces the entire cycle
upper bound to the high-private-color case. -/
theorem cycle_upper_bound_of_high_private_bound (k : ℕ) (hk : 3 ≤ k)
    (hhigh : HighPrivateCycleBound k) (n : ℕ) :
    (antiRamseyNum (cycleGraph k) n : ℝ) ≤
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hfrac : (0 : ℝ) ≤ 1 / ((k : ℝ) - 1) := le_of_lt (one_div_pos.mpr hden)
  have halpha : (0 : ℝ) ≤ ((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1) := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    apply antiRamseyNum_le_real (mul_nonneg halpha (Nat.cast_nonneg _))
    intro q c hc hH
    by_cases hsmall : ∃ v, ((privateColors c v).card : ℝ) ≤ ((k : ℝ) - 2) / 2
    · obtain ⟨v, hv⟩ := hsmall
      have hcount := color_count_le_delete_add_private c v hH
      simp only [Fintype.card_fin, Nat.add_sub_cancel] at hcount
      have hcountR : (q : ℝ) ≤ (antiRamseyNum (cycleGraph k) n : ℝ) +
          ((privateColors c v).card : ℝ) := by exact_mod_cast hcount
      push_cast
      nlinarith
    · apply hhigh (n + 1) q c hc hH
      push Not at hsmall
      exact hsmall

/-- Once the high-private-color input is proved, the bounded-error cycle
asymptotic follows from the checked block construction and deletion induction. -/
theorem cycle_asymptotic_of_high_private_bound (k : ℕ) (hk : 3 ≤ k)
    (hhigh : HighPrivateCycleBound k) :
    ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ))) := by
  rw [isBigO_one_nat_atTop_iff]
  refine ⟨((k - 1).choose 2 + 2 : ℕ), fun n ↦ ?_⟩
  rw [Real.norm_eq_abs, abs_le]
  have hlo := cycle_lower_bound_real k hk n
  have hhi := cycle_upper_bound_of_high_private_bound k hk hhigh n
  constructor <;> linarith [Nat.cast_nonneg ((k - 1).choose 2 + 2) (α := ℝ)]

end Erdos1105
