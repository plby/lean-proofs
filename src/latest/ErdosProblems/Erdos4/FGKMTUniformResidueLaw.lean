import ErdosProblems.Erdos4.FGKMTFullTupleMomentBounds
import ErdosProblems.Erdos4.FGKMTExpectationExtraction
import ErdosProblems.Erdos4.FGKMTLawMoments
import ErdosProblems.Erdos4.FGKMTWeightedNormalizerLoss

/-! Uniform residue assignments and the exact conversion from conditional probabilities. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical RandomResidueSieve

namespace FiniteLaw

theorem mean_filter_card {Ω V : Type*} [Fintype Ω] [Fintype V]
    (ν : FiniteLaw Ω) (E : Ω → V → Prop) [∀ o, DecidablePred (E o)] :
    ν.mean (fun o => ((Finset.univ.filter (E o)).card : ℝ)) =
      ∑ v, ν.prob (fun o => E o v) := by
  have hc : ∀ o, ((Finset.univ.filter (E o)).card : ℝ) =
      ∑ v : V, if E o v then (1 : ℝ) else 0 := by
    intro o
    simp
  calc
    _ = ν.mean (fun o => ∑ v : V, if E o v then (1 : ℝ) else 0) := ν.mean_congr hc
    _ = ∑ v : V, ν.mean (fun o => if E o v then (1 : ℝ) else 0) := ν.mean_finset_sum _ _
    _ = _ := by simp only [← prob_eq_mean]

theorem exists_two_mean_bounds {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (f g : Ω → ℝ) (hf0 : ∀ o, 0 ≤ f o) (hg0 : ∀ o, 0 ≤ g o)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hf : ν.mean f ≤ A) (hg : ν.mean g ≤ B) :
    ∃ o, 0 < ν.weight o ∧ f o ≤ 2 * A ∧ g o ≤ 2 * B := by
  obtain ⟨o, ho, hsum⟩ := ν.exists_support_le_mean (fun o => f o / A + g o / B)
  have hm : ν.mean (fun o => f o / A + g o / B) ≤ 2 := by
    rw [mean_add, mean_div_const, mean_div_const]
    have ha := (div_le_one hA).mpr hf
    have hb := (div_le_one hB).mpr hg
    linarith
  have hh := hsum.trans hm
  have hfa : f o / A ≤ 2 := by
    have hgb := div_nonneg (hg0 o) hB.le
    linarith
  have hgb : g o / B ≤ 2 := by
    have hfa := div_nonneg (hf0 o) hA.le
    linarith
  exact ⟨o, ho, (div_le_iff₀ hA).mp hfa, (div_le_iff₀ hB).mp hgb⟩

end FiniteLaw

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def uniformResidueLaw : FiniteLaw (∀ l, ZMod (ell l)) where
  weight := weight ell
  nonneg := weight_nonneg ell
  total := sum_weight ell

theorem uniformResidueLaw_survival (T : Finset ℕ) :
    (uniformResidueLaw ell).prob (fun a => Survives ell a T) = survivalMass ell T :=
  survivalMass_eq ell T

theorem uniformResidueLaw_singleton (q : ℕ) :
    (uniformResidueLaw ell).prob (fun a => Survives ell a {q}) = UnitFourier.unitDensity ell := by
  rw [uniformResidueLaw_survival, survivalMass_singleton]

theorem uniform_surviving_event_eq (q : ℕ) (E : (∀ l, ZMod (ell l)) → Prop) :
    (uniformResidueLaw ell).prob (fun a => Survives ell a {q} ∧ E a) =
      UnitFourier.unitDensity ell * (conditionalResidueLaw ell q).prob E := by
  unfold FiniteLaw.prob
  dsimp only [uniformResidueLaw, conditionalResidueLaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hσ : UnitFourier.unitDensity ell ≠ 0 := (UnitFourier.unitDensity_pos ell).ne'
  unfold conditionalWeight
  by_cases hS : Survives ell a {q} <;> by_cases hE : E a <;>
    simp [hS, hE, hσ, div_eq_mul_inv, mul_comm, mul_left_comm]

end Erdos4.FGKMT
