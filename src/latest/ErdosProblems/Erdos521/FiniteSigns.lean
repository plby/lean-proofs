/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite uniform sign law on any injectively selected coordinates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SeparatedSigns
import ErdosProblems.Erdos521.SignSymmetry

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem uniformBool_eq_bernoulli : (PMF.uniformOfFintype Bool).toMeasure =
    Ber(true, false, ⟨1 / 2, by norm_num⟩) := by
  apply Measure.ext_of_singleton
  intro b
  rw [(PMF.uniformOfFintype Bool).toMeasure_apply_singleton b (measurableSet_singleton b), PMF.uniformOfFintype_apply,
    bernoulliMeasure_apply _ (measurableSet_singleton b)]
  cases b <;> norm_num [unitInterval.toNNReal, unitInterval.symm]
  all_goals
    change (2 : ℝ≥0∞)⁻¹ = ((1 / 2 : ℝ≥0) : ℝ≥0∞)
    norm_num

theorem signLaw_map_encodeSign : signLaw.map encodeSign = (PMF.uniformOfFintype Bool).toMeasure := by
  rw [signLaw, map_bernoulliMeasure, uniformBool_eq_bernoulli]
  congr 1 <;> norm_num [encodeSign]

theorem uniformBool_pi (k : ℕ) :
    Measure.pi (fun _ : Fin k ↦ (PMF.uniformOfFintype Bool).toMeasure) =
      (PMF.uniformOfFintype (Fin k → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro w
  have hsingle (b : Bool) : (PMF.uniformOfFintype Bool).toMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
    rw [(PMF.uniformOfFintype Bool).toMeasure_apply_singleton b (measurableSet_singleton b), PMF.uniformOfFintype_apply]
    norm_num
  rw [Measure.pi_singleton,
    (PMF.uniformOfFintype (Fin k → Bool)).toMeasure_apply_singleton w (measurableSet_singleton w)]
  simp only [hsingle, PMF.uniformOfFintype_apply, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.inv_pow.symm

noncomputable def selectedSigns {k : ℕ} (ι : Fin k → ℕ) (ε : ℕ → ℝ) (i : Fin k) : Bool := encodeSign (ε (ι i))

theorem measurable_selectedSigns {k : ℕ} (ι : Fin k → ℕ) : Measurable (selectedSigns ι) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_encodeSign.comp (measurable_pi_apply (ι i))

theorem sequenceLaw_map_selectedSigns {k : ℕ} (ι : Fin k → ℕ) (hι : Function.Injective ι) :
    sequenceLaw.map (selectedSigns ι) = (PMF.uniformOfFintype (Fin k → Bool)).toMeasure := by
  have hind : iIndepFun (fun i ε ↦ encodeSign (ε (ι i))) sequenceLaw :=
    (independent_coefficients.precomp hι).comp (fun _ ↦ encodeSign) (fun _ ↦ measurable_encodeSign)
  have hmap := hind.map_fun_eq_pi_map (fun i ↦
    (measurable_encodeSign.comp (measurable_pi_apply (ι i))).aemeasurable)
  change sequenceLaw.map (selectedSigns ι) = _ at hmap
  rw [hmap]
  apply Eq.trans _ (uniformBool_pi k)
  congr 1
  funext i
  have hcoord : sequenceLaw.map (fun ε ↦ encodeSign (ε (ι i))) = signLaw.map encodeSign := by
    rw [← sequenceLaw_map_eval (ι i), Measure.map_map measurable_encodeSign (measurable_pi_apply (ι i))]
    rfl
  exact hcoord.trans signLaw_map_encodeSign

theorem signValue_encodeSign {x : ℝ} (hx : x = 1 ∨ x = -1) : signValue (encodeSign x) = x := by
  rcases hx with rfl | rfl <;> norm_num [signValue, encodeSign]

theorem finiteSignValue_eq_sum {k : ℕ} (q : ℝ) (w : Fin k → Bool) :
    finiteSignValue q w = ∑ i : Fin k, signValue (w i) * q ^ (i : ℕ) := by
  induction k with
  | zero => simp [finiteSignValue, signWordValue]
  | succ k ih =>
    rw [finiteSignValue, List.ofFn_succ, signWordValue]
    change signValue (w 0) + q * finiteSignValue q (fun i : Fin k ↦ w i.succ) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem ae_finiteSignValue_selectedSigns {k : ℕ} (ι : Fin k → ℕ) (q : ℝ) :
    ∀ᵐ ε ∂sequenceLaw, finiteSignValue q (selectedSigns ι ε) =
      ∑ i : Fin k, ε (ι i) * q ^ (i : ℕ) := by
  filter_upwards [ae_sequence_signs] with ε hε
  rw [finiteSignValue_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [selectedSigns, signValue_encodeSign (hε (ι i))]

theorem selected_geometric_sum_smallBall {k : ℕ} (ι : Fin k → ℕ) (hι : Function.Injective ι)
    {q z δ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 2 / 5) (hδ : 2 * δ < q ^ k) :
    sequenceLaw.real {ε | |(∑ i : Fin k, ε (ι i) * q ^ (i : ℕ)) - z| ≤ δ} ≤ 1 / (2 : ℝ) ^ k := by
  have h := finiteSignValue_small_interval_probability (z := z) hq₀ hq₁ k hδ
  rw [← sequenceLaw_map_selectedSigns ι hι,
    map_measureReal_apply (measurable_selectedSigns ι) (Set.toFinite _).measurableSet] at h
  change sequenceLaw.real {ε | |finiteSignValue q (selectedSigns ι ε) - z| ≤ δ} ≤ _ at h
  have heq : {ε | |finiteSignValue q (selectedSigns ι ε) - z| ≤ δ} =ᵐ[sequenceLaw]
      {ε | |(∑ i : Fin k, ε (ι i) * q ^ (i : ℕ)) - z| ≤ δ} := by
    filter_upwards [ae_finiteSignValue_selectedSigns ι q] with ε hε
    change (|finiteSignValue q (selectedSigns ι ε) - z| ≤ δ) =
      (|(∑ i : Fin k, ε (ι i) * q ^ (i : ℕ)) - z| ≤ δ)
    rw [hε]
  rw [measureReal_congr heq] at h
  exact h

end Erdos521
