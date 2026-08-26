import ErdosProblems.Erdos4.TupleCollisionMass

/-!
# Conditional tuple masses and their first moment

The outer finite mean conditions on the target surviving. The total
surviving tuple mass and its hitting submass are nonnegative, and the
second never exceeds the first, including zero normalizers. The first
moment is an exact weighted sum of conditional joint-survival masses.
-/

open scoped BigOperators

namespace Erdos4.ConditionalTupleMoments

open RandomResidueSieve AffineTuples TupleCollisionMass

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def indicator (a : ∀ l, ZMod (ell l)) (T : Finset ℕ) : ℝ := by
  classical
  exact if Survives ell a T then 1 else 0

theorem indicator_nonneg (a : ∀ l, ZMod (ell l)) (T : Finset ℕ) : 0 ≤ indicator ell a T := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_le_one (a : ∀ l, ZMod (ell l)) (T : Finset ℕ) : indicator ell a T ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_mul (a : ∀ l, ZMod (ell l)) (T U : Finset ℕ) :
    indicator ell a T * indicator ell a U = indicator ell a (T ∪ U) := by
  classical
  unfold indicator
  rw [survives_union]
  by_cases hT : Survives ell a T <;> by_cases hU : Survives ell a U <;> simp [hT, hU]

noncomputable def mean (q : ℕ) (f : (∀ l, ZMod (ell l)) → ℝ) : ℝ :=
  ∑ a : ∀ l, ZMod (ell l), conditionalWeight ell q a * f a

theorem mean_nonneg (q : ℕ) (f : (∀ l, ZMod (ell l)) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean ell q f := Finset.sum_nonneg (fun a _ha =>
      mul_nonneg (conditionalWeight_nonneg ell q a) (hf a))

theorem mean_mono (q : ℕ) (f g : (∀ l, ZMod (ell l)) → ℝ) (hfg : ∀ a, f a ≤ g a) :
    mean ell q f ≤ mean ell q g := Finset.sum_le_sum (fun a _ha =>
      mul_le_mul_of_nonneg_left (hfg a) (conditionalWeight_nonneg ell q a))

theorem mean_const (q : ℕ) (c : ℝ) : mean ell q (fun _ => c) = c := by
  rw [mean, ← Finset.sum_mul, sum_conditionalWeight, one_mul]

theorem mean_const_mul (q : ℕ) (c : ℝ) (f : (∀ l, ZMod (ell l)) → ℝ) :
    mean ell q (fun a => c * f a) = c * mean ell q f := by
  unfold mean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ha => by ring)

theorem mean_sum {I : Type*} (s : Finset I) (q : ℕ)
    (f : I → (∀ l, ZMod (ell l)) → ℝ) :
    mean ell q (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean ell q (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_indicator (q : ℕ) (T : Finset ℕ) :
    mean ell q (fun a => indicator ell a T) =
      survivalMass ell (insert q T) / UnitFourier.unitDensity ell := by
  classical
  have heq : mean ell q (fun a => indicator ell a T) =
      ∑ a : ∀ l, ZMod (ell l), if Survives ell a T then conditionalWeight ell q a else 0 := by
    apply Finset.sum_congr rfl
    intro a _ha
    unfold indicator
    by_cases hS : Survives ell a T
    · simp only [if_pos hS, mul_one]
    · simp only [if_neg hS, mul_zero]
  rw [heq]
  exact conditional_survivalMass ell q T

theorem conditional_relative_error (q : ℕ) (T : Finset ℕ) (hq : q ∈ T) {ε : ℝ}
    (hT : |survivalMass ell T / UnitFourier.unitDensity ell ^ T.card - 1| ≤ ε) :
    |mean ell q (fun a => indicator ell a T) /
      UnitFourier.unitDensity ell ^ (T.card - 1) - 1| ≤ ε := by
  have hc : 1 ≤ T.card := Finset.card_pos.mpr ⟨q, hq⟩
  have hpow : UnitFourier.unitDensity ell ^ (T.card - 1) * UnitFourier.unitDensity ell =
      UnitFourier.unitDensity ell ^ T.card := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  rw [mean_indicator, Finset.insert_eq_of_mem hq]
  have heq : (survivalMass ell T / UnitFourier.unitDensity ell) /
      UnitFourier.unitDensity ell ^ (T.card - 1) =
      survivalMass ell T / UnitFourier.unitDensity ell ^ T.card := by
    rw [div_div, mul_comm, hpow]
  rw [heq]
  exact hT

variable {k : ℕ}

noncomputable def tupleMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ)
    (a : ∀ l, ZMod (ell l)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, μ n * indicator ell a (tuple h p n)

noncomputable def hittingMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (a : ∀ l, ZMod (ell l)) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, (if q ∈ tuple h p n then μ n else 0) * indicator ell a (tuple h p n)

theorem tupleMass_nonneg (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (a : ∀ l, ZMod (ell l)) :
    0 ≤ tupleMass ell h p Y μ a := Finset.sum_nonneg (fun n hn =>
      mul_nonneg (hμ n hn) (indicator_nonneg ell a (tuple h p n)))

theorem hittingMass_nonneg (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (a : ∀ l, ZMod (ell l)) :
    0 ≤ hittingMass ell h p Y μ q a := by
  apply Finset.sum_nonneg
  intro n hn
  apply mul_nonneg _ (indicator_nonneg ell a (tuple h p n))
  split_ifs
  · exact hμ n hn
  · exact le_rfl

theorem hittingMass_le_tupleMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (a : ∀ l, ZMod (ell l)) :
    hittingMass ell h p Y μ q a ≤ tupleMass ell h p Y μ a := by
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (indicator_nonneg ell a (tuple h p n))
  split_ifs
  · exact le_rfl
  · exact hμ n hn

theorem hittingMass_le_hitMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) (a : ∀ l, ZMod (ell l)) :
    hittingMass ell h p Y μ q a ≤ hitMass h p Y μ q := by
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_of_le_one_right _ (indicator_le_one ell a (tuple h p n))
  split_ifs
  · exact hμ n hn
  · exact le_rfl

theorem mean_hittingMass (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ) :
    mean ell q (hittingMass ell h p Y μ q) =
      ∑ n ∈ Finset.Icc 1 Y, (if q ∈ tuple h p n then μ n else 0) *
        (survivalMass ell (insert q (tuple h p n)) / UnitFourier.unitDensity ell) := by
  unfold hittingMass
  rw [mean_sum]
  simp only [mean_const_mul, mean_indicator]

theorem firstMoment_bounds (h : Fin k → ℕ) (p Y : ℕ) (μ : ℕ → ℝ) (q : ℕ)
    (hμ : ∀ n ∈ Finset.Icc 1 Y, 0 ≤ μ n) {L U : ℝ}
    (hlocal : ∀ n ∈ Finset.Icc 1 Y, q ∈ tuple h p n →
      L ≤ mean ell q (fun a => indicator ell a (tuple h p n)) ∧
        mean ell q (fun a => indicator ell a (tuple h p n)) ≤ U) :
    L * hitMass h p Y μ q ≤ mean ell q (hittingMass ell h p Y μ q) ∧
      mean ell q (hittingMass ell h p Y μ q) ≤ U * hitMass h p Y μ q := by
  have heq : mean ell q (hittingMass ell h p Y μ q) =
      ∑ n ∈ Finset.Icc 1 Y, (if q ∈ tuple h p n then μ n else 0) *
        mean ell q (fun a => indicator ell a (tuple h p n)) := by
    unfold hittingMass
    rw [mean_sum]
    simp only [mean_const_mul]
  rw [heq]
  unfold hitMass
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro n hn
    by_cases hq : q ∈ tuple h p n
    · simp only [if_pos hq]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hlocal n hn hq).1 (hμ n hn)
    · simp [hq]
  · apply Finset.sum_le_sum
    intro n hn
    by_cases hq : q ∈ tuple h p n
    · simp only [if_pos hq]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hlocal n hn hq).2 (hμ n hn)
    · simp [hq]

end Erdos4.ConditionalTupleMoments
