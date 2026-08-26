/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
From finite quadrant paths to cone-survival probabilities for Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SecondMoment
import ErdosProblems.Erdos521.BridgeCounts

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Reverse exactly the first `m+1` coordinates. -/
def reverseIndex (m i : ℕ) : ℕ := if i ≤ m then m - i else i

theorem reverseIndex_involutive (m : ℕ) : Function.Involutive (reverseIndex m) := by
  intro i
  simp only [reverseIndex]
  split_ifs <;> omega

def reversePrefix {α : Type*} (m : ℕ) (ω : ℕ → α) : ℕ → α :=
  fun i ↦ ω (reverseIndex m i)

theorem measurePreserving_reversePrefix {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (m : ℕ) :
    MeasurePreserving (reversePrefix m) (Measure.infinitePi fun _ : ℕ ↦ ν)
      (Measure.infinitePi fun _ : ℕ ↦ ν) := by
  refine ⟨by fun_prop [reversePrefix], ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (reverseIndex_involutive m).injective

/-- All nonempty partial sums, up to time `m+1`, lie in the cone. -/
def pairSurvival (m : ℕ) : Set (ℕ → ℝ × ℝ) :=
  {ω | ∀ r ≤ m, InCone (partialSum (fun i ↦ (ω i).1) r)
    (partialSum (fun i ↦ (ω i).2) r)}

theorem measurableSet_pairSurvival (m : ℕ) : MeasurableSet (pairSurvival m) := by
  have hfst (r : ℕ) : Measurable (fun ω : ℕ → ℝ × ℝ ↦
      partialSum (fun i ↦ (ω i).1) r) :=
    Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).fst
  have hsnd (r : ℕ) : Measurable (fun ω : ℕ → ℝ × ℝ ↦
      partialSum (fun i ↦ (ω i).2) r) :=
    Finset.measurable_sum _ fun i _ ↦ (measurable_pi_apply i).snd
  simp only [pairSurvival, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro _
  simp only [inCone_iff, Set.ofPred_and]
  exact (measurableSet_le measurable_const ((hfst r).add (hsnd r))).inter
    (measurableSet_le measurable_const ((hfst r).sub (hsnd r)))

theorem partialSum_reversePrefix (a : ℕ → ℝ) (m r : ℕ) (hr : r ≤ m) :
    partialSum (reversePrefix m a) r = prefixSum a (m + 1) - prefixSum a (m - r) := by
  rw [← partialSum_reverse a m r hr]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hr
  simp [reversePrefix, reverseIndex, hi']

theorem pairRecord_eq_reverse_survival (m : ℕ) :
    pairRecord m = reversePrefix m ⁻¹' pairSurvival m := by
  ext ω
  change ConeRecord _ _ m ↔ ∀ r ≤ m, InCone _ _
  simp only [show (fun i ↦ (reversePrefix m ω i).1) =
      reversePrefix m (fun i ↦ (ω i).1) from rfl,
    show (fun i ↦ (reversePrefix m ω i).2) =
      reversePrefix m (fun i ↦ (ω i).2) from rfl]
  constructor
  · intro h r hr
    rw [partialSum_reversePrefix _ m r hr, partialSum_reversePrefix _ m r hr]
    exact h (m - r) (Nat.sub_le _ _)
  · intro h k hk
    have hr := h (m - k) (Nat.sub_le _ _)
    rw [partialSum_reversePrefix _ m _ (Nat.sub_le _ _),
      partialSum_reversePrefix _ m _ (Nat.sub_le _ _), Nat.sub_sub_self hk] at hr
    exact hr

theorem pairRecord_measure_eq_survival (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (m : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ ν) (pairRecord m) =
      (Measure.infinitePi fun _ : ℕ ↦ ν) (pairSurvival m) := by
  rw [pairRecord_eq_reverse_survival]
  exact (measurePreserving_reversePrefix ν m).measure_preimage
    (measurableSet_pairSurvival m).nullMeasurableSet

namespace Pitman

def signPair (d : Direction) : ℝ × ℝ :=
  ((step d).1 + (step d).2, (step d).1 - (step d).2)

noncomputable def directionLaw : Measure Direction := (PMF.uniformOfFintype Direction).toMeasure

instance : IsProbabilityMeasure directionLaw := by
  unfold directionLaw
  infer_instance

noncomputable def pairedDirectionLaw : Measure (ℝ × ℝ) := directionLaw.map signPair

theorem measurable_signPair : Measurable signPair := measurable_of_finite _

instance : IsProbabilityMeasure pairedDirectionLaw :=
  Measure.isProbabilityMeasure_map measurable_signPair.aemeasurable

def pairSequence (ω : ℕ → Direction) : ℕ → ℝ × ℝ := fun i ↦ signPair (ω i)

theorem measurePreserving_pairSequence :
    MeasurePreserving pairSequence (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
      (Measure.infinitePi fun _ : ℕ ↦ pairedDirectionLaw) := by
  exact ⟨by fun_prop [pairSequence], Measure.infinitePi_map_pi _ fun _ ↦ measurable_signPair⟩

theorem directionLaw_singleton (d : Direction) : directionLaw {d} = (4 : ℝ≥0∞)⁻¹ := by
  simp [directionLaw, PMF.uniformOfFintype_apply]

theorem finite_directionLaw (n : ℕ) :
    (Measure.infinitePi fun _ : Fin n ↦ directionLaw) =
      (PMF.uniformOfFintype (Fin n → Direction)).toMeasure := by
  apply Measure.ext_of_singleton
  intro w
  simp [directionLaw_singleton, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

def directionPrefix (n : ℕ) (ω : ℕ → Direction) : List Direction :=
  List.ofFn fun i : Fin n ↦ ω i

theorem directionPrefix_length (n : ℕ) (ω : ℕ → Direction) :
    (directionPrefix n ω).length = n := by simp [directionPrefix]

theorem directionPrefix_succ (n : ℕ) (ω : ℕ → Direction) :
    directionPrefix (n + 1) ω = directionPrefix n ω ++ [ω n] := by
  change List.ofFn _ = _
  rw [List.ofFn_succ_last]
  rfl

theorem directionPrefix_take (n k : ℕ) (hkn : k ≤ n) (ω : ℕ → Direction) :
    (directionPrefix n ω).take k = directionPrefix k ω := by
  apply List.ext_getElem
  · simp [directionPrefix, hkn]
  · intro i hi hj
    simp [directionPrefix]

noncomputable def survivingTuples (n : ℕ) : Finset (Fin n → Direction) := by
  classical
  exact Finset.univ.filter fun w ↦ StaysNonnegative (List.ofFn w)

theorem survivingWords_card (n : ℕ) :
    (survivingWords n).card = (survivingTuples n).card := by
  classical
  have heq : survivingWords n = (survivingTuples n).image List.ofFn := by
    ext w
    simp only [survivingWords, allWords, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and, survivingTuples]
    constructor
    · rintro ⟨⟨f, rfl⟩, hf⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, rfl⟩, hf⟩
  rw [heq, Finset.card_image_of_injective _ List.ofFn_injective]

theorem direction_survival_measure (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
      {ω | StaysNonnegative (directionPrefix n ω)} =
      (survivingWords n).card / (4 : ℝ≥0∞) ^ n := by
  classical
  have hmap : (Measure.infinitePi fun _ : ℕ ↦ directionLaw).map
      (fun ω (i : Fin n) ↦ ω i) =
      (PMF.uniformOfFintype (Fin n → Direction)).toMeasure := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, finite_directionLaw]
  have hmeas : Measurable (fun (ω : ℕ → Direction) (i : Fin n) ↦ ω i) := by fun_prop
  have hevent : {ω | StaysNonnegative (directionPrefix n ω)} =
      (fun ω (i : Fin n) ↦ ω i) ⁻¹' (survivingTuples n : Set (Fin n → Direction)) := by
    ext ω
    simp [survivingTuples, directionPrefix]
  rw [hevent, ← Measure.map_apply hmeas (survivingTuples n).measurableSet, hmap,
    PMF.toMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, ← survivingWords_card, div_eq_mul_inv]

theorem prefixSum_pairSequence (n : ℕ) (ω : ℕ → Direction) :
    prefixSum (fun i ↦ (pairSequence ω i).1) n =
        ((walk (directionPrefix n ω)).1 : ℝ) + (walk (directionPrefix n ω)).2 ∧
      prefixSum (fun i ↦ (pairSequence ω i).2) n =
        ((walk (directionPrefix n ω)).1 : ℝ) - (walk (directionPrefix n ω)).2 := by
  induction n with
  | zero => simp [prefixSum, directionPrefix]
  | succ n ih =>
    rw [prefixSum_succ, prefixSum_succ, directionPrefix_succ,
      walk_append, walk_singleton, ih.1, ih.2]
    simp only [pairSequence, signPair, Prod.fst_add, Prod.snd_add, Int.cast_add]
    constructor <;> ring

theorem pairSequence_inCone_iff (n : ℕ) (ω : ℕ → Direction) :
    InCone (prefixSum (fun i ↦ (pairSequence ω i).1) n)
      (prefixSum (fun i ↦ (pairSequence ω i).2) n) ↔
      0 ≤ walk (directionPrefix n ω) := by
  rw [(prefixSum_pairSequence n ω).1, (prefixSum_pairSequence n ω).2, inCone_iff]
  change _ ↔ 0 ≤ (walk (directionPrefix n ω)).1 ∧ 0 ≤ (walk (directionPrefix n ω)).2
  have h₁ : (0 : ℤ) ≤ (walk (directionPrefix n ω)).1 ↔
      (0 : ℝ) ≤ ((walk (directionPrefix n ω)).1 : ℝ) := by exact_mod_cast Iff.rfl
  have h₂ : (0 : ℤ) ≤ (walk (directionPrefix n ω)).2 ↔
      (0 : ℝ) ≤ ((walk (directionPrefix n ω)).2 : ℝ) := by exact_mod_cast Iff.rfl
  rw [h₁, h₂]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem pairSequence_survival_iff (m : ℕ) (ω : ℕ → Direction) :
    pairSequence ω ∈ pairSurvival m ↔ StaysNonnegative (directionPrefix (m + 1) ω) := by
  change (∀ r ≤ m, InCone _ _) ↔ _
  change (∀ r ≤ m, InCone (prefixSum (fun i ↦ (pairSequence ω i).1) (r + 1))
    (prefixSum (fun i ↦ (pairSequence ω i).2) (r + 1))) ↔ _
  simp only [pairSequence_inCone_iff, StaysNonnegative, directionPrefix_length]
  constructor
  · intro h k hk
    rw [directionPrefix_take _ _ hk]
    cases k with
    | zero => simp [directionPrefix]
    | succ k => exact h k (by omega)
  · intro h r hr
    have hk : r + 1 ≤ m + 1 := by omega
    simpa only [directionPrefix_take _ _ hk] using h (r + 1) hk

/-- Exact survival probability under the four equally likely diagonal sign pairs. -/
theorem pairedDirection_survival_measure (m : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ pairedDirectionLaw) (pairSurvival m) =
      (survivingWords (m + 1)).card / (4 : ℝ≥0∞) ^ (m + 1) := by
  rw [← measurePreserving_pairSequence.measure_preimage
    (measurableSet_pairSurvival m).nullMeasurableSet]
  have heq : pairSequence ⁻¹' pairSurvival m =
      {ω | StaysNonnegative (directionPrefix (m + 1) ω)} := by
    ext ω
    exact pairSequence_survival_iff m ω
  rw [heq, direction_survival_measure]

theorem pairedDirection_recordProbability (m : ℕ) :
    recordProbability pairedDirectionLaw m =
      (survivingWords (m + 1)).card / (4 : ℝ) ^ (m + 1) := by
  rw [recordProbability, measureReal_def, pairRecord_measure_eq_survival,
    pairedDirection_survival_measure]
  simp

/-- A harmonic lower bound at the even path lengths. -/
theorem pairedDirection_recordProbability_lower (j : ℕ) :
    1 / (4 * ((j : ℝ) + 1)) ≤ recordProbability pairedDirectionLaw (2 * (j + 1) - 1) := by
  rw [pairedDirection_recordProbability, show 2 * (j + 1) - 1 + 1 = 2 * (j + 1) by omega]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hcount : (16 : ℝ) ^ (j + 1) ≤
      4 * ((j : ℝ) + 1) * (survivingWords (2 * (j + 1))).card := by
    exact_mod_cast survivingWords_card_lower j
  have hpow : (4 : ℝ) ^ (2 * (j + 1)) = 16 ^ (j + 1) := by
    rw [pow_mul]
    norm_num
  rw [one_mul, hpow]
  simpa [mul_comm] using hcount

/-- The concrete fair-sign record probabilities have divergent sum. -/
theorem pairedDirection_recordProbability_divergent :
    Filter.Tendsto (recordProbabilitySum pairedDirectionLaw) Filter.atTop Filter.atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (recordProbability_nonneg pairedDirectionLaw)).mp
  intro hs
  have hsub : Summable (fun j ↦ recordProbability pairedDirectionLaw (2 * (j + 1) - 1)) :=
    hs.comp_injective (by intro a b h; dsimp at h; omega)
  have hsmall : Summable (fun j : ℕ ↦ 1 / (4 * ((j : ℝ) + 1))) :=
    hsub.of_nonneg_of_le (fun _ ↦ by positivity) pairedDirection_recordProbability_lower
  have hharm : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) := by
    apply (hsmall.mul_left (4 : ℝ)).congr
    intro j
    field_simp
  have hshift : Summable (fun j : ℕ ↦ 1 / ((j + 1 : ℕ) : ℝ)) := by
    simpa using hharm
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hshift)

theorem pairedDirection_infiniteRecords_measure_one :
    (Measure.infinitePi fun _ : ℕ ↦ pairedDirectionLaw) pairInfiniteRecords = 1 :=
  pairInfiniteRecords_measure_one_of_divergence pairedDirectionLaw
    pairedDirection_recordProbability_divergent

end Pitman
end Erdos521
