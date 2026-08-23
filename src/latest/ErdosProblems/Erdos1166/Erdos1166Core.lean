/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This core file formalizes the deterministic deduction used in the resolution of
Erdős Problem 1166.  It also proves the planar maximal-local-time
`O((log n)^2)` upper bound internally from exact return probabilities, Kac
moments, and Borel--Cantelli.  The remaining deep probabilistic input is the
eventual three-favourite-sites theorem of Hao--Li--Okada--Zheng.  The file
also proves recurrence/maximal-local-time divergence, stopping-time
measurability, and iid restart, isolating the remaining source dependency to
the HLOZ summable four-favourite-site screening estimate.
-/

import Mathlib
import ErdosProblems.Erdos1166.Erdos1166Kac
import ErdosProblems.Erdos1166.Erdos1166IIDRestart
import ErdosProblems.Erdos1166.Erdos1166HLOZUrn

namespace Erdos1166

open Filter MeasureTheory
open scoped BigOperators ENNReal

/-- The state space of the planar walk. -/
abbrev Site := ℤ × ℤ

/-- The four equally likely increments of planar simple symmetric random walk. -/
abbrev Direction := Fin 4

/-- The lattice increment represented by a direction. -/
def directionStep (d : Direction) : Site :=
  match d.1 with
  | 0 => (1, 0)
  | 1 => (-1, 0)
  | 2 => (0, 1)
  | _ => (0, -1)

theorem measurable_directionStep : Measurable directionStep :=
  measurable_from_top

/-- The path determined by a sequence of increments.  At time `n` it is the
sum of the first `n` increments, so it starts at the origin. -/
def simpleRandomWalk (ω : ℕ → Direction) (n : ℕ) : Site :=
  ∑ j ∈ Finset.range n, directionStep (ω j)

theorem measurable_simpleRandomWalk : Measurable simpleRandomWalk := by
  unfold simpleRandomWalk
  fun_prop

/-- The iid uniform law of the four direction increments. -/
noncomputable def incrementLaw : Measure (ℕ → Direction) :=
  Measure.infinitePi fun _ : ℕ ↦ (PMF.uniformOfFintype Direction).toMeasure

/-- The canonical law of planar simple symmetric random walk, as the image of
the iid uniform increment law under partial summation. -/
noncomputable def simpleRandomWalkLaw : Measure (ℕ → Site) :=
  incrementLaw.map simpleRandomWalk

instance : IsProbabilityMeasure incrementLaw := by
  unfold incrementLaw
  infer_instance

instance : IsProbabilityMeasure simpleRandomWalkLaw := by
  unfold simpleRandomWalkLaw
  exact Measure.isProbabilityMeasure_map measurable_simpleRandomWalk.aemeasurable

open MeasureTheory ProbabilityTheory

noncomputable abbrev directionLaw : Measure Direction :=
  (PMF.uniformOfFintype Direction).toMeasure

theorem increment_eval_map (n : ℕ) :
    incrementLaw.map (fun ω ↦ ω n) = directionLaw := by
  simp [incrementLaw, directionLaw, MeasureTheory.Measure.infinitePi_map_eval]

theorem increment_iIndep :
    iIndepFun (fun n (ω : ℕ → Direction) ↦ ω n) incrementLaw := by
  unfold incrementLaw
  exact iIndepFun_infinitePi (X := fun _ d ↦ d) (by fun_prop)

theorem increment_direction_prob (n : ℕ) (d : Direction) :
    incrementLaw {ω | ω n = d} = (4 : ENNReal)⁻¹ := by
  calc
    incrementLaw {ω | ω n = d} =
        (incrementLaw.map (fun ω ↦ ω n)) {d} := by
      rw [Measure.map_apply]
      · rfl
      · fun_prop
      · measurability
    _ = directionLaw {d} := by rw [increment_eval_map]
    _ = (4 : ENNReal)⁻¹ := by
      simp [directionLaw]

theorem increment_event_prob (n : ℕ) (A : Finset Direction) :
    incrementLaw {ω | ω n ∈ A} =
      (A.card : ENNReal) / Fintype.card Direction := by
  calc
    incrementLaw {ω | ω n ∈ A} =
        (incrementLaw.map (fun ω ↦ ω n)) (A : Set Direction) := by
      rw [Measure.map_apply]
      · rfl
      · fun_prop
      · measurability
    _ = directionLaw (A : Set Direction) := by rw [increment_eval_map]
    _ = (A.card : ENNReal) / Fintype.card Direction := by
      simpa [directionLaw] using
        PMF.toMeasure_uniformOfFintype_apply (A : Set Direction) (by measurability)

abbrev stepX (d : Direction) : ℤ := (directionStep d).1
abbrev stepY (d : Direction) : ℤ := (directionStep d).2

private theorem ennreal_two_div_four : (2 : ENNReal) / 4 = (2 : ENNReal)⁻¹ := by
  rw [eq_comm, ← one_div]
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
  rw [show (4 : ENNReal) = 2 * 2 by norm_num, one_div, mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

theorem stepX_eq_one_iff (d : Direction) : stepX d = 1 ↔ d = 0 := by
  fin_cases d <;> decide

theorem stepX_eq_neg_one_iff (d : Direction) : stepX d = -1 ↔ d = 1 := by
  fin_cases d <;> decide

theorem stepX_eq_zero_iff (d : Direction) : stepX d = 0 ↔ d = 2 ∨ d = 3 := by
  fin_cases d <;> decide

theorem stepY_eq_one_iff (d : Direction) : stepY d = 1 ↔ d = 2 := by
  fin_cases d <;> decide

theorem stepY_eq_neg_one_iff (d : Direction) : stepY d = -1 ↔ d = 3 := by
  fin_cases d <;> decide

theorem stepY_eq_zero_iff (d : Direction) : stepY d = 0 ↔ d = 0 ∨ d = 1 := by
  fin_cases d <;> decide

theorem stepX_prob_one (n : ℕ) :
    incrementLaw {ω | stepX (ω n) = 1} = (4 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepX d = 1
  have h := increment_event_prob n A
  have hA : A = {0} := by decide
  simpa [A, hA, stepX_eq_one_iff] using h

theorem stepX_prob_neg_one (n : ℕ) :
    incrementLaw {ω | stepX (ω n) = -1} = (4 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepX d = -1
  have h := increment_event_prob n A
  have hA : A = {1} := by decide
  simpa [A, hA, stepX_eq_neg_one_iff] using h

theorem stepX_prob_zero (n : ℕ) :
    incrementLaw {ω | stepX (ω n) = 0} = (2 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepX d = 0
  have h := increment_event_prob n A
  have hA : A = {2, 3} := by decide
  simpa [A, hA, stepX_eq_zero_iff, ennreal_two_div_four] using h

theorem stepY_prob_one (n : ℕ) :
    incrementLaw {ω | stepY (ω n) = 1} = (4 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepY d = 1
  have h := increment_event_prob n A
  have hA : A = {2} := by decide
  simpa [A, hA, stepY_eq_one_iff] using h

theorem stepY_prob_neg_one (n : ℕ) :
    incrementLaw {ω | stepY (ω n) = -1} = (4 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepY d = -1
  have h := increment_event_prob n A
  have hA : A = {3} := by decide
  simpa [A, hA, stepY_eq_neg_one_iff] using h

theorem stepY_prob_zero (n : ℕ) :
    incrementLaw {ω | stepY (ω n) = 0} = (2 : ENNReal)⁻¹ := by
  let A := Finset.univ.filter fun d : Direction ↦ stepY d = 0
  have h := increment_event_prob n A
  have hA : A = {0, 1} := by decide
  simpa [A, hA, stepY_eq_zero_iff, ennreal_two_div_four] using h

theorem step_eval_map (n : ℕ) :
    incrementLaw.map (fun ω ↦ directionStep (ω n)) =
      directionLaw.map directionStep := by
  calc
    incrementLaw.map (fun ω ↦ directionStep (ω n)) =
        (incrementLaw.map (fun ω ↦ ω n)).map directionStep := by
      rw [Measure.map_map]
      rfl
      all_goals fun_prop
    _ = directionLaw.map directionStep := by rw [increment_eval_map]

theorem step_iIndep :
    iIndepFun (fun n (ω : ℕ → Direction) ↦ directionStep (ω n)) incrementLaw := by
  exact increment_iIndep.comp (fun _ ↦ directionStep) (fun _ ↦ measurable_directionStep)

/-! Finite-prefix API for exact return probabilities. -/

abbrev Prefix (n : ℕ) := (i : ↑(Finset.range n)) → Direction

def finitePosition {n : ℕ} (w : Prefix n) : Site :=
  ∑ i, directionStep (w i)

def returningPrefixes (n : ℕ) : Finset (Prefix n) :=
  Finset.univ.filter fun w ↦ finitePosition w = (0, 0)

theorem finitePosition_restrict (n : ℕ) (ω : ℕ → Direction) :
    finitePosition ((Finset.range n).restrict ω) = simpleRandomWalk ω n := by
  simpa [finitePosition, simpleRandomWalk] using
    (Finset.sum_attach (Finset.range n) (fun j ↦ directionStep (ω j)))

noncomputable abbrev prefixLaw (n : ℕ) : Measure (Prefix n) :=
  Measure.pi fun _ : ↑(Finset.range n) ↦ directionLaw

theorem increment_restrict_map (n : ℕ) :
    incrementLaw.map (Finset.range n).restrict = prefixLaw n := by
  simpa [incrementLaw, prefixLaw, directionLaw] using
    (Measure.infinitePi_map_restrict
      (fun _ : ℕ ↦ (PMF.uniformOfFintype Direction).toMeasure)
      (I := Finset.range n))

theorem prefixLaw_singleton (n : ℕ) (w : Prefix n) :
    prefixLaw n {w} = (4 : ENNReal)⁻¹ ^ n := by
  change (Measure.pi fun _ : ↑(Finset.range n) ↦ directionLaw) {w} = _
  rw [← Measure.infinitePi_eq_pi]
  rw [Measure.infinitePi_singleton_of_fintype]
  simp [directionLaw]

theorem return_prob_eq_card_div_pow (n : ℕ) :
    incrementLaw {ω | simpleRandomWalk ω n = (0, 0)} =
      (returningPrefixes n).card / (4 : ENNReal) ^ n := by
  let A := returningPrefixes n
  calc
    incrementLaw {ω | simpleRandomWalk ω n = (0, 0)} =
        (incrementLaw.map (Finset.range n).restrict) (A : Set (Prefix n)) := by
      rw [Measure.map_apply]
      · congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Finset.mem_coe,
          A, returningPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [finitePosition_restrict]
      · fun_prop
      · measurability
    _ = prefixLaw n (A : Set (Prefix n)) := by rw [increment_restrict_map]
    _ = ∑ w ∈ A, prefixLaw n {w} := by rw [sum_measure_singleton]
    _ = ∑ _w ∈ A, (4 : ENNReal)⁻¹ ^ n := by
      apply Finset.sum_congr rfl
      intro w _
      exact prefixLaw_singleton n w
    _ = (A.card : ENNReal) / (4 : ENNReal) ^ n := by
      simp [div_eq_mul_inv, ENNReal.inv_pow]
    _ = (returningPrefixes n).card / (4 : ENNReal) ^ n := by rfl

theorem prefixLaw_return (n : ℕ) :
    prefixLaw n {w | finitePosition w = (0, 0)} =
      incrementLaw {ω | simpleRandomWalk ω n = (0, 0)} := by
  symm
  calc
    incrementLaw {ω | simpleRandomWalk ω n = (0, 0)} =
        (incrementLaw.map (Finset.range n).restrict)
          {w | finitePosition w = (0, 0)} := by
      rw [Measure.map_apply]
      · congr 1
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [finitePosition_restrict]
      · fun_prop
      · measurability
    _ = prefixLaw n {w | finitePosition w = (0, 0)} := by rw [increment_restrict_map]

/-! A diagonal-coordinate bijection for the exact count at even times. -/

def directionBitsFun (d : Direction) : Bool × Bool :=
  match d.1 with
  | 0 => (false, false)
  | 1 => (true, true)
  | 2 => (false, true)
  | _ => (true, false)

def bitsDirectionFun (b : Bool × Bool) : Direction :=
  match b with
  | (false, false) => 0
  | (true, true) => 1
  | (false, true) => 2
  | (true, false) => 3

def directionBitsEquiv : Direction ≃ Bool × Bool where
  toFun := directionBitsFun
  invFun := bitsDirectionFun
  left_inv d := by fin_cases d <;> simp [directionBitsFun, bitsDirectionFun]
  right_inv b := by
    rcases b with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂ <;> simp [directionBitsFun, bitsDirectionFun]

def prefixBitsEquiv (n : ℕ) : Prefix n ≃
    ((↑(Finset.range n) → Bool) × (↑(Finset.range n) → Bool)) where
  toFun w := (fun i ↦ (directionBitsEquiv (w i)).1,
    fun i ↦ (directionBitsEquiv (w i)).2)
  invFun uv i := directionBitsEquiv.symm (uv.1 i, uv.2 i)
  left_inv w := by
    funext i
    simp
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext <;> funext i <;> simp

def boolSign (b : Bool) : ℤ := if b then -1 else 1

theorem diagonal_step_one (d : Direction) :
    stepX d + stepY d = boolSign (directionBitsEquiv d).1 := by
  fin_cases d <;>
    norm_num [stepX, stepY, directionStep, directionBitsEquiv, directionBitsFun, boolSign]

theorem diagonal_step_two (d : Direction) :
    stepX d - stepY d = boolSign (directionBitsEquiv d).2 := by
  fin_cases d <;>
    norm_num [stepX, stepY, directionStep, directionBitsEquiv, directionBitsFun, boolSign]

def truePositions {I : Type*} [Fintype I] [DecidableEq I] (u : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ u i = true

def boolFunEquivFinset (I : Type*) [Fintype I] [DecidableEq I] : (I → Bool) ≃ Finset I where
  toFun := truePositions
  invFun A i := decide (i ∈ A)
  left_inv u := by
    funext i
    simp [truePositions]
  right_inv A := by
    ext i
    simp [truePositions]

def BalancedBits (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :=
  {u : I → Bool // (truePositions u).card = j}

def balancedBitsEquivPowersetCard (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    BalancedBits I j ≃ Set.powersetCard I j :=
  (boolFunEquivFinset I).subtypeEquiv fun _ ↦ Iff.rfl

noncomputable instance (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    Fintype (BalancedBits I j) :=
  Fintype.ofEquiv (Set.powersetCard I j) (balancedBitsEquivPowersetCard I j).symm

theorem card_balancedBits (I : Type*) [Fintype I] [DecidableEq I] (j : ℕ) :
    Fintype.card (BalancedBits I j) = (Fintype.card I).choose j := by
  rw [Fintype.card_congr (balancedBitsEquivPowersetCard I j)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]

theorem sum_boolSign_eq_card_sub_twice {I : Type*} [Fintype I] [DecidableEq I]
    (u : I → Bool) :
    ∑ i, boolSign (u i) = (Fintype.card I : ℤ) - 2 * (truePositions u).card := by
  classical
  calc
    ∑ i, boolSign (u i) =
        ∑ i, ((1 : ℤ) - 2 * if u i = true then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      cases u i <;> simp [boolSign]
    _ = (Fintype.card I : ℤ) - 2 * (truePositions u).card := by
      simp [truePositions, Finset.sum_sub_distrib]
      calc
        ∑ x, (if u x = true then (2 : ℤ) else 0) =
            ∑ x, 2 * (if u x = true then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> norm_num
        _ = 2 * ∑ x, (if u x = true then (1 : ℤ) else 0) := by
          rw [Finset.mul_sum]
        _ = 2 * (truePositions u).card := by simp [truePositions]

theorem sum_boolSign_eq_zero_iff {I : Type*} [Fintype I] [DecidableEq I]
    (j : ℕ) (hcard : Fintype.card I = 2 * j) (u : I → Bool) :
    (∑ i, boolSign (u i)) = 0 ↔ (truePositions u).card = j := by
  rw [sum_boolSign_eq_card_sub_twice, hcard]
  constructor <;> intro h
  · exact_mod_cast (by omega : (truePositions u).card = j)
  · omega

theorem diagonal_sum_one {n : ℕ} (w : Prefix n) :
    ∑ i, boolSign (directionBitsEquiv (w i)).1 =
      (finitePosition w).1 + (finitePosition w).2 := by
  calc
    ∑ i, boolSign (directionBitsEquiv (w i)).1 =
        ∑ i, (stepX (w i) + stepY (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (diagonal_step_one (w i)).symm
    _ = (∑ i, stepX (w i)) + ∑ i, stepY (w i) := Finset.sum_add_distrib
    _ = (finitePosition w).1 + (finitePosition w).2 := by
      simp [finitePosition, stepX, stepY, Prod.fst_sum, Prod.snd_sum]

theorem diagonal_sum_two {n : ℕ} (w : Prefix n) :
    ∑ i, boolSign (directionBitsEquiv (w i)).2 =
      (finitePosition w).1 - (finitePosition w).2 := by
  calc
    ∑ i, boolSign (directionBitsEquiv (w i)).2 =
        ∑ i, (stepX (w i) - stepY (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (diagonal_step_two (w i)).symm
    _ = (∑ i, stepX (w i)) - ∑ i, stepY (w i) := by
      simpa using (Finset.sum_sub_distrib (s := Finset.univ)
        (fun i ↦ stepX (w i)) (fun i ↦ stepY (w i)))
    _ = (finitePosition w).1 - (finitePosition w).2 := by
      simp [finitePosition, stepX, stepY, Prod.fst_sum, Prod.snd_sum]

theorem finitePosition_eq_zero_iff_diagonal {n : ℕ} (w : Prefix n) :
    finitePosition w = (0, 0) ↔
      (∑ i, boolSign (directionBitsEquiv (w i)).1) = 0 ∧
      (∑ i, boolSign (directionBitsEquiv (w i)).2) = 0 := by
  rw [diagonal_sum_one, diagonal_sum_two]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    apply Prod.ext <;> dsimp
    · omega
    · omega

theorem finitePosition_eq_zero_iff_balanced (j : ℕ) (w : Prefix (2 * j)) :
    finitePosition w = (0, 0) ↔
      (truePositions (prefixBitsEquiv (2 * j) w).1).card = j ∧
      (truePositions (prefixBitsEquiv (2 * j) w).2).card = j := by
  rw [finitePosition_eq_zero_iff_diagonal]
  change (∑ i, boolSign ((prefixBitsEquiv (2 * j) w).1 i)) = 0 ∧
      (∑ i, boolSign ((prefixBitsEquiv (2 * j) w).2 i)) = 0 ↔ _
  rw [sum_boolSign_eq_zero_iff j (by simp), sum_boolSign_eq_zero_iff j (by simp)]

def returningEquivBalanced (j : ℕ) :
    ↑(returningPrefixes (2 * j)) ≃
      BalancedBits (↑(Finset.range (2 * j))) j ×
        BalancedBits (↑(Finset.range (2 * j))) j where
  toFun w := by
    have hwzero : finitePosition w.1 = (0, 0) := by
      simpa [returningPrefixes] using w.2
    have hwbal := (finitePosition_eq_zero_iff_balanced j w.1).mp hwzero
    exact (⟨(prefixBitsEquiv (2 * j) w.1).1, hwbal.1⟩,
      ⟨(prefixBitsEquiv (2 * j) w.1).2, hwbal.2⟩)
  invFun uv := by
    let w := (prefixBitsEquiv (2 * j)).symm (uv.1.1, uv.2.1)
    refine ⟨w, ?_⟩
    simp only [returningPrefixes, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (finitePosition_eq_zero_iff_balanced j w).mpr
    simpa [w] using And.intro uv.1.2 uv.2.2
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem returningPrefixes_card_even (j : ℕ) :
    (returningPrefixes (2 * j)).card = ((2 * j).choose j) ^ 2 := by
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (returningEquivBalanced j), Fintype.card_prod,
    card_balancedBits]
  simp [pow_two]

theorem return_prob_even (j : ℕ) :
    incrementLaw {ω | simpleRandomWalk ω (2 * j) = (0, 0)} =
      (((2 * j).choose j : ENNReal) ^ 2) / (4 : ENNReal) ^ (2 * j) := by
  rw [return_prob_eq_card_div_pow, returningPrefixes_card_even]
  norm_cast

theorem finitePosition_ne_zero_odd (j : ℕ) (w : Prefix (2 * j + 1)) :
    finitePosition w ≠ (0, 0) := by
  intro hw
  have hdiag := (finitePosition_eq_zero_iff_diagonal w).mp hw
  have hsum := hdiag.1
  rw [sum_boolSign_eq_card_sub_twice] at hsum
  simp only [Fintype.card_coe, Finset.card_range] at hsum
  omega

theorem returningPrefixes_card_odd (j : ℕ) :
    (returningPrefixes (2 * j + 1)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  have hwzero := (Finset.mem_filter.mp hw).2
  exact finitePosition_ne_zero_odd j w hwzero

theorem return_prob_odd (j : ℕ) :
    incrementLaw {ω | simpleRandomWalk ω (2 * j + 1) = (0, 0)} = 0 := by
  rw [return_prob_eq_card_div_pow, returningPrefixes_card_odd]
  simp

theorem succ_mul_centralBinom_sq_le_sixteen_pow : ∀ j : ℕ,
    (j + 1) * Nat.centralBinom j ^ 2 ≤ 16 ^ j := by
  intro j
  induction j with
  | zero => norm_num [Nat.centralBinom]
  | succ j ih =>
      have hrec := Nat.succ_mul_centralBinom_succ j
      have hsq := congrArg (fun x : ℕ ↦ x ^ 2) hrec
      have hpoly : (j + 2) * (2 * j + 1) ^ 2 ≤ 4 * (j + 1) ^ 3 := by nlinarith
      have hmul : (j + 1) ^ 2 *
            ((j + 2) * Nat.centralBinom (j + 1) ^ 2) ≤
          (j + 1) ^ 2 * 16 ^ (j + 1) := by
        calc
          (j + 1) ^ 2 * ((j + 2) * Nat.centralBinom (j + 1) ^ 2) =
              (j + 2) * ((j + 1) * Nat.centralBinom (j + 1)) ^ 2 := by ring
          _ = (j + 2) * (2 * (2 * j + 1) * Nat.centralBinom j) ^ 2 := by rw [hsq]
          _ = 4 * ((j + 2) * (2 * j + 1) ^ 2) * Nat.centralBinom j ^ 2 := by ring
          _ ≤ 4 * (4 * (j + 1) ^ 3) * Nat.centralBinom j ^ 2 := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hpoly) le_rfl
          _ = 16 * (j + 1) ^ 2 * ((j + 1) * Nat.centralBinom j ^ 2) := by ring
          _ ≤ 16 * (j + 1) ^ 2 * 16 ^ j := Nat.mul_le_mul_left _ ih
          _ = (j + 1) ^ 2 * 16 ^ (j + 1) := by rw [pow_succ]; ring
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        Nat.le_of_mul_le_mul_left hmul (by positivity)

theorem choose_sq_le_sixteen_pow (j : ℕ) :
    (j + 1) * ((2 * j).choose j) ^ 2 ≤ 16 ^ j := by
  simpa [Nat.centralBinom_eq_two_mul_choose] using
    succ_mul_centralBinom_sq_le_sixteen_pow j

theorem return_real_even (j : ℕ) :
    incrementLaw.real {ω | simpleRandomWalk ω (2 * j) = (0, 0)} =
      (((2 * j).choose j : ℝ) ^ 2) / (4 : ℝ) ^ (2 * j) := by
  rw [Measure.real, return_prob_even]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]

theorem return_real_odd (j : ℕ) :
    incrementLaw.real {ω | simpleRandomWalk ω (2 * j + 1) = (0, 0)} = 0 := by
  rw [Measure.real, return_prob_odd]
  rfl

theorem return_real_le_two_div_succ (d : ℕ) :
    incrementLaw.real {ω | simpleRandomWalk ω d = (0, 0)} ≤ 2 / (d + 1 : ℝ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' d
  · rw [return_real_even]
    have hbinom :
        ((j + 1 : ℕ) : ℝ) * (((2 * j).choose j : ℝ) ^ 2) ≤ (16 : ℝ) ^ j := by
      exact_mod_cast choose_sq_le_sixteen_pow j
    have hpow : (4 : ℝ) ^ (2 * j) = 16 ^ j := by
      rw [pow_mul]
      norm_num
    rw [hpow]
    have hcalc :
        (((2 * j).choose j : ℝ) ^ 2) / (16 : ℝ) ^ j ≤
          2 / (((2 * j + 1 : ℕ) : ℝ)) := by
      calc
        (((2 * j).choose j : ℝ) ^ 2) / (16 : ℝ) ^ j ≤
            1 / (j + 1 : ℝ) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          simpa [mul_comm] using hbinom
        _ ≤ 2 / (((2 * j + 1 : ℕ) : ℝ)) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          norm_num
          linarith
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcalc
  · rw [return_real_odd]
    positivity

namespace CollisionKernel

abbrev TimeTuple (n r : ℕ) := Fin r → Fin (n + 1)

def timeGaps (n k : ℕ) (t : TimeTuple n (k + 1)) : Fin k → Fin (n + 1) :=
  fun i ↦ ⟨(t i.succ).val - (t i.castSucc).val, by omega⟩

abbrev GapIndex {n k : ℕ} (t : TimeTuple n (k + 1)) (i : Fin k) :=
  ↑(Finset.range (timeGaps n k t i).val)

def blockCoord {n k : ℕ} (t : TimeTuple n (k + 1))
    (p : (i : Fin k) × GapIndex t i) : ℕ :=
  (t p.1.castSucc).val + p.2.val

def extractBlocks {n k : ℕ} (t : TimeTuple n (k + 1))
    (ω : ℕ → Direction) : (i : Fin k) → GapIndex t i → Direction :=
  fun i j ↦ ω (blockCoord t ⟨i, j⟩)

theorem measurable_extractBlocks {n k : ℕ} (t : TimeTuple n (k + 1)) :
    Measurable (extractBlocks t) := by
  unfold extractBlocks
  fun_prop

theorem blockCoord_injective {n k : ℕ} {t : TimeTuple n (k + 1)}
    (ht : Monotone t) : Function.Injective (blockCoord t) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have ha_lt : (t i.castSucc).val + a.val < (t i.succ).val := by
    have hmono : (t i.castSucc).val ≤ (t i.succ).val :=
      Fin.val_le_of_le (ht (Fin.castSucc_le_succ i))
    have ha := a.2
    simp only [Finset.mem_range] at ha
    simp only [timeGaps] at ha
    omega
  have hb_lt : (t j.castSucc).val + b.val < (t j.succ).val := by
    have hmono : (t j.castSucc).val ≤ (t j.succ).val :=
      Fin.val_le_of_le (ht (Fin.castSucc_le_succ j))
    have hb := b.2
    simp only [Finset.mem_range] at hb
    simp only [timeGaps] at hb
    omega
  have hij : i = j := by
    apply le_antisymm
    · by_contra hji
      have hji' : j < i := lt_of_not_ge hji
      have hindex : j.succ ≤ i.castSucc := by
        exact Fin.mk_le_mk.mpr (by omega)
      have hcross := Fin.val_le_of_le (ht hindex)
      simp only [blockCoord] at hab
      omega
    · by_contra hij
      have hij' : i < j := lt_of_not_ge hij
      have hindex : i.succ ≤ j.castSucc := by
        exact Fin.mk_le_mk.mpr (by omega)
      have hcross := Fin.val_le_of_le (ht hindex)
      simp only [blockCoord] at hab
      omega
  subst j
  have hab' : a = b := by
    apply Subtype.ext
    simp only [blockCoord] at hab
    omega
  subst b
  rfl

noncomputable abbrev blockLaw {n k : ℕ} (t : TimeTuple n (k + 1)) (i : Fin k) :
    Measure (GapIndex t i → Direction) :=
  Measure.infinitePi fun _ : GapIndex t i ↦ directionLaw

theorem extractBlocks_map {n k : ℕ} {t : TimeTuple n (k + 1)} (ht : Monotone t) :
    incrementLaw.map (extractBlocks t) = Measure.infinitePi (blockLaw t) := by
  let flat : (ℕ → Direction) → ((i : Fin k) × GapIndex t i) → Direction :=
    fun ω p ↦ ω (blockCoord t p)
  let curryEquiv := MeasurableEquiv.piCurry (fun i : Fin k ↦ fun _ : GapIndex t i ↦ Direction)
  have hfun : extractBlocks t = curryEquiv ∘ flat := by
    funext ω i j
    rfl
  rw [hfun, ← Measure.map_map curryEquiv.measurable (by fun_prop)]
  unfold incrementLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj (blockCoord_injective ht)]
  simpa [blockLaw, directionLaw, curryEquiv] using
    (Measure.infinitePi_map_piCurry
      (fun i : Fin k ↦ fun _ : GapIndex t i ↦
        (PMF.uniformOfFintype Direction).toMeasure))

theorem finitePosition_extractBlock {n k : ℕ} {t : TimeTuple n (k + 1)}
    (ht : Monotone t) (i : Fin k) (ω : ℕ → Direction) :
    finitePosition (extractBlocks t ω i) =
      simpleRandomWalk ω (t i.succ).val - simpleRandomWalk ω (t i.castSucc).val := by
  have hab : (t i.castSucc).val ≤ (t i.succ).val :=
    Fin.val_le_of_le (ht (Fin.castSucc_le_succ i))
  let a := (t i.castSucc).val
  let b := (t i.succ).val
  let f : ℕ → Site := fun m ↦ directionStep (ω m)
  calc
    finitePosition (extractBlocks t ω i) =
        ∑ m ∈ Finset.range (b - a), f (a + m) := by
      change (∑ m : GapIndex t i, directionStep (ω (a + m.val))) = _
      calc
        (∑ m : GapIndex t i, directionStep (ω (a + m.val))) =
            ∑ m ∈ (Finset.range (b - a)).attach,
              directionStep (ω (a + m.val)) := by
          apply Finset.sum_congr
          · exact Finset.univ_eq_attach (Finset.range (b - a))
          · intro _ _
            rfl
        _ = ∑ m ∈ Finset.range (b - a), f (a + m) :=
          Finset.sum_attach (Finset.range (b - a)) (fun m ↦ f (a + m))
    _ = ∑ m ∈ Finset.Ico a b, f m := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ = (∑ m ∈ Finset.range b, f m) - ∑ m ∈ Finset.range a, f m :=
      Finset.sum_Ico_eq_sub f hab
    _ = simpleRandomWalk ω (t i.succ).val -
        simpleRandomWalk ω (t i.castSucc).val := by
      rfl

theorem allEqual_iff_adjacent {k : ℕ} {A : Type*} (f : Fin (k + 1) → A) :
    (∀ i j, f i = f j) ↔ ∀ i : Fin k, f i.succ = f i.castSucc := by
  constructor
  · intro h i
    exact h _ _
  · intro h
    have hz : ∀ i : Fin (k + 1), f i = f 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => exact (h i).trans ih
    intro i j
    exact (hz i).trans (hz j).symm

def collisionSet {n k : ℕ} (t : TimeTuple n (k + 1)) : Set (ℕ → Direction) :=
  {ω | ∀ i j, simpleRandomWalk ω (t i).val = simpleRandomWalk ω (t j).val}

def blockReturnSet {n k : ℕ} (t : TimeTuple n (k + 1)) (i : Fin k) :
    Set (GapIndex t i → Direction) :=
  {w | finitePosition w = (0, 0)}

theorem measurableSet_blockReturnSet {n k : ℕ} (t : TimeTuple n (k + 1)) (i : Fin k) :
    MeasurableSet (blockReturnSet t i) := by
  change MeasurableSet ((fun w : GapIndex t i → Direction ↦ finitePosition w) ⁻¹' {(0, 0)})
  apply (show Measurable (fun w : GapIndex t i → Direction ↦ finitePosition w) by
    unfold finitePosition
    fun_prop)
  measurability

theorem collisionSet_preimage_blocks {n k : ℕ} {t : TimeTuple n (k + 1)}
    (ht : Monotone t) :
    collisionSet t = extractBlocks t ⁻¹' (Set.univ.pi (blockReturnSet t)) := by
  ext ω
  simp only [collisionSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    forall_const, blockReturnSet]
  rw [allEqual_iff_adjacent]
  apply forall_congr'
  intro i
  rw [finitePosition_extractBlock ht]
  exact (sub_eq_zero).symm

theorem blockLaw_return {n k : ℕ} (t : TimeTuple n (k + 1)) (i : Fin k) :
    blockLaw t i (blockReturnSet t i) =
      incrementLaw {ω | simpleRandomWalk ω (timeGaps n k t i).val = (0, 0)} := by
  change (Measure.infinitePi fun _ : GapIndex t i ↦ directionLaw)
      {w | finitePosition w = (0, 0)} = _
  rw [Measure.infinitePi_eq_pi]
  exact prefixLaw_return (timeGaps n k t i).val

theorem collision_measure_eq_prod_return {n k : ℕ} {t : TimeTuple n (k + 1)}
    (ht : Monotone t) :
    incrementLaw (collisionSet t) =
      ∏ i : Fin k,
        incrementLaw {ω | simpleRandomWalk ω (timeGaps n k t i).val = (0, 0)} := by
  rw [collisionSet_preimage_blocks ht]
  rw [← Measure.map_apply (measurable_extractBlocks t) (by
    exact MeasurableSet.univ_pi fun i ↦ measurableSet_blockReturnSet t i)]
  rw [extractBlocks_map ht]
  rw [Measure.infinitePi_pi_univ (blockLaw t)
    (fun i ↦ measurableSet_blockReturnSet t i)]
  simp only [tprod_fintype, blockLaw_return]

noncomputable def returnKernel (n : ℕ) (d : Fin (n + 1)) : ℝ :=
  incrementLaw.real {ω | simpleRandomWalk ω d.val = (0, 0)}

def gapWeight (n k : ℕ) (q : Fin (n + 1) → ℝ) (t : TimeTuple n (k + 1)) : ℝ :=
  ∏ i : Fin k, q (timeGaps n k t i)

theorem collision_real_eq_gapWeight {n k : ℕ} {t : TimeTuple n (k + 1)}
    (ht : Monotone t) :
    incrementLaw.real (collisionSet t) = gapWeight n k (returnKernel n) t := by
  have h := congrArg ENNReal.toReal (collision_measure_eq_prod_return ht)
  simpa [Measure.real, gapWeight, returnKernel, ENNReal.toReal_prod] using h

theorem sum_returnKernel_le (n : ℕ) :
    ∑ d : Fin (n + 1), returnKernel n d ≤
      2 * (1 + Real.log (n + 1 : ℝ)) := by
  calc
    ∑ d : Fin (n + 1), returnKernel n d ≤
        ∑ d : Fin (n + 1), 2 / (d.val + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact return_real_le_two_div_succ d.val
    _ = ∑ m ∈ Finset.range (n + 1), 2 / (m + 1 : ℝ) := by
      exact Fin.sum_univ_eq_sum_range (fun m : ℕ ↦ 2 / (m + 1 : ℝ)) (n + 1)
    _ = ∑ m ∈ Finset.range (n + 1),
        2 * (1 / (m + 1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [div_eq_mul_inv, one_div]
    _ = 2 * ∑ m ∈ Finset.range (n + 1), 1 / (m + 1 : ℝ) := by
      rw [Finset.mul_sum]
    _ = 2 * (harmonic (n + 1) : ℝ) := by
      congr 1
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv]
    _ ≤ 2 * (1 + Real.log (n + 1 : ℝ)) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)

theorem sum_returnKernel_dyadic_le (k : ℕ) (hk : 1 ≤ k) :
    ∑ d : Fin (2 ^ k + 1), returnKernel (2 ^ k) d ≤ 6 * k := by
  refine (sum_returnKernel_le (2 ^ k)).trans ?_
  have hpow : (2 : ℕ) ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_two_pow
    omega
  have hpowR : ((2 : ℕ) ^ k + 1 : ℕ) ≤ 2 ^ (k + 1) := hpow
  have hlog : Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) ≤
      Real.log ((2 : ℝ) ^ (k + 1)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hpowR
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log 2 ≤ 1 :=
    le_trans Real.log_two_lt_d9.le (by norm_num)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogupper : Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
    calc
      Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) ≤
          ((k : ℝ) + 1) * Real.log 2 := by simpa using hlog
      _ ≤ ((k : ℝ) + 1) * 1 := by gcongr
      _ = (k : ℝ) + 1 := by ring
  push_cast
  norm_num [Nat.cast_pow] at hlogupper ⊢
  nlinarith

end CollisionKernel


/-- Sites visited by a path through time `n`, including times `0` and `n`. -/
def visitedSites (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (Finset.range (n + 1)).image s

/-- Number of visits to `x` through time `n`, including times `0` and `n`. -/
def localTime (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((Finset.range (n + 1)).filter fun j ↦ s j = x).card

/-- Local time at a fixed site and time is measurable as a function of the
path. -/
theorem measurable_localTime_eval (n : ℕ) (x : Site) :
    Measurable fun s : ℕ → Site ↦ localTime s n x := by
  unfold localTime
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_pi_apply j) measurable_const
  · exact measurable_const
  · exact measurable_const

/-- Joint measurability of finite-horizon local time in the path and site. -/
theorem measurable_localTime (n : ℕ) :
    Measurable fun p : (ℕ → Site) × Site ↦ localTime p.1 n p.2 := by
  unfold localTime
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite
  · exact measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst) measurable_snd
  · exact measurable_const
  · exact measurable_const

/-- The largest local time of a site visited through time `n`. -/
def maxLocalTime (s : ℕ → Site) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup fun j ↦ localTime s n (s j)

/-- The finite-horizon maximal local time is measurable as a function of the
path.  This permits Markov bounds for its dyadic bad events. -/
theorem measurable_maxLocalTime_eval (n : ℕ) :
    Measurable fun s : ℕ → Site ↦ maxLocalTime s n := by
  unfold maxLocalTime
  let hs : (Finset.range (n + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (by omega)
  let f : ℕ → (ℕ → Site) → ℕ := fun j s ↦ localTime s n (s j)
  have hmf : ∀ j ∈ Finset.range (n + 1), Measurable (f j) := by
    intro j _
    exact (measurable_localTime n).comp (measurable_id.prodMk (measurable_pi_apply j))
  have hm : Measurable ((Finset.range (n + 1)).sup' hs f) :=
    Finset.measurable_sup' hs hmf
  rw [Finset.sup'_eq_sup hs] at hm
  have heq : (Finset.range (n + 1)).sup f =
      fun s ↦ (Finset.range (n + 1)).sup fun j ↦ localTime s n (s j) := by
    funext s
    exact Finset.sup_apply _ _ _
  rw [heq] at hm
  exact hm

/-! ### Kac moments for the canonical planar walk -/

/-- The canonical walk, restricted to the finite time interval `0, ..., n`. -/
def finiteCoordinateProcess (n : ℕ) (ω : ℕ → Direction) (i : Fin (n + 1)) : Site :=
  simpleRandomWalk ω i.val

theorem measurable_finiteCoordinateProcess (n : ℕ) :
    Measurable (finiteCoordinateProcess n) := by
  unfold finiteCoordinateProcess simpleRandomWalk
  fun_prop

theorem measurableSet_kacCollision (n r : ℕ) (t : KacMoment.TimeTuple n r) :
    MeasurableSet (KacMoment.collisionSet n r (finiteCoordinateProcess n) t) := by
  unfold KacMoment.collisionSet KacMoment.allEqualAlong
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_eq_fun
    ((measurable_pi_apply (t i).val).comp measurable_simpleRandomWalk)
    ((measurable_pi_apply (t j).val).comp measurable_simpleRandomWalk)

theorem kacCollision_eq_collisionKernel {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    KacMoment.collisionSet n (k + 1) (finiteCoordinateProcess n) t =
      CollisionKernel.collisionSet t := by
  rfl

theorem kacTimeGaps_eq_kernelTimeGaps {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1)) :
    KacMoment.timeGaps n k t = CollisionKernel.timeGaps n k t := by
  rfl

/-- Exact collision factorization supplies the probabilistic kernel hypothesis
in the abstract Kac moment inequality. -/
theorem canonical_kac_kernel {n k : ℕ}
    (t : KacMoment.TimeTuple n (k + 1))
    (ht : t ∈ KacMoment.sortedTuples n (k + 1)) :
    incrementLaw.real
        (KacMoment.collisionSet n (k + 1) (finiteCoordinateProcess n) t) ≤
      KacMoment.gapWeight n k (CollisionKernel.returnKernel n) t := by
  have htmono : Monotone t := by simpa [KacMoment.sortedTuples] using ht
  rw [kacCollision_eq_collisionKernel]
  have h := CollisionKernel.collision_real_eq_gapWeight htmono
  simpa [KacMoment.gapWeight, CollisionKernel.gapWeight,
    kacTimeGaps_eq_kernelTimeGaps] using h.le

/-- Kac's moment bound for the canonical planar simple random walk. -/
theorem canonical_kac_moment (n k : ℕ) :
    ∫ ω, KacMoment.localMoment n (k + 1) (finiteCoordinateProcess n) ω ∂incrementLaw ≤
      ((k + 1).factorial : ℝ) * (n + 1) *
        (∑ d : Fin (n + 1), CollisionKernel.returnKernel n d) ^ k := by
  apply KacMoment.kac_moment_bound_of_collision_kernel
  · exact measurableSet_kacCollision n (k + 1)
  · intro d
    exact measureReal_nonneg
  · exact canonical_kac_kernel

theorem canonical_kac_moment_order (n r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, KacMoment.localMoment n r (finiteCoordinateProcess n) ω ∂incrementLaw ≤
      (r.factorial : ℝ) * (n + 1) *
        (2 * (1 + Real.log (n + 1 : ℝ))) ^ (r - 1) := by
  have hm := canonical_kac_moment n (r - 1)
  have hsum := CollisionKernel.sum_returnKernel_le n
  rw [Nat.sub_add_cancel hr] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg) hsum (r - 1))
    (by positivity))

theorem dyadic_green_le_six_mul (k : ℕ) (hk : 1 ≤ k) :
    2 * (1 + Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ)) ≤ 6 * k := by
  have hnat : (2 : ℕ) ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have : 1 ≤ (2 : ℕ) ^ k := one_le_pow₀ (by norm_num)
    omega
  have hreal : (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hnat
  have hlog : Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) ≤
      Real.log ((2 : ℝ) ^ (k + 1)) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) by positivity))
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (2 : ℝ) ^ (k + 1) by positivity))
      hreal
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast at hlog
  have hmul : ((k : ℝ) + 1) * Real.log 2 ≤ ((k : ℝ) + 1) * 1 :=
    mul_le_mul_of_nonneg_left hlogtwo (by positivity)
  have hlogbound := hlog.trans (by simpa using hmul)
  push_cast
  nlinarith

theorem finiteLocalTime_finiteCoordinateProcess (s : ℕ → Site) (n : ℕ) (x : Site) :
    KacMoment.finiteLocalTime n (fun i : Fin (n + 1) ↦ s i.val) x =
      localTime s n x := by
  rw [KacMoment.finiteLocalTime, localTime,
    Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ if s j = x then 1 else 0) (n + 1)

theorem finiteMaxLocalTime_finiteCoordinateProcess (s : ℕ → Site) (n : ℕ) :
    KacMoment.finiteMaxLocalTime n (fun i : Fin (n + 1) ↦ s i.val) =
      maxLocalTime s n := by
  unfold KacMoment.finiteMaxLocalTime maxLocalTime
  simp_rw [finiteLocalTime_finiteCoordinateProcess]
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (s := Finset.range (n + 1))
      (f := fun j ↦ localTime s n (s j)) (Finset.mem_range.mpr i.isLt)
  · apply Finset.sup_le
    intro j hj
    let i : Fin (n + 1) := ⟨j, Finset.mem_range.mp hj⟩
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun i : Fin (n + 1) ↦ localTime s n (s i.val)) (Finset.mem_univ i)

/-- The explicit dyadic maximal-local-time tail bound under the increment law. -/
theorem canonical_dyadic_maxLocalTime_tail (k : ℕ) (hk : 1 ≤ k) :
    incrementLaw.real
        {ω | 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)} ≤
      2 * ((4 : ℝ)⁻¹) ^ k := by
  let G : ℝ := 2 * (1 + Real.log (((2 : ℕ) ^ k + 1 : ℕ) : ℝ))
  have hG0 : 0 ≤ G := by
    dsimp [G]
    have honeNat : 1 ≤ (2 : ℕ) ^ k + 1 := by
      exact Nat.le_add_left 1 ((2 : ℕ) ^ k)
    have hone : (1 : ℝ) ≤ (((2 : ℕ) ^ k + 1 : ℕ) : ℝ) := by
      exact_mod_cast honeNat
    exact mul_nonneg (by norm_num) (add_nonneg (by norm_num) (Real.log_nonneg hone))
  have hG : G ≤ 6 * k := dyadic_green_le_six_mul k hk
  have hKac := canonical_kac_moment_order ((2 : ℕ) ^ k) k hk
  have hTail := KacMoment.dyadic_maxLocalTime_tail
    (Site := Site) k hk (finiteCoordinateProcess ((2 : ℕ) ^ k)) incrementLaw
    (measurableSet_kacCollision ((2 : ℕ) ^ k) k) G hG0 hG (by
      simpa [G, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using hKac)
  have hevent :
      {ω | 48 * k ^ 2 ≤
        KacMoment.finiteMaxLocalTime ((2 : ℕ) ^ k)
          (finiteCoordinateProcess ((2 : ℕ) ^ k) ω)} =
      {ω | 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show finiteCoordinateProcess ((2 : ℕ) ^ k) ω =
        (fun i : Fin ((2 : ℕ) ^ k + 1) ↦ simpleRandomWalk ω i.val) from rfl]
    rw [finiteMaxLocalTime_finiteCoordinateProcess]
  rw [← hevent]
  exact hTail

theorem canonical_dyadic_maxLocalTime_tail_ennreal (k : ℕ) (hk : 1 ≤ k) :
    incrementLaw
        {ω | 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)} ≤
      2 * ((4 : ENNReal)⁻¹) ^ k := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top incrementLaw _)]
  have h := ENNReal.ofReal_le_ofReal (canonical_dyadic_maxLocalTime_tail k hk)
  calc
    ENNReal.ofReal (incrementLaw.real
        {ω | 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)}) ≤
        ENNReal.ofReal (2 * ((4 : ℝ)⁻¹) ^ k) := h
    _ = 2 * ((4 : ENNReal)⁻¹) ^ k := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)), ENNReal.ofReal_pow,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
      all_goals try positivity
      norm_num

namespace HLOZFoundation

/-- The coordinate process on the canonical path space. -/
def coordinateProcess (n : ℕ) (s : ℕ → Site) : Site := s n

theorem measurable_coordinateProcess (n : ℕ) : Measurable (coordinateProcess n) := by
  exact measurable_pi_apply n

/-- The natural filtration of the canonical coordinate process. -/
noncomputable def canonicalFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site)) :=
  Filtration.natural coordinateProcess fun n ↦
    (measurable_coordinateProcess n).stronglyMeasurable

theorem adapted_coordinateProcess : Adapted canonicalFiltration coordinateProcess := by
  simpa [canonicalFiltration] using (Filtration.stronglyAdapted_natural
    (u := coordinateProcess)
    (fun n ↦ (measurable_coordinateProcess n).stronglyMeasurable)).adapted

/-- The indicator that the coordinate process visits `x` at time `j`. -/
def visitIndicator (x : Site) (j : ℕ) (s : ℕ → Site) : ℕ :=
  if s j = x then 1 else 0

theorem measurable_visitIndicator_le (x : Site) {j n : ℕ} (hjn : j ≤ n) :
    Measurable[canonicalFiltration n] (visitIndicator x j) := by
  have hcoord : Measurable[canonicalFiltration n] (coordinateProcess j) :=
    adapted_coordinateProcess.measurable_le hjn
  have hset : MeasurableSet[canonicalFiltration n]
      {s : ℕ → Site | coordinateProcess j s = x} :=
    hcoord (measurableSet_singleton x)
  exact Measurable.ite hset measurable_const measurable_const

theorem localTime_eq_sum_visitIndicator (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s n x = ∑ j ∈ Finset.range (n + 1), visitIndicator x j s := by
  simp [localTime, visitIndicator]

theorem adapted_localTime (x : Site) :
    Adapted canonicalFiltration (fun n s ↦ localTime s n x) := by
  intro n
  change Measurable[canonicalFiltration n] (fun s ↦ localTime s n x)
  rw [show (fun s ↦ localTime s n x) =
      fun s ↦ ∑ j ∈ Finset.range (n + 1), visitIndicator x j s by
    funext s
    exact localTime_eq_sum_visitIndicator s n x]
  exact Finset.measurable_fun_sum _ fun j hj ↦
    measurable_visitIndicator_le x (by
      simp only [Finset.mem_range] at hj
      omega)

/-- First time at or after `n` at which the coordinate process hits `A`. -/
noncomputable def firstHitAfter (A : Set Site) (n : ℕ) : (ℕ → Site) → WithTop ℕ :=
  hittingAfter coordinateProcess A n

theorem isStoppingTime_firstHitAfter {A : Set Site} (hA : MeasurableSet A) (n : ℕ) :
    IsStoppingTime canonicalFiltration (firstHitAfter A n) := by
  exact adapted_coordinateProcess.isStoppingTime_hittingAfter hA

theorem isStoppingTime_firstHitSiteAfter (x : Site) (n : ℕ) :
    IsStoppingTime canonicalFiltration (firstHitAfter {x} n) := by
  exact isStoppingTime_firstHitAfter (measurableSet_singleton x) n

@[simp] theorem untopA_coe_nat (k : ℕ) : ((k : WithTop ℕ).untopA) = k := by
  rfl

/-- Hit `A` at or after a possibly unbounded stopping time.  The value remains
`⊤` when the input stopping time is `⊤`. -/
noncomputable def firstHitAfterStopping (A : Set Site)
    (τ : (ℕ → Site) → WithTop ℕ) : (ℕ → Site) → WithTop ℕ :=
  fun s ↦ if τ s = ⊤ then ⊤
    else hittingAfter coordinateProcess A (τ s).untopA s

theorem isStoppingTime_firstHitAfterStopping {A : Set Site}
    {τ : (ℕ → Site) → WithTop ℕ} (hA : MeasurableSet A)
    (hτ : IsStoppingTime canonicalFiltration τ) :
    IsStoppingTime canonicalFiltration (firstHitAfterStopping A τ) := by
  intro n
  have hset : {s | firstHitAfterStopping A τ s ≤ n} =
      ⋃ k : ℕ, ⋃ (_ : k ≤ n),
        {s | τ s = k} ∩ {s | firstHitAfter A k s ≤ n} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases ht : τ s = ⊤
      · simp [firstHitAfterStopping, ht] at h
      · lift τ s to ℕ using ht with k hk
        have hhit : hittingAfter coordinateProcess A k s ≤ n := by
          simpa [firstHitAfterStopping, ← hk] using h
        have hkn : k ≤ n := by
          exact WithTop.coe_le_coe.mp
            ((le_hittingAfter (u := coordinateProcess) (s := A)
              (n := k) s).trans hhit)
        refine ⟨k, hkn, rfl, ?_⟩
        simpa [firstHitAfter] using hhit
    · rintro ⟨k, hkn, hτk, hhit⟩
      have ht : τ s ≠ ⊤ := by simp [hτk]
      simpa [firstHitAfterStopping, firstHitAfter, ht, hτk] using hhit
  change MeasurableSet[canonicalFiltration n]
    {s | firstHitAfterStopping A τ s ≤ n}
  rw [hset]
  refine MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun hkn ↦ ?_
  exact (canonicalFiltration.mono hkn _ (hτ.measurableSet_eq_of_countable k)).inter
    ((isStoppingTime_firstHitAfter hA k) n)

/-- An unbounded chain of strict successive hits.  `target k` is the set hit
at step `k+1`; the search begins one time unit after the preceding hit. -/
noncomputable def strictHitChain (target : ℕ → Set Site) :
    ℕ → (ℕ → Site) → WithTop ℕ
  | 0 => fun _ ↦ 0
  | k + 1 => firstHitAfterStopping (target k)
      (fun s ↦ strictHitChain target k s + 1)

theorem isStoppingTime_strictHitChain {target : ℕ → Set Site}
    (htarget : ∀ k, MeasurableSet (target k)) (k : ℕ) :
    IsStoppingTime canonicalFiltration (strictHitChain target k) := by
  induction k with
  | zero => simpa [strictHitChain] using
      isStoppingTime_const canonicalFiltration (0 : ℕ)
  | succ k ih =>
      rw [strictHitChain]
      exact isStoppingTime_firstHitAfterStopping (htarget k) (ih.add_const' 1)

/-- First time at or after `n` at which the local time at `x` reaches `q`. -/
noncomputable def firstLocalTimeGEAfter (x : Site) (q n : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  hittingAfter (fun k s ↦ localTime s k x) (Set.Ici q) n

theorem isStoppingTime_firstLocalTimeGEAfter (x : Site) (q n : ℕ) :
    IsStoppingTime canonicalFiltration (firstLocalTimeGEAfter x q n) := by
  exact (adapted_localTime x).isStoppingTime_hittingAfter measurableSet_Ici

/-- Starting from a bounded stopping time, hit `A` before the deterministic
cutoff `N`; the value is `N` if there is no such hit. -/
noncomputable def nextHitBefore (A : Set Site)
    (τ : (ℕ → Site) → WithTop ℕ) (N : ℕ) : (ℕ → Site) → WithTop ℕ :=
  fun s ↦ (hittingBtwn coordinateProcess A (τ s).untopA N s : ℕ)

theorem nextHitBefore_le (A : Set Site) (τ : (ℕ → Site) → WithTop ℕ)
    (N : ℕ) (s : ℕ → Site) : nextHitBefore A τ N s ≤ N := by
  unfold nextHitBefore
  exact_mod_cast (hittingBtwn_le (u := coordinateProcess) (s := A)
    (n := (τ s).untopA) (m := N) s)

theorem isStoppingTime_nextHitBefore {A : Set Site}
    {τ : (ℕ → Site) → WithTop ℕ} {N : ℕ}
    (hA : MeasurableSet A) (hτ : IsStoppingTime canonicalFiltration τ)
    (hτN : ∀ s, τ s ≤ N) :
    IsStoppingTime canonicalFiltration (nextHitBefore A τ N) := by
  exact adapted_coordinateProcess.isStoppingTime_hittingBtwn_isStoppingTime
    hτ hτN hA

/-- A finite-horizon sequence of successive hits. `target k` is the set hit
at step `k+1`. This packages alternating inner/outer boundary excursions. -/
noncomputable def boundedHitChain (target : ℕ → Set Site) (N : ℕ) :
    ℕ → (ℕ → Site) → WithTop ℕ
  | 0 => fun _ ↦ 0
  | k + 1 => nextHitBefore (target k) (boundedHitChain target N k) N

theorem boundedHitChain_le (target : ℕ → Set Site) (N k : ℕ) (s : ℕ → Site) :
    boundedHitChain target N k s ≤ N := by
  cases k with
  | zero => simp [boundedHitChain]
  | succ k => exact nextHitBefore_le (target k) (boundedHitChain target N k) N s

theorem isStoppingTime_boundedHitChain {target : ℕ → Set Site}
    (htarget : ∀ k, MeasurableSet (target k)) (N k : ℕ) :
    IsStoppingTime canonicalFiltration (boundedHitChain target N k) := by
  induction k with
  | zero => simpa [boundedHitChain] using isStoppingTime_const canonicalFiltration (0 : ℕ)
  | succ k ih =>
      rw [boundedHitChain]
      exact isStoppingTime_nextHitBefore (htarget k) ih
        (boundedHitChain_le target N k)

/-- At a stopping time bounded by `N`, the stopped coordinate is already
measurable with respect to time `N`. -/
theorem stronglyMeasurable_stoppedCoordinate_of_le
    {τ : (ℕ → Site) → WithTop ℕ} {N : ℕ}
    (hτ : IsStoppingTime canonicalFiltration τ) (hτN : ∀ s, τ s ≤ N) :
    StronglyMeasurable[canonicalFiltration N]
      (stoppedValue coordinateProcess τ) := by
  exact stronglyMeasurable_stoppedValue_of_le
    adapted_coordinateProcess.stronglyAdapted.isStronglyProgressive_of_discrete
    hτ hτN

theorem stronglyMeasurable_coordinateAtBoundedHitChain
    {target : ℕ → Set Site} (htarget : ∀ k, MeasurableSet (target k))
    (N k : ℕ) :
    StronglyMeasurable[canonicalFiltration N]
      (stoppedValue coordinateProcess (boundedHitChain target N k)) := by
  exact stronglyMeasurable_stoppedCoordinate_of_le
    (isStoppingTime_boundedHitChain htarget N k)
    (boundedHitChain_le target N k)

end HLOZFoundation

namespace HLOZFoundation

open ProbabilityTheory

lemma measurable_simpleRandomWalk_time_iidHistory {j k : ℕ} (hjk : j ≤ k) :
    Measurable[iidHistory (X := Direction) k]
      (fun ω : ℕ → Direction ↦ simpleRandomWalk ω j) := by
  unfold simpleRandomWalk
  apply Finset.measurable_fun_sum
  intro i hi
  apply measurable_directionStep.comp
  apply measurable_iff_comap_le.mpr
  have hik : i < k := (Finset.mem_range.mp hi).trans_le hjk
  exact le_iSup_of_le i (le_iSup_of_le hik le_rfl)

/-- Pulling the canonical path filtration at time `k` back along partial
summation uses only increment coordinates strictly before `k`. -/
lemma measurable_simpleRandomWalk_iidHistory_canonicalFiltration (k : ℕ) :
    Measurable[iidHistory (X := Direction) k, canonicalFiltration k]
      simpleRandomWalk := by
  apply measurable_iff_comap_le.mpr
  simp only [canonicalFiltration, Filtration.natural,
    MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup_le fun j ↦ iSup_le fun hjk ↦ ?_
  simpa [Function.comp_def, coordinateProcess] using
    (measurable_simpleRandomWalk_time_iidHistory hjk).comap_le

/-- The increment-space strong restart theorem at a bounded stopping time of
the canonical walk.  An event known at the stopping time is independent of a
finite block of increments beginning at that time. -/
theorem incrementLaw_inter_blockAfter_boundedStopping_eq_mul
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime canonicalFiltration τ) {N : ℕ}
    (hτN : ∀ s, τ s ≤ N)
    {A : Set (ℕ → Site)} (hA : MeasurableSet[hτ.measurableSpace] A)
    (m : ℕ) {B : Set (Fin m → Direction)} (hB : MeasurableSet B) :
    incrementLaw
        (simpleRandomWalk ⁻¹' A ∩
          iidBlockAfter (X := Direction)
            (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) m ⁻¹' B) =
      incrementLaw (simpleRandomWalk ⁻¹' A) *
        (Measure.infinitePi fun _ : Fin m ↦
          (PMF.uniformOfFintype Direction).toMeasure) B := by
  unfold incrementLaw
  apply measure_inter_iidBlockAfter_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure)
    (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) m
    (simpleRandomWalk ⁻¹' A) ?_ hB
  intro k
  have hPath : MeasurableSet[canonicalFiltration k]
      (A ∩ {s | τ s = k}) := by
    apply (hτ.measurableSet_inter_eq_iff A k).mp
    exact hA.inter (hτ.measurableSet_eq' k)
  have hPre : MeasurableSet[iidHistory (X := Direction) k]
      (simpleRandomWalk ⁻¹' (A ∩ {s | τ s = k})) :=
    measurable_simpleRandomWalk_iidHistory_canonicalFiltration k hPath
  convert hPre using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hωA, hτk⟩
    refine ⟨hωA, ?_⟩
    have hne : τ (simpleRandomWalk ω) ≠ ⊤ := by
      intro ht
      have hle := hτN (simpleRandomWalk ω)
      rw [ht] at hle
      exact (WithTop.not_top_le_coe N) hle
    have hcoe : ((τ (simpleRandomWalk ω)).untopA : WithTop ℕ) =
        τ (simpleRandomWalk ω) := by
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop _ hne
    calc
      τ (simpleRandomWalk ω) =
          ((τ (simpleRandomWalk ω)).untopA : WithTop ℕ) := hcoe.symm
      _ = (k : WithTop ℕ) := congrArg ((↑) : ℕ → WithTop ℕ) hτk
  · rintro ⟨hωA, hτk⟩
    refine ⟨hωA, ?_⟩
    rw [hτk]
    rfl

/-- Strong restart at a possibly unbounded stopping time of the canonical
walk, on a past event on which the stopping time is finite.  This is the
form used by untruncated excursion decompositions. -/
theorem incrementLaw_inter_blockAfter_stopping_eq_mul
    {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime canonicalFiltration τ)
    {A : Set (ℕ → Site)} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hA_finite : A ⊆ {s | τ s ≠ ⊤})
    (m : ℕ) {B : Set (Fin m → Direction)} (hB : MeasurableSet B) :
    incrementLaw
        (simpleRandomWalk ⁻¹' A ∩
          iidBlockAfter (X := Direction)
            (fun ω ↦ (τ (simpleRandomWalk ω)).untopA) m ⁻¹' B) =
      incrementLaw (simpleRandomWalk ⁻¹' A) *
        (Measure.infinitePi fun _ : Fin m ↦
          (PMF.uniformOfFintype Direction).toMeasure) B := by
  unfold incrementLaw
  apply measure_inter_iidBlockAfter_untopA_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure)
    (fun ω ↦ τ (simpleRandomWalk ω)) m (simpleRandomWalk ⁻¹' A)
  · intro ω hω
    exact hA_finite hω
  · intro k
    have hPath : MeasurableSet[canonicalFiltration k]
        (A ∩ {s | τ s = k}) := by
      apply (hτ.measurableSet_inter_eq_iff A k).mp
      exact hA.inter (hτ.measurableSet_eq' k)
    have hPre : MeasurableSet[iidHistory (X := Direction) k]
        (simpleRandomWalk ⁻¹' (A ∩ {s | τ s = k})) :=
      measurable_simpleRandomWalk_iidHistory_canonicalFiltration k hPath
    simpa only [Set.preimage_inter, Set.preimage_setOf_eq] using hPre
  · exact hB

/-- Specialization of strong restart to the finite-horizon hit chains used
for successive boundary excursions. -/
theorem incrementLaw_inter_blockAfter_boundedHitChain_eq_mul
    {target : ℕ → Set Site} (htarget : ∀ k, MeasurableSet (target k))
    (N r : ℕ) {A : Set (ℕ → Site)}
    (hA : MeasurableSet[
      (isStoppingTime_boundedHitChain htarget N r).measurableSpace] A)
    (m : ℕ) {B : Set (Fin m → Direction)} (hB : MeasurableSet B) :
    incrementLaw
        (simpleRandomWalk ⁻¹' A ∩
          iidBlockAfter (X := Direction)
            (fun ω ↦ (boundedHitChain target N r
              (simpleRandomWalk ω)).untopA) m ⁻¹' B) =
      incrementLaw (simpleRandomWalk ⁻¹' A) *
        (Measure.infinitePi fun _ : Fin m ↦
          (PMF.uniformOfFintype Direction).toMeasure) B := by
  exact incrementLaw_inter_blockAfter_boundedStopping_eq_mul
    (isStoppingTime_boundedHitChain htarget N r)
    (boundedHitChain_le target N r) hA m hB

end HLOZFoundation

/-- Sites attaining the largest local time at time `n`. -/
def favoriteSites (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (visitedSites s n).filter fun x ↦ localTime s n x = maxLocalTime s n

/-- All sites which have been favourite at some time through `n`. -/
def favoriteUnion (s : ℕ → Site) (n : ℕ) : Finset Site :=
  (Finset.range (n + 1)).biUnion (favoriteSites s)

/-- Favourite sites occurring strictly before time `N`. -/
def favoriteUnionBefore (s : ℕ → Site) (N : ℕ) : Finset Site :=
  (Finset.range N).biUnion (favoriteSites s)

theorem visitedSites_mono {s : ℕ → Site} {i j : ℕ} (hij : i ≤ j) :
    visitedSites s i ⊆ visitedSites s j := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨k, ?_, rfl⟩
  simp only [Finset.mem_range] at hk ⊢
  omega

theorem localTime_mono {s : ℕ → Site} {i j : ℕ} (hij : i ≤ j) (x : Site) :
    localTime s i x ≤ localTime s j x := by
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨?_, hk.2⟩
  simp only [Finset.mem_range] at hk ⊢
  omega

theorem localTime_eq_zero_of_not_mem_visitedSites {s : ℕ → Site} {n : ℕ} {x : Site}
    (hx : x ∉ visitedSites s n) : localTime s n x = 0 := by
  rw [localTime, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hsk : s k ∈ visitedSites s n :=
    Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
  exact hx (by simpa [(Finset.mem_filter.mp hk).2] using hsk)

theorem localTime_pos_of_mem_visitedSites {s : ℕ → Site} {n : ℕ} {x : Site}
    (hx : x ∈ visitedSites s n) : 0 < localTime s n x := by
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  change 0 < ((Finset.range (n + 1)).filter fun j ↦ s j = s k).card
  rw [Finset.card_pos]
  exact ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩

theorem localTime_le_maxLocalTime {s : ℕ → Site} {n : ℕ} {x : Site}
    (hx : x ∈ visitedSites s n) : localTime s n x ≤ maxLocalTime s n := by
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  exact Finset.le_sup (f := fun j ↦ localTime s n (s j)) hk

theorem maxLocalTime_pos (s : ℕ → Site) (n : ℕ) : 0 < maxLocalTime s n := by
  have hzero : 0 ∈ Finset.range (n + 1) := by simp
  exact (localTime_pos_of_mem_visitedSites
      (s := s) (n := n) (x := s 0) (Finset.mem_image.mpr ⟨0, hzero, rfl⟩)).trans_le
    (Finset.le_sup (f := fun j ↦ localTime s n (s j)) hzero)

theorem maxLocalTime_mono {s : ℕ → Site} {i j : ℕ} (hij : i ≤ j) :
    maxLocalTime s i ≤ maxLocalTime s j := by
  unfold maxLocalTime
  rw [Finset.sup_le_iff]
  intro k hk
  have hkj : k ∈ Finset.range (j + 1) := by
    simp only [Finset.mem_range] at hk ⊢
    omega
  exact (localTime_mono hij (s k)).trans
    (Finset.le_sup (f := fun k ↦ localTime s j (s k)) hkj)


open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Elementary lower Wallis bound sufficient for recurrence. -/
theorem sixteen_pow_succ_le_four_mul_succ_mul_centralBinom_sq : ∀ j : ℕ,
    16 ^ (j + 1) ≤ 4 * (j + 1) * Nat.centralBinom (j + 1) ^ 2 := by
  intro j
  induction j with
  | zero => norm_num [Nat.centralBinom]
  | succ j ih =>
      have hrec := Nat.succ_mul_centralBinom_succ (j + 1)
      have hsq := congrArg (fun x : ℕ ↦ x ^ 2) hrec
      have hpoly : 4 * (j + 2) * (j + 1) ≤ (2 * j + 3) ^ 2 := by nlinarith
      have hmul :
          (j + 2) ^ 2 * 16 ^ (j + 2) ≤
            (j + 2) ^ 2 * (4 * (j + 2) * Nat.centralBinom (j + 2) ^ 2) := by
        calc
          (j + 2) ^ 2 * 16 ^ (j + 2) =
              16 * (j + 2) ^ 2 * 16 ^ (j + 1) := by rw [pow_succ]; ring
          _ ≤ 16 * (j + 2) ^ 2 *
              (4 * (j + 1) * Nat.centralBinom (j + 1) ^ 2) :=
            Nat.mul_le_mul_left _ ih
          _ = 16 * (j + 2) * (4 * (j + 2) * (j + 1)) *
              Nat.centralBinom (j + 1) ^ 2 := by ring
          _ ≤ 16 * (j + 2) * (2 * j + 3) ^ 2 *
              Nat.centralBinom (j + 1) ^ 2 := by gcongr
          _ = 4 * (j + 2) *
              ((j + 2) * Nat.centralBinom (j + 2)) ^ 2 := by
            rw [hsq]
            ring
          _ = (j + 2) ^ 2 * (4 * (j + 2) *
              Nat.centralBinom (j + 2) ^ 2) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (by positivity)

theorem sixteen_pow_succ_le_four_mul_succ_mul_choose_sq (j : ℕ) :
    16 ^ (j + 1) ≤ 4 * (j + 1) * ((2 * (j + 1)).choose (j + 1)) ^ 2 := by
  simpa [Nat.centralBinom_eq_two_mul_choose] using
    sixteen_pow_succ_le_four_mul_succ_mul_centralBinom_sq j

theorem return_real_even_succ_lower (j : ℕ) :
    1 / (4 * (j + 1 : ℝ)) ≤
      incrementLaw.real
        {ω | simpleRandomWalk ω (2 * (j + 1)) = (0, 0)} := by
  rw [return_real_even]
  have hbinom :
      (16 : ℝ) ^ (j + 1) ≤
        4 * (j + 1 : ℝ) * (((2 * (j + 1)).choose (j + 1) : ℝ) ^ 2) := by
    exact_mod_cast sixteen_pow_succ_le_four_mul_succ_mul_choose_sq j
  have hpow : (4 : ℝ) ^ (2 * (j + 1)) = 16 ^ (j + 1) := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
  rw [hpow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbinom

theorem secondMoment_support_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (C : ℝ) (hC : ∀ ω, f ω ≤ C) :
    (∫ ω, f ω ∂μ) ^ 2 ≤
      μ.real {ω | 0 < f ω} * ∫ ω, (f ω) ^ 2 ∂μ := by
  let A : Set Ω := {ω | 0 < f ω}
  let g : Ω → ℝ := A.indicator 1
  have hA : MeasurableSet A := hf measurableSet_Ioi
  have hg : Measurable g := measurable_const.indicator hA
  have hfLp : MemLp f (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_of_nonneg (hf0 ω)]
      exact hC ω)
  have hgLp : MemLp g (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ by
      simp only [g]
      by_cases hω : ω ∈ A <;> simp [hω])
  have hfg : (fun ω ↦ f ω * g ω) = f := by
    funext ω
    by_cases hω : ω ∈ A
    · simp [g, hω]
    · have hz : f ω = 0 := by
        simp only [A, Set.mem_setOf_eq, not_lt] at hω
        exact le_antisymm hω (hf0 ω)
      simp [g, hω, hz]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) (f := f) (g := g)
    Real.HolderConjugate.two_two
    (Eventually.of_forall hf0)
    (Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ A <;> simp [g, hω]) hfLp hgLp
  rw [hfg] at hholder
  have hfsq : 0 ≤ ∫ ω, (f ω) ^ 2 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω ↦ sq_nonneg (f ω))
  have hgsq : (∫ ω, (g ω) ^ 2 ∂μ) = μ.real A := by
    have hgid : (fun ω ↦ (g ω) ^ 2) = g := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [g, hω]
    rw [hgid]
    simp [g, hA]
  have hgsqR : (∫ ω, (g ω) ^ (2 : ℝ) ∂μ) = μ.real A := by
    simpa only [Real.rpow_two] using hgsq
  have hholder' :
      (∫ ω, f ω ∂μ) ≤
        (∫ ω, (f ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (μ.real A) ^ (1 / (2 : ℝ)) := by
    calc
      (∫ ω, f ω ∂μ) ≤
          (∫ ω, (f ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ ω, (g ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
      _ = _ := by rw [hgsqR]
  have hμA : 0 ≤ μ.real A := measureReal_nonneg
  norm_num [one_div] at hholder'
  have hholderS :
      (∫ ω, f ω ∂μ) ≤
        Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    simpa [Real.sqrt_eq_rpow] using hholder'
  have hmean : 0 ≤ ∫ ω, f ω ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall hf0)
  have hsquare := (sq_le_sq₀ hmean
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hholderS
  rw [mul_pow, Real.sq_sqrt hfsq, Real.sq_sqrt hμA] at hsquare
  simpa [A, mul_comm] using hsquare

def returnIndicator (i : ℕ) (ω : ℕ → Direction) : ℝ :=
  if simpleRandomWalk ω i = (0, 0) then 1 else 0

def returnCount (n : ℕ) (ω : ℕ → Direction) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), returnIndicator i ω

theorem measurableSet_returnAt (i : ℕ) :
    MeasurableSet {ω : ℕ → Direction | simpleRandomWalk ω i = (0, 0)} := by
  exact measurableSet_eq_fun
    ((measurable_pi_apply i).comp measurable_simpleRandomWalk) measurable_const

theorem measurable_returnIndicator (i : ℕ) : Measurable (returnIndicator i) := by
  exact Measurable.ite (measurableSet_returnAt i) measurable_const measurable_const

theorem measurable_returnCount (n : ℕ) : Measurable (returnCount n) := by
  exact Finset.measurable_sum _ fun i _ ↦ measurable_returnIndicator i

theorem returnCount_nonneg (n : ℕ) (ω : ℕ → Direction) : 0 ≤ returnCount n ω := by
  apply Finset.sum_nonneg
  intro i _
  simp only [returnIndicator]
  split_ifs <;> norm_num

theorem returnCount_le (n : ℕ) (ω : ℕ → Direction) : returnCount n ω ≤ n + 1 := by
  calc
    returnCount n ω ≤ ∑ _i ∈ Finset.range (n + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [returnIndicator]
      split_ifs <;> norm_num
    _ = n + 1 := by simp

theorem returnIndicator_eq_indicator (i : ℕ) :
    returnIndicator i =
      ({ω | simpleRandomWalk ω i = (0, 0)} : Set (ℕ → Direction)).indicator
        (fun _ ↦ (1 : ℝ)) := by
  funext ω
  by_cases hω : simpleRandomWalk ω i = (0, 0) <;>
    simp [returnIndicator, hω]

theorem integral_returnIndicator (i : ℕ) :
    ∫ ω, returnIndicator i ω ∂incrementLaw =
      incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)} := by
  rw [returnIndicator_eq_indicator]
  exact integral_indicator_one (measurableSet_returnAt i)

theorem integral_returnCount (n : ℕ) :
    ∫ ω, returnCount n ω ∂incrementLaw =
      ∑ i ∈ Finset.range (n + 1),
        incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)} := by
  unfold returnCount
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_returnIndicator i
  · intro i _
    rw [returnIndicator_eq_indicator]
    exact
      ((integrable_const (c := (1 : ℝ)) (μ := incrementLaw)).indicator
        (measurableSet_returnAt i))

def zeroIJTimes (i j : ℕ) (hij : i ≤ j) : CollisionKernel.TimeTuple j 3 :=
  ![0, ⟨i, by omega⟩, ⟨j, by omega⟩]

theorem monotone_zeroIJTimes (i j : ℕ) (hij : i ≤ j) :
    Monotone (zeroIJTimes i j hij) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [zeroIJTimes]

theorem collisionSet_zeroIJTimes (i j : ℕ) (hij : i ≤ j) :
    CollisionKernel.collisionSet (zeroIJTimes i j hij) =
      {ω | simpleRandomWalk ω i = (0, 0)} ∩
        {ω | simpleRandomWalk ω j = (0, 0)} := by
  ext ω
  simp only [CollisionKernel.collisionSet, Set.mem_inter_iff, Set.mem_setOf_eq]
  have hzero : (0 : Site) = (0, 0) := rfl
  constructor
  · intro h
    have hi := h (0 : Fin 3) (1 : Fin 3)
    have hj := h (0 : Fin 3) (2 : Fin 3)
    simpa [zeroIJTimes, simpleRandomWalk, hzero] using And.intro hi.symm hj.symm
  · rintro ⟨hi, hj⟩ a b
    fin_cases a <;> fin_cases b <;> simp_all [zeroIJTimes, simpleRandomWalk, hzero]

theorem gapWeight_zeroIJTimes (i j : ℕ) (hij : i ≤ j) :
    CollisionKernel.gapWeight j 2 (CollisionKernel.returnKernel j)
        (zeroIJTimes i j hij) =
      incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)} *
        incrementLaw.real {ω | simpleRandomWalk ω (j - i) = (0, 0)} := by
  simp [CollisionKernel.gapWeight, CollisionKernel.returnKernel,
    CollisionKernel.timeGaps, zeroIJTimes]

theorem integral_returnIndicator_mul_of_le (i j : ℕ) (hij : i ≤ j) :
    ∫ ω, returnIndicator i ω * returnIndicator j ω ∂incrementLaw =
      incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)} *
        incrementLaw.real {ω | simpleRandomWalk ω (j - i) = (0, 0)} := by
  let Ei : Set (ℕ → Direction) := {ω | simpleRandomWalk ω i = (0, 0)}
  let Ej : Set (ℕ → Direction) := {ω | simpleRandomWalk ω j = (0, 0)}
  have hprod : (fun ω ↦ returnIndicator i ω * returnIndicator j ω) =
      (Ei ∩ Ej).indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω
    by_cases hi : simpleRandomWalk ω i = (0, 0) <;>
      by_cases hj : simpleRandomWalk ω j = (0, 0) <;>
      simp [returnIndicator, Ei, Ej, hi, hj]
  rw [hprod]
  calc
    ∫ ω, (Ei ∩ Ej).indicator (fun _ ↦ (1 : ℝ)) ω ∂incrementLaw =
        incrementLaw.real (Ei ∩ Ej) := by
      apply integral_indicator_one
      simpa [Ei, Ej] using
        (measurableSet_returnAt i).inter (measurableSet_returnAt j)
    _ = incrementLaw.real (CollisionKernel.collisionSet (zeroIJTimes i j hij)) := by
      rw [collisionSet_zeroIJTimes i j hij]
    _ = _ := (CollisionKernel.collision_real_eq_gapWeight
      (monotone_zeroIJTimes i j hij)).trans (gapWeight_zeroIJTimes i j hij)

theorem integrable_returnIndicator (i : ℕ) : Integrable (returnIndicator i) incrementLaw := by
  rw [returnIndicator_eq_indicator]
  exact ((integrable_const (c := (1 : ℝ)) (μ := incrementLaw)).indicator
    (measurableSet_returnAt i))

theorem integrable_returnIndicator_mul (i j : ℕ) :
    Integrable (fun ω ↦ returnIndicator i ω * returnIndicator j ω) incrementLaw := by
  apply (integrable_returnIndicator i).mul_bdd (c := 1)
    (measurable_returnIndicator j).aestronglyMeasurable
  filter_upwards [] with ω
  simp only [returnIndicator]
  split_ifs <;> norm_num

theorem integral_returnCount_sq (n : ℕ) :
    ∫ ω, (returnCount n ω) ^ 2 ∂incrementLaw =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ∫ ω, returnIndicator i ω * returnIndicator j ω ∂incrementLaw := by
  have hpoint : (fun ω ↦ (returnCount n ω) ^ 2) =
      fun ω ↦ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        returnIndicator i ω * returnIndicator j ω := by
    funext ω
    simp only [returnCount, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hpoint, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    intro j _
    exact integrable_returnIndicator_mul i j
  · intro i _
    exact integrable_finsetSum _ fun j _ ↦ integrable_returnIndicator_mul i j

noncomputable def returnProb (i : ℕ) : ℝ :=
  incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)}

noncomputable def orderedPairWeight (i j : ℕ) : ℝ :=
  if i ≤ j then returnProb i * returnProb (j - i) else 0

theorem returnProb_nonneg (i : ℕ) : 0 ≤ returnProb i := measureReal_nonneg

theorem integral_returnIndicator_mul_le_ordered (i j : ℕ) :
    ∫ ω, returnIndicator i ω * returnIndicator j ω ∂incrementLaw ≤
      orderedPairWeight i j + orderedPairWeight j i := by
  rcases le_total i j with hij | hji
  · rw [integral_returnIndicator_mul_of_le i j hij]
    simp only [orderedPairWeight, if_pos hij, returnProb]
    exact le_add_of_nonneg_right (by positivity)
  · rw [show (fun ω ↦ returnIndicator i ω * returnIndicator j ω) =
        fun ω ↦ returnIndicator j ω * returnIndicator i ω by
      funext ω; ring,
      integral_returnIndicator_mul_of_le j i hji]
    simp only [orderedPairWeight, if_pos hji, returnProb]
    exact le_add_of_nonneg_left (by positivity)

def encodeOrderedPair (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 - p.1)

theorem sum_orderedPairWeight_le_sq (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, orderedPairWeight i j ≤
      (∑ d ∈ Finset.range N, returnProb d) ^ 2 := by
  let pairs := (Finset.range N ×ˢ Finset.range N).filter fun p ↦ p.1 ≤ p.2
  let target := Finset.range N ×ˢ Finset.range N
  let W : ℕ × ℕ → ℝ := fun p ↦ returnProb p.1 * returnProb p.2
  have hinj : Set.InjOn encodeOrderedPair pairs := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    simp only [encodeOrderedPair, Prod.mk.injEq] at heq
    change (i, j) ∈ (Finset.range N ×ˢ Finset.range N).filter
      (fun p ↦ p.1 ≤ p.2) at hp
    change (i', j') ∈ (Finset.range N ×ˢ Finset.range N).filter
      (fun p ↦ p.1 ≤ p.2) at hp'
    rw [Finset.mem_filter] at hp hp'
    apply Prod.ext
    · exact heq.1
    · dsimp
      have hi : i = i' := heq.1
      have hg : j - i = j' - i' := heq.2
      have hij : i ≤ j := hp.2
      have hij' : i' ≤ j' := hp'.2
      omega
  have hsubset : pairs.image encodeOrderedPair ⊆ target := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨⟨i, j⟩, hij, rfl⟩
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij
    simp [target, encodeOrderedPair]
    omega
  calc
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, orderedPairWeight i j =
        ∑ p ∈ pairs, W (encodeOrderedPair p) := by
      simp only [pairs, Finset.sum_filter, orderedPairWeight, W, encodeOrderedPair]
      rw [Finset.sum_product]
    _ = ∑ p ∈ pairs.image encodeOrderedPair, W p := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ target, W p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p _ _
      exact mul_nonneg (returnProb_nonneg p.1) (returnProb_nonneg p.2)
    _ = (∑ d ∈ Finset.range N, returnProb d) ^ 2 := by
      simp only [target, W, Finset.sum_product, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem integral_returnCount_sq_le_two_mul_mean_sq (n : ℕ) :
    ∫ ω, (returnCount n ω) ^ 2 ∂incrementLaw ≤
      2 * (∫ ω, returnCount n ω ∂incrementLaw) ^ 2 := by
  let A := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    orderedPairWeight i j
  have hsym :
      (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        orderedPairWeight j i) = A := by
    rw [Finset.sum_comm]
  rw [integral_returnCount_sq, integral_returnCount]
  calc
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ∫ ω, returnIndicator i ω * returnIndicator j ω ∂incrementLaw ≤
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (orderedPairWeight i j + orderedPairWeight j i) := by
      gcongr with i hi j hj
      exact integral_returnIndicator_mul_le_ordered i j
    _ = A + A := by
      simp_rw [Finset.sum_add_distrib]
      exact congrArg (A + ·) hsym
    _ = 2 * A := by ring
    _ ≤ 2 * (∑ d ∈ Finset.range (n + 1), returnProb d) ^ 2 := by
      gcongr
      exact sum_orderedPairWeight_le_sq (n + 1)
    _ = 2 * (∑ i ∈ Finset.range (n + 1),
        incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)}) ^ 2 := by rfl

theorem quarter_harmonic_le_returnMean (n : ℕ) :
    (1 / 4 : ℝ) * (harmonic (n + 1) : ℝ) ≤
      ∫ ω, returnCount (2 * (n + 1)) ω ∂incrementLaw := by
  let evenTimes := (Finset.range (n + 1)).image fun j ↦ 2 * (j + 1)
  have hinj : Set.InjOn (fun j : ℕ ↦ 2 * (j + 1)) (Finset.range (n + 1)) := by
    intro a _ b _ h
    change 2 * (a + 1) = 2 * (b + 1) at h
    omega
  have hsubset : evenTimes ⊆ Finset.range (2 * (n + 1) + 1) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    simp only [Finset.mem_range] at hj ⊢
    omega
  rw [integral_returnCount]
  calc
    (1 / 4 : ℝ) * (harmonic (n + 1) : ℝ) =
        ∑ j ∈ Finset.range (n + 1), 1 / (4 * (j + 1 : ℝ)) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      field_simp
    _ ≤ ∑ j ∈ Finset.range (n + 1), returnProb (2 * (j + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      exact return_real_even_succ_lower j
    _ = ∑ i ∈ evenTimes, returnProb i := by
      symm
      rw [Finset.sum_image hinj]
    _ ≤ ∑ i ∈ Finset.range (2 * (n + 1) + 1), returnProb i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro i _ _
      exact returnProb_nonneg i
    _ = ∑ i ∈ Finset.range (2 * (n + 1) + 1),
        incrementLaw.real {ω | simpleRandomWalk ω i = (0, 0)} := by rfl

theorem tendsto_returnMean_atTop :
    Tendsto (fun n ↦ ∫ ω, returnCount (2 * (n + 1)) ω ∂incrementLaw)
      atTop atTop := by
  have hcast : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hharm : Tendsto (fun n : ℕ ↦ (harmonic n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hlog
    filter_upwards [] with n
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic n
  have hquarter : Tendsto (fun n : ℕ ↦ (1 / 4 : ℝ) * (harmonic (n + 1) : ℝ))
      atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    exact hharm.comp (tendsto_add_atTop_nat 1)
  exact tendsto_atTop_mono quarter_harmonic_le_returnMean hquarter

theorem half_mean_sq_le_measure_ge_half_mul_second
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (hfint : Integrable f μ) (hfsqint : Integrable (fun ω ↦ (f ω) ^ 2) μ)
    (C : ℝ) (hC : ∀ ω, f ω ≤ C) :
    ((∫ ω, f ω ∂μ) / 2) ^ 2 ≤
      μ.real {ω | (∫ x, f x ∂μ) / 2 ≤ f ω} *
        ∫ ω, (f ω) ^ 2 ∂μ := by
  let m : ℝ := ∫ ω, f ω ∂μ
  let A : Set Ω := {ω | m / 2 ≤ f ω}
  let g : Ω → ℝ := A.indicator f
  have hm0 : 0 ≤ m := integral_nonneg_of_ae (Eventually.of_forall hf0)
  have hA : MeasurableSet A := hf measurableSet_Ici
  have hg : Measurable g := hf.indicator hA
  have hg0 : ∀ ω, 0 ≤ g ω := by
    intro ω
    by_cases hω : ω ∈ A <;> simp [g, hω, hf0]
  have hgC : ∀ ω, g ω ≤ C := by
    intro ω
    by_cases hω : ω ∈ A
    · simpa [g, hω] using hC ω
    · have hC0 : 0 ≤ C := (hf0 ω).trans (hC ω)
      simp [g, hω, hC0]
  have hcomp : ∫ ω in Aᶜ, f ω ∂μ ≤ m / 2 := by
    calc
      ∫ ω in Aᶜ, f ω ∂μ ≤ ∫ _ω in Aᶜ, m / 2 ∂μ := by
        apply setIntegral_mono_on hfint.integrableOn (integrable_const (m / 2)) hA.compl
        intro ω hω
        simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
        exact hω.le
      _ = μ.real Aᶜ * (m / 2) := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ 1 * (m / 2) := by
        gcongr
        simpa using measureReal_mono (show Aᶜ ⊆ (Set.univ : Set Ω) from Set.subset_univ _)
      _ = m / 2 := one_mul _
  have hgm : m / 2 ≤ ∫ ω, g ω ∂μ := by
    rw [show (∫ ω, g ω ∂μ) = ∫ ω in A, f ω ∂μ by
      exact integral_indicator hA]
    have hsplit := integral_add_compl hA hfint
    linarith
  have hsecond := secondMoment_support_lower μ g hg hg0 C hgC
  have hsupport : { ω | 0 < g ω } ⊆ A := by
    intro ω hω
    by_contra hnot
    simp [g, hnot] at hω
  have hmeas : μ.real {ω | 0 < g ω} ≤ μ.real A :=
    measureReal_mono hsupport
  have hgsq : ∫ ω, (g ω) ^ 2 ∂μ ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
    apply integral_mono
    · exact hfsqint.mono (hg.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ by
          by_cases hω : ω ∈ A <;>
            simp [g, hω, abs_of_nonneg (hf0 ω), sq_nonneg (f ω)])
    · exact hfsqint
    · intro ω
      by_cases hω : ω ∈ A <;> simp [g, hω, sq_nonneg (f ω)]
  calc
    (m / 2) ^ 2 ≤ (∫ ω, g ω ∂μ) ^ 2 := by
      gcongr
    _ ≤ μ.real {ω | 0 < g ω} * ∫ ω, (g ω) ^ 2 ∂μ := hsecond
    _ ≤ μ.real A * ∫ ω, (f ω) ^ 2 ∂μ := by
      exact mul_le_mul hmeas hgsq
        (integral_nonneg_of_ae (Eventually.of_forall fun ω ↦ sq_nonneg (g ω)))
        measureReal_nonneg
    _ = _ := by rfl

theorem integrable_returnCount (n : ℕ) :
    Integrable (returnCount n) incrementLaw := by
  unfold returnCount
  exact integrable_finsetSum _ fun i _ ↦ integrable_returnIndicator i

theorem integrable_returnCount_sq (n : ℕ) :
    Integrable (fun ω ↦ (returnCount n ω) ^ 2) incrementLaw := by
  apply (integrable_const (c := ((n + 1 : ℝ) ^ 2)) (μ := incrementLaw)).mono
    ((measurable_returnCount n).pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (returnCount n ω)), abs_of_nonneg (sq_nonneg (n + 1 : ℝ))]
  nlinarith [returnCount_nonneg n ω, returnCount_le n ω]

theorem one_le_returnCount (n : ℕ) (ω : ℕ → Direction) : 1 ≤ returnCount n ω := by
  have hzero : (0 : Site) = (0, 0) := rfl
  calc
    (1 : ℝ) = returnIndicator 0 ω := by simp [returnIndicator, simpleRandomWalk, hzero]
    _ ≤ ∑ i ∈ Finset.range (n + 1), returnIndicator i ω := by
      exact Finset.single_le_sum
        (s := Finset.range (n + 1)) (f := fun i ↦ returnIndicator i ω)
        (fun i _ ↦ by
          simp only [returnIndicator]
          split_ifs <;> norm_num) (by simp)

theorem one_le_returnMean (n : ℕ) :
    1 ≤ ∫ ω, returnCount n ω ∂incrementLaw := by
  calc
    (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂incrementLaw := by simp
    _ ≤ ∫ ω, returnCount n ω ∂incrementLaw := by
      apply integral_mono (integrable_const (1 : ℝ)) (integrable_returnCount n)
      exact one_le_returnCount n

theorem one_eighth_le_measure_ge_half_returnMean (n : ℕ) :
    (1 / 8 : ℝ) ≤ incrementLaw.real
      {ω | (∫ x, returnCount n x ∂incrementLaw) / 2 ≤ returnCount n ω} := by
  let m : ℝ := ∫ ω, returnCount n ω ∂incrementLaw
  let p : ℝ := incrementLaw.real {ω | m / 2 ≤ returnCount n ω}
  have hpaley : (m / 2) ^ 2 ≤ p *
      ∫ ω, (returnCount n ω) ^ 2 ∂incrementLaw := by
    exact half_mean_sq_le_measure_ge_half_mul_second incrementLaw (returnCount n)
      (measurable_returnCount n) (returnCount_nonneg n) (integrable_returnCount n)
      (integrable_returnCount_sq n) (n + 1) (returnCount_le n)
  have hsecond : ∫ ω, (returnCount n ω) ^ 2 ∂incrementLaw ≤ 2 * m ^ 2 :=
    integral_returnCount_sq_le_two_mul_mean_sq n
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hpaley' : (m / 2) ^ 2 ≤ p * (2 * m ^ 2) :=
    hpaley.trans (mul_le_mul_of_nonneg_left hsecond hp0)
  have hm : 1 ≤ m := one_le_returnMean n
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hm)
  have hscaled : (1 / 8 : ℝ) * m ^ 2 ≤ p * m ^ 2 := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hm2).mp hscaled

def returnThreshold (K : ℕ) : Set (ℕ → Direction) :=
  ⋃ n, {ω | (K : ℝ) ≤ returnCount n ω}

def unboundedOriginReturns : Set (ℕ → Direction) :=
  ⋂ K, returnThreshold K

theorem measurableSet_returnThreshold (K : ℕ) : MeasurableSet (returnThreshold K) := by
  exact MeasurableSet.iUnion fun n ↦ (measurable_returnCount n) measurableSet_Ici

theorem antitone_returnThreshold : Antitone returnThreshold := by
  intro K L hKL ω hω
  simp only [returnThreshold, Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
  rcases hω with ⟨n, hn⟩
  have hKL' : (K : ℝ) ≤ L := by exact_mod_cast hKL
  exact ⟨n, hKL'.trans hn⟩

theorem measurableSet_unboundedOriginReturns : MeasurableSet unboundedOriginReturns := by
  exact MeasurableSet.iInter measurableSet_returnThreshold

theorem one_eighth_le_measureReal_returnThreshold (K : ℕ) :
    (1 / 8 : ℝ) ≤ incrementLaw.real (returnThreshold K) := by
  have hevent := (tendsto_atTop.1 tendsto_returnMean_atTop (2 * K : ℝ)).exists
  rcases hevent with ⟨n, hn⟩
  let N := 2 * (n + 1)
  have hhalf : (K : ℝ) ≤
      (∫ ω, returnCount N ω ∂incrementLaw) / 2 := by
    dsimp only [N]
    linarith
  calc
    (1 / 8 : ℝ) ≤ incrementLaw.real
        {ω | (∫ x, returnCount N x ∂incrementLaw) / 2 ≤ returnCount N ω} :=
      one_eighth_le_measure_ge_half_returnMean N
    _ ≤ incrementLaw.real (returnThreshold K) := by
      apply measureReal_mono (h₂ := measure_ne_top incrementLaw (returnThreshold K))
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [returnThreshold, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨N, hhalf.trans hω⟩

theorem one_eighth_le_measureReal_unboundedOriginReturns :
    (1 / 8 : ℝ) ≤ incrementLaw.real unboundedOriginReturns := by
  have hlim : Tendsto (incrementLaw ∘ returnThreshold) atTop
      (nhds (incrementLaw unboundedOriginReturns)) := by
    simpa only [unboundedOriginReturns] using tendsto_measure_iInter_atTop
      (fun K ↦ (measurableSet_returnThreshold K).nullMeasurableSet)
      antitone_returnThreshold
      ⟨0, measure_ne_top incrementLaw (returnThreshold 0)⟩
  have hlimReal : Tendsto (fun K ↦ incrementLaw.real (returnThreshold K)) atTop
      (nhds (incrementLaw.real unboundedOriginReturns)) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top incrementLaw unboundedOriginReturns)).comp hlim
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlimReal
    one_eighth_le_measureReal_returnThreshold

theorem returnCount_eq_localTime_origin (n : ℕ) (ω : ℕ → Direction) :
    returnCount n ω =
      (localTime (simpleRandomWalk ω) n (0, 0) : ℕ) := by
  simp only [returnCount, returnIndicator, localTime, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> norm_num

theorem unboundedOriginReturns_maxLocalTime_tendsto {ω : ℕ → Direction}
    (hω : ω ∈ unboundedOriginReturns) :
    Tendsto (fun n ↦ maxLocalTime (simpleRandomWalk ω) n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hb := hω
  simp only [unboundedOriginReturns, Set.mem_iInter, returnThreshold,
    Set.mem_iUnion, Set.mem_setOf_eq] at hb
  rcases hb b with ⟨n, hn⟩
  have hbn : b ≤ localTime (simpleRandomWalk ω) n (0, 0) := by
    have hbn' : (b : ℝ) ≤ (localTime (simpleRandomWalk ω) n (0, 0) : ℕ) := by
      rw [← returnCount_eq_localTime_origin n ω]
      exact hn
    exact_mod_cast hbn'
  filter_upwards [eventually_ge_atTop n] with m hnm
  have hzero : simpleRandomWalk ω 0 = (0, 0) := by
    have hz : (0 : Site) = (0, 0) := rfl
    simp [simpleRandomWalk, hz]
  have horigin : (0, 0) ∈ visitedSites (simpleRandomWalk ω) m := by
    exact Finset.mem_image.mpr ⟨0, by simp, hzero⟩
  exact hbn.trans ((localTime_mono hnm (0, 0)).trans
    (localTime_le_maxLocalTime horigin))

def incrementMaxLocalTimeDiverges : Set (ℕ → Direction) :=
  {ω | Tendsto (fun n ↦ maxLocalTime (simpleRandomWalk ω) n) atTop atTop}

theorem measurableSet_incrementMaxLocalTimeDiverges :
    MeasurableSet incrementMaxLocalTimeDiverges := by
  have heq : incrementMaxLocalTimeDiverges =
      ⋂ K : ℕ, ⋃ n : ℕ, {ω | K ≤ maxLocalTime (simpleRandomWalk ω) n} := by
    ext ω
    simp only [incrementMaxLocalTimeDiverges, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h K
      exact (tendsto_atTop.1 h K).exists
    · intro h
      apply tendsto_atTop.2
      intro K
      rcases h K with ⟨n, hn⟩
      filter_upwards [eventually_ge_atTop n] with m hnm
      exact hn.trans (maxLocalTime_mono hnm)
  rw [heq]
  exact MeasurableSet.iInter fun K ↦ MeasurableSet.iUnion fun n ↦
    ((measurable_maxLocalTime_eval n).comp measurable_simpleRandomWalk) measurableSet_Ici

theorem one_eighth_le_measureReal_incrementMaxLocalTimeDiverges :
    (1 / 8 : ℝ) ≤ incrementLaw.real incrementMaxLocalTimeDiverges := by
  refine one_eighth_le_measureReal_unboundedOriginReturns.trans
    (measureReal_mono ?_ (measure_ne_top incrementLaw incrementMaxLocalTimeDiverges))
  intro ω hω
  exact unboundedOriginReturns_maxLocalTime_tendsto hω

theorem localTime_le_maxLocalTime_any (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s n x ≤ maxLocalTime s n := by
  by_cases hx : x ∈ visitedSites s n
  · exact localTime_le_maxLocalTime hx
  · rw [localTime_eq_zero_of_not_mem_visitedSites hx]
    exact Nat.zero_le _

theorem localTime_le_prefix_add_of_eventually_translate
    {s t : ℕ → Site} {K : ℕ} {c x : Site}
    (h : ∀ j, K ≤ j → s j = c + t j) (n : ℕ) :
    localTime t n x ≤ K + localTime s n (c + x) := by
  unfold localTime
  calc
    ((Finset.range (n + 1)).filter fun j ↦ t j = x).card ≤
        (Finset.range K ∪
          (Finset.range (n + 1)).filter fun j ↦ s j = c + x).card := by
      apply Finset.card_le_card
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_union]
      by_cases hjK : j < K
      · exact Or.inl (Finset.mem_range.mpr hjK)
      · apply Or.inr
        rw [Finset.mem_filter]
        refine ⟨hj.1, ?_⟩
        rw [h j (by omega), hj.2]
    _ ≤ (Finset.range K).card +
        ((Finset.range (n + 1)).filter fun j ↦ s j = c + x).card :=
      Finset.card_union_le _ _
    _ = K + ((Finset.range (n + 1)).filter fun j ↦ s j = c + x).card := by
      rw [Finset.card_range]

theorem maxLocalTime_le_prefix_add_of_eventually_translate
    {s t : ℕ → Site} {K : ℕ} {c : Site}
    (h : ∀ j, K ≤ j → s j = c + t j) (n : ℕ) :
    maxLocalTime t n ≤ K + maxLocalTime s n := by
  rw [maxLocalTime, Finset.sup_le_iff]
  intro j hj
  exact (localTime_le_prefix_add_of_eventually_translate h n).trans
    (Nat.add_le_add_left (localTime_le_maxLocalTime_any s n (c + t j)) K)

theorem maxLocalTime_tendsto_iff_of_eventually_translate
    {s t : ℕ → Site} {K : ℕ} {c : Site}
    (h : ∀ j, K ≤ j → s j = c + t j) :
    Tendsto (maxLocalTime s) atTop atTop ↔
      Tendsto (maxLocalTime t) atTop atTop := by
  have hrev : ∀ j, K ≤ j → t j = -c + s j := by
    intro j hj
    rw [h j hj]
    simp
  constructor
  · intro hs
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 hs (K + b)] with n hn
    have hle := maxLocalTime_le_prefix_add_of_eventually_translate hrev n
    omega
  · intro ht
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_atTop.1 ht (K + b)] with n hn
    have hle := maxLocalTime_le_prefix_add_of_eventually_translate h n
    omega

def incrementCoordinateSigma (i : ℕ) : MeasurableSpace (ℕ → Direction) :=
  MeasurableSpace.comap (fun ω ↦ ω i) inferInstance

def incrementTailSigma (K : ℕ) : MeasurableSpace (ℕ → Direction) :=
  ⨆ i, ⨆ (_ : K ≤ i), incrementCoordinateSigma i

def walkAfter (K : ℕ) (ω : ℕ → Direction) (n : ℕ) : Site :=
  ∑ j ∈ Finset.Ico K n, directionStep (ω j)

theorem measurable_walkAfter (K : ℕ) :
    Measurable[incrementTailSigma K] (walkAfter K) := by
  letI : MeasurableSpace (ℕ → Direction) := incrementTailSigma K
  change Measurable (walkAfter K)
  apply measurable_pi_lambda
  intro n
  unfold walkAfter
  apply Finset.measurable_fun_sum
  intro i hi
  apply measurable_directionStep.comp
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le i (le_iSup_of_le (Finset.mem_Ico.mp hi).1 le_rfl)

theorem simpleRandomWalk_eq_add_walkAfter {K n : ℕ} (hKn : K ≤ n)
    (ω : ℕ → Direction) :
    simpleRandomWalk ω n = simpleRandomWalk ω K + walkAfter K ω n := by
  exact (Finset.sum_range_add_sum_Ico (fun j ↦ directionStep (ω j)) hKn).symm

def pathMaxLocalTimeDiverges : Set (ℕ → Site) :=
  {s | Tendsto (maxLocalTime s) atTop atTop}

theorem measurableSet_pathMaxLocalTimeDiverges :
    MeasurableSet pathMaxLocalTimeDiverges := by
  have heq : pathMaxLocalTimeDiverges =
      ⋂ K : ℕ, ⋃ n : ℕ, {s | K ≤ maxLocalTime s n} := by
    ext s
    simp only [pathMaxLocalTimeDiverges, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h K
      exact (tendsto_atTop.1 h K).exists
    · intro h
      apply tendsto_atTop.2
      intro K
      rcases h K with ⟨n, hn⟩
      filter_upwards [eventually_ge_atTop n] with m hnm
      exact hn.trans (maxLocalTime_mono hnm)
  rw [heq]
  exact MeasurableSet.iInter fun K ↦ MeasurableSet.iUnion fun n ↦
    (measurable_maxLocalTime_eval n) measurableSet_Ici

theorem measurableSet_incrementMaxLocalTimeDiverges_incrementTailSigma (K : ℕ) :
    MeasurableSet[incrementTailSigma K] incrementMaxLocalTimeDiverges := by
  have heq : incrementMaxLocalTimeDiverges =
      walkAfter K ⁻¹' pathMaxLocalTimeDiverges := by
    ext ω
    simp only [incrementMaxLocalTimeDiverges, pathMaxLocalTimeDiverges,
      Set.mem_setOf_eq, Set.mem_preimage]
    apply maxLocalTime_tendsto_iff_of_eventually_translate
    intro n hKn
    exact simpleRandomWalk_eq_add_walkAfter hKn ω
  rw [heq]
  exact measurableSet_pathMaxLocalTimeDiverges.preimage (measurable_walkAfter K)

theorem measurableSet_incrementMaxLocalTimeDiverges_tail :
    MeasurableSet[
      limsup (fun i ↦ incrementCoordinateSigma i) atTop]
      incrementMaxLocalTimeDiverges := by
  rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  intro K
  change MeasurableSet[incrementTailSigma K] incrementMaxLocalTimeDiverges
  exact measurableSet_incrementMaxLocalTimeDiverges_incrementTailSigma K

theorem incrementLaw_incrementMaxLocalTimeDiverges_eq_one :
    incrementLaw incrementMaxLocalTimeDiverges = 1 := by
  have hle : ∀ i, incrementCoordinateSigma i ≤
      (inferInstance : MeasurableSpace (ℕ → Direction)) := by
    intro i
    exact (measurable_pi_apply i).comap_le
  have hind : iIndep incrementCoordinateSigma incrementLaw := by
    change iIndep
      (fun x ↦ MeasurableSpace.comap (fun ω : ℕ → Direction ↦ ω x)
        (inferInstance : MeasurableSpace Direction)) incrementLaw
    exact increment_iIndep.iIndep
  have hzeroOne := measure_zero_or_one_of_measurableSet_limsup_atTop
    hle hind measurableSet_incrementMaxLocalTimeDiverges_tail
  rcases hzeroOne with hzero | hone
  · exfalso
    have hrealZero : incrementLaw.real incrementMaxLocalTimeDiverges = 0 := by
      simp [measureReal_def, hzero]
    linarith [one_eighth_le_measureReal_incrementMaxLocalTimeDiverges]
  · exact hone

theorem incrementLaw_maxLocalTime_tendsto :
    ∀ᵐ ω ∂incrementLaw,
      Tendsto (fun n ↦ maxLocalTime (simpleRandomWalk ω) n) atTop atTop := by
  apply (ae_mem_iff_measure_eq
    measurableSet_incrementMaxLocalTimeDiverges.nullMeasurableSet).2
  simpa [incrementMaxLocalTimeDiverges] using
    incrementLaw_incrementMaxLocalTimeDiverges_eq_one

theorem simpleRandomWalkLaw_maxLocalTime_tendsto :
    ∀ᵐ s ∂simpleRandomWalkLaw,
      Tendsto (fun n ↦ maxLocalTime s n) atTop atTop := by
  apply (ae_mem_iff_measure_eq
    measurableSet_pathMaxLocalTimeDiverges.nullMeasurableSet).2
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk measurableSet_pathMaxLocalTimeDiverges]
  change incrementLaw incrementMaxLocalTimeDiverges =
    (Measure.map simpleRandomWalk incrementLaw) Set.univ
  rw [incrementLaw_incrementMaxLocalTimeDiverges_eq_one]
  rw [Measure.map_apply measurable_simpleRandomWalk MeasurableSet.univ]
  simp

theorem favoriteSites_subset_visitedSites (s : ℕ → Site) (n : ℕ) :
    favoriteSites s n ⊆ visitedSites s n := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

/-- The finite definition of `favoriteSites` agrees with maximization over
the whole lattice, including sites not visited by time `n`. -/
theorem mem_favoriteSites_iff_globalMax {s : ℕ → Site} {n : ℕ} {x : Site} :
    x ∈ favoriteSites s n ↔ ∀ y : Site, localTime s n y ≤ localTime s n x := by
  constructor
  · intro hx y
    rcases Finset.mem_filter.mp hx with ⟨_, hxmax⟩
    by_cases hy : y ∈ visitedSites s n
    · exact (localTime_le_maxLocalTime hy).trans_eq hxmax.symm
    · rw [localTime_eq_zero_of_not_mem_visitedSites hy]
      exact Nat.zero_le _
  · intro hglobal
    have hxvisited : x ∈ visitedSites s n := by
      by_contra hx
      have hxzero := localTime_eq_zero_of_not_mem_visitedSites hx
      have hs0pos : 0 < localTime s n (s 0) := by
        apply localTime_pos_of_mem_visitedSites
        apply Finset.mem_image.mpr
        exact ⟨0, by simp, rfl⟩
      have := hglobal (s 0)
      omega
    apply Finset.mem_filter.mpr
    refine ⟨hxvisited, ?_⟩
    apply Nat.le_antisymm (localTime_le_maxLocalTime hxvisited)
    unfold maxLocalTime
    rw [Finset.sup_le_iff]
    intro k _
    exact hglobal (s k)

/-- During a plateau of the maximal local time, favourite sets can only grow. -/
theorem favoriteSites_subset_of_maxLocalTime_eq {s : ℕ → Site} {i j : ℕ}
    (hij : i ≤ j) (hmax : maxLocalTime s i = maxLocalTime s j) :
    favoriteSites s i ⊆ favoriteSites s j := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxvisited, hxmax⟩
  apply Finset.mem_filter.mpr
  have hxvisited' : x ∈ visitedSites s j := visitedSites_mono hij hxvisited
  refine ⟨hxvisited', ?_⟩
  apply Nat.le_antisymm
  · exact localTime_le_maxLocalTime hxvisited'
  · calc
      maxLocalTime s j = maxLocalTime s i := hmax.symm
      _ = localTime s i x := hxmax.symm
      _ ≤ localTime s j x := localTime_mono hij x

/-- Times in `[N,n]` at which a nondecreasing statistic has value `m`. -/
def timesAtLevel (M : ℕ → ℕ) (N n m : ℕ) : Finset ℕ :=
  (Finset.Icc N n).filter fun k ↦ M k = m

/-- Union of a finite-set process over the times at one level. -/
def unionAtLevel {α : Type*} [DecidableEq α] (F : ℕ → Finset α)
    (M : ℕ → ℕ) (N n m : ℕ) : Finset α :=
  (timesAtLevel M N n m).biUnion F

/-- If finite sets are nested whenever their level is unchanged, the union at
one level is contained in the set at the last time at that level. -/
theorem unionAtLevel_card_le {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (M : ℕ → ℕ) (N n m r : ℕ)
    (hnested : ∀ ⦃i j⦄, i ≤ j → M i = M j → F i ⊆ F j)
    (hcard : ∀ k, N ≤ k → k ≤ n → (F k).card ≤ r) :
    (unionAtLevel F M N n m).card ≤ r := by
  classical
  by_cases hempty : timesAtLevel M N n m = ∅
  · simp [unionAtLevel, hempty]
  · have hne : (timesAtLevel M N n m).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    let kmax := (timesAtLevel M N n m).max' hne
    have hkmax : kmax ∈ timesAtLevel M N n m := by
      exact Finset.max'_mem _ _
    have hsubset : unionAtLevel F M N n m ⊆ F kmax := by
      rw [unionAtLevel, Finset.biUnion_subset_iff_forall_subset]
      intro k hk
      apply hnested (Finset.le_max' _ _ hk)
      have hkLevel := (Finset.mem_filter.mp hk).2
      have hkmaxLevel := (Finset.mem_filter.mp hkmax).2
      exact hkLevel.trans hkmaxLevel.symm
    refine (Finset.card_le_card hsubset).trans ?_
    have hkmaxIcc := (Finset.mem_filter.mp hkmax).1
    exact hcard kmax (Finset.mem_Icc.mp hkmaxIcc).1 (Finset.mem_Icc.mp hkmaxIcc).2

/-- Union of a finite-set process over the time interval `[N,n]`. -/
def intervalUnion {α : Type*} [DecidableEq α] (F : ℕ → Finset α)
    (N n : ℕ) : Finset α :=
  (Finset.Icc N n).biUnion F

/-- Regrouping a nested-on-level finite-set process by its positive levels. -/
theorem intervalUnion_card_le_mul {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (M : ℕ → ℕ) (N n r : ℕ)
    (hMpos : ∀ k, 0 < M k) (hMmono : Monotone M)
    (hnested : ∀ ⦃i j⦄, i ≤ j → M i = M j → F i ⊆ F j)
    (hcard : ∀ k, N ≤ k → (F k).card ≤ r) :
    (intervalUnion F N n).card ≤ r * M n := by
  classical
  let levels := Finset.Icc 1 (M n)
  let grouped := levels.biUnion (unionAtLevel F M N n)
  have hsubset : intervalUnion F N n ⊆ grouped := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hkIcc, hxF⟩
    have hkN : N ≤ k := (Finset.mem_Icc.mp hkIcc).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hkIcc).2
    apply Finset.mem_biUnion.mpr
    refine ⟨M k, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hMpos k, hMmono hkn⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨k, ?_, hxF⟩
      exact Finset.mem_filter.mpr ⟨hkIcc, rfl⟩
  calc
    (intervalUnion F N n).card ≤ grouped.card := Finset.card_le_card hsubset
    _ ≤ levels.card * r := Finset.card_biUnion_le_card_mul _ _ _ fun m _ ↦
      unionAtLevel_card_le F M N n m r hnested fun k hkN hkn ↦ hcard k hkN
    _ = r * M n := by simp [levels, Nat.mul_comm]

theorem intervalFavoriteUnion_card_le (s : ℕ → Site) (N n r : ℕ)
    (hcard : ∀ k, N ≤ k → (favoriteSites s k).card ≤ r) :
    (intervalUnion (favoriteSites s) N n).card ≤ r * maxLocalTime s n := by
  apply intervalUnion_card_le_mul (favoriteSites s) (maxLocalTime s) N n r
  · exact maxLocalTime_pos s
  · exact fun _ _ hij ↦ maxLocalTime_mono hij
  · exact fun _ _ hij hmax ↦ favoriteSites_subset_of_maxLocalTime_eq hij hmax
  · exact hcard

/-- The exact deterministic estimate behind Erdős Problem 1166.  Finitely
many early times contribute the first summand; every later maximal-local-time
level contributes at most `r` sites. -/
theorem favoriteUnion_card_le_early_add_mul_max (s : ℕ → Site) (N n r : ℕ)
    (hcard : ∀ k, N ≤ k → (favoriteSites s k).card ≤ r) :
    (favoriteUnion s n).card ≤
      (favoriteUnionBefore s N).card + r * maxLocalTime s n := by
  have hsubset : favoriteUnion s n ⊆
      favoriteUnionBefore s N ∪ intervalUnion (favoriteSites s) N n := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hk, hxF⟩
    simp only [Finset.mem_range] at hk
    by_cases hkN : k < N
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_range.mpr hkN, hxF⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨k, Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt hkN, by omega⟩, hxF⟩
  calc
    (favoriteUnion s n).card ≤
        (favoriteUnionBefore s N ∪ intervalUnion (favoriteSites s) N n).card :=
      Finset.card_le_card hsubset
    _ ≤ (favoriteUnionBefore s N).card +
        (intervalUnion (favoriteSites s) N n).card :=
      Finset.card_union_le _ _
    _ ≤ (favoriteUnionBefore s N).card + r * maxLocalTime s n :=
      Nat.add_le_add_left (intervalFavoriteUnion_card_le s N n r hcard) _

/-- The eventual conclusion of the planar favourite-site theorem used in the
resolution of Problem 1166. -/
def EventuallyAtMostThree (s : ℕ → Site) : Prop :=
  ∀ᶠ n : ℕ in atTop, (favoriteSites s n).card ≤ 3

/-- The eventual consequence of the Erdős--Taylor maximal-local-time bound. -/
def HasMaxLocalTimeLogSqBound (s : ℕ → Site) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    (maxLocalTime s n : ℝ) ≤ C * Real.log (n : ℝ) ^ 2

/-- A monotone sequence which is quadratically bounded at dyadic times is
quadratically bounded in the natural logarithm at every sufficiently large
time.  This is the deterministic interpolation step in the standard
Borel--Cantelli proof of the Erdős--Taylor upper bound. -/
theorem eventually_log_sq_of_eventually_dyadic
    (M : ℕ → ℕ) (hmono : Monotone M) (A : ℝ) (hA : 0 ≤ A)
    (hdyadic : ∀ᶠ k : ℕ in atTop,
      (M (2 ^ k) : ℝ) ≤ A * (k : ℝ) ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      (M n : ℝ) ≤ (4 * A / Real.log 2 ^ 2) * Real.log (n : ℝ) ^ 2 := by
  rw [Filter.eventually_atTop] at hdyadic ⊢
  obtain ⟨K, hK⟩ := hdyadic
  refine ⟨2 ^ max K 2, ?_⟩
  intro n hn
  let j := Nat.log 2 n + 1
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ max K 2) hn
  have hjK : K ≤ j := by
    have hpowK : 2 ^ K ≤ n :=
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_left K 2)).trans hn
    have hKlog : K ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by omega) hpowK
    omega
  have hnj : n ≤ 2 ^ j := (Nat.lt_pow_succ_log_self (by omega) n).le
  have hMj : (M n : ℝ) ≤ M (2 ^ j) := by
    exact_mod_cast hmono hnj
  have hjbound : (M (2 ^ j) : ℝ) ≤ A * (j : ℝ) ^ 2 := hK j hjK
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowlog : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 hnpos.ne'
  have hloglower : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowlog
  have hnlarge : (4 : ℕ) ≤ n := by
    have : 2 ^ 2 ≤ 2 ^ max K 2 :=
      Nat.pow_le_pow_right (by omega) (Nat.le_max_right K 2)
    norm_num at this ⊢
    exact this.trans hn
  have hlogn : Real.log 2 ≤ Real.log n := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show (2 : ℕ) ≤ n by omega)
  have hjlog : (j : ℝ) * Real.log 2 ≤ 2 * Real.log n := by
    dsimp [j]
    push_cast
    nlinarith
  have hjnonneg : 0 ≤ (j : ℝ) := by positivity
  have hlogsq : (j : ℝ) ^ 2 ≤
      (4 / Real.log 2 ^ 2) * Real.log (n : ℝ) ^ 2 := by
    have hsquare := (sq_le_sq₀ (mul_nonneg hjnonneg hlog2pos.le)
      (by positivity : 0 ≤ 2 * Real.log (n : ℝ))).2 hjlog
    field_simp
    nlinarith
  calc
    (M n : ℝ) ≤ (M (2 ^ j) : ℕ) := hMj
    _ ≤ A * (j : ℝ) ^ 2 := hjbound
    _ ≤ A * ((4 / Real.log 2 ^ 2) * Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlogsq hA
    _ = (4 * A / Real.log 2 ^ 2) * Real.log (n : ℝ) ^ 2 := by ring

/-- Dyadic maximal-local-time estimates imply the eventual logarithmic-square
bound in the path property used by the main theorem. -/
theorem hasMaxLocalTimeLogSqBound_of_dyadic (s : ℕ → Site) (A : ℝ) (hA : 0 < A)
    (hdyadic : ∀ᶠ k : ℕ in atTop,
      (maxLocalTime s (2 ^ k) : ℝ) ≤ A * (k : ℝ) ^ 2) :
    HasMaxLocalTimeLogSqBound s := by
  refine ⟨4 * A / Real.log 2 ^ 2, by positivity, ?_⟩
  exact eventually_log_sq_of_eventually_dyadic (maxLocalTime s)
    (fun _ _ hij ↦ maxLocalTime_mono hij) A hA.le hdyadic

/-- A convenient quantitative form of the first Borel--Cantelli lemma for
the geometric tail used in the dyadic maximal-local-time argument. -/
theorem ae_eventually_notMem_of_measure_le_four_inv_pow
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (bad : ℕ → Set Ω)
    (hbad : ∀ k, μ (bad k) ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k) :
    ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ bad k := by
  apply MeasureTheory.ae_eventually_notMem
  have hle : (∑' k, μ (bad k)) ≤
      ∑' k : ℕ, 2 * ((4 : ℝ≥0∞)⁻¹) ^ k :=
    ENNReal.summable.tsum_le_tsum hbad ENNReal.summable
  have hratio : (4 : ℝ≥0∞)⁻¹ < 1 := by norm_num
  have hgeom : (∑' k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k) < ∞ :=
    tsum_geometric_lt_top.mpr hratio
  have hbound : (∑' k : ℕ, 2 * ((4 : ℝ≥0∞)⁻¹) ^ k) < ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (by norm_num) hgeom
  exact (hle.trans_lt hbound).ne

/-- The same Borel--Cantelli consequence when the geometric estimate is only
known after a finite number of dyadic scales. -/
theorem ae_eventually_notMem_of_eventually_measure_le_four_inv_pow
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (bad : ℕ → Set Ω)
    (hbad : ∀ᶠ k : ℕ in atTop,
      μ (bad k) ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ k) :
    ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω ∉ bad k := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hbad
  have hshift : ∀ j : ℕ, μ (bad (K + j)) ≤
      2 * ((4 : ℝ≥0∞)⁻¹) ^ j := by
    intro j
    calc
      μ (bad (K + j)) ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ (K + j) :=
        hK _ (Nat.le_add_right K j)
      _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ j := by
        apply mul_le_mul_of_nonneg_left
        · exact pow_le_pow_of_le_one (a := ((4 : ℝ≥0∞)⁻¹)) (by positivity)
            (by norm_num) (Nat.le_add_left j K)
        · exact bot_le
  have hae := ae_eventually_notMem_of_measure_le_four_inv_pow μ
    (fun j ↦ bad (K + j)) hshift
  filter_upwards [hae] with ω hω
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hω
  apply Filter.eventually_atTop.mpr
  refine ⟨K + J, fun k hk ↦ ?_⟩
  have hKk : K ≤ k := le_trans (Nat.le_add_right K J) hk
  have hJsub : J ≤ k - K := by omega
  simpa [Nat.add_sub_of_le hKk] using hJ (k - K) hJsub

/-- The stronger exponent-two conclusion asked for in Erdős Problem 1166. -/
def HasCumulativeFavoriteLogSqBound (s : ℕ → Site) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    ((favoriteUnion s n).card : ℝ) ≤ C * Real.log (n : ℝ) ^ 2

/-- Pathwise form of the resolution: the eventual three-favourites theorem
and the Erdős--Taylor bound imply the cumulative `O((log n)^2)` bound. -/
theorem hasCumulativeFavoriteLogSqBound
    (s : ℕ → Site) (hthree : EventuallyAtMostThree s)
    (hmax : HasMaxLocalTimeLogSqBound s) :
    HasCumulativeFavoriteLogSqBound s := by
  rcases Filter.eventually_atTop.mp hthree with ⟨N, hN⟩
  rcases hmax with ⟨C, hCpos, hC⟩
  refine ⟨((favoriteUnionBefore s N).card : ℝ) + 3 * C, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop 3, hC] with
      n hnN hn3 hmaxn
  have hfinite := favoriteUnion_card_le_early_add_mul_max s N n 3 hN
  have hfiniteReal :
      ((favoriteUnion s n).card : ℝ) ≤
        ((favoriteUnionBefore s N).card : ℝ) + 3 * (maxLocalTime s n : ℝ) := by
    exact_mod_cast hfinite
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn3)
  have hlogsq : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- Measure-theoretic assembly of the two probability-one source results.
The measure and process are left abstract because the deduction depends only
on their two stated almost-everywhere path properties. -/
theorem erdos_1166_of_ae_inputs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → ℕ → Site)
    (hthree : ∀ᵐ ω ∂μ, EventuallyAtMostThree (S ω))
    (hmax : ∀ᵐ ω ∂μ, HasMaxLocalTimeLogSqBound (S ω)) :
    ∀ᵐ ω ∂μ, HasCumulativeFavoriteLogSqBound (S ω) := by
  filter_upwards [hthree, hmax] with ω hthreeω hmaxω
  exact hasCumulativeFavoriteLogSqBound (S ω) hthreeω hmaxω

/-- The precise planar conclusion of Hao--Li--Okada--Zheng used here. -/
def HLOZPlanarConclusion : Prop :=
  ∀ᵐ s ∂simpleRandomWalkLaw, EventuallyAtMostThree s


/-- A path has at least four favourite sites at some time at which its
maximal local time is exactly `m`. -/
def fourFavoritesAtLevel (m : ℕ) : Set (ℕ → Site) :=
  {s | ∃ n, maxLocalTime s n = m ∧ 4 ≤ (favoriteSites s n).card}

/-- Sites whose local time has reached at least `m` by time `n`.  Restricting
to `visitedSites` is exact for positive levels and keeps the object finite. -/
def sitesAtLeastLevel (s : ℕ → Site) (n m : ℕ) : Finset Site :=
  (visitedSites s n).filter fun x ↦ m ≤ localTime s n x

/-- The finite visited set at a fixed horizon is measurable in the path. -/
theorem measurable_visitedSites_eval (n : ℕ) :
    Measurable fun s : ℕ → Site ↦ visitedSites s n := by
  rw [measurable_finset_iff]
  intro x
  simp only [visitedSites, Finset.mem_image]
  fun_prop

/-- The finite set of sites above a fixed local-time level is measurable in
the path. -/
theorem measurable_sitesAtLeastLevel_eval (n m : ℕ) :
    Measurable fun s : ℕ → Site ↦ sitesAtLeastLevel s n m := by
  rw [measurable_finset_iff]
  intro x
  simp only [sitesAtLeastLevel, Finset.mem_filter]
  exact ((measurable_finset_mem x).comp (measurable_visitedSites_eval n)).and
    (measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (measurable_localTime_eval n x)))

/-- The number of sites above a fixed level is measurable in the path. -/
theorem measurable_card_sitesAtLeastLevel_eval (n m : ℕ) :
    Measurable fun s : ℕ → Site ↦ (sitesAtLeastLevel s n m).card := by
  exact (measurable_of_countable (fun t : Finset Site ↦ t.card)).comp
    (measurable_sitesAtLeastLevel_eval n m)

/-- The visited set through time `n` is measurable from the canonical walk
history through time `n`. -/
theorem measurable_visitedSites_canonical (n : ℕ) :
    Measurable[HLOZFoundation.canonicalFiltration n]
      (fun s : ℕ → Site ↦ visitedSites s n) := by
  letI : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration n
  change Measurable (fun s : ℕ → Site ↦ visitedSites s n)
  rw [measurable_finset_iff]
  intro x
  simp only [visitedSites, Finset.mem_image]
  apply Measurable.exists
  intro j
  by_cases hj : j ∈ Finset.range (n + 1)
  · simp only [hj, true_and]
    apply measurableSet_setOfPred.mp
    exact measurableSet_eq_fun
      (HLOZFoundation.adapted_coordinateProcess.measurable_le (by
        simp only [Finset.mem_range] at hj
        omega)) measurable_const
  · simp [hj]

/-- The level set through time `n` is measurable from the canonical walk
history through time `n`. -/
theorem measurable_sitesAtLeastLevel_canonical (n m : ℕ) :
    Measurable[HLOZFoundation.canonicalFiltration n]
      (fun s : ℕ → Site ↦ sitesAtLeastLevel s n m) := by
  letI : MeasurableSpace (ℕ → Site) := HLOZFoundation.canonicalFiltration n
  change Measurable (fun s : ℕ → Site ↦ sitesAtLeastLevel s n m)
  rw [measurable_finset_iff]
  intro x
  simp only [sitesAtLeastLevel, Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp (measurable_visitedSites_canonical n)
  · exact measurableSet_setOfPred.mp
      (measurableSet_le measurable_const
        (HLOZFoundation.adapted_localTime x n))

/-- The number of sites which have reached local-time level `m` is an adapted
process for the canonical walk filtration. -/
theorem adapted_card_sitesAtLeastLevel (m : ℕ) :
    Adapted HLOZFoundation.canonicalFiltration
      (fun n s ↦ (sitesAtLeastLevel s n m).card) := by
  intro n
  exact (measurable_of_countable (fun t : Finset Site ↦ t.card)).comp
    (measurable_sitesAtLeastLevel_canonical n m)

/-- HLOZ's threshold time `T_m^k`: the first time at which at least `k`
sites have accumulated local time at least `m`. -/
noncomputable def firstKSitesReachLevel (m k : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  hittingAfter (fun n s ↦ (sitesAtLeastLevel s n m).card) (Set.Ici k) 0

/-- The threshold time `T_m^k` is a stopping time. -/
theorem isStoppingTime_firstKSitesReachLevel (m k : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (firstKSitesReachLevel m k) := by
  exact (adapted_card_sitesAtLeastLevel m).isStoppingTime_hittingAfter
    measurableSet_Ici

/-- Equality-based version of HLOZ's threshold time: the first time exactly
`k` sites have accumulated local time at least `m`. -/
noncomputable def firstExactlyKSitesReachLevel (m k : ℕ) :
    (ℕ → Site) → WithTop ℕ :=
  hittingAfter (fun n s ↦ (sitesAtLeastLevel s n m).card) ({k} : Set ℕ) 0

/-- The equality-based threshold time is also a stopping time. -/
theorem isStoppingTime_firstExactlyKSitesReachLevel (m k : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (firstExactlyKSitesReachLevel m k) := by
  exact (adapted_card_sitesAtLeastLevel m).isStoppingTime_hittingAfter
    (measurableSet_singleton k)

/-- First time, at or after a possibly unbounded stopping time, that exactly
`k` sites have reached local-time level `m`. -/
noncomputable def firstExactlyKSitesReachLevelAfterStopping (m k : ℕ)
    (τ : (ℕ → Site) → WithTop ℕ) : (ℕ → Site) → WithTop ℕ :=
  fun s ↦ if τ s = ⊤ then ⊤ else
    hittingAfter (fun n s ↦ (sitesAtLeastLevel s n m).card)
      ({k} : Set ℕ) (τ s).untopA s

/-- Hitting an exact level after a possibly unbounded stopping time is again
a stopping time. -/
theorem isStoppingTime_firstExactlyKSitesReachLevelAfterStopping
    (m k : ℕ) {τ : (ℕ → Site) → WithTop ℕ}
    (hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (firstExactlyKSitesReachLevelAfterStopping m k τ) := by
  intro n
  have hset : {s | firstExactlyKSitesReachLevelAfterStopping m k τ s ≤ n} =
      ⋃ j : ℕ, ⋃ (_ : j ≤ n),
        {s | τ s = j} ∩
          {s | hittingAfter
            (fun q s ↦ (sitesAtLeastLevel s q m).card)
            ({k} : Set ℕ) j s ≤ n} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases ht : τ s = ⊤
      · simp [firstExactlyKSitesReachLevelAfterStopping, ht] at h
      · lift τ s to ℕ using ht with j hj
        have hhit : hittingAfter
            (fun q s ↦ (sitesAtLeastLevel s q m).card)
            ({k} : Set ℕ) j s ≤ n := by
          simpa [firstExactlyKSitesReachLevelAfterStopping, ← hj] using h
        have hjn : j ≤ n := by
          exact WithTop.coe_le_coe.mp
            ((le_hittingAfter
              (u := fun q s ↦ (sitesAtLeastLevel s q m).card)
              (s := ({k} : Set ℕ)) (n := j) s).trans hhit)
        exact ⟨j, hjn, rfl, hhit⟩
    · rintro ⟨j, hjn, hτj, hhit⟩
      have ht : τ s ≠ ⊤ := by simp [hτj]
      simpa [firstExactlyKSitesReachLevelAfterStopping, ht, hτj] using hhit
  change MeasurableSet[HLOZFoundation.canonicalFiltration n]
    {s | firstExactlyKSitesReachLevelAfterStopping m k τ s ≤ n}
  rw [hset]
  refine MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun hjn ↦ ?_
  exact (HLOZFoundation.canonicalFiltration.mono hjn _
      (hτ.measurableSet_eq_of_countable j)).inter
    ((adapted_card_sitesAtLeastLevel m).isStoppingTime_hittingAfter
      (measurableSet_singleton k) n)

/-- The literal recursive definition (2.7) of HLOZ: `T_m^0=0`, and
`T_m^(k+1)` is the first later time at which exactly `k+1` sites have
reached level `m`. -/
noncomputable def recursiveExactlyKSitesReachLevel (m : ℕ) :
    ℕ → (ℕ → Site) → WithTop ℕ
  | 0 => fun _ ↦ 0
  | k + 1 => firstExactlyKSitesReachLevelAfterStopping m (k + 1)
      (fun s ↦ recursiveExactlyKSitesReachLevel m k s + 1)

/-- Every literal recursive HLOZ threshold is a stopping time. -/
theorem isStoppingTime_recursiveExactlyKSitesReachLevel (m k : ℕ) :
    IsStoppingTime HLOZFoundation.canonicalFiltration
      (recursiveExactlyKSitesReachLevel m k) := by
  induction k with
  | zero =>
      simpa [recursiveExactlyKSitesReachLevel] using
        isStoppingTime_const HLOZFoundation.canonicalFiltration (0 : ℕ)
  | succ k ih =>
      rw [recursiveExactlyKSitesReachLevel]
      exact isStoppingTime_firstExactlyKSitesReachLevelAfterStopping m (k + 1)
        (ih.add_const' 1)

/-- Starting the after-stopping construction at time zero recovers the direct
first-exactly-`k` threshold. -/
theorem firstExactlyKSitesReachLevelAfterStopping_zero (m k : ℕ) :
    firstExactlyKSitesReachLevelAfterStopping m k (fun _ ↦ 0) =
      firstExactlyKSitesReachLevel m k := by
  funext s
  simp [firstExactlyKSitesReachLevelAfterStopping,
    firstExactlyKSitesReachLevel]

/-- Every finite fiber of the literal recursive HLOZ threshold, pulled back
to increment space, belongs to the increment history through that time. -/
theorem measurableSet_recursiveExactlyKSitesReachLevel_fiber_iidHistory
    (m k n : ℕ) :
    MeasurableSet[ProbabilityTheory.iidHistory (X := Direction) n]
      {ω : ℕ → Direction |
        recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) = n} := by
  have hPath : MeasurableSet[HLOZFoundation.canonicalFiltration n]
      {s : ℕ → Site | recursiveExactlyKSitesReachLevel m k s = n} :=
    (isStoppingTime_recursiveExactlyKSitesReachLevel m k).measurableSet_eq_of_countable n
  exact HLOZFoundation.measurable_simpleRandomWalk_iidHistory_canonicalFiltration
    n hPath

/-- This is exactly the finite-fiber past-measurability premise required by
the unbounded iid restart theorem. -/
theorem measurableSet_recursiveExactlyKSitesReachLevel_finite_inter_fiber
    (m k n : ℕ) :
    MeasurableSet[ProbabilityTheory.iidHistory (X := Direction) n]
      ({ω : ℕ → Direction |
          recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤} ∩
        {ω | recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) = n}) := by
  have hfiber :=
    measurableSet_recursiveExactlyKSitesReachLevel_fiber_iidHistory m k n
  have heq :
      {ω : ℕ → Direction |
        recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤} ∩
        {ω | recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) = n} =
      {ω | recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) = n} := by
    apply Set.inter_eq_right.mpr
    intro ω hω
    change recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) =
      (n : WithTop ℕ) at hω
    change recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤
    rw [hω]
    simp
  rw [heq]
  exact hfiber

/-- Direct iid restart at HLOZ's literal recursive threshold, restricted to
the event where the threshold is finite. -/
theorem incrementLaw_inter_blockAfter_recursiveExactlyKSitesReachLevel_eq_mul
    (m k r : ℕ) {B : Set (Fin r → Direction)} (hB : MeasurableSet B) :
    incrementLaw
        ({ω : ℕ → Direction |
            recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤} ∩
          ProbabilityTheory.iidBlockAfter (X := Direction)
            (fun ω ↦ (recursiveExactlyKSitesReachLevel m k
              (simpleRandomWalk ω)).untopA) r ⁻¹' B) =
      incrementLaw
          {ω : ℕ → Direction |
            recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤} *
        (Measure.infinitePi fun _ : Fin r ↦
          (PMF.uniformOfFintype Direction).toMeasure) B := by
  unfold incrementLaw
  apply ProbabilityTheory.measure_inter_iidBlockAfter_untopA_eq_mul
    ((PMF.uniformOfFintype Direction).toMeasure)
    (fun ω ↦ recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω)) r
    {ω | recursiveExactlyKSitesReachLevel m k (simpleRandomWalk ω) ≠ ⊤}
  · exact fun _ h ↦ h
  · intro n
    exact measurableSet_recursiveExactlyKSitesReachLevel_finite_inter_fiber m k n
  · exact hB

/-- For a fixed level, the set of sites which have reached that level grows
monotonically with time. -/
theorem sitesAtLeastLevel_mono_time {s : ℕ → Site} {i j m : ℕ} (hij : i ≤ j) :
    sitesAtLeastLevel s i m ⊆ sitesAtLeastLevel s j m := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxv, hxm⟩
  apply Finset.mem_filter.mpr
  exact ⟨visitedSites_mono hij hxv, hxm.trans (localTime_mono hij x)⟩

/-- In one time step the local time at `x` increases by one exactly when the
new position is `x`. -/
theorem localTime_succ (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s (n + 1) x =
      localTime s n x + if s (n + 1) = x then 1 else 0 := by
  have hrange : Finset.range (n + 2) =
      insert (n + 1) (Finset.range (n + 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert]
    omega
  unfold localTime
  rw [show n + 1 + 1 = n + 2 by omega, hrange]
  rw [Finset.filter_insert]
  by_cases h : s (n + 1) = x <;> simp [h]

/-- In one time step, the only site which can newly reach a prescribed local
time level is the new position. -/
theorem sitesAtLeastLevel_succ_subset (s : ℕ → Site) (n m : ℕ) :
    sitesAtLeastLevel s (n + 1) m ⊆
      insert (s (n + 1)) (sitesAtLeastLevel s n m) := by
  intro x hx
  by_cases hnew : x = s (n + 1)
  · simp [hnew]
  · have hnew' : s (n + 1) ≠ x := Ne.symm hnew
    have hxv : x ∈ visitedSites s (n + 1) := (Finset.mem_filter.mp hx).1
    have hxm : m ≤ localTime s (n + 1) x := (Finset.mem_filter.mp hx).2
    have hxvold : x ∈ visitedSites s n := by
      rcases Finset.mem_image.mp hxv with ⟨j, hj, hsj⟩
      have hjlt : j < n + 2 := Finset.mem_range.mp hj
      have hjne : j ≠ n + 1 := by
        intro hjEq
        apply hnew
        simpa [hjEq] using hsj.symm
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_range.mpr ?_, hsj⟩
      omega
    have hltold : localTime s (n + 1) x = localTime s n x := by
      rw [localTime_succ, if_neg hnew', add_zero]
    simp only [Finset.mem_insert]
    right
    exact Finset.mem_filter.mpr ⟨hxvold, by simpa [hltold] using hxm⟩

/-- Consequently, the number of sites which have reached a fixed level grows
by at most one in a single time step.  This is what makes the `≥ k`
threshold time coincide with HLOZ's first time of equality with `k`. -/
theorem card_sitesAtLeastLevel_succ_le (s : ℕ → Site) (n m : ℕ) :
    (sitesAtLeastLevel s (n + 1) m).card ≤
      (sitesAtLeastLevel s n m).card + 1 := by
  calc
    _ ≤ (insert (s (n + 1)) (sitesAtLeastLevel s n m)).card :=
      Finset.card_le_card (sitesAtLeastLevel_succ_subset s n m)
    _ ≤ _ := Finset.card_insert_le _ _

/-- At a finite positive threshold time, exactly `k` sites (rather than merely
at least `k`) have reached the prescribed level.  This identifies our robust
`Set.Ici k` stopping-time definition with the equality-based definition in
HLOZ. -/
theorem card_at_firstKSitesReachLevel_eq
    (s : ℕ → Site) (m k : ℕ) (hk : 0 < k)
    (hfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    (sitesAtLeastLevel s (firstKSitesReachLevel m k s).untopA m).card = k := by
  let T := firstKSitesReachLevel m k s
  let t : ℕ := T.untopA
  have hTcoe : (t : WithTop ℕ) = T := by
    dsimp only [t, T]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hge : k ≤ (sitesAtLeastLevel s t m).card := by
    have hmem : (sitesAtLeastLevel s t m).card ∈ Set.Ici k := by
      exact hittingAfter_mem_set_of_ne_top
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici k) (n := 0) (ω := s) hfinite
    exact hmem
  have hle : (sitesAtLeastLevel s t m).card ≤ k := by
    by_cases ht0 : t = 0
    · have hle0 : (sitesAtLeastLevel s 0 m).card ≤ k := by
        calc
          (sitesAtLeastLevel s 0 m).card ≤ (visitedSites s 0).card :=
            Finset.card_filter_le _ _
          _ = 1 := by simp [visitedSites]
          _ ≤ k := hk
      simpa [ht0] using hle0
    · obtain ⟨t', htsucc⟩ := Nat.exists_eq_succ_of_ne_zero ht0
      have hprevLt : (t' : WithTop ℕ) < T := by
        rw [← hTcoe]
        rw [htsucc]
        exact_mod_cast Nat.lt_succ_self t'
      have hnot : (sitesAtLeastLevel s t' m).card ∉ Set.Ici k := by
        exact notMem_of_lt_hittingAfter
          (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
          (s := Set.Ici k) (n := 0) (ω := s) hprevLt (Nat.zero_le t')
      have hprev : (sitesAtLeastLevel s t' m).card < k := by
        simpa only [Set.mem_Ici, not_le] using hnot
      have hstep := card_sitesAtLeastLevel_succ_le s t' m
      have hstep' : (sitesAtLeastLevel s t'.succ m).card ≤
          (sitesAtLeastLevel s t' m).card + 1 := by
        simpa [Nat.succ_eq_add_one] using hstep
      rw [htsucc]
      omega
  exact Nat.le_antisymm hle hge

/-- Because the level-count process grows by at most one at each step, for
positive `k` the first time it is at least `k` is exactly the first time it is
equal to `k`. -/
theorem firstExactlyKSitesReachLevel_eq (s : ℕ → Site) (m k : ℕ)
    (hk : 0 < k) :
    firstExactlyKSitesReachLevel m k s = firstKSitesReachLevel m k s := by
  let T := firstKSitesReachLevel m k s
  let E := firstExactlyKSitesReachLevel m k s
  by_cases hT : T = ⊤
  · have hTnone : ∀ j, 0 ≤ j →
        (sitesAtLeastLevel s j m).card ∉ Set.Ici k := by
      simpa only [T, firstKSitesReachLevel, hittingAfter_eq_top_iff] using hT
    have hEnone : ∀ j, 0 ≤ j →
        (sitesAtLeastLevel s j m).card ∉ ({k} : Set ℕ) := by
      intro j hj hjeq
      have heq : (sitesAtLeastLevel s j m).card = k := by
        simpa only [Set.mem_singleton_iff] using hjeq
      exact hTnone j hj (by
        simpa only [Set.mem_Ici, heq] using (le_refl k))
    have hE : E = ⊤ := by
      simpa only [E, firstExactlyKSitesReachLevel, hittingAfter_eq_top_iff]
        using hEnone
    exact hE.trans hT.symm
  · have hcard : (sitesAtLeastLevel s T.untopA m).card = k := by
      exact card_at_firstKSitesReachLevel_eq s m k hk hT
    have hEleT : E ≤ T := by
      have hle : E ≤ (T.untopA : WithTop ℕ) := by
        exact hittingAfter_le_of_mem
          (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
          (s := ({k} : Set ℕ)) (n := 0) (i := T.untopA) (ω := s)
          (Nat.zero_le _) (by simpa only [Set.mem_singleton_iff] using hcard)
      have hcoe : (T.untopA : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop hT]
        exact WithTop.coe_untop T hT
      exact hle.trans_eq hcoe
    have hTleE : T ≤ E := by
      by_cases hE : E = ⊤
      · simp [hE]
      · have hmem : (sitesAtLeastLevel s E.untopA m).card ∈ ({k} : Set ℕ) := by
          exact hittingAfter_mem_set_of_ne_top
            (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
            (s := ({k} : Set ℕ)) (n := 0) (ω := s) hE
        have hle : T ≤ (E.untopA : WithTop ℕ) := by
          exact hittingAfter_le_of_mem
            (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
            (s := Set.Ici k) (n := 0) (i := E.untopA) (ω := s)
            (Nat.zero_le _) (by
              have heq : (sitesAtLeastLevel s E.untopA m).card = k := by
                simpa only [Set.mem_singleton_iff] using hmem
              simpa only [Set.mem_Ici, heq] using (le_refl k))
        have hcoe : (E.untopA : WithTop ℕ) = E := by
          rw [WithTop.untopA_eq_untop hE]
          exact WithTop.coe_untop E hE
        exact hle.trans_eq hcoe
    exact le_antisymm hEleT hTleE

/-- HLOZ's location `L_m^k` where the `k`-th site to reach local-time level
`m` is created.  Its value is relevant only when the corresponding threshold
time is finite. -/
noncomputable def levelCreationSite (s : ℕ → Site) (m k : ℕ) : Site :=
  s (firstKSitesReachLevel m k s).untopA

/-- At a finite positive threshold, the site created there has local time
exactly `m`.  In particular the threshold position is genuinely the newly
created level-`m` site, not merely an arbitrary position at that stopping
time. -/
theorem levelCreationSite_localTime_eq
    (s : ℕ → Site) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    localTime s (firstKSitesReachLevel m k s).untopA
      (levelCreationSite s m k) = m := by
  let T := firstKSitesReachLevel m k s
  let t : ℕ := T.untopA
  let x : Site := s t
  change localTime s t x = m
  have hTcoe : (t : WithTop ℕ) = T := by
    dsimp only [t, T]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hcard : (sitesAtLeastLevel s t m).card = k := by
    exact card_at_firstKSitesReachLevel_eq s m k hk hfinite
  by_cases ht0 : t = 0
  · have hxmem : x ∈ sitesAtLeastLevel s t m := by
      have hpos : 0 < (sitesAtLeastLevel s t m).card := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
      have hyv : y ∈ visitedSites s 0 := by
        simpa [ht0] using (Finset.mem_filter.mp hy).1
      have hyx : y = x := by
        simp [visitedSites, x, ht0] at hyv ⊢
        exact hyv
      simpa [hyx, ht0] using hy
    have hxm : m ≤ localTime s t x := (Finset.mem_filter.mp hxmem).2
    have hlt : localTime s t x = 1 := by
      change ((Finset.range (t + 1)).filter (fun j ↦ s j = x)).card = 1
      rw [ht0]
      have hx : x = s 0 := by simp [x, ht0]
      rw [hx]
      change ((Finset.range 1).filter (fun j ↦ s j = s 0)).card = 1
      have hf : (Finset.range 1).filter (fun j ↦ s j = s 0) = {0} := by
        ext j
        by_cases hj : j = 0 <;> simp [hj]
      rw [hf]
      simp
    omega
  · obtain ⟨t', htsucc⟩ := Nat.exists_eq_succ_of_ne_zero ht0
    have hprevLt : (t' : WithTop ℕ) < T := by
      rw [← hTcoe, htsucc]
      exact_mod_cast Nat.lt_succ_self t'
    have hnot : (sitesAtLeastLevel s t' m).card ∉ Set.Ici k := by
      exact notMem_of_lt_hittingAfter
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici k) (n := 0) (ω := s) hprevLt (Nat.zero_le t')
    have hprev : (sitesAtLeastLevel s t' m).card < k := by
      simpa only [Set.mem_Ici, not_le] using hnot
    have hxmem : x ∈ sitesAtLeastLevel s t m := by
      by_contra hxnot
      have hsub : sitesAtLeastLevel s t m ⊆ sitesAtLeastLevel s t' m := by
        intro y hy
        have hy' := sitesAtLeastLevel_succ_subset s t' m
          (by simpa [Nat.succ_eq_add_one, htsucc] using hy)
        simp only [Finset.mem_insert] at hy'
        rcases hy' with hyx | hyold
        · exfalso
          apply hxnot
          simpa [x, htsucc, Nat.succ_eq_add_one, hyx] using hy
        · exact hyold
      have hle := Finset.card_le_card hsub
      omega
    have hxold : x ∉ sitesAtLeastLevel s t' m := by
      intro hxold
      have hmono := sitesAtLeastLevel_mono_time
        (s := s) (i := t') (j := t) (m := m) (by omega)
      have hsub : sitesAtLeastLevel s t m ⊆ sitesAtLeastLevel s t' m := by
        intro y hy
        have hy' := sitesAtLeastLevel_succ_subset s t' m
          (by simpa [Nat.succ_eq_add_one, htsucc] using hy)
        simp only [Finset.mem_insert] at hy'
        rcases hy' with hyx | hyold
        · simpa [x, htsucc, Nat.succ_eq_add_one, hyx] using hxold
        · exact hyold
      have heq := Finset.Subset.antisymm hsub hmono
      have := congrArg Finset.card heq
      omega
    have hxoldlt : localTime s t' x < m := by
      by_contra hnotlt
      have hmle : m ≤ localTime s t' x := by omega
      have hxv : x ∈ visitedSites s t' := by
        by_contra hxnv
        have hz := localTime_eq_zero_of_not_mem_visitedSites hxnv
        omega
      exact hxold (Finset.mem_filter.mpr ⟨hxv, hmle⟩)
    have hxm : m ≤ localTime s t x := (Finset.mem_filter.mp hxmem).2
    have hstep : localTime s t x = localTime s t' x + 1 := by
      rw [htsucc]
      simpa [x, htsucc, Nat.succ_eq_add_one] using
        (localTime_succ s t' x)
    omega

/-- Raising the requested number of level-`m` sites can only delay its first
threshold time. -/
theorem firstKSitesReachLevel_mono_k (s : ℕ → Site) (m : ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    firstKSitesReachLevel m i s ≤ firstKSitesReachLevel m j s := by
  let Tj := firstKSitesReachLevel m j s
  by_cases hjtop : Tj = ⊤
  · simp [Tj, hjtop]
  · have hjmem : (sitesAtLeastLevel s Tj.untopA m).card ∈ Set.Ici j := by
      exact hittingAfter_mem_set_of_ne_top
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici j) (n := 0) (ω := s) hjtop
    have himem : (sitesAtLeastLevel s Tj.untopA m).card ∈ Set.Ici i :=
      hij.trans hjmem
    have hle : firstKSitesReachLevel m i s ≤ (Tj.untopA : WithTop ℕ) := by
      exact hittingAfter_le_of_mem
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici i) (n := 0) (i := Tj.untopA) (ω := s)
        (Nat.zero_le _) himem
    have hcoe : (Tj.untopA : WithTop ℕ) = Tj := by
      rw [WithTop.untopA_eq_untop hjtop]
      exact WithTop.coe_untop Tj hjtop
    exact hle.trans_eq hcoe

/-- Positive level-site thresholds are strictly increasing until the later
one becomes infinite. -/
theorem firstKSitesReachLevel_strict_mono_k (s : ℕ → Site) (m : ℕ)
    {i j : ℕ} (hi : 0 < i) (hij : i < j)
    (hjfinite : firstKSitesReachLevel m j s ≠ ⊤) :
    firstKSitesReachLevel m i s < firstKSitesReachLevel m j s := by
  have hle := firstKSitesReachLevel_mono_k s m hij.le
  apply lt_of_le_of_ne hle
  intro heq
  have hifinite : firstKSitesReachLevel m i s ≠ ⊤ := by
    intro hitop
    apply hjfinite
    rw [← heq, hitop]
  have hci := card_at_firstKSitesReachLevel_eq s m i hi hifinite
  have hcj := card_at_firstKSitesReachLevel_eq s m j (hi.trans hij) hjfinite
  have htime : (firstKSitesReachLevel m i s).untopA =
      (firstKSitesReachLevel m j s).untopA := by rw [heq]
  rw [htime] at hci
  omega

/-- Just before a positive finite threshold, its creation site has not yet
reached the prescribed local-time level. -/
theorem levelCreationSite_not_mem_previous
    (s : ℕ → Site) (m k : ℕ) (hk : 0 < k)
    (hfinite : firstKSitesReachLevel m k s ≠ ⊤)
    (htpos : 0 < (firstKSitesReachLevel m k s).untopA) :
    levelCreationSite s m k ∉
      sitesAtLeastLevel s ((firstKSitesReachLevel m k s).untopA - 1) m := by
  let T := firstKSitesReachLevel m k s
  let t : ℕ := T.untopA
  let x : Site := s t
  change x ∉ sitesAtLeastLevel s (t - 1) m
  have hTcoe : (t : WithTop ℕ) = T := by
    dsimp only [t, T]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have htpos' : 0 < t := by simpa [t, T] using htpos
  obtain ⟨t', htsucc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have hprevLt : (t' : WithTop ℕ) < T := by
    rw [← hTcoe, htsucc]
    exact_mod_cast Nat.lt_succ_self t'
  have hnot : (sitesAtLeastLevel s t' m).card ∉ Set.Ici k := by
    exact notMem_of_lt_hittingAfter
      (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
      (s := Set.Ici k) (n := 0) (ω := s) hprevLt (Nat.zero_le t')
  have hprev : (sitesAtLeastLevel s t' m).card < k := by
    simpa only [Set.mem_Ici, not_le] using hnot
  have hcard := card_at_firstKSitesReachLevel_eq s m k hk hfinite
  change (sitesAtLeastLevel s t m).card = k at hcard
  have hxmem : x ∈ sitesAtLeastLevel s t m := by
    by_contra hxnot
    have hsub : sitesAtLeastLevel s t m ⊆ sitesAtLeastLevel s t' m := by
      intro y hy
      have hy' := sitesAtLeastLevel_succ_subset s t' m
        (by simpa [Nat.succ_eq_add_one, htsucc] using hy)
      simp only [Finset.mem_insert] at hy'
      rcases hy' with hyx | hyold
      · exfalso
        apply hxnot
        simpa [x, htsucc, Nat.succ_eq_add_one, hyx] using hy
      · exact hyold
    have hle := Finset.card_le_card hsub
    omega
  have hxold : x ∉ sitesAtLeastLevel s t' m := by
    intro hxold
    have hmono := sitesAtLeastLevel_mono_time
      (s := s) (i := t') (j := t) (m := m) (by omega)
    have hsub : sitesAtLeastLevel s t m ⊆ sitesAtLeastLevel s t' m := by
      intro y hy
      have hy' := sitesAtLeastLevel_succ_subset s t' m
        (by simpa [Nat.succ_eq_add_one, htsucc] using hy)
      simp only [Finset.mem_insert] at hy'
      rcases hy' with hyx | hyold
      · simpa [x, htsucc, Nat.succ_eq_add_one, hyx] using hxold
      · exact hyold
    have heq := Finset.Subset.antisymm hsub hmono
    have := congrArg Finset.card heq
    omega
  simpa [htsucc] using hxold

/-- Distinct threshold indices produce distinct level-creation sites. -/
theorem levelCreationSite_ne_of_lt
    (s : ℕ → Site) (m : ℕ) {i j : ℕ}
    (hm : 0 < m) (hi : 0 < i) (hij : i < j)
    (hjfinite : firstKSitesReachLevel m j s ≠ ⊤) :
    levelCreationSite s m i ≠ levelCreationSite s m j := by
  let Ti := firstKSitesReachLevel m i s
  let Tj := firstKSitesReachLevel m j s
  let ti : ℕ := Ti.untopA
  let tj : ℕ := Tj.untopA
  have hstrict := firstKSitesReachLevel_strict_mono_k s m hi hij hjfinite
  have hifinite : Ti ≠ ⊤ := by
    intro hitop
    simp [Ti, hitop] at hstrict
  have hiCoe : (ti : WithTop ℕ) = Ti := by
    dsimp only [ti]
    rw [WithTop.untopA_eq_untop hifinite]
    exact WithTop.coe_untop Ti hifinite
  have hjCoe : (tj : WithTop ℕ) = Tj := by
    dsimp only [tj]
    rw [WithTop.untopA_eq_untop hjfinite]
    exact WithTop.coe_untop Tj hjfinite
  have htlt : ti < tj := by
    exact_mod_cast hiCoe.trans_lt (hstrict.trans_eq hjCoe.symm)
  have hjpos : 0 < tj := by omega
  have hLiLocal : localTime s ti (levelCreationSite s m i) = m := by
    exact levelCreationSite_localTime_eq s m i hm hi hifinite
  have hLiVisited : levelCreationSite s m i ∈ visitedSites s ti := by
    apply Finset.mem_image.mpr
    exact ⟨ti, by simp, rfl⟩
  have hLiLevel : levelCreationSite s m i ∈ sitesAtLeastLevel s ti m := by
    exact Finset.mem_filter.mpr ⟨hLiVisited, by omega⟩
  have hbefore : levelCreationSite s m i ∈ sitesAtLeastLevel s (tj - 1) m := by
    exact sitesAtLeastLevel_mono_time (by omega) hLiLevel
  have hLjNot : levelCreationSite s m j ∉ sitesAtLeastLevel s (tj - 1) m := by
    exact levelCreationSite_not_mem_previous s m j (hi.trans hij) hjfinite hjpos
  intro heq
  exact hLjNot (by simpa [heq] using hbefore)

/-- If the global first hitting time lies after a deterministic start time,
starting the search there does not change the hitting time. -/
theorem hittingAfter_eq_of_le_hittingAfter_zero
    {Ω β : Type*} (u : ℕ → Ω → β) (A : Set β) (n : ℕ) (ω : Ω)
    (h : (n : WithTop ℕ) ≤ hittingAfter u A 0 ω) :
    hittingAfter u A n ω = hittingAfter u A 0 ω := by
  apply le_antisymm
  · let T := hittingAfter u A 0 ω
    by_cases htop : T = ⊤
    · change hittingAfter u A n ω ≤ T
      rw [htop]
      simp
    · have hmem : u T.untopA ω ∈ A :=
        hittingAfter_mem_set_of_ne_top htop
      have hcoe : (T.untopA : WithTop ℕ) = T := by
        rw [WithTop.untopA_eq_untop htop]
        exact WithTop.coe_untop T htop
      have hn : n ≤ T.untopA := by
        apply WithTop.coe_le_coe.mp
        change (n : WithTop ℕ) ≤ T at h
        rw [← hcoe] at h
        exact h
      have hle : hittingAfter u A n ω ≤ (T.untopA : WithTop ℕ) :=
        hittingAfter_le_of_mem hn hmem
      exact hle.trans_eq hcoe
  · exact hittingAfter_mono u A (Nat.zero_le n) ω

/-- At a level `m ≥ 2`, the first one-site threshold cannot occur at time
zero. -/
theorem firstExactlyOne_ge_one (s : ℕ → Site) (m : ℕ) (hm : 2 ≤ m) :
    (1 : WithTop ℕ) ≤ firstExactlyKSitesReachLevel m 1 s := by
  change ((1 : ℕ) : WithTop ℕ) ≤ firstExactlyKSitesReachLevel m 1 s
  apply WithTop.coe_le_iff.mpr
  intro a ha
  by_contra ha0
  have haeq : a = 0 := by omega
  subst a
  have hne : firstExactlyKSitesReachLevel m 1 s ≠ ⊤ := by rw [ha]; simp
  have hmem := hittingAfter_mem_set_of_ne_top
    (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
    (s := ({1} : Set ℕ)) (n := 0) (ω := s) hne
  have hzeroSet : sitesAtLeastLevel s 0 m = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hlt : localTime s 0 x ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    exact (not_le_of_gt (by omega : localTime s 0 x < m))
      (Finset.mem_filter.mp hx).2
  have hzero : (sitesAtLeastLevel s 0 m).card = 0 := by rw [hzeroSet]; simp
  have hun : (firstExactlyKSitesReachLevel m 1 s).untopA = 0 := by
    rw [ha]
    rfl
  change (sitesAtLeastLevel s (firstExactlyKSitesReachLevel m 1 s).untopA m).card ∈
    ({1} : Set ℕ) at hmem
  rw [hun, hzero] at hmem
  simp at hmem

/-- For every source-relevant level `m ≥ 2`, the literal recursive HLOZ
definition (2.7) agrees with the direct first-exactly-`k` threshold. -/
theorem recursiveExactlyKSitesReachLevel_eq (s : ℕ → Site) (m k : ℕ)
    (hm : 2 ≤ m) :
    recursiveExactlyKSitesReachLevel m (k + 1) s =
      firstExactlyKSitesReachLevel m (k + 1) s := by
  induction k generalizing s with
  | zero =>
      rw [recursiveExactlyKSitesReachLevel]
      simp only [Nat.zero_add, WithTop.coe_zero, zero_add]
      unfold firstExactlyKSitesReachLevelAfterStopping
      simp
      exact hittingAfter_eq_of_le_hittingAfter_zero
        (fun n s ↦ (sitesAtLeastLevel s n m).card) ({1} : Set ℕ) 1 s
        (firstExactlyOne_ge_one s m hm)
  | succ k ih =>
      rw [recursiveExactlyKSitesReachLevel]
      have ihfun : (fun s ↦ recursiveExactlyKSitesReachLevel m (k + 1) s) =
          firstExactlyKSitesReachLevel m (k + 1) := by
        funext s
        exact ih s
      simp only [ih]
      let Tk := firstExactlyKSitesReachLevel m (k + 1) s
      let Tnext := firstExactlyKSitesReachLevel m (k + 2) s
      by_cases hTk : Tk = ⊤
      · have hTnext : Tnext = ⊤ := by
          have hle : Tk ≤ Tnext := by
            dsimp only [Tk, Tnext]
            rw [firstExactlyKSitesReachLevel_eq s m (k + 1) (by omega),
              firstExactlyKSitesReachLevel_eq s m (k + 2) (by omega)]
            exact firstKSitesReachLevel_mono_k s m (by omega)
          simpa [hTk] using hle
        simp [firstExactlyKSitesReachLevelAfterStopping, Tk, Tnext, hTk, hTnext]
      · have hstart : ((Tk.untopA + 1 : ℕ) : WithTop ℕ) ≤ Tnext := by
          by_cases hnext : Tnext = ⊤
          · simp [hnext]
          · have hstrict : Tk < Tnext := by
              dsimp only [Tk, Tnext]
              rw [firstExactlyKSitesReachLevel_eq s m (k + 1) (by omega),
                firstExactlyKSitesReachLevel_eq s m (k + 2) (by omega)]
              have hnextK : firstKSitesReachLevel m (k + 2) s ≠ ⊤ := by
                rw [← firstExactlyKSitesReachLevel_eq s m (k + 2) (by omega)]
                simpa [Tnext] using hnext
              exact firstKSitesReachLevel_strict_mono_k s m (by omega)
                (by omega) hnextK
            have hkcoe : (Tk.untopA : WithTop ℕ) = Tk := by
              rw [WithTop.untopA_eq_untop hTk]
              exact WithTop.coe_untop Tk hTk
            have hncoe : (Tnext.untopA : WithTop ℕ) = Tnext := by
              rw [WithTop.untopA_eq_untop hnext]
              exact WithTop.coe_untop Tnext hnext
            have hnat : Tk.untopA < Tnext.untopA := by
              exact_mod_cast hkcoe.trans_lt (hstrict.trans_eq hncoe.symm)
            have hnat' : Tk.untopA + 1 ≤ Tnext.untopA := by omega
            exact (WithTop.coe_le_coe.mpr hnat').trans_eq hncoe
        unfold firstExactlyKSitesReachLevelAfterStopping
        have hkcoe : (Tk.untopA : WithTop ℕ) = Tk := by
          rw [WithTop.untopA_eq_untop hTk]
          exact WithTop.coe_untop Tk hTk
        have hsum : Tk + 1 = ((Tk.untopA + 1 : ℕ) : WithTop ℕ) := by
          rw [← hkcoe]
          norm_num
        change (if Tk + 1 = ⊤ then ⊤ else
          hittingAfter (fun n s ↦ (sitesAtLeastLevel s n m).card)
            ({k + 2} : Set ℕ) (Tk + 1).untopA s) = Tnext
        rw [hsum]
        rw [if_neg (by simp)]
        have hu : (((Tk.untopA + 1 : ℕ) : WithTop ℕ).untopA) =
            Tk.untopA + 1 := by rfl
        rw [hu]
        change hittingAfter
          (fun n s ↦ (sitesAtLeastLevel s n m).card)
          ({k + 2} : Set ℕ) (Tk.untopA + 1) s = Tnext
        dsimp only [Tnext]
        exact hittingAfter_eq_of_le_hittingAfter_zero
          (fun n s ↦ (sitesAtLeastLevel s n m).card)
          ({k + 2} : Set ℕ) (Tk.untopA + 1) s hstart

/-- No site has reached level `m` exactly when the maximal local time is
strictly below `m`. -/
theorem card_sitesAtLeastLevel_eq_zero_iff_max_lt
    (s : ℕ → Site) (n m : ℕ) :
    (sitesAtLeastLevel s n m).card = 0 ↔ maxLocalTime s n < m := by
  constructor
  · intro hzero
    by_contra hnot
    have hmmax : m ≤ maxLocalTime s n := by omega
    obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup
      (Finset.range (n + 1)) (by simp) (fun j ↦ localTime s n (s j))
    have hxmem : s j ∈ sitesAtLeastLevel s n m := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      simpa [maxLocalTime, hsup] using hmmax
    have : 0 < (sitesAtLeastLevel s n m).card :=
      Finset.card_pos.mpr ⟨_, hxmem⟩
    omega
  · intro hmax
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hle := localTime_le_maxLocalTime (Finset.mem_filter.mp hx).1
    have hm := (Finset.mem_filter.mp hx).2
    omega

/-- At a time when the maximal local time is `m`, the sites that have reached
level `m` are exactly the favourite sites. -/
theorem sitesAtLeastLevel_eq_favoriteSites_of_max_eq
    {s : ℕ → Site} {n m : ℕ} (hmax : maxLocalTime s n = m) :
    sitesAtLeastLevel s n m = favoriteSites s n := by
  ext x
  simp only [sitesAtLeastLevel, favoriteSites, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxm⟩
    refine ⟨hx, Nat.le_antisymm (localTime_le_maxLocalTime hx) ?_⟩
    omega
  · rintro ⟨hx, hxmax⟩
    refine ⟨hx, ?_⟩
    omega

/-- HLOZ's level event `M_m^4`: at some time four sites have reached local
time `m`, while no site has yet reached local time `m + 1`. -/
def hlozFourSitesReachLevelFirst (m : ℕ) : Set (ℕ → Site) :=
  {s | ∃ n,
    4 ≤ (sitesAtLeastLevel s n m).card ∧ maxLocalTime s n < m + 1}

/-- HLOZ's four-sites-at-level event is measurable under the canonical path
sigma algebra. -/
theorem measurableSet_hlozFourSitesReachLevelFirst (m : ℕ) :
    MeasurableSet (hlozFourSitesReachLevelFirst m) := by
  rw [show hlozFourSitesReachLevelFirst m = ⋃ n : ℕ,
      {s | 4 ≤ (sitesAtLeastLevel s n m).card ∧ maxLocalTime s n < m + 1} by
    ext s
    simp [hlozFourSitesReachLevelFirst]]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurableSet_le measurable_const
      (measurable_card_sitesAtLeastLevel_eval n m)
  · exact measurableSet_lt (measurable_maxLocalTime_eval n) measurable_const

/-- The source event `M_m^4` is exactly the event that four favourites occur
on the maximal-local-time plateau `m`. -/
theorem hlozFourSitesReachLevelFirst_eq_fourFavoritesAtLevel (m : ℕ) :
    hlozFourSitesReachLevelFirst m = fourFavoritesAtLevel m := by
  ext s
  constructor
  · rintro ⟨n, hfour, hbelow⟩
    have hnonempty : (sitesAtLeastLevel s n m).Nonempty :=
      Finset.card_pos.mp (by omega)
    rcases hnonempty with ⟨x, hx⟩
    have hxm : m ≤ localTime s n x := (Finset.mem_filter.mp hx).2
    have hxvisited : x ∈ visitedSites s n := (Finset.mem_filter.mp hx).1
    have hmaxge : m ≤ maxLocalTime s n :=
      hxm.trans (localTime_le_maxLocalTime hxvisited)
    have hmaxeq : maxLocalTime s n = m := by omega
    refine ⟨n, hmaxeq, ?_⟩
    rw [← sitesAtLeastLevel_eq_favoriteSites_of_max_eq hmaxeq]
    exact hfour
  · rintro ⟨n, hmaxeq, hfour⟩
    refine ⟨n, ?_, by omega⟩
    rw [sitesAtLeastLevel_eq_favoriteSites_of_max_eq hmaxeq]
    exact hfour

/-- HLOZ's original stopping-time presentation of `M_m^4`. -/
def hlozThresholdTimeEvent (m : ℕ) : Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m 4 s < firstKSitesReachLevel (m + 1) 1 s}

/-- The stopping-time event `T_m^4 < T_{m+1}^1` is exactly the direct
four-sites-at-level event. -/
theorem hlozThresholdTimeEvent_eq (m : ℕ) :
    hlozThresholdTimeEvent m = hlozFourSitesReachLevelFirst m := by
  ext s
  constructor
  · intro h
    change firstKSitesReachLevel m 4 s < firstKSitesReachLevel (m + 1) 1 s at h
    have hne : firstKSitesReachLevel m 4 s ≠ ⊤ := ne_top_of_lt h
    let n : ℕ := (firstKSitesReachLevel m 4 s).untopA
    have hncoe : (n : WithTop ℕ) = firstKSitesReachLevel m 4 s := by
      dsimp only [n]
      rw [WithTop.untopA_eq_untop hne]
      exact WithTop.coe_untop _ hne
    have hnmem : (sitesAtLeastLevel s n m).card ∈ Set.Ici 4 := by
      exact hittingAfter_mem_set_of_ne_top
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici 4) (n := 0) (ω := s) hne
    have hnlt : (n : WithTop ℕ) < firstKSitesReachLevel (m + 1) 1 s :=
      hncoe.trans_lt h
    have hnnot : (sitesAtLeastLevel s n (m + 1)).card ∉ Set.Ici 1 := by
      exact notMem_of_lt_hittingAfter
        (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
        (s := Set.Ici 1) (n := 0) (ω := s) hnlt (Nat.zero_le n)
    have hzero : (sitesAtLeastLevel s n (m + 1)).card = 0 := by
      simp only [Set.mem_Ici, not_le] at hnnot
      omega
    refine ⟨n, hnmem, ?_⟩
    exact (card_sitesAtLeastLevel_eq_zero_iff_max_lt s n (m + 1)).mp hzero
  · rintro ⟨n, hfour, hmax⟩
    change firstKSitesReachLevel m 4 s < firstKSitesReachLevel (m + 1) 1 s
    have hT4le : firstKSitesReachLevel m 4 s ≤ n := by
      exact hittingAfter_le_of_mem
        (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
        (s := Set.Ici 4) (n := 0) (ω := s) (Nat.zero_le n) hfour
    have hT1gt : (n : WithTop ℕ) < firstKSitesReachLevel (m + 1) 1 s := by
      by_contra hnot
      have hT1le : firstKSitesReachLevel (m + 1) 1 s ≤ n := by
        simpa only [not_lt] using hnot
      change hittingAfter
        (fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
        (Set.Ici 1) 0 s ≤ (n : WithTop ℕ) at hT1le
      have hex : ∃ j ∈ Set.Icc 0 n,
          (sitesAtLeastLevel s j (m + 1)).card ∈ Set.Ici 1 :=
        (hittingAfter_le_iff
          (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
          (s := Set.Ici 1) (n := 0) (ω := s) (i := n)).mp hT1le
      rcases hex with ⟨j, hj, hjmem⟩
      have hjcard : 1 ≤ (sitesAtLeastLevel s j (m + 1)).card := hjmem
      have hjnonempty : (sitesAtLeastLevel s j (m + 1)).Nonempty :=
        Finset.card_pos.mp (by omega)
      rcases hjnonempty with ⟨x, hx⟩
      have hx' := sitesAtLeastLevel_mono_time
        (s := s) (m := m + 1) hj.2 hx
      have hzero :=
        (card_sitesAtLeastLevel_eq_zero_iff_max_lt s n (m + 1)).mpr hmax
      have : 0 < (sitesAtLeastLevel s n (m + 1)).card :=
        Finset.card_pos.mpr ⟨x, hx'⟩
      omega
    exact hT4le.trans_lt hT1gt

/-- Four favourite sites persist forward as long as the maximal local time
stays on the same plateau. -/
theorem fourFavorites_persist_on_plateau {s : ℕ → Site} {i j : ℕ}
    (hij : i ≤ j) (hmax : maxLocalTime s i = maxLocalTime s j)
    (hfour : 4 ≤ (favoriteSites s i).card) :
    4 ≤ (favoriteSites s j).card := by
  exact hfour.trans (Finset.card_le_card
    (favoriteSites_subset_of_maxLocalTime_eq hij hmax))

/-- The same bad-level event, expressed by aggregating all favourite sets on
the level-`m` plateau up to a witness time that is itself on that plateau. -/
def fourFavoritesAtLevelViaPlateau (m : ℕ) : Set (ℕ → Site) :=
  {s | ∃ n, maxLocalTime s n = m ∧
    4 ≤ (unionAtLevel (favoriteSites s) (maxLocalTime s) 0 n m).card}

/-- Plateau nesting shows that aggregating all earlier favourite sets at one
maximal-local-time level creates no new sites beyond the favourite set at the
latest witness time.  Thus the aggregated and existential level events agree. -/
theorem fourFavoritesAtLevelViaPlateau_eq (m : ℕ) :
    fourFavoritesAtLevelViaPlateau m = fourFavoritesAtLevel m := by
  ext s
  constructor
  · rintro ⟨n, hlevel, hfour⟩
    refine ⟨n, hlevel, hfour.trans ?_⟩
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hk, hxk⟩
    have hkIcc := (Finset.mem_filter.mp hk).1
    have hklevel := (Finset.mem_filter.mp hk).2
    exact favoriteSites_subset_of_maxLocalTime_eq
      (Finset.mem_Icc.mp hkIcc).2 (hklevel.trans hlevel.symm) hxk
  · rintro ⟨n, hlevel, hfour⟩
    refine ⟨n, hlevel, hfour.trans ?_⟩
    apply Finset.card_le_card
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le n, le_rfl⟩,
      hlevel⟩, hx⟩

/-- If the maximum diverges and only finitely many maximal-local-time levels
ever contain four favourites, then eventually there are at most three
favourites. -/
theorem eventuallyAtMostThree_of_tendsto_max_and_eventually_good_levels
    (s : ℕ → Site)
    (hmax : Tendsto (maxLocalTime s) atTop atTop)
    (hlevels : ∀ᶠ m : ℕ in atTop, s ∉ fourFavoritesAtLevel m) :
    EventuallyAtMostThree s := by
  rw [eventually_atTop] at hlevels
  obtain ⟨M, hM⟩ := hlevels
  have hmaxM : ∀ᶠ n : ℕ in atTop, M ≤ maxLocalTime s n :=
    (tendsto_atTop.1 hmax M)
  filter_upwards [hmaxM] with n hn
  by_contra hnot
  have hfour : 4 ≤ (favoriteSites s n).card := by omega
  exact hM (maxLocalTime s n) hn ⟨n, rfl, hfour⟩

/-- Exact summability boundary for the HLOZ upper conclusion, after separating
the elementary divergence-of-the-maximum input. -/
theorem hlozPlanarConclusion_of_level_tsum
    (hmax : ∀ᵐ s ∂simpleRandomWalkLaw,
      Tendsto (maxLocalTime s) atTop atTop)
    (hsum : (∑' m : ℕ,
      simpleRandomWalkLaw (fourFavoritesAtLevel m)) ≠ ∞) :
    HLOZPlanarConclusion := by
  have hsum' : (∑' m : ℕ,
      simpleRandomWalkLaw (fourFavoritesAtLevelViaPlateau m)) ≠ ∞ := by
    simpa only [fourFavoritesAtLevelViaPlateau_eq] using hsum
  have hplateauLevels : ∀ᵐ s ∂simpleRandomWalkLaw,
      ∀ᶠ m : ℕ in atTop, s ∉ fourFavoritesAtLevelViaPlateau m :=
    MeasureTheory.ae_eventually_notMem hsum'
  have hlevels : ∀ᵐ s ∂simpleRandomWalkLaw,
      ∀ᶠ m : ℕ in atTop, s ∉ fourFavoritesAtLevel m := by
    filter_upwards [hplateauLevels] with s hs
    filter_upwards [hs] with m hm
    simpa only [fourFavoritesAtLevelViaPlateau_eq] using hm
  filter_upwards [hmax, hlevels] with s hsmax hslevels
  exact eventuallyAtMostThree_of_tendsto_max_and_eventually_good_levels
    s hsmax hslevels

/-- The polynomial estimate delivered by HLOZ Proposition 4.7 is summable
as soon as its exponent is greater than one.  This theorem records the exact
analytic interface between that screening estimate and the favourite-site
conclusion. -/
theorem hlozPlanarConclusion_of_polynomial_level_bound
    (hmax : ∀ᵐ s ∂simpleRandomWalkLaw,
      Tendsto (maxLocalTime s) atTop atTop)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hbad : ∀ m : ℕ,
      simpleRandomWalkLaw (fourFavoritesAtLevel m) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  have hsummable : Summable (fun m : ℕ ↦ C / ((m : ℝ) + 1) ^ p) := by
    have hbase := (Real.summable_one_div_nat_add_rpow 1 p).2 hp
    have hmul := hbase.mul_left C
    exact hmul.congr (fun m ↦ by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1)]
      ring)
  have hnonneg : ∀ m : ℕ, 0 ≤ C / ((m : ℝ) + 1) ^ p := by
    intro m
    positivity
  have hbound :
      (∑' m : ℕ, ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
    exact ENNReal.ofReal_ne_top
  have hsumle :
      (∑' m : ℕ, simpleRandomWalkLaw (fourFavoritesAtLevel m)) ≤
        ∑' m : ℕ, ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p) :=
    ENNReal.tsum_le_tsum hbad
  exact hlozPlanarConclusion_of_level_tsum hmax
    (ne_top_of_le_ne_top hbound hsumle)

/-- Canonical planar specialization of the HLOZ polynomial screening
estimate.  Recurrence, and hence divergence of the maximal local time, has
already been proved above for `simpleRandomWalkLaw`; the only remaining input
is the summable four-favourite-site estimate itself. -/
theorem hlozPlanarConclusion_of_polynomial_level_bound_canonical
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hbad : ∀ m : ℕ,
      simpleRandomWalkLaw (fourFavoritesAtLevel m) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion :=
  hlozPlanarConclusion_of_polynomial_level_bound
    simpleRandomWalkLaw_maxLocalTime_tendsto hC hp hbad

/-- Source-facing form of the preceding theorem.  Its hypothesis is the
polynomial bound for HLOZ's event `M_m^4`, expressed as four sites reaching
level `m` before any site reaches level `m + 1`. -/
theorem hlozPlanarConclusion_of_hloz_polynomial_bound
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hbad : ∀ m : ℕ,
      simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_polynomial_level_bound_canonical hC hp
  intro m
  simpa only [hlozFourSitesReachLevelFirst_eq_fourFavoritesAtLevel] using hbad m

/-- Exact stopping-time form of the HLOZ interface.  A summable polynomial
bound for `T_m^4 < T_{m+1}^1` implies eventual absence of four favourites. -/
theorem hlozPlanarConclusion_of_threshold_time_polynomial_bound
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hbad : ∀ m : ℕ,
      simpleRandomWalkLaw (hlozThresholdTimeEvent m) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_hloz_polynomial_bound hC hp
  intro m
  simpa only [hlozThresholdTimeEvent_eq] using hbad m

/-- A cover of HLOZ's event `M_m^4` by the six pairing subevents converts a
uniform polynomial estimate for every pairing into the corresponding
polynomial estimate for `M_m^4`. -/
theorem measure_hlozFourSitesReachLevelFirst_le_of_six_pairing_cover
    (pairingEvent : ℕ → Fin 6 → Set (ℕ → Site))
    (hmeas : ∀ m i, MeasurableSet (pairingEvent m i))
    (hcover : ∀ m, hlozFourSitesReachLevelFirst m ⊆
      ⋃ i : Fin 6, pairingEvent m i)
    {C p : ℝ}
    (hpair : ∀ m i,
      simpleRandomWalkLaw (pairingEvent m i) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p))
    (m : ℕ) :
    simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m) ≤
      ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p) := by
  have _hunionMeas : MeasurableSet (⋃ i : Fin 6, pairingEvent m i) :=
    MeasurableSet.iUnion (hmeas m)
  calc
    simpleRandomWalkLaw (hlozFourSitesReachLevelFirst m) ≤
        simpleRandomWalkLaw (⋃ i : Fin 6, pairingEvent m i) :=
      measure_mono (hcover m)
    _ ≤ ∑ i : Fin 6, simpleRandomWalkLaw (pairingEvent m i) :=
      measure_iUnion_fintype_le simpleRandomWalkLaw (pairingEvent m)
    _ ≤ ∑ _i : Fin 6,
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p) := by
      exact Finset.sum_le_sum fun i _ ↦ hpair m i
    _ = 6 * ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p) := by simp
    _ = ENNReal.ofReal ((6 * C) / ((m : ℝ) + 1) ^ p) := by
      rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      congr 1
      ring

/-- The abstract finishing chain for HLOZ's six pairing cover.  Once the six
source pairing estimates are established, their finite union and the first
Borel--Cantelli lemma give eventual absence of four favorite sites. -/
theorem hlozPlanarConclusion_of_six_pairing_cover
    (pairingEvent : ℕ → Fin 6 → Set (ℕ → Site))
    (hmeas : ∀ m i, MeasurableSet (pairingEvent m i))
    (hcover : ∀ m, hlozFourSitesReachLevelFirst m ⊆
      ⋃ i : Fin 6, pairingEvent m i)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hpair : ∀ m i,
      simpleRandomWalkLaw (pairingEvent m i) ≤
        ENNReal.ofReal (C / ((m : ℝ) + 1) ^ p)) :
    HLOZPlanarConclusion := by
  apply hlozPlanarConclusion_of_hloz_polynomial_bound
    (C := 6 * C) (p := p) (by positivity) hp
  intro m
  exact measure_hlozFourSitesReachLevelFirst_le_of_six_pairing_cover
    pairingEvent hmeas hcover hpair m

/-- An eventual geometric estimate at maximal-local-time levels is enough.
This is the direct first-Borel--Cantelli reduction with the same convenient
`2 * 4⁻ᵐ` majorant already used in `Erdos1166`. -/
theorem hlozPlanarConclusion_of_eventually_geometric_level_bound
    (hmax : ∀ᵐ s ∂simpleRandomWalkLaw,
      Tendsto (maxLocalTime s) atTop atTop)
    (hbad : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw (fourFavoritesAtLevel m) ≤
        2 * ((4 : ℝ≥0∞)⁻¹) ^ m) :
    HLOZPlanarConclusion := by
  have hbad' : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw (fourFavoritesAtLevelViaPlateau m) ≤
        2 * ((4 : ℝ≥0∞)⁻¹) ^ m := by
    simpa only [fourFavoritesAtLevelViaPlateau_eq] using hbad
  have hlevels := ae_eventually_notMem_of_eventually_measure_le_four_inv_pow
    simpleRandomWalkLaw fourFavoritesAtLevelViaPlateau hbad'
  filter_upwards [hmax, hlevels] with s hsmax hsplateau
  have hslevels : ∀ᶠ m : ℕ in atTop, s ∉ fourFavoritesAtLevel m := by
    filter_upwards [hsplateau] with m hm
    simpa only [fourFavoritesAtLevelViaPlateau_eq] using hm
  exact eventuallyAtMostThree_of_tendsto_max_and_eventually_good_levels
    s hsmax hslevels

/-- Canonical planar specialization of the eventual geometric screening
estimate. -/
theorem hlozPlanarConclusion_of_eventually_geometric_level_bound_canonical
    (hbad : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw (fourFavoritesAtLevel m) ≤
        2 * ((4 : ℝ≥0∞)⁻¹) ^ m) :
    HLOZPlanarConclusion :=
  hlozPlanarConclusion_of_eventually_geometric_level_bound
    simpleRandomWalkLaw_maxLocalTime_tendsto hbad


/-- The precise consequence of the planar Erdős--Taylor estimate used here. -/
def ErdosTaylorPlanarConclusion : Prop :=
  ∀ᵐ s ∂simpleRandomWalkLaw, HasMaxLocalTimeLogSqBound s

/-- The Erdős--Taylor input is reduced to the explicit dyadic tail estimate
delivered by the local-time moment calculation. -/
theorem erdosTaylorPlanarConclusion_of_dyadic_tail
    {A : ℝ} (hA : 0 < A)
    (hbad : ∀ k : ℕ,
      simpleRandomWalkLaw
          {s | A * (k : ℝ) ^ 2 < (maxLocalTime s (2 ^ k) : ℝ)} ≤
        2 * ((4 : ℝ≥0∞)⁻¹) ^ k) :
    ErdosTaylorPlanarConclusion := by
  have hae := ae_eventually_notMem_of_measure_le_four_inv_pow simpleRandomWalkLaw
    (fun k ↦ {s | A * (k : ℝ) ^ 2 < (maxLocalTime s (2 ^ k) : ℝ)}) hbad
  filter_upwards [hae] with s hs
  apply hasMaxLocalTimeLogSqBound_of_dyadic s A hA
  filter_upwards [hs] with k hk
  exact le_of_not_gt hk

/-- Eventual dyadic tail estimates are sufficient; a finite prefix of scales
does not affect the almost-sure Erdős--Taylor conclusion. -/
theorem erdosTaylorPlanarConclusion_of_eventually_dyadic_tail
    {A : ℝ} (hA : 0 < A)
    (hbad : ∀ᶠ k : ℕ in atTop,
      simpleRandomWalkLaw
          {s | A * (k : ℝ) ^ 2 < (maxLocalTime s (2 ^ k) : ℝ)} ≤
        2 * ((4 : ℝ≥0∞)⁻¹) ^ k) :
    ErdosTaylorPlanarConclusion := by
  have hae := ae_eventually_notMem_of_eventually_measure_le_four_inv_pow
    simpleRandomWalkLaw
    (fun k ↦ {s | A * (k : ℝ) ^ 2 < (maxLocalTime s (2 ^ k) : ℝ)}) hbad
  filter_upwards [hae] with s hs
  apply hasMaxLocalTimeLogSqBound_of_dyadic s A hA
  filter_upwards [hs] with k hk
  exact le_of_not_gt hk

/-- The Kac-moment estimate, transferred from the iid increment space to the
canonical path law. -/
theorem simpleRandomWalkLaw_dyadic_maxLocalTime_tail (k : ℕ) (hk : 1 ≤ k) :
    simpleRandomWalkLaw
        {s | (48 : ℝ) * (k : ℝ) ^ 2 < (maxLocalTime s (2 ^ k) : ℝ)} ≤
      2 * ((4 : ℝ≥0∞)⁻¹) ^ k := by
  have hmeas : MeasurableSet
      {s : ℕ → Site |
        (48 : ℝ) * (k : ℝ) ^ 2 < (maxLocalTime s ((2 : ℕ) ^ k) : ℝ)} := by
    exact measurableSet_lt measurable_const
      (MeasurableEmbedding.natCast.measurable.comp
        (measurable_maxLocalTime_eval ((2 : ℕ) ^ k)))
  rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk hmeas]
  calc
    incrementLaw
        (simpleRandomWalk ⁻¹'
          {s | (48 : ℝ) * (k : ℝ) ^ 2 <
            (maxLocalTime s ((2 : ℕ) ^ k) : ℝ)}) ≤
        incrementLaw
          {ω | 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)} := by
      apply measure_mono
      intro ω hω
      change (48 : ℝ) * (k : ℝ) ^ 2 <
        (maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k) : ℝ) at hω
      change 48 * k ^ 2 ≤ maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k)
      have hlt : 48 * k ^ 2 < maxLocalTime (simpleRandomWalk ω) ((2 : ℕ) ^ k) := by
        exact_mod_cast hω
      exact hlt.le
    _ ≤ 2 * ((4 : ENNReal)⁻¹) ^ k :=
      canonical_dyadic_maxLocalTime_tail_ennreal k hk

/-- The planar Erdős--Taylor maximal-local-time upper bound is proved here
from exact planar return probabilities, Kac moments, and Borel--Cantelli. -/
theorem erdosTaylorPlanar : ErdosTaylorPlanarConclusion := by
  apply erdosTaylorPlanarConclusion_of_eventually_dyadic_tail (A := 48) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact simpleRandomWalkLaw_dyadic_maxLocalTime_tail k hk

/-- Erdős Problem 1166 for the canonical planar simple symmetric random-walk
law, conditional only on the HLOZ eventual-three-favourites conclusion; the
Erdős--Taylor input has been proved above. -/
theorem erdos_1166_of_hloz (hHLOZ : HLOZPlanarConclusion)
    : ∀ᵐ s ∂simpleRandomWalkLaw, HasCumulativeFavoriteLogSqBound s :=
  erdos_1166_of_ae_inputs simpleRandomWalkLaw id hHLOZ erdosTaylorPlanar

end Erdos1166
