/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.StageAssembly

/-!
# The concrete smooth/rough moment estimate for Erdős Problem 586

This file performs the arithmetic reindexing which is deliberately absent
from `Moments`.  At a prime stage `r`, the old part of every newly exposed
modulus is split into its `2,3,5`-smooth part and the complementary rough
part.  The smooth fibres are divisibility antichains, so `Smooth` bounds
their LCM energy by `17 / 10`.  The rough keys are then enlarged to the
finite box of possible prime exponents; the local sums are the finite Euler
factors proved in `Moments`.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

local instance momentPartialPeriodNeZero (Q r : ℕ) :
    NeZero (partialPeriod Q r) := ⟨(partialPeriod_pos Q r).ne'⟩

private lemma momentStagePrime_pos_all (r : ℕ) : 0 < stagePrime r := by
  cases r with
  | zero => norm_num [stagePrime]
  | succ r => exact stagePrime_pos (Nat.succ_pos r)

local instance momentStagePowerNeZero (Q r : ℕ) :
    NeZero (stagePrime r ^ stageExponent Q r) :=
  ⟨(pow_pos (momentStagePrime_pos_all r) _).ne'⟩

/-! ## Removing the first three prime coordinates -/

/-- The exponent triple of the `2,3,5`-smooth part of a positive natural. -/
def fiveSmoothExponents (m : ℕ) : Exp3 :=
  (m.factorization 2, m.factorization 3, m.factorization 5)

/-- Remove the complete powers of `2`, `3`, and `5`, in that order. -/
def fiveRoughPart (m : ℕ) : ℕ :=
  ordCompl[5] (ordCompl[3] (ordCompl[2] m))

@[simp] lemma decode5_fiveSmoothExponents (m : ℕ) :
    decode5 (fiveSmoothExponents m) =
      2 ^ m.factorization 2 * 3 ^ m.factorization 3 *
        5 ^ m.factorization 5 := rfl

lemma fiveRoughPart_pos {m : ℕ} (hm : m ≠ 0) : 0 < fiveRoughPart m := by
  exact Nat.ordCompl_pos 5
    (Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 hm).ne').ne'

lemma factorization_ordCompl_two_at_three (m : ℕ) :
    (ordCompl[2] m).factorization 3 = m.factorization 3 := by
  rw [Nat.factorization_ordCompl]
  simp

lemma factorization_ordCompl_two_three_at_five (m : ℕ) :
    (ordCompl[3] (ordCompl[2] m)).factorization 5 =
      m.factorization 5 := by
  rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl]
  simp

/-- Exact smooth/rough factorization. -/
theorem decode5_mul_fiveRoughPart (m : ℕ) :
    decode5 (fiveSmoothExponents m) * fiveRoughPart m = m := by
  change (2 ^ m.factorization 2 * 3 ^ m.factorization 3 *
      5 ^ m.factorization 5) * fiveRoughPart m = m
  rw [← factorization_ordCompl_two_at_three m,
    ← factorization_ordCompl_two_three_at_five m]
  change (ordProj[2] m * ordProj[3] (ordCompl[2] m) *
      ordProj[5] (ordCompl[3] (ordCompl[2] m))) *
        ordCompl[5] (ordCompl[3] (ordCompl[2] m)) = m
  calc
    _ = ordProj[2] m *
        (ordProj[3] (ordCompl[2] m) *
          (ordProj[5] (ordCompl[3] (ordCompl[2] m)) *
            ordCompl[5] (ordCompl[3] (ordCompl[2] m)))) := by ac_rfl
    _ = ordProj[2] m *
        (ordProj[3] (ordCompl[2] m) * ordCompl[3] (ordCompl[2] m)) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = ordProj[2] m * ordCompl[2] m := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = m := Nat.ordProj_mul_ordCompl_eq_self m 2

lemma fiveRoughPart_factorization (m : ℕ) :
    (fiveRoughPart m).factorization =
      ((m.factorization.erase 2).erase 3).erase 5 := by
  unfold fiveRoughPart
  rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl,
    Nat.factorization_ordCompl]

@[simp] lemma fiveRoughPart_factorization_two (m : ℕ) :
    (fiveRoughPart m).factorization 2 = 0 := by
  rw [show (fiveRoughPart m).factorization =
      ((m.factorization.erase 2).erase 3).erase 5 by
    exact fiveRoughPart_factorization m]
  simp

@[simp] lemma fiveRoughPart_factorization_three (m : ℕ) :
    (fiveRoughPart m).factorization 3 = 0 := by
  rw [show (fiveRoughPart m).factorization =
      ((m.factorization.erase 2).erase 3).erase 5 by
    exact fiveRoughPart_factorization m]
  simp

@[simp] lemma fiveRoughPart_factorization_five (m : ℕ) :
    (fiveRoughPart m).factorization 5 = 0 := by
  rw [show (fiveRoughPart m).factorization =
      ((m.factorization.erase 2).erase 3).erase 5 by
    exact fiveRoughPart_factorization m]
  simp

lemma fiveRoughPart_factorization_of_ne {m q : ℕ}
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq5 : q ≠ 5) :
    (fiveRoughPart m).factorization q = m.factorization q := by
  rw [show (fiveRoughPart m).factorization =
      ((m.factorization.erase 2).erase 3).erase 5 by
    exact fiveRoughPart_factorization m]
  simp [hq2, hq3, hq5]

lemma decode5_pos (x : Exp3) : 0 < decode5 x := by
  unfold decode5
  positivity

lemma factorization_decode5_two (x : Exp3) :
    (decode5 x).factorization 2 = x.1 := by
  norm_num [decode5, Nat.factorization_mul, Nat.Prime.factorization_pow]

lemma factorization_decode5_three (x : Exp3) :
    (decode5 x).factorization 3 = x.2.1 := by
  norm_num [decode5, Nat.factorization_mul, Nat.Prime.factorization_pow]

lemma factorization_decode5_five (x : Exp3) :
    (decode5 x).factorization 5 = x.2.2 := by
  norm_num [decode5, Nat.factorization_mul, Nat.Prime.factorization_pow]

lemma factorization_decode5_of_ne (x : Exp3) {q : ℕ}
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hq5 : q ≠ 5) :
    (decode5 x).factorization q = 0 := by
  norm_num [decode5, Nat.factorization_mul, Nat.Prime.factorization_pow,
    hq2, hq3, hq5]

/-- LCM is coordinatewise maximum on `2,3,5` exponent triples. -/
lemma lcm_decode5 (x y : Exp3) :
    Nat.lcm (decode5 x) (decode5 y) =
      decode5 (max x.1 y.1, max x.2.1 y.2.1, max x.2.2 y.2.2) := by
  apply Nat.eq_of_factorization_eq
    (Nat.lcm_ne_zero (decode5_pos x).ne' (decode5_pos y).ne')
    (decode5_pos _).ne'
  intro q
  rw [Nat.factorization_lcm (decode5_pos x).ne' (decode5_pos y).ne']
  by_cases hq2 : q = 2
  · subst q
    simp [factorization_decode5_two]
  by_cases hq3 : q = 3
  · subst q
    simp [factorization_decode5_three]
  by_cases hq5 : q = 5
  · subst q
    simp [factorization_decode5_five]
  simp [factorization_decode5_of_ne, hq2, hq3, hq5]

/-- The real LCM kernel is precisely reciprocal smooth LCM. -/
lemma tripleKernel_fiveSmoothExponents (m n : ℕ) :
    tripleKernel (fiveSmoothExponents m) (fiveSmoothExponents n) =
      1 / (Nat.lcm (decode5 (fiveSmoothExponents m))
        (decode5 (fiveSmoothExponents n)) : ℕ) := by
  rw [lcm_decode5]
  unfold tripleKernel decode5 fiveSmoothExponents
  push_cast
  simp only [one_div, mul_inv_rev, inv_pow]
  ring

/-- LCM separates into its smooth and rough coordinates. -/
lemma lcm_eq_smooth_lcm_mul_rough_lcm {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.lcm m n =
      Nat.lcm (decode5 (fiveSmoothExponents m))
          (decode5 (fiveSmoothExponents n)) *
        Nat.lcm (fiveRoughPart m) (fiveRoughPart n) := by
  let sm := decode5 (fiveSmoothExponents m)
  let sn := decode5 (fiveSmoothExponents n)
  let rm := fiveRoughPart m
  let rn := fiveRoughPart n
  have hsm : sm ≠ 0 := (decode5_pos _).ne'
  have hsn : sn ≠ 0 := (decode5_pos _).ne'
  have hrm : rm ≠ 0 := (fiveRoughPart_pos hm).ne'
  have hrn : rn ≠ 0 := (fiveRoughPart_pos hn).ne'
  apply Nat.eq_of_factorization_eq
    (Nat.lcm_ne_zero hm hn)
    (mul_ne_zero (Nat.lcm_ne_zero hsm hsn) (Nat.lcm_ne_zero hrm hrn))
  intro q
  rw [Nat.factorization_lcm hm hn,
    Nat.factorization_mul (Nat.lcm_ne_zero hsm hsn)
      (Nat.lcm_ne_zero hrm hrn),
    Nat.factorization_lcm hsm hsn, Nat.factorization_lcm hrm hrn]
  change max (m.factorization q) (n.factorization q) =
    max ((decode5 (fiveSmoothExponents m)).factorization q)
        ((decode5 (fiveSmoothExponents n)).factorization q) +
      max ((fiveRoughPart m).factorization q)
        ((fiveRoughPart n).factorization q)
  by_cases hq2 : q = 2
  · subst q
    rw [factorization_decode5_two, factorization_decode5_two,
      fiveRoughPart_factorization_two, fiveRoughPart_factorization_two]
    simp [fiveSmoothExponents]
  by_cases hq3 : q = 3
  · subst q
    rw [factorization_decode5_three, factorization_decode5_three,
      fiveRoughPart_factorization_three, fiveRoughPart_factorization_three]
    simp [fiveSmoothExponents]
  by_cases hq5 : q = 5
  · subst q
    rw [factorization_decode5_five, factorization_decode5_five,
      fiveRoughPart_factorization_five, fiveRoughPart_factorization_five]
    simp [fiveSmoothExponents]
  rw [factorization_decode5_of_ne _ hq2 hq3 hq5,
    factorization_decode5_of_ne _ hq2 hq3 hq5,
    fiveRoughPart_factorization_of_ne hq2 hq3 hq5,
    fiveRoughPart_factorization_of_ne hq2 hq3 hq5]
  simp

lemma reciprocal_lcm_eq_rough_mul_tripleKernel {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    (1 / (Nat.lcm m n : ℕ) : ℝ) =
      (1 / (Nat.lcm (fiveRoughPart m) (fiveRoughPart n) : ℕ) : ℝ) *
        tripleKernel (fiveSmoothExponents m) (fiveSmoothExponents n) := by
  rw [tripleKernel_fiveSmoothExponents, lcm_eq_smooth_lcm_mul_rough_lcm hm hn]
  push_cast
  field_simp [Nat.lcm_ne_zero
    (decode5_pos (fiveSmoothExponents m)).ne'
    (decode5_pos (fiveSmoothExponents n)).ne',
    Nat.lcm_ne_zero (fiveRoughPart_pos hm).ne' (fiveRoughPart_pos hn).ne']

/-! ## The processed-prime multiplier on rough parts -/

lemma processedClassFactor_eq_prod_Ico (p : ℕ → ℕ) (δ : ℕ → ℝ)
    (m r : ℕ) :
    processedClassFactor p δ m r =
      ∏ t ∈ Finset.Ico 1 (r + 1),
        if p t ∣ m then 1 / (1 - δ t) else 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      let f : ℕ → ℝ := fun t =>
        if p t ∣ m then 1 / (1 - δ t) else 1
      calc
        processedClassFactor p δ m (r + 1) =
            processedClassFactor p δ m r * f (r + 1) := by rfl
        _ = (∏ t ∈ Finset.Ico 1 (r + 1), f t) * f (r + 1) := by rw [ih]
        _ = ∏ t ∈ Finset.Ico 1 (r + 1 + 1), f t :=
          (Finset.prod_Ico_succ_top (by omega : 1 ≤ r + 1) f).symm

lemma processedClassFactor_stagePrime_eq_prod_rough
    (δ : ℕ → ℝ) (m r : ℕ) (hr : 4 ≤ r)
    (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0) :
    processedClassFactor stagePrime δ m (r - 1) =
      ∏ t ∈ Finset.Ico 4 r,
        if stagePrime t ∣ m then 1 / (1 - δ t) else 1 := by
  rw [processedClassFactor_eq_prod_Ico]
  have hpred : r - 1 + 1 = r := by omega
  rw [hpred, ← Finset.prod_Ico_consecutive
    (f := fun t => if stagePrime t ∣ m then 1 / (1 - δ t) else 1)
    (by omega : 1 ≤ 4) hr]
  have hfirst :
      (∏ t ∈ Finset.Ico 1 4,
        if stagePrime t ∣ m then 1 / (1 - δ t) else 1) = 1 := by
    norm_num [Finset.prod_Ico_succ_top, hδ1, hδ2, hδ3]
  rw [hfirst, one_mul]

lemma seven_le_stagePrime {t : ℕ} (ht : 4 ≤ t) : 7 ≤ stagePrime t := by
  have hlt : stagePrime 3 < stagePrime t := by
    exact stagePrime_strictMonoOn
      (show 3 ∈ Set.Ici 1 by simp only [Set.mem_Ici]; omega)
      (show t ∈ Set.Ici 1 by simp only [Set.mem_Ici]; omega) (by omega)
  have hp := stagePrime_prime (by omega : 0 < t)
  norm_num at hlt
  by_contra h
  have heq : stagePrime t = 6 := by omega
  rw [heq] at hp
  norm_num at hp

lemma stagePrime_dvd_iff_dvd_fiveRoughPart {m t : ℕ}
    (hm : m ≠ 0) (ht : 4 ≤ t) :
    stagePrime t ∣ m ↔ stagePrime t ∣ fiveRoughPart m := by
  have hp := stagePrime_prime (by omega : 0 < t)
  have hp7 := seven_le_stagePrime ht
  have hp2 : stagePrime t ≠ 2 := by omega
  have hp3 : stagePrime t ≠ 3 := by omega
  have hp5 : stagePrime t ≠ 5 := by omega
  have hs0 : decode5 (fiveSmoothExponents m) ≠ 0 := (decode5_pos _).ne'
  have hnsm : ¬ stagePrime t ∣ decode5 (fiveSmoothExponents m) := by
    rw [hp.dvd_iff_one_le_factorization hs0]
    rw [factorization_decode5_of_ne _ hp2 hp3 hp5]
    simp
  conv_lhs => rw [← decode5_mul_fiveRoughPart m]
  constructor
  · intro h
    rcases hp.dvd_mul.mp h with hs | hr
    · exact False.elim (hnsm hs)
    · exact hr
  · intro hr
    exact hp.dvd_mul.mpr (Or.inr hr)

lemma stagePrime_dvd_lcm_iff_dvd_rough_lcm {m n t : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (ht : 4 ≤ t) :
    stagePrime t ∣ Nat.lcm m n ↔
      stagePrime t ∣ Nat.lcm (fiveRoughPart m) (fiveRoughPart n) := by
  have hp := stagePrime_prime (by omega : 0 < t)
  rw [hp.dvd_lcm, hp.dvd_lcm,
    stagePrime_dvd_iff_dvd_fiveRoughPart hm ht,
    stagePrime_dvd_iff_dvd_fiveRoughPart hn ht]

lemma processedClassFactor_lcm_eq_rough_lcm
    (δ : ℕ → ℝ) {m n r : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hr : 4 ≤ r) (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0) :
    processedClassFactor stagePrime δ (Nat.lcm m n) (r - 1) =
      processedClassFactor stagePrime δ
        (Nat.lcm (fiveRoughPart m) (fiveRoughPart n)) (r - 1) := by
  rw [processedClassFactor_stagePrime_eq_prod_rough δ _ r hr hδ1 hδ2 hδ3,
    processedClassFactor_stagePrime_eq_prod_rough δ _ r hr hδ1 hδ2 hδ3]
  apply Finset.prod_congr rfl
  intro t ht
  simp only [stagePrime_dvd_lcm_iff_dvd_rough_lcm hm hn
    (Finset.mem_Ico.mp ht).1]

/-! ## Concrete keys and smooth fibres -/

/-- The rough integer together with the positive exponent of the new prime. -/
abbrev MomentRoughKey := ℕ × ℕ

def momentStageSmoothValue {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) : Exp3 :=
  fiveSmoothExponents (momentStageOldPart i)

def momentStageRoughKey {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) : MomentRoughKey :=
  (fiveRoughPart (momentStageOldPart i), momentStageExponent i)

lemma momentStageOldPart_eq_smooth_mul_rough {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ}
    (i : MomentStageIndex A s Q r) :
    momentStageOldPart i =
      decode5 (momentStageSmoothValue i) * (momentStageRoughKey i).1 := by
  exact (decode5_mul_fiveRoughPart (momentStageOldPart i)).symm

/-- The rough key and smooth exponent triple determine the occurrence,
because equality of reconstructed moduli contradicts antichainness unless
the two occurrence indices agree. -/
lemma momentStage_key_value_injective
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    Function.Injective (fun i : MomentStageIndex A s Q r =>
      (momentStageRoughKey i, momentStageSmoothValue i)) := by
  intro i j hij
  have hrough : fiveRoughPart (momentStageOldPart i) =
      fiveRoughPart (momentStageOldPart j) := congrArg (fun x => x.1.1) hij
  have hexp : momentStageExponent i = momentStageExponent j :=
    congrArg (fun x => x.1.2) hij
  have hsmooth : momentStageSmoothValue i = momentStageSmoothValue j :=
    congrArg Prod.snd hij
  have hold : momentStageOldPart i = momentStageOldPart j := by
    rw [momentStageOldPart_eq_smooth_mul_rough i,
      momentStageOldPart_eq_smooth_mul_rough j]
    change decode5 (momentStageSmoothValue i) *
        fiveRoughPart (momentStageOldPart i) =
      decode5 (momentStageSmoothValue j) *
        fiveRoughPart (momentStageOldPart j)
    rw [hsmooth, hrough]
  have hmod : (A.get i.1).modulus = (A.get j.1).modulus := by
    rw [momentStageModulus_eq hQ i, momentStageModulus_eq hQ j,
      hold, hexp]
  apply Subtype.ext
  by_contra hne
  exact (hanti i.1 i.2.1 j.1 j.2.1 hne) (hmod ▸ dvd_rfl)

lemma momentStage_key_value_injOn
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    Set.InjOn (fun i : MomentStageIndex A s Q r =>
      (momentStageRoughKey i, momentStageSmoothValue i)) Set.univ :=
  Set.injOn_of_injective (momentStage_key_value_injective A s hQ hanti)

/-- Above a fixed rough key, the occurring `2,3,5` exponent triples form an
antichain.  This is the exact hypothesis consumed by Lemma 9.4. -/
lemma momentStage_smoothFiber_antichain
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (k : MomentRoughKey) :
    TripleAntichain
      (keyedFiber
        (Finset.univ : Finset (MomentStageIndex A s Q r))
        momentStageRoughKey momentStageSmoothValue k) := by
  classical
  intro x hx y hy hxy hle
  rw [keyedFiber] at hx hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hy
  have hki : momentStageRoughKey i = k := (Finset.mem_filter.mp hi).2
  have hkj : momentStageRoughKey j = k := (Finset.mem_filter.mp hj).2
  have hsdiv : decode5 (momentStageSmoothValue i) ∣
      decode5 (momentStageSmoothValue j) := by
    apply tripleLe_decode5_dvd
    simpa [hix, hjy] using hle
  have hrough : (momentStageRoughKey i).1 =
      (momentStageRoughKey j).1 := by rw [hki, hkj]
  have hexp : momentStageExponent i = momentStageExponent j := by
    change (momentStageRoughKey i).2 = (momentStageRoughKey j).2
    rw [hki, hkj]
  have holdDiv : momentStageOldPart i ∣ momentStageOldPart j := by
    rw [momentStageOldPart_eq_smooth_mul_rough i,
      momentStageOldPart_eq_smooth_mul_rough j]
    exact Nat.mul_dvd_mul hsdiv (hrough ▸ dvd_rfl)
  have hmodDiv : (A.get i.1).modulus ∣ (A.get j.1).modulus := by
    rw [momentStageModulus_eq hQ i, momentStageModulus_eq hQ j, hexp]
    exact mul_dvd_mul_right holdDiv _
  have hij : i = j := by
    by_contra hij
    exact (momentStage_moduli_antichain hanti i j hij) hmodDiv
  apply hxy
  rw [← hix, ← hjy, hij]

/-! ## Reindexing the concrete LCM sum -/

/-- The part of the pair summand left after the smooth LCM kernel is
removed. -/
def momentStageRoughWeight (δ : ℕ → ℝ) (r : ℕ)
    (k l : MomentRoughKey) : ℝ :=
  (1 / (stagePrime r : ℝ) ^ k.2) *
    (1 / (stagePrime r : ℝ) ^ l.2) *
      ((1 / (Nat.lcm k.1 l.1 : ℕ) : ℝ) *
        processedClassFactor stagePrime δ (Nat.lcm k.1 l.1) (r - 1))

lemma momentStageOldPart_ne_zero {A : CoveringFamily}
    {s : Finset (Fin A.length)} {Q r : ℕ} (hQ : Q ≠ 0)
    (i : MomentStageIndex A s Q r) : momentStageOldPart i ≠ 0 := by
  intro hz
  have hmod := momentStageModulus_eq hQ i
  rw [hz, zero_mul] at hmod
  have hlt := (A.get i.1).one_lt_modulus
  omega

lemma momentStage_lcmSummand_eq_rough_mul_kernel
    {A : CoveringFamily} {s : Finset (Fin A.length)} {Q r : ℕ}
    (hQ : Q ≠ 0) (hr : 4 ≤ r) (δ : ℕ → ℝ)
    (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0)
    (i j : MomentStageIndex A s Q r) :
    (momentStageCoefficient i * momentStageCoefficient j) *
        ((1 / (Nat.lcm (momentStageOldPart i)
          (momentStageOldPart j) : ℕ)) *
          processedClassFactor stagePrime δ
            (Nat.lcm (momentStageOldPart i) (momentStageOldPart j)) (r - 1)) =
      momentStageRoughWeight δ r (momentStageRoughKey i)
          (momentStageRoughKey j) *
        tripleKernel (momentStageSmoothValue i) (momentStageSmoothValue j) := by
  have hi0 := momentStageOldPart_ne_zero hQ i
  have hj0 := momentStageOldPart_ne_zero hQ j
  rw [processedClassFactor_lcm_eq_rough_lcm δ hi0 hj0 hr hδ1 hδ2 hδ3,
    reciprocal_lcm_eq_rough_mul_tripleKernel hi0 hj0]
  unfold momentStageCoefficient momentStageRoughWeight momentStageRoughKey
    momentStageSmoothValue
  ring

lemma momentStage_lcmSum_le_smoothRough
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (δ : ℕ → ℝ) (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0) :
    (∑ i : MomentStageIndex A s Q r,
      ∑ j : MomentStageIndex A s Q r,
        (momentStageCoefficient i * momentStageCoefficient j) *
          ((1 / (Nat.lcm (momentStageOldPart i)
            (momentStageOldPart j) : ℕ)) *
            processedClassFactor stagePrime δ
              (Nat.lcm (momentStageOldPart i)
                (momentStageOldPart j)) (r - 1))) ≤
      smoothRoughSecondMoment
        ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
          momentStageRoughKey)
        (momentStageRoughWeight δ r)
        (keyedFiber
          (Finset.univ : Finset (MomentStageIndex A s Q r))
          momentStageRoughKey momentStageSmoothValue) := by
  apply pair_sum_le_smoothRough_of_reindex
    (I := (Finset.univ : Finset (MomentStageIndex A s Q r)))
    (key := momentStageRoughKey) (value := momentStageSmoothValue)
    (hvalue := by
      intro i hi j hj hij
      exact momentStage_key_value_injective A s hQ hanti hij)
  intro i hi j hj
  exact le_of_eq
    (momentStage_lcmSummand_eq_rough_mul_kernel hQ hr δ hδ1 hδ2 hδ3 i j)

/-! ## Injecting rough keys into the finite exponent box -/

lemma fiveRoughPart_dvd (m : ℕ) : fiveRoughPart m ∣ m := by
  exact (Nat.ordCompl_dvd _ 5).trans
    ((Nat.ordCompl_dvd _ 3).trans (Nat.ordCompl_dvd _ 2))

lemma prime_dvd_partialPeriod_exists_stage
    {Q r q : ℕ} (hr : 4 ≤ r) (hq : q.Prime)
    (hq7 : 7 ≤ q) (hdiv : q ∣ partialPeriod Q (r - 1)) :
    ∃ t ∈ Finset.Ico 4 r, stagePrime t = q := by
  have hprev : 0 < r - 1 := by omega
  unfold partialPeriod at hdiv
  obtain ⟨u, hu, hqu⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdiv
  have huQ : u ∈ Q.primeFactors := activePrimeFactors_subset Q (r - 1) hu
  have hup : u.Prime := Nat.prime_of_mem_primeFactors huQ
  have heq : q = u := Nat.prime_eq_prime_of_dvd_pow hq hup hqu
  have hule : u ≤ stagePrime (r - 1) :=
    (mem_activePrimeFactors_iff hprev).mp hu |>.2
  let t := primeStage q
  have htpos : 0 < t := primeStage_pos q
  have htp : stagePrime t = q := stagePrime_primeStage hq
  have ht4 : 4 ≤ t := by
    by_contra h
    have ht3 : t ≤ 3 := by omega
    have hmono : stagePrime t ≤ stagePrime 3 :=
      stagePrime_mono htpos ht3
    norm_num [htp] at hmono
    omega
  have htr : t < r := by
    by_contra h
    have hrt : r ≤ t := by omega
    have hrpos : 0 < r := by omega
    have hmono : stagePrime r ≤ stagePrime t :=
      stagePrime_mono hrpos hrt
    have hstep : stagePrime (r - 1) < stagePrime r :=
      stagePrime_strictMonoOn
        (by simp only [Set.mem_Ici]; omega)
        (by simp only [Set.mem_Ici]; omega) (by omega)
    rw [htp, heq] at hmono
    omega
  exact ⟨t, Finset.mem_Ico.mpr ⟨ht4, htr⟩, htp⟩

lemma fiveRoughPart_eq_of_stage_factorizations
    {Q r m n : ℕ} (hr : 4 ≤ r) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmQ : fiveRoughPart m ∣ partialPeriod Q (r - 1))
    (hnQ : fiveRoughPart n ∣ partialPeriod Q (r - 1))
    (hfac : ∀ t ∈ Finset.Ico 4 r,
      (fiveRoughPart m).factorization (stagePrime t) =
        (fiveRoughPart n).factorization (stagePrime t)) :
    fiveRoughPart m = fiveRoughPart n := by
  have hrm0 := (fiveRoughPart_pos hm).ne'
  have hrn0 := (fiveRoughPart_pos hn).ne'
  apply Nat.eq_of_factorization_eq hrm0 hrn0
  intro q
  by_cases hq : q.Prime
  · by_cases hq2 : q = 2
    · subst q; simp
    by_cases hq3 : q = 3
    · subst q; simp
    by_cases hq5 : q = 5
    · subst q; simp
    have hq7 : 7 ≤ q := by
      have hq0 := hq.ne_zero
      have hq1 := hq.ne_one
      have hq4 : q ≠ 4 := by
        intro h
        subst q
        norm_num at hq
      have hq6 : q ≠ 6 := by
        intro h
        subst q
        norm_num at hq
      omega
    by_cases hd : q ∣ fiveRoughPart m ∨ q ∣ fiveRoughPart n
    · have hdQ : q ∣ partialPeriod Q (r - 1) := by
        rcases hd with hd | hd
        · exact hd.trans hmQ
        · exact hd.trans hnQ
      obtain ⟨t, ht, htp⟩ := prime_dvd_partialPeriod_exists_stage hr hq hq7 hdQ
      rw [← htp]
      exact hfac t ht
    · push_neg at hd
      have hmzero : (fiveRoughPart m).factorization q = 0 := by
        have := (hq.dvd_iff_one_le_factorization hrm0).not.mp hd.1
        omega
      have hnzero : (fiveRoughPart n).factorization q = 0 := by
        have := (hq.dvd_iff_one_le_factorization hrn0).not.mp hd.2
        omega
      rw [hmzero, hnzero]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

abbrev MomentRoughExponentCoordinates (r : ℕ) :=
  (t : ℕ) → t ∈ Finset.Ico 4 r → ℕ × ℕ

def momentRoughPairEncoding (r : ℕ)
    (z : MomentRoughKey × MomentRoughKey) :
    (ℕ × ℕ) × MomentRoughExponentCoordinates r :=
  ((z.1.2, z.2.2), fun t =>
    fun _ => (z.1.1.factorization (stagePrime t),
      z.2.1.factorization (stagePrime t)))

def momentRoughExponentBox (Q t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (stageExponent Q t + 1)).product
    (Finset.range (stageExponent Q t + 1))

def momentNewExponentPairBox (Q r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (stageExponent Q r + 1)).product
    (Finset.Ico 1 (stageExponent Q r + 1))

def momentRoughPairBox (Q r : ℕ) :
    Finset ((ℕ × ℕ) × MomentRoughExponentCoordinates r) :=
  (momentNewExponentPairBox Q r).product
    ((Finset.Ico 4 r).pi fun t => momentRoughExponentBox Q t)

lemma momentStageRoughKey_mem_image_iff
    {A : CoveringFamily} {s : Finset (Fin A.length)} {Q r : ℕ}
    (k : MomentRoughKey) :
    k ∈ (Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey ↔
      ∃ i : MomentStageIndex A s Q r, momentStageRoughKey i = k := by
  simp

lemma momentStageRoughKey_rough_dvd_partial
    {A : CoveringFamily} {s : Finset (Fin A.length)} {Q r : ℕ}
    {k : MomentRoughKey}
    (hk : k ∈ (Finset.univ : Finset (MomentStageIndex A s Q r)).image
      momentStageRoughKey) :
    k.1 ∣ partialPeriod Q (r - 1) := by
  obtain ⟨i, rfl⟩ := (momentStageRoughKey_mem_image_iff _).mp hk
  exact (fiveRoughPart_dvd (momentStageOldPart i)).trans
    (momentStageOldPart_dvd i)

lemma momentRoughPairEncoding_injOn
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r) :
    Set.InjOn (momentRoughPairEncoding r)
      (↑(((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey).product
        ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
          momentStageRoughKey)) : Set (MomentRoughKey × MomentRoughKey)) := by
  classical
  intro z hz z' hz' he
  have hzmem := Finset.mem_product.mp hz
  have hz'mem := Finset.mem_product.mp hz'
  obtain ⟨i, hi⟩ := (momentStageRoughKey_mem_image_iff z.1).mp hzmem.1
  obtain ⟨j, hj⟩ := (momentStageRoughKey_mem_image_iff z.2).mp hzmem.2
  obtain ⟨i', hi'⟩ := (momentStageRoughKey_mem_image_iff z'.1).mp hz'mem.1
  obtain ⟨j', hj'⟩ := (momentStageRoughKey_mem_image_iff z'.2).mp hz'mem.2
  have hexps : (z.1.2, z.2.2) = (z'.1.2, z'.2.2) := congrArg Prod.fst he
  have hcoords :
      (momentRoughPairEncoding r z).2 = (momentRoughPairEncoding r z').2 :=
    congrArg Prod.snd he
  have hfac1 : ∀ t ∈ Finset.Ico 4 r,
      (fiveRoughPart (momentStageOldPart i)).factorization (stagePrime t) =
        (fiveRoughPart (momentStageOldPart i')).factorization (stagePrime t) := by
    intro t ht
    have := congrArg (fun f => (f t ht).1) hcoords
    change z.1.1.factorization (stagePrime t) =
      z'.1.1.factorization (stagePrime t) at this
    rw [← hi, ← hi'] at this
    simpa only [momentRoughPairEncoding, momentStageRoughKey] using this
  have hfac2 : ∀ t ∈ Finset.Ico 4 r,
      (fiveRoughPart (momentStageOldPart j)).factorization (stagePrime t) =
        (fiveRoughPart (momentStageOldPart j')).factorization (stagePrime t) := by
    intro t ht
    have := congrArg (fun f => (f t ht).2) hcoords
    change z.2.1.factorization (stagePrime t) =
      z'.2.1.factorization (stagePrime t) at this
    rw [← hj, ← hj'] at this
    simpa only [momentRoughPairEncoding, momentStageRoughKey] using this
  have hrough1 : z.1.1 = z'.1.1 := by
    rw [← hi, ← hi']
    exact fiveRoughPart_eq_of_stage_factorizations hr
      (momentStageOldPart_ne_zero hQ i) (momentStageOldPart_ne_zero hQ i')
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd i))
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd i')) hfac1
  have hrough2 : z.2.1 = z'.2.1 := by
    rw [← hj, ← hj']
    exact fiveRoughPart_eq_of_stage_factorizations hr
      (momentStageOldPart_ne_zero hQ j) (momentStageOldPart_ne_zero hQ j')
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd j))
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd j')) hfac2
  have hexp1 : z.1.2 = z'.1.2 :=
    (Prod.ext_iff.mp hexps).1
  have hexp2 : z.2.2 = z'.2.2 :=
    (Prod.ext_iff.mp hexps).2
  apply Prod.ext_iff.mpr
  exact ⟨Prod.ext_iff.mpr ⟨hrough1, hexp1⟩,
    Prod.ext_iff.mpr ⟨hrough2, hexp2⟩⟩

lemma momentRoughPairEncoding_mem_box
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0)
    {z : MomentRoughKey × MomentRoughKey}
    (hz : z ∈ ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey).product
      ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey)) :
    momentRoughPairEncoding r z ∈ momentRoughPairBox Q r := by
  classical
  have hzmem := Finset.mem_product.mp hz
  obtain ⟨i, hi⟩ := (momentStageRoughKey_mem_image_iff z.1).mp hzmem.1
  obtain ⟨j, hj⟩ := (momentStageRoughKey_mem_image_iff z.2).mp hzmem.2
  rw [momentRoughPairBox]
  apply Finset.mem_product.mpr
  constructor
  · rw [momentNewExponentPairBox]
    apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_Ico]
      simpa [momentRoughPairEncoding, ← hi] using
        ⟨momentStageExponent_pos i,
          momentStageExponent_le hQ i⟩
    · rw [Finset.mem_Ico]
      simpa [momentRoughPairEncoding, ← hj] using
        ⟨momentStageExponent_pos j,
          momentStageExponent_le hQ j⟩
  · rw [Finset.mem_pi]
    intro t ht
    rw [momentRoughExponentBox]
    apply Finset.mem_product.mpr
    have hiQ : fiveRoughPart (momentStageOldPart i) ∣ Q :=
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd i)).trans
        (partialPeriod_dvd Q (r - 1) hQ)
    have hjQ : fiveRoughPart (momentStageOldPart j) ∣ Q :=
      ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd j)).trans
        (partialPeriod_dvd Q (r - 1) hQ)
    have hi0 := (fiveRoughPart_pos (momentStageOldPart_ne_zero hQ i)).ne'
    have hj0 := (fiveRoughPart_pos (momentStageOldPart_ne_zero hQ j)).ne'
    have hile := ((Nat.factorization_le_iff_dvd hi0 hQ).2 hiQ) (stagePrime t)
    have hjle := ((Nat.factorization_le_iff_dvd hj0 hQ).2 hjQ) (stagePrime t)
    constructor <;> rw [Finset.mem_range]
    · change z.1.1.factorization (stagePrime t) < stageExponent Q t + 1
      rw [← hi]
      simpa only [momentStageRoughKey, stageExponent, Nat.lt_succ_iff] using hile
    · change z.2.1.factorization (stagePrime t) < stageExponent Q t + 1
      rw [← hj]
      simpa only [momentStageRoughKey, stageExponent, Nat.lt_succ_iff] using hjle

def roughLcmProduct (r a b : ℕ) : ℕ :=
  ∏ t ∈ Finset.Ico 4 r,
    stagePrime t ^ max (a.factorization (stagePrime t))
      (b.factorization (stagePrime t))

lemma fiveRough_lcm_eq_roughLcmProduct
    {Q r m n : ℕ} (hr : 4 ≤ r) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmQ : fiveRoughPart m ∣ partialPeriod Q (r - 1))
    (hnQ : fiveRoughPart n ∣ partialPeriod Q (r - 1)) :
    Nat.lcm (fiveRoughPart m) (fiveRoughPart n) =
      roughLcmProduct r (fiveRoughPart m) (fiveRoughPart n) := by
  let a := fiveRoughPart m
  let b := fiveRoughPart n
  have ha0 : a ≠ 0 := (fiveRoughPart_pos hm).ne'
  have hb0 : b ≠ 0 := (fiveRoughPart_pos hn).ne'
  have hprod0 : roughLcmProduct r a b ≠ 0 := by
    unfold roughLcmProduct
    exact Finset.prod_ne_zero_iff.mpr fun t ht =>
      pow_ne_zero _ (stagePrime_prime
        (by have := (Finset.mem_Ico.mp ht).1; omega : 0 < t)).ne_zero
  apply Nat.eq_of_factorization_eq (Nat.lcm_ne_zero ha0 hb0) hprod0
  intro q
  rw [Nat.factorization_lcm ha0 hb0]
  unfold roughLcmProduct
  rw [Nat.factorization_prod_apply]
  · change max (a.factorization q) (b.factorization q) =
      ∑ t ∈ Finset.Ico 4 r,
        (stagePrime t ^ max (a.factorization (stagePrime t))
          (b.factorization (stagePrime t))).factorization q
    by_cases hq : q.Prime
    · by_cases hdiv : q ∣ a ∨ q ∣ b
      · have hq7 : 7 ≤ q := by
          have hq2 : q ≠ 2 := by
            intro he
            subst q
            rcases hdiv with hd | hd
            · have hh := (Nat.prime_two.dvd_iff_one_le_factorization ha0).mp hd
              simp [a] at hh
            · have hh := (Nat.prime_two.dvd_iff_one_le_factorization hb0).mp hd
              simp [b] at hh
          have hq3 : q ≠ 3 := by
            intro he
            subst q
            rcases hdiv with hd | hd
            · have hh := ((by norm_num : Nat.Prime 3).dvd_iff_one_le_factorization ha0).mp hd
              simp [a] at hh
            · have hh := ((by norm_num : Nat.Prime 3).dvd_iff_one_le_factorization hb0).mp hd
              simp [b] at hh
          have hq5 : q ≠ 5 := by
            intro he
            subst q
            rcases hdiv with hd | hd
            · have hh := ((by norm_num : Nat.Prime 5).dvd_iff_one_le_factorization ha0).mp hd
              simp [a] at hh
            · have hh := ((by norm_num : Nat.Prime 5).dvd_iff_one_le_factorization hb0).mp hd
              simp [b] at hh
          have hq0 := hq.ne_zero
          have hq1 := hq.ne_one
          have hq4 : q ≠ 4 := by
            intro he
            subst q
            norm_num at hq
          have hq6 : q ≠ 6 := by
            intro he
            subst q
            norm_num at hq
          omega
        have hdQ : q ∣ partialPeriod Q (r - 1) := by
          rcases hdiv with hd | hd
          · exact hd.trans hmQ
          · exact hd.trans hnQ
        obtain ⟨t, ht, htp⟩ := prime_dvd_partialPeriod_exists_stage hr hq hq7 hdQ
        rw [Finset.sum_eq_single t]
        · subst q
          rw [Nat.factorization_pow_self
            (stagePrime_prime (by have := (Finset.mem_Ico.mp ht).1; omega))]
        · intro u hu hut
          have hune : stagePrime u ≠ q := by
            intro he
            apply hut
            apply (stagePrime_strictMonoOn.injOn)
            · simp only [Set.mem_Ici]
              have := (Finset.mem_Ico.mp hu).1
              omega
            · simp only [Set.mem_Ici]
              have := (Finset.mem_Ico.mp ht).1
              omega
            · exact he.trans htp.symm
          rw [Nat.Prime.factorization_pow
            (stagePrime_prime (by have := (Finset.mem_Ico.mp hu).1; omega))]
          simp [Finsupp.single_apply, hune]
        · exact fun hnot => (hnot ht).elim
      · push_neg at hdiv
        have ha : a.factorization q = 0 := by
          have := (hq.dvd_iff_one_le_factorization ha0).not.mp hdiv.1
          omega
        have hb : b.factorization q = 0 := by
          have := (hq.dvd_iff_one_le_factorization hb0).not.mp hdiv.2
          omega
        rw [ha, hb, max_self]
        symm
        apply Finset.sum_eq_zero
        intro t ht
        by_cases he : stagePrime t = q
        · subst q
          simp [ha, hb]
        · rw [Nat.Prime.factorization_pow
            (stagePrime_prime (by have := (Finset.mem_Ico.mp ht).1; omega))]
          simp [Finsupp.single_apply, he]
    · have ha : a.factorization q = 0 :=
        Nat.factorization_eq_zero_of_not_prime _ hq
      have hb : b.factorization q = 0 :=
        Nat.factorization_eq_zero_of_not_prime _ hq
      rw [ha, hb, max_self]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  · intro t ht
    exact pow_ne_zero _ (stagePrime_prime
      (by have := (Finset.mem_Ico.mp ht).1; omega : 0 < t)).ne_zero

def momentRoughLocalWeight (δ : ℕ → ℝ) (t : ℕ) (e : ℕ × ℕ) : ℝ :=
  if max e.1 e.2 = 0 then 1
  else (1 / (1 - δ t)) *
    (1 / (stagePrime t : ℝ)) ^ max e.1 e.2

def momentRoughBoxWeight (δ : ℕ → ℝ) (r : ℕ)
    (x : (ℕ × ℕ) × MomentRoughExponentCoordinates r) : ℝ :=
  (1 / (stagePrime r : ℝ)) ^ x.1.1 *
    (1 / (stagePrime r : ℝ)) ^ x.1.2 *
      ∏ t ∈ (Finset.Ico 4 r).attach,
        momentRoughLocalWeight δ t.1 (x.2 t.1 t.2)

lemma reciprocal_roughLcm_eq_prod {Q r m n : ℕ}
    (hr : 4 ≤ r) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmQ : fiveRoughPart m ∣ partialPeriod Q (r - 1))
    (hnQ : fiveRoughPart n ∣ partialPeriod Q (r - 1)) :
    (1 / (Nat.lcm (fiveRoughPart m) (fiveRoughPart n) : ℕ) : ℝ) =
      ∏ t ∈ Finset.Ico 4 r,
        (1 / (stagePrime t : ℝ)) ^
          max ((fiveRoughPart m).factorization (stagePrime t))
            ((fiveRoughPart n).factorization (stagePrime t)) := by
  rw [fiveRough_lcm_eq_roughLcmProduct hr hm hn hmQ hnQ]
  unfold roughLcmProduct
  push_cast
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  simpa only [one_div] using (inv_pow (stagePrime t : ℝ) _).symm
lemma roughMultiplier_eq_prod_local
    {Q r m n : ℕ} (hr : 4 ≤ r) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmQ : fiveRoughPart m ∣ partialPeriod Q (r - 1))
    (hnQ : fiveRoughPart n ∣ partialPeriod Q (r - 1))
    (δ : ℕ → ℝ) (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0) :
    (1 / (Nat.lcm (fiveRoughPart m) (fiveRoughPart n) : ℕ) : ℝ) *
        processedClassFactor stagePrime δ
          (Nat.lcm (fiveRoughPart m) (fiveRoughPart n)) (r - 1) =
      ∏ t ∈ Finset.Ico 4 r,
        momentRoughLocalWeight δ t
          ((fiveRoughPart m).factorization (stagePrime t),
            (fiveRoughPart n).factorization (stagePrime t)) := by
  rw [reciprocal_roughLcm_eq_prod hr hm hn hmQ hnQ,
    processedClassFactor_stagePrime_eq_prod_rough δ _ r hr hδ1 hδ2 hδ3,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  let e := max ((fiveRoughPart m).factorization (stagePrime t))
    ((fiveRoughPart n).factorization (stagePrime t))
  have hp := stagePrime_prime
    (by have := (Finset.mem_Ico.mp ht).1; omega : 0 < t)
  have hl0 : Nat.lcm (fiveRoughPart m) (fiveRoughPart n) ≠ 0 :=
    Nat.lcm_ne_zero (fiveRoughPart_pos hm).ne' (fiveRoughPart_pos hn).ne'
  have hdvd : stagePrime t ∣
      Nat.lcm (fiveRoughPart m) (fiveRoughPart n) ↔ 0 < e := by
    rw [hp.dvd_iff_one_le_factorization hl0, Nat.factorization_lcm
      (fiveRoughPart_pos hm).ne' (fiveRoughPart_pos hn).ne']
    change 1 ≤ max ((fiveRoughPart m).factorization (stagePrime t))
        ((fiveRoughPart n).factorization (stagePrime t)) ↔ 0 < e
    omega
  unfold momentRoughLocalWeight
  change (1 / (stagePrime t : ℝ)) ^ e *
      (if stagePrime t ∣ Nat.lcm (fiveRoughPart m) (fiveRoughPart n)
        then 1 / (1 - δ t) else 1) =
    if e = 0 then 1
    else (1 / (1 - δ t)) * (1 / (stagePrime t : ℝ)) ^ e
  by_cases he : e = 0
  · rw [if_neg (hdvd.not.mpr (by omega)), if_pos he, he, pow_zero,
      one_mul]
  · rw [if_pos (hdvd.mpr (by omega)), if_neg he]
    ring

lemma momentStageRoughWeight_eq_boxWeight
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (δ : ℕ → ℝ) (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0)
    {z : MomentRoughKey × MomentRoughKey}
    (hz : z ∈ ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey).product
      ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey)) :
    momentStageRoughWeight δ r z.1 z.2 =
      momentRoughBoxWeight δ r (momentRoughPairEncoding r z) := by
  have hzmem := Finset.mem_product.mp hz
  obtain ⟨i, hi⟩ := (momentStageRoughKey_mem_image_iff z.1).mp hzmem.1
  obtain ⟨j, hj⟩ := (momentStageRoughKey_mem_image_iff z.2).mp hzmem.2
  have hmul := roughMultiplier_eq_prod_local hr
    (momentStageOldPart_ne_zero hQ i) (momentStageOldPart_ne_zero hQ j)
    ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd i))
    ((fiveRoughPart_dvd _).trans (momentStageOldPart_dvd j))
    δ hδ1 hδ2 hδ3
  unfold momentStageRoughWeight momentRoughBoxWeight momentRoughPairEncoding
  rw [← hi, ← hj]
  unfold momentStageRoughKey
  rw [hmul]
  simp only
  have hprod :
      (∏ t ∈ Finset.Ico 4 r,
        momentRoughLocalWeight δ t
          ((fiveRoughPart (momentStageOldPart i)).factorization (stagePrime t),
            (fiveRoughPart (momentStageOldPart j)).factorization (stagePrime t))) =
      ∏ t ∈ (Finset.Ico 4 r).attach,
        momentRoughLocalWeight δ t.1
          ((fiveRoughPart (momentStageOldPart i)).factorization (stagePrime t.1),
            (fiveRoughPart (momentStageOldPart j)).factorization (stagePrime t.1)) :=
    (Finset.prod_attach (Finset.Ico 4 r) (fun t =>
      momentRoughLocalWeight δ t
        ((fiveRoughPart (momentStageOldPart i)).factorization (stagePrime t),
          (fiveRoughPart (momentStageOldPart j)).factorization (stagePrime t)))).symm
  rw [hprod, one_div_pow, one_div_pow]

lemma momentRoughLocalWeight_nonneg
    (δ : ℕ → ℝ) (hδhalf : ∀ t, δ t ≤ 1 / 2) (t : ℕ) (e : ℕ × ℕ) :
    0 ≤ momentRoughLocalWeight δ t e := by
  unfold momentRoughLocalWeight
  split_ifs
  · norm_num
  · have : 0 < 1 - δ t := by have := hδhalf t; linarith
    positivity

lemma momentRoughBoxWeight_nonneg
    (δ : ℕ → ℝ) (hδhalf : ∀ t, δ t ≤ 1 / 2) (r : ℕ)
    (x : (ℕ × ℕ) × MomentRoughExponentCoordinates r) :
    0 ≤ momentRoughBoxWeight δ r x := by
  unfold momentRoughBoxWeight
  apply mul_nonneg
  · apply mul_nonneg <;> positivity
  · exact Finset.prod_nonneg fun t ht =>
      momentRoughLocalWeight_nonneg δ hδhalf t.1 (x.2 t.1 t.2)

lemma sum_momentNewExponentPairBox_le
    {Q r : ℕ} (hr : 0 < r) :
    (∑ e ∈ momentNewExponentPairBox Q r,
      (1 / (stagePrime r : ℝ)) ^ e.1 *
        (1 / (stagePrime r : ℝ)) ^ e.2) ≤
      1 / ((stagePrime r : ℝ) - 1) ^ 2 := by
  have hgeom := finite_prime_power_pair_sum_le
    (p := (stagePrime r : ℝ)) (by exact_mod_cast stagePrime_one_lt hr)
    (stageExponent Q r) (stageExponent Q r)
  calc
    (∑ e ∈ momentNewExponentPairBox Q r,
      (1 / (stagePrime r : ℝ)) ^ e.1 *
        (1 / (stagePrime r : ℝ)) ^ e.2) =
        (∑ a ∈ Finset.Ico 1 (stageExponent Q r + 1),
          (1 / (stagePrime r : ℝ)) ^ a) *
        (∑ b ∈ Finset.Ico 1 (stageExponent Q r + 1),
          (1 / (stagePrime r : ℝ)) ^ b) := by
      let S := Finset.Ico 1 (stageExponent Q r + 1)
      calc
        (∑ e ∈ momentNewExponentPairBox Q r,
            (1 / (stagePrime r : ℝ)) ^ e.1 *
              (1 / (stagePrime r : ℝ)) ^ e.2) =
            ∑ a ∈ S, ∑ b ∈ S,
              (1 / (stagePrime r : ℝ)) ^ a *
                (1 / (stagePrime r : ℝ)) ^ b := by
          unfold momentNewExponentPairBox
          change (∑ e ∈ S ×ˢ S,
              (1 / (stagePrime r : ℝ)) ^ e.1 *
                (1 / (stagePrime r : ℝ)) ^ e.2) =
            ∑ a ∈ S, ∑ b ∈ S,
              (1 / (stagePrime r : ℝ)) ^ a *
                (1 / (stagePrime r : ℝ)) ^ b
          exact Finset.sum_product' S S
            (fun a b => (1 / (stagePrime r : ℝ)) ^ a *
              (1 / (stagePrime r : ℝ)) ^ b)
        _ = (∑ a ∈ S, (1 / (stagePrime r : ℝ)) ^ a) *
            (∑ b ∈ S, (1 / (stagePrime r : ℝ)) ^ b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ ≤ 1 / ((stagePrime r : ℝ) - 1) ^ 2 := hgeom

lemma sum_momentRoughCoordinateBox_le
    {Q r : ℕ} (hr : 4 ≤ r) (δ : ℕ → ℝ)
    (hδhalf : ∀ t, δ t ≤ 1 / 2) :
    (∑ x ∈ (Finset.Ico 4 r).pi (fun t => momentRoughExponentBox Q t),
      ∏ t ∈ (Finset.Ico 4 r).attach,
        momentRoughLocalWeight δ t.1 (x t.1 t.2)) ≤
      ∏ t ∈ Finset.Ico 4 r, secondMomentEulerFactor (stagePrime t) (δ t) := by
  let S := Finset.Ico 4 r
  have hlocal : ∀ t ∈ S,
      (∑ e ∈ momentRoughExponentBox Q t,
        momentRoughLocalWeight δ t e) ≤
        secondMomentEulerFactor (stagePrime t) (δ t) := by
    intro t ht
    have ht4 : 4 ≤ t := (Finset.mem_Ico.mp ht).1
    have hδlt : δ t < 1 := lt_of_le_of_lt (hδhalf t) (by norm_num)
    unfold momentRoughExponentBox
    calc
      (∑ x ∈ (Finset.range (stageExponent Q t + 1)).product
          (Finset.range (stageExponent Q t + 1)),
          momentRoughLocalWeight δ t x) =
          ∑ a ∈ Finset.range (stageExponent Q t + 1),
            ∑ b ∈ Finset.range (stageExponent Q t + 1),
              momentRoughLocalWeight δ t (a, b) := by
        exact Finset.sum_product _ _ _
      _ ≤ secondMomentEulerFactor (stagePrime t) (δ t) := by
        simpa [momentRoughLocalWeight, max_eq_zero] using
          (finite_exponent_pair_factor_le
            (p := (stagePrime t : ℝ)) (δ := δ t)
            (by exact_mod_cast stagePrime_one_lt (by omega : 0 < t))
            hδlt (stageExponent Q t))
  have hpi := sum_pi_prod_le_prod
    (s := S) (t := fun t => momentRoughExponentBox Q t)
    (f := fun t e => momentRoughLocalWeight δ t e)
    (B := fun t => secondMomentEulerFactor (stagePrime t) (δ t))
    (fun t ht e he => momentRoughLocalWeight_nonneg δ hδhalf t e)
    hlocal
  simpa [S] using hpi

lemma sum_momentRoughPairBox_le
    {Q r : ℕ} (hr : 4 ≤ r) (δ : ℕ → ℝ)
    (hδhalf : ∀ t, δ t ≤ 1 / 2) :
    (∑ x ∈ momentRoughPairBox Q r, momentRoughBoxWeight δ r x) ≤
      1 / ((stagePrime r : ℝ) - 1) ^ 2 *
        ∏ t ∈ Finset.Ico 4 r,
          secondMomentEulerFactor (stagePrime t) (δ t) := by
  let E := momentNewExponentPairBox Q r
  let C := (Finset.Ico 4 r).pi (fun t => momentRoughExponentBox Q t)
  let newWeight : ℕ × ℕ → ℝ := fun e =>
    (1 / (stagePrime r : ℝ)) ^ e.1 * (1 / (stagePrime r : ℝ)) ^ e.2
  let coordinateWeight : MomentRoughExponentCoordinates r → ℝ := fun x =>
    ∏ t ∈ (Finset.Ico 4 r).attach,
      momentRoughLocalWeight δ t.1 (x t.1 t.2)
  have hsplit :
      (∑ x ∈ momentRoughPairBox Q r, momentRoughBoxWeight δ r x) =
        (∑ e ∈ E, newWeight e) * (∑ x ∈ C, coordinateWeight x) := by
    change (∑ z ∈ E.product C, newWeight z.1 * coordinateWeight z.2) =
      (∑ e ∈ E, newWeight e) * (∑ x ∈ C, coordinateWeight x)
    calc
      _ = ∑ e ∈ E, ∑ x ∈ C, newWeight e * coordinateWeight x := by
        exact Finset.sum_product' E C (fun e x => newWeight e * coordinateWeight x)
      _ = (∑ e ∈ E, newWeight e) * (∑ x ∈ C, coordinateWeight x) := by
        symm
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.mul_sum]
  rw [hsplit]
  calc
    (∑ e ∈ E, newWeight e) * (∑ x ∈ C, coordinateWeight x) ≤
        (1 / ((stagePrime r : ℝ) - 1) ^ 2) *
          (∑ x ∈ C, coordinateWeight x) := by
      apply mul_le_mul_of_nonneg_right
      · simpa [E, newWeight] using sum_momentNewExponentPairBox_le
          (Q := Q) (r := r) (by omega : 0 < r)
      · exact Finset.sum_nonneg fun x hx => by
          unfold coordinateWeight
          exact Finset.prod_nonneg fun t ht =>
            momentRoughLocalWeight_nonneg δ hδhalf t.1 (x t.1 t.2)
    _ ≤ (1 / ((stagePrime r : ℝ) - 1) ^ 2) *
        ∏ t ∈ Finset.Ico 4 r,
          secondMomentEulerFactor (stagePrime t) (δ t) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [C, coordinateWeight] using
          sum_momentRoughCoordinateBox_le (Q := Q) hr δ hδhalf
      · positivity

lemma momentStage_roughSecondMoment_le
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (δ : ℕ → ℝ) (hδhalf : ∀ t, δ t ≤ 1 / 2)
    (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0) :
    roughSecondMoment
        ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
          momentStageRoughKey)
        (momentStageRoughWeight δ r) ≤
      1 / ((stagePrime r : ℝ) - 1) ^ 2 *
        ∏ t ∈ Finset.Ico 4 r,
          secondMomentEulerFactor (stagePrime t) (δ t) := by
  let R := (Finset.univ : Finset (MomentStageIndex A s Q r)).image
    momentStageRoughKey
  calc
    roughSecondMoment R (momentStageRoughWeight δ r) =
        ∑ z ∈ R.product R, momentStageRoughWeight δ r z.1 z.2 := by
      unfold roughSecondMoment
      exact (Finset.sum_product' R R (momentStageRoughWeight δ r)).symm
    _ ≤ ∑ x ∈ momentRoughPairBox Q r, momentRoughBoxWeight δ r x := by
      apply sum_le_sum_over_injective_encoding
        (encode := momentRoughPairEncoding r)
      · simpa [R] using momentRoughPairEncoding_injOn A s hQ hr
      · intro z hz
        simpa [R] using momentRoughPairEncoding_mem_box A s hQ hz
      · intro z hz
        exact le_of_eq (momentStageRoughWeight_eq_boxWeight A s hQ hr
          δ hδ1 hδ2 hδ3 (by simpa [R] using hz))
      · intro x hx
        exact momentRoughBoxWeight_nonneg δ hδhalf r x
    _ ≤ 1 / ((stagePrime r : ℝ) - 1) ^ 2 *
        ∏ t ∈ Finset.Ico 4 r,
          secondMomentEulerFactor (stagePrime t) (δ t) :=
      sum_momentRoughPairBox_le hr δ hδhalf

lemma momentStageRoughWeight_nonneg
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (δ : ℕ → ℝ) (hδhalf : ∀ t, δ t ≤ 1 / 2)
    (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0)
    {k l : MomentRoughKey}
    (hk : k ∈ (Finset.univ : Finset (MomentStageIndex A s Q r)).image
      momentStageRoughKey)
    (hl : l ∈ (Finset.univ : Finset (MomentStageIndex A s Q r)).image
      momentStageRoughKey) :
    0 ≤ momentStageRoughWeight δ r k l := by
  let z : MomentRoughKey × MomentRoughKey := (k, l)
  have hz : z ∈
      ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey).product
      ((Finset.univ : Finset (MomentStageIndex A s Q r)).image
        momentStageRoughKey) := Finset.mem_product.mpr ⟨hk, hl⟩
  rw [momentStageRoughWeight_eq_boxWeight A s hQ hr δ hδ1 hδ2 hδ3 hz]
  exact momentRoughBoxWeight_nonneg δ hδhalf r _

/-- The fully instantiated BBMST second-moment estimate at a selected
divisibility-antichain stage.  Neither the smooth reindexing nor the rough
Euler estimate remains as a premise. -/
theorem momentStage_secondMoment_le_refined
    (A : CoveringFamily) (s : Finset (Fin A.length))
    {Q r : ℕ} (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (δ : ℕ → ℝ) (hδhalf : ∀ t, δ t ≤ 1 / 2)
    (hδ1 : δ 1 = 0) (hδ2 : δ 2 = 0) (hδ3 : δ 3 = 0)
    (mu : FiniteProbability (ZMod (partialPeriod Q (r - 1))))
    (hclass : HasProcessedClassMassBound mu δ) :
    secondMoment mu (momentStageBadSet A s Q r hQ) ≤
      refinedSecondMomentBound fiveSmoothKappa (stagePrime r)
        (Finset.Ico 4 r) (fun t => (stagePrime t : ℝ)) δ := by
  let R := (Finset.univ : Finset (MomentStageIndex A s Q r)).image
    momentStageRoughKey
  let D := keyedFiber
    (Finset.univ : Finset (MomentStageIndex A s Q r))
    momentStageRoughKey momentStageSmoothValue
  calc
    secondMoment mu (momentStageBadSet A s Q r hQ) ≤
        ∑ i : MomentStageIndex A s Q r,
          ∑ j : MomentStageIndex A s Q r,
            (momentStageCoefficient i * momentStageCoefficient j) *
              ((1 / (Nat.lcm (momentStageOldPart i)
                (momentStageOldPart j) : ℕ)) *
                processedClassFactor stagePrime δ
                  (Nat.lcm (momentStageOldPart i)
                    (momentStageOldPart j)) (r - 1)) :=
      momentStage_secondMoment_le_lcmSum A s hQ (by omega) mu δ hclass
    _ ≤ smoothRoughSecondMoment R (momentStageRoughWeight δ r) D := by
      simpa [R, D] using
        momentStage_lcmSum_le_smoothRough A s hQ hr hanti δ hδ1 hδ2 hδ3
    _ ≤ refinedSecondMomentBound fiveSmoothKappa (stagePrime r)
        (Finset.Ico 4 r) (fun t => (stagePrime t : ℝ)) δ := by
      apply smoothRoughSecondMoment_le_refined_bound
      · intro k hk l hl
        exact momentStageRoughWeight_nonneg A s hQ hr δ hδhalf
          hδ1 hδ2 hδ3 hk hl
      · intro k hk
        exact momentStage_smoothFiber_antichain A s hQ hanti k
      · simpa [R] using momentStage_roughSecondMoment_le
          A s hQ hr δ hδhalf hδ1 hδ2 hδ3

end

end Erdos586
