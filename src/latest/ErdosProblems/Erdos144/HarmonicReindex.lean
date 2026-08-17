/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicDecomposition

/-!
# Finite reindexing lemmas for the harmonic energy estimate

This file records the exact finite identities used when an ordered balanced
pair of ternary states is reindexed by its preceding selected coordinate and
its forced largest differing coordinate.  In particular, after the forced
coordinate is deleted, summing over all remaining ordered ternary profiles
costs exactly the Bernoulli inclusion probability of the predecessor.
-/

open scoped BigOperators

namespace Erdos144.HarmonicReindex

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicBlocks HarmonicOctaves HarmonicDecomposition

theorem collisionWitness_ext {S : Finset ℕ}
    (u v : Σ z : ℤ,
      {q // q ∈ ((signedStates S).filter fun a ↦ signedValue S a = z).offDiag})
    (hleft : collisionWitnessLeft u = collisionWitnessLeft v)
    (hright : collisionWitnessRight u = collisionWitnessRight v) :
    u = v := by
  rcases u with ⟨zu, qu⟩
  rcases v with ⟨zv, qv⟩
  have hzu := (Finset.mem_filter.mp
    (Finset.mem_offDiag.mp qu.property).1).2
  have hzv := (Finset.mem_filter.mp
    (Finset.mem_offDiag.mp qv.property).1).2
  have hz : zu = zv := by
    exact hzu.symm.trans
      ((congrArg (signedValue S) hleft).trans hzv)
  subst zv
  have hq : qu = qv := Subtype.ext (Prod.ext hleft hright)
  exact congrArg (fun q ↦ Sigma.mk zu q) hq

/-- Ordered ternary profiles on a selected set. -/
def pairProfiles (S : Finset ℕ) : Finset ((↑S → Fin 3) × (↑S → Fin 3)) :=
  Finset.univ

@[simp] theorem pairProfiles_card (S : Finset ℕ) :
    (pairProfiles S).card = 9 ^ S.card := by
  simp only [pairProfiles, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  rw [← mul_pow]
  norm_num

/-- Once a selected coordinate has been removed, the normalized sum over
all ordered ternary profiles on the remaining selected set is exactly its
Bernoulli weight. -/
theorem sum_pairProfiles_normalized_weight
    (I S : Finset ℕ) :
    (∑ _q ∈ pairProfiles S,
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
        (9 : ℝ) ^ S.card) =
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S := by
  rw [Finset.sum_const, nsmul_eq_mul, pairProfiles_card]
  push_cast
  have h9 : (9 : ℝ) ^ S.card ≠ 0 := by positivity
  field_simp

/-- Summing all normalized erased profiles which still contain `M` costs
exactly `1/M`.  This is the second harmonic factor in the
largest-coordinate estimate. -/
theorem sum_normalized_pairProfiles_containing_eq
    {I : Finset ℕ} {M : ℕ} (hMI : M ∈ I) :
    (∑ S ∈ I.powerset.filter (fun S ↦ M ∈ S),
      ∑ _q ∈ pairProfiles S,
        Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
          (9 : ℝ) ^ S.card) =
      1 / (M : ℝ) := by
  simp_rw [sum_pairProfiles_normalized_weight]
  exact sum_harmonic_weight_filter_mem_eq hMI

/-- The exact deletion factor is at most `1/(9M)` whenever the deleted
coordinate lies strictly above `M`. -/
theorem harmonic_normalized_weight_erase_le
    {I S : Finset ℕ} {M n : ℕ}
    (hSI : S ⊆ I) (hIpos : ∀ i ∈ I, 0 < i)
    (hnI : n ∈ I) (hnS : n ∈ S) (hM : 0 < M) (hMn : M < n) :
    Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
        (9 : ℝ) ^ S.card ≤
      (1 / (9 * (M : ℝ))) *
        (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) (S.erase n) /
          (9 : ℝ) ^ (S.erase n).card) := by
  rw [harmonic_normalized_weight_eq_erase hnI hnS (by omega)]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsucc : (M : ℝ) + 1 ≤ n := by
    exact_mod_cast (show M + 1 ≤ n by omega)
  have hpred : (M : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hfactor :
      1 / (9 * ((n : ℝ) - 1)) ≤ 1 / (9 * (M : ℝ)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have hnonneg :
      0 ≤ Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) (S.erase n) /
        (9 : ℝ) ^ (S.erase n).card := by
    apply div_nonneg
    · apply Erdos697.Bernoulli.weight_nonneg
      · intro i hi
        positivity
      · intro i hi
        have hiPos : 0 < i := hIpos i hi
        exact (div_le_one (by exact_mod_cast hiPos)).2 (by exact_mod_cast hiPos)
      · exact Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hSI)
    · positivity
  exact mul_le_mul_of_nonneg_right hfactor hnonneg

/-- The six unequal ordered local ternary pairs turn the deletion factor
`1/(9M)` into the familiar `2/(3M)`. -/
theorem six_mul_forced_factor (M : ℕ) :
    (6 : ℝ) * (1 / (9 * (M : ℝ))) = 2 / (3 * (M : ℝ)) := by
  ring

/-- Low-octave fibre bound after all erased profiles have been summed.
This packages the two exact harmonic factors: selecting the predecessor
costs `1/M`, while the forced coordinate and its six unequal local state
pairs cost `2/(3M)`. -/
theorem low_fibre_mass_le {I : Finset ℕ} {M : ℕ}
    (hMI : M ∈ I) :
    (6 : ℝ) * (1 / (9 * (M : ℝ))) *
        (∑ S ∈ I.powerset.filter (fun S ↦ M ∈ S),
          ∑ _q ∈ pairProfiles S,
            Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
              (9 : ℝ) ^ S.card) =
      (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) := by
  rw [sum_normalized_pairProfiles_containing_eq hMI]
  ring

/-! ## Exact diagonal-tail loss -/

/-- Ordered profiles whose two ternary states agree on a prescribed set of
coordinates. -/
def pairProfilesAgreeOn (S : Finset ℕ) (Q : Finset ↑S) :
    Finset ((↑S → Fin 3) × (↑S → Fin 3)) :=
  (pairProfiles S).filter fun q ↦ ∀ i ∈ Q, q.1 i = q.2 i

/-- A profile agreeing on `Q` is the same data as its first state together
with the restriction of its second state to the complement of `Q`. -/
def agreePairEquiv (S : Finset ℕ) (Q : Finset ↑S) :
    {q : (↑S → Fin 3) × (↑S → Fin 3) //
      ∀ i ∈ Q, q.1 i = q.2 i} ≃
      (↑S → Fin 3) × ({i : ↑S // i ∉ Q} → Fin 3) where
  toFun q := ⟨q.1.1, fun i ↦ q.1.2 i.1⟩
  invFun q := ⟨⟨q.1, fun i ↦ if hi : i ∈ Q then q.1 i else q.2 ⟨i, hi⟩⟩, by
    intro i hi
    simp [hi]⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i ∈ Q
      · simp [hi, q.2 i hi]
      · simp [hi]
  right_inv q := by
    apply Prod.ext
    · rfl
    · funext i
      simp [i.2]

theorem pairProfilesAgreeOn_card (S : Finset ℕ) (Q : Finset ↑S) :
    (pairProfilesAgreeOn S Q).card =
      3 ^ S.card * 3 ^ (S.card - Q.card) := by
  have hfilter :
      (pairProfilesAgreeOn S Q).card =
        Fintype.card {q : (↑S → Fin 3) × (↑S → Fin 3) //
          ∀ i ∈ Q, q.1 i = q.2 i} := by
    let e : {q // q ∈ pairProfilesAgreeOn S Q} ≃
        {q : (↑S → Fin 3) × (↑S → Fin 3) //
          ∀ i ∈ Q, q.1 i = q.2 i} :=
      { toFun := fun q ↦
          ⟨q.val, (Finset.mem_filter.mp q.property).2⟩
        invFun := fun q ↦
          ⟨q.val, Finset.mem_filter.mpr
            ⟨by simp [pairProfiles], q.property⟩⟩
        left_inv := fun q ↦ Subtype.ext rfl
        right_inv := fun q ↦ Subtype.ext rfl }
    calc
      (pairProfilesAgreeOn S Q).card =
          Fintype.card {q // q ∈ pairProfilesAgreeOn S Q} := by simp
      _ = _ := Fintype.card_congr e
  rw [hfilter, Fintype.card_congr (agreePairEquiv S Q)]
  simp [Fintype.card_subtype_compl]

/-- Prescribing diagonality on `Q` loses exactly one factor `3` for each
coordinate of `Q` after normalization by all ordered pair profiles. -/
theorem sum_pairProfilesAgreeOn_normalized_weight
    (I S : Finset ℕ) (Q : Finset ↑S) :
    (∑ _q ∈ pairProfilesAgreeOn S Q,
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
        (9 : ℝ) ^ S.card) =
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) S /
        (3 : ℝ) ^ Q.card := by
  rw [Finset.sum_const, nsmul_eq_mul, pairProfilesAgreeOn_card]
  push_cast
  have hQS : Q.card ≤ S.card := by
    simpa using Finset.card_le_card (Finset.subset_univ Q)
  have hsplit : S.card = (S.card - Q.card) + Q.card := by omega
  rw [show (9 : ℝ) ^ S.card =
      3 ^ S.card * 3 ^ S.card by rw [← mul_pow]; norm_num]
  rw [hsplit, pow_add]
  field_simp
  rw [Nat.add_sub_cancel]

/-! ## The low-octave overcounting universe -/

/-- Difference contributed by an erased ordered profile. -/
def profileDifference {T : Finset ℕ}
    (q : (↑T → Fin 3) × (↑T → Fin 3)) : ℤ :=
  Finset.univ.sum fun i : ↑T ↦
    signedTerm i.1 (q.1 i) - signedTerm i.1 (q.2 i)

/-- Possible forced coordinates extending an erased profile. -/
def forcedExtensions (I : Finset ℕ) (M : ℕ) (T : Finset ℕ)
    (q : (↑T → Fin 3) × (↑T → Fin 3))
    (xy : Fin 3 × Fin 3) : Finset ℕ :=
  I.filter fun n ↦ M < n ∧ n ∉ T ∧
    signedTerm n xy.1 - signedTerm n xy.2 = -profileDifference q

theorem forcedExtensions_card_le_one
    {I : Finset ℕ} {M : ℕ} {T : Finset ℕ}
    {q : (↑T → Fin 3) × (↑T → Fin 3)}
    {xy : Fin 3 × Fin 3} (hxy : xy.1 ≠ xy.2) :
    (forcedExtensions I M T q xy).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro n hn m hm
  have hnEq := (Finset.mem_filter.mp hn).2.2.2
  have hmEq := (Finset.mem_filter.mp hm).2.2.2
  exact signedTerm_difference_injective hxy (hnEq.trans hmEq.symm)

theorem sum_forcedExtensions_odds_le
    {I : Finset ℕ} {M : ℕ} {T : Finset ℕ}
    {q : (↑T → Fin 3) × (↑T → Fin 3)}
    {xy : Fin 3 × Fin 3} (hM : 0 < M) (hxy : xy.1 ≠ xy.2) :
    (∑ n ∈ forcedExtensions I M T q xy,
      1 / (9 * ((n : ℝ) - 1))) ≤
      1 / (9 * (M : ℝ)) := by
  have hbound : ∀ n ∈ forcedExtensions I M T q xy,
      1 / (9 * ((n : ℝ) - 1)) ≤ 1 / (9 * (M : ℝ)) := by
    intro n hn
    have hMn : M < n := (Finset.mem_filter.mp hn).2.1
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hsucc : (M : ℝ) + 1 ≤ n := by
      exact_mod_cast (show M + 1 ≤ n by omega)
    have hpred : (M : ℝ) ≤ (n : ℝ) - 1 := by linarith
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  calc
    (∑ n ∈ forcedExtensions I M T q xy,
        1 / (9 * ((n : ℝ) - 1))) ≤
        ∑ _n ∈ forcedExtensions I M T q xy,
          1 / (9 * (M : ℝ)) := by
      exact Finset.sum_le_sum fun n hn ↦ hbound n hn
    _ = ((forcedExtensions I M T q xy).card : ℝ) *
          (1 / (9 * (M : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * (1 / (9 * (M : ℝ))) := by
      gcongr
      exact_mod_cast forcedExtensions_card_le_one hxy
    _ = 1 / (9 * (M : ℝ)) := one_mul _

/-- Total mass of the canonical low-octave overcounting codes with
predecessor `M`. -/
def lowReindexMass (I : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ T ∈ I.powerset.filter (fun T ↦ M ∈ T),
    ∑ q ∈ pairProfiles T,
      ∑ xy ∈ unequalStatePairs,
        (∑ n ∈ forcedExtensions I M T q xy,
          1 / (9 * ((n : ℝ) - 1))) *
            (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
              (9 : ℝ) ^ T.card)

/-- The canonical low-octave codes have total mass at most
`(2/3) / M²`. -/
theorem lowReindexMass_le {I : Finset ℕ} {M : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i) (hMI : M ∈ I) :
    lowReindexMass I M ≤ (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) := by
  have hM : 0 < M := hIpos M hMI
  unfold lowReindexMass
  calc
    (∑ T ∈ I.powerset.filter (fun T ↦ M ∈ T),
      ∑ q ∈ pairProfiles T,
        ∑ xy ∈ unequalStatePairs,
          (∑ n ∈ forcedExtensions I M T q xy,
            1 / (9 * ((n : ℝ) - 1))) *
              (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
                (9 : ℝ) ^ T.card)) ≤
        ∑ T ∈ I.powerset.filter (fun T ↦ M ∈ T),
          ∑ q ∈ pairProfiles T,
            ∑ _xy ∈ unequalStatePairs,
              (1 / (9 * (M : ℝ))) *
                (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
                  (9 : ℝ) ^ T.card) := by
      apply Finset.sum_le_sum
      intro T hT
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro xy hxy
      apply mul_le_mul_of_nonneg_right
      · exact sum_forcedExtensions_odds_le hM
          (Finset.mem_filter.mp hxy).2
      · apply div_nonneg
        · apply Erdos697.Bernoulli.weight_nonneg
          · intro i hi
            positivity
          · intro i hi
            have hip : 0 < i := hIpos i hi
            exact (div_le_one (by exact_mod_cast hip)).2 (by exact_mod_cast hip)
          · exact (Finset.mem_filter.mp hT).1
        · positivity
    _ = (6 : ℝ) * (1 / (9 * (M : ℝ))) *
        (∑ T ∈ I.powerset.filter (fun T ↦ M ∈ T),
          ∑ _q ∈ pairProfiles T,
            Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
              (9 : ℝ) ^ T.card) := by
      simp only [Finset.sum_const, nsmul_eq_mul, unequalStatePairs_card]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      ring
    _ = (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) :=
      low_fibre_mass_le hMI

/-! ## Separated diagonal tails for high octaves -/

/-- Total normalized mass of diagonal ordered profiles whose selected tail
has at least `t` coordinates.  The `3^|V|` denominator is what remains
after summing the three diagonal local states on every selected coordinate. -/
def diagonalTailMass (J : Finset ℕ) (t : ℕ) : ℝ :=
  ∑ V ∈ J.powerset.filter (fun V ↦ t ≤ V.card),
    Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V /
      (3 : ℝ) ^ V.card

theorem diagonalTailMass_le {J : Finset ℕ} {t : ℕ}
    (hJpos : ∀ i ∈ J, 0 < i) :
    diagonalTailMass J t ≤ 1 / (3 : ℝ) ^ t := by
  have hwt : ∀ V ∈ J.powerset,
      0 ≤ Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V := by
    intro V hV
    apply Erdos697.Bernoulli.weight_nonneg
    · intro i hi
      positivity
    · intro i hi
      have hip := hJpos i hi
      exact (div_le_one (by exact_mod_cast hip)).2 (by exact_mod_cast hip)
    · exact hV
  calc
    diagonalTailMass J t ≤
        (1 / (3 : ℝ) ^ t) *
          ∑ V ∈ J.powerset.filter (fun V ↦ t ≤ V.card),
            Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V := by
      unfold diagonalTailMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro V hV
      rw [Finset.mem_filter] at hV
      have hpow : (3 : ℝ) ^ t ≤ 3 ^ V.card := by
        exact pow_le_pow_right₀ (by norm_num) hV.2
      have hinv : 1 / (3 : ℝ) ^ V.card ≤ 1 / 3 ^ t :=
        one_div_le_one_div_of_le (by positivity) hpow
      calc
        Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V /
            (3 : ℝ) ^ V.card =
            (1 / (3 : ℝ) ^ V.card) *
              Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V := by ring
        _ ≤ (1 / (3 : ℝ) ^ t) *
              Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V :=
          mul_le_mul_of_nonneg_right hinv (hwt V hV.1)
    _ ≤ (1 / (3 : ℝ) ^ t) *
        (∑ V ∈ J.powerset,
          Erdos697.Bernoulli.weight J (fun i ↦ 1 / (i : ℝ)) V) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro V hV
          exact (Finset.mem_filter.mp hV).1
        · intro V hV hnot
          exact hwt V hV
      · positivity
    _ = 1 / (3 : ℝ) ^ t := by
      rw [Erdos697.Bernoulli.sum_weight_powerset]
      ring

theorem sum_forcedExtensions_probability_le
    {I : Finset ℕ} {M : ℕ} {T : Finset ℕ}
    {q : (↑T → Fin 3) × (↑T → Fin 3)}
    {xy : Fin 3 × Fin 3} (hM : 0 < M) (hxy : xy.1 ≠ xy.2) :
    (∑ n ∈ forcedExtensions I M T q xy,
      1 / (9 * (n : ℝ))) ≤
      1 / (9 * (M : ℝ)) := by
  have hbound : ∀ n ∈ forcedExtensions I M T q xy,
      1 / (9 * (n : ℝ)) ≤ 1 / (9 * (M : ℝ)) := by
    intro n hn
    have hMn : M < n := (Finset.mem_filter.mp hn).2.1
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ n := by exact_mod_cast hMn.le
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  calc
    (∑ n ∈ forcedExtensions I M T q xy,
        1 / (9 * (n : ℝ))) ≤
        ∑ _n ∈ forcedExtensions I M T q xy,
          1 / (9 * (M : ℝ)) :=
      Finset.sum_le_sum fun n hn ↦ hbound n hn
    _ = ((forcedExtensions I M T q xy).card : ℝ) *
          (1 / (9 * (M : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * (1 / (9 * (M : ℝ))) := by
      gcongr
      exact_mod_cast forcedExtensions_card_le_one hxy
    _ = 1 / (9 * (M : ℝ)) := one_mul _

def lowerRegion (I : Finset ℕ) (M : ℕ) : Finset ℕ :=
  I.filter fun i ↦ i ≤ M

def upperRegion (I : Finset ℕ) (n : ℕ) : Finset ℕ :=
  I.filter fun i ↦ n < i

def highExtensionFibre (I : Finset ℕ) (M t : ℕ)
    (U : Finset ℕ)
    (q : (↑U → Fin 3) × (↑U → Fin 3))
    (xy : Fin 3 × Fin 3) : ℝ :=
  ∑ n ∈ forcedExtensions I M U q xy,
    (1 / (9 * (n : ℝ))) *
      (Erdos697.Bernoulli.weight (lowerRegion I M)
          (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
      diagonalTailMass (upperRegion I n) t

theorem highExtensionFibre_le
    {I : Finset ℕ} {M t : ℕ} {U : Finset ℕ}
    {q : (↑U → Fin 3) × (↑U → Fin 3)}
    {xy : Fin 3 × Fin 3}
    (hIpos : ∀ i ∈ I, 0 < i) (hM : 0 < M)
    (hU : U ∈ (lowerRegion I M).powerset) (hxy : xy.1 ≠ xy.2) :
    highExtensionFibre I M t U q xy ≤
      (1 / (9 * (M : ℝ))) *
        (Erdos697.Bernoulli.weight (lowerRegion I M)
            (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
        (1 / (3 : ℝ) ^ t) := by
  have hLowerPos : ∀ i ∈ lowerRegion I M, 0 < i := by
    intro i hi
    exact hIpos i (Finset.mem_filter.mp hi).1
  have hnorm : 0 ≤
      Erdos697.Bernoulli.weight (lowerRegion I M)
          (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card := by
    apply div_nonneg
    · apply Erdos697.Bernoulli.weight_nonneg
      · intro i hi
        positivity
      · intro i hi
        have hip := hLowerPos i hi
        exact (div_le_one (by exact_mod_cast hip)).2 (by exact_mod_cast hip)
      · exact hU
    · positivity
  unfold highExtensionFibre
  calc
    (∑ n ∈ forcedExtensions I M U q xy,
      (1 / (9 * (n : ℝ))) *
        (Erdos697.Bernoulli.weight (lowerRegion I M)
            (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
        diagonalTailMass (upperRegion I n) t) ≤
      ∑ n ∈ forcedExtensions I M U q xy,
        (1 / (9 * (n : ℝ))) *
          (Erdos697.Bernoulli.weight (lowerRegion I M)
              (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
          (1 / (3 : ℝ) ^ t) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := lt_of_lt_of_le hM
        (Finset.mem_filter.mp hn).2.1.le
      apply mul_le_mul_of_nonneg_left
      · exact diagonalTailMass_le (fun i hi ↦
          hIpos i (Finset.mem_filter.mp hi).1)
      · exact mul_nonneg (by positivity) hnorm
    _ = (∑ n ∈ forcedExtensions I M U q xy,
          1 / (9 * (n : ℝ))) *
        (Erdos697.Bernoulli.weight (lowerRegion I M)
            (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
        (1 / (3 : ℝ) ^ t) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ (1 / (9 * (M : ℝ))) *
        (Erdos697.Bernoulli.weight (lowerRegion I M)
            (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
        (1 / (3 : ℝ) ^ t) := by
      gcongr
      exact sum_forcedExtensions_probability_le hM hxy

/-- Separated high-octave overcounting mass with at least `t` diagonal
selected coordinates above the forced coordinate. -/
def highReindexMass (I : Finset ℕ) (M t : ℕ) : ℝ :=
  ∑ U ∈ (lowerRegion I M).powerset.filter (fun U ↦ M ∈ U),
    ∑ q ∈ pairProfiles U,
      ∑ xy ∈ unequalStatePairs,
        highExtensionFibre I M t U q xy

theorem highReindexMass_le
    {I : Finset ℕ} {M t : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i) (hMI : M ∈ I) :
    highReindexMass I M t ≤
      (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) *
        (1 / (3 : ℝ) ^ t) := by
  have hM : 0 < M := hIpos M hMI
  have hMLower : M ∈ lowerRegion I M := by simp [lowerRegion, hMI]
  unfold highReindexMass
  calc
    (∑ U ∈ (lowerRegion I M).powerset.filter (fun U ↦ M ∈ U),
      ∑ q ∈ pairProfiles U,
        ∑ xy ∈ unequalStatePairs,
          highExtensionFibre I M t U q xy) ≤
      ∑ U ∈ (lowerRegion I M).powerset.filter (fun U ↦ M ∈ U),
        ∑ q ∈ pairProfiles U,
          ∑ _xy ∈ unequalStatePairs,
            (1 / (9 * (M : ℝ))) *
              (Erdos697.Bernoulli.weight (lowerRegion I M)
                  (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
              (1 / (3 : ℝ) ^ t) := by
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro xy hxy
      exact highExtensionFibre_le hIpos hM
        (Finset.mem_filter.mp hU).1 (Finset.mem_filter.mp hxy).2
    _ = (6 : ℝ) * (1 / (9 * (M : ℝ))) *
        (∑ U ∈ (lowerRegion I M).powerset.filter (fun U ↦ M ∈ U),
          ∑ _q ∈ pairProfiles U,
            Erdos697.Bernoulli.weight (lowerRegion I M)
                (fun i ↦ 1 / (i : ℝ)) U / (9 : ℝ) ^ U.card) *
        (1 / (3 : ℝ) ^ t) := by
      simp only [Finset.sum_const, nsmul_eq_mul, unequalStatePairs_card]
      push_cast
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ = (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) *
        (1 / (3 : ℝ) ^ t) := by
      rw [sum_normalized_pairProfiles_containing_eq hMLower]
      ring

theorem highReindexMass_two_mul_sub_le
    {I : Finset ℕ} {M k : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i) (hMI : M ∈ I) :
    highReindexMass I M (2 * k - 1) ≤
      2 * (9 : ℝ) ^ (-(k : ℤ)) * (1 / (M : ℝ) ^ 2) := by
  have hbase := highReindexMass_le (t := 2 * k - 1) hIpos hMI
  have hdiag := diagonal_factor_le (q := 2 * k - 1) (k := k) (by omega)
  have hrecip : 0 ≤ 1 / (M : ℝ) ^ 2 := by positivity
  calc
    highReindexMass I M (2 * k - 1) ≤
        (2 / 3 : ℝ) * (1 / (M : ℝ) ^ 2) *
          (1 / (3 : ℝ) ^ (2 * k - 1)) := hbase
    _ = ((2 / 3 : ℝ) *
          (1 / (3 : ℝ) ^ (2 * k - 1))) *
          (1 / (M : ℝ) ^ 2) := by ring
    _ ≤ (2 * (1 / (9 : ℝ) ^ k)) *
          (1 / (M : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hdiag hrecip
    _ = 2 * (9 : ℝ) ^ (-(k : ℤ)) *
          (1 / (M : ℝ) ^ 2) := by
      rw [zpow_neg, zpow_natCast]
      ring

theorem sum_lowReindexMass_octave_le
    {I : Finset ℕ} {D r : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i)
    (hsub : octave D r ⊆ I) :
    (∑ M ∈ octave D r, lowReindexMass I M) ≤
      lowContribution D r := by
  unfold lowContribution
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  exact lowReindexMass_le hIpos (hsub hM)

theorem sum_highReindexMass_octave_le
    {I : Finset ℕ} {D s k : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i)
    (hsub : octave D (s + k) ⊆ I) :
    (∑ M ∈ octave D (s + k),
      highReindexMass I M (2 * k - 1)) ≤
      highContribution D s k := by
  unfold highContribution
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  exact highReindexMass_two_mul_sub_le hIpos (hsub hM)

/-- Once every collision witness has been put into its canonical low or
high separated code, the explicit octave decomposition follows formally. -/
theorem normalizedOffDiagonalExpectation_le_concrete_of_reindex
    {I : Finset ℕ} {D R s : ℕ}
    (hIpos : ∀ i ∈ I, 0 < i)
    (hlowSub : ∀ r < s, octave D r ⊆ I)
    (hhighSub : ∀ k < R - s, octave D (s + k) ⊆ I)
    (hreindex :
      normalizedOffDiagonalExpectation I (OctaveRegular D R s) ≤
        (∑ r ∈ Finset.range s,
          ∑ M ∈ octave D r, lowReindexMass I M) +
        ∑ k ∈ Finset.range (R - s),
          ∑ M ∈ octave D (s + k),
            highReindexMass I M (2 * k - 1)) :
    normalizedOffDiagonalExpectation I (OctaveRegular D R s) ≤
      (∑ r ∈ Finset.range s, lowContribution D r) +
        ∑ k ∈ Finset.range (R - s), highContribution D s k := by
  refine hreindex.trans (add_le_add ?_ ?_)
  · apply Finset.sum_le_sum
    intro r hr
    exact sum_lowReindexMass_octave_le hIpos
      (hlowSub r (Finset.mem_range.mp hr))
  · apply Finset.sum_le_sum
    intro k hk
    exact sum_highReindexMass_octave_le hIpos
      (hhighSub k (Finset.mem_range.mp hk))

/-- The complete numerical `1200·8^s/D` bound, conditional only on the
finite witness-to-code reindexing inequality displayed above. -/
theorem normalizedOffDiagonalExpectation_le_1200_of_reindex
    {I : Finset ℕ} {D R s : ℕ} (hD : 0 < D)
    (hIpos : ∀ i ∈ I, 0 < i)
    (hlowSub : ∀ r < s, octave D r ⊆ I)
    (hhighSub : ∀ k < R - s, octave D (s + k) ⊆ I)
    (hreindex :
      normalizedOffDiagonalExpectation I (OctaveRegular D R s) ≤
        (∑ r ∈ Finset.range s,
          ∑ M ∈ octave D r, lowReindexMass I M) +
        ∑ k ∈ Finset.range (R - s),
          ∑ M ∈ octave D (s + k),
            highReindexMass I M (2 * k - 1)) :
    normalizedOffDiagonalExpectation I (OctaveRegular D R s) ≤
      1200 * (8 : ℝ) ^ s / D := by
  apply normalizedOffDiagonalExpectation_le_of_concrete_decomposition
    (N := R - s) hD
  exact normalizedOffDiagonalExpectation_le_concrete_of_reindex
    hIpos hlowSub hhighSub hreindex

/-! ## Injective deletion of the forced coordinate -/

/-- Restrict a state to a selected set with one coordinate erased. -/
def eraseProfile {S : Finset ℕ} (n : ℕ) (a : ↑S → Fin 3) :
    ↑(S.erase n) → Fin 3 :=
  fun i ↦ a ⟨i.1, Finset.mem_of_mem_erase i.2⟩

/-- A state on `S` is equivalently its restriction away from `n` and its
value at `n`. -/
def eraseProfileEquiv (S : Finset ℕ) (n : ℕ) (hn : n ∈ S) :
    (↑S → Fin 3) ≃ ((↑(S.erase n) → Fin 3) × Fin 3) where
  toFun a := ⟨eraseProfile n a, a ⟨n, hn⟩⟩
  invFun q := fun i ↦
    if hi : i.1 = n then q.2
    else q.1 ⟨i.1, Finset.mem_erase.mpr ⟨hi, i.2⟩⟩
  left_inv a := by
    funext i
    by_cases hi : i.1 = n
    · have hieq : i = ⟨n, hn⟩ := Subtype.ext hi
      subst i
      simp
    · simp [hi, eraseProfile]
  right_inv q := by
    apply Prod.ext
    · funext i
      have hi : i.1 ≠ n := (Finset.mem_erase.mp i.2).1
      simp [eraseProfile, hi]
    · simp

/-- Deleting one coordinate from both ordered states and retaining their two
local values is injective. -/
theorem eraseProfile_pair_injective
    {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) :
    Function.Injective (fun q : (↑S → Fin 3) × (↑S → Fin 3) ↦
      ((eraseProfile n q.1, eraseProfile n q.2),
        (q.1 ⟨n, hn⟩, q.2 ⟨n, hn⟩))) := by
  intro q q' h
  have hleft :
      (eraseProfileEquiv S n hn) q.1 =
        (eraseProfileEquiv S n hn) q'.1 := by
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) h
    · exact congrArg (fun z ↦ z.2.1) h
  have hright :
      (eraseProfileEquiv S n hn) q.2 =
        (eraseProfileEquiv S n hn) q'.2 := by
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.2) h
    · exact congrArg (fun z ↦ z.2.2) h
  exact Prod.ext
    ((eraseProfileEquiv S n hn).injective hleft)
    ((eraseProfileEquiv S n hn).injective hright)

theorem signedValue_eraseProfile_add
    {S : Finset ℕ} {n : ℕ} (hn : n ∈ S)
    (a : ↑S → Fin 3) :
    signedValue (S.erase n) (eraseProfile n a) +
        signedTerm n (a ⟨n, hn⟩) = signedValue S a := by
  let N : ↑S := ⟨n, hn⟩
  let e : ↑(S.erase n) ≃ {i : ↑S // i ≠ N} :=
    { toFun := fun i ↦ ⟨⟨i.1, Finset.mem_of_mem_erase i.2⟩, by
          intro h
          exact (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val h)⟩
      invFun := fun i ↦ ⟨i.1.1, Finset.mem_erase.mpr ⟨by
          intro h
          apply i.2
          exact Subtype.ext h, i.1.2⟩⟩
      left_inv := fun i ↦ Subtype.ext rfl
      right_inv := fun i ↦ Subtype.ext (Subtype.ext rfl) }
  have heq :
      (∑ i : ↑(S.erase n), signedTerm i.1 ((eraseProfile n a) i)) =
        ∑ i : {i : ↑S // i ≠ N}, signedTerm i.1.1 (a i.1) := by
    apply Fintype.sum_equiv e
    intro i
    rfl
  unfold signedValue
  rw [heq]
  have hsub :
      (∑ i : {i : ↑S // i ≠ N}, signedTerm i.1.1 (a i.1)) =
        ∑ i ∈ (Finset.univ : Finset ↑S).erase N,
          signedTerm i.1 (a i) := by
    symm
    exact Finset.sum_subtype ((Finset.univ : Finset ↑S).erase N)
      (fun i ↦ by simp [N]) (fun i ↦ signedTerm i.1 (a i))
  rw [hsub]
  exact Finset.sum_erase_add (Finset.univ : Finset ↑S)
    (fun i ↦ signedTerm i.1 (a i)) (Finset.mem_univ N)

theorem profileDifference_erase_add
    {S : Finset ℕ} {n : ℕ} (hn : n ∈ S)
    (a b : ↑S → Fin 3) :
    profileDifference (eraseProfile n a, eraseProfile n b) +
        (signedTerm n (a ⟨n, hn⟩) - signedTerm n (b ⟨n, hn⟩)) =
      signedValue S a - signedValue S b := by
  unfold profileDifference
  rw [Finset.sum_sub_distrib]
  change (signedValue (S.erase n) (eraseProfile n a) -
      signedValue (S.erase n) (eraseProfile n b)) + _ = _
  rw [← signedValue_eraseProfile_add hn a,
    ← signedValue_eraseProfile_add hn b]
  ring

/-- Non-dependent payload of a canonical low-octave code after its erased
selected set has been fixed. -/
structure LowDatum (I T : Finset ℕ) where
  profile : (↑T → Fin 3) × (↑T → Fin 3)
  localPair : Fin 3 × Fin 3
  forced : ↑I
deriving DecidableEq, Fintype

def lowDatumEquiv (I T : Finset ℕ) :
    LowDatum I T ≃
      ((↑T → Fin 3) × (↑T → Fin 3)) × (Fin 3 × Fin 3) × ↑I where
  toFun d := (d.profile, d.localPair, d.forced)
  invFun d := ⟨d.1, d.2.1, d.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

/-- Canonical low code: predecessor, erased selected set, erased ordered
profile, unequal local pair, and forced coordinate. -/
abbrev LowCode (I : Finset ℕ) :=
  Σ _M : ↑I, Σ T : {T : Finset ℕ // T ∈ I.powerset}, LowDatum I T.1

def LowCode.Valid {I : Finset ℕ} (c : LowCode I) : Prop :=
  c.1.1 ∈ c.2.1.1 ∧
    c.2.2.localPair ∈ unequalStatePairs ∧
    c.2.2.forced.1 ∈
      forcedExtensions I c.1.1 c.2.1.1 c.2.2.profile c.2.2.localPair

def lowCodes (I : Finset ℕ) : Finset (LowCode I) :=
  Finset.univ.filter LowCode.Valid

def lowCodeMass {I : Finset ℕ} (c : LowCode I) : ℝ :=
  (1 / (9 * ((c.2.2.forced.1 : ℝ) - 1))) *
    (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) c.2.1.1 /
      (9 : ℝ) ^ c.2.1.1.card)

def extendProfile (T : Finset ℕ) (a : ↑T → Fin 3) : ℕ → Fin 3 :=
  fun n ↦ if hn : n ∈ T then a ⟨n, hn⟩ else 0

theorem extendProfile_injective (T : Finset ℕ) :
    Function.Injective (extendProfile T) := by
  intro a b h
  funext i
  have hi := congrFun h i.1
  simpa [extendProfile, i.2] using hi

def lowCodeStateData {I : Finset ℕ} (c : LowCode I) :
    (ℕ → Fin 3) × (ℕ → Fin 3) × (Fin 3 × Fin 3) :=
  (extendProfile c.2.1.1 c.2.2.profile.1,
    extendProfile c.2.1.1 c.2.2.profile.2,
    c.2.2.localPair)

/-- Canonical deletion code attached to one ordered collision witness. -/
def witnessLowCode
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i)
    (w : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S})
    (hw : w ∈ eventCollisionWitnesses I Good) : LowCode I := by
  let a := collisionWitnessLeft w.2.val
  let b := collisionWitnessRight w.2.val
  have hab : a ≠ b := collisionWitnessLeft_ne_right w.2.val
  have hbal : signedValue w.1 a = signedValue w.1 b :=
    collisionWitness_signedValue_eq w.2.val
  have hsub : w.1 ⊆ I := eventCollisionWitness_set_subset hw
  have hpos : ∀ n ∈ w.1, 0 < n := fun n hn ↦ hIpos n (hsub hn)
  let L := largestDifferingCoordinate a b hab
  let M := precedingSelectedCoordinate hab hbal hpos
  have hLI : L.1 ∈ I := hsub L.2
  have hMI : M.1 ∈ I := hsub M.2
  have hTsub : w.1.erase L.1 ⊆ I :=
    (Finset.erase_subset _ _).trans hsub
  exact ⟨⟨M.1, hMI⟩,
    ⟨⟨w.1.erase L.1, Finset.mem_powerset.mpr hTsub⟩,
      { profile := (eraseProfile L.1 a, eraseProfile L.1 b)
        localPair := (a L, b L)
        forced := ⟨L.1, hLI⟩ }⟩⟩

theorem witnessLowCode_valid
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i)
    (w : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S})
    (hw : w ∈ eventCollisionWitnesses I Good) :
    (witnessLowCode hIpos w hw).Valid := by
  let a := collisionWitnessLeft w.2.val
  let b := collisionWitnessRight w.2.val
  have hab : a ≠ b := collisionWitnessLeft_ne_right w.2.val
  have hbal : signedValue w.1 a = signedValue w.1 b :=
    collisionWitness_signedValue_eq w.2.val
  have hsub : w.1 ⊆ I := eventCollisionWitness_set_subset hw
  have hpos : ∀ n ∈ w.1, 0 < n := fun n hn ↦ hIpos n (hsub hn)
  let L := largestDifferingCoordinate a b hab
  let M := precedingSelectedCoordinate hab hbal hpos
  have hML : M < L := precedingSelectedCoordinate_lt_largest hab hbal hpos
  have hMne : M.1 ≠ L.1 := ne_of_lt hML
  have hlocal : a L ≠ b L := largestDifferingCoordinate_ne hab
  have hdiff := profileDifference_erase_add L.2 a b
  have hzero : signedValue w.1 a - signedValue w.1 b = 0 := sub_eq_zero.mpr hbal
  dsimp [witnessLowCode, LowCode.Valid]
  refine ⟨Finset.mem_erase.mpr ⟨hMne, M.2⟩, ?_, ?_⟩
  · simpa [unequalStatePairs] using hlocal
  · simp only [forcedExtensions, Finset.mem_filter]
    refine ⟨hsub L.2, hML, by simp, ?_⟩
    dsimp [L, M] at hdiff ⊢
    linarith

theorem witness_mass_eq_lowCodeMass
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i)
    (w : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S})
    (hw : w ∈ eventCollisionWitnesses I Good) :
    Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
        (9 : ℝ) ^ w.1.card =
      lowCodeMass (witnessLowCode hIpos w hw) := by
  let a := collisionWitnessLeft w.2.val
  let b := collisionWitnessRight w.2.val
  have hab : a ≠ b := collisionWitnessLeft_ne_right w.2.val
  have hbal : signedValue w.1 a = signedValue w.1 b :=
    collisionWitness_signedValue_eq w.2.val
  have hsub : w.1 ⊆ I := eventCollisionWitness_set_subset hw
  have hpos : ∀ n ∈ w.1, 0 < n := fun n hn ↦ hIpos n (hsub hn)
  let L := largestDifferingCoordinate a b hab
  let M := precedingSelectedCoordinate hab hbal hpos
  have hML : M < L := precedingSelectedCoordinate_lt_largest hab hbal hpos
  have hLtwo : 1 < L.1 := lt_of_le_of_lt (hpos M.1 M.2) hML
  dsimp [lowCodeMass, witnessLowCode]
  exact harmonic_normalized_weight_eq_erase (hsub L.2) L.2 hLtwo

theorem witnessLowCode_injective
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i)
    (w₁ w₂ : Σ S : Finset ℕ, {u // u ∈ orderedCollisionWitnesses S})
    (hw₁ : w₁ ∈ eventCollisionWitnesses I Good)
    (hw₂ : w₂ ∈ eventCollisionWitnesses I Good)
    (hcode : witnessLowCode hIpos w₁ hw₁ =
      witnessLowCode hIpos w₂ hw₂) :
    w₁ = w₂ := by
  let a₁ := collisionWitnessLeft w₁.2.val
  let b₁ := collisionWitnessRight w₁.2.val
  let a₂ := collisionWitnessLeft w₂.2.val
  let b₂ := collisionWitnessRight w₂.2.val
  have hab₁ : a₁ ≠ b₁ := collisionWitnessLeft_ne_right w₁.2.val
  have hab₂ : a₂ ≠ b₂ := collisionWitnessLeft_ne_right w₂.2.val
  have hbal₁ : signedValue w₁.1 a₁ = signedValue w₁.1 b₁ :=
    collisionWitness_signedValue_eq w₁.2.val
  have hbal₂ : signedValue w₂.1 a₂ = signedValue w₂.1 b₂ :=
    collisionWitness_signedValue_eq w₂.2.val
  have hsub₁ : w₁.1 ⊆ I := eventCollisionWitness_set_subset hw₁
  have hsub₂ : w₂.1 ⊆ I := eventCollisionWitness_set_subset hw₂
  have hpos₁ : ∀ n ∈ w₁.1, 0 < n := fun n hn ↦ hIpos n (hsub₁ hn)
  have hpos₂ : ∀ n ∈ w₂.1, 0 < n := fun n hn ↦ hIpos n (hsub₂ hn)
  let L₁ := largestDifferingCoordinate a₁ b₁ hab₁
  let L₂ := largestDifferingCoordinate a₂ b₂ hab₂
  have hn : L₁.1 = L₂.1 := by
    exact congrArg (fun c : LowCode I ↦ c.2.2.forced.1) hcode
  have hT : w₁.1.erase L₁.1 = w₂.1.erase L₂.1 := by
    exact congrArg (fun c : LowCode I ↦ c.2.1.1) hcode
  have hS : w₁.1 = w₂.1 := by
    have hT' : w₁.1.erase L₂.1 = w₂.1.erase L₂.1 := by
      simpa only [hn] using hT
    calc
      w₁.1 = insert L₁.1 (w₁.1.erase L₁.1) :=
        (Finset.insert_erase L₁.2).symm
      _ = insert L₂.1 (w₁.1.erase L₂.1) := by rw [hn]
      _ = insert L₂.1 (w₂.1.erase L₂.1) := by rw [hT']
      _ = w₂.1 := Finset.insert_erase L₂.2
  rcases w₁ with ⟨S₁, u₁⟩
  rcases w₂ with ⟨S₂, u₂⟩
  dsimp at hS
  subst S₂
  have hL : L₁ = L₂ := Subtype.ext hn
  subst L₂
  have hdata :
      lowCodeStateData (witnessLowCode hIpos ⟨S₁, u₁⟩ hw₁) =
        lowCodeStateData (witnessLowCode hIpos ⟨S₁, u₂⟩ hw₂) :=
    congrArg lowCodeStateData hcode
  have heraseA : eraseProfile L₁.1 a₁ = eraseProfile L₁.1 a₂ := by
    apply extendProfile_injective (S₁.erase L₁.1)
    have hd := congrArg (fun z ↦ z.1) hdata
    simp only [lowCodeStateData, witnessLowCode] at hd
    rw [← hL] at hd
    exact hd
  have heraseB : eraseProfile L₁.1 b₁ = eraseProfile L₁.1 b₂ := by
    apply extendProfile_injective (S₁.erase L₁.1)
    have hd := congrArg (fun z ↦ z.2.1) hdata
    simp only [lowCodeStateData, witnessLowCode] at hd
    rw [← hL] at hd
    exact hd
  have hlocal : (a₁ L₁, b₁ L₁) = (a₂ L₁, b₂ L₁) := by
    have hd := congrArg (fun z ↦ z.2.2) hdata
    simp only [lowCodeStateData, witnessLowCode] at hd
    rw [← hL] at hd
    exact hd
  have hpair :
      ((eraseProfile L₁.1 a₁, eraseProfile L₁.1 b₁),
        (a₁ L₁, b₁ L₁)) =
      ((eraseProfile L₁.1 a₂, eraseProfile L₁.1 b₂),
        (a₂ L₁, b₂ L₁)) := by
    exact Prod.ext (Prod.ext heraseA heraseB) hlocal
  have habpair : (a₁, b₁) = (a₂, b₂) :=
    eraseProfile_pair_injective L₁.2 hpair
  have ha : a₁ = a₂ := congrArg Prod.fst habpair
  have hb : b₁ = b₂ := congrArg Prod.snd habpair
  have huval : u₁.val = u₂.val := collisionWitness_ext u₁.val u₂.val ha hb
  have hu : u₁ = u₂ := Subtype.ext huval
  exact congrArg (fun u ↦ Sigma.mk S₁ u) hu

def witnessLowCodeImage
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i) : Finset (LowCode I) :=
  (eventCollisionWitnesses I Good).attach.image fun w ↦
    witnessLowCode hIpos w.1 w.2

theorem witnessLowCodeImage_subset
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i) :
    witnessLowCodeImage (Good := Good) hIpos ⊆ lowCodes I := by
  intro c hc
  rw [witnessLowCodeImage, Finset.mem_image] at hc
  rcases hc with ⟨w, hw, rfl⟩
  rw [lowCodes, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, witnessLowCode_valid hIpos w.1 w.2⟩

theorem lowCodeMass_nonneg
    {I : Finset ℕ} (hIpos : ∀ i ∈ I, 0 < i)
    {c : LowCode I} (hc : c.Valid) : 0 ≤ lowCodeMass c := by
  rcases hc with ⟨hM, hxy, hn⟩
  have hTsub : c.2.1.1 ⊆ I := Finset.mem_powerset.mp c.2.1.2
  have hMpos : 0 < c.1.1 := hIpos c.1.1 (hTsub hM)
  have hMn : c.1.1 < c.2.2.forced.1 := (Finset.mem_filter.mp hn).2.1
  have hnR : (1 : ℝ) < c.2.2.forced.1 := by
    exact_mod_cast (lt_of_le_of_lt hMpos hMn)
  unfold lowCodeMass
  apply mul_nonneg
  · positivity
  · apply div_nonneg
    · apply Erdos697.Bernoulli.weight_nonneg
      · intro i hi
        positivity
      · intro i hi
        have hip := hIpos i hi
        exact (div_le_one (by exact_mod_cast hip)).2 (by exact_mod_cast hip)
      · exact c.2.1.2
    · positivity

theorem witness_sum_eq_lowCodeImage_sum
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i) :
    (∑ w ∈ eventCollisionWitnesses I Good,
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
        (9 : ℝ) ^ w.1.card) =
      ∑ c ∈ witnessLowCodeImage (Good := Good) hIpos, lowCodeMass c := by
  rw [witnessLowCodeImage, Finset.sum_image]
  · calc
      (∑ w ∈ eventCollisionWitnesses I Good,
        Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
          (9 : ℝ) ^ w.1.card) =
          ∑ w ∈ (eventCollisionWitnesses I Good).attach,
            Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1.1 /
              (9 : ℝ) ^ w.1.1.card :=
        (Finset.sum_attach _ _).symm
      _ = ∑ w ∈ (eventCollisionWitnesses I Good).attach,
            lowCodeMass (witnessLowCode hIpos w.1 w.2) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact witness_mass_eq_lowCodeMass hIpos w.1 w.2
  · intro w₁ hw₁ w₂ hw₂ h
    apply Subtype.ext
    exact witnessLowCode_injective hIpos w₁.1 w₂.1 w₁.2 w₂.2 h

theorem witness_sum_le_lowCodes_sum
    {I : Finset ℕ} {Good : Finset ℕ → Prop} [DecidablePred Good]
    (hIpos : ∀ i ∈ I, 0 < i) :
    (∑ w ∈ eventCollisionWitnesses I Good,
      Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) w.1 /
        (9 : ℝ) ^ w.1.card) ≤
      ∑ c ∈ lowCodes I, lowCodeMass c := by
  rw [witness_sum_eq_lowCodeImage_sum hIpos]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact witnessLowCodeImage_subset hIpos
  · intro c hc hnot
    exact lowCodeMass_nonneg hIpos (Finset.mem_filter.mp hc).2

theorem sum_lowCodeMass_eq (I : Finset ℕ) :
    (∑ c ∈ lowCodes I, lowCodeMass c) =
      ∑ M ∈ I, lowReindexMass I M := by
  rw [lowCodes, Finset.sum_filter]
  change (∑ c : LowCode I, if c.Valid then lowCodeMass c else 0) = _
  rw [Fintype.sum_sigma]
  calc
    (∑ M : ↑I,
      ∑ y, if LowCode.Valid ⟨M, y⟩ then lowCodeMass ⟨M, y⟩ else 0) =
        ∑ M : ↑I, lowReindexMass I M.1 := by
      apply Fintype.sum_congr
      intro M
      rw [Fintype.sum_sigma]
      unfold lowReindexMass
      rw [Finset.sum_filter]
      calc
        (∑ T : {T : Finset ℕ // T ∈ I.powerset},
          ∑ d, if LowCode.Valid ⟨M, T, d⟩ then
            lowCodeMass ⟨M, T, d⟩ else 0) =
            ∑ T ∈ I.powerset,
              if M.1 ∈ T then
                ∑ q ∈ pairProfiles T,
                  ∑ xy ∈ unequalStatePairs,
                    (∑ n ∈ forcedExtensions I M.1 T q xy,
                      1 / (9 * ((n : ℝ) - 1))) *
                    (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
                      (9 : ℝ) ^ T.card)
              else 0 := by
          symm
          calc
            (∑ T ∈ I.powerset,
              if M.1 ∈ T then
                ∑ q ∈ pairProfiles T,
                  ∑ xy ∈ unequalStatePairs,
                    (∑ n ∈ forcedExtensions I M.1 T q xy,
                      1 / (9 * ((n : ℝ) - 1))) *
                    (Erdos697.Bernoulli.weight I (fun i ↦ 1 / (i : ℝ)) T /
                      (9 : ℝ) ^ T.card)
              else 0) =
                ∑ T : {T : Finset ℕ // T ∈ I.powerset},
                  if M.1 ∈ T.1 then
                    ∑ q ∈ pairProfiles T.1,
                      ∑ xy ∈ unequalStatePairs,
                        (∑ n ∈ forcedExtensions I M.1 T.1 q xy,
                          1 / (9 * ((n : ℝ) - 1))) *
                        (Erdos697.Bernoulli.weight I
                          (fun i ↦ 1 / (i : ℝ)) T.1 / (9 : ℝ) ^ T.1.card)
                  else 0 :=
              Finset.sum_subtype I.powerset (fun _ ↦ Iff.rfl) _
            _ = ∑ T : {T : Finset ℕ // T ∈ I.powerset},
                ∑ d, if LowCode.Valid ⟨M, T, d⟩ then
                  lowCodeMass ⟨M, T, d⟩ else 0 := by
              apply Fintype.sum_congr
              intro T
              have hequiv :
                  (∑ d : LowDatum I T,
                    if LowCode.Valid ⟨M, T, d⟩ then
                      lowCodeMass ⟨M, T, d⟩ else 0) =
                    ∑ z : ((↑T → Fin 3) × (↑T → Fin 3)) ×
                        (Fin 3 × Fin 3) × ↑I,
                      if LowCode.Valid ⟨M, T,
                        ⟨z.1, z.2.1, z.2.2⟩⟩ then
                        lowCodeMass ⟨M, T, ⟨z.1, z.2.1, z.2.2⟩⟩ else 0 := by
                apply Fintype.sum_equiv (lowDatumEquiv I T)
                intro d
                rfl
              rw [hequiv]
              rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
              by_cases hMT : M.1 ∈ T.1
              · simp only [LowCode.Valid, lowCodeMass, pairProfiles,
                  unequalStatePairs, forcedExtensions, hMT, true_and,
                  Finset.mem_univ, Finset.sum_filter]
                rw [Fintype.sum_prod_type]
                apply Fintype.sum_congr
                intro a
                apply Fintype.sum_congr
                intro b
                rw [Fintype.sum_prod_type]
                simp only [Finset.sum_mul]
                apply Fintype.sum_congr
                intro xy
                by_cases hxy : xy.1 = xy.2
                · simp [hxy]
                · simpa [hxy] using
                    (Finset.sum_attach I (fun x : ℕ ↦
                      if M.1 < x ∧ x ∉ T.1 ∧
                          signedTerm x xy.1 - signedTerm x xy.2 =
                            -profileDifference (a, b) then
                        ((x : ℝ) - 1)⁻¹ * 9⁻¹ *
                          (Erdos697.Bernoulli.weight I
                              (fun i ↦ (i : ℝ)⁻¹) T.1 /
                            9 ^ T.1.card)
                      else 0)).symm
              · simp [LowCode.Valid, hMT]
    _ = ∑ M ∈ I, lowReindexMass I M := by
      symm
      exact Finset.sum_subtype I (fun _ ↦ Iff.rfl) _

end

end Erdos144.HarmonicReindex
