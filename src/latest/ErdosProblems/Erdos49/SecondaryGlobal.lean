import ErdosProblems.Erdos49.SecondaryArithmetic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Dyadic summation for the secondary set

This file chooses the two additive bucket widths used by the local secondary
packing theorem and sums the resulting estimate over the chosen denominator
and the dyadic prime and integer bands.
-/

open scoped BigOperators

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

def secondaryT (H : ℕ) : ℕ := H ^ 6

def secondaryV (H P : ℕ) : ℕ := P / secondaryT H

def secondaryU (H P X : ℕ) : ℕ :=
  X / (64 * P * secondaryT H)

def secondaryBand (N L : ℕ) (A : Finset ℕ) (d i j : ℕ) : Finset ℕ :=
  A.filter fun n ↦ secondaryD N L n = d ∧
    (secondaryP N L n).log2 = i ∧ n.log2 = j

@[simp] lemma mem_secondaryBand {N L : ℕ} {A : Finset ℕ} {d i j n : ℕ} :
    n ∈ secondaryBand N L A d i j ↔
      n ∈ A ∧ secondaryD N L n = d ∧
        (secondaryP N L n).log2 = i ∧ n.log2 = j := by
  simp [secondaryBand, and_assoc]

lemma dyadic_bounds {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.log2 ≤ n ∧ n < 2 * 2 ^ n.log2 := by
  exact ⟨Nat.log2_self_le hn, by
    simpa [pow_succ, mul_comm] using Nat.lt_log2_self (n := n)⟩

lemma secondaryBand_subset {N L : ℕ} {A : Finset ℕ} {d i j : ℕ} :
    secondaryBand N L A d i j ⊆ A := by
  intro n hn
  exact (mem_secondaryBand.mp hn).1

lemma secondaryBand_mono {N L : ℕ} {A : Finset ℕ} {d i j : ℕ}
    (hmono : TotientMonotoneOn A) :
    TotientMonotoneOn (secondaryBand N L A d i j) :=
  hmono.mono secondaryBand_subset

/-- A member of one dyadic secondary band satisfies all the hypotheses of the
local structured packing theorem. -/
lemma secondaryBand_data
    {N L H : ℕ} {A : Finset ℕ} (hAsec : A ⊆ secondarySet N L)
    {d i j : ℕ} :
    let B := secondaryBand N L A d i j
    let P := 2 ^ i
    let X := 2 ^ j
    (B ⊆ secondarySet N L) ∧
      (∀ n ∈ B, secondaryD N L n = d) ∧
      (∀ n ∈ B, P ≤ secondaryP N L n ∧ secondaryP N L n ≤ 2 * P) ∧
      (∀ n ∈ B, X ≤ n ∧ n ≤ 2 * X) := by
  dsimp only
  constructor
  · exact secondaryBand_subset.trans hAsec
  constructor
  · intro n hn
    exact (mem_secondaryBand.mp hn).2.1
  constructor
  · intro n hn
    have hmem := mem_secondaryBand.mp hn
    have hpPrime := (secondaryWitness_spec (hAsec hmem.1)).2.1
    have hb := dyadic_bounds hpPrime.ne_zero
    rw [hmem.2.2.1] at hb
    exact ⟨hb.1, hb.2.le⟩
  · intro n hn
    have hmem := mem_secondaryBand.mp hn
    have hnPos := (mem_secondarySet.mp (hAsec hmem.1)).1
    have hb := dyadic_bounds (Nat.ne_of_gt hnPos)
    rw [hmem.2.2.2] at hb
    exact ⟨hb.1, hb.2.le⟩

/-- The factor separation in a secondary representation forces a useful
upper bound for the square of the dyadic prime scale. -/
lemma secondaryBand_square_scale
    {N L : ℕ} {A : Finset ℕ} (hAsec : A ⊆ secondarySet N L)
    {d i j n : ℕ} (hn : n ∈ secondaryBand N L A d i j) :
    d * (2 ^ i) ^ 2 * L < 2 * 2 ^ j := by
  have hmem := mem_secondaryBand.mp hn
  have hr := secondaryWitness_spec (hAsec hmem.1)
  have hd : secondaryD N L n = d := hmem.2.1
  have hpLog : (secondaryP N L n).log2 = i := hmem.2.2.1
  have hnLog : n.log2 = j := hmem.2.2.2
  have hpLow : 2 ^ i ≤ secondaryP N L n := by
    rw [← hpLog]
    exact Nat.log2_self_le hr.2.1.ne_zero
  have hsLarge : secondaryP N L n * L < secondaryS N L n :=
    hr.2.2.2.2.1
  have hfac : n = secondaryD N L n * secondaryP N L n * secondaryS N L n :=
    hr.2.2.2.2.2.2.2.2.2.1
  have hnUpper : n < 2 * 2 ^ j := by
    rw [← hnLog]
    simpa [pow_succ, mul_comm] using Nat.lt_log2_self (n := n)
  rw [hd] at hfac
  calc
    d * (2 ^ i) ^ 2 * L ≤
        d * (secondaryP N L n) ^ 2 * L := by gcongr
    _ < d * secondaryP N L n * secondaryS N L n := by
      have hdPos : 0 < d := by
        rw [← hd]
        exact Nat.zero_lt_one.trans_le hr.1
      calc
        d * (secondaryP N L n) ^ 2 * L =
            (d * secondaryP N L n) * (secondaryP N L n * L) := by ring
        _ < (d * secondaryP N L n) * secondaryS N L n :=
          Nat.mul_lt_mul_of_pos_left hsLarge
            (Nat.mul_pos hdPos hr.2.1.pos)
    _ = n := hfac.symm
    _ < 2 * 2 ^ j := hnUpper

/-- The automatic additive widths satisfy the two numerical separation
conditions required by `secondary_cell_order`. -/
lemma secondary_bucket_scales
    {H P X L : ℕ} (hH : 2 ≤ H)
    (hPscale : 2 * secondaryT H ≤ P)
    (hXscale : 64 * P * secondaryT H ≤ X)
    (hLscale : 32 * secondaryT H < L) :
    0 < secondaryU H P X ∧ 0 < secondaryV H P ∧
      8 * P ^ 2 * secondaryU H P X < secondaryV H P * X ∧
      16 * P < secondaryV H P * L := by
  let T := secondaryT H
  let U := secondaryU H P X
  let V := secondaryV H P
  have hT : 0 < T := by simp [T, secondaryT]; positivity
  have hP : 0 < P := hT.trans_le (by omega)
  have hV : 0 < V := by
    dsimp only [V, secondaryV]
    exact Nat.div_pos (by omega) hT
  have hU : 0 < U := by
    dsimp only [U, secondaryU]
    exact Nat.div_pos hXscale (by positivity)
  have hPb := quotientBucket_bounds (W := T) (n := P) hT
  change P / T * T ≤ P ∧ P < P / T * T + T at hPb
  have hPtwo : P < 2 * V * T := by
    dsimp only [V, secondaryV]
    calc
      P < P / T * T + T := hPb.2
      _ ≤ 2 * (P / T) * T := by
        have : 1 ≤ P / T := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hV)
        nlinarith
  have hUb := quotientBucket_bounds (W := 64 * P * T) (n := X) (by positivity)
  change X / (64 * P * T) * (64 * P * T) ≤ X ∧
    X < X / (64 * P * T) * (64 * P * T) + 64 * P * T at hUb
  have hsmall : 16 * P * T * U < X := by
    have hstrict : 16 * P * T * U < 64 * P * T * U := by
      nlinarith
    have hle : 64 * P * T * U ≤ X := by
      dsimp only [U, secondaryU]
      nlinarith [hUb.1]
    exact hstrict.trans_le hle
  refine ⟨hU, hV, ?_, ?_⟩
  · have hmul := Nat.mul_lt_mul_of_pos_right (k := 8 * P * U) hPtwo
      (by positivity : 0 < 8 * P * U)
    have hsmallV := Nat.mul_lt_mul_of_pos_left (k := V) hsmall hV
    nlinarith
  · have hmul := Nat.mul_lt_mul_of_pos_left (k := 16) hPtwo (by omega)
    have hscale := Nat.mul_lt_mul_of_pos_left (k := V) hLscale hV
    nlinarith

/-- Raw local estimate for one dyadic band with the automatically chosen
bucket widths. -/
theorem secondaryBand_raw_bound
    {N L H : ℕ} {A : Finset ℕ}
    (hAsec : A ⊆ secondarySet N L) (hmono : TotientMonotoneOn A)
    (hH : 2 ≤ H) (hLscale : 32 * secondaryT H < L)
    {d i j : ℕ}
    (hPscale : 2 * secondaryT H ≤ 2 ^ i)
    (hXscale : 64 * (2 ^ i) * secondaryT H ≤ 2 ^ j) :
    let B := secondaryBand N L A d i j
    let P := 2 ^ i
    let X := 2 ^ j
    let U := secondaryU H P X
    let V := secondaryV H P
    (B.card : ℝ) ≤
      (V : ℝ) * (2 * (2 * X) : ℕ) / (d * P : ℕ) +
        ((((2 * X) / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) * (3 * V) := by
  dsimp only
  let B := secondaryBand N L A d i j
  by_cases hB : B.Nonempty
  · obtain ⟨n, hn⟩ := hB
    have hdata := secondaryBand_data (H := H) hAsec (d := d) (i := i) (j := j)
    have hd : 0 < d := by
      have hr := secondaryWitness_spec (hAsec (secondaryBand_subset hn))
      have hdeq := (mem_secondaryBand.mp hn).2.1
      rw [← hdeq]
      exact Nat.zero_lt_one.trans_le hr.1
    have hscales := secondary_bucket_scales hH hPscale hXscale hLscale
    have hbound := secondary_structured_band_bound
      (hAsec := hdata.1) (hmono := secondaryBand_mono hmono)
      (hd₀ := hd) (hP := by positivity) (hU := hscales.1)
      (hV := hscales.2.1) (hd := hdata.2.1)
      (hpBand := hdata.2.2.1) (hnBand := hdata.2.2.2)
      (houter := hscales.2.2.1) (hinner := hscales.2.2.2)
    exact hbound
  · change (B.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Elementary bounds for the two key-count factors in the raw band
estimate. -/
lemma secondary_bucket_count_bounds
    {H P X : ℕ} (hH : 2 ≤ H)
    (hPscale : 2 * secondaryT H ≤ P)
    (hXscale : 64 * P * secondaryT H ≤ X) :
    let T := secondaryT H
    let U := secondaryU H P X
    let V := secondaryV H P
    2 * X / U + 1 ≤ 257 * P * T ∧
      2 * P / V + 1 ≤ 5 * T ∧ V ≤ P := by
  dsimp only
  let T := secondaryT H
  let U := secondaryU H P X
  let V := secondaryV H P
  have hs := secondary_bucket_scales hH hPscale hXscale
    (L := 32 * T + 1) (by simp [T])
  have hU : 0 < U := hs.1
  have hV : 0 < V := hs.2.1
  have hT : 0 < T := by simp [T, secondaryT]; positivity
  have hP : 0 < P := hT.trans_le (by omega)
  have hUb := quotientBucket_bounds (W := 64 * P * T) (n := X) (by positivity)
  change X / (64 * P * T) * (64 * P * T) ≤ X ∧
    X < X / (64 * P * T) * (64 * P * T) + 64 * P * T at hUb
  have hXupper : X < 128 * P * T * U := by
    dsimp only [U, secondaryU]
    have hUone : 1 ≤ X / (64 * P * T) := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hU)
    calc
      X < X / (64 * P * T) * (64 * P * T) + 64 * P * T := hUb.2
      _ ≤ 2 * (X / (64 * P * T)) * (64 * P * T) := by nlinarith
      _ = 128 * P * T * (X / (64 * P * T)) := by ring
  have hOuter : 2 * X / U + 1 ≤ 257 * P * T := by
    have hmul : 2 * X ≤ (256 * P * T) * U := by nlinarith
    have hdiv : 2 * X / U ≤ 256 * P * T :=
      Nat.div_le_of_le_mul (by simpa [mul_comm] using hmul)
    have hPT : 1 ≤ P * T := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero hP.ne' hT.ne')
    calc
      2 * X / U + 1 ≤ 256 * P * T + 1 := Nat.add_le_add_right hdiv 1
      _ ≤ 257 * P * T := by nlinarith
  have hPb := quotientBucket_bounds (W := T) (n := P) hT
  change P / T * T ≤ P ∧ P < P / T * T + T at hPb
  have hPupper : P < 2 * V * T := by
    dsimp only [V, secondaryV]
    have hVone : 1 ≤ P / T := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hV)
    calc
      P < P / T * T + T := hPb.2
      _ ≤ 2 * (P / T) * T := by nlinarith
  have hInner : 2 * P / V + 1 ≤ 5 * T := by
    have hmul : 2 * P ≤ (4 * T) * V := by nlinarith
    have hdiv : 2 * P / V ≤ 4 * T :=
      Nat.div_le_of_le_mul (by simpa [mul_comm] using hmul)
    nlinarith
  have hVP : V ≤ P := by
    dsimp only [V, secondaryV]
    exact Nat.div_le_self P T
  exact ⟨hOuter, hInner, hVP⟩

/-- Uniform simplified estimate for a nonempty dyadic secondary band. -/
theorem secondaryBand_bound
    {N L H : ℕ} {A : Finset ℕ}
    (hAsec : A ⊆ secondarySet N L) (hmono : TotientMonotoneOn A)
    (hH : 2 ≤ H) (hLscale : 32 * secondaryT H < L)
    (hLT : secondaryT H ^ 3 ≤ L)
    {d i j : ℕ}
    (hPscale : 2 * secondaryT H ≤ 2 ^ i)
    (hXscale : 64 * (2 ^ i) * secondaryT H ≤ 2 ^ j) :
    ((secondaryBand N L A d i j).card : ℝ) ≤
      8000 * (2 ^ j : ℕ) / (d * secondaryT H : ℕ) := by
  let B := secondaryBand N L A d i j
  let T := secondaryT H
  let P := 2 ^ i
  let X := 2 ^ j
  let U := secondaryU H P X
  let V := secondaryV H P
  by_cases hB : B.Nonempty
  · obtain ⟨n, hn⟩ := hB
    have hd : 0 < d := by
      have hr := secondaryWitness_spec (hAsec (secondaryBand_subset hn))
      have hdeq := (mem_secondaryBand.mp hn).2.1
      rw [← hdeq]
      exact Nat.zero_lt_one.trans_le hr.1
    have hT : 0 < T := by simp [T, secondaryT]; positivity
    have hP : 0 < P := by positivity
    have hX : 0 < X := by positivity
    have hraw := secondaryBand_raw_bound hAsec hmono hH hLscale
      (d := d) (i := i) (j := j) hPscale hXscale
    have hcounts := secondary_bucket_count_bounds hH hPscale hXscale
    have hscales := secondary_bucket_scales hH hPscale hXscale hLscale
    have hU : 0 < U := hscales.1
    have hV : 0 < V := hscales.2.1
    have hVT : V * T ≤ P := by
      dsimp only [V, secondaryV]
      exact Nat.div_mul_le_self P T
    have hsq := secondaryBand_square_scale hAsec hn
    have hsqT : d * P ^ 2 * T ^ 3 < 2 * X := by
      have hmul : d * P ^ 2 * T ^ 3 ≤ d * P ^ 2 * L := by gcongr
      exact hmul.trans_lt (by simpa [P, X] using hsq)
    have htermOne :
        (V : ℝ) * (2 * (2 * X) : ℕ) / (d * P : ℕ) ≤
          4 * (X : ℝ) / (d * T : ℕ) := by
      apply (div_le_div_iff₀
        (by positivity : (0 : ℝ) < (d * P : ℕ))
        (by positivity : (0 : ℝ) < (d * T : ℕ))).2
      have hcross :
          V * (2 * (2 * X)) * (d * T) ≤ 4 * X * (d * P) := by
        calc
          V * (2 * (2 * X)) * (d * T) = (4 * X * d) * (V * T) := by ring
          _ ≤ (4 * X * d) * P := Nat.mul_le_mul_left _ hVT
          _ = 4 * X * (d * P) := by ring
      exact_mod_cast hcross
    have hOuter : 2 * X / U + 1 ≤ 257 * P * T := by
      simpa [T, P, X, U, V] using hcounts.1
    have hInner : 2 * P / V + 1 ≤ 5 * T := by
      simpa [T, P, X, U, V] using hcounts.2.1
    have hVP : V ≤ P := by
      simpa [T, P, X, U, V] using hcounts.2.2
    have hkeyNat :
        ((2 * X / U + 1) * (2 * P / V + 1)) * (3 * V) ≤
          3855 * P ^ 2 * T ^ 2 := by
      calc
        ((2 * X / U + 1) * (2 * P / V + 1)) * (3 * V) ≤
            ((257 * P * T) * (5 * T)) * (3 * P) := by gcongr
        _ = 3855 * P ^ 2 * T ^ 2 := by ring
    have hkeyReal :
        ((((2 * X) / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) * (3 * V) ≤
          7710 * (X : ℝ) / (d * T : ℕ) := by
      have hkeyCast :
          (((((2 * X) / U + 1) * (2 * P / V + 1)) * (3 * V) : ℕ) : ℝ) ≤
            (3855 * P ^ 2 * T ^ 2 : ℕ) := by exact_mod_cast hkeyNat
      have hden : (0 : ℝ) < (d * T : ℕ) := by positivity
      apply (le_div_iff₀ hden).2
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hkeyCast ⊢
      have hscaleNat :
          3855 * (d * P ^ 2 * T ^ 3) < 7710 * X := by
        have hm := Nat.mul_lt_mul_of_pos_left (k := 3855) hsqT (by omega)
        nlinarith
      have hscale :
          (3855 : ℝ) * ((d : ℝ) * P ^ 2 * T ^ 3) < 7710 * X := by
        exact_mod_cast hscaleNat
      have hkeyCast' :
          (((((2 * X / U + 1) * (2 * P / V + 1) : ℕ) : ℝ) *
              (3 * (V : ℝ)))) ≤ 3855 * (P : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
        norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hkeyCast ⊢
        exact hkeyCast
      calc
        (((2 * X / U + 1 : ℕ) : ℝ) * ((2 * P / V + 1 : ℕ) : ℝ) *
            (3 * (V : ℝ))) * ((d : ℝ) * (T : ℝ)) ≤
            (3855 * (P : ℝ) ^ 2 * (T : ℝ) ^ 2) * ((d : ℝ) * (T : ℝ)) :=
          mul_le_mul_of_nonneg_right (by
            simpa only [Nat.cast_mul] using hkeyCast') (by positivity)
        _ ≤ 7710 * (X : ℝ) := by nlinarith
    dsimp only [B, T, P, X, U, V] at hraw ⊢
    apply hraw.trans
    dsimp only [T, P, X, U, V] at htermOne hkeyReal ⊢
    calc
      _ ≤ 4 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) +
          7710 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) :=
        add_le_add htermOne hkeyReal
      _ ≤ 8000 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) := by
        have hden : (0 : ℝ) < (d * secondaryT H : ℕ) := by positivity
        have hx : 0 ≤ (((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ)) := by
          positivity
        calc
          4 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) +
              7710 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) =
                7714 * (((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ)) := by ring
          _ ≤ 8000 * (((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ)) := by
            gcongr <;> norm_num
          _ = 8000 * ((2 ^ j : ℕ) : ℝ) / (d * secondaryT H : ℕ) := by ring
  · change (B.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    positivity

#print axioms secondaryBand_bound

/-- For the global choice `L ≥ H^18`, every occupied secondary band is
automatically large enough for the local two-scale argument. -/
theorem secondaryBand_uniform_bound
    {N L H : ℕ} {A : Finset ℕ}
    (hAsec : A ⊆ secondarySet N L) (hmono : TotientMonotoneOn A)
    (hH : 2 ≤ H) (hLT : secondaryT H ^ 3 ≤ L)
    (d i j : ℕ) :
    ((secondaryBand N L A d i j).card : ℝ) ≤
      8000 * (2 ^ j : ℕ) / (d * secondaryT H : ℕ) := by
  let B := secondaryBand N L A d i j
  by_cases hB : B.Nonempty
  · obtain ⟨n, hn⟩ := hB
    have hmem := mem_secondaryBand.mp hn
    have hr := secondaryWitness_spec (hAsec hmem.1)
    let T := secondaryT H
    let P := 2 ^ i
    let X := 2 ^ j
    have hT : 64 ≤ T := by
      dsimp only [T, secondaryT]
      nlinarith [Nat.pow_le_pow_left hH 6]
    have h128 : 128 * T ≤ T ^ 3 := by
      have hsquare : 128 ≤ T * T := by nlinarith
      calc
        128 * T ≤ (T * T) * T := Nat.mul_le_mul_right T hsquare
        _ = T ^ 3 := by ring
    have hLlarge : 128 * T ≤ L := h128.trans hLT
    have hpUpper : secondaryP N L n < 2 * P := by
      have hb := (dyadic_bounds hr.2.1.ne_zero).2
      simpa [P, hmem.2.2.1] using hb
    have hPscale : 2 * T ≤ P := by
      have hpLarge : L < secondaryP N L n := hr.2.2.1
      nlinarith
    have hsq : d * P ^ 2 * L < 2 * X := by
      simpa [P, X] using secondaryBand_square_scale hAsec hn
    have hd : 1 ≤ d := by
      rw [← hmem.2.1]
      exact hr.1
    have hXscale : 64 * P * T ≤ X := by
      have hPL : 128 * P * T ≤ P ^ 2 * L := by
        calc
          128 * P * T = P * (128 * T) := by ring
          _ ≤ P * L := Nat.mul_le_mul_left P hLlarge
          _ ≤ P ^ 2 * L := by
            have hPone : 1 ≤ P := by
              dsimp only [P]
              exact Nat.one_le_pow i 2 (by omega)
            have hPP : P ≤ P ^ 2 := by
              calc
                P = P * 1 := by simp
                _ ≤ P * P := Nat.mul_le_mul_left P hPone
                _ = P ^ 2 := by ring
            exact Nat.mul_le_mul_right L hPP
      have hfull : 128 * P * T < 2 * X := by
        calc
          128 * P * T ≤ d * (128 * P * T) := by
            exact Nat.le_mul_of_pos_left _ hd
          _ ≤ d * (P ^ 2 * L) := Nat.mul_le_mul_left d hPL
          _ = d * P ^ 2 * L := by ring
          _ < 2 * X := hsq
      have htwice : 2 * (64 * P * T) < 2 * X := by
        calc
          2 * (64 * P * T) = 128 * P * T := by ring
          _ < 2 * X := hfull
      exact ((Nat.mul_lt_mul_left (by omega : 0 < 2)).mp htwice).le
    have hLscale : 32 * T < L := by omega
    apply secondaryBand_bound hAsec hmono hH
      (by simpa [T] using hLscale) hLT
      (by simpa [T, P] using hPscale)
      (by simpa [T, P, X] using hXscale)
  · change (B.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    positivity

def secondaryBandIndices (N : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N).product
    ((Finset.range (N.log2 + 1)).product (Finset.range (N.log2 + 1)))

lemma secondary_card_eq_sum_bands
    {N L : ℕ} {A : Finset ℕ} (hAsec : A ⊆ secondarySet N L) :
    A.card = ∑ z ∈ secondaryBandIndices N,
      (secondaryBand N L A z.1 z.2.1 z.2.2).card := by
  let f : ℕ → ℕ × (ℕ × ℕ) := fun n ↦
    (secondaryD N L n, ((secondaryP N L n).log2, n.log2))
  have hband (z : ℕ × (ℕ × ℕ)) :
      secondaryBand N L A z.1 z.2.1 z.2.2 = A.filter fun n ↦ f n = z := by
    ext n
    simp only [mem_secondaryBand, Finset.mem_filter]
    constructor
    · rintro ⟨hn, hd, hp, hx⟩
      exact ⟨hn, Prod.ext hd (Prod.ext hp hx)⟩
    · rintro ⟨hn, hz⟩
      have hd := congrArg (fun w : ℕ × (ℕ × ℕ) ↦ w.1) hz
      have hp := congrArg (fun w : ℕ × (ℕ × ℕ) ↦ w.2.1) hz
      have hx := congrArg (fun w : ℕ × (ℕ × ℕ) ↦ w.2.2) hz
      exact ⟨hn, by simpa [f] using hd, by simpa [f] using hp,
        by simpa [f] using hx⟩
  simp_rw [hband]
  apply Finset.card_eq_sum_card_fiberwise
  intro n hn
  have hr := secondaryWitness_spec (hAsec hn)
  have hnN := (mem_secondarySet.mp (hAsec hn)).2.1
  have hnPos := (mem_secondarySet.mp (hAsec hn)).1
  have hfac := hr.2.2.2.2.2.2.2.2.2.1
  have hdDvd : secondaryD N L n ∣ n := by
    exact ⟨secondaryP N L n * secondaryS N L n,
      hfac.trans (by ring)⟩
  have hpDvd : secondaryP N L n ∣ n := by
    exact ⟨secondaryD N L n * secondaryS N L n,
      hfac.trans (by ring)⟩
  have hdN : secondaryD N L n ≤ N :=
    (Nat.le_of_dvd hnPos hdDvd).trans hnN
  have hpN : secondaryP N L n ≤ N :=
    (Nat.le_of_dvd hnPos hpDvd).trans hnN
  change (secondaryD N L n, ((secondaryP N L n).log2, n.log2)) ∈
    secondaryBandIndices N
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨hr.1, hdN⟩
  · apply Finset.mem_product.mpr
    constructor <;> rw [Finset.mem_range, Nat.lt_succ_iff]
    · change (secondaryP N L n).log2 ≤ N.log2
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hpN
    · change n.log2 ≤ N.log2
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right hnN

/-- The complete secondary estimate after summing the fixed-band bounds. -/
theorem secondary_global_bound
    {N L H : ℕ} {A : Finset ℕ}
    (hAsec : A ⊆ secondarySet N L) (hmono : TotientMonotoneOn A)
    (hN : 0 < N) (hH : 2 ≤ H) (hLT : secondaryT H ^ 3 ≤ L) :
    (A.card : ℝ) ≤
      8000 * (N : ℝ) * (1 + Real.log N) * (N.log2 + 1 : ℕ) ^ 2 /
        secondaryT H := by
  let K := N.log2 + 1
  have hpartition := secondary_card_eq_sum_bands hAsec
  have hpoint (z : ℕ × (ℕ × ℕ)) (hz : z ∈ secondaryBandIndices N) :
      ((secondaryBand N L A z.1 z.2.1 z.2.2).card : ℝ) ≤
        (8000 : ℝ) * ((2 ^ z.2.2 : ℕ) : ℝ) /
          ((z.1 * secondaryT H : ℕ) : ℝ) :=
    secondaryBand_uniform_bound hAsec hmono hH hLT _ _ _
  have hsum : (A.card : ℝ) ≤ ∑ z ∈ secondaryBandIndices N,
      (8000 : ℝ) * ((2 ^ z.2.2 : ℕ) : ℝ) /
        ((z.1 * secondaryT H : ℕ) : ℝ) := by
    rw [hpartition, Nat.cast_sum]
    exact Finset.sum_le_sum hpoint
  have hharm :
      (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div] using harmonic_le_one_add_log N
  have hgeom : (∑ j ∈ Finset.range K, ((2 ^ j : ℕ) : ℝ)) ≤ K * N := by
    calc
      (∑ j ∈ Finset.range K, ((2 ^ j : ℕ) : ℝ)) ≤
          ∑ _j ∈ Finset.range K, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjK := Finset.mem_range.mp hj
        have hjlog : j ≤ N.log2 := by dsimp only [K] at hjK; omega
        have hjpow : 2 ^ j ≤ N := by
          rw [Nat.log2_eq_log_two] at hjlog
          exact Nat.pow_le_of_le_log hN.ne' hjlog
        exact_mod_cast hjpow
      _ = (K : ℝ) * N := by simp
  have hsumEq :
      (∑ z ∈ secondaryBandIndices N,
        (8000 : ℝ) * ((2 ^ z.2.2 : ℕ) : ℝ) /
          ((z.1 * secondaryT H : ℕ) : ℝ)) =
      (8000 / (secondaryT H : ℝ)) *
        (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) *
        (K : ℝ) * (∑ j ∈ Finset.range K, ((2 ^ j : ℕ) : ℝ)) := by
    let s := Finset.Icc 1 N
    let r := Finset.range K
    let f : ℕ × (ℕ × ℕ) → ℝ := fun z ↦
      (8000 : ℝ) * ((2 ^ z.2.2 : ℕ) : ℝ) /
        ((z.1 * secondaryT H : ℕ) : ℝ)
    change (s.product (r.product r)).sum f = _
    calc
      (s.product (r.product r)).sum f =
          ∑ d ∈ s, ∑ w ∈ r.product r, f (d, w) :=
        Finset.sum_product s (r.product r) f
      _ = ∑ d ∈ s, ∑ i ∈ r, ∑ j ∈ r, f (d, (i, j)) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact Finset.sum_product r r (fun w ↦ f (d, w))
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            (8000 / (secondaryT H : ℝ)) * ((1 : ℝ) / d) *
              ((2 ^ j : ℕ) : ℝ) := by
        dsimp only [s, r, f]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = (8000 / (secondaryT H : ℝ)) *
          (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) *
          (K : ℝ) * (∑ j ∈ Finset.range K, ((2 ^ j : ℕ) : ℝ)) := by
        simp_rw [← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        simp_rw [← Finset.mul_sum]
        ring
  apply hsum.trans
  rw [hsumEq]
  have hTnat : 0 < secondaryT H := by simp [secondaryT]; positivity
  have hT : (0 : ℝ) < secondaryT H := by exact_mod_cast hTnat
  have hnonneg : 0 ≤ 8000 / (secondaryT H : ℝ) := by positivity
  calc
    (8000 / (secondaryT H : ℝ)) *
        (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d) *
        (K : ℝ) * (∑ j ∈ Finset.range K, ((2 ^ j : ℕ) : ℝ)) ≤
      (8000 / (secondaryT H : ℝ)) * (1 + Real.log N) *
        (K : ℝ) * (K * N) := by gcongr
    _ = 8000 * (N : ℝ) * (1 + Real.log N) * (N.log2 + 1 : ℕ) ^ 2 /
        secondaryT H := by
      dsimp only [K]
      ring

#print axioms secondary_global_bound

end

end Erdos49
