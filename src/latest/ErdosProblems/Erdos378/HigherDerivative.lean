/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.ReciprocalExponential
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Higher derivative estimates for reciprocal exponential sums

This file formalizes the order-parameterized Weyl--van der Corput step used
in Granville--Ramaré, Lemmas 8.3--8.6.  The formulation below keeps the
successive differencing lengths in a list.  This is more convenient for the
reciprocal phase than hard-coding a fixed number of correlation layers.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace HigherDerivative

open ReciprocalExponential

noncomputable section

/-- The iterated multiplicative correlation of a complex sequence. -/
def iteratedCorrelation : List ℕ → (ℕ → ℂ) → ℕ → ℂ
  | [], u => u
  | r :: rs, u => fun n ↦
      iteratedCorrelation rs u n *
        conj (iteratedCorrelation rs u (n + r))

@[simp] lemma iteratedCorrelation_nil (u : ℕ → ℂ) :
    iteratedCorrelation [] u = u := rfl

@[simp] lemma iteratedCorrelation_cons (r : ℕ) (rs : List ℕ)
    (u : ℕ → ℂ) (n : ℕ) :
    iteratedCorrelation (r :: rs) u n =
      iteratedCorrelation rs u n *
        conj (iteratedCorrelation rs u (n + r)) := rfl

lemma norm_iteratedCorrelation_le_one {u : ℕ → ℂ}
    (hu : ∀ n, ‖u n‖ ≤ 1) (rs : List ℕ) (n : ℕ) :
    ‖iteratedCorrelation rs u n‖ ≤ 1 := by
  induction rs generalizing n with
  | nil => simpa using hu n
  | cons r rs ih =>
      rw [iteratedCorrelation_cons, norm_mul, Complex.norm_conj]
      exact mul_le_one₀ (ih n) (norm_nonneg _) (ih (n + r))

/-- The normalized absolute correlation sum.  The denominator remains the
original ambient length `N` at every differencing level. -/
def correlationAverage (u : ℕ → ℂ) (N : ℕ) (rs : List ℕ) : ℝ :=
  ‖∑ n ∈ Finset.Icc 1 (N - rs.sum), iteratedCorrelation rs u n‖ /
    (8 * (N : ℝ))

lemma correlationAverage_nonneg (u : ℕ → ℂ) (N : ℕ)
    (rs : List ℕ) : 0 ≤ correlationAverage u N rs := by
  unfold correlationAverage
  positivity

/-- One normalized van der Corput step. -/
lemma correlationAverage_sq_le
    {u : ℕ → ℂ} {N L : ℕ} {rs : List ℕ}
    (hN : 0 < N) (hL : 1 ≤ L) (hfit : rs.sum + L ≤ N)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    correlationAverage u N rs ^ 2 ≤
      1 / (8 * (L : ℝ)) +
        (1 / (2 * (L : ℝ))) *
          ∑ r ∈ Finset.Icc 1 (L - 1),
            correlationAverage u N (r :: rs) := by
  let M := N - rs.sum
  have hLM : L ≤ M := by dsimp only [M]; omega
  have hM : 1 ≤ M := hL.trans hLM
  have hvdc := vdc_norm_sq_mul_le
    (fun n ↦ iteratedCorrelation rs u n) hL hLM
    (fun n _hn ↦ norm_iteratedCorrelation_le_one hu rs n)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hLreal : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_lt_of_lt hL)
  have hMleN : M ≤ N := Nat.sub_le _ _
  have hMreal : (M : ℝ) ≤ N := by exact_mod_cast hMleN
  have hcorr : ∀ r ∈ Finset.Icc 1 (L - 1),
      (∑ n ∈ Finset.Icc 1 (M - r),
          iteratedCorrelation rs u n *
            conj (iteratedCorrelation rs u (n + r))) =
        ∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
          iteratedCorrelation (r :: rs) u n := by
    intro r hr
    have hrsum : (r :: rs).sum = rs.sum + r := by simp [Nat.add_comm]
    rw [hrsum, show N - (rs.sum + r) = M - r by
      dsimp only [M]
      omega]
    apply Finset.sum_congr rfl
    intro n hn
    rw [iteratedCorrelation_cons]
  rw [correlationAverage]
  change
    (‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ /
        (8 * (N : ℝ))) ^ 2 ≤ _
  have hvdc' :
      (L : ℝ) ^ 2 *
          ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 ≤
        2 * (L : ℝ) * (M : ℝ) ^ 2 +
          4 * (M : ℝ) * (L : ℝ) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                iteratedCorrelation (r :: rs) u n‖ := by
    apply hvdc.trans_eq
    congr 2
    apply Finset.sum_congr rfl
    intro r hr
    rw [hcorr r hr]
  rw [div_pow]
  -- Clearing the positive common denominator leaves the two coarse bounds
  -- `M ≤ N` and `#Icc 1 (L-1) ≤ L`.
  have hsumRewrite :
      (∑ r ∈ Finset.Icc 1 (L - 1),
          correlationAverage u N (r :: rs)) =
        (1 / (8 * (N : ℝ))) *
          ∑ r ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
              iteratedCorrelation (r :: rs) u n‖ := by
    unfold correlationAverage
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    field_simp
  rw [hsumRewrite]
  have hdiag :
      ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 /
          (64 * (N : ℝ) ^ 2) ≤ 1 / (8 * (L : ℝ)) +
        (1 / (16 * (N : ℝ) * (L : ℝ))) *
          ∑ r ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
              iteratedCorrelation (r :: rs) u n‖ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * (N : ℝ) ^ 2)]
    rw [show (1 / (8 * (L : ℝ)) +
        1 / (16 * (N : ℝ) * (L : ℝ)) *
          ∑ r ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
              iteratedCorrelation (r :: rs) u n‖) *
          (64 * (N : ℝ) ^ 2) =
        8 * (N : ℝ) ^ 2 / (L : ℝ) +
          4 * (N : ℝ) / (L : ℝ) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                iteratedCorrelation (r :: rs) u n‖ by field_simp <;> ring]
    have hvdcDiv :
        ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 ≤
          (2 * (L : ℝ) * (M : ℝ) ^ 2 +
            4 * (M : ℝ) * (L : ℝ) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖) /
            (L : ℝ) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hLreal 2)]
      simpa only [mul_comm] using hvdc'
    have hdiagPart :
        2 * (L : ℝ) * (M : ℝ) ^ 2 / (L : ℝ) ^ 2 ≤
          8 * (N : ℝ) ^ 2 / (L : ℝ) := by
      field_simp
      nlinarith [sq_nonneg ((N : ℝ) - M)]
    have hoffPart :
        4 * (M : ℝ) * (L : ℝ) *
              (∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖) /
            (L : ℝ) ^ 2 ≤
          4 * (N : ℝ) / (L : ℝ) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖ := by
      have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc 1 (L - 1),
          ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
            iteratedCorrelation (r :: rs) u n‖ := by positivity
      calc
        4 * (M : ℝ) * (L : ℝ) *
              (∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖) /
            (L : ℝ) ^ 2 =
          4 * (M : ℝ) / (L : ℝ) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖ := by
            field_simp [ne_of_gt hLreal]
        _ ≤ 4 * (N : ℝ) / (L : ℝ) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖ := by
            gcongr
    calc
      ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 ≤
          (2 * (L : ℝ) * (M : ℝ) ^ 2 +
            4 * (M : ℝ) * (L : ℝ) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                  iteratedCorrelation (r :: rs) u n‖) /
              (L : ℝ) ^ 2 := hvdcDiv
      _ ≤ _ := by
        calc
          (2 * (L : ℝ) * (M : ℝ) ^ 2 +
              4 * (M : ℝ) * (L : ℝ) *
                ∑ r ∈ Finset.Icc 1 (L - 1),
                  ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                    iteratedCorrelation (r :: rs) u n‖) /
                (L : ℝ) ^ 2 =
            2 * (L : ℝ) * (M : ℝ) ^ 2 / (L : ℝ) ^ 2 +
              (4 * (M : ℝ) * (L : ℝ) *
                ∑ r ∈ Finset.Icc 1 (L - 1),
                  ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                    iteratedCorrelation (r :: rs) u n‖) /
                (L : ℝ) ^ 2 := by rw [add_div]
          _ ≤ 8 * (N : ℝ) ^ 2 / (L : ℝ) +
              4 * (N : ℝ) / (L : ℝ) *
                ∑ r ∈ Finset.Icc 1 (L - 1),
                  ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                    iteratedCorrelation (r :: rs) u n‖ :=
            add_le_add hdiagPart hoffPart
  calc
    ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 /
        (8 * (N : ℝ)) ^ 2 =
      ‖∑ n ∈ Finset.Icc 1 M, iteratedCorrelation rs u n‖ ^ 2 /
        (64 * (N : ℝ) ^ 2) := by ring
    _ ≤ 1 / (8 * (L : ℝ)) +
        1 / (16 * (N : ℝ) * (L : ℝ)) *
          ∑ r ∈ Finset.Icc 1 (L - 1),
            ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
              iteratedCorrelation (r :: rs) u n‖ := hdiag
    _ = 1 / (8 * (L : ℝ)) +
        (1 / (2 * (L : ℝ))) *
          ((1 / (8 * (N : ℝ))) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              ‖∑ n ∈ Finset.Icc 1 (N - (r :: rs).sum),
                iteratedCorrelation (r :: rs) u n‖) := by ring

/-- The average of the terminal correlations after the remaining sequence
of differencing lengths has been used. -/
def terminalCorrelationMean (u : ℕ → ℂ) (N : ℕ) :
    List ℕ → List ℕ → ℝ
  | [], rs => correlationAverage u N rs
  | L :: Ls, rs =>
      (1 / (L : ℝ)) *
        ∑ r ∈ Finset.Icc 1 (L - 1),
          terminalCorrelationMean u N Ls (r :: rs)

/-- Accumulated diagonal loss in the iterated van der Corput argument. -/
def differencingError : List ℕ → ℝ
  | [] => 0
  | L :: Ls => 1 / (L : ℝ) + differencingError Ls

lemma terminalCorrelationMean_nonneg (u : ℕ → ℂ) (N : ℕ)
    (Ls rs : List ℕ) : 0 ≤ terminalCorrelationMean u N Ls rs := by
  induction Ls generalizing rs with
  | nil => exact correlationAverage_nonneg u N rs
  | cons L Ls ih =>
      simp only [terminalCorrelationMean]
      exact mul_nonneg (by positivity) <|
        Finset.sum_nonneg fun r _hr ↦ ih (r :: rs)

lemma differencingError_nonneg (Ls : List ℕ) :
    0 ≤ differencingError Ls := by
  induction Ls with
  | nil => simp [differencingError]
  | cons L Ls ih =>
      simp only [differencingError]
      positivity

private lemma normalized_sum_pow_le_sum_pow
    {s : Finset ℕ} {f : ℕ → ℝ} {L P : ℕ}
    (hL : 0 < L) (hcard : s.card ≤ L) (hP : 0 < P)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ((1 / (L : ℝ)) * ∑ i ∈ s, f i) ^ P ≤
      (1 / (L : ℝ)) * ∑ i ∈ s, (f i) ^ P := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hP)
  have hjensen := pow_sum_le_card_mul_sum_pow (s := s) (f := f) hf p
  have hcardR : (s.card : ℝ) ≤ L := by exact_mod_cast hcard
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hsumPow : 0 ≤ ∑ i ∈ s, f i ^ (p + 1) :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (hf i hi) _
  have hcardPow : (s.card : ℝ) ^ p ≤ (L : ℝ) ^ p := by
    exact pow_le_pow_left₀ (by positivity) hcardR p
  rw [show (1 / (L : ℝ)) * ∑ i ∈ s, f i =
      (∑ i ∈ s, f i) / (L : ℝ) by
        simp only [one_div, div_eq_mul_inv, one_mul]
        ring]
  rw [div_pow, div_le_iff₀ (pow_pos hLreal (p + 1))]
  calc
    (∑ i ∈ s, f i) ^ (p + 1) ≤
        (s.card : ℝ) ^ p * ∑ i ∈ s, f i ^ (p + 1) := hjensen
    _ ≤ (L : ℝ) ^ p * ∑ i ∈ s, f i ^ (p + 1) :=
      mul_le_mul_of_nonneg_right hcardPow hsumPow
    _ = ((1 / (L : ℝ)) * ∑ i ∈ s, f i ^ (p + 1)) *
        (L : ℝ) ^ (p + 1) := by
      field_simp [ne_of_gt hLreal]
      ring

/-- A deliberately generous constant for the iterated moment estimate. -/
def vdcMomentConstant (k : ℕ) : ℝ :=
  2 ^ (2 ^ k : ℕ)

lemma vdcMomentConstant_pos (k : ℕ) : 0 < vdcMomentConstant k := by
  unfold vdcMomentConstant
  positivity

/-- List form of the Weyl--van der Corput inequality (Granville--Ramaré
Lemma 8.3).  Constants are intentionally coarse; the important features are
the `2^k` moment, one reciprocal loss for each cutoff, and the terminal
average over all positive shifts. -/
theorem correlationAverage_pow_two_pow_le
    {u : ℕ → ℂ} {N : ℕ} (rs Ls : List ℕ)
    (hN : 0 < N) (hfit : rs.sum + Ls.sum ≤ N)
    (hLs : ∀ L ∈ Ls, 1 ≤ L) (hu : ∀ n, ‖u n‖ ≤ 1) :
    correlationAverage u N rs ^ (2 ^ Ls.length) ≤
      vdcMomentConstant Ls.length *
        (differencingError Ls + terminalCorrelationMean u N Ls rs) := by
  induction Ls generalizing rs with
  | nil =>
      simp only [List.length_nil, pow_zero, terminalCorrelationMean,
        differencingError, zero_add]
      have hA := correlationAverage_nonneg u N rs
      unfold vdcMomentConstant
      norm_num
      linarith
  | cons L Ls ih =>
      have hL : 1 ≤ L := hLs L (by simp)
      have htail : ∀ K ∈ Ls, 1 ≤ K := by
        intro K hK
        exact hLs K (by simp [hK])
      have hheadFit : rs.sum + L ≤ N := by
        have hsumNonneg : L ≤ L + Ls.sum := Nat.le_add_right L _
        exact (Nat.add_le_add_left hsumNonneg rs.sum).trans hfit
      have hstep := correlationAverage_sq_le hN hL hheadFit hu
      let A := correlationAverage u N rs
      let a : ℝ := 1 / (8 * (L : ℝ))
      let b : ℝ := (1 / (2 * (L : ℝ))) *
        ∑ r ∈ Finset.Icc 1 (L - 1),
          correlationAverage u N (r :: rs)
      let P : ℕ := 2 ^ Ls.length
      have hA0 : 0 ≤ A := correlationAverage_nonneg u N rs
      have ha0 : 0 ≤ a := by dsimp only [a]; positivity
      have hb0 : 0 ≤ b := by
        dsimp only [b]
        exact mul_nonneg (by positivity) <|
          Finset.sum_nonneg fun r _hr ↦ correlationAverage_nonneg u N (r :: rs)
      have hP : 0 < P := by dsimp only [P]; positivity
      have hstep' : A ^ 2 ≤ a + b := by
        simpa only [A, a, b] using hstep
      have hraise : A ^ (2 * P) ≤ (a + b) ^ P := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg A) hstep' P
      have hadd := add_pow_le ha0 hb0 P
      have haOne : a ≤ 1 := by
        dsimp only [a]
        have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
        rw [div_le_one₀ (by positivity)]
        nlinarith
      have haPow : a ^ P ≤ 1 / (L : ℝ) := by
        have haPOne : a ^ P ≤ a := by
          obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hP)
          rw [hq, pow_succ']
          exact mul_le_of_le_one_right ha0 (pow_le_one₀ ha0 haOne)
        calc
          a ^ P ≤ a := haPOne
          _ ≤ 1 / (L : ℝ) := by
            dsimp only [a]
            gcongr
            nlinarith [show (1 : ℝ) ≤ L by exact_mod_cast hL]
      have hbMean : b ≤
          (1 / (L : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              correlationAverage u N (r :: rs) := by
        dsimp only [b]
        have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc 1 (L - 1),
            correlationAverage u N (r :: rs) :=
          Finset.sum_nonneg fun r _hr ↦ correlationAverage_nonneg u N (r :: rs)
        have hcoef : 1 / (2 * (L : ℝ)) ≤ 1 / (L : ℝ) := by
          have hLreal : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_lt_of_lt hL)
          rw [div_le_div_iff₀ (by positivity) hLreal]
          nlinarith
        exact mul_le_mul_of_nonneg_right hcoef hsum0
      have hbPow : b ^ P ≤
          (1 / (L : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              correlationAverage u N (r :: rs) ^ P := by
        calc
          b ^ P ≤ ((1 / (L : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                correlationAverage u N (r :: rs)) ^ P :=
            pow_le_pow_left₀ hb0 hbMean P
          _ ≤ _ := normalized_sum_pow_le_sum_pow
            (s := Finset.Icc 1 (L - 1))
            (f := fun r ↦ correlationAverage u N (r :: rs))
            (L := L) (P := P) (by omega) (by simp) hP
            (fun r _hr ↦ correlationAverage_nonneg u N (r :: rs))
      have hchild : ∀ r ∈ Finset.Icc 1 (L - 1),
          correlationAverage u N (r :: rs) ^ P ≤
            vdcMomentConstant Ls.length *
              (differencingError Ls +
                terminalCorrelationMean u N Ls (r :: rs)) := by
        intro r hr
        have hrL : r ≤ L - 1 := (Finset.mem_Icc.mp hr).2
        have hchildFit : (r :: rs).sum + Ls.sum ≤ N := by
          simp only [List.sum_cons] at hfit ⊢
          omega
        simpa [P] using ih (r :: rs) hchildFit htail
      have hchildren :
          (1 / (L : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                correlationAverage u N (r :: rs) ^ P ≤
            vdcMomentConstant Ls.length *
              (differencingError Ls +
                terminalCorrelationMean u N (L :: Ls) rs) := by
        have hsum := Finset.sum_le_sum hchild
        have hL0 : 0 ≤ 1 / (L : ℝ) := by positivity
        calc
          (1 / (L : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                correlationAverage u N (r :: rs) ^ P ≤
            (1 / (L : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (L - 1),
                vdcMomentConstant Ls.length *
                  (differencingError Ls +
                    terminalCorrelationMean u N Ls (r :: rs)) := by
              gcongr
          _ ≤ vdcMomentConstant Ls.length *
              (differencingError Ls +
                terminalCorrelationMean u N (L :: Ls) rs) := by
            have hsumExact :
                (∑ r ∈ Finset.Icc 1 (L - 1),
                    vdcMomentConstant Ls.length *
                      (differencingError Ls +
                        terminalCorrelationMean u N Ls (r :: rs))) =
                  ((Finset.Icc 1 (L - 1)).card : ℝ) *
                      (vdcMomentConstant Ls.length * differencingError Ls) +
                    vdcMomentConstant Ls.length *
                      ∑ r ∈ Finset.Icc 1 (L - 1),
                        terminalCorrelationMean u N Ls (r :: rs) := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
              rw [Finset.mul_sum]
            simp only [terminalCorrelationMean]
            rw [hsumExact]
            have hcard : ((Finset.Icc 1 (L - 1)).card : ℝ) ≤ L := by
              simp
            have hErr0 := differencingError_nonneg Ls
            have hC0 := (vdcMomentConstant_pos Ls.length).le
            have hmean0 : 0 ≤ ∑ r ∈ Finset.Icc 1 (L - 1),
                terminalCorrelationMean u N Ls (r :: rs) :=
              Finset.sum_nonneg fun r _hr ↦
                terminalCorrelationMean_nonneg u N Ls (r :: rs)
            have hLpos : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_lt_of_lt hL)
            have hcardDiv :
                ((Finset.Icc 1 (L - 1)).card : ℝ) / L ≤ 1 := by
              rw [div_le_one₀ hLpos]
              exact hcard
            have hcardErr :
                (((Finset.Icc 1 (L - 1)).card : ℝ) / L) *
                    differencingError Ls ≤ differencingError Ls :=
              mul_le_of_le_one_left hErr0 hcardDiv
            calc
              (1 / (L : ℝ)) *
                  (((Finset.Icc 1 (L - 1)).card : ℝ) *
                      (vdcMomentConstant Ls.length * differencingError Ls) +
                    vdcMomentConstant Ls.length *
                      ∑ r ∈ Finset.Icc 1 (L - 1),
                        terminalCorrelationMean u N Ls (r :: rs)) =
                vdcMomentConstant Ls.length *
                  ((((Finset.Icc 1 (L - 1)).card : ℝ) / L) *
                      differencingError Ls +
                    (1 / (L : ℝ)) *
                      ∑ r ∈ Finset.Icc 1 (L - 1),
                        terminalCorrelationMean u N Ls (r :: rs)) := by ring
              _ ≤ vdcMomentConstant Ls.length *
                  (differencingError Ls +
                    (1 / (L : ℝ)) *
                      ∑ r ∈ Finset.Icc 1 (L - 1),
                        terminalCorrelationMean u N Ls (r :: rs)) := by
                gcongr
      have hbase : A ^ (2 * P) ≤
          2 ^ (P - 1) *
            (1 / (L : ℝ) +
              vdcMomentConstant Ls.length *
                (differencingError Ls +
                  terminalCorrelationMean u N (L :: Ls) rs)) := by
        calc
          A ^ (2 * P) ≤ (a + b) ^ P := hraise
          _ ≤ 2 ^ (P - 1) * (a ^ P + b ^ P) := by
            simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hP))]
              using hadd
          _ ≤ 2 ^ (P - 1) *
              (1 / (L : ℝ) +
                vdcMomentConstant Ls.length *
                  (differencingError Ls +
                    terminalCorrelationMean u N (L :: Ls) rs)) := by
            apply mul_le_mul_of_nonneg_left
            · exact add_le_add haPow (hbPow.trans hchildren)
            · positivity
      have hRest0 : 0 ≤ differencingError Ls +
          terminalCorrelationMean u N (L :: Ls) rs :=
        add_nonneg (differencingError_nonneg Ls)
          (terminalCorrelationMean_nonneg u N (L :: Ls) rs)
      have hCoef1 : 2 ^ (P - 1 : ℕ) ≤
          vdcMomentConstant (L :: Ls).length := by
        unfold vdcMomentConstant
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        simp only [List.length_cons, pow_succ]
        dsimp only [P]
        omega
      have hCoef2 : 2 ^ (P - 1 : ℕ) * vdcMomentConstant Ls.length ≤
          vdcMomentConstant (L :: Ls).length := by
        unfold vdcMomentConstant
        rw [← pow_add]
        apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        simp only [List.length_cons, pow_succ]
        dsimp only [P]
        omega
      rw [show 2 ^ (L :: Ls).length = 2 * P by
        simp only [List.length_cons, pow_succ]
        dsimp only [P]
        omega]
      exact hbase.trans <| by
        simp only [differencingError]
        calc
          2 ^ (P - 1) *
              (1 / (L : ℝ) +
                vdcMomentConstant Ls.length *
                  (differencingError Ls +
                    terminalCorrelationMean u N (L :: Ls) rs)) =
            2 ^ (P - 1) * (1 / (L : ℝ)) +
              (2 ^ (P - 1) * vdcMomentConstant Ls.length) *
                (differencingError Ls +
                  terminalCorrelationMean u N (L :: Ls) rs) := by ring
          _ ≤ vdcMomentConstant (L :: Ls).length * (1 / (L : ℝ)) +
              vdcMomentConstant (L :: Ls).length *
                (differencingError Ls +
                  terminalCorrelationMean u N (L :: Ls) rs) := by
            gcongr
          _ = vdcMomentConstant (L :: Ls).length *
              (1 / (L : ℝ) + differencingError Ls +
                terminalCorrelationMean u N (L :: Ls) rs) := by ring

/-! ## Terminal reciprocal correlations -/

/-- Iterated multiplicative correlations of an additive character are the
corresponding signed additive finite differences. -/
lemma iteratedCorrelation_e_eq (F : ℝ → ℝ) (rs : List ℕ) (n : ℕ) :
    iteratedCorrelation rs (fun m ↦ e (F m)) n =
      e (((-1 : ℝ) ^ rs.length) *
        forwardDifferences (rs.map (fun r : ℕ ↦ (r : ℝ))) F n) := by
  induction rs generalizing n with
  | nil => simp [iteratedCorrelation, forwardDifferences]
  | cons r rs ih =>
      rw [iteratedCorrelation_cons, ih n, ih (n + r), ← e_sub]
      congr 1
      simp only [List.length_cons, List.map_cons, forwardDifferences_cons,
        Nat.cast_add]
      rw [pow_succ]
      ring

lemma forwardDifferences_translate (F : ℝ → ℝ) (rs : List ℝ)
    (a t : ℝ) :
    forwardDifferences rs (fun x ↦ F (a + x)) t =
      forwardDifferences rs F (a + t) := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih =>
      rw [forwardDifferences_cons, forwardDifferences_cons, ih, ih]
      congr 1
      ring

/-- The real phase represented by an iterated reciprocal correlation. -/
def signedReciprocalDifference
    (X : ℝ) (A : ℕ) (rs : List ℕ) (i : ℕ) : ℝ :=
  ((-1 : ℝ) ^ rs.length) *
    forwardDifferences (rs.map (fun r : ℕ ↦ (r : ℝ)))
      (fun t ↦ -X / t) (A + i : ℕ)

lemma iteratedCorrelation_reciprocal_eq
    (X : ℝ) (A : ℕ) (rs : List ℕ) (n : ℕ) :
    iteratedCorrelation rs
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ))) n =
      e (signedReciprocalDifference X A rs n) := by
  have h := iteratedCorrelation_e_eq
    (fun t : ℝ ↦ -X / ((A : ℝ) + t)) rs n
  calc
    iteratedCorrelation rs
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ))) n =
      iteratedCorrelation rs
        (fun m ↦ e (-X / ((A : ℝ) + (m : ℝ)))) n := by
          congr 3
          funext m
          push_cast
          rfl
    _ = e (((-1 : ℝ) ^ rs.length) *
        forwardDifferences (rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t : ℝ ↦ -X / ((A : ℝ) + t)) n) := h
    _ = e (signedReciprocalDifference X A rs n) := by
      unfold signedReciprocalDifference
      congr 2
      rw [forwardDifferences_translate]
      congr 2
      push_cast
      ring

private lemma neg_one_pow_mul_succ (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 1)) = -1 := by
  rw [← pow_add]
  have hk : k + (k + 1) = 2 * k + 1 := by omega
  rw [hk, pow_succ]
  have heven : ((-1 : ℝ) ^ (2 * k)) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven]
  norm_num

lemma signedReciprocalDifference_succ_sub (X : ℝ) (A : ℕ)
    (rs : List ℕ) (i : ℕ) :
    signedReciprocalDifference X A rs (i + 1) -
        signedReciprocalDifference X A rs i =
      ((-1 : ℝ) ^ rs.length) *
        forwardDifferences
          ((1 : ℝ) :: rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t ↦ -X / t) (A + i : ℕ) := by
  simp only [signedReciprocalDifference, forwardDifferences_cons]
  push_cast
  ring

/-- Mean-value form of a terminal reciprocal-correlation gap, in every
derivative order. -/
lemma exists_signedReciprocalDifference_gap
    (X : ℝ) (hX : 0 < X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) (i : ℕ) :
    ∃ y : ℝ, (A + i : ℕ) ≤ y ∧
      y ≤ (A + i : ℕ) + 1 + rs.sum ∧
      signedReciprocalDifference X A rs (i + 1) -
          signedReciprocalDifference X A rs i =
        X * ((rs.length + 1).factorial : ℝ) *
          (rs.prod : ℝ) / y ^ (rs.length + 2) := by
  let shifts : List ℝ :=
    (1 : ℝ) :: rs.map (fun r : ℕ ↦ (r : ℝ))
  have hshifts : ∀ r ∈ shifts, 0 < r := by
    intro r hr
    rw [show shifts = (1 : ℝ) ::
      rs.map (fun r : ℕ ↦ (r : ℝ)) by rfl] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · norm_num
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact_mod_cast hrs s hs
  have ht : 0 < (((A + i : ℕ) : ℝ)) := by positivity
  obtain ⟨y, hty, hy, hfd⟩ :=
    exists_forwardDifferences_reciprocal_eq X shifts hshifts ht
  refine ⟨y, hty, ?_, ?_⟩
  · have hsum : shifts.sum = 1 + (rs.sum : ℝ) := by
      simp [shifts]
    calc
      y ≤ ((A + i : ℕ) : ℝ) + shifts.sum := hy
      _ = ((A + i : ℕ) : ℝ) + 1 + (rs.sum : ℝ) := by rw [hsum]; ring
      _ = (((A + i : ℕ) : ℝ) + 1 + rs.sum) := by push_cast; ring
  · rw [signedReciprocalDifference_succ_sub, hfd]
    have hypos : 0 < y := ht.trans_le hty
    have hsign := neg_one_pow_mul_succ rs.length
    have hlen : shifts.length = rs.length + 1 := by simp [shifts]
    have hprod : shifts.prod = (rs.prod : ℝ) := by
      simp [shifts]
    rw [hlen, hprod]
    unfold reciprocalDeriv
    rw [show -1 - ((rs.length + 1 : ℕ) : ℤ) =
        -((rs.length + 2 : ℕ) : ℤ) by omega]
    rw [zpow_neg]
    rw [zpow_natCast]
    change ((-1 : ℝ) ^ rs.length) *
        ((rs.prod : ℝ) *
          (-X * (((-1 : ℝ) ^ (rs.length + 1)) *
            ((rs.length + 1).factorial : ℝ) *
            (y ^ (rs.length + 2))⁻¹))) = _
    calc
      ((-1 : ℝ) ^ rs.length) *
          ((rs.prod : ℝ) *
            (-X * (((-1 : ℝ) ^ (rs.length + 1)) *
              ((rs.length + 1).factorial : ℝ) *
              (y ^ (rs.length + 2))⁻¹))) =
        -(((-1 : ℝ) ^ rs.length) *
            ((-1 : ℝ) ^ (rs.length + 1))) *
          X * ((rs.length + 1).factorial : ℝ) *
          (rs.prod : ℝ) * (y ^ (rs.length + 2))⁻¹ := by ring
      _ = X * ((rs.length + 1).factorial : ℝ) *
          (rs.prod : ℝ) / y ^ (rs.length + 2) := by
        rw [hsign]
        simp only [neg_neg, one_mul, div_eq_mul_inv]

lemma signedReciprocalDifference_gap_lower
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) {i : ℕ}
    (hi : i + 1 + rs.sum ≤ N) :
    X * ((rs.length + 1).factorial : ℝ) * (rs.prod : ℝ) /
        ((A + N : ℕ) : ℝ) ^ (rs.length + 2) ≤
      signedReciprocalDifference X A rs (i + 1) -
        signedReciprocalDifference X A rs i := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_signedReciprocalDifference_gap X hX hA rs hrs i
  rw [hgap]
  have hypos : 0 < y := (by positivity : 0 < (((A + i : ℕ) : ℝ))).trans_le hty
  have hyAN : y ≤ ((A + N : ℕ) : ℝ) := by
    calc
      y ≤ ((A + i : ℕ) : ℝ) + 1 + rs.sum := hy
      _ ≤ ((A + N : ℕ) : ℝ) := by
        have hnat : A + i + 1 + rs.sum ≤ A + N := by omega
        exact_mod_cast hnat
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

lemma signedReciprocalDifference_gap_upper
    (X : ℝ) (hX : 0 < X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) (i : ℕ) :
    signedReciprocalDifference X A rs (i + 1) -
        signedReciprocalDifference X A rs i ≤
      X * ((rs.length + 1).factorial : ℝ) * (rs.prod : ℝ) /
        (A : ℝ) ^ (rs.length + 2) := by
  obtain ⟨y, hty, hy, hgap⟩ :=
    exists_signedReciprocalDifference_gap X hX hA rs hrs i
  rw [hgap]
  have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
  have hAy : (A : ℝ) ≤ y := by
    exact (by exact_mod_cast Nat.le_add_right A i :
      (A : ℝ) ≤ (A + i : ℕ)).trans hty
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · gcongr

private lemma neg_one_pow_mul_add_two (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 2)) = 1 := by
  rw [← pow_add]
  have hk : k + (k + 2) = 2 * (k + 1) := by omega
  rw [hk, pow_mul]
  norm_num

lemma signedReciprocalDifference_gap_succ_sub
    (X : ℝ) (A : ℕ) (rs : List ℕ) (i : ℕ) :
    (signedReciprocalDifference X A rs (i + 2) -
        signedReciprocalDifference X A rs (i + 1)) -
      (signedReciprocalDifference X A rs (i + 1) -
        signedReciprocalDifference X A rs i) =
      ((-1 : ℝ) ^ rs.length) *
        forwardDifferences
          ((1 : ℝ) :: (1 : ℝ) ::
            rs.map (fun r : ℕ ↦ (r : ℝ)))
          (fun t ↦ -X / t) (A + i : ℕ) := by
  simp only [signedReciprocalDifference, forwardDifferences_cons]
  push_cast
  ring

lemma signedReciprocalDifference_gap_antitone
    (X : ℝ) (hX : 0 ≤ X) {A : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r) :
    Antitone (fun i ↦
      signedReciprocalDifference X A rs (i + 1) -
        signedReciprocalDifference X A rs i) := by
  apply antitone_nat_of_succ_le
  intro i
  by_cases hXzero : X = 0
  · subst X
    have hzero : forwardDifferences
        (rs.map (fun r : ℕ ↦ (r : ℝ))) (fun _ : ℝ ↦ 0) = fun _ ↦ 0 := by
      induction rs with
      | nil => rfl
      | cons r rs ih =>
          funext t
          simp only [List.map_cons, forwardDifferences_cons]
          rw [ih (fun s hs => hrs s (by simp [hs]))]
          simp
    simp [signedReciprocalDifference, hzero]
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hXzero)
    let shifts : List ℝ :=
      (1 : ℝ) :: (1 : ℝ) ::
        rs.map (fun r : ℕ ↦ (r : ℝ))
    have hshifts : ∀ r ∈ shifts, 0 < r := by
      intro r hr
      rw [show shifts = (1 : ℝ) :: (1 : ℝ) ::
        rs.map (fun r : ℕ ↦ (r : ℝ)) by rfl] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · norm_num
      · rcases List.mem_cons.mp hr with rfl | hr
        · norm_num
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact_mod_cast hrs s hs
    have ht : 0 < (((A + i : ℕ) : ℝ)) := by positivity
    obtain ⟨y, hty, hy, hfd⟩ :=
      exists_forwardDifferences_reciprocal_eq X shifts hshifts ht
    have hlen : shifts.length = rs.length + 2 := by simp [shifts]
    have hprod : shifts.prod = (rs.prod : ℝ) := by simp [shifts]
    have hsign := neg_one_pow_mul_add_two rs.length
    have hypos : 0 < y := ht.trans_le hty
    have hnonpos :
        ((-1 : ℝ) ^ rs.length) *
          (shifts.prod * reciprocalDeriv X shifts.length y) ≤ 0 := by
      rw [hlen, hprod]
      unfold reciprocalDeriv
      rw [show -1 - ((rs.length + 2 : ℕ) : ℤ) =
          -((rs.length + 3 : ℕ) : ℤ) by omega]
      rw [zpow_neg, zpow_natCast]
      rw [show ((-1 : ℝ) ^ rs.length) *
            ((rs.prod : ℝ) *
              (-X * (((-1 : ℝ) ^ (rs.length + 2)) *
                ((rs.length + 2).factorial : ℝ) *
                (y ^ (rs.length + 3))⁻¹))) =
          -(((-1 : ℝ) ^ rs.length) *
              ((-1 : ℝ) ^ (rs.length + 2))) *
            X * ((rs.length + 2).factorial : ℝ) *
            (rs.prod : ℝ) * (y ^ (rs.length + 3))⁻¹ by ring]
      rw [hsign]
      have hpos : 0 ≤ X * ((rs.length + 2).factorial : ℝ) *
          (rs.prod : ℝ) * (y ^ (rs.length + 3))⁻¹ := by positivity
      nlinarith
    have hchange := signedReciprocalDifference_gap_succ_sub X A rs i
    rw [← sub_nonpos]
    rw [show i + 1 + 1 = i + 2 by omega]
    rw [hchange, hfd]
    exact hnonpos

/-- The terminal correlation in the iterated moment argument is bounded by
the sharp first-derivative estimate. -/
theorem norm_terminal_reciprocal_correlation_le
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A)
    (rs : List ℕ) (hrs : ∀ r ∈ rs, 0 < r)
    (hN : rs.sum + 2 ≤ N)
    (hsmall : X * ((rs.length + 1).factorial : ℝ) *
        (rs.prod : ℝ) / (A : ℝ) ^ (rs.length + 2) ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc 1 (N - rs.sum),
        iteratedCorrelation rs
          (fun m ↦ e (-X / ((A + m : ℕ) : ℝ))) n‖ ≤
      1 + 3 / (2 *
        (X * ((rs.length + 1).factorial : ℝ) *
          (rs.prod : ℝ) /
            ((A + N : ℕ) : ℝ) ^ (rs.length + 2))) := by
  let M := N - rs.sum
  let m : ℝ := X * ((rs.length + 1).factorial : ℝ) *
    (rs.prod : ℝ) / ((A + N : ℕ) : ℝ) ^ (rs.length + 2)
  have hM : 2 ≤ M := by dsimp only [M]; omega
  have hm : 0 < m := by
    dsimp only [m]
    have hprod : 0 < rs.prod := List.prod_pos hrs
    positivity
  have hphase : ∀ i,
      iteratedCorrelation rs
          (fun q ↦ e (-X / ((A + q : ℕ) : ℝ))) (i + 1) =
        e (signedReciprocalDifference X A rs (i + 1)) :=
    fun i ↦ iteratedCorrelation_reciprocal_eq X A rs (i + 1)
  rw [sum_Icc_one_eq_sum_range]
  simp_rw [hphase]
  apply norm_sum_e_le_of_antitone_phaseDiff_sharp
    (fun i ↦ signedReciprocalDifference X A rs (i + 1)) M hM m hm
  · intro i hi
    dsimp only [m]
    apply signedReciprocalDifference_gap_lower X hX hA rs hrs
    dsimp only [M] at hi
    omega
  · intro i hi
    exact (signedReciprocalDifference_gap_upper X hX hA rs hrs (i + 1)).trans hsmall
  · have hanti := signedReciprocalDifference_gap_antitone X hX.le hA rs hrs
    intro i j hij
    exact hanti (by omega)

/-! ## Averaging the reciprocal products -/

/-- `IsShiftExtension Ls rs ss` means that `ss` is obtained from `rs` by
choosing, successively, a positive shift strictly below each cutoff in
`Ls`.  This is precisely the tree traversed by `terminalCorrelationMean`. -/
inductive IsShiftExtension : List ℕ → List ℕ → List ℕ → Prop
  | nil (rs : List ℕ) : IsShiftExtension [] rs rs
  | cons {L : ℕ} {Ls rs ss : List ℕ} {r : ℕ}
      (hr : r ∈ Finset.Icc 1 (L - 1))
      (hrest : IsShiftExtension Ls (r :: rs) ss) :
      IsShiftExtension (L :: Ls) rs ss

/-- The product of the normalized harmonic weights contributed by all
differencing layers. -/
def reciprocalShiftFactor : List ℕ → ℝ
  | [] => 1
  | L :: Ls =>
      ((1 / (L : ℝ)) *
        ∑ r ∈ Finset.Icc 1 (L - 1), (1 / (r : ℝ))) *
        reciprocalShiftFactor Ls

lemma reciprocalShiftFactor_nonneg (Ls : List ℕ) :
    0 ≤ reciprocalShiftFactor Ls := by
  induction Ls with
  | nil => simp [reciprocalShiftFactor]
  | cons L Ls ih =>
      simp only [reciprocalShiftFactor]
      positivity

lemma IsShiftExtension.length {Ls rs ss : List ℕ}
    (h : IsShiftExtension Ls rs ss) :
    ss.length = Ls.length + rs.length := by
  induction h with
  | nil => simp
  | cons hr hrest ih => simp at ih ⊢; omega

lemma IsShiftExtension.pos {Ls rs ss : List ℕ}
    (h : IsShiftExtension Ls rs ss)
    (hrs : ∀ r ∈ rs, 0 < r) : ∀ r ∈ ss, 0 < r := by
  induction h with
  | nil => exact hrs
  | @cons L Ls rs ss r hr hrest ih =>
      apply ih
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact (Finset.mem_Icc.mp hr).1
      · exact hrs s hs

lemma IsShiftExtension.sum_le {Ls rs ss : List ℕ}
    (h : IsShiftExtension Ls rs ss) :
    ss.sum ≤ Ls.sum + rs.sum := by
  induction h with
  | nil => simp
  | @cons L Ls rs ss r hr hrest ih =>
      simp only [List.sum_cons] at ih ⊢
      have hrL : r ≤ L := (Finset.mem_Icc.mp hr).2.trans (Nat.sub_le L 1)
      omega

lemma IsShiftExtension.prod_le {Ls rs ss : List ℕ}
    (h : IsShiftExtension Ls rs ss) :
    ss.prod ≤ Ls.prod * rs.prod := by
  induction h with
  | nil => simp
  | @cons L Ls rs ss r hr hrest ih =>
      simp only [List.prod_cons] at ih ⊢
      have hrL : r ≤ L := (Finset.mem_Icc.mp hr).2.trans (Nat.sub_le L 1)
      calc
        ss.prod ≤ Ls.prod * (r * rs.prod) := ih
        _ ≤ Ls.prod * (L * rs.prod) := by gcongr
        _ = L * Ls.prod * rs.prod := by ring

/-- An abstract averaging lemma.  A terminal estimate of the form
`a + b / ∏ shifts` averages exactly to the product of normalized harmonic
sums recorded by `reciprocalShiftFactor`. -/
theorem terminalCorrelationMean_le_of_leaf
    {u : ℕ → ℂ} {N : ℕ} {a b : ℝ} (Ls rs : List ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrs : ∀ r ∈ rs, 0 < r)
    (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hleaf : ∀ ss, IsShiftExtension Ls rs ss →
      correlationAverage u N ss ≤ a + b / (ss.prod : ℝ)) :
    terminalCorrelationMean u N Ls rs ≤
      a + b / (rs.prod : ℝ) * reciprocalShiftFactor Ls := by
  induction Ls generalizing rs with
  | nil =>
      simpa [terminalCorrelationMean, reciprocalShiftFactor] using
        hleaf rs (IsShiftExtension.nil rs)
  | cons L Ls ih =>
      have hL : 1 ≤ L := hcut L (by simp)
      have htail : ∀ K ∈ Ls, 1 ≤ K := by
        intro K hK
        exact hcut K (by simp [hK])
      have hchild : ∀ r ∈ Finset.Icc 1 (L - 1),
          terminalCorrelationMean u N Ls (r :: rs) ≤
            a + b / ((r :: rs).prod : ℝ) *
              reciprocalShiftFactor Ls := by
        intro r hr
        apply ih (r :: rs)
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact (Finset.mem_Icc.mp hr).1
          · exact hrs s hs
        · exact htail
        · intro ss hss
          exact hleaf ss (IsShiftExtension.cons hr hss)
      simp only [terminalCorrelationMean]
      have hsum := Finset.sum_le_sum hchild
      have hLreal : (0 : ℝ) < L := by exact_mod_cast (Nat.zero_lt_of_lt hL)
      have hrsprod : (0 : ℝ) < rs.prod := by
        exact_mod_cast List.prod_pos hrs
      calc
        (1 / (L : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              terminalCorrelationMean u N Ls (r :: rs) ≤
          (1 / (L : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (L - 1),
              (a + b / ((r :: rs).prod : ℝ) *
                reciprocalShiftFactor Ls) := by
            gcongr
        _ ≤ a + b / (rs.prod : ℝ) *
            (((1 / (L : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (L - 1), (1 / (r : ℝ))) *
              reciprocalShiftFactor Ls) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul, List.prod_cons,
            Nat.cast_mul]
          have hcard : ((Finset.Icc 1 (L - 1)).card : ℝ) ≤ L := by simp
          have hconst : (1 / (L : ℝ)) *
              (((Finset.Icc 1 (L - 1)).card : ℝ) * a) ≤ a := by
            rw [show (1 / (L : ℝ)) *
                (((Finset.Icc 1 (L - 1)).card : ℝ) * a) =
              (((Finset.Icc 1 (L - 1)).card : ℝ) / L) * a by ring]
            apply mul_le_of_le_one_left ha
            rw [div_le_one₀ hLreal]
            exact hcard
          have hrecip :
              (1 / (L : ℝ)) *
                  ∑ r ∈ Finset.Icc 1 (L - 1),
                    (b / ((r : ℝ) * (rs.prod : ℝ)) *
                      reciprocalShiftFactor Ls) =
                b / (rs.prod : ℝ) *
                  (((1 / (L : ℝ)) *
                    ∑ r ∈ Finset.Icc 1 (L - 1), (1 / (r : ℝ))) *
                    reciprocalShiftFactor Ls) := by
            rw [show (∑ r ∈ Finset.Icc 1 (L - 1),
                    (b / ((r : ℝ) * (rs.prod : ℝ)) *
                      reciprocalShiftFactor Ls)) =
                (b / (rs.prod : ℝ) * reciprocalShiftFactor Ls) *
                  ∑ r ∈ Finset.Icc 1 (L - 1), (1 / (r : ℝ)) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              have hrpos : (0 : ℝ) < r := by
                exact_mod_cast (Finset.mem_Icc.mp hr).1
              field_simp [ne_of_gt hrpos, ne_of_gt hrsprod]
              <;> ring]
            ring
          rw [mul_add, hrecip]
          exact add_le_add hconst le_rfl
        _ = a + b / (rs.prod : ℝ) *
            reciprocalShiftFactor (L :: Ls) := by
          rfl

/-- The averaged terminal bound for reciprocal phases.  The first term is
the normalized endpoint loss; the second retains the full harmonic saving
from the product of the chosen shifts. -/
theorem terminalCorrelationMean_reciprocal_le
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 1).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 2) ≤ 1 / 2) :
    terminalCorrelationMean
        (fun m ↦ e (-X / ((A + m : ℕ) : ℝ))) N Ls [] ≤
      1 / (8 * (N : ℝ)) +
        (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 2) /
          (16 * (N : ℝ) * X * ((Ls.length + 1).factorial : ℝ))) *
          reciprocalShiftFactor Ls := by
  let u : ℕ → ℂ := fun m ↦ e (-X / ((A + m : ℕ) : ℝ))
  let a : ℝ := 1 / (8 * (N : ℝ))
  let b : ℝ := 3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 2) /
    (16 * (N : ℝ) * X * ((Ls.length + 1).factorial : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hleaf : ∀ ss, IsShiftExtension Ls [] ss →
      correlationAverage u N ss ≤ a + b / (ss.prod : ℝ) := by
    intro ss hss
    have hlen : ss.length = Ls.length := by
      simpa using hss.length
    have hpos : ∀ r ∈ ss, 0 < r :=
      hss.pos (by simp)
    have hsum : ss.sum + 2 ≤ N := by
      have := hss.sum_le
      simp only [List.sum_nil, add_zero] at this
      omega
    have hprod : ss.prod ≤ Ls.prod := by
      have := hss.prod_le
      simpa using this
    have hsmallss :
        X * ((ss.length + 1).factorial : ℝ) *
            (ss.prod : ℝ) / (A : ℝ) ^ (ss.length + 2) ≤ 1 / 2 := by
      rw [hlen]
      calc
        X * ((Ls.length + 1).factorial : ℝ) *
              (ss.prod : ℝ) / (A : ℝ) ^ (Ls.length + 2) ≤
            X * ((Ls.length + 1).factorial : ℝ) *
              (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 2) := by
          gcongr
        _ ≤ 1 / 2 := hsmall
    have hnorm := norm_terminal_reciprocal_correlation_le
      X hX hA ss hpos hsum hsmallss
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hprodreal : (0 : ℝ) < ss.prod := by
      exact_mod_cast List.prod_pos hpos
    rw [correlationAverage]
    change
      ‖∑ n ∈ Finset.Icc 1 (N - ss.sum),
          iteratedCorrelation ss u n‖ / (8 * (N : ℝ)) ≤ a + b / (ss.prod : ℝ)
    calc
      ‖∑ n ∈ Finset.Icc 1 (N - ss.sum),
          iteratedCorrelation ss u n‖ / (8 * (N : ℝ)) ≤
        (1 + 3 / (2 *
          (X * ((ss.length + 1).factorial : ℝ) *
            (ss.prod : ℝ) /
              ((A + N : ℕ) : ℝ) ^ (ss.length + 2)))) /
          (8 * (N : ℝ)) := by
            apply div_le_div_of_nonneg_right
            · simpa only [u] using hnorm
            · positivity
      _ = a + b / (ss.prod : ℝ) := by
        dsimp only [a, b]
        rw [hlen]
        field_simp [ne_of_gt hNreal, ne_of_gt hX, ne_of_gt hprodreal]
        <;> ring
  have havg := terminalCorrelationMean_le_of_leaf
    (u := u) (N := N) (a := a) (b := b) Ls [] ha hb (by simp) hcut hleaf
  simpa only [u, a, b, List.prod_nil, Nat.cast_one, div_one, one_mul] using havg

/-- Higher-derivative reciprocal exponential-sum estimate with arbitrary
differencing cutoffs. -/
theorem reciprocal_exponential_sum_high_derivative
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 1).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 2) ≤ 1 / 2) :
    (‖∑ n ∈ Finset.Icc 1 N,
        e (-X / ((A + n : ℕ) : ℝ))‖ / (8 * (N : ℝ))) ^
        (2 ^ Ls.length) ≤
      vdcMomentConstant Ls.length *
        (differencingError Ls + 1 / (8 * (N : ℝ)) +
          (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 2) /
            (16 * (N : ℝ) * X * ((Ls.length + 1).factorial : ℝ))) *
            reciprocalShiftFactor Ls) := by
  let u : ℕ → ℂ := fun m ↦ e (-X / ((A + m : ℕ) : ℝ))
  have hu : ∀ n, ‖u n‖ ≤ 1 := by
    intro n
    simp [u]
  have hmoment := correlationAverage_pow_two_pow_le
    (u := u) (N := N) [] Ls hN (by simp; omega) hcut hu
  have hterm := terminalCorrelationMean_reciprocal_le
    X hX hA hN Ls hcut hfit hsmall
  have hC : 0 ≤ vdcMomentConstant Ls.length :=
    (vdcMomentConstant_pos Ls.length).le
  rw [correlationAverage] at hmoment
  simp only [List.sum_nil, Nat.sub_zero, List.length_nil, u] at hmoment
  exact hmoment.trans <| by
    apply mul_le_mul_of_nonneg_left _ hC
    linarith

lemma conj_e_eq_e_neg (x : ℝ) : conj (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I]
  have hreal : conj ((2 * Real.pi * x : ℝ) : ℂ) =
      ((2 * Real.pi * x : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [show ((2 : ℂ) * Real.pi * x) = ((2 * Real.pi * x : ℝ) : ℂ) by
    push_cast; rfl, hreal]
  push_cast
  ring

/-- Sign-reversed form, used for reciprocal product sums. -/
theorem reciprocal_exponential_sum_high_derivative_pos
    (X : ℝ) (hX : 0 < X) {A N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (Ls : List ℕ) (hcut : ∀ L ∈ Ls, 1 ≤ L)
    (hfit : Ls.sum + 2 ≤ N)
    (hsmall : X * ((Ls.length + 1).factorial : ℝ) *
        (Ls.prod : ℝ) / (A : ℝ) ^ (Ls.length + 2) ≤ 1 / 2) :
    (‖∑ n ∈ Finset.Icc 1 N,
        e (X / ((A + n : ℕ) : ℝ))‖ / (8 * (N : ℝ))) ^
        (2 ^ Ls.length) ≤
      vdcMomentConstant Ls.length *
        (differencingError Ls + 1 / (8 * (N : ℝ)) +
          (3 * ((A + N : ℕ) : ℝ) ^ (Ls.length + 2) /
            (16 * (N : ℝ) * X * ((Ls.length + 1).factorial : ℝ))) *
            reciprocalShiftFactor Ls) := by
  have hbase := reciprocal_exponential_sum_high_derivative
    X hX hA hN Ls hcut hfit hsmall
  have hconj :
      conj (∑ n ∈ Finset.Icc 1 N,
        e (-X / ((A + n : ℕ) : ℝ))) =
        ∑ n ∈ Finset.Icc 1 N,
          e (X / ((A + n : ℕ) : ℝ)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [conj_e_eq_e_neg]
    congr 1
    ring
  rw [← hconj, Complex.norm_conj]
  exact hbase

end

end HigherDerivative
end Erdos378
