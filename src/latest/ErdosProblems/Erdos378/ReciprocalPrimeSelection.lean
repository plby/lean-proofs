/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.ReciprocalPrimeWindow
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Reciprocal cancellation on the Granville--Ramaré prime window

The required window `(sqrt k, (10/9)sqrt k]` is obtained by subtracting two
intervals with common upper endpoint `2 sqrt k`.  This permits the existing
quadratic-frequency Vaughan estimate to handle the three Fourier modes in
the elementary degree-three minorant used below.
-/

open Filter
open scoped Topology BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace ReciprocalPrimeSelection

open PrimeReciprocal
open ReciprocalExponential
open VaughanReciprocalFull
open ReciprocalChebyshevAsymptotic
open ReciprocalPrimeWindow

noncomputable section

def sourcePrimeUpper (k : ℕ) : ℕ := 10 * Nat.sqrt k / 9

private lemma weightedChebyshevInterval_add
    (w : ℕ → ℂ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    weightedChebyshevInterval w a b + weightedChebyshevInterval w b c =
      weightedChebyshevInterval w a c := by
  unfold weightedChebyshevInterval
  rw [← Finset.sum_union]
  · rw [Finset.Ioc_union_Ioc_eq_Ioc hab hbc]
  · rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    have h₁ := Finset.mem_Ioc.mp hn₁
    have h₂ := Finset.mem_Ioc.mp hn₂
    omega

theorem norm_weightedChebyshev_source_window_le
    {k h : ℕ} (hslarge : 4 * 16384 ^ 2 ≤ Nat.sqrt k)
    (hhpos : 0 < h) (hh : h ≤ 3)
    (hsize : 16 * reciprocalDifferencingLength (2 * Nat.sqrt k) *
      ((reciprocalVaughanCutoff (2 * Nat.sqrt k)) ^ 2) ^ 2 ≤ Nat.sqrt k) :
    ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ))
        (Nat.sqrt k) (sourcePrimeUpper k)‖ ≤
      2 * reciprocalChebyshevMajorant (2 * Nat.sqrt k)
        (reciprocalVaughanCutoff (2 * Nat.sqrt k))
        (reciprocalDifferencingLength (2 * Nat.sqrt k)) := by
  let s := Nat.sqrt k
  let u := sourcePrimeUpper k
  let y := 2 * s
  let T := reciprocalVaughanCutoff y
  let L := reciprocalDifferencingLength y
  have hs : 7 ≤ s := by omega
  have hsu : s ≤ u := by
    dsimp only [u, sourcePrimeUpper]
    omega
  have huy : u ≤ y := by
    dsimp only [u, y, sourcePrimeUpper]
    omega
  have hkpos : 0 < k := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      ((show 1 ≤ s by omega).trans (by simpa only [s] using Nat.sqrt_le_self k))
  have hXpos : 0 < (h * k : ℕ) := Nat.mul_pos hhpos hkpos
  have hT : 0 < T := reciprocalVaughanCutoff_pos y
  have hL : 2 ≤ L := by
    unfold L reciprocalDifferencingLength
    have hfloor : 1 ≤ Nat.floor (Real.sqrt (y : ℝ)) := by
      apply Nat.le_floor
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast (show 1 ≤ y by omega)
    omega
  have hTx : T ≤ s := by
    have hsize' : 16 * L * T ^ 4 ≤ s := by
      calc
        16 * L * T ^ 4 = 16 * L * (T ^ 2) ^ 2 := by ring
        _ ≤ s := by simpa only [s, y, T, L] using hsize
    calc
      T ≤ T ^ 4 := le_self_pow₀ (by omega) (by norm_num)
      _ ≤ 16 * L * T ^ 4 := by
        have : 1 ≤ 16 * L := by omega
        nlinarith
      _ ≤ s := hsize'
  have hTy : T ≤ y := hTx.trans (by omega)
  have hsSq : s ^ 2 ≤ k := by
    simpa [s, pow_two] using Nat.sqrt_le k
  have hXlo : ((y : ℝ) ^ 2) ≤ 4 * ((h * k : ℕ) : ℝ) := by
    have hnat : y ^ 2 ≤ 4 * (h * k) := by
      dsimp only [y]
      nlinarith
    exact_mod_cast hnat
  have hklt : k < (s + 1) ^ 2 := by
    simpa only [s, pow_two] using Nat.lt_succ_sqrt k
  have hXhi : (((h * k : ℕ) : ℝ)) ≤ (y : ℝ) ^ 2 := by
    have hnat : h * k ≤ y ^ 2 := by
      have : 3 * k ≤ 4 * s ^ 2 := by nlinarith
      dsimp only [y]
      nlinarith
    exact_mod_cast hnat
  have hbig :
      ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ)) s y‖ ≤
        reciprocalChebyshevMajorant y T L := by
    apply norm_weightedChebyshevInterval_reciprocal_le
      (X := ((h * k : ℕ) : ℝ)) (x := s) (y := y) (T := T) (L := L)
    · exact_mod_cast hXpos
    · exact hT
    · exact hTy
    · exact hTx
    · exact hL
    · simpa only [s, y, T, L] using hsize
    · simpa only [s] using hslarge
    · exact hXlo
    · exact hXhi
    · dsimp only [y]
      omega
  have htail :
      ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ)) u y‖ ≤
        reciprocalChebyshevMajorant y T L := by
    apply norm_weightedChebyshevInterval_reciprocal_le
      (X := ((h * k : ℕ) : ℝ)) (x := u) (y := y) (T := T) (L := L)
    · exact_mod_cast hXpos
    · exact hT
    · exact hTy
    · exact hTx.trans hsu
    · exact hL
    · exact (by simpa only [s, y, T, L] using hsize.trans hsu)
    · simpa only [s] using hslarge.trans hsu
    · exact hXlo
    · exact hXhi
    · omega
  have hsplit := weightedChebyshevInterval_add
    (reciprocalWeight ((h * k : ℕ) : ℝ)) hsu huy
  have heq : weightedChebyshevInterval
      (reciprocalWeight ((h * k : ℕ) : ℝ)) s u =
        weightedChebyshevInterval
          (reciprocalWeight ((h * k : ℕ) : ℝ)) s y -
      weightedChebyshevInterval
          (reciprocalWeight ((h * k : ℕ) : ℝ)) u y := by
    rw [eq_sub_iff_add_eq]
    exact hsplit
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

theorem tendsto_norm_weightedChebyshev_source_window_div
    {h : ℕ} (hhpos : 0 < h) (hh : h ≤ 3) :
    Tendsto (fun k : ℕ ↦
      ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ))
        (Nat.sqrt k) (sourcePrimeUpper k)‖ / (Nat.sqrt k : ℝ))
      atTop (nhds 0) := by
  let F : ℕ → ℝ := fun k ↦
    ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ))
      (Nat.sqrt k) (sourcePrimeUpper k)‖ / (Nat.sqrt k : ℝ)
  let E : ℕ → ℝ := fun k ↦
    4 * (reciprocalChebyshevMajorant (2 * Nat.sqrt k)
      (reciprocalVaughanCutoff (2 * Nat.sqrt k))
      (reciprocalDifferencingLength (2 * Nat.sqrt k)) /
        (2 * Nat.sqrt k : ℕ))
  have hE : Tendsto E atTop (nhds 0) := by
    dsimp only [E]
    simpa using tendsto_reciprocal_sqrt_window_majorant.const_mul 4
  have hsTop : Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b ^ 2, fun a ha ↦ Nat.le_sqrt'.mpr ha⟩
  have hlarge : ∀ᶠ k : ℕ in atTop, 4 * 16384 ^ 2 ≤ Nat.sqrt k :=
    hsTop.eventually (eventually_ge_atTop (4 * 16384 ^ 2))
  have hparam : ∀ᶠ k : ℕ in atTop,
      16 * reciprocalDifferencingLength (2 * Nat.sqrt k) *
        ((reciprocalVaughanCutoff (2 * Nat.sqrt k)) ^ 2) ^ 2 ≤ Nat.sqrt k := by
    have hp := tendsto_two_mul_sqrt.eventually eventually_reciprocal_parameters_size
    filter_upwards [hp] with k hk
    simpa using hk
  have hnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ F k := by
    filter_upwards with k
    exact div_nonneg (norm_nonneg _) (by positivity)
  have hbound : ∀ᶠ k : ℕ in atTop, F k ≤ E k := by
    filter_upwards [hlarge, hparam] with k hklarge hksize
    have hspos : 0 < Nat.sqrt k := by omega
    have hmain := norm_weightedChebyshev_source_window_le
      hklarge hhpos hh hksize
    dsimp only [F, E]
    calc
      _ ≤ (2 * reciprocalChebyshevMajorant (2 * Nat.sqrt k)
          (reciprocalVaughanCutoff (2 * Nat.sqrt k))
          (reciprocalDifferencingLength (2 * Nat.sqrt k))) /
            (Nat.sqrt k : ℝ) :=
        div_le_div_of_nonneg_right hmain (by positivity)
      _ = 4 * (reciprocalChebyshevMajorant (2 * Nat.sqrt k)
          (reciprocalVaughanCutoff (2 * Nat.sqrt k))
          (reciprocalDifferencingLength (2 * Nat.sqrt k)) /
            (2 * Nat.sqrt k : ℕ)) := by
        push_cast
        field_simp
        ring
  exact squeeze_zero' hnonneg hbound hE

/-! ## The explicit degree-three minorant -/

noncomputable def sourceMinorant (t : ℝ) : ℝ :=
  (1 / 8 : ℝ) *
    (1 + 3 * Real.cos t + 3 * Real.cos (2 * t) + Real.cos (3 * t))

lemma sourceMinorant_factor (t : ℝ) :
    sourceMinorant t =
      (1 / 2 : ℝ) * (Real.cos t - 1 / 2) * (Real.cos t + 1) ^ 2 := by
  unfold sourceMinorant
  rw [Real.cos_two_mul, Real.cos_three_mul]
  ring

lemma e_re (x : ℝ) : (e x).re = Real.cos (2 * Real.pi * x) := by
  unfold e
  rw [Complex.exp_re]
  simp

lemma shifted_reciprocalWeight_re (h k p : ℕ) (hp : 0 < p) :
    (e ((5 : ℝ) * h / 6) *
        reciprocalWeight ((h * k : ℕ) : ℝ) p).re =
      Real.cos (h * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))) := by
  unfold reciprocalWeight
  rw [← e_add]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  rw [show (5 : ℝ) * h / 6 + -((h * k : ℕ) : ℝ) / p =
      -(h * ((k : ℝ) / p - 5 / 6)) by
    push_cast
    field_simp
    ring]
  rw [e_re]
  rw [show 2 * Real.pi * (-(h * ((k : ℝ) / p - 5 / 6))) =
      -(h * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))) by ring,
    Real.cos_neg]

lemma reciprocal_phase_cos_eq_mod (h k p : ℕ) (hp : 0 < p) (hpk : p ≤ k) :
    Real.cos (h * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))) =
      Real.cos (h *
        (2 * Real.pi * (((k % p : ℕ) : ℝ) / p + 1 / 6))) := by
  have hq : 1 ≤ k / p :=
    (Nat.le_div_iff_mul_le hp).2 (by simpa using hpk)
  have hkdecomp : k = (k / p) * p + k % p := by
    simpa [mul_comm] using (Nat.div_add_mod k p).symm
  have hkquot : (k : ℝ) / p =
      (k / p : ℕ) + (k % p : ℕ) / (p : ℝ) := by
    have hpR : (p : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    exact_mod_cast (show k = p * (k / p) + k % p by
      simpa [mul_comm] using hkdecomp)
  rw [hkquot]
  rw [show h * (2 * Real.pi *
      (((k / p : ℕ) : ℝ) + ((k % p : ℕ) : ℝ) / p - 5 / 6)) =
      h * (2 * Real.pi * (((k % p : ℕ) : ℝ) / p + 1 / 6)) +
        (h * (k / p - 1) : ℕ) * (2 * Real.pi) by
    have hqcast : (((k / p : ℕ) : ℝ)) =
        ((k / p - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show k / p = (k / p - 1) + 1 by omega)
    rw [hqcast]
    push_cast
    ring]
  exact Real.cos_add_nat_mul_two_pi _ _

lemma source_arc_cos_le {p r : ℕ} (hp : 0 < p)
    (hout : 3 * r < 2 * p) :
    Real.cos (2 * Real.pi * (((r : ℕ) : ℝ) / p + 1 / 6)) ≤ 1 / 2 := by
  let phi : ℝ := 2 * Real.pi * ((r : ℝ) / p + 1 / 6)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpi : 0 < Real.pi := Real.pi_pos
  have hphiLo : Real.pi / 3 ≤ phi := by
    dsimp only [phi]
    have hr0 : (0 : ℝ) ≤ r := by positivity
    have : 0 ≤ (r : ℝ) / p := div_nonneg hr0 hpR.le
    nlinarith
  have houtR : (3 : ℝ) * r ≤ 2 * p := by exact_mod_cast hout.le
  have hfrac : (r : ℝ) / p ≤ 2 / 3 := by
    rw [div_le_iff₀ hpR]
    nlinarith
  have hphiHi : phi ≤ 5 * Real.pi / 3 := by
    dsimp only [phi]
    have hadd : (r : ℝ) / p + 1 / 6 ≤ 5 / 6 := by linarith
    have := mul_le_mul_of_nonneg_left hadd
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    nlinarith
  by_cases hmid : phi ≤ Real.pi
  · rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hmid hphiLo
  · have hpile : Real.pi ≤ phi := (lt_of_not_ge hmid).le
    have hpsi0 : 0 ≤ 2 * Real.pi - phi := by linarith
    have hpsipi : 2 * Real.pi - phi ≤ Real.pi := by linarith
    have hlo : Real.pi / 3 ≤ 2 * Real.pi - phi := by linarith
    rw [← Real.cos_pi_div_three, ← Real.cos_two_pi_sub phi]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpsipi hlo

lemma sourceMinorant_nonpos {t : ℝ} (hcos : Real.cos t ≤ 1 / 2) :
    sourceMinorant t ≤ 0 := by
  rw [sourceMinorant_factor]
  have hdiff : Real.cos t - 1 / 2 ≤ 0 := sub_nonpos.mpr hcos
  have hs : 0 ≤ (Real.cos t + 1) ^ 2 := sq_nonneg _
  have hm : (Real.cos t - 1 / 2) * (Real.cos t + 1) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hdiff hs
  nlinarith

lemma sourceMinorant_le_one (t : ℝ) : sourceMinorant t ≤ 1 := by
  rw [sourceMinorant_factor]
  have hc := Real.neg_one_le_cos t
  have hc' := Real.cos_le_one t
  by_cases h : Real.cos t ≤ 1 / 2
  · have hdiff : Real.cos t - 1 / 2 ≤ 0 := sub_nonpos.mpr h
    have hs : 0 ≤ (Real.cos t + 1) ^ 2 := sq_nonneg _
    nlinarith
  · have hdiff : 0 ≤ Real.cos t - 1 / 2 :=
      sub_nonneg.mpr (le_of_not_ge h)
    have hdiff' : Real.cos t - 1 / 2 ≤ 1 / 2 := by linarith
    have hadd : 0 ≤ Real.cos t + 1 := by linarith
    have hadd' : Real.cos t + 1 ≤ 2 := by linarith
    have hsq : (Real.cos t + 1) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul hdiff' hsq (sq_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]

lemma abs_sourceMinorant_le_one (t : ℝ) : |sourceMinorant t| ≤ 1 := by
  unfold sourceMinorant
  have h1 : |Real.cos t| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have h2 : |Real.cos (2 * t)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have h3 : |Real.cos (3 * t)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  rw [abs_mul]
  norm_num
  have hsum :
      |1 + 3 * Real.cos t + 3 * Real.cos (2 * t) + Real.cos (3 * t)| ≤
        |1| + |3 * Real.cos t| + |3 * Real.cos (2 * t)| +
          |Real.cos (3 * t)| := by
    calc
      _ ≤ |1 + 3 * Real.cos t + 3 * Real.cos (2 * t)| +
          |Real.cos (3 * t)| := abs_add_le _ _
      _ ≤ (|1 + 3 * Real.cos t| + |3 * Real.cos (2 * t)|) +
          |Real.cos (3 * t)| := by gcongr; exact abs_add_le _ _
      _ ≤ (|1| + |3 * Real.cos t| + |3 * Real.cos (2 * t)|) +
          |Real.cos (3 * t)| := by gcongr; exact abs_add_le _ _
  have hsum8 :
      |1 + 3 * Real.cos t + 3 * Real.cos (2 * t) + Real.cos (3 * t)| ≤ 8 := by
    calc
      _ ≤ |1| + |3 * Real.cos t| + |3 * Real.cos (2 * t)| +
          |Real.cos (3 * t)| := hsum
      _ ≤ 8 := by
        rw [abs_mul, abs_mul]
        norm_num at h1 h2 h3 ⊢
        linarith
  nlinarith

/-! ## Removing prime powers -/

def primeReciprocalInterval (X : ℝ) (a b : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * reciprocalWeight X p

private lemma weightedChebyshevInterval_eq_prime_add_nonprime
    (X : ℝ) (a b : ℕ) :
    weightedChebyshevInterval (reciprocalWeight X) a b =
      primeReciprocalInterval X a b +
        ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
          (ArithmeticFunction.vonMangoldt n : ℂ) * reciprocalWeight X n := by
  unfold weightedChebyshevInterval primeReciprocalInterval
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc a b) (fun n : ℕ ↦ n.Prime)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact congrArg (fun z : ℝ ↦ (z : ℂ) * reciprocalWeight X p)
    (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2)

lemma norm_primeReciprocalInterval_sub_weighted_le
    (X : ℝ) (a b : ℕ) :
    ‖primeReciprocalInterval X a b -
        weightedChebyshevInterval (reciprocalWeight X) a b‖ ≤
      Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ) := by
  rw [weightedChebyshevInterval_eq_prime_add_nonprime]
  simp only [sub_add_cancel_left, norm_neg]
  calc
    ‖∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * reciprocalWeight X n‖ ≤
      ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * reciprocalWeight X n‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.norm_mul, norm_reciprocalWeight, mul_one,
        Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    _ ≤ ∑ n ∈ (Finset.Ioc 0 b).filter (fun n : ℕ ↦ ¬n.Prime),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hnab, hnprime⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hnab).1,
            (Finset.mem_Ioc.mp hnab).2⟩, hnprime⟩
      · intro n hn hnnot
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp

lemma norm_primeReciprocalInterval_le
    {X : ℝ} {a b : ℕ} {R : ℝ}
    (hcheb : ‖weightedChebyshevInterval (reciprocalWeight X) a b‖ ≤ R) :
    ‖primeReciprocalInterval X a b‖ ≤
      R + (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) := by
  have hdiff := norm_primeReciprocalInterval_sub_weighted_le X a b
  have hdecomp : primeReciprocalInterval X a b =
      (primeReciprocalInterval X a b -
        weightedChebyshevInterval (reciprocalWeight X) a b) +
          weightedChebyshevInterval (reciprocalWeight X) a b := by ring
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hdiff hcheb) |>.trans (by linarith)

/-! ## Asymptotic removal of prime powers -/

private theorem tendsto_natSqrt_atTop :
    Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b ^ 2, fun a ha ↦ Nat.le_sqrt'.mpr ha⟩

theorem tendsto_sourcePrimeUpper_atTop :
    Tendsto sourcePrimeUpper atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨(9 * max b 1) ^ 2, ?_⟩
  intro k hk
  have hs : 9 * max b 1 ≤ Nat.sqrt k := Nat.le_sqrt'.mpr hk
  unfold sourcePrimeUpper
  omega

private theorem tendsto_chebyshevPsi_nat_ratio :
    Tendsto (fun n : ℕ ↦ Chebyshev.psi (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
    BoundedGaps.PrimeNumberTheorem.chebyshevPsi_natCast_isEquivalent
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast (show n ≠ 0 by omega)

private theorem tendsto_chebyshevTheta_nat_ratio :
    Tendsto (fun n : ℕ ↦ Chebyshev.theta (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
    BoundedGaps.PrimeNumberTheorem.chebyshevTheta_natCast_isEquivalent
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast (show n ≠ 0 by omega)

theorem tendsto_psi_sub_theta_sourcePrimeUpper_div_sqrt :
    Tendsto (fun k : ℕ ↦
      (Chebyshev.psi (sourcePrimeUpper k : ℝ) -
          Chebyshev.theta (sourcePrimeUpper k : ℝ)) / (Nat.sqrt k : ℝ))
      atTop (nhds 0) := by
  let u : ℕ → ℕ := sourcePrimeUpper
  let s : ℕ → ℕ := fun k ↦ Nat.sqrt k
  let D : ℕ → ℝ := fun k ↦
    Chebyshev.psi (u k : ℝ) / (u k : ℝ) -
      Chebyshev.theta (u k : ℝ) / (u k : ℝ)
  have huTop : Tendsto u atTop atTop := tendsto_sourcePrimeUpper_atTop
  have hsTop : Tendsto s atTop atTop := tendsto_natSqrt_atTop
  have hD : Tendsto D atTop (nhds 0) := by
    have hpsi := tendsto_chebyshevPsi_nat_ratio.comp huTop
    have htheta := tendsto_chebyshevTheta_nat_ratio.comp huTop
    simpa only [D, Function.comp_apply, sub_self] using hpsi.sub htheta
  have hE : Tendsto (fun k ↦ 2 * |D k|) atTop (nhds 0) := by
    simpa using (hD.abs.const_mul 2)
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < s k :=
    hsTop.eventually (eventually_gt_atTop 0)
  have hnonneg : ∀ᶠ k : ℕ in atTop,
      0 ≤ (Chebyshev.psi (u k : ℝ) - Chebyshev.theta (u k : ℝ)) /
        (s k : ℝ) := by
    filter_upwards [hpos] with k hsk
    exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) (by positivity)
  have hbound : ∀ᶠ k : ℕ in atTop,
      (Chebyshev.psi (u k : ℝ) - Chebyshev.theta (u k : ℝ)) /
          (s k : ℝ) ≤ 2 * |D k| := by
    filter_upwards [hpos, huTop.eventually (eventually_gt_atTop 0)] with k hsk huk
    have hus : u k ≤ 2 * s k := by
      dsimp only [u, s, sourcePrimeUpper]
      omega
    have hsR : (0 : ℝ) < s k := by exact_mod_cast hsk
    have huR : (0 : ℝ) < u k := by exact_mod_cast huk
    have huratio : (u k : ℝ) / (s k : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hsR]
      exact_mod_cast hus
    have hrewrite :
        (Chebyshev.psi (u k : ℝ) - Chebyshev.theta (u k : ℝ)) /
            (s k : ℝ) = D k * ((u k : ℝ) / (s k : ℝ)) := by
      dsimp only [D]
      field_simp [ne_of_gt hsR, ne_of_gt huR]
    rw [hrewrite]
    have hDnonneg : 0 ≤ D k := by
      dsimp only [D]
      rw [div_sub_div_same]
      exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)) huR.le
    calc
      D k * ((u k : ℝ) / (s k : ℝ)) ≤ D k * 2 :=
        mul_le_mul_of_nonneg_left huratio hDnonneg
      _ ≤ 2 * |D k| := by rw [abs_of_nonneg hDnonneg, mul_comm]
  exact squeeze_zero' hnonneg hbound hE

theorem tendsto_norm_primeReciprocal_source_window_div
    {h : ℕ} (hhpos : 0 < h) (hh : h ≤ 3) :
    Tendsto (fun k : ℕ ↦
      ‖primeReciprocalInterval ((h * k : ℕ) : ℝ)
        (Nat.sqrt k) (sourcePrimeUpper k)‖ / (Nat.sqrt k : ℝ))
      atTop (nhds 0) := by
  let P : ℕ → ℝ := fun k ↦
    ‖primeReciprocalInterval ((h * k : ℕ) : ℝ)
      (Nat.sqrt k) (sourcePrimeUpper k)‖ / (Nat.sqrt k : ℝ)
  let E : ℕ → ℝ := fun k ↦
    ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ))
        (Nat.sqrt k) (sourcePrimeUpper k)‖ / (Nat.sqrt k : ℝ) +
      (Chebyshev.psi (sourcePrimeUpper k : ℝ) -
        Chebyshev.theta (sourcePrimeUpper k : ℝ)) / (Nat.sqrt k : ℝ)
  have hE : Tendsto E atTop (nhds 0) := by
    simpa only [E, zero_add] using
      (tendsto_norm_weightedChebyshev_source_window_div hhpos hh).add
        tendsto_psi_sub_theta_sourcePrimeUpper_div_sqrt
  have hspos : ∀ᶠ k : ℕ in atTop, 0 < Nat.sqrt k :=
    tendsto_natSqrt_atTop.eventually (eventually_gt_atTop 0)
  have hnonneg : ∀ᶠ k : ℕ in atTop, 0 ≤ P k := by
    filter_upwards [hspos] with k hk
    exact div_nonneg (norm_nonneg _) (by positivity)
  have hbound : ∀ᶠ k : ℕ in atTop, P k ≤ E k := by
    filter_upwards [hspos] with k hk
    dsimp only [P, E]
    have hsR : (0 : ℝ) ≤ Nat.sqrt k := by positivity
    have hmain := norm_primeReciprocalInterval_le
      (X := ((h * k : ℕ) : ℝ)) (a := Nat.sqrt k)
      (b := sourcePrimeUpper k) (R :=
        ‖weightedChebyshevInterval (reciprocalWeight ((h * k : ℕ) : ℝ))
          (Nat.sqrt k) (sourcePrimeUpper k)‖) le_rfl
    calc
      _ ≤ (‖weightedChebyshevInterval
          (reciprocalWeight ((h * k : ℕ) : ℝ)) (Nat.sqrt k)
            (sourcePrimeUpper k)‖ +
          (Chebyshev.psi (sourcePrimeUpper k : ℝ) -
            Chebyshev.theta (sourcePrimeUpper k : ℝ))) / (Nat.sqrt k : ℝ) :=
        div_le_div_of_nonneg_right hmain hsR
      _ = _ := by ring
  exact squeeze_zero' hnonneg hbound hE

/-! ## A positive logarithmic mass of selected primes -/

def sourcePrimeSet (k : ℕ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt k) (sourcePrimeUpper k)).filter Nat.Prime

def sourcePrimeLogMass (k : ℕ) : ℝ :=
  ∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ)

def sourcePrimeMode (h k : ℕ) : ℂ :=
  e ((5 : ℝ) * h / 6) *
    primeReciprocalInterval ((h * k : ℕ) : ℝ)
      (Nat.sqrt k) (sourcePrimeUpper k)

def sourcePrimeMinorantSum (k : ℕ) : ℝ :=
  ∑ p ∈ sourcePrimeSet k,
    Real.log (p : ℝ) *
      sourceMinorant (2 * Real.pi * ((k : ℝ) / p - 5 / 6))

private lemma primeLogInterval_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log (p : ℝ)) +
      ∑ p ∈ (Finset.Ioc b c).filter Nat.Prime, Real.log (p : ℝ) =
        ∑ p ∈ (Finset.Ioc a c).filter Nat.Prime, Real.log (p : ℝ) := by
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_union]
  · rw [Finset.Ioc_union_Ioc_eq_Ioc hab hbc]
  · rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h₁ := Finset.mem_Ioc.mp hp₁
    have h₂ := Finset.mem_Ioc.mp hp₂
    omega

lemma sourcePrimeLogMass_eq_theta_sub (k : ℕ) :
    sourcePrimeLogMass k =
      Chebyshev.theta (sourcePrimeUpper k : ℝ) -
        Chebyshev.theta (Nat.sqrt k : ℝ) := by
  have hsu : Nat.sqrt k ≤ sourcePrimeUpper k := by
    unfold sourcePrimeUpper
    omega
  have hadd := primeLogInterval_add (a := 0) (b := Nat.sqrt k)
    (c := sourcePrimeUpper k) (Nat.zero_le _) hsu
  unfold sourcePrimeLogMass sourcePrimeSet Chebyshev.theta
  simp only [Nat.floor_natCast]
  linarith

theorem eventually_sourcePrimeLogMass_lower :
    ∀ᶠ k : ℕ in atTop,
      (Nat.sqrt k : ℝ) / 20 ≤ sourcePrimeLogMass k := by
  let s : ℕ → ℕ := fun k ↦ Nat.sqrt k
  let u : ℕ → ℕ := sourcePrimeUpper
  have hsTop : Tendsto s atTop atTop := tendsto_natSqrt_atTop
  have huTop : Tendsto u atTop atTop := tendsto_sourcePrimeUpper_atTop
  have hsTheta := tendsto_chebyshevTheta_nat_ratio.comp hsTop
  have huTheta := tendsto_chebyshevTheta_nat_ratio.comp huTop
  have hsClose : ∀ᶠ k : ℕ in atTop,
      |Chebyshev.theta (s k : ℝ) / (s k : ℝ) - 1| < 1 / 1000 :=
    hsTheta.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  have huClose : ∀ᶠ k : ℕ in atTop,
      |Chebyshev.theta (u k : ℝ) / (u k : ℝ) - 1| < 1 / 1000 :=
    huTheta.eventually (Metric.ball_mem_nhds 1 (by norm_num))
  filter_upwards [hsClose, huClose,
    hsTop.eventually (eventually_ge_atTop 90)] with k hsC huC hsk
  have hspos : (0 : ℝ) < s k := by positivity
  have huposNat : 0 < u k := by
    dsimp only [u, sourcePrimeUpper, s] at *
    omega
  have hupos : (0 : ℝ) < u k := by exact_mod_cast huposNat
  have husNat : 11 * s k ≤ 10 * u k := by
    dsimp only [u, sourcePrimeUpper, s] at *
    omega
  have hus : (11 : ℝ) / 10 * s k ≤ u k := by
    have husR : ((11 * s k : ℕ) : ℝ) ≤ ((10 * u k : ℕ) : ℝ) := by
      exact_mod_cast husNat
    push_cast at husR
    linarith
  have hsRatio := (abs_lt.mp hsC).2
  have huRatio := (abs_lt.mp huC).1
  have hsUpper : Chebyshev.theta (s k : ℝ) ≤
      (1001 / 1000 : ℝ) * s k := by
    have hratio : Chebyshev.theta (s k : ℝ) / (s k : ℝ) <
        (1001 / 1000 : ℝ) := by linarith
    have hmul := (div_lt_iff₀ hspos).mp hratio
    linarith
  have huLower : (999 / 1000 : ℝ) * u k ≤
      Chebyshev.theta (u k : ℝ) := by
    have hratio : (999 / 1000 : ℝ) <
        Chebyshev.theta (u k : ℝ) / (u k : ℝ) := by linarith
    exact ((lt_div_iff₀ hupos).mp hratio).le
  rw [sourcePrimeLogMass_eq_theta_sub]
  dsimp only [s, u] at *
  nlinarith

lemma norm_sourcePrimeMode (h k : ℕ) :
    ‖sourcePrimeMode h k‖ =
      ‖primeReciprocalInterval ((h * k : ℕ) : ℝ)
        (Nat.sqrt k) (sourcePrimeUpper k)‖ := by
  unfold sourcePrimeMode
  rw [norm_mul, norm_e, one_mul]

theorem tendsto_norm_sourcePrimeMode_div
    {h : ℕ} (hhpos : 0 < h) (hh : h ≤ 3) :
    Tendsto (fun k : ℕ ↦ ‖sourcePrimeMode h k‖ / (Nat.sqrt k : ℝ))
      atTop (nhds 0) := by
  simpa only [norm_sourcePrimeMode] using
    tendsto_norm_primeReciprocal_source_window_div hhpos hh

lemma sourcePrimeMode_re (h k : ℕ) :
    (sourcePrimeMode h k).re =
      ∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
        Real.cos (h * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))) := by
  unfold sourcePrimeMode primeReciprocalInterval sourcePrimeSet
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show e (5 * (h : ℝ) / 6) *
      ((Real.log (p : ℝ) : ℂ) * reciprocalWeight ((h * k : ℕ) : ℝ) p) =
        (Real.log (p : ℝ) : ℂ) *
          (e (5 * (h : ℝ) / 6) * reciprocalWeight ((h * k : ℕ) : ℝ) p) by
    ring]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact shifted_reciprocalWeight_re h k p (Finset.mem_filter.mp hp).2.pos

lemma sourcePrimeMinorantSum_eq_modes (k : ℕ) :
    sourcePrimeMinorantSum k =
      (1 / 8 : ℝ) * (sourcePrimeLogMass k +
        3 * (sourcePrimeMode 1 k).re +
        3 * (sourcePrimeMode 2 k).re + (sourcePrimeMode 3 k).re) := by
  unfold sourcePrimeMinorantSum sourceMinorant
  calc
    (∑ p ∈ sourcePrimeSet k,
        Real.log (p : ℝ) *
          ((1 / 8 : ℝ) *
            (1 + 3 * Real.cos (2 * Real.pi * ((k : ℝ) / p - 5 / 6)) +
              3 * Real.cos (2 * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))) +
              Real.cos (3 * (2 * Real.pi * ((k : ℝ) / p - 5 / 6)))))) =
      (1 / 8 : ℝ) *
        ((∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ)) +
          3 * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
            Real.cos (1 * (2 * Real.pi * ((k : ℝ) / p - 5 / 6)))) +
          3 * (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
            Real.cos (2 * (2 * Real.pi * ((k : ℝ) / p - 5 / 6)))) +
          (∑ p ∈ sourcePrimeSet k, Real.log (p : ℝ) *
            Real.cos (3 * (2 * Real.pi * ((k : ℝ) / p - 5 / 6))))) := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring_nf
    _ = _ := by
      have h1 := sourcePrimeMode_re 1 k
      have h2 := sourcePrimeMode_re 2 k
      have h3 := sourcePrimeMode_re 3 k
      norm_num at h1 h2 h3
      simp only [one_mul]
      rw [← h1, ← h2, ← h3]
      unfold sourcePrimeLogMass
      ring

theorem eventually_sourcePrimeMinorantSum_lower :
    ∀ᶠ k : ℕ in atTop,
      (Nat.sqrt k : ℝ) / 200 ≤ sourcePrimeMinorantSum k := by
  have h1 : ∀ᶠ k : ℕ in atTop,
      ‖sourcePrimeMode 1 k‖ / (Nat.sqrt k : ℝ) < 1 / 1000 :=
    (tendsto_norm_sourcePrimeMode_div (h := 1) (by omega) (by omega)).eventually
      (Iio_mem_nhds (by norm_num))
  have h2 : ∀ᶠ k : ℕ in atTop,
      ‖sourcePrimeMode 2 k‖ / (Nat.sqrt k : ℝ) < 1 / 1000 :=
    (tendsto_norm_sourcePrimeMode_div (h := 2) (by omega) (by omega)).eventually
      (Iio_mem_nhds (by norm_num))
  have h3 : ∀ᶠ k : ℕ in atTop,
      ‖sourcePrimeMode 3 k‖ / (Nat.sqrt k : ℝ) < 1 / 1000 :=
    (tendsto_norm_sourcePrimeMode_div (h := 3) (by omega) (by omega)).eventually
      (Iio_mem_nhds (by norm_num))
  have hspos : ∀ᶠ k : ℕ in atTop, 0 < Nat.sqrt k :=
    tendsto_natSqrt_atTop.eventually (eventually_gt_atTop 0)
  filter_upwards [eventually_sourcePrimeLogMass_lower, h1, h2, h3, hspos]
    with k hmass hm1 hm2 hm3 hs
  have hsR : (0 : ℝ) < Nat.sqrt k := by exact_mod_cast hs
  have hm1' : ‖sourcePrimeMode 1 k‖ < (Nat.sqrt k : ℝ) / 1000 := by
    rw [div_lt_iff₀ hsR] at hm1
    nlinarith
  have hm2' : ‖sourcePrimeMode 2 k‖ < (Nat.sqrt k : ℝ) / 1000 := by
    rw [div_lt_iff₀ hsR] at hm2
    nlinarith
  have hm3' : ‖sourcePrimeMode 3 k‖ < (Nat.sqrt k : ℝ) / 1000 := by
    rw [div_lt_iff₀ hsR] at hm3
    nlinarith
  have hre1 : -(Nat.sqrt k : ℝ) / 1000 < (sourcePrimeMode 1 k).re :=
    lt_of_lt_of_le (by linarith : -(Nat.sqrt k : ℝ) / 1000 <
      -‖sourcePrimeMode 1 k‖)
      ((abs_le.mp (Complex.abs_re_le_norm (sourcePrimeMode 1 k))).1)
  have hre2 : -(Nat.sqrt k : ℝ) / 1000 < (sourcePrimeMode 2 k).re :=
    lt_of_lt_of_le (by linarith : -(Nat.sqrt k : ℝ) / 1000 <
      -‖sourcePrimeMode 2 k‖)
      ((abs_le.mp (Complex.abs_re_le_norm (sourcePrimeMode 2 k))).1)
  have hre3 : -(Nat.sqrt k : ℝ) / 1000 < (sourcePrimeMode 3 k).re :=
    lt_of_lt_of_le (by linarith : -(Nat.sqrt k : ℝ) / 1000 <
      -‖sourcePrimeMode 3 k‖)
      ((abs_le.mp (Complex.abs_re_le_norm (sourcePrimeMode 3 k))).1)
  rw [sourcePrimeMinorantSum_eq_modes]
  nlinarith

def sourceGoodPrimeSet (k : ℕ) : Finset ℕ :=
  (sourcePrimeSet k).filter fun p ↦ 2 * p ≤ 3 * (k % p)

lemma sourceGoodPrimeSet_conditions {k p : ℕ}
    (hp : p ∈ sourceGoodPrimeSet k) :
    p.Prime ∧ Nat.sqrt k < p ∧ p ≤ sourcePrimeUpper k ∧
      k < p ^ 2 ∧ 2 * p ≤ 3 * (k % p) ∧ 81 * p ^ 2 ≤ 100 * k := by
  rcases Finset.mem_filter.mp hp with ⟨hpSet, hrem⟩
  rcases Finset.mem_filter.mp hpSet with ⟨hpIoc, hprime⟩
  rcases Finset.mem_Ioc.mp hpIoc with ⟨hsqrt, hupper⟩
  have hkp : k < p ^ 2 := by
    have hklt := Nat.lt_succ_sqrt k
    nlinarith
  have hscale : 9 * p ≤ 10 * Nat.sqrt k := by
    unfold sourcePrimeUpper at hupper
    omega
  have hsSq : (Nat.sqrt k) ^ 2 ≤ k := by
    simpa [pow_two] using Nat.sqrt_le k
  have hsize : 81 * p ^ 2 ≤ 100 * k := by
    nlinarith
  exact ⟨hprime, hsqrt, hupper, hkp, hrem, hsize⟩

lemma sourcePrimeMinorantSum_le_good_log_sum {k : ℕ}
    (hk : 2 ≤ Nat.sqrt k) :
    sourcePrimeMinorantSum k ≤
      ∑ p ∈ sourceGoodPrimeSet k, Real.log (p : ℝ) := by
  unfold sourcePrimeMinorantSum sourceGoodPrimeSet
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := Finset.mem_filter.mp hp
  have hpprime : p.Prime := hpdata.2
  have hpIoc := Finset.mem_Ioc.mp hpdata.1
  have hp_le_k : p ≤ k := by
    have hu : sourcePrimeUpper k ≤ 2 * Nat.sqrt k := by
      unfold sourcePrimeUpper
      omega
    have hsSq : (Nat.sqrt k) ^ 2 ≤ k := by
      simpa [pow_two] using Nat.sqrt_le k
    nlinarith
  by_cases hgood : 2 * p ≤ 3 * (k % p)
  · simp only [hgood, if_true]
    exact mul_le_of_le_one_right (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))
      (sourceMinorant_le_one _)
  · simp only [hgood, if_false]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le)
    · apply sourceMinorant_nonpos
      have hphase := reciprocal_phase_cos_eq_mod 1 k p hpprime.pos hp_le_k
      norm_num at hphase
      rw [hphase]
      apply source_arc_cos_le hpprime.pos
      omega

theorem eventually_good_prime_log_sum_lower :
    ∀ᶠ k : ℕ in atTop,
      (Nat.sqrt k : ℝ) / 200 ≤
        ∑ p ∈ sourceGoodPrimeSet k, Real.log (p : ℝ) := by
  filter_upwards [eventually_sourcePrimeMinorantSum_lower,
    tendsto_natSqrt_atTop.eventually (eventually_ge_atTop 2)] with k hlo hk
  exact hlo.trans (sourcePrimeMinorantSum_le_good_log_sum hk)

theorem eventually_good_prime_card_mul_log_lower :
    ∀ᶠ k : ℕ in atTop,
      (Nat.sqrt k : ℝ) / 200 ≤
        ((sourceGoodPrimeSet k).card : ℝ) *
          Real.log (sourcePrimeUpper k : ℝ) := by
  filter_upwards [eventually_good_prime_log_sum_lower,
    tendsto_sourcePrimeUpper_atTop.eventually (eventually_ge_atTop 2)] with
      k hlo hu
  apply hlo.trans
  calc
    (∑ p ∈ sourceGoodPrimeSet k, Real.log (p : ℝ)) ≤
        ∑ _p ∈ sourceGoodPrimeSet k,
          Real.log (sourcePrimeUpper k : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by
        exact_mod_cast (sourceGoodPrimeSet_conditions hp).1.pos)
        (by exact_mod_cast (sourceGoodPrimeSet_conditions hp).2.2.1)
    _ = ((sourceGoodPrimeSet k).card : ℝ) *
        Real.log (sourcePrimeUpper k : ℝ) := by simp

end

end ReciprocalPrimeSelection
end Erdos378
