import ErdosProblems.Erdos520.CaichHypercontractive
import ErdosProblems.Erdos520.Doob
import ErdosProblems.Erdos520.SmoothMartingale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# The largest-prime reduction and Doob assembly for Caich's `lambda^(2)`

For fixed `z` and a prime window `(a,b]`, the process in Caich's
`lambda^(2)` estimate is the martingale of partial largest-prime sums

`Psi(z,q) - Psi(z,a)`, `a <= q <= b`.

This file gives both pieces used in the paper: the exact `n = p*k`
reduction with multiplicity at most three for the squarefree Rademacher
model, and the global `L^4` Doob estimate followed by the finite-sum
hypercontractive estimate from `CaichHypercontractive`.
-/

/-! ## The exact largest-prime band -/

/-- Integers at most `z` whose prime factors are all at most `b`, but not all
at most `a`. -/
def caichLargestPrimeBand (z a b : ℕ) : Finset ℕ :=
  Nat.smoothNumbersUpTo z (b + 1) \ Nat.smoothNumbersUpTo z (a + 1)

theorem smoothNumbersUpTo_subset_of_le {z a b : ℕ} (hab : a ≤ b) :
    Nat.smoothNumbersUpTo z (a + 1) ⊆
      Nat.smoothNumbersUpTo z (b + 1) := by
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1, Nat.smoothNumbers_mono (by omega) hn.2⟩

/-- The terminal smooth increment is exactly the sum over the largest-prime
band. -/
theorem Psi_sub_Psi_eq_sum_caichLargestPrimeBand
    (omega : Omega) (z : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Ψ omega z b - Ψ omega z a =
      ∑ n ∈ caichLargestPrimeBand z a b, f omega n := by
  unfold Ψ caichLargestPrimeBand
  symm
  exact Finset.sum_sdiff_eq_sub (smoothNumbersUpTo_subset_of_le hab)

/-- Every member of the band is a positive integer at most `z`. -/
theorem caichLargestPrimeBand_subset_Ioc (z a b : ℕ) :
    caichLargestPrimeBand z a b ⊆ Finset.Ioc 0 z := by
  intro n hn
  rw [caichLargestPrimeBand, Finset.mem_sdiff,
    Nat.mem_smoothNumbersUpTo] at hn
  rw [Finset.mem_Ioc]
  exact ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hn.1.2), hn.1.1⟩

/-- A squarefree band member has a prime divisor in `(a,b]`. -/
theorem exists_freshPrime_dvd_of_mem_caichLargestPrimeBand
    {z a b n : ℕ} (hn : n ∈ caichLargestPrimeBand z a b) :
    ∃ p, p ∈ freshPrimes a b ∧ p ∣ n := by
  rw [caichLargestPrimeBand, Finset.mem_sdiff,
    Nat.mem_smoothNumbersUpTo] at hn
  have hnotSmooth : n ∉ Nat.smoothNumbers (a + 1) := by
    intro hsm
    exact hn.2 (Nat.mem_smoothNumbersUpTo.mpr ⟨hn.1.1, hsm⟩)
  have hnot : ¬∀ p, p.Prime → p ∣ n → p < a + 1 :=
    mt Nat.mem_smoothNumbers'.mpr hnotSmooth
  push Not at hnot
  obtain ⟨p, hpprime, hpdvd, hpa⟩ := hnot
  have hpb : p < b + 1 := Nat.mem_smoothNumbers'.mp hn.1.2 p hpprime hpdvd
  exact ⟨p, (mem_freshPrimes.mpr ⟨hpprime, by omega, by omega⟩), hpdvd⟩

/-- A deterministic witness prime for each integer in the band. -/
noncomputable def caichBandWitnessPrime (z a b n : ℕ) : ℕ :=
  if h : n ∈ caichLargestPrimeBand z a b then
    Classical.choose (exists_freshPrime_dvd_of_mem_caichLargestPrimeBand h)
  else 1

theorem caichBandWitnessPrime_mem {z a b n : ℕ}
    (hn : n ∈ caichLargestPrimeBand z a b) :
    caichBandWitnessPrime z a b n ∈ freshPrimes a b := by
  rw [caichBandWitnessPrime, dif_pos hn]
  exact (Classical.choose_spec
    (exists_freshPrime_dvd_of_mem_caichLargestPrimeBand hn)).1

theorem caichBandWitnessPrime_dvd {z a b n : ℕ}
    (hn : n ∈ caichLargestPrimeBand z a b) :
    caichBandWitnessPrime z a b n ∣ n := by
  rw [caichBandWitnessPrime, dif_pos hn]
  exact (Classical.choose_spec
    (exists_freshPrime_dvd_of_mem_caichLargestPrimeBand hn)).2

/-- Prime/cofactor pairs large enough to contain the image of every band
integer under `n = p*(n/p)`. -/
def caichPrimeCofactorPairs (z a b : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (freshPrimes a b).sigma fun p => Finset.Ioc 0 (z / p)

/-- The selected prime and its exact cofactor. -/
noncomputable def caichBandPrimeCofactor (z a b n : ℕ) : Σ _ : ℕ, ℕ :=
  ⟨caichBandWitnessPrime z a b n,
    n / caichBandWitnessPrime z a b n⟩

theorem caichBandPrimeCofactor_mem {z a b n : ℕ}
    (hn : n ∈ caichLargestPrimeBand z a b) :
    caichBandPrimeCofactor z a b n ∈ caichPrimeCofactorPairs z a b := by
  rw [caichPrimeCofactorPairs, Finset.mem_sigma]
  let p := caichBandWitnessPrime z a b n
  have hpMem : p ∈ freshPrimes a b := caichBandWitnessPrime_mem hn
  have hpPrime : p.Prime := (mem_freshPrimes.mp hpMem).1
  have hpDvd : p ∣ n := caichBandWitnessPrime_dvd hn
  have hnRange := Finset.mem_Ioc.mp (caichLargestPrimeBand_subset_Ioc z a b hn)
  refine ⟨hpMem, Finset.mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hnRange.2⟩⟩
  exact Nat.div_pos (Nat.le_of_dvd hnRange.1 hpDvd) hpPrime.pos

theorem caichBandPrimeCofactor_product {z a b n : ℕ}
    (hn : n ∈ caichLargestPrimeBand z a b) :
    (caichBandPrimeCofactor z a b n).1 *
      (caichBandPrimeCofactor z a b n).2 = n := by
  exact Nat.mul_div_cancel' (caichBandWitnessPrime_dvd hn)

/-- On squarefree band members the factor `3` is exact: adjoining the
witness prime multiplies `tau_3` by three. -/
theorem orderedDivisorCount_three_band_eq
    {z a b n : ℕ} (hn : n ∈ caichLargestPrimeBand z a b)
    (hsq : Squarefree n) :
    orderedDivisorCount 3 n =
      3 * orderedDivisorCount 3 (caichBandPrimeCofactor z a b n).2 := by
  let p := caichBandWitnessPrime z a b n
  let k := n / p
  have hpMem : p ∈ freshPrimes a b := caichBandWitnessPrime_mem hn
  have hpPrime : p.Prime := (mem_freshPrimes.mp hpMem).1
  have hpDvd : p ∣ n := caichBandWitnessPrime_dvd hn
  have hpk : p * k = n := Nat.mul_div_cancel' hpDvd
  have hpNotDvdK : ¬p ∣ k := by
    intro hpdk
    have hsqDvd : p * p ∣ n := by
      rw [← hpk]
      exact Nat.mul_dvd_mul_left p hpdk
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hpPrime) hsqDvd
  have hcop : p.Coprime k := hpPrime.coprime_iff_not_dvd.mpr hpNotDvdK
  calc
    orderedDivisorCount 3 n = orderedDivisorCount 3 (p * k) := by rw [hpk]
    _ = orderedDivisorCount 3 p * orderedDivisorCount 3 k :=
      (orderedDivisorCount_isMultiplicative 3).map_mul_of_coprime hcop
    _ = 3 * orderedDivisorCount 3 k := by
      rw [orderedDivisorCount_prime 3 hpPrime]

/-- Exact `n=p*k` reduction behind the factor `3` in Caich's
`lambda^(2)` and `lambda^(3)` estimates.  The right side may count the same
integer more than once; this is why the result is an inequality. -/
theorem sum_squarefree_band_orderedDivisorCount_three_le
    (z a b : ℕ) :
    (∑ n ∈ (caichLargestPrimeBand z a b).filter Squarefree,
        orderedDivisorCount 3 n) ≤
      ∑ p ∈ freshPrimes a b, ∑ k ∈ Finset.Ioc 0 (z / p),
        3 * orderedDivisorCount 3 k := by
  classical
  let s := (caichLargestPrimeBand z a b).filter Squarefree
  let pair : ℕ → (Σ _ : ℕ, ℕ) := caichBandPrimeCofactor z a b
  have hpair_mem : ∀ n ∈ s, pair n ∈ caichPrimeCofactorPairs z a b := by
    intro n hn
    exact caichBandPrimeCofactor_mem (Finset.mem_filter.mp hn).1
  have hpair_product : ∀ n ∈ s, (pair n).1 * (pair n).2 = n := by
    intro n hn
    exact caichBandPrimeCofactor_product (Finset.mem_filter.mp hn).1
  have hinj : Set.InjOn pair (s : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    calc
      n₁ = (pair n₁).1 * (pair n₁).2 := (hpair_product n₁ hn₁).symm
      _ = (pair n₂).1 * (pair n₂).2 := congrArg (fun u => u.1 * u.2) heq
      _ = n₂ := hpair_product n₂ hn₂
  have himage : Finset.image pair s ⊆ caichPrimeCofactorPairs z a b := by
    rw [Finset.image_subset_iff]
    exact hpair_mem
  calc
    (∑ n ∈ (caichLargestPrimeBand z a b).filter Squarefree,
        orderedDivisorCount 3 n) =
        ∑ n ∈ s, 3 * orderedDivisorCount 3 (pair n).2 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact orderedDivisorCount_three_band_eq
        (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
    _ = ∑ u ∈ Finset.image pair s,
          3 * orderedDivisorCount 3 u.2 := by
      exact (Finset.sum_image
        (f := fun u : (Σ _ : ℕ, ℕ) =>
          3 * orderedDivisorCount 3 u.2) hinj).symm
    _ ≤ ∑ u ∈ caichPrimeCofactorPairs z a b,
          3 * orderedDivisorCount 3 u.2 :=
      Finset.sum_le_sum_of_subset himage
    _ = ∑ p ∈ freshPrimes a b, ∑ k ∈ Finset.Ioc 0 (z / p),
          3 * orderedDivisorCount 3 k := by
      exact Finset.sum_sigma _ _ _

/-! ## The global Doob martingale for `lambda^(2)` -/

/-- Terminal largest-prime increment over `(a,b]`. -/
noncomputable def caichLambda2Terminal
    (z a b : ℕ) (omega : Omega) : ℝ :=
  Ψ omega z b - Ψ omega z a

theorem stronglyMeasurable_caichLambda2Terminal (z a b : ℕ) :
    StronglyMeasurable (caichLambda2Terminal z a b) := by
  exact ((stronglyMeasurable_Ψ_filtration z b).mono (εFiltration.le b)).sub
    ((stronglyMeasurable_Ψ_filtration z a).mono (εFiltration.le a))

theorem integrable_caichLambda2Terminal (z a b : ℕ) :
    Integrable (caichLambda2Terminal z a b) μ :=
  (integrable_Ψ z b).sub (integrable_Ψ z a)

theorem norm_caichLambda2Terminal_le (z a b : ℕ) (omega : Omega) :
    ‖caichLambda2Terminal z a b omega‖ ≤
      (squarefreeSmoothSets z b).card + (squarefreeSmoothSets z a).card := by
  change ‖Ψ omega z b - Ψ omega z a‖ ≤ _
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_Ψ_le_card omega z b) (norm_Ψ_le_card omega z a))

/-- The terminal increment has every finite moment; `L^4` is the instance
needed below. -/
theorem memLp_four_caichLambda2Terminal (z a b : ℕ) :
    MemLp (caichLambda2Terminal z a b) 4 μ := by
  let C : ℝ := (squarefreeSmoothSets z b).card +
    (squarefreeSmoothSets z a).card
  apply MemLp.of_bound
    (stronglyMeasurable_caichLambda2Terminal z a b).aestronglyMeasurable C
  exact ae_of_all μ fun omega => by
    exact norm_caichLambda2Terminal_le z a b omega

/-- The canonical conditional-expectation martingale of the terminal
largest-prime increment. -/
noncomputable def caichLambda2Doob
    (z a b : ℕ) : ℕ → Omega → ℝ :=
  fun k => μ[caichLambda2Terminal z a b | εFiltration k]

theorem caichLambda2Doob_martingale (z a b : ℕ) :
    Martingale (caichLambda2Doob z a b) εFiltration μ := by
  exact martingale_condExp (caichLambda2Terminal z a b) εFiltration μ

/-- At times inside `[a,b]`, the canonical Doob process is the concrete
partial largest-prime sum `Psi(z,k)-Psi(z,a)`. -/
theorem caichLambda2Doob_ae_eq_increment
    (z : ℕ) {a b k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) :
    caichLambda2Doob z a b k =ᵐ[μ]
      fun omega => Ψ omega z k - Ψ omega z a := by
  have hsub := condExp_sub (integrable_Ψ z b) (integrable_Ψ z a)
    (εFiltration k)
  have hb := (martingale_Ψ z).condExp_ae_eq hkb
  have ha : μ[fun omega : Omega => Ψ omega z a | εFiltration k] =ᵐ[μ]
      fun omega => Ψ omega z a := by
    rw [condExp_of_stronglyMeasurable (εFiltration.le k)
      ((stronglyMeasurable_Ψ_filtration z a).mono
        ((εFiltration).mono hak)) (integrable_Ψ z a)]
  unfold caichLambda2Doob caichLambda2Terminal
  exact hsub.trans (hb.sub ha)

/-- Before the lower endpoint, the canonical process is zero. -/
theorem caichLambda2Doob_ae_eq_zero_of_le
    (z : ℕ) {a b k : ℕ} (hka : k ≤ a) (hkb : k ≤ b) :
    caichLambda2Doob z a b k =ᵐ[μ] (0 : Omega → ℝ) := by
  have hsub := condExp_sub (integrable_Ψ z b) (integrable_Ψ z a)
    (εFiltration k)
  have hb := (martingale_Ψ z).condExp_ae_eq hkb
  have ha := (martingale_Ψ z).condExp_ae_eq hka
  unfold caichLambda2Doob caichLambda2Terminal
  exact hsub.trans (by simpa only [Pi.sub_apply, sub_self] using! hb.sub ha)

/-- At the terminal time the canonical process is exactly the terminal
increment. -/
theorem caichLambda2Doob_terminal
    (z : ℕ) {a b : ℕ} (hab : a ≤ b) :
    caichLambda2Doob z a b b = caichLambda2Terminal z a b := by
  unfold caichLambda2Doob
  exact condExp_of_stronglyMeasurable (εFiltration.le b)
    ((stronglyMeasurable_Ψ_filtration z b).sub
      ((stronglyMeasurable_Ψ_filtration z a).mono ((εFiltration).mono hab)))
    (integrable_caichLambda2Terminal z a b)

/-- Doob's `L^4` estimate for the exact largest-prime process. -/
theorem integral_caichLambda2Doob_max_four_le
    (z : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∫ omega, finiteRunningMax
        (fun k omega => |caichLambda2Doob z a b k omega| ^ 2)
        b omega ^ 2 ∂μ ≤
      4 * ∫ omega, |caichLambda2Terminal z a b omega| ^ 4 ∂μ := by
  have hX := caichLambda2Doob_martingale z a b
  let C : ℝ := (squarefreeSmoothSets z b).card +
    (squarefreeSmoothSets z a).card
  have hpath4 (k : ℕ) : MemLp (caichLambda2Doob z a b k) 4 μ := by
    apply MemLp.of_bound
      ((hX.stronglyMeasurable k).mono (εFiltration.le k)).aestronglyMeasurable C
    have hnorm :
        (fun omega => ‖μ[caichLambda2Terminal z a b | εFiltration k] omega‖) ≤ᵐ[μ]
          μ[fun omega => ‖caichLambda2Terminal z a b omega‖ |
            εFiltration k] := norm_condExp_le (caichLambda2Terminal z a b)
    have hmono :
        μ[fun omega => ‖caichLambda2Terminal z a b omega‖ | εFiltration k] ≤ᵐ[μ]
          μ[(fun _ : Omega => C) | εFiltration k] :=
      condExp_mono (integrable_caichLambda2Terminal z a b).norm
        (integrable_const C) (ae_of_all μ fun omega =>
          norm_caichLambda2Terminal_le z a b omega)
    filter_upwards [hnorm, hmono] with omega h₁ h₂
    unfold caichLambda2Doob
    rw [condExp_const (εFiltration.le k) C] at h₂
    exact h₁.trans h₂
  have hint : ∀ k, Integrable
      (fun omega => |caichLambda2Doob z a b k omega| ^ 2) μ := by
    intro k
    have hpath2 : MemLp (caichLambda2Doob z a b k) 2 μ :=
      (hpath4 k).mono_exponent (by norm_num)
    simpa only [Real.norm_eq_abs] using!
      hpath2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hbase := hint b
  have hfour : Integrable
      (fun omega => |caichLambda2Doob z a b b omega| ^ 4) μ := by
    simpa only [Real.norm_eq_abs] using!
      (hpath4 b).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hterminal : MemLp
      (fun omega => |caichLambda2Doob z a b b omega| ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq hbase.aestronglyMeasurable).2 (by
      simpa only [← pow_mul, Nat.mul_comm] using! hfour)
  have h := Martingale.integral_sq_finiteRunningMax_abs_pow_le
    hX 2 b hint hterminal
  simpa only [caichLambda2Doob_terminal z hab] using! h

/-! ## Concrete maximum and hypercontractive terminal bound -/

/-- A pointwise version of the largest-prime path: zero below `a`, the
actual increment inside `[a,b]`, and stopped at `b`. -/
noncomputable def caichLambda2ConcretePath
    (z a b : ℕ) : ℕ → Omega → ℝ :=
  fun k omega =>
    if a ≤ k then Ψ omega z (min k b) - Ψ omega z a else 0

theorem caichLambda2Doob_ae_eq_concrete
    (z a b k : ℕ) (hkb : k ≤ b) :
    caichLambda2Doob z a b k =ᵐ[μ] caichLambda2ConcretePath z a b k := by
  by_cases hak : a ≤ k
  · change caichLambda2Doob z a b k =ᵐ[μ]
      fun omega => if a ≤ k then Ψ omega z (min k b) - Ψ omega z a else 0
    simpa only [if_pos hak, min_eq_left hkb] using!
      caichLambda2Doob_ae_eq_increment z hak hkb
  · have hka : k ≤ a := by omega
    change caichLambda2Doob z a b k =ᵐ[μ]
      fun omega => if a ≤ k then Ψ omega z (min k b) - Ψ omega z a else 0
    simpa only [if_neg hak] using!
      caichLambda2Doob_ae_eq_zero_of_le z hka hkb

/-- The running maximum of the canonical process and the concrete
largest-prime path agree almost everywhere. -/
theorem finiteRunningMax_caichLambda2Doob_ae_eq_concrete
    (z a b : ℕ) :
    finiteRunningMax
        (fun k omega => |caichLambda2Doob z a b k omega| ^ 2) b =ᵐ[μ]
      finiteRunningMax
        (fun k omega => |caichLambda2ConcretePath z a b k omega| ^ 2) b := by
  have hall : ∀ᵐ omega ∂μ, ∀ k, k ≤ b →
      caichLambda2Doob z a b k omega =
        caichLambda2ConcretePath z a b k omega := by
    rw [ae_all_iff]
    intro k
    by_cases hkb : k ≤ b
    · exact (caichLambda2Doob_ae_eq_concrete z a b k hkb).mono
        fun omega heq _ => heq
    · exact ae_of_all μ fun omega hk => (hkb hk).elim
  filter_upwards [hall] with omega h
  unfold finiteRunningMax
  apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
  intro k hk
  have hkb : k ≤ b := by
    rw [Finset.mem_range] at hk
    omega
  change |caichLambda2Doob z a b k omega| ^ 2 =
    |caichLambda2ConcretePath z a b k omega| ^ 2
  rw [h k hkb]

/-- Every individual largest-prime cutoff in `[a,b]` is dominated by the
concrete running maximum used in the Doob estimate. -/
theorem abs_increment_pow_four_le_caichLambda2Concrete_max
    (omega : Omega) (z : ℕ) {a b k : ℕ} (hak : a ≤ k) (hkb : k ≤ b) :
    |Ψ omega z k - Ψ omega z a| ^ 4 ≤
      finiteRunningMax
        (fun q omega => |caichLambda2ConcretePath z a b q omega| ^ 2)
        b omega ^ 2 := by
  have hkRange : k ∈ Finset.range (b + 1) := by
    rw [Finset.mem_range]
    omega
  have hpath : caichLambda2ConcretePath z a b k omega =
      Ψ omega z k - Ψ omega z a := by
    simp only [caichLambda2ConcretePath, hak, if_true, min_eq_left hkb]
  have hle : |Ψ omega z k - Ψ omega z a| ^ 2 ≤
      finiteRunningMax
        (fun q omega => |caichLambda2ConcretePath z a b q omega| ^ 2)
        b omega := by
    rw [← hpath]
    exact Finset.le_sup'
      (fun q => |caichLambda2ConcretePath z a b q omega| ^ 2) hkRange
  calc
    |Ψ omega z k - Ψ omega z a| ^ 4 =
        (|Ψ omega z k - Ψ omega z a| ^ 2) ^ 2 := by ring
    _ ≤ finiteRunningMax
        (fun q omega => |caichLambda2ConcretePath z a b q omega| ^ 2)
        b omega ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hle 2

/-- Hypercontractivity and the divisor-sum estimate bound the terminal
fourth moment. -/
theorem integral_abs_caichLambda2Terminal_four_le
    (z : ℕ) {a b : ℕ} (hz : 3 ≤ z) (hab : a ≤ b) :
    (∫ omega, |caichLambda2Terminal z a b omega| ^ 4 ∂μ) ≤
      ((z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2) ^ 2 := by
  have h := integral_caichFiniteRMFSum_one_pow_le
    2 (by norm_num) z (caichLargestPrimeBand z a b) hz
      (caichLargestPrimeBand_subset_Ioc z a b)
  simpa only [caichLambda2Terminal,
    Psi_sub_Psi_eq_sum_caichLargestPrimeBand _ z hab,
    show 2 * 2 = 4 by norm_num, show 2 * 2 - 2 = 2 by norm_num] using! h

/-- Complete fixed-`z` Doob--hypercontractive estimate for Caich's
`lambda^(2)` largest-prime maximum. -/
theorem integral_caichLambda2Concrete_max_four_le
    (z : ℕ) {a b : ℕ} (hz : 3 ≤ z) (hab : a ≤ b) :
    ∫ omega, finiteRunningMax
        (fun k omega => |caichLambda2ConcretePath z a b k omega| ^ 2)
        b omega ^ 2 ∂μ ≤
      4 * ((z : ℝ) * (2 * Real.log (z : ℝ)) ^ 2) ^ 2 := by
  have hdoob := integral_caichLambda2Doob_max_four_le z hab
  have hmax := finiteRunningMax_caichLambda2Doob_ae_eq_concrete z a b
  have hintEq :
      (∫ omega, finiteRunningMax
          (fun k omega => |caichLambda2Doob z a b k omega| ^ 2)
          b omega ^ 2 ∂μ) =
        ∫ omega, finiteRunningMax
          (fun k omega => |caichLambda2ConcretePath z a b k omega| ^ 2)
          b omega ^ 2 ∂μ := by
    apply integral_congr_ae
    exact hmax.fun_comp (fun x : ℝ => x ^ 2)
  rw [hintEq] at hdoob
  exact hdoob.trans (mul_le_mul_of_nonneg_left
    (integral_abs_caichLambda2Terminal_four_le z hz hab) (by norm_num))

end Problem520
end Erdos
