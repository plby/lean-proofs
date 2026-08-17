/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting
import Mathlib

/- The local verification cache for `BoundedGaps` was produced by Lake and
records this generated name for the standard order on `ℕ`.  Re-exporting the
same reducible instance name keeps that cache compatible; a clean Lake build
reduces it to the ordinary `Nat` partial order. -/
namespace Nat
abbrev «instPartialOrder_.lake» : PartialOrder ℕ := inferInstance
end Nat

/-!
# Erdős Problem 1202

Erdős asked whether removing half of the residue classes modulo sufficiently many
primes below `n ^ (1 - ε)` must leave at most `ε n` positive integers up to `n`.
The answer is negative.  We formalize the interval construction of Price and
GPT-5.4 Pro: primes in one short interval have aligned upper-half forbidden
sets, while a positive-density striped set survives every sieve.

The detailed mathematical proof and Leanization plan are in `tex/1202.tex`.
-/

namespace Erdos1202

open Filter Finset Real
open scoped Topology

noncomputable section

/-- Positive integers at most `n` avoiding every indexed forbidden residue set. -/
def survivors {k : ℕ} (n : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun x ↦ ∀ i, (x : ZMod (p i)) ∉ A i

/-- The literal assertion recorded as Erdős Problem 1202.

The source quantifies both `ε` and `η`, but its displayed upper bound uses `ε`;
we preserve that quantifier structure exactly. -/
def Erdos1202Statement : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η →
    ∃ k : ℕ, 0 < k ∧ ∀ (n : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) →
      StrictMono p →
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((survivors n p A).card : ℝ) ≤ ε * n

/-- The upper half of the least nonnegative representatives modulo `p`. -/
def upperHalf (p : ℕ) (hp0 : p ≠ 0) : Finset (ZMod p) :=
  letI : NeZero p := ⟨hp0⟩
  Finset.univ.filter fun a ↦ (p + 1) / 2 ≤ a.val

lemma upperHalf_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (upperHalf p hp.ne_zero).card = (p - 1) / 2 := by
  cases p with
  | zero => exact (hp.ne_zero rfl).elim
  | succ n =>
    change (Finset.univ.filter fun a : Fin (n + 1) ↦
        (n + 1 + 1) / 2 ≤ a.val).card = (n + 1 - 1) / 2
    have hthreshold : (n + 1 + 1) / 2 < n + 1 := by
      have hp2 := hp.two_le
      omega
    let a : Fin (n + 1) := ⟨(n + 1 + 1) / 2, hthreshold⟩
    have hfilter : (Finset.univ.filter fun x : Fin (n + 1) ↦
        (n + 1 + 1) / 2 ≤ x.val) = Finset.Ici a := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      rfl
    rw [hfilter, Fin.card_Ici]
    dsimp [a]
    obtain ⟨d, hd⟩ := hp.odd_of_ne_two hp2
    omega

lemma not_mem_upperHalf_of_mod_le {p x : ℕ} (hp : p.Prime)
    (hx : x % p ≤ (p - 1) / 2) :
    (x : ZMod p) ∉ upperHalf p hp.ne_zero := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp only [upperHalf, Finset.mem_filter, Finset.mem_univ, true_and,
    ZMod.val_natCast, not_le]
  have hp2 := hp.two_le
  omega

/-! ## The finite aligned-block construction -/

/-- Encoding a block number and a remainder less than `B`. -/
def blockEmbedding (B : ℕ) [NeZero B] : (ℕ × Fin B) ↪ ℕ where
  toFun qr := B * qr.1 + qr.2.val
  inj' := by
    rintro ⟨q, r⟩ ⟨q', r'⟩ h
    have hq := congrArg (fun x : ℕ ↦ x / B) h
    have hr := congrArg (fun x : ℕ ↦ x % B) h
    have hB : 0 < B := NeZero.pos B
    simp only [Nat.mul_add_div hB, Nat.div_eq_of_lt r.isLt, add_zero,
      Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_eq_of_lt r.isLt,
      Nat.div_eq_of_lt r'.isLt, Nat.mod_eq_of_lt r'.isLt] at hq
    simp only [Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt r'.isLt] at hr
    exact Prod.ext hq (Fin.ext hr)

lemma alignedBlock_card (B Q lo hi : ℕ) [NeZero B] (hhi : hi < B) :
    ((((Finset.range Q).product
      (Finset.Icc (⟨lo % B, Nat.mod_lt _ (NeZero.pos B)⟩ : Fin B)
        ⟨hi, hhi⟩)).map (blockEmbedding B))).card =
      Q * (hi + 1 - lo % B) := by
  calc
    _ = ((Finset.range Q).product
          (Finset.Icc (⟨lo % B, Nat.mod_lt _ (NeZero.pos B)⟩ : Fin B)
            ⟨hi, hhi⟩)).card := by rw [Finset.card_map]
    _ = (Finset.range Q).card *
          (Finset.Icc (⟨lo % B, Nat.mod_lt _ (NeZero.pos B)⟩ : Fin B)
            ⟨hi, hhi⟩).card := by
              rw [Finset.product_eq_sprod, Finset.card_product]
    _ = Q * (hi + 1 - lo % B) := by simp

lemma lt_nine_tenths_rpow_of_pow {p n : ℕ} (h : p ^ 10 < n ^ 9) :
    (p : ℝ) < (n : ℝ) ^ (9 / 10 : ℝ) := by
  have hreal : (p : ℝ) ^ 10 < (n : ℝ) ^ 9 := by exact_mod_cast h
  have hroot : (p : ℝ) < ((n : ℝ) ^ 9) ^ ((10 : ℝ)⁻¹) :=
    (Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 10)).2
      (by simpa [Real.rpow_natCast] using hreal)
  convert hroot using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  norm_num

lemma common_remainder_le_half {M H B p q r x : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hBM : M ≤ B)
    (hpB : B ≤ p) (hpBH : p < B + H)
    (hqH : q * H ≤ M / 16) (hrlo : M / 16 ≤ r) (hrhi : r ≤ B / 2)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : x = q * B + r) :
    x % p ≤ (p - 1) / 2 := by
  have hd : p - B < H := by omega
  have hqd : q * (p - B) ≤ M / 16 :=
    (Nat.mul_le_mul_left q (Nat.le_of_lt hd)).trans hqH
  have hqdr : q * (p - B) ≤ r := hqd.trans hrlo
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hhalf : B / 2 ≤ (p - 1) / 2 := by
    have hdiv : B / 2 ≤ p / 2 := Nat.div_le_div_right hpB
    obtain ⟨d, hd⟩ := hpodd
    omega
  have hremp : r - q * (p - B) < p := by
    have : r ≤ (p - 1) / 2 := hrhi.trans hhalf
    omega
  have hrewrite : x = q * p + (r - q * (p - B)) := by
    subst x
    have hp_split : B + (p - B) = p := Nat.add_sub_of_le hpB
    calc
      q * B + r = q * B + (q * (p - B) + (r - q * (p - B))) := by
        rw [Nat.add_sub_of_le hqdr]
      _ = (q * B + q * (p - B)) + (r - q * (p - B)) := by omega
      _ = q * (B + (p - B)) + (r - q * (p - B)) := by rw [Nat.mul_add]
      _ = q * p + (r - q * (p - B)) := by rw [hp_split]
  rw [hrewrite]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
    zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hremp]
  exact (Nat.sub_le r _).trans (hrhi.trans hhalf)

/-! ## Short clusters of primes -/

/-- The primes in the half-open dyadic interval `(M, 2M]`. -/
def dyadicPrimes (M : ℕ) : Finset ℕ :=
  Nat.primesLE (2 * M) \ Nat.primesLE M

lemma mem_dyadicPrimes {M p : ℕ} :
    p ∈ dyadicPrimes M ↔ M < p ∧ p ≤ 2 * M ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or,
    not_le]
  aesop

lemma eventually_primeCounting_tenth_bounds :
    ∀ᶠ x : ℕ in atTop,
      (9 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (Nat.primeCounting x : ℝ) ∧
      (Nat.primeCounting x : ℝ) ≤
          (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ)),
    neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]

lemma eventually_log_two_mul_le_eleven_tenths :
    ∀ᶠ x : ℕ in atTop,
      Real.log (2 * x : ℝ) ≤
        (11 / 10 : ℝ) * Real.log (x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ x : ℕ in atTop,
      10 * Real.log 2 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (10 * Real.log 2))
  filter_upwards [hevent, eventually_ge_atTop 1] with x hx hxone
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  rw [show (2 * x : ℝ) = 2 * (x : ℝ) by norm_num,
    Real.log_mul (by norm_num) hxpos.ne']
  linarith

/-- A coarse dyadic consequence of the prime number theorem. -/
lemma eventually_dyadicPrimes_card_lower :
    ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (dyadicPrimes x).card := by
  have hpnt := eventually_primeCounting_tenth_bounds
  have htwoTop : Tendsto (fun x : ℕ ↦ 2 * x) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards with x
    simpa only [id_eq] using (show x ≤ 2 * x by omega)
  have hpntTwo := htwoTop.eventually eventually_primeCounting_tenth_bounds
  have hlog := eventually_log_two_mul_le_eleven_tenths
  have hlogPos : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  filter_upwards [hpnt, hpntTwo, hlog, hlogPos, eventually_ge_atTop 3]
      with x hx hxTwo hlog hlogPos hxthree
  norm_num [Nat.cast_mul] at hxTwo
  have hlogTwoPos : 0 < Real.log (2 * x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * x by omega))
  have hmono : Nat.primesLE x ⊆ Nat.primesLE (2 * x) :=
    Nat.primesLE_mono (by omega)
  have hcard : (dyadicPrimes x).card =
      Nat.primeCounting (2 * x) - Nat.primeCounting x := by
    rw [dyadicPrimes, Finset.card_sdiff_of_subset hmono,
      Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
  have hpiMono : Nat.primeCounting x ≤ Nat.primeCounting (2 * x) := by
    simpa [← Nat.primesLE_card_eq_primeCounting] using
      Finset.card_le_card hmono
  have hcardR : ((dyadicPrimes x).card : ℝ) =
      (Nat.primeCounting (2 * x) : ℝ) - (Nat.primeCounting x : ℝ) := by
    rw [hcard, Nat.cast_sub hpiMono]
  rw [hcardR]
  have hratio :
      (x : ℝ) / Real.log (x : ℝ) ≤
        (11 / 10 : ℝ) * ((x : ℝ) / Real.log (2 * x : ℝ)) := by
    have hxnonneg : (0 : ℝ) ≤ x := by positivity
    have hmul :
        (x : ℝ) * Real.log (2 * x : ℝ) ≤
          ((11 / 10 : ℝ) * (x : ℝ)) * Real.log (x : ℝ) := by
      nlinarith [mul_nonneg hxnonneg (sub_nonneg.mpr hlog)]
    calc
      (x : ℝ) / Real.log (x : ℝ) ≤
          ((11 / 10 : ℝ) * (x : ℝ)) / Real.log (2 * x : ℝ) :=
        (div_le_div_iff₀ hlogPos hlogTwoPos).2 hmul
      _ = (11 / 10 : ℝ) *
          ((x : ℝ) / Real.log (2 * x : ℝ)) := by ring
  have hmainNonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
  calc
    (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ))
        ≤ (59 / 110 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hmainNonneg
    _ ≤ (9 / 10 : ℝ) * ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
          (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
      have hscaled := mul_le_mul_of_nonneg_left hratio
        (show (0 : ℝ) ≤ 18 / 11 by norm_num)
      calc
        (59 / 110 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) =
            (18 / 11 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) -
              (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by ring
        _ ≤ (18 / 10 : ℝ) * ((x : ℝ) / Real.log (2 * x : ℝ)) -
              (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
          exact sub_le_sub_right (by nlinarith) _
        _ = (9 / 10 : ℝ) * ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
              (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
          norm_num [Nat.cast_mul]
          ring
    _ ≤ (Nat.primeCounting (2 * x) : ℝ) -
          (Nat.primeCounting x : ℝ) := sub_le_sub hxTwo.1 hx.2

/-- At the polynomial scale used below, the dyadic interval contains enough
primes that some width-`t³` bucket contains any prescribed finite number. -/
lemma eventually_scale_supply (k : ℕ) :
    ∀ᶠ t : ℕ in atTop,
      ((4 * t ^ 4) / (t ^ 3) + 1) * k ≤
        (dyadicPrimes (4 * t ^ 4)).card := by
  have hdyadic := eventually_dyadicPrimes_card_lower
  rw [Filter.eventually_atTop] at hdyadic ⊢
  obtain ⟨X, hX⟩ := hdyadic
  refine ⟨max X (max (10 * (k + 1)) 2), ?_⟩
  intro t ht
  have htX : X ≤ t := le_trans (Nat.le_max_left _ _) ht
  have htk : 10 * (k + 1) ≤ t :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans ht)
  have ht2 : 2 ≤ t :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans ht)
  have htpos : 0 < t := by omega
  have htM : t ≤ 4 * t ^ 4 := by
    have hpow : t ≤ t ^ 4 := Nat.le_self_pow (by norm_num : 4 ≠ 0) t
    omega
  have hPNT := hX (4 * t ^ 4) (htX.trans htM)
  have hlogpos : 0 < Real.log ((4 * t ^ 4 : ℕ) : ℝ) := by
    apply Real.log_pos
    have ht4pos : 0 < t ^ 4 := pow_pos htpos _
    exact_mod_cast (show 1 < 4 * t ^ 4 by omega)
  have hlograw := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ ((4 * t ^ 4 : ℕ) : ℝ) by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hMsq : (((4 * t ^ 4 : ℕ) : ℝ)) =
      ((2 : ℝ) * (t : ℝ) ^ 2) ^ 2 := by
    push_cast
    ring
  have hsqrt : Real.sqrt (((4 * t ^ 4 : ℕ) : ℝ)) =
      2 * (t : ℝ) ^ 2 := by
    rw [hMsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hlogupper : Real.log (((4 * t ^ 4 : ℕ) : ℝ)) ≤
      4 * (t : ℝ) ^ 2 := by
    rw [← Real.sqrt_eq_rpow] at hlograw
    rw [hsqrt] at hlograw
    norm_num [div_eq_mul_inv] at hlograw ⊢
    linarith
  have hhalf : (1 / 2 : ℝ) * (t : ℝ) ^ 2 ≤
      (1 / 2 : ℝ) *
        ((((4 * t ^ 4 : ℕ) : ℝ)) /
          Real.log (((4 * t ^ 4 : ℕ) : ℝ))) := by
    have hdiv : (1 / 2 : ℝ) * (t : ℝ) ^ 2 ≤
        (2 * (t : ℝ) ^ 4) /
          Real.log (((4 * t ^ 4 : ℕ) : ℝ)) := by
      apply (le_div_iff₀ hlogpos).2
      calc
        (1 / 2 : ℝ) * (t : ℝ) ^ 2 *
              Real.log (((4 * t ^ 4 : ℕ) : ℝ)) ≤
            (1 / 2 : ℝ) * (t : ℝ) ^ 2 * (4 * (t : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hlogupper (by positivity)
        _ = 2 * (t : ℝ) ^ 4 := by ring
    convert hdiv using 1 <;> push_cast <;> ring
  have hMH : (4 * t ^ 4) / (t ^ 3) = 4 * t := by
    rw [show 4 * t ^ 4 = (4 * t) * t ^ 3 by ring,
      Nat.mul_div_left _ (pow_pos htpos 3)]
  have htkR :
      (((((4 * t ^ 4) / (t ^ 3) + 1) * k : ℕ) : ℝ)) ≤
        (1 / 2 : ℝ) * (t : ℝ) ^ 2 := by
    rw [hMH]
    have hmul := mul_le_mul_of_nonneg_right htk (show 0 ≤ t by omega)
    have hmulR :
        (10 : ℝ) * ((k : ℝ) + 1) * (t : ℝ) ≤ (t : ℝ) * (t : ℝ) := by
      exact_mod_cast hmul
    push_cast
    nlinarith [hmulR]
  have hcardR :
      (((((4 * t ^ 4) / (t ^ 3) + 1) * k : ℕ) : ℝ)) ≤
        ((dyadicPrimes (4 * t ^ 4)).card : ℝ) :=
    htkR.trans (hhalf.trans hPNT)
  exact_mod_cast hcardR

lemma exists_prime_cluster {M H k : ℕ} (hH : 0 < H)
    (hcard : (M / H + 1) * k ≤ (dyadicPrimes M).card) :
    ∃ B : ℕ, ∃ S : Finset ℕ,
      M ≤ B ∧ S.card = k ∧ S ⊆ dyadicPrimes M ∧
      (∀ p ∈ S, B ≤ p ∧ p < B + H) := by
  let f : ℕ → ℕ := fun p ↦ (p - M) / H
  let T := Finset.range (M / H + 1)
  have hmap : ∀ p ∈ dyadicPrimes M, f p ∈ T := by
    intro p hp
    have hp2M : p ≤ 2 * M := (mem_dyadicPrimes.mp hp).2.1
    have hsub : p - M ≤ M := by omega
    simp only [f, T, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hsub)
  have hT : T.Nonempty := by simp [T]
  obtain ⟨j, hjT, hjcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := dyadicPrimes M) (t := T) (f := f) (n := k)
      hmap hT (by simpa [T] using hcard)
  let fiber := (dyadicPrimes M).filter fun p ↦ f p = j
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hjcard
  refine ⟨M + j * H, S, Nat.le_add_right M _, hScard,
    hSsub.trans (Finset.filter_subset _ _), ?_⟩
  intro p hpS
  have hpFiber := hSsub hpS
  have hpP : p ∈ dyadicPrimes M := (Finset.mem_filter.mp hpFiber).1
  have hfj : (p - M) / H = j := (Finset.mem_filter.mp hpFiber).2
  have hpM : M < p := (mem_dyadicPrimes.mp hpP).1
  have hlo : j * H ≤ p - M := by
    rw [← hfj]
    exact Nat.div_mul_le_self _ _
  have hhi : p - M < (j + 1) * H := by
    rw [← hfj]
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ (p - M) hH
  constructor
  · calc
      M + j * H ≤ M + (p - M) := Nat.add_le_add_left hlo M
      _ = p := Nat.add_sub_of_le hpM.le
  · calc
      p = M + (p - M) := (Nat.add_sub_of_le hpM.le).symm
      _ < M + (j + 1) * H := Nat.add_lt_add_left hhi M
      _ = (M + j * H) + H := by rw [Nat.add_mul]; omega

/-! ## The counterexamples and the negative answer -/

/-- For every prescribed number of primes, there is a counterexample at
`ε = 1/10`: all primes are below `n^(9/10)`, yet more than `n/10` integers
survive after half of the classes modulo every prime are forbidden. -/
theorem erdos_1202_counterexample (k : ℕ) :
    ∃ (n : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧
      StrictMono p ∧
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (9 / 10 : ℝ)) ∧
      (∀ i, (A i).card = (p i - 1) / 2) ∧
      (1 / 10 : ℝ) * n < (survivors n p A).card := by
  by_cases hk0 : k = 0
  · subst k
    let p : Fin 0 → ℕ := Fin.elim0
    let A : (i : Fin 0) → Finset (ZMod (p i)) := fun i ↦ Fin.elim0 i
    refine ⟨1, p, A, (fun i ↦ Fin.elim0 i), ?_,
      (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_⟩
    · intro i
      exact Fin.elim0 i
    norm_num [survivors, p, A]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hsupplyEventually := eventually_scale_supply k
  rw [Filter.eventually_atTop] at hsupplyEventually
  obtain ⟨T, hT⟩ := hsupplyEventually
  let t := 12 * max T 100
  let M := 4 * t ^ 4
  let H := t ^ 3
  let N := t ^ 5
  have htT : T ≤ t := by
    dsimp [t]
    have h := Nat.le_max_left T 100
    omega
  have ht100 : 100 ≤ t := by
    dsimp [t]
    have h := Nat.le_max_right T 100
    omega
  have htpos : 0 < t := by omega
  have hHpos : 0 < H := by positivity
  have hsupply : (M / H + 1) * k ≤ (dyadicPrimes M).card := by
    exact hT t htT
  obtain ⟨B, S, hMB, hScard, hSP, hcluster⟩ :=
    exists_prime_cluster hHpos hsupply
  let e : Fin k ≃o S := S.orderIsoOfFin hScard
  let p : Fin k → ℕ := fun i ↦ (e i).val
  have hpS : ∀ i, p i ∈ S := fun i ↦ (e i).property
  have hpPrime : ∀ i, (p i).Prime := by
    intro i
    exact (mem_dyadicPrimes.mp (hSP (hpS i))).2.2
  have hpMono : StrictMono p := by
    intro i j hij
    exact e.strictMono hij
  let A : (i : Fin k) → Finset (ZMod (p i)) :=
    fun i ↦ upperHalf (p i) (hpPrime i).ne_zero
  have hAcard : ∀ i, (A i).card = (p i - 1) / 2 := by
    intro i
    apply upperHalf_card (hpPrime i)
    have hpM := (mem_dyadicPrimes.mp (hSP (hpS i))).1
    have ht4pos : 0 < t ^ 4 := pow_pos htpos _
    dsimp [M] at hpM
    omega
  have hp_le_twoM : ∀ i, p i ≤ 2 * M := by
    intro i
    exact (mem_dyadicPrimes.mp (hSP (hpS i))).2.1
  have hp_pow : ∀ i, (p i) ^ 10 < N ^ 9 := by
    intro i
    have hpi := hp_le_twoM i
    have ht5 : 8 ^ 10 < t ^ 5 := by
      calc
        8 ^ 10 < 100 ^ 5 := by norm_num
        _ ≤ t ^ 5 := Nat.pow_le_pow_left ht100 5
    have ht40pos : 0 < t ^ 40 := pow_pos htpos _
    calc
      (p i) ^ 10 ≤ (2 * M) ^ 10 := Nat.pow_le_pow_left hpi 10
      _ = 8 ^ 10 * t ^ 40 := by dsimp [M]; ring
      _ < t ^ 5 * t ^ 40 := Nat.mul_lt_mul_of_pos_right ht5 ht40pos
      _ = N ^ 9 := by dsimp [N]; ring
  have hpBound : ∀ i, (p i : ℝ) < (N : ℝ) ^ (9 / 10 : ℝ) := by
    intro i
    exact lt_nine_tenths_rpow_of_pow (hp_pow i)
  let i0 : Fin k := ⟨0, hkpos⟩
  have hBtwoM : B ≤ 2 * M :=
    (hcluster (p i0) (hpS i0)).1.trans (hp_le_twoM i0)
  have hMpos : 0 < M := by positivity
  have hBpos : 0 < B := hMpos.trans_le hMB
  letI : NeZero B := ⟨hBpos.ne'⟩
  have hloB : M / 16 < B := by
    have hlt : M / 16 < M := Nat.div_lt_self hMpos (by omega)
    exact hlt.trans_le hMB
  let Rfin : Finset (Fin B) :=
    Finset.Icc ⟨M / 16, hloB⟩
      ⟨B / 2, Nat.div_lt_self hBpos (by omega)⟩
  let Q := t / 12
  let R : Finset ℕ :=
    ((Finset.range Q).product Rfin).map (blockEmbedding B)
  have hQ : Q = max T 100 := by
    dsimp [Q, t]
    exact Nat.mul_div_cancel_left _ (by omega : 0 < 12)
  have hM16 : M / 16 = 5184 * (max T 100) ^ 4 := by
    dsimp [M, t]
    rw [show 4 * (12 * max T 100) ^ 4 =
        (5184 * max T 100 ^ 4) * 16 by ring,
      Nat.mul_div_left _ (by norm_num : 0 < 16)]
  have hqH : ∀ q < Q, q * H ≤ M / 16 := by
    intro q hq
    rw [hQ] at hq
    let u := max T 100
    have huq : q ≤ u := hq.le
    rw [hM16]
    calc
      q * H ≤ u * H := Nat.mul_le_mul_right H huq
      _ = 1728 * u ^ 4 := by dsimp [H, t, u]; ring
      _ ≤ 5184 * u ^ 4 := by gcongr <;> norm_num
  have hRsub : R ⊆ survivors N p A := by
    intro x hxR
    change x ∈ ((Finset.range Q).product Rfin).map (blockEmbedding B) at hxR
    rw [Finset.mem_map] at hxR
    obtain ⟨qr, hqr, rfl⟩ := hxR
    rcases qr with ⟨q, r⟩
    have hq : q < Q := Finset.mem_range.mp (Finset.mem_product.mp hqr).1
    have hr := Finset.mem_Icc.mp (Finset.mem_product.mp hqr).2
    have hrlo : M / 16 ≤ r.val := by
      change M / 16 ≤ r.val
      exact hr.1
    have hrhi : r.val ≤ B / 2 := by
      change r.val ≤ B / 2
      exact hr.2
    have hxone : 1 ≤ B * q + r.val := by
      have hloPos : 0 < M / 16 := by
        rw [hM16]
        positivity
      omega
    have hxN : B * q + r.val ≤ N := by
      have hqle : q ≤ Q := hq.le
      have hrB : r.val ≤ B := hrhi.trans (Nat.div_le_self B 2)
      have hprod := Nat.mul_le_mul hBtwoM hqle
      rw [hQ] at hprod
      have hsum := Nat.add_le_add hprod (hrB.trans hBtwoM)
      dsimp [M, N, t] at hsum ⊢
      ring_nf at hsum ⊢
      nlinarith [show 100 ≤ max T 100 from Nat.le_max_right _ _]
    rw [survivors, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨hxone, hxN⟩, ?_⟩
    intro i
    apply not_mem_upperHalf_of_mod_le (hpPrime i)
    apply common_remainder_le_half hMpos hHpos hMB
      (hcluster (p i) (hpS i)).1 (hcluster (p i) (hpS i)).2
      (hqH q hq) hrlo hrhi (hpPrime i)
    · intro hp2
      have hpM := (mem_dyadicPrimes.mp (hSP (hpS i))).1
      rw [hp2] at hpM
      have ht4pos : 0 < t ^ 4 := pow_pos htpos _
      dsimp [M] at hpM
      omega
    · change B * q + r.val = q * B + r.val
      rw [Nat.mul_comm B q]
  have hRcard : R.card = Q * (B / 2 + 1 - M / 16) := by
    dsimp [R, Rfin]
    simpa [Nat.mod_eq_of_lt hloB] using
      alignedBlock_card B Q (M / 16) (B / 2)
        (Nat.div_lt_self hBpos (by omega))
  have hRlarge : (1 / 10 : ℝ) * N < R.card := by
    let u := max T 100
    have hhalfmono : M / 2 ≤ B / 2 := Nat.div_le_div_right hMB
    have hMhalf : M / 2 = 8 * (M / 16) := by
      rw [hM16]
      dsimp [M, t, u]
      rw [show 4 * (12 * max T 100) ^ 4 =
          (41472 * max T 100 ^ 4) * 2 by ring,
        Nat.mul_div_left _ (by norm_num : 0 < 2)]
      ring
    have hinner : 7 * (M / 16) ≤ B / 2 + 1 - M / 16 := by
      omega
    have hnat : 7 * Q * (M / 16) ≤ R.card := by
      rw [hRcard]
      nlinarith [Nat.mul_le_mul_left Q hinner]
    have hreal : (1 / 10 : ℝ) * N < (7 * Q * (M / 16) : ℕ) := by
      let C : ℕ := 7 * Q * (M / 16)
      have huNat : 0 < u := by dsimp [u]; omega
      have hstrict : N < 10 * C := by
        calc
          N = 248832 * u ^ 5 := by dsimp [N, t, u]; ring
          _ < 362880 * u ^ 5 :=
            Nat.mul_lt_mul_of_pos_right (by norm_num) (pow_pos huNat 5)
          _ = 10 * C := by
            dsimp [C]
            rw [hQ, hM16]
            dsimp [u]
            ring
      have hstrictR : (N : ℝ) < (10 * C : ℕ) := by
        exact_mod_cast hstrict
      calc
        (1 / 10 : ℝ) * N < (1 / 10 : ℝ) * (10 * C : ℕ) :=
          mul_lt_mul_of_pos_left hstrictR (by norm_num)
        _ = (C : ℝ) := by push_cast; ring
        _ = (7 * Q * (M / 16) : ℕ) := by rfl
    exact hreal.trans_le (by exact_mod_cast hnat)
  refine ⟨N, p, A, hpPrime, hpMono, hpBound, hAcard, ?_⟩
  have hcardsub := Finset.card_le_card hRsub
  exact hRlarge.trans_le (by exact_mod_cast hcardsub)

/-- Erdős Problem 1202 has a negative answer. -/
theorem erdos_1202 : ¬ Erdos1202Statement := by
  intro hstatement
  obtain ⟨k, hkpos, hk⟩ :=
    hstatement (1 / 10) 1 (by norm_num) (by norm_num)
  obtain ⟨n, p, A, hp, hmono, hp_lt, hAcard, hlarge⟩ :=
    erdos_1202_counterexample k
  have hsmall := hk n p A hp hmono (by
    intro i
    simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num]
      using hp_lt i) hAcard
  exact (not_le_of_gt hlarge) hsmall

end

end Erdos1202

#print axioms Erdos1202.erdos_1202
