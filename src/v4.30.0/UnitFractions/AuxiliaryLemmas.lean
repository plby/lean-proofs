import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import UnitFractions.Definitions
import UnitFractions.ForMathlib.BasicEstimates
import UnitFractions.ForMathlib.Misc

namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

noncomputable section

/-!
This file ports the statement surface of the old `src/aux_lemmas.lean`.

Several results from the Lean 3 file are now available directly in Mathlib 4, sometimes under
slightly different names. In particular, this file mainly re-exports or lightly repackages:

* `tendsto_mul_exp_add_div_pow_atTop`
* `tendsto_nat_ceil_atTop`
* `Nat.dvd_iff_prime_pow_dvd_dvd`
* `ArithmeticFunction.sigma_zero_apply`
* the harmonic-series asymptotics around `Real.eulerMascheroniConstant`

The remaining declarations below are included for API coverage.
-/

theorem tendsto_mul_add_div_pow_log_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (b * x + c) / log x ^ n) atTop atTop :=
  ((tendsto_mul_exp_add_div_pow_atTop b c n hb).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]

theorem tendsto_pow_rec_log_log_at_top {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ (c / Real.log (Real.log x))) atTop atTop := by
  have haux : Tendsto (fun x : ℝ => c * x / Real.log x) atTop atTop := by
    simpa [pow_one, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_mul_add_div_pow_log_at_top c 0 1 hc
  refine ((tendsto_exp_atTop.comp haux).comp tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, div_eq_mul_inv, mul_assoc, mul_left_comm]

theorem tendsto_nat_ceil_at_top {α : Type*} [Semiring α] [LinearOrder α]
    [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α => ⌈x⌉₊) atTop atTop := by
  simpa using (tendsto_nat_ceil_atTop : Tendsto (fun x : α => ⌈x⌉₊) atTop atTop)

theorem weird_floor_sq_tendsto_at_top :
    Tendsto (fun x : ℝ => ⌈Real.logb 2 x⌉₊ ^ 2) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
    tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide)
  simpa using hpow.comp (tendsto_nat_ceil_atTop.comp (Real.tendsto_logb_atTop one_lt_two))

theorem tendsto_pow_at_top_of {f g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l atTop) :
    Tendsto (fun x : ℝ => g x ^ f x) l atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log (g x)) l atTop := tendsto_log_atTop.comp hg
  have hf' : ∀ᶠ x in l, c / 2 ≤ f x := by
    exact (hf.eventually (Ioi_mem_nhds (show c / 2 < c by linarith))).mono fun _ hx => le_of_lt hx
  have hmul : Tendsto (fun x : ℝ => Real.log (g x) * f x) l atTop := by
    have hbase : Tendsto (fun x : ℝ => (c / 2) * Real.log (g x)) l atTop :=
      Tendsto.const_mul_atTop (show 0 < c / 2 by linarith) hlog
    refine tendsto_atTop_mono' _ ?_ hbase
    filter_upwards [hf', hg.eventually_gt_atTop (1 : ℝ)] with x hx hxg
    have hxlog : 0 ≤ Real.log (g x) := le_of_lt (Real.log_pos hxg)
    nlinarith
  refine (tendsto_exp_atTop.comp hmul).congr' ?_
  filter_upwards [hg.eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Function.comp, Real.rpow_def_of_pos hx, mul_comm]

theorem tendsto_pow_rec_loglog_spec_at_top :
    Tendsto (fun x : ℝ => x ^ ((1 : ℝ) - 8 / Real.log (Real.log x))) atTop atTop := by
  refine tendsto_pow_at_top_of zero_lt_one ?_ tendsto_id
  have hzero : Tendsto (fun x : ℝ => (8 : ℝ) / Real.log (Real.log x)) atTop (𝓝 0) := by
    exact
      (show Tendsto (fun _ : ℝ => (8 : ℝ)) atTop (𝓝 8) from tendsto_const_nhds).div_atTop
        (tendsto_log_atTop.comp tendsto_log_atTop)
  simpa using tendsto_const_nhds.sub hzero

section

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

theorem sum_bUnion_le_sum_of_nonneg {f : ℕ → M} {s : Finset ℕ} {t : ℕ → Finset ℕ}
    (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    (s.biUnion t).sum f ≤ ∑ x ∈ s, ∑ i ∈ t x, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert n s hns hs =>
      have hunion :
          (insert n s).biUnion t = s.biUnion t ∪ (t n \ s.biUnion t) := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
          rcases Finset.mem_insert.mp hm with rfl | hm
          · by_cases hxs : x ∈ s.biUnion t
            · exact Finset.mem_union.mpr <| Or.inl hxs
            · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hxm, hxs⟩
          · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_biUnion.mpr ⟨m, hm, hxm⟩
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
            exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
          · exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, (Finset.mem_sdiff.mp hx).1⟩
      have hf' : ∀ x ∈ s.biUnion t, 0 ≤ f x := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
        exact hf x <| Finset.mem_biUnion.mpr ⟨m, Finset.mem_insert_of_mem hm, hxm⟩
      rw [hunion, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_insert hns, add_comm]
      have htail :
          Finset.sum (t n \ s.biUnion t) f ≤ Finset.sum (t n) f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
        intro x hx _
        exact hf x <| Finset.mem_biUnion.mpr ⟨n, Finset.mem_insert_self n s, hx⟩
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add (hs hf') htail

end

theorem nat_cast_diff_issue {x y : ℤ} : (|x - y| : ℝ) = Int.natAbs (x - y) := by
  calc
    |(x : ℝ) - y| = |((x - y : ℤ) : ℝ)| := by norm_num
    _ = ((Int.natAbs (x - y) : ℕ) : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

theorem harmonic_sum_bound_two :
    ∀ᶠ N in (atTop : Filter ℕ), (Finset.sum (range (N + 1)) fun n => (1 : ℝ) / n) ≤
      2 * Real.log N := by
  filter_upwards [eventually_ge_atTop 6] with N hN
  have hN0 : N ≠ 0 := by omega
  have hsum : Finset.sum (range (N + 1)) (fun n => (1 : ℝ) / n) = ((harmonic N : ℚ) : ℝ) := by
    have h1N : 1 ≤ N + 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ h1N]
    rw [Finset.Ico_add_one_right_eq_Icc]
    simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hseq :
      (((harmonic N : ℚ) : ℝ) - Real.log N) = Real.eulerMascheroniSeq' N := by
    simp [Real.eulerMascheroniSeq', hN0]
  have hsmall : (((harmonic N : ℚ) : ℝ) - Real.log N) < 2 / 3 := by
    rw [hseq]
    exact (Real.strictAnti_eulerMascheroniSeq'.antitone (by omega)).trans_lt
      Real.eulerMascheroniSeq'_six_lt_two_thirds
  have hlog : (2 / 3 : ℝ) ≤ Real.log N := by
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
    have hlog2 : Real.log 2 ≤ Real.log N :=
      log_le_log_of_le (show 0 < (2 : ℝ) by norm_num) h2N
    linarith [Real.log_two_gt_d9]
  rw [hsum]
  have : (((harmonic N : ℚ) : ℝ)) ≤ Real.log N + 2 / 3 := by linarith
  refine this.trans ?_
  linarith

theorem sum_le_card_mul_real {A : Finset ℕ} {M : ℝ} {f : ℕ → ℝ}
    (h : ∀ n ∈ A, f n ≤ M) :
    A.sum f ≤ A.card * M := by
  simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul A f M h)

theorem two_in_Icc {a b x y : ℤ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (|x - y| : ℝ) ≤ b - a := by
  rcases Finset.mem_Icc.mp hx with ⟨hax, hxb⟩
  rcases Finset.mem_Icc.mp hy with ⟨hay, hyb⟩
  have habs : |x - y| ≤ b - a := by
    refine abs_le.mpr ?_
    constructor <;> linarith
  exact_mod_cast habs

theorem two_in_Icc' {a b x y : ℤ} (I : Finset ℤ) (hI : I = Icc a b) (hx : x ∈ I) (hy : y ∈ I) :
    (|x - y| : ℝ) ≤ b - a := by
  rw [hI] at hx hy
  exact two_in_Icc hx hy

theorem dvd_iff_ppowers_dvd (d n : ℕ) :
    d ∣ n ↔ ∀ q, q ∣ d → IsPrimePow q → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpkd
    by_cases hk : k = 0
    · simp [hk]
    · exact h (p ^ k) hpkd (hp.isPrimePow.pow hk)

theorem dvd_iff_ppowers_dvd' (d n : ℕ) (hd : d ≠ 0) :
    d ∣ n ↔ ∀ q, q ∣ d → (IsPrimePow q ∧ Nat.Coprime q (d / q)) → q ∣ n := by
  constructor
  · intro hdn q hqd _hq
    exact dvd_trans hqd hdn
  · intro h
    rw [dvd_iff_ppowers_dvd]
    intro q hqd hq
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    let r := p ^ d.factorization p
    have hk' : k ≤ d.factorization p := by
      exact (hp.pow_dvd_iff_le_factorization hd).1 hqd
    have hfac : d.factorization p ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le hk hk')
    have hrd : r ∣ d := by
      dsimp [r]
      simpa using (Nat.ordProj_dvd d p)
    have hqr : p ^ k ∣ r := by
      dsimp [r]
      exact pow_dvd_pow _ hk'
    have hrcond : IsPrimePow r ∧ Nat.Coprime r (d / r) := by
      dsimp [r]
      refine ⟨hp.isPrimePow.pow hfac, ?_⟩
      exact (factorization_eq_iff (n := d) hp hfac).2 rfl |>.2
    exact dvd_trans hqr (h r hrd hrcond)

theorem rec_sum_le_card_div {A : Finset ℕ} {M : ℝ} (hM : 0 < M) (h : ∀ n ∈ A, M ≤ (n : ℝ)) :
    (rec_sum A : ℝ) ≤ A.card / M := by
  have hsum : (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := by
    simp [rec_sum]
  calc
    (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := hsum
    _ ≤ A.card * (1 / M) := sum_le_card_mul_real fun n hn => by
      exact one_div_le_one_div_of_le hM (h n hn)
    _ = A.card / M := by simp [div_eq_mul_inv]

theorem divisor_function_eq_card_divisors {n : ℕ} :
    ArithmeticFunction.sigma 0 n = n.divisors.card := by
  simp [ArithmeticFunction.sigma_zero_apply]

theorem tendsto_coe_log_pow_at_top (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℕ => Real.log x ^ c) atTop atTop := by
  exact (tendsto_rpow_atTop hc).comp tendsto_log_coe_at_top

theorem one_lt_four : (1 : ℝ) < 4 := by norm_num

/-!
Compatibility declarations from the remainder of `src/aux_lemmas.lean`.

Theorems already available directly from Mathlib, such as `sum_pow`, `sum_pow'`, and
`sum_add_sum`, are not duplicated here.
-/

theorem prime_counting_lower_bound_explicit :
    ∀ᶠ N : ℕ in atTop, ⌊Real.sqrt (N : ℝ)⌋₊ ≤ ((Icc 1 N).filter Nat.Prime).card := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  obtain ⟨c, hc₀, hcheb⟩ := chebyshev_first_all
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 : ℝ))
    , tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((1 / c) ^ (4 : ℝ)))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with N hlarge hlogN h2N hcN hloglogN
  have hlogN' : 0 < Real.log N := by simpa [Function.comp] using hlogN
  have hloglogN' : 0 < Real.log (Real.log N) := by simpa [Function.comp] using hloglogN
  have h0N : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_two h2N
  have hcheb' : c * (N : ℝ) ≤ chebyshev_first N := by
    have := hcheb (N : ℝ) h2N
    rw [Real.norm_of_nonneg (show 0 ≤ (N : ℝ) by positivity),
      Real.norm_of_nonneg (chebyshev_first_nonneg (N : ℝ))] at this
    simpa using this
  have htriv : chebyshev_first N ≤ (π N : ℝ) * Real.log N := by
    simpa using (chebyshev_first_trivial_bound (N : ℝ))
  rw [← prime_counting_eq_card_primes]
  refine Nat.floor_le_of_le ?_
  refine le_of_mul_le_mul_right ?_ hlogN'
  refine le_trans ?_ <| le_trans hcheb' htriv
  refine (Real.log_le_log_iff (mul_pos (Real.sqrt_pos.2 h0N) hlogN')
    (mul_pos hc₀ h0N)).mp ?_
  rw [Real.log_mul (Real.sqrt_pos.2 h0N).ne' hlogN'.ne', Real.sqrt_eq_rpow,
    Real.log_rpow h0N, Real.log_mul hc₀.ne' (show (N : ℝ) ≠ 0 by positivity)]
  have hlargeAbs : |Real.log (Real.log N)| ≤ (1 / 4 : ℝ) * |Real.log N| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge
  have hlarge' : Real.log (Real.log N) ≤ (1 / 4 : ℝ) * Real.log N := by
    rw [abs_of_pos hloglogN', abs_of_pos hlogN'] at hlargeAbs
    exact hlargeAbs
  have hcN' : Real.log (1 / c) ≤ (1 / 4 : ℝ) * Real.log N := by
    have hlog := Real.log_le_log (show 0 < (1 / c) ^ (4 : ℝ) by positivity) hcN
    rw [Real.log_rpow (one_div_pos.mpr hc₀)] at hlog
    nlinarith
  have hc' : Real.log c = -Real.log (1 / c) := by
    have hcinv : Real.log (1 / c) = -Real.log c := by
      rw [one_div]
      exact Real.log_inv c
    linarith
  rw [hc']
  have hleft : (1 / 2 : ℝ) * Real.log N + Real.log (Real.log N) ≤ (3 / 4 : ℝ) * Real.log N := by
    linarith
  have hright : (3 / 4 : ℝ) * Real.log N ≤ -Real.log (1 / c) + Real.log N := by
    linarith
  exact le_trans hleft hright

theorem something_like_this {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (A B : Finset ι)
    (hA : A.card = B.card) :
    (∑ g : B ≃ A, ∏ j : B, f (g j)) = B.card.factorial * A.prod f := by
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_const, nsmul_eq_mul]
    congr 2
    let e : B ≃ A := Fintype.equivOfCardEq (by simpa using hA.symm)
    simpa [e] using Fintype.card_equiv e
  · intro g _
    rw [← Finset.prod_coe_sort A]
    exact Fintype.prod_equiv g _ _ (fun x ↦ rfl)

theorem my_function_aux {n : ℕ} :
    (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  change Multiset.count x (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) :
    Multiset ℕ) ≤ 1
  rw [Finsupp.sum, Multiset.count_sum']
  simp only [Multiset.count_singleton]
  rw [← Finset.card_filter]
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter] at ha hb
  have hpa : Nat.Prime a := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using ha.1
  have hpb : Nat.Prime b := Nat.prime_of_mem_primeFactors <| by
    simpa [Nat.support_factorization] using hb.1
  apply eq_of_prime_pow_eq (Nat.prime_iff.mp hpa) (Nat.prime_iff.mp hpb)
  · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha.1)
  · exact ha.2.symm.trans hb.2

def my_function (n : ℕ) : Finset ℕ :=
  ((((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).toFinset)

theorem card_my_function {n : ℕ} : (my_function n).card = ω n := by
  calc
    (my_function n).card =
        (((Nat.factorization n).sum fun p k ↦ ({p ^ k} : Multiset ℕ)) : Multiset ℕ).card := by
          exact Multiset.toFinset_card_of_nodup my_function_aux
    _ = n.factorization.support.card := by
      rw [Finsupp.sum, Multiset.card_sum]
      simp
    _ = n.primeFactors.card := by rw [Nat.support_factorization]
    _ = ω n := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      symm
      simpa using
        (Multiset.card_toFinset (m := (n.primeFactorsList : Multiset ℕ)))

theorem prod_my_function {n : ℕ} (hn : n ≠ 0) :
    (my_function n).prod id = n := by
  rw [← Finset.prod_val, my_function, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr my_function_aux,
    Finsupp.sum, Multiset.prod_sum]
  simp only [Multiset.prod_singleton]
  exact Nat.prod_factorization_pow_eq_self hn

theorem my_function_injective {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    my_function n = my_function m → n = m := by
  intro h
  rw [← prod_my_function hn, h, prod_my_function hm]

theorem rec_sum_le_prod_sum_aux {A : Finset ℕ} (t : ℕ) (hA : 0 ∉ A) :
    (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) ≤
      ((ppowers_in_set A).powersetCard t).sum fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n) := by
  have hsubset :
      (A.filter fun n : ℕ ↦ ω n = t).image my_function ⊆ (ppowers_in_set A).powersetCard t := by
    intro B hB
    rcases Finset.mem_image.mp hB with ⟨n, hn, rfl⟩
    rw [Finset.mem_powersetCard]
    constructor
    · intro m hm
      simp only [my_function, Multiset.mem_toFinset, Finsupp.sum, Multiset.mem_sum,
        Multiset.mem_singleton] at hm
      rcases hm with ⟨a, ha, rfl⟩
      rw [mem_ppowers_in_set']
      · exact ⟨n, (Finset.mem_filter.mp hn).1, rfl⟩
      · exact Nat.prime_of_mem_primeFactors <| by simpa [Nat.support_factorization] using ha
      · exact Finsupp.mem_support_iff.mp ha
    · exact (card_my_function (n := n)).trans ((Finset.mem_filter.mp hn).2)
  have himage :
      (A.filter (fun n : ℕ ↦ ω n = t)).sum (fun i ↦ (1 : ℝ) / i) =
        ((A.filter fun n : ℕ ↦ ω n = t).image my_function).sum
          (fun x ↦ x.prod (fun n ↦ (1 : ℝ) / n)) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro x hx
      simp only [one_div]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
      exact (congrArg (fun z : ℕ => ((z : ℝ) : ℝ)⁻¹)
        (prod_my_function (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA))).symm
    · intro x hx y hy hxy
      exact my_function_injective (ne_of_mem_of_not_mem (Finset.mem_filter.mp hx).1 hA)
        (ne_of_mem_of_not_mem (Finset.mem_filter.mp hy).1 hA) hxy
  rw [himage]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro i _ _
  refine Finset.prod_nonneg ?_
  intro j _
  rw [one_div]
  exact inv_nonneg.mpr (by positivity : 0 ≤ (j : ℝ))

theorem rec_sum_le_prod_sum {A : Finset ℕ} (hA₀ : 0 ∉ A) {I : Finset ℕ}
    (hI : ∀ n ∈ A, ω n ∈ I) :
    (rec_sum A : ℝ) ≤
      I.sum (fun t ↦ ((ppowers_in_set A).sum fun q ↦ (1 / q : ℝ)) ^ t / Nat.factorial t) := by
  classical
  let w : ℕ → ℝ := fun q ↦ (1 : ℝ) / q
  have hpowcard :
      ∀ s : Finset ℕ, ∀ t : ℕ,
        (s.powersetCard t).sum (fun x ↦ x.prod w) ≤ (s.sum w) ^ t / Nat.factorial t := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro t
      cases t with
      | zero =>
          simp [w, Finset.powersetCard_zero]
      | succ t =>
          rw [Finset.powersetCard_eq_empty.mpr (Nat.succ_pos t)]
          simp [w]
    · intro a s ha hs t
      cases t with
      | zero =>
          simp [w, ha, Finset.powersetCard_zero]
      | succ t =>
          have hdisj :
              Disjoint (s.powersetCard t.succ) ((s.powersetCard t).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rcases Finset.mem_image.mp hx2 with ⟨y, hy, rfl⟩
            have hxsub : insert a y ⊆ s := (Finset.mem_powersetCard.mp hx1).1
            exact ha (hxsub (by simp))
          have hy_not : ∀ y ∈ s.powersetCard t, a ∉ y := by
            intro y hy hay
            exact ha ((Finset.mem_powersetCard.mp hy).1 hay)
          rw [Finset.powersetCard_succ_insert ha t, Finset.sum_union hdisj, Finset.sum_image]
          swap
          · intro y hy z hz h
            apply Finset.ext
            intro b
            by_cases hb : b = a
            · subst hb
              simp [hy_not y hy, hy_not z hz]
            · have hmem := congrArg (fun s : Finset ℕ => b ∈ s) h
              simpa [hb] using hmem
          have hins :
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                w a * ∑ y ∈ s.powersetCard t, y.prod w := by
            calc
              ∑ y ∈ s.powersetCard t, (insert a y).prod w =
                  ∑ y ∈ s.powersetCard t, w a * y.prod w := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.prod_insert (hy_not y hy)]
              _ = w a * ∑ y ∈ s.powersetCard t, y.prod w := by
                    rw [← Finset.mul_sum]
          have hwa_nonneg : 0 ≤ w a := by
            dsimp [w]
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le a
          have hs_nonneg : 0 ≤ s.sum w := by
            refine Finset.sum_nonneg ?_
            intro i hi
            dsimp [w]
            rw [one_div_nonneg]
            exact_mod_cast Nat.zero_le i
          rw [hins]
          have hmain :
              (s.powersetCard t.succ).sum (fun x ↦ x.prod w) +
                  w a * ∑ x ∈ s.powersetCard t, x.prod w ≤
                (s.sum w) ^ t.succ / Nat.factorial t.succ +
                  w a * ((s.sum w) ^ t / Nat.factorial t) := by
            exact add_le_add (hs t.succ) (mul_le_mul_of_nonneg_left (hs t) hwa_nonneg)
          refine le_trans hmain ?_
          have hbinom :
              (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t ≤
                (s.sum w + w a) ^ t.succ := by
            by_cases hsum : s.sum w = 0
            · rw [hsum]
              cases t with
              | zero => simp
              | succ t => simp [hwa_nonneg]
            · have hsum0 : 0 < s.sum w := lt_of_le_of_ne hs_nonneg (by simpa [eq_comm] using hsum)
              have hratio :
                  -2 ≤ w a / s.sum w := by
                have hratio0 : 0 ≤ w a / s.sum w := div_nonneg hwa_nonneg hs_nonneg
                linarith
              have hpow :
                  (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) ≤
                    (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := by
                exact
                  mul_le_mul_of_nonneg_left (one_add_mul_le_pow hratio t.succ)
                    (pow_nonneg hs_nonneg _)
              calc
                (s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t =
                    (s.sum w) ^ t.succ * (1 + (t.succ : ℝ) * (w a / s.sum w)) := by
                      rw [pow_succ']
                      field_simp [hsum]
                _ ≤ (s.sum w) ^ t.succ * (1 + w a / s.sum w) ^ t.succ := hpow
                _ = (s.sum w * (1 + w a / s.sum w)) ^ t.succ := by rw [mul_pow]
                _ = (s.sum w + w a) ^ t.succ := by
                  congr 1
                  field_simp [hsum]
          have hfact :
              (s.sum w) ^ t.succ / Nat.factorial t.succ + w a * ((s.sum w) ^ t / Nat.factorial t) =
                ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) /
                  Nat.factorial t.succ := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp [show (Nat.factorial t : ℝ) ≠ 0 by positivity]
          rw [hfact]
          have hdiv :
              ((s.sum w) ^ t.succ + (t.succ : ℝ) * w a * (s.sum w) ^ t) / Nat.factorial t.succ ≤
                (s.sum w + w a) ^ t.succ / Nat.factorial t.succ :=
            div_le_div_of_nonneg_right hbinom (by positivity)
          refine hdiv.trans_eq ?_
          simp [Finset.sum_insert, ha, w, add_comm]
  rw [rec_sum]
  push_cast
  have hA : I.biUnion (fun t ↦ A.filter fun n : ℕ ↦ ω n = t) = A := by
    simpa using
      (Finset.biUnion_filter_eq_of_maps_to (s := A) (t := I) (f := fun n : ℕ ↦ ω n) hI)
  nth_rewrite 1 [← hA]
  refine le_trans (sum_bUnion_le_sum_of_nonneg ?_) ?_
  · intro n hn
    rw [one_div_nonneg]
    exact_mod_cast Nat.zero_le n
  refine Finset.sum_le_sum ?_
  intro t ht
  refine le_trans (rec_sum_le_prod_sum_aux t hA₀) ?_
  simpa [w] using hpowcard (ppowers_in_set A) t

theorem such_large_N_wow :
    ∀ᶠ N : ℕ in atTop, 2 * log (log (⌈Real.logb 2 N⌉₊ ^ 2)) < (1 / 500 : ℝ) * log (log N) := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 8000 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 / log 2 : ℝ)))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (exp (exp (2 * log ((2 : ℕ) : ℝ))) * log 2))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.sqrt 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (1500 * log 2 * 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux ] with
    N h1N h1logN hlogN' hlog2logN hcomplogN hsqrtlogN hloglogN hlarge1
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one h1logN
  have h0loglogN : 0 < log (log N) := by
    refine lt_trans ?_ hloglogN
    refine mul_pos ?_ zero_lt_two
    refine mul_pos ?_ (log_pos one_lt_two)
    norm_num1
  have h2000 : (0 : ℝ) < 1500 := by norm_num1
  have hhelper : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ 2 := by
    refine le_trans (le_of_lt (Nat.ceil_lt_add_one ?_)) ?_
    · exact Real.logb_nonneg one_lt_two h1N
    rw [← add_halves (log N ^ 2)]
    refine add_le_add ?_ ?_
    · rw [Real.logb]
      rw [div_eq_mul_inv]
      have htmp : (log 2)⁻¹ ≤ log N / 2 := by
        rw [le_div_iff₀ zero_lt_two]
        simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlogN'
      calc
        log N * (log 2)⁻¹ ≤ log N * (log N / 2) := by gcongr
        _ = log N ^ 2 / 2 := by ring
    · rw [le_div_iff₀, one_mul, ← Real.sqrt_le_left]
      · exact hsqrtlogN
      · exact le_of_lt h0logN
      · exact zero_lt_two
  have hhelper2 : (1 : ℝ) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, one_lt_div (log_pos one_lt_two)]
    · exact hlog2logN
  have hhelper3 : exp (exp (2 * log ↑2)) < ⌈Real.logb 2 N⌉₊ := by
    refine lt_of_lt_of_le ?_ (Nat.le_ceil _)
    rw [Real.logb, lt_div_iff₀ (log_pos one_lt_two)]
    exact hcomplogN
  have hloglogN' : 1500 * log 2 * 2 < log (log N) := by
    simpa [Function.comp] using hloglogN
  have hhelperR : (⌈Real.logb 2 N⌉₊ : ℝ) ≤ log N ^ (2 : ℝ) := by
    simpa [Real.rpow_natCast] using hhelper
  have hlogceil :
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log 2 + log (log (log N)) := by
    have hinner :
        log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := by
      refine Real.log_le_log (log_pos hhelper2) ?_
      exact Real.log_le_log (lt_trans zero_lt_one hhelper2) hhelperR
    calc
      log (log (⌈Real.logb 2 N⌉₊ : ℝ)) ≤ log (log (log N ^ (2 : ℝ))) := hinner
      _ = log 2 + log (log (log N)) := by
        rw [Real.log_rpow h0logN, Real.log_mul two_ne_zero h0loglogN.ne']
  have hlarge1' : |log (log (log N))| ≤ (1 / 8000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, Real.norm_eq_abs] using hlarge1
  have hbigconst : (1 : ℝ) < 1500 * log 2 * 2 := by
    nlinarith [Real.log_two_gt_d9]
  have h0logloglogN : 0 < log (log (log N)) := by
    refine Real.log_pos ?_
    exact lt_trans hbigconst hloglogN'
  rw [← Real.rpow_natCast, Real.log_rpow (lt_trans zero_lt_one hhelper2)]
  have hmul :
      log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) =
        log 2 + log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    rw [Real.log_mul two_ne_zero (log_pos hhelper2).ne']
  change 2 * log ((2 : ℝ) * log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N)
  rw [hmul, mul_add]
  have hstep1 :
      2 * log 2 + 2 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) <
        (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
    have haux' : 2 * log 2 < log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by
      refine (lt_log_iff_exp_lt (log_pos hhelper2)).2 ?_
      refine (lt_log_iff_exp_lt (lt_trans zero_lt_one hhelper2)).2 ?_
      exact hhelper3
    linarith
  have hstep2 :
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) < (1 / 500 : ℝ) * log (log N) := by
    have hconst : 3 * log 2 < (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hsmall :
        3 * log (log (log N)) ≤ (1 / 1000 : ℝ) * log (log N) := by
      rw [abs_of_pos h0logloglogN, abs_of_pos h0loglogN] at hlarge1'
      have : log (log (log N)) ≤ (1 / 8000 : ℝ) * log (log N) := hlarge1'
      linarith
    calc
      (2 + 1) * log (log (⌈Real.logb 2 N⌉₊ : ℝ))
          = 3 * log (log (⌈Real.logb 2 N⌉₊ : ℝ)) := by ring
      _ ≤ 3 * (log 2 + log (log (log N))) := by gcongr
      _ < (1 / 500 : ℝ) * log (log N) := by linarith
  exact lt_trans hstep1 hstep2

theorem explicit_mertens :
    ∀ᶠ N : ℕ in atTop,
      (((range (N + 1)).filter IsPrimePow).sum (fun q ↦ (1 / q : ℝ)) : ℝ) ≤ 2 * log (log N) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  obtain ⟨c, hc₀, hc⟩ := hb.exists_pos
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (c : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (b + 1))
    , tendsto_natCast_atTop_atTop.eventually hc.bound ] with N hN₁ hN₂ hN₃
  dsimp at hN₁ hN₂
  have hN₄ : 0 < log N := hc₀.trans_le hN₁
  simp_rw [norm_inv, ← div_eq_mul_inv, ← one_div, norm_eq_abs, abs_of_nonneg hN₄.le,
    Nat.floor_natCast]
    at hN₃
  have hdiv : c / log N ≤ 1 := by
    rw [div_le_iff₀ hN₄]
    linarith
  have hmain := sub_le_iff_le_add.1 (sub_le_of_abs_sub_le_right (hN₃.trans hdiv))
  convert hmain.trans (show log (log N) + b + 1 ≤ 2 * log (log N) by linarith) using 2
  rw [range_eq_Ico, Finset.Ico_add_one_right_eq_Icc]
  ext n
  simpa only
    [Finset.mem_filter, and_congr_left_iff, Finset.mem_Icc, zero_le', iff_and_self, true_and]
    using fun h _ => (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h.ne_zero, h.ne_one⟩).le

theorem card_factors_le_log {n : ℕ} : Ω n ≤ ⌊Real.logb 2 n⌋₊ := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hΩ : Ω n = 0
  · rw [hΩ]
    exact Nat.zero_le _
  have h0n : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : 2 ^ Ω n ≤ n := by
    rw [ArithmeticFunction.cardFactors_apply]
    calc
      2 ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
        exact List.pow_card_le_prod _ _ fun p hp =>
          (Nat.prime_of_mem_primeFactorsList hp).two_le
      _ = n := Nat.prod_primeFactorsList hn
  exact Nat.le_floor <| (Real.le_logb_iff_rpow_le one_lt_two h0n).2 <| by
    simpa [Real.rpow_natCast] using (show ((2 : ℕ) ^ Ω n : ℝ) ≤ n by exact_mod_cast hpow)

theorem this_condition_here {p : ℕ → Prop} [DecidablePred p] {A : Finset ℕ}
    (hA : ∀ a ∈ A, p a) {N : ℕ} (hN : A.card ≤ ((range N).filter p).card)
    (h : ¬ (range N).filter p ⊆ A) :
    (∃ r < N, r ∉ A ∧ p r ∧ ∃ a ∈ A, r < a) ∨ A ⊂ (range N).filter p := by
  let _ := hN
  have h₁ : (((range N).filter p) \ A).Nonempty := by
    rwa [Finset.sdiff_nonempty]
  rw [or_iff_not_imp_right]
  intro h₂
  have h₂ : (A \ ((range N).filter p)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h'
    exact h₂ ⟨h', h⟩
  obtain ⟨r, hr⟩ := h₁
  obtain ⟨a, ha⟩ := h₂
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hr
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and', not_lt] at ha
  exact ⟨r, hr.1.1, hr.2, hr.1.2, a, ha.1, hr.1.1.trans_le (ha.2 (hA _ ha.1))⟩

theorem prime_power_recip_downward_bound (A : Finset ℕ) (ha : ∀ q ∈ A, IsPrimePow q)
    (N : ℕ) (hN : A.card ≤ ((range N).filter IsPrimePow).card) :
    A.sum (fun q ↦ (1 : ℝ) / q) ≤ ((range N).filter IsPrimePow).sum (fun q ↦ (1 : ℝ) / q) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.sum_empty]
    refine Finset.sum_nonneg ?_
    simp
  let a := A.max' hA
  let choices : Finset (Finset ℕ) :=
    (((range (a + 1)).filter IsPrimePow).powerset.filter fun B =>
      B.card ≤ ((range N).filter IsPrimePow).card)
  have hAc : A ∈ choices := by
    simp only [choices, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range,
      Nat.lt_add_one_iff]
    exact ⟨fun b hb ↦ ⟨Finset.le_max' _ _ hb, ha _ hb⟩, hN⟩
  by_cases haN : a < N
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun a' ha' => ?_) ?_
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(Finset.le_max' _ _ ha').trans_lt haN, ha _ ha'⟩
    · simp
  have haN : N ≤ a := Nat.le_of_not_gt haN
  have hchoices : choices.Nonempty := ⟨A, hAc⟩
  obtain ⟨B, hB, hB'⟩ := Finset.exists_max_image choices
    (fun B ↦ B.sum fun q ↦ (1 : ℝ) / q) hchoices
  simp only [choices, Finset.mem_filter, Finset.mem_powerset] at hB
  suffices hEq : (range N).filter IsPrimePow = B by
    rw [hEq]
    exact hB' _ hAc
  suffices hsub : (range N).filter IsPrimePow ⊆ B by
    exact Finset.eq_of_subset_of_card_le hsub hB.2
  by_contra h
  have hBpp : ∀ a : ℕ, a ∈ B → IsPrimePow a := by
    intro x hx
    exact (Finset.mem_filter.mp (hB.1 hx)).2
  rcases this_condition_here hBpp hB.2 h with
    ⟨r, hr, hr', hr'', a', ha', hra'⟩ | hssub
  · have hr''' : r ∉ B.erase a' := fun hrB ↦ hr' (Finset.erase_subset _ _ hrB)
    let B' := (B.erase a').cons r hr'''
    have hra : r ≤ a := hra'.le.trans <| by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (hB.1 ha')).1)
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change (B.erase a').cons r hr''' ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
          exact ⟨hra, hr''⟩
        · exact (Finset.erase_subset _ _).trans hB.1
      · change ((B.erase a').cons r hr''').card ≤ ((range N).filter IsPrimePow).card
        have hcard :
            ((B.erase a').cons r hr''').card = B.card := by
          rw [Finset.card_cons, Finset.card_erase_of_mem ha',
            Nat.sub_add_cancel (Finset.card_pos.mpr ⟨a', ha'⟩)]
        exact hcard.symm ▸ hB.2
    have hmax := hB' B' hB''
    rw [Finset.sum_cons, ← Finset.add_sum_erase _ _ ha', add_le_add_iff_right] at hmax
    exact (not_le_of_gt hra') <| Nat.cast_le.mp <|
      le_of_one_div_le_one_div (by exact_mod_cast hr''.pos) hmax
  · obtain ⟨b, hb, hb'⟩ := Finset.ssubset_iff_exists_cons_subset.mp hssub
    let B' := B.cons b hb
    have hB'' : B' ∈ choices := by
      simp only [choices, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · change B.cons b hb ⊆ (range (a + 1)).filter IsPrimePow
        rw [Finset.cons_subset]
        constructor
        · have hbmem := hb' (Finset.mem_cons_self b B)
          rw [Finset.mem_filter, Finset.mem_range] at hbmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hbmem.1.le.trans haN, hbmem.2⟩
        · intro x hx
          have hxmem := hb' (Finset.mem_cons_of_mem hx)
          rw [Finset.mem_filter, Finset.mem_range] at hxmem
          rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff] at ⊢
          exact ⟨hxmem.1.le.trans haN, hxmem.2⟩
      · change (B.cons b hb).card ≤ ((range N).filter IsPrimePow).card
        exact Finset.card_le_card hb'
    have hmax := hB' _ hB''
    rw [Finset.sum_cons, add_le_iff_nonpos_left, one_div_nonpos, ← Nat.cast_zero, Nat.cast_le,
      le_zero_iff] at hmax
    have hbmem : b ∈ (range N).filter IsPrimePow := hb' (Finset.mem_cons_self b B)
    exact (Finset.mem_filter.mp hbmem).2.pos.ne' hmax

theorem Omega_eq_card_prime_pow_divisors {n : ℕ} (hn : n ≠ 0) :
    Ω n = (n.divisors.filter IsPrimePow).card := by
  revert hn
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp hk hpk
    rw [Nat.divisors_prime_pow hp, ArithmeticFunction.cardFactors_apply_prime_pow hp]
    have hfilter :
        (Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩
          (Finset.range (k + 1))).filter IsPrimePow =
          Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Finset.Ico 1 (k + 1)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨hx, hxpp⟩
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := by
          intro hi0
          exact not_isPrimePow_one (by simpa [hi0] using hxpp)
        refine Finset.mem_map.mpr ⟨i, Finset.mem_Ico.mpr ?_, rfl⟩
        exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0), Finset.mem_range.mp hi⟩
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        have hi0 : i ≠ 0 := by
          exact (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp hi).1).ne'
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_map.mpr ⟨i, Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2, rfl⟩
        · exact (isPrimePow_pow_iff hi0).2 hp.isPrimePow
    rw [hfilter, Finset.card_map]
    rw [Nat.card_Ico]
    omega
  · simp
  · simp [Finset.filter_singleton, not_isPrimePow_one]
  · intro a b ha hb hab haI hbI hab0
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
      ArithmeticFunction.cardFactors_mul ha0 hb0, haI ha0, hbI hb0,
      Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro d hdA hdB
    have hda : d ∣ a := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdA).1
    have hdb : d ∣ b := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdB).1
    have hd1 : d = 1 := Nat.eq_one_of_dvd_coprimes hab hda hdb
    exact (not_isPrimePow_one <| hd1 ▸ (Finset.mem_filter.mp hdA).2).elim

theorem rec_pp_sum_close :
    ∀ᶠ N : ℕ in atTop,
      ∀ x y : ℤ,
        x ≠ y →
          |(x : ℝ) - y| ≤ N →
            ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
                (fun q : ℕ ↦ (1 : ℝ) / q) <
              ((1 : ℝ) / 500) * log (log N) := by
  filter_upwards
    [ eventually_gt_atTop 0
    , such_large_N_wow
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        prime_counting_lower_bound_explicit
    , (weird_floor_sq_tendsto_at_top.comp tendsto_natCast_atTop_atTop).eventually
        explicit_mertens ] with N hlarge0 hlarge1 hprimes hmertens x y hxy hxyN
  let m := Int.natAbs (x - y)
  let M := Ω m
  let T := ⌈Real.logb 2 N⌉₊ ^ 2
  have hm : m ≠ 0 := by
    rwa [Int.natAbs_ne_zero, sub_ne_zero]
  have hMT : M ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
    calc
      M ≤ ⌊Real.logb 2 m⌋₊ := card_factors_le_log
      _ ≤ ⌊Real.sqrt T⌋₊ := by
        refine Nat.le_floor ?_
        have hlogm_nonneg : 0 ≤ Real.logb 2 m := by
          exact Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hm)
        refine le_trans (Nat.floor_le hlogm_nonneg) ?_
        calc
          Real.logb 2 m ≤ Real.logb 2 N := by
            rw [nat_cast_diff_issue] at hxyN
            exact Real.logb_le_logb_of_le one_lt_two
              (by exact_mod_cast Nat.pos_of_ne_zero hm) hxyN
          _ ≤ Real.sqrt T := by
            dsimp [T]
            push_cast
            rw [Real.sqrt_sq]
            · exact_mod_cast Nat.le_ceil (Real.logb 2 N)
            · positivity
      _ ≤ ((Finset.Icc 1 T).filter Nat.Prime).card := hprimes
      _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_filter, Finset.mem_Icc] at hp
        rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
        exact ⟨hp.1.2, hp.2.isPrimePow⟩
  calc
    ((range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ (n : ℤ) ∣ x ∧ (n : ℤ) ∣ y)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) ≤
      ((Finset.range (N + 1)).filter (fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m)).sum
        (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro q hq
            rw [Finset.mem_filter] at hq
            rw [Finset.mem_filter]
            refine ⟨hq.1, hq.2.1, ?_⟩
            exact Int.natCast_dvd_natCast.mp <| by
              simpa [m] using Int.dvd_natAbs.mpr (dvd_sub hq.2.2.1 hq.2.2.2)
          · intro q _ _
            positivity
    _ ≤ ((Finset.range (T + 1)).filter IsPrimePow).sum (fun q : ℕ ↦ (1 : ℝ) / q) := by
          refine prime_power_recip_downward_bound _ ?_ _ ?_
          · intro q hq
            exact (Finset.mem_filter.mp hq).2.1
          · have hcard :
                ((Finset.range (N + 1)).filter fun n : ℕ ↦ IsPrimePow n ∧ n ∣ m).card ≤ Ω m := by
              rw [Omega_eq_card_prime_pow_divisors hm]
              refine Finset.card_le_card ?_
              intro x hx
              rcases Finset.mem_filter.mp hx with ⟨_, hxpp, hxdvd⟩
              refine Finset.mem_filter.mpr ?_
              constructor
              · rw [Nat.mem_divisors]
                exact ⟨hxdvd, hm⟩
              · exact hxpp
            exact hcard.trans hMT
    _ < ((1 : ℝ) / 500) * log (log N) := by
          refine lt_of_le_of_lt hmertens ?_
          dsimp [T]
          push_cast
          exact hlarge1

theorem ppowers_count_eq_prime_count {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card =
      (n.divisors.filter Nat.Prime).card := by
  let f : ℕ → ℕ := fun p ↦ p ^ n.factorization p
  have h₁ :
      n.divisors.filter (fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)) =
        (n.divisors.filter Nat.Prime).image f := by
    ext r
    rw [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro ha
      have hdivr : r ∣ n := Nat.dvd_of_mem_divisors ha.1
      rcases (isPrimePow_nat_iff r).1 ha.2.1 with ⟨p, k, hp, hk, hpk⟩
      have hdivpk : p ^ k ∣ n := by simpa [hpk] using hdivr
      have hcop : Nat.Coprime (p ^ k) (n / p ^ k) := by simpa [hpk] using ha.2.2
      refine ⟨p, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨dvd_trans (dvd_pow_self _ hk.ne') hdivpk, hn⟩, hp⟩
      · dsimp [f]
        rw [← hpk, (coprime_div_iff hp hdivpk hk.ne' hcop).symm]
    · rintro ⟨p, hp, hpa⟩
      subst r
      rcases Finset.mem_filter.mp hp with ⟨hpDiv, hpPrime⟩
      have hpdvd : p ∣ n := Nat.dvd_of_mem_divisors hpDiv
      have h0fac : 0 < n.factorization p := hpPrime.factorization_pos_of_dvd hn hpdvd
      refine ⟨?_, hpPrime.isPrimePow.pow h0fac.ne', ?_⟩
      · rw [Nat.mem_divisors]
        exact ⟨Nat.ordProj_dvd n p, hn⟩
      · have : n.factorization p = n.factorization p := rfl
        rw [← factorization_eq_iff hpPrime h0fac.ne'] at this
        exact this.2
  rw [h₁]
  refine Finset.card_image_of_injOn ?_
  intro p₁ hp₁ p₂ hp₂ hps
  rcases Finset.mem_filter.mp hp₁ with ⟨hp₁div, hp₁prime⟩
  rcases Finset.mem_filter.mp hp₂ with ⟨hp₂div, hp₂prime⟩
  exact eq_of_prime_pow_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hp₂prime)
    (hp₁prime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_divisors hp₁div)) hps

theorem omega_count_eq_ppowers {n : ℕ} :
    (n.divisors.filter fun r : ℕ ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card = ω n := by
  by_cases hn0 : n = 0
  · rw [hn0]
    simp
  · rw [ppowers_count_eq_prime_count hn0]
    have hEq : n.divisors.filter Nat.Prime = n.primeFactors := by
      ext q
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors_of_ne_zero hn0]
      constructor
      · intro h
        exact ⟨h.2, h.1.1⟩
      · intro h
        exact ⟨⟨h.2, hn0⟩, h.1⟩
    rw [hEq, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

theorem exp_pol_lbound (k : ℕ) (x : ℝ) (h : 0 < x) : x ^ k < k.factorial * exp x := by
  let f : ℕ → ℝ := fun i ↦ x ^ i / i.factorial
  have hsum_nonneg : 0 ≤ Finset.sum (Finset.range k) f := by
    exact Finset.sum_nonneg fun _ _ ↦ by
      change 0 ≤ x ^ _ / _
      positivity
  have hsum_eq :
      Finset.sum (Finset.range (k + 2)) f = Finset.sum (Finset.range k) f + f k + f (k + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum :
      f k + f (k + 1) ≤ Finset.sum (Finset.range (k + 2)) f := by
    rw [hsum_eq]
    nlinarith
  have hpos : 0 < f (k + 1) := by
    change 0 < x ^ (k + 1) / (k + 1).factorial
    positivity
  have hlt :
      f k < Finset.sum (Finset.range (k + 2)) f := by
    calc
      f k < f k + f (k + 1) := by
        exact lt_add_of_pos_right (f k) hpos
      _ ≤ Finset.sum (Finset.range (k + 2)) f := hsum
  have hexp : Finset.sum (Finset.range (k + 2)) f ≤ exp x :=
    by simpa [f] using Real.sum_le_exp_of_nonneg (le_of_lt h) (k + 2)
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hdiv : f k < exp x := lt_of_lt_of_le hlt hexp
  simp [f] at hdiv
  simpa [mul_comm] using (div_lt_iff₀ hfac).mp hdiv

theorem factorial_bound (t : ℕ) : ((t : ℝ) * exp (-1)) ^ t ≤ t.factorial := by
  by_cases h0 : t = 0
  · simp [h0]
  · have ht : 0 < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hlt : (t : ℝ) ^ t / exp t < t.factorial := by
      have hmain := exp_pol_lbound t t ht
      have hexp : 0 < exp (t : ℝ) := Real.exp_pos _
      rw [div_lt_iff₀ hexp]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    have hpoweq : ((t : ℝ) * exp (-1)) ^ t = (t : ℝ) ^ t / exp t := by
      calc
        ((t : ℝ) * exp (-1)) ^ t = (t : ℝ) ^ t * (exp (-1)) ^ t := by rw [mul_pow]
        _ = (t : ℝ) ^ t * exp ((t : ℝ) * (-1)) := by
          rw [← Real.exp_nat_mul (-1) t]
        _ = (t : ℝ) ^ t / exp t := by
          rw [show ((t : ℝ) * (-1)) = -(t : ℝ) by ring, Real.exp_neg, div_eq_mul_inv]
    exact le_of_lt (hpoweq ▸ hlt)

theorem helpful_decreasing_bound {x y : ℝ} {n : ℕ} (h0y : 0 < y) (hn : x ≤ n) (hy : y ≤ x) :
    (y / (n * exp (-1))) ^ n ≤ (y / (x * exp (-1))) ^ x := by
  have hx0 : 0 < x := lt_of_lt_of_le h0y hy
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le hx0 hn
  have hnexp : 0 < (n * exp (-1)) := mul_pos hn0 (exp_pos (-1))
  have hxexp : 0 < x * exp (-1) := mul_pos hx0 (exp_pos (-1))
  have hleft : 0 < y / (n * exp (-1)) := div_pos h0y hnexp
  have hright : 0 < y / (x * exp (-1)) := div_pos h0y hxexp
  let f : ℝ → ℝ := fun t ↦ (log y + 1) * t - t * log t
  have hderiv : ∀ t, t ≠ 0 → deriv f t = log y - log t := by
    intro t ht
    have hsub := deriv_fun_sub
      (f := fun s : ℝ ↦ (log y + 1) * s)
      (g := fun s : ℝ ↦ s * log s)
      (x := t)
      ((differentiableAt_const _).mul differentiableAt_id)
      (differentiableAt_id.mul (differentiableAt_log ht))
    have hlin : deriv (fun s : ℝ ↦ (log y + 1) * s) t = log y + 1 := by
      simp
    calc
      deriv f t =
          deriv (fun s : ℝ ↦ (log y + 1) * s) t - deriv (fun s : ℝ ↦ s * log s) t := by
        simpa [f] using hsub
      _ = (log y + 1) - (log t + 1) := by rw [hlin, Real.deriv_mul_log ht]
      _ = log y - log t := by ring
  have hcont : ContinuousOn f (Set.Ici y) := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · refine ContinuousOn.mul continuous_id.continuousOn ?_
      refine Real.continuousOn_log.mono ?_
      intro z hz
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le h0y hz)
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici y)) := by
    intro z hz
    rw [interior_Ici, Set.mem_Ioi] at hz
    dsimp [f]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub ?_ ?_
    · exact (differentiableAt_const _).mul differentiableAt_id
    · exact differentiableAt_id.mul (differentiableAt_log (ne_of_gt (lt_trans h0y hz)))
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici y) hcont hdiff
    (fun z hz ↦ by
      rw [interior_Ici, Set.mem_Ioi] at hz
      rw [hderiv z (ne_of_gt (lt_trans h0y hz)), sub_nonpos]
      exact Real.log_le_log h0y (le_of_lt hz))
  have hxIci : x ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact hy
  have hnIci : (n : ℝ) ∈ Set.Ici y := by
    rw [Set.mem_Ici]
    exact le_trans hy hn
  specialize hanti hxIci hnIci hn
  have hleft' : (y / (n * exp (-1))) ^ n = Real.exp (f n) := by
    calc
      (y / (n * exp (-1))) ^ n = (Real.exp (Real.log (y / (n * exp (-1))))) ^ n := by
        rw [Real.exp_log hleft]
      _ = Real.exp ((n : ℝ) * Real.log (y / (n * exp (-1)))) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (f n) := by
        congr 1
        change (n : ℝ) * Real.log (y / (n * exp (-1))) = f n
        rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hnexp),
          Real.log_mul (ne_of_gt hn0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
        dsimp [f]
        ring
  have hright' : (y / (x * exp (-1))) ^ x = Real.exp (f x) := by
    rw [Real.rpow_def_of_pos hright]
    congr 1
    change Real.log (y / (x * exp (-1))) * x = f x
    rw [Real.log_div (ne_of_gt h0y) (ne_of_gt hxexp),
      Real.log_mul (ne_of_gt hx0) (ne_of_gt (exp_pos (-1))), Real.log_exp]
    dsimp [f]
    ring
  rw [hleft', hright']
  exact (Real.exp_le_exp).2 hanti

theorem sub_le_omega_div {a b : ℕ} (h : b ∣ a) : (ω a : ℝ) - ω b ≤ ω (a / b) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by simpa using h
    simp
  have hnat : ω a ≤ ω b + ω (a / b) := by
    simp only [ArithmeticFunction.cardDistinctFactors_apply]
    obtain ⟨k, rfl⟩ := h
    have hk0 : k ≠ 0 := by
      intro hk0
      simp [hk0] at ha
    have hk : 0 < k := Nat.pos_of_ne_zero hk0
    rw [Nat.mul_div_cancel_left _ hb, add_comm, ← List.length_append]
    apply List.Subperm.length_le
    refine (List.nodup_dedup _).subperm ?_
    intro x hx
    rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk.ne'] at hx
    simpa [or_comm] using hx
  rw [sub_le_iff_le_add, add_comm]
  exact_mod_cast hnat

theorem omega_div_le {a b : ℕ} (h : b ∣ a) : ω (a / b) ≤ ω a := by
  obtain ⟨k, rfl⟩ := h
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  simp only [ArithmeticFunction.cardDistinctFactors_apply, Nat.mul_div_cancel_left _ hb]
  refine (List.nodup_dedup _).subperm ?_ |>.length_le
  intro t ht
  rw [List.mem_dedup, Nat.mem_primeFactorsList_mul hb.ne' hk]
  exact Or.inr (List.mem_dedup.mp ht)

theorem div_bound_useful_version {ε : ℝ} (hε1 : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ n : ℕ, n ≤ N ^ 2 → (ArithmeticFunction.sigma 0 n : ℝ) ≤
        N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε)) := by
  let c : ℝ := ε / 2
  have hc : 0 < c := half_pos hε1
  have hhelp0 : 1 ≤ 2 * Real.log 2 * (1 + ε) := by
    have hbase : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    calc
      1 ≤ 2 * Real.log 2 := hbase
      _ ≤ 2 * Real.log 2 * (1 + ε) := by
        have hpos : 0 ≤ 2 * Real.log 2 := le_of_lt (mul_pos zero_lt_two (Real.log_pos one_lt_two))
        nlinarith
  have hhelp : 0 < 2 * Real.log 2 * (1 + ε) := lt_of_lt_of_le zero_lt_one hhelp0
  have hhelp2 : 0 < (1 + ε) / (1 + c) := by
    refine div_pos (add_pos zero_lt_one hε1) (add_pos zero_lt_one hc)
  have hboundc : 0 < (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) := by
    refine div_pos ?_ hhelp2
    rw [sub_pos, one_lt_div]
    · simpa [c] using half_lt_self hε1
    · exact add_pos zero_lt_one hc
  have haux := (isLittleO_log_id_atTop).bound hboundc
  have hdiv := divisor_bound hc
  rw [Filter.eventually_atTop] at hdiv
  rcases hdiv with ⟨M, hdiv⟩
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (M : ℝ))
    , ((tendsto_pow_rec_log_log_at_top hhelp).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (Real.exp 1))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ)) ] with
    N h1N hN hN' hlarge h0logN h0loglogN h0logloglogN
  intro n hn
  let X : ℝ := N ^ (2 * Real.log 2 / log (log (N : ℝ)) * (1 + ε))
  have hXhelp : X = N ^ (2 * Real.log 2 * (1 + ε) / log (log (N : ℝ))) := by
    dsimp [X]
    rw [div_eq_mul_inv]
    ring_nf
  have hMX : (M : ℝ) ≤ X := by
    rw [hXhelp]
    exact hN
  have heX : Real.exp 1 ≤ X := by
    rw [hXhelp]
    exact hN'
  have h1X : 1 < X := by
    exact lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) heX
  have hlogX : 0 < log X := Real.log_pos h1X
  by_cases hnbig : (n : ℝ) ≤ X
  · exact (trivial_divisor_bound.trans hnbig)
  rw [not_le] at hnbig
  have hloglogn' : 0 < log (log n) := by
    refine Real.log_pos ?_
    rw [Real.lt_log_iff_exp_lt]
    · exact lt_of_le_of_lt heX hnbig
    · exact lt_trans (lt_trans zero_lt_one h1X) hnbig
  have hloglogn : 0 ≤ log (log n) := le_of_lt hloglogn'
  have hnM : (M : ℝ) ≤ n := le_trans hMX (le_of_lt hnbig)
  refine le_trans (hdiv n ?_) ?_
  · exact_mod_cast hnM
  transitivity ((N : ℝ) ^ 2) ^ (Real.log 2 / log (log ↑n) * (1 + c))
  · refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast hn
    · refine mul_nonneg ?_ ?_
      · exact div_nonneg (Real.log_nonneg one_le_two) hloglogn
      · exact add_nonneg zero_le_one (le_of_lt hc)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast Nat.zero_le N)]
    have hlarge' :
        log (log (log N)) ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * log (log N) := by
      have htmp : |log (log (log N))| ≤
          (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) * |log (log N)| := by
        simpa [Function.comp, Real.norm_eq_abs] using hlarge
      rw [show |log (log (log N))| = log (log (log N)) by exact abs_of_pos h0logloglogN] at htmp
      rw [show |log (log N)| = log (log N) by exact abs_of_pos h0loglogN] at htmp
      exact htmp
    have hcoef :
        (((1 + ε) / (1 + c) - 1) / ((1 + ε) / (1 + c))) = 1 - (1 + c) / (1 + ε) := by
      field_simp [hhelp2.ne']
    have hconst : 0 ≤ log (2 * Real.log 2 * (1 + ε)) := Real.log_nonneg hhelp0
    have hlogXeq :
        log (log X) =
          log (2 * Real.log 2 * (1 + ε)) + log (log N) - log (log (log N)) := by
      rw [hXhelp, Real.log_rpow (lt_of_lt_of_le zero_lt_one h1N)]
      have hcalc :
          2 * Real.log 2 * (1 + ε) / log (log N) * log N =
            (2 * Real.log 2 * (1 + ε) * log N) / log (log N) := by
        ring
      rw [hcalc, Real.log_div, Real.log_mul]
      · exact ne_of_gt hhelp
      · exact ne_of_gt h0logN
      · exact ne_of_gt (mul_pos hhelp h0logN)
      · exact ne_of_gt h0loglogN
    have hXmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log X) := by
      rw [hlogXeq]
      rw [hcoef] at hlarge'
      nlinarith [hconst, hlarge']
    have hXlog : log (log X) ≤ log (log n) := by
      refine Real.log_le_log hlogX ?_
      exact Real.log_le_log (lt_trans zero_lt_one h1X) (le_of_lt hnbig)
    have hmain : ((1 + c) / (1 + ε)) * log (log N) ≤ log (log n) :=
      le_trans hXmain hXlog
    have hfrac' : (1 + c) / log (log n) ≤ (1 + ε) / log (log N) := by
      have hεpos : 0 < 1 + ε := add_pos zero_lt_one hε1
      have hmain'' :
          ((1 + c) / (1 + ε)) * log (log N) * (1 + ε) ≤ log (log n) * (1 + ε) := by
        exact mul_le_mul_of_nonneg_right hmain (le_of_lt hεpos)
      have hmain' : (1 + c) * log (log N) ≤ (1 + ε) * log (log n) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hεpos.ne'] using hmain''
      exact (div_le_div_iff₀ hloglogn' h0loglogN).2 hmain'
    have hfrac :
        Real.log 2 / log (log ↑n) * (1 + c) ≤
          Real.log 2 / log (log ↑N) * (1 + ε) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hfrac' (le_of_lt (Real.log_pos one_lt_two))
    have hpowbound :
        (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑n) * (1 + c))) ≤
          (N : ℝ) ^ (2 * (Real.log 2 / log (log ↑N) * (1 + ε))) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast h1N
      · exact mul_le_mul_of_nonneg_left hfrac zero_le_two
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpowbound

theorem another_large_N (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      1 / c / 2 ≤ log (log (log N)) ∧
        2 ^ ((100 : ℝ) / 99) ≤ log N ∧
        4 * log (log (log N)) ≤ log (log N) ∧
        log 2 < log (log (log N)) ∧
        log N ^ (-((2 : ℝ) / 99) / 2) ≤
          C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) /
            log N ^ ((2 : ℝ) / ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) ∧
        (1 - 2 / 99) * log (log N) +
            (1 + 5 / log (⌊(log (log N)) / (2 * log (log (log N)))⌋₊) * log (log N)) ≤
          (99 / 100 : ℝ) * log (log N) := by
  let _ := hc
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 4 by norm_num))
  have haux2 := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3960000 by norm_num))
  have haux3 := (Real.isLittleO_log_id_atTop.bound <| by
    have hden : 0 < ((Real.exp 10000 + 1) * 2 : ℝ) := by
      positivity
    exact one_div_pos.2 hden)
  have hhelp : 0 < (1 : ℝ) / 10000 := by
    norm_num
  filter_upwards
    [ (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux3
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 : ℝ) ^ ((100 : ℝ) / 99)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (1 / c / 2))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (log 2))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (1000 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((tendsto_rpow_atTop hhelp).comp
          (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop ((C / 2)⁻¹)) ] with
    N hlarge hlarge2 hlarge3 h0logN h1logN hlogN hlogloglogN' hlogloglogN h0loglogN hloglogN
      h0logloglogN hlargepow
  dsimp at hlargepow
  have h0logN_real : 0 < log N := by
    simpa [Function.comp] using h0logN
  have h1logN_real : 1 ≤ log N := by
    simpa [Function.comp] using h1logN
  have h0loglogN_real : 0 < log (log N) := by
    simpa [Function.comp] using h0loglogN
  have hloglogN_real : (1000 : ℝ) ≤ log (log N) := by
    simpa [Function.comp] using hloglogN
  have h0logloglogN_real : 0 < log (log (log N)) := by
    simpa [Function.comp] using h0logloglogN
  let x : ℝ := (log (log N)) / (2 * log (log (log N)))
  let F : ℝ := ⌊x⌋₊
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (le_of_lt h0loglogN_real)
      (mul_nonneg zero_le_two (le_of_lt h0logloglogN_real))
  have hlarge_abs : |log (log (log N))| ≤ (1 / 4 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge
  have hlarge2_abs : |log (log (log N))| ≤ (1 / 3960000 : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge2
  have hlarge3_abs :
      |log (log (log N))| ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * |log (log N)| := by
    simpa [Function.comp, id, Real.norm_eq_abs] using hlarge3
  have hlarge' : log (log (log N)) ≤ (1 / 4 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge_abs
    exact hlarge_abs
  have hlarge2' : log (log (log N)) ≤ (1 / 3960000 : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge2_abs
    exact hlarge2_abs
  have hlarge3' : log (log (log N)) ≤ (1 / ((Real.exp 10000 + 1) * 2) : ℝ) * log (log N) := by
    rw [abs_of_pos h0logloglogN_real, abs_of_pos h0loglogN_real] at hlarge3_abs
    exact hlarge3_abs
  have hx_exp : Real.exp 10000 + 1 ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul : log (log (log N)) * ((Real.exp 10000 + 1) * 2) ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge3'
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hhelp2 : Real.exp 10000 ≤ F := by
    change Real.exp 10000 ≤ (⌊x⌋₊ : ℝ)
    rw [natCast_floor_eq_intCast_floor hx_nonneg]
    have hfloor : x - 1 < ((⌊x⌋ : ℤ) : ℝ) := by
      exact_mod_cast (Int.sub_one_lt_floor x)
    linarith
  have hF_pos : 0 < F := lt_of_lt_of_le (Real.exp_pos 10000) hhelp2
  have hx_big : (1980000 : ℝ) ≤ x := by
    dsimp [x]
    refine (_root_.le_div_iff₀ ?_).2 ?_
    · positivity
    have hmul0 : log (log (log N)) * 3960000 ≤ log (log N) := by
      refine (_root_.le_div_iff₀ (by positivity)).mp ?_
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlarge2'
    nlinarith
  have hF_big_nat : 1980000 ≤ ⌊x⌋₊ := by
    rw [Nat.le_floor_iff hx_nonneg]
    exact hx_big
  have hF_big : (1980000 : ℝ) ≤ F := by
    change (1980000 : ℝ) ≤ (⌊x⌋₊ : ℝ)
    exact_mod_cast hF_big_nat
  refine ⟨hlogloglogN', hlogN, ?_, hlogloglogN, ?_, ?_⟩
  · nlinarith
  · change log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ (2 / F)
    have htwo_div_F : 2 / F ≤ 2 / (1980000 : ℝ) := by
      have hone_div : 1 / F ≤ 1 / (1980000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (1980000 : ℝ) by positivity) hF_big
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (2 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hexp : -((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F ≤ -((1 : ℝ) / 10000) := by
      nlinarith
    have hpow_small : log N ^ (-((1 : ℝ) / 10000)) ≤ C / 2 := by
      rw [Real.rpow_neg (le_of_lt h0logN_real)]
      exact (inv_le_comm₀ (Real.rpow_pos_of_pos h0logN_real _) (div_pos hC zero_lt_two)).2 hlargepow
    have hpow_mid : log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) ≤ C / 2 := by
      exact (Real.rpow_le_rpow_of_exponent_le h1logN_real hexp).trans hpow_small
    have hmain : log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
        log N ^ (2 / F) ≤ C := by
      have hmul := mul_le_mul_of_nonneg_left hpow_mid (show 0 ≤ (2 : ℝ) by positivity)
      have hrewrite :
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
            log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
              log N ^ (2 / F) := by
        calc
          2 * log N ^ (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
              2 * (log N ^ (-((2 : ℝ) / 99) / 2) *
                (log N ^ ((1 : ℝ) / 100) * log N ^ (2 / F))) := by
                  rw [show (-((2 : ℝ) / 99) / 2 + (1 : ℝ) / 100 + 2 / F) =
                      (-((2 : ℝ) / 99) / 2) + ((1 : ℝ) / 100 + 2 / F) by ring,
                    Real.rpow_add h0logN_real, Real.rpow_add h0logN_real]
          _ = log N ^ (-((2 : ℝ) / 99) / 2) * (2 * log N ^ ((1 : ℝ) / 100)) *
                log N ^ (2 / F) := by ring
      rw [hrewrite] at hmul
      linarith
    refine (_root_.le_div_iff₀ (Real.rpow_pos_of_pos h0logN_real _)).2 ?_
    have hmain' : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) *
        (2 * log N ^ ((1 : ℝ) / 100)) ≤ C := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    have hafter : log N ^ (-((2 : ℝ) / 99) / 2) * log N ^ (2 / F) ≤
        C * (2 * log N ^ ((1 : ℝ) / 100))⁻¹ := by
      exact (le_mul_inv_iff₀ (mul_pos zero_lt_two (Real.rpow_pos_of_pos h0logN_real _))).2 hmain'
    simpa [one_div] using hafter
  · change (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N)
    have hone : 1 ≤ (1 / 1000 : ℝ) * log (log N) := by
      nlinarith
    have hlogF : (10000 : ℝ) ≤ log F := by
      simpa using Real.log_le_log (Real.exp_pos 10000) hhelp2
    have hdiv : 5 / log F ≤ (5 : ℝ) / 10000 := by
      have hone_div : 1 / log F ≤ 1 / (10000 : ℝ) := by
        simpa using one_div_le_one_div_of_le (show 0 < (10000 : ℝ) by positivity) hlogF
      have hmul := mul_le_mul_of_nonneg_left hone_div (show 0 ≤ (5 : ℝ) by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      (1 - 2 / 99) * log (log N) + (1 + 5 / log F * log (log N)) ≤
          ((97 : ℝ) / 99) * log (log N) + (1 / 1000) * log (log N) + (5 / 10000) * log (log N) := by
            rw [add_assoc]
            refine add_le_add ?_ ?_
            · norm_num
            · refine add_le_add hone ?_
              exact mul_le_mul_of_nonneg_right hdiv (le_of_lt h0loglogN)
      _ ≤ (99 / 100 : ℝ) * log (log N) := by
        have hcoef : ((97 : ℝ) / 99) + 1 / 1000 + 5 / 10000 ≤ 99 / 100 := by norm_num
        simpa [left_distrib, right_distrib, add_assoc, add_left_comm, add_comm, mul_add] using
          mul_le_mul_of_nonneg_right hcoef (le_of_lt h0loglogN_real)

theorem yet_another_large_N :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) * N ^ (-2 / log (log N) + 2 * log 2 / log (log N) * (1 + 1 / 3)) <
        log N ^ (-((1 : ℝ) / 101)) / 6 := by
  have haux := (Real.isLittleO_log_id_atTop.bound (show 0 < (1 : ℝ) / 3 by norm_num))
  filter_upwards
    [ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually haux
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (log (6 * 2) / (1 - 1 / 101)))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_ge_atTop (-log (2 + -(2 * log 2) * (1 + 1 / 3))))
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (0 : ℝ))
    , ((Real.tendsto_exp_div_pow_atTop 3).comp
          (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
        (eventually_gt_atTop (1 : ℝ)) ] with
    N h0N hlarge h0logN hloglogN hlogloglogN h0loglogN h0logloglogN hcube
  have hhelp : 0 < 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hlog2 : log 2 < (3 / 4 : ℝ) := by
      exact lt_trans Real.log_two_lt_d9 (by norm_num)
    nlinarith
  rw [_root_.lt_div_iff₀' (show (0 : ℝ) < 6 by norm_num), ← mul_assoc]
  apply (Real.log_lt_log_iff
    (mul_pos (mul_pos (by norm_num : 0 < (6 : ℝ)) zero_lt_two) (Real.rpow_pos_of_pos h0N _))
    (Real.rpow_pos_of_pos h0logN _)).1
  rw [Real.log_rpow h0logN,
    Real.log_mul (by norm_num : (6 : ℝ) * 2 ≠ 0) (Real.rpow_pos_of_pos h0N _).ne', neg_mul,
    lt_neg, neg_add, Real.log_rpow h0N, ← sub_eq_neg_add, lt_sub_iff_add_lt, ← neg_mul, neg_add,
    ← neg_div, neg_neg, ← neg_mul, ← neg_div]
  have hlog12 : log (6 * 2) < (1 - 1 / 101 : ℝ) * log (log N) := by
    have hcoef : 0 < (1 - 1 / 101 : ℝ) := by norm_num
    have := (_root_.div_lt_iff₀ hcoef).1 hloglogN
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hcinv : 1 / log (log N) ≤ 2 + -(2 * log 2) * (1 + 1 / 3) := by
    have hrecip : (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ ≤ log (log N) := by
      calc
        (2 + -(2 * log 2) * (1 + 1 / 3))⁻¹ = Real.exp (-log (2 + -(2 * log 2) * (1 + 1 / 3))) := by
          rw [Real.exp_neg, Real.exp_log hhelp]
        _ ≤ Real.exp (log (log (log N))) := Real.exp_le_exp.mpr hlogloglogN
        _ = log (log N) := by simpa [Function.comp] using (Real.exp_log h0loglogN)
    have hmul : 1 ≤ (2 + -(2 * log 2) * (1 + 1 / 3)) * log (log N) := by
      have := (inv_le_iff_one_le_mul₀ hhelp).1 hrecip
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have := (_root_.div_le_iff₀ h0loglogN).2 <|
      by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  have hcube' : log (log N) < log N / (log (log N)) ^ 2 := by
    have hcube'' : (log (log N)) ^ 3 < log N := by
      have hcube0 : 1 < log N / (log (log N)) ^ 3 := by
        calc
          1 < Real.exp (log (log N)) / (log (log N)) ^ 3 := by simpa [Function.comp] using hcube
          _ = log N / (log (log N)) ^ 3 := by
            simpa [Function.comp] using
              congrArg (fun t => t / (log (log N)) ^ 3) (Real.exp_log h0logN)
      have := (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 3 by positivity)).1 hcube0
      simpa [pow_succ, pow_two, mul_assoc] using this
    refine (_root_.lt_div_iff₀ (show 0 < (log (log N)) ^ 2 by positivity)).2 ?_
    simpa [pow_succ, pow_two, mul_assoc] using hcube''
  have hcoeff :
      2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3) =
        (2 + -(2 * log 2) * (1 + 1 / 3)) / log (log N) := by
    field_simp [h0loglogN.ne']
  have hrhs :
      log (log N) <
        (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := by
    rw [hcoeff, div_eq_mul_inv, mul_assoc]
    have hmul :
        log N / (log (log N)) ^ 2 ≤
          (2 + -(2 * log 2) * (1 + 1 / 3)) * (log N * (log (log N))⁻¹) := by
      have hrewrite :
          log N / (log (log N)) ^ 2 = (1 / log (log N)) * (log N * (log (log N))⁻¹) := by
        field_simp [h0loglogN.ne']
      rw [hrewrite]
      have htmp := mul_le_mul_of_nonneg_right hcinv (by positivity : 0 ≤ log N * (log (log N))⁻¹)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
    exact lt_of_lt_of_le hcube' <|
      by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) + log (6 * 2) <
        (1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) +
          (1 - 1 / 101 : ℝ) * log ((log ∘ Nat.cast) N) := by
      simpa [Function.comp] using add_lt_add_left hlog12 ((1 / 101 : ℝ) * log ((log ∘ Nat.cast) N))
    _ = log (log N) := by
      simp [Function.comp]
      ring
    _ < (2 / log (log N) + -(2 * log 2) / log (log N) * (1 + 1 / 3)) * log N := hrhs

theorem yet_another_large_N' :
    ∀ᶠ N : ℕ in atTop,
      1 / log N + (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N)) ≤
        log N ^ (-(1 / 101 : ℝ)) / 6 := by
  have haux :
      Asymptotics.IsLittleO atTop (fun x : ℝ ↦ log x) (fun x ↦ x ^ (1 / 10100 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10100)
  have hbound := haux.bound (show 0 < (1000 : ℝ) / 6012 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hbound
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (12 ^ ((101 : ℝ) / 100)))
    ] with N hsmall h0logN hlogN
  rw [← add_halves (log N ^ (-(1 / 101 : ℝ)) / 6)]
  refine add_le_add ?_ ?_
  · have hpow : (12 : ℝ) ≤ log N ^ (100 / 101 : ℝ) := by
      have h :=
        Real.rpow_le_rpow
          (show 0 ≤ (12 : ℝ) ^ ((101 : ℝ) / 100) by positivity)
          hlogN
          (by norm_num : 0 ≤ (100 : ℝ) / 101)
      calc
        (12 : ℝ) = ((12 : ℝ) ^ ((101 : ℝ) / 100)) ^ ((100 : ℝ) / 101) := by
          rw [← Real.rpow_mul (by positivity : 0 ≤ (12 : ℝ))]
          norm_num
        _ ≤ log N ^ (100 / 101 : ℝ) := h
    have hmain : 12 * (1 / log N) ≤ log N ^ (-(1 / 101 : ℝ)) := by
      calc
        12 * (1 / log N) ≤ log N ^ (100 / 101 : ℝ) * (1 / log N) := by
          gcongr
        _ = log N ^ (-(1 / 101 : ℝ)) := by
          have hInv : (1 / log N) = log N ^ (-1 : ℝ) := by
            calc
              1 / log N = (log N)⁻¹ := by ring
              _ = log N ^ (-1 : ℝ) := by
                have htmp : log N ^ (-(1 : ℝ)) = (log N ^ (1 : ℝ))⁻¹ :=
                  Real.rpow_neg h0logN.le (1 : ℝ)
                simpa [Real.rpow_one] using htmp.symm
          rw [hInv]
          have hrpow0 :
              log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) =
                log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) := by
            simpa [Function.comp] using
              (Real.rpow_add h0logN (100 / 101 : ℝ) (-1 : ℝ)).symm
          calc
            log N ^ (100 / 101 : ℝ) * log N ^ (-1 : ℝ) = log N ^ ((100 / 101 : ℝ) + (-1 : ℝ)) :=
              hrpow0
            _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
    have h12 : (0 : ℝ) < 12 := by norm_num
    nlinarith
  · have hsmall' :
        log (log N) ≤ (1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)) := by
      have hnonnegLogLog : 0 ≤ log (log N) := by
        apply Real.log_nonneg
        have h12 : (1 : ℝ) ≤ 12 ^ ((101 : ℝ) / 100) := by
          have hbase : (1 : ℝ) ≤ 12 := by norm_num
          simpa using
            (Real.rpow_le_rpow (by positivity : 0 ≤ (1 : ℝ)) hbase
              (by norm_num : 0 ≤ ((101 : ℝ) / 100)))
        exact h12.trans hlogN
      have hnonnegPow : 0 ≤ log N ^ (1 / 10100 : ℝ) := by
        positivity
      have habs :
          |log (log N)| ≤ (1000 / 6012 : ℝ) * |log N ^ (1 / 10100 : ℝ)| := by
        simpa using hsmall
      rw [abs_of_nonneg hnonnegLogLog, abs_of_nonneg hnonnegPow] at habs
      exact habs
    calc
      (1 / (2 * log N ^ ((1 : ℝ) / 100))) * ((501 / 500 : ℝ) * log (log N))
          = ((501 / 1000 : ℝ) * log (log N)) * (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              field_simp
              ring
      _ ≤ ((501 / 1000 : ℝ) * ((1000 / 6012 : ℝ) * (log N ^ (1 / 10100 : ℝ)))) *
            (log N ^ ((1 : ℝ) / 100))⁻¹ := by
              gcongr
      _ = (1 / 12 : ℝ) * (log N ^ (1 / 10100 : ℝ) * (log N ^ ((1 : ℝ) / 100))⁻¹) := by
            ring
      _ = (1 / 12 : ℝ) * log N ^ (-(1 / 101 : ℝ)) := by
            have hInv : (log N ^ ((1 : ℝ) / 100))⁻¹ = log N ^ (-(1 / 100 : ℝ)) := by
              have htmp : log N ^ (-(1 / 100 : ℝ)) = (log N ^ ((1 : ℝ) / 100))⁻¹ :=
                Real.rpow_neg h0logN.le ((1 : ℝ) / 100)
              exact htmp.symm
            rw [hInv]
            congr 1
            have hrpow0 :
                log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := by
              simpa [Function.comp] using
                (Real.rpow_add h0logN (1 / 10100 : ℝ) (-(1 / 100 : ℝ))).symm
            calc
              log N ^ (1 / 10100 : ℝ) * log N ^ (-(1 / 100 : ℝ)) =
                  log N ^ ((1 / 10100 : ℝ) + (-(1 / 100 : ℝ))) := hrpow0
              _ = log N ^ (-(1 / 101 : ℝ)) := by congr 2; norm_num
      _ = log N ^ (-(1 / 101 : ℝ)) / 12 := by ring
      _ = log N ^ (-(1 / 101 : ℝ)) / 6 / 2 := by ring

theorem and_another_large_N (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, 2 * log (log N) + 1 ≤ (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) := by
  let c : ℝ := (1 - ε) * log (1 + ε ^ 2)
  have hbase : 1 < 1 + ε ^ 2 := by
    rw [lt_add_iff_pos_right]
    exact sq_pos_of_pos h1
  have hεlt1 : ε < 1 := lt_trans h2 one_half_lt_one
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (sub_pos.mpr hεlt1) (Real.log_pos hbase)
  have haux := (isLittleO_log_rpow_atTop hc).bound (show 0 < (1 : ℝ) / 4 by norm_num)
  filter_upwards
    [ (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , (tendsto_coe_log_pow_at_top c hc).eventually (eventually_ge_atTop (2 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually haux ] with
    N hlogN hpow hsmall
  have h0logN : 0 < log N := by
    exact lt_trans zero_lt_one hlogN
  have h0loglogN : 0 < log (log N) := Real.log_pos hlogN
  have hsmall' : log (log N) ≤ (1 / 4 : ℝ) * (log N ^ c) := by
    have habs : |log (log N)| ≤ (1 / 4 : ℝ) * |log N ^ c| := by
      simpa [Function.comp, Real.norm_eq_abs] using hsmall
    rw [abs_of_pos h0loglogN, abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos h0logN _))] at habs
    exact habs
  have hconst : 1 ≤ (1 / 2 : ℝ) * (log N ^ c) := by
    have : (2 : ℝ) ≤ log N ^ c := hpow
    nlinarith
  have hmain : 2 * log (log N) + 1 ≤ log N ^ c := by
    have hlogpart : 2 * log (log N) ≤ (1 / 2 : ℝ) * (log N ^ c) := by
      nlinarith
    linarith
  have hrpow :
      (1 + ε ^ 2) ^ ((1 - ε) * log (log N)) = log N ^ c := by
    rw [Real.rpow_def_of_pos (show 0 < 1 + ε ^ 2 by positivity), Real.rpow_def_of_pos h0logN]
    dsimp [c]
    ring_nf
  simpa [hrpow] using hmain

theorem prime_pow_not_coprime_prime_pow {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    ¬ Nat.Coprime a b →
      ∃ p k l : ℕ, Nat.Prime p ∧ (k ≠ 0 ∧ l ≠ 0) ∧ p ^ k = a ∧ p ^ l = b := by
  intro hab
  rcases (isPrimePow_nat_iff a).1 ha with ⟨q, k, hq, hk, hqa⟩
  rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
  refine ⟨q, k, l, hq, ⟨hk.ne', hl.ne'⟩, hqa, ?_⟩
  rw [← hrb]
  by_contra hqr
  apply hab
  rw [← hqa, ← hrb]
  refine Nat.coprime_pow_primes k l hq hr ?_
  intro hEq
  apply hqr
  simp [hEq]

theorem omega_mul_ppower {a q : ℕ} (hq : IsPrimePow q) : ω (q * a) ≤ 1 + ω a := by
  have hωq_nat : ω q = 1 := by
    rcases (isPrimePow_nat_iff q).1 hq with ⟨p, k, hp, hk, rfl⟩
    simpa using ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp hk.ne'
  have hωq : (ω q : ℝ) = 1 := by exact_mod_cast hωq_nat
  have hdivω : (ω ((q * a) / q) : ℝ) = ω a := by
    rw [Nat.mul_div_cancel_left _ hq.pos]
  have hsub : (ω (q * a) : ℝ) - ω q ≤ ω ((q * a) / q) := sub_le_omega_div (dvd_mul_right q a)
  have hreal : (ω (q * a) : ℝ) ≤ 1 + ω a := by
    calc
    (ω (q * a) : ℝ) ≤ ω q + ω ((q * a) / q) := by linarith
    _ = 1 + ω a := by rw [hωq, hdivω]
  exact_mod_cast hreal

theorem prime_dvd_prime_pow_then {a p : ℕ} (ha : IsPrimePow a) (hp : Nat.Prime p) (hpa : p ∣ a) :
    ∃ k : ℕ, k ≠ 0 ∧ p ^ k = a := by
  rcases (isPrimePow_nat_iff a).1 ha with ⟨r, k, hr, hk, hkr⟩
  refine ⟨k, hk.ne', ?_⟩
  rw [← hkr] at hpa
  have hpr : p ∣ r := hp.dvd_of_dvd_pow hpa
  have hEq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
  rw [hEq]
  exact hkr

theorem prime_pow_not_coprime_prod_iff {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD : ∀ d ∈ D, IsPrimePow d) :
    ¬ Nat.Coprime a (D.prod id) ↔
      ∃ p ka kd d : ℕ,
        d ∈ D ∧ Nat.Prime p ∧ ka ≠ 0 ∧ kd ≠ 0 ∧ p ^ ka = a ∧ p ^ kd = d := by
  constructor
  · intro h
    rw [Nat.Prime.not_coprime_iff_dvd] at h
    rcases h with ⟨p, hp, hpa, hpD⟩
    have hp' : Prime p := Nat.prime_iff.mp hp
    have hpD' : p ∣ D.toList.prod := by
      simpa using hpD
    rcases (Prime.dvd_prod_iff hp').mp hpD' with ⟨d, hdL, hd2⟩
    have hdD : d ∈ D := by simpa using hdL
    rcases prime_dvd_prime_pow_then ha hp hpa with ⟨ka, hka, hpka⟩
    rcases prime_dvd_prime_pow_then (hD d hdD) hp hd2 with ⟨kd, hkd, hpkd⟩
    exact ⟨p, ka, kd, d, hdD, hp, hka, hkd, hpka, hpkd⟩
  · rintro ⟨p, ka, kd, d, hd, hp, hka, hkd, hpka, hpkd⟩
    rw [Nat.Prime.not_coprime_iff_dvd]
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← hpka]
      exact dvd_pow_self _ hka
    · refine dvd_trans ?_ (Finset.dvd_prod_of_mem id hd)
      rw [← hpkd]
      exact dvd_pow_self _ hkd

theorem prime_pow_prods_coprime {A B : Finset ℕ} (hA : ∀ a ∈ A, IsPrimePow a)
    (hB : ∀ b ∈ B, IsPrimePow b) :
    Nat.Coprime (A.prod id) (B.prod id) ↔ ∀ a ∈ A, ∀ b ∈ B, Nat.Coprime a b := by
  let _ := hA
  let _ := hB
  constructor
  · intro h a ha b hb
    by_contra h'
    rw [Nat.Prime.not_coprime_iff_dvd] at h'
    rcases h' with ⟨r, hr, hra, hrb⟩
    have : ¬ ∃ p, Nat.Prime p ∧ p ∣ A.prod id ∧ p ∣ B.prod id := by
      intro hn
      exact (Nat.Prime.not_coprime_iff_dvd.mpr hn) h
    exact this ⟨r, hr, dvd_trans hra (Finset.dvd_prod_of_mem id ha),
      dvd_trans hrb (Finset.dvd_prod_of_mem id hb)⟩
  · intro h
    rw [Nat.coprime_prod_left_iff]
    intro a ha
    rw [Nat.coprime_prod_right_iff]
    intro b hb
    exact h a ha b hb

theorem weighted_ph {s : Finset ℕ} {f w : ℕ → ℚ} {b : ℚ} (h0b : 0 < b)
    (hw : ∀ a : ℕ, a ∈ s → 0 ≤ w a)
    (hb : b ≤ s.sum (fun x : ℕ ↦ w x * f x)) :
    ∃ (y : ℕ) (_ : y ∈ s), b ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    rw [hs, Finset.sum_empty] at hb
    exact (not_le_of_gt h0b) hb
  by_contra h
  push Not at h
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s f hsne
  have hylt : s.sum (fun x : ℕ ↦ w x) * f y < b := h y hys
  have hsumle : s.sum (fun x : ℕ ↦ w x * f x) ≤ s.sum (fun x : ℕ ↦ w x) * f y := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro n hn
    exact mul_le_mul_of_nonneg_left (hy n hn) (hw n hn)
  exact (not_lt_of_ge hb) (lt_of_le_of_lt hsumle hylt)

theorem prime_pow_not_coprime_iff {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    ¬ Nat.Coprime a b ↔
      ∃ p ka kb : ℕ, Nat.Prime p ∧ ka ≠ 0 ∧ kb ≠ 0 ∧ p ^ ka = a ∧ p ^ kb = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff a).1 ha with ⟨p, k, hp, hk, hpa⟩
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    by_cases hpr : p = r
    · refine ⟨p, k, l, hp, hk.ne', hl.ne', hpa, ?_⟩
      simpa [hpr] using hrb
    · exfalso
      apply hab
      rw [← hpa, ← hrb]
      exact Nat.coprime_pow_primes k l hp hr hpr
  · rintro ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    rw [Nat.Prime.not_coprime_iff_dvd]
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← hpa]
      exact dvd_pow_self _ hka
    · rw [← hpb]
      exact dvd_pow_self _ hkb

theorem eq_iff_ppowers_dvd (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔
      (∀ q, q ∣ a → IsPrimePow q → Nat.Coprime q (a / q) → q ∣ b) ∧
        ∀ q, q ∣ b → IsPrimePow q → Nat.Coprime q (b / q) → q ∣ a := by
  constructor
  · intro h
    subst h
    exact ⟨fun _ hq _ _ => hq, fun _ hq _ _ => hq⟩
  · rintro ⟨hab, hba⟩
    apply Nat.dvd_antisymm
    · exact (dvd_iff_ppowers_dvd' a b ha).2 fun q hq hq' => hab q hq hq'.1 hq'.2
    · exact (dvd_iff_ppowers_dvd' b a hb).2 fun q hq hq' => hba q hq hq'.1 hq'.2

theorem is_prime_pow_dvd_prod {n : ℕ} {D : Finset ℕ}
    (hD : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ D.prod id ↔ ∃ d, d ∈ D ∧ n ∣ d := by
  induction D using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Nat.dvd_one]
      constructor
      · intro h
        exact (hn.ne_one h).elim
      · rintro ⟨d, hd, _⟩
        simp at hd
  | @insert q D hqD hDind =>
      constructor
      · intro h
        rw [Finset.prod_insert hqD] at h
        have hnec : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Nat.Coprime a b := by
          intro a ha b hb hab
          exact hD a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
        specialize hDind hnec
        have hcop : Nat.Coprime q (D.prod id) := by
          rw [Nat.coprime_prod_right_iff]
          intro d hd
          exact hD q (Finset.mem_insert_self q D) d (Finset.mem_insert_of_mem hd) <| by
            intro hEq
            exact hqD (hEq ▸ hd)
        rcases (hcop.isPrimePow_dvd_mul hn).mp h with hq | hD'
        · exact ⟨q, Finset.mem_insert_self q D, hq⟩
        · rw [hDind] at hD'
          rcases hD' with ⟨d, hd1, hd2⟩
          exact ⟨d, Finset.mem_insert_of_mem hd1, hd2⟩
      · rintro ⟨d, hd1, hd2⟩
        exact dvd_trans hd2 (Finset.dvd_prod_of_mem id hd1)

theorem prime_pow_dvd_prime_pow {a b : ℕ} (ha : IsPrimePow a) (hb : IsPrimePow b) :
    a ∣ b ↔ ∃ p k l : ℕ, Nat.Prime p ∧ 0 < k ∧ k ≤ l ∧ p ^ k = a ∧ p ^ l = b := by
  constructor
  · intro hab
    rcases (isPrimePow_nat_iff b).1 hb with ⟨r, l, hr, hl, hrb⟩
    rw [← hrb] at hab
    rw [Nat.dvd_prime_pow hr] at hab
    rcases hab with ⟨k, hkl, h⟩
    refine ⟨r, k, l, hr, ?_, hkl, h.symm, hrb⟩
    refine Nat.pos_iff_ne_zero.mpr ?_
    intro hk
    rw [hk, pow_zero] at h
    exact ha.ne_one h
  · rintro ⟨p, k, l, hp, _hk, hkl, hpa, hpb⟩
    rw [← hpa, ← hpb]
    exact pow_dvd_pow _ hkl

theorem prime_pow_dvd_prod_prime_pow {a : ℕ} {D : Finset ℕ} (ha : IsPrimePow a)
    (hD1 : ∀ a₁ ∈ D, ∀ b ∈ D, a₁ ≠ b → Nat.Coprime a₁ b) (hD2 : ∀ d ∈ D, IsPrimePow d) :
    a ∣ D.prod id → Nat.Coprime a (D.prod id / a) → a ∈ D := by
  intro haD hacop
  by_cases hprod0 : D.prod id = 0
  · rw [hprod0, Nat.zero_div, Nat.coprime_zero_right] at hacop
    exact (ha.ne_one hacop).elim
  have haD' := haD
  rw [is_prime_pow_dvd_prod hD1 ha] at haD
  rcases haD with ⟨d, hd1, hd2⟩
  have hEq : a = d := by
    rw [prime_pow_dvd_prime_pow ha (hD2 d hd1)] at hd2
    rcases hd2 with ⟨p, k, l, hp, h0k, hkl, hpa, hpd⟩
    rw [← hpa, ← hpd]
    have hfac1 : k = (D.prod id).factorization p := by
      rw [← hpa] at haD'
      rw [← hpa] at hacop
      exact coprime_div_iff hp haD' (Nat.ne_zero_of_lt h0k) hacop
    have hfac2 : l ≤ (D.prod id).factorization p := by
      rw [← hp.pow_dvd_iff_le_factorization hprod0, hpd]
      exact Finset.dvd_prod_of_mem id hd1
    have hfac3 : k = l := le_antisymm hkl <| by
      rw [hfac1]
      exact hfac2
    rw [hfac3]
  rw [hEq]
  exact hd1

theorem prod_of_subset_le_prod_of_ge_one' {s : Finset ℕ} {f : ℕ → ℝ} :
    ∀ t : Finset ℕ,
      t ⊆ s →
        (∀ i ∈ s, 0 ≤ f i) →
          (∀ i ∈ s, i ∉ t → 1 ≤ f i) →
            t.prod f ≤ s.prod f := by
  induction s using Finset.induction_on with
  | empty =>
      intro t ht hs hf
      rw [Finset.subset_empty.mp ht]
  | @insert n s hns hsind =>
      intro t ht hs hf
      rw [Finset.prod_insert hns]
      by_cases htn : n ∈ t
      · let t' := t.erase n
        have htt' : insert n t' = t := Finset.insert_erase htn
        rw [← htt', Finset.prod_insert (Finset.notMem_erase _ _)]
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · refine hsind t' ?_ ?_ ?_
          · exact (Finset.erase_subset_erase _ ht).trans (Finset.erase_insert_subset _ _)
          · intro a ha
            exact hs a (Finset.mem_insert_of_mem ha)
          · intro a ha1 ha2
            refine hf a (Finset.mem_insert_of_mem ha1) ?_
            intro hat
            apply ha2
            rw [Finset.mem_erase]
            refine ⟨?_, hat⟩
            intro han
            apply hns
            simpa [han] using ha1
        · exact hs n (ht htn)
      · have ht' : t ⊆ s := by
          intro a ha
          rcases Finset.mem_insert.mp (ht ha) with rfl | ha'
          · exact False.elim (htn ha)
          · exact ha'
        refine le_trans (hsind t ht' ?_ ?_) ?_
        · intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
        · intro i hi1 hi2
          exact hf i (Finset.mem_insert_of_mem hi1) hi2
        refine le_mul_of_one_le_left ?_ ?_
        · refine Finset.prod_nonneg ?_
          intro i hi
          exact hs i (Finset.mem_insert_of_mem hi)
        · exact hf n (Finset.mem_insert_self n s) htn

theorem prod_of_subset_le_prod_of_ge_one {s t : Finset ℕ} {f : ℕ → ℝ} (h : t ⊆ s)
    (hs : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, i ∉ t → 1 ≤ f i) :
    t.prod f ≤ s.prod f := by
  exact prod_of_subset_le_prod_of_ge_one' t h hs hf

theorem sum_le_sum_of_inj' {A : Finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ) :
    ∀ B : Finset ℕ,
      (∀ b ∈ B, 0 ≤ f2 b) →
        (∀ a ∈ A, g a ∈ B) →
          (∀ a1 ∈ A, ∀ a2 ∈ A, g a1 = g a2 → a1 = a2) →
            (∀ a ∈ A, f2 (g a) = f1 a) → A.sum f1 ≤ B.sum f2 := by
  induction A using Finset.induction_on with
  | empty =>
      intro B hf2 hgB hginj hgf
      simp only [Finset.sum_empty]
      exact Finset.sum_nonneg hf2
  | @insert n A hnA hA =>
      intro B hf2 hgB hginj hgf
      rw [Finset.sum_insert hnA]
      let B' := B.erase (g n)
      have hBB' : insert (g n) B' = B := Finset.insert_erase (hgB n (Finset.mem_insert_self n A))
      rw [← hBB', Finset.sum_insert (Finset.notMem_erase _ _)]
      refine add_le_add ?_ ?_
      · simp [hgf n (Finset.mem_insert_self n A)]
      · refine hA B' ?_ ?_ ?_ ?_
        · intro b hb
          exact hf2 b (Finset.mem_of_mem_erase hb)
        · intro a ha
          rw [Finset.mem_erase]
          refine ⟨?_, hgB a (Finset.mem_insert_of_mem ha)⟩
          intro hEq
          have han : a = n :=
            hginj a (Finset.mem_insert_of_mem ha) n (Finset.mem_insert_self n A) hEq
          rw [han] at ha
          exact hnA ha
        · intro a1 ha1 a2 ha2 hgai
          exact hginj a1 (Finset.mem_insert_of_mem ha1) a2 (Finset.mem_insert_of_mem ha2) hgai
        · intro a ha
          exact hgf a (Finset.mem_insert_of_mem ha)

theorem sum_le_sum_of_inj {A B : Finset ℕ} {f1 f2 : ℕ → ℝ} (g : ℕ → ℕ)
    (hf2 : ∀ b ∈ B, 0 ≤ f2 b) (hgB : ∀ a ∈ A, g a ∈ B)
    (hginj : ∀ a1 ∈ A, ∀ a2 ∈ A, g a1 = g a2 → a1 = a2) (hgf : ∀ a ∈ A, f2 (g a) = f1 a) :
    A.sum f1 ≤ B.sum f2 := by
  exact sum_le_sum_of_inj' g B hf2 hgB hginj hgf

theorem card_bUnion_lt_card_mul_real {s : Finset ℤ} {f : ℤ → Finset ℕ} (m : ℝ)
    (h : ∀ a : ℤ, a ∈ s → ((f a).card : ℝ) < m) :
    s.Nonempty → ((s.biUnion f).card : ℝ) < s.card * m := by
  intro hs
  have hcard : (s.biUnion f).card ≤ Finset.sum s fun a => (f a).card := Finset.card_biUnion_le
  calc
    ((s.biUnion f).card : ℝ) ≤ Finset.sum s (fun a => ((f a).card : ℝ)) := by exact_mod_cast hcard
    _ < Finset.sum s (fun _ => m) := Finset.sum_lt_sum_of_nonempty hs h
    _ = s.card * m := by simp [nsmul_eq_mul]

theorem prod_le_max_size {ι N : Type*} [CommMonoidWithZero N] [Preorder N] [ZeroLEOneClass N]
    [PosMulMono N] {s : Finset ι} {f : ι → N} (hs : ∀ i ∈ s, 0 ≤ f i) (M : N)
    (hf : ∀ i ∈ s, f i ≤ M) : s.prod f ≤ M ^ s.card := by
  calc
    s.prod f ≤ s.prod fun _ => M := Finset.prod_le_prod hs hf
    _ = M ^ s.card := by simp

theorem sum_add_sum_add_sum {A B C : Finset ℕ} {f : ℕ → ℝ} :
    A.sum f + B.sum f + C.sum f =
      (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
  have hAB :
      A.sum f + B.sum f = (A ∪ B).sum f + (A ∩ B).sum f := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := f)).symm
  have hABC :
      (A ∪ B).sum f + C.sum f = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f := by
    simpa [add_comm, add_left_comm, add_assoc, Finset.union_assoc] using
      (Finset.sum_union_inter (s₁ := A ∪ B) (s₂ := C) (f := f)).symm
  have hInter :
      ((A ∪ B) ∩ C).sum f = (A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f := by
    have h' := Finset.sum_union_inter (s₁ := A ∩ C) (s₂ := B ∩ C) (f := f)
    have hUnion : A ∩ C ∪ B ∩ C = (A ∪ B) ∩ C := by
      ext x
      simp [or_and_right]
    rw [hUnion] at h'
    have hEq : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
      ext x
      simp [and_left_comm]
    rw [hEq] at h'
    linarith
  calc
    A.sum f + B.sum f + C.sum f = ((A ∪ B).sum f + (A ∩ B).sum f) + C.sum f := by rw [hAB]
    _ = (A ∪ B).sum f + C.sum f + (A ∩ B).sum f := by ring
    _ = (A ∪ B ∪ C).sum f + ((A ∪ B) ∩ C).sum f + (A ∩ B).sum f := by rw [hABC]
    _ =
        (A ∪ B ∪ C).sum f +
          ((A ∩ C).sum f + (B ∩ C).sum f - (A ∩ B ∩ C).sum f) +
            (A ∩ B).sum f := by rw [hInter]
    _ = (A ∪ B ∪ C).sum f + (A ∩ B).sum f + (A ∩ C).sum f + (B ∩ C).sum f -
          (A ∩ B ∩ C).sum f := by ring

theorem rec_sum_le_three {A B C : Finset ℕ} :
    rec_sum (A ∪ B ∪ C) ≤ rec_sum A + rec_sum B + rec_sum C := by
  let B' := B \ A
  let C' := C \ (A ∪ B')
  have hunion : A ∪ B ∪ C ⊆ A ∪ B' ∪ C' := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_union.mp hn with hn | hn
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hn
      · by_cases hna : n ∈ A
        · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl hna
        · exact
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hn, hna⟩
    · by_cases hAB : n ∈ A ∪ B'
      · exact Finset.mem_union.mpr <| Or.inl hAB
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_sdiff.mpr ⟨hn, hAB⟩
  refine le_trans (rec_sum_mono hunion) ?_
  rw [rec_sum_disjoint, rec_sum_disjoint]
  · refine add_le_add ?_ ?_
    · rw [add_le_add_iff_left]
      change rec_sum (B \ A) ≤ rec_sum B
      exact rec_sum_mono Finset.sdiff_subset
    · change rec_sum (C \ (A ∪ B')) ≤ rec_sum C
      exact rec_sum_mono Finset.sdiff_subset
  · exact Finset.disjoint_sdiff
  · exact Finset.disjoint_sdiff

theorem nat_gcd_prod_le_diff {a b c : ℤ} (hab : a ≠ b) (hac : a ≠ c) :
    Nat.gcd (Int.natAbs a) (Int.natAbs (b * c)) ≤ Int.natAbs (a - b) * Int.natAbs (a - c) := by
  refine Nat.le_of_dvd ?_ ?_
  · rw [Nat.pos_iff_ne_zero]
    intro hz
    rw [mul_eq_zero, Int.natAbs_eq_zero, Int.natAbs_eq_zero, sub_eq_zero, sub_eq_zero] at hz
    rcases hz with hz | hz
    · exact hab hz
    · exact hac hz
  · rw [Int.natAbs_mul]
    refine dvd_trans (gcd_mul_dvd_mul_gcd _ _ _) ?_
    refine mul_dvd_mul ?_ ?_
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
    · rw [← Int.natCast_dvd]
      refine dvd_sub ?_ ?_
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
      · rw [← Int.dvd_natAbs]
        exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)

theorem triv_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    1 - 2 * ε ≤ (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) := by
  let _ := hε2
  have hpos : 0 < 1 + ε ^ 2 := by positivity
  have hpos' : 1 + ε ^ 2 ≠ 0 := ne_of_gt hpos
  rw [div_eq_mul_inv, ← mul_assoc]
  field_simp [hpos']
  nlinarith [sq_nonneg ε, le_of_lt hε1]

theorem help_ε_estimate (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    log (1 - ε) * (1 - ε) ≤ -ε / 2 := by
  have h1ε : 0 < 1 - ε := by linarith
  calc
    log (1 - ε) * (1 - ε) ≤ ((1 - ε) - 1) * (1 - ε) := by
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt h1ε)
      simpa using Real.log_le_sub_one_of_pos h1ε
    _ = -ε * (1 - ε) := by ring
    _ ≤ -ε / 2 := by nlinarith

theorem floor_sub_ceil {x y z : ℝ} : (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ x + y := by
  calc
    (⌊z + x⌋ : ℝ) - ⌈z - y⌉ ≤ z + x - ⌈z - y⌉ := by
      gcongr
      exact Int.floor_le (z + x)
    _ ≤ z + x - (z - y) := by
      gcongr
      exact Int.le_ceil (z - y)
    _ = x + y := by ring

theorem useful_identity (i : ℕ) (h : (1 : ℝ) < i) :
    (1 : ℝ) + 1 / (i - 1) = |(1 - (i : ℝ)⁻¹)⁻¹| := by
  have hi0 : (0 : ℝ) < i := lt_trans zero_lt_one h
  have hineq : 0 ≤ (1 - (i : ℝ)⁻¹)⁻¹ := by
    apply inv_nonneg.mpr
    have hrewrite : 1 - (i : ℝ)⁻¹ = ((i : ℝ) - 1) / i := by
      field_simp [show (i : ℝ) ≠ 0 by linarith]
    rw [hrewrite]
    exact div_nonneg (by linarith) (le_of_lt hi0)
  rw [abs_of_nonneg hineq]
  field_simp [show (i : ℝ) ≠ 0 by linarith, show (i : ℝ) - 1 ≠ 0 by linarith]
  ring

theorem useful_exp_estimate : ((35 : ℝ) / 100) ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) := by
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hexp]
  nlinarith [Real.exp_one_lt_d9]

theorem rec_qsum_lower_bound (ε : ℝ) (hε1 : 0 < ε) (hε2 : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ,
        log N ^ (-ε / 2) ≤ rec_sum A →
          (∀ n ∈ A, (1 - ε) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
            (1 - 2 * ε) * Real.exp (-1) * log (log N) ≤
              (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ)) := by
  filter_upwards
    [ eventually_ge_atTop (0 : ℕ)
    , and_another_large_N ε hε1 hε2
    , (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)) ] with
    N _ hlarge0 hlarge1 hlarge2 A hrecA hreg
  let L : ℝ := log (log N)
  let x : ℝ := (1 - ε) * L
  have hεlt1 : ε < 1 := lt_trans hε2 one_half_lt_one
  have h1ε : 0 < 1 - ε := sub_pos.mpr hεlt1
  have hL : 0 < L := by
    simpa [L] using hlarge1
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos h1ε hL
  have hreg' : ∀ n ∈ A, x ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * L) := by
    intro n hn
    simpa [x, L] using hreg n hn
  have h0A : 0 ∉ A := by
    intro h0
    have h0reg := hreg' 0 h0
    rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
    exact (not_le_of_gt hx) (by simpa using h0reg.1)
  let S : ℝ := (ppowers_in_set A).sum (fun q ↦ (1 / q : ℝ))
  have hS : 0 < S := by
    have hAne : A.Nonempty := by
      by_contra hAne
      rw [Finset.not_nonempty_iff_eq_empty] at hAne
      rw [hAne, rec_sum_empty] at hrecA
      have hlogN : 0 < log N := lt_of_lt_of_le zero_lt_one hlarge2
      have hpow : 0 < log N ^ (-ε / 2) := Real.rpow_pos_of_pos hlogN (-ε / 2)
      linarith
    rcases hAne with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      have h0reg := hreg' 0 (ha0 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_zero] at h0reg
      exact (not_le_of_gt hx) (by simpa using h0reg.1)
    have ha1 : a ≠ 1 := by
      intro ha1
      have h1reg := hreg' 1 (ha1 ▸ ha)
      rw [ArithmeticFunction.cardDistinctFactors_one] at h1reg
      exact (not_le_of_gt hx) (by simpa using h1reg.1)
    have ha2 : 2 ≤ a := by omega
    have hpp : (ppowers_in_set A).Nonempty := ppowers_in_set_nonempty ⟨a, ha, ha2⟩
    dsimp [S]
    refine Finset.sum_pos ?_ hpp
    intro q hq
    have hq0 : q ≠ 0 := by
      intro hq0
      rw [hq0] at hq
      exact zero_not_mem_ppowers_in_set hq
    rw [one_div_pos]
    exact_mod_cast Nat.pos_of_ne_zero hq0
  let D : ℝ := Real.exp (-1) * x
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.exp_pos (-1)) hx
  by_cases hdone : x < S
  · have hcoef : (1 - 2 * ε) * Real.exp (-1) ≤ 1 - ε := by
      have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
        exact (le_of_lt Real.exp_neg_one_lt_d9).trans (by norm_num)
      nlinarith
    have hmain := mul_le_mul_of_nonneg_right hcoef (le_of_lt hL)
    simpa [S, x, L, mul_assoc, mul_left_comm, mul_comm] using hmain.trans (le_of_lt hdone)
  · have hSle : S ≤ x := not_lt.mp hdone
    let I : Finset ℕ := (Finset.range (⌊2 * L⌋₊ + 1)).filter (fun n : ℕ ↦ x ≤ n)
    have hrec_upper :
        rec_sum A ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := by
      refine rec_sum_le_prod_sum h0A ?_
      intro n hn
      have hnreg := hreg' n hn
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hnreg.1⟩
      rw [Nat.lt_succ_iff]
      exact Nat.le_floor hnreg.2
    have hsum_upper :
        I.sum (fun t ↦ S ^ t / Nat.factorial t) ≤
          I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := by
      refine Finset.sum_le_sum ?_
      intro t ht
      rw [div_pow]
      have hpow_pos : 0 < S ^ t := pow_pos hS t
      have hfac_pos : 0 < (t.factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos t
      have hden_pos : 0 < (((t : ℝ) * Real.exp (-1)) ^ t) := by
        cases t with
        | zero =>
            simp
        | succ t =>
            have hbase : 0 < (((Nat.succ t : ℕ) : ℝ) * Real.exp (-1)) := by positivity
            exact pow_pos hbase _
      exact (div_le_div_iff_of_pos_left hpow_pos hfac_pos hden_pos).2 (factorial_bound t)
    have hpointwise :
        ∀ t ∈ I, (S / (t * Real.exp (-1))) ^ t ≤ (S / D) ^ x := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      simpa [D, x, mul_assoc, mul_left_comm, mul_comm] using
        (helpful_decreasing_bound hS ht'.2 hSle)
    have hsum_card :
        I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) ≤ (I.card : ℝ) * (S / D) ^ x := by
      refine sum_le_card_mul_real ?_
      intro t ht
      exact hpointwise t ht
    have hIcard_nat : I.card ≤ (Finset.range (⌊2 * L⌋₊ + 1)).card := by
      simpa [I] using
        (Finset.card_filter_le (s := Finset.range (⌊2 * L⌋₊ + 1)) (p := fun n : ℕ ↦ x ≤ n))
    have hIcard :
        (I.card : ℝ) ≤ (1 + ε ^ 2) ^ x := by
      calc
        (I.card : ℝ) ≤ ((Finset.range (⌊2 * L⌋₊ + 1)).card : ℝ) := by
          exact_mod_cast hIcard_nat
        _ = (⌊2 * L⌋₊ : ℝ) + 1 := by simp
        _ ≤ 2 * L + 1 := by
          have hfloor : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by positivity)
          linarith
        _ ≤ (1 + ε ^ 2) ^ x := by
          simpa [x, L] using hlarge0
    have hrec_bound :
        log N ^ (-ε / 2) ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
      have hpow_nonneg : 0 ≤ (S / D) ^ x := by positivity
      calc
        log N ^ (-ε / 2) ≤ rec_sum A := hrecA
        _ ≤ I.sum (fun t ↦ S ^ t / Nat.factorial t) := hrec_upper
        _ ≤ I.sum (fun t ↦ (S / (t * Real.exp (-1))) ^ t) := hsum_upper
        _ ≤ (I.card : ℝ) * (S / D) ^ x := hsum_card
        _ ≤ (1 + ε ^ 2) ^ x * (S / D) ^ x := by
          exact mul_le_mul_of_nonneg_right hIcard hpow_nonneg
    have hleft :
        (1 - ε) ^ x ≤ log N ^ (-ε / 2) := by
      have hEq : (1 - ε) ^ x = log N ^ (log (1 - ε) * (1 - ε)) := by
        dsimp [x, L]
        nth_rewrite 1 [← Real.exp_log h1ε]
        rw [← Real.exp_mul, ← mul_assoc, mul_comm _ (log (log N)), Real.exp_mul,
          Real.exp_log]
        exact lt_of_lt_of_le zero_lt_one hlarge2
      rw [hEq]
      refine Real.rpow_le_rpow_of_exponent_le hlarge2 ?_
      exact help_ε_estimate ε hε1 hε2
    have hbase_nonneg : 0 ≤ (1 - ε) / (1 + ε ^ 2) := by
      exact div_nonneg (le_of_lt h1ε) (by positivity)
    have hright_nonneg : 0 ≤ S / D := by
      exact div_nonneg (le_of_lt hS) (le_of_lt hD)
    have hbase :
        (1 - ε) / (1 + ε ^ 2) ≤ S / D := by
      rw [← Real.rpow_le_rpow_iff hbase_nonneg hright_nonneg hx]
      have hfac_pos : 0 < (1 + ε ^ 2) ^ x := Real.rpow_pos_of_pos (by positivity) x
      calc
        ((1 - ε) / (1 + ε ^ 2)) ^ x = (1 - ε) ^ x / (1 + ε ^ 2) ^ x := by
          rw [Real.div_rpow (le_of_lt h1ε) (by positivity)]
        _ ≤ log N ^ (-ε / 2) / (1 + ε ^ 2) ^ x := by
          exact (div_le_div_iff_of_pos_right hfac_pos).2 hleft
        _ ≤ (S / D) ^ x := by
          rw [div_le_iff₀ hfac_pos]
          simpa [mul_assoc, mul_left_comm, mul_comm] using hrec_bound
    have hmid : ((1 - ε) / (1 + ε ^ 2)) * D ≤ S := by
      exact (le_div_iff₀ hD).mp hbase
    have htriv :
        (1 - 2 * ε) * Real.exp (-1) * L ≤
          (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L := by
      have hcoef := triv_ε_estimate ε hε1 hε2
      have hEL_nonneg : 0 ≤ Real.exp (-1) * L := by
        exact mul_nonneg (le_of_lt (Real.exp_pos (-1))) (le_of_lt hL)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hcoef hEL_nonneg
    have hmid' :
        (1 - ε) * ((1 - ε) / (1 + ε ^ 2)) * Real.exp (-1) * L ≤ S := by
      simpa [D, x, L, mul_assoc, mul_left_comm, mul_comm] using hmid
    simpa [S, L] using htriv.trans hmid'

theorem useful_rec_aux1 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ N k : ℕ,
          1 ≤ k →
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) ≤
              C ^ k := by
  have haux :
      ∃ C : ℝ,
        0 < C ∧
          ∀ N : ℕ,
            ((range (N + 1)).filter Nat.Prime).prod
                (fun p ↦ ((1 : ℝ) + 1 / (p * (p - 1)))) ≤ C := by
    have ht : ∀ n : ℕ,
        log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      intro n
      by_cases h0 : n = 0
      · subst h0
        simp [zero_pow]
      by_cases h1 : n = 1
      · subst h1
        simp
      have h2 : 2 ≤ n := by omega
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_trans zero_lt_one h2)
      have hn1_pos : 0 < (n : ℝ) - 1 := by
        have hn_gt : (1 : ℝ) < n := by
          exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
        linarith
      have hlog :
          log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 1))) ≤
            1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have hpos : 0 < 1 + 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 (mul_pos hn_pos hn1_pos))
        simpa using (Real.log_le_sub_one_of_pos hpos)
      have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast h2
        nlinarith
      have hhalf_pos : 0 < (n : ℝ) / 2 := by positivity
      have hdiv : 1 / ((n : ℝ) - 1) ≤ 2 / (n : ℝ) := by
        have h := one_div_le_one_div_of_le hhalf_pos hhalf
        have hEq : 1 / ((n : ℝ) / 2) = 2 / (n : ℝ) := by
          field_simp [hn_pos.ne']
        exact h.trans_eq hEq
      have h_inv :
          1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 * (1 / (n : ℝ) ^ (2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hdiv (one_div_nonneg.2 hn_pos.le)
        simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact hlog.trans h_inv
    have hsummable :
        Summable (fun n : ℕ => (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact (summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2)).mul_left 2
    refine ⟨Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))), Real.exp_pos _, ?_⟩
    intro N
    let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
    have hs_log :
        log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ≤
          ∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ)) := by
      rw [Real.log_prod]
      · refine le_trans (Finset.sum_le_sum fun i hi ↦ ht i) ?_
        exact hsummable.sum_le_tsum s (fun _ _ ↦ by positivity)
      · intro i hi
        have hip := (Finset.mem_filter.mp hi).2
        have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
          have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
          have hi1_pos : 0 < (i : ℝ) - 1 := by
            have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
            linarith
          exact mul_pos hi_pos hi1_pos
        have hpos : 0 < (1 : ℝ) + 1 / ((i : ℝ) * ((i : ℝ) - 1)) := by
          exact add_pos zero_lt_one (one_div_pos.2 hden)
        exact hpos.ne'
    have hs_pos : 0 < s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
      apply Finset.prod_pos
      intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
    have hexp :
        Real.exp (log (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))) ≤
          Real.exp (∑' n : ℕ, (2 : ℝ) * (1 / (n : ℝ) ^ (2 : ℝ))) := by
      exact Real.exp_le_exp.mpr hs_log
    rw [Real.exp_log hs_pos] at hexp
    simpa [s] using hexp
  rcases haux with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro N k hk
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  change s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_lt hip.one_lt)
        linarith
      have hden_nonneg : 0 ≤ (i : ℝ) * ((i : ℝ) - 1) := by
        exact mul_nonneg (by exact_mod_cast Nat.zero_le i) hi1_nonneg
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hden_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2
      have hden_pos : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)) := by
        exact one_div_nonneg.2 hden_pos.le
      have hstep :=
        one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2
      have hden : 0 < (i : ℝ) * ((i : ℝ) - 1) := by
        have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hip.pos
        have hi1_pos : 0 < (i : ℝ) - 1 := by
          have hi_gt : (1 : ℝ) < i := by exact_mod_cast hip.one_lt
          linarith
        exact mul_pos hi_pos hi1_pos
      exact add_pos zero_lt_one (one_div_pos.2 hden)
  have hN' : s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤ C := by
    simpa [s] using hN N
  have hpow : (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k ≤ C ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN' k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)))))
    _ ≤ C ^ k := hpow

theorem useful_rec_aux3 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N : ℕ,
            1 < y →
              y < N →
                ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                    (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) ≤
                  C * |log N| / |log y| := by
  rcases weak_mertens_third_upper_all with ⟨u, hu, hupp⟩
  rcases weak_mertens_third_lower_all with ⟨l, hl, hlow⟩
  refine ⟨u / l, div_pos hu hl, ?_⟩
  intro y N hy hyN
  let f : ℕ → ℝ := fun p ↦ (1 + 1 / (p - 1) : ℝ)
  let s : Finset ℕ := (range (N + 1)).filter Nat.Prime
  let t : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ (n : ℝ) ≤ y
  let u' : Finset ℕ := (range (N + 1)).filter fun n ↦ Nat.Prime n ∧ y < n
  let fy : Finset ℕ := (Icc 1 ⌊y⌋₊).filter Nat.Prime
  have hf_eq : ∀ p : ℕ, Nat.Prime p → f p = (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    calc
      f p = |(1 - (p : ℝ)⁻¹)⁻¹| := useful_identity p hp1
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := by
        refine abs_of_nonneg ?_
        exact (inv_pos.mpr (sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1))).le
  have hs_eq : s.prod f = partial_euler_product N := by
    rw [partial_euler_product]
    have hs' : s = (Icc 1 N).filter Nat.Prime := by
      ext n
      change n ∈ (range (N + 1)).filter Nat.Prime ↔ n ∈ (Icc 1 N).filter Nat.Prime
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hn, hp⟩
        exact ⟨⟨hp.one_lt.le, Nat.lt_succ_iff.mp hn⟩, hp⟩
      · rintro ⟨⟨_, hn⟩, hp⟩
        exact ⟨Nat.lt_succ_of_le hn, hp⟩
    rw [hs']
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have hfy_eq : fy.prod f = partial_euler_product ⌊y⌋₊ := by
    rw [partial_euler_product]
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hf_eq p (Finset.mem_filter.mp hp).2
  have ht_subset : t ⊆ s := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnr, hnp⟩
    exact Finset.mem_filter.mpr ⟨hnr, hnp.1⟩
  have hsdiff : s \ t = u' := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_sdiff.mp hn with ⟨hsn, hnt⟩
      rcases Finset.mem_filter.mp hsn with ⟨hnr, hnp⟩
      refine Finset.mem_filter.mpr ⟨hnr, hnp, ?_⟩
      by_contra hny
      exact hnt <| Finset.mem_filter.mpr ⟨hnr, ⟨hnp, le_of_not_gt hny⟩⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnr, hnp, hny⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hnr, hnp⟩, ?_⟩
      intro hnt
      exact not_lt_of_ge (Finset.mem_filter.mp hnt).2.2 hny
  have hfy_subset : fy ⊆ t := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxprime⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    have hxy : (x : ℝ) ≤ y := by
      rw [← Nat.le_floor_iff]
      · exact hx2
      · exact le_trans zero_le_one (le_of_lt hy)
    have hxN : x ≤ N := by
      exact_mod_cast le_trans hxy (le_of_lt hyN)
    refine Finset.mem_filter.mpr ?_
    exact ⟨by simpa [Finset.mem_range, Nat.lt_succ_iff] using hxN, ⟨hxprime, hxy⟩⟩
  have ht_nonneg : ∀ i ∈ t, 0 ≤ f i := by
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact add_nonneg zero_le_one (div_nonneg zero_le_one hsub)
  have ht_one : ∀ i ∈ t, i ∉ fy → 1 ≤ f i := by
    intro i hi hif
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 ≤ (i : ℝ) - 1 := sub_nonneg.mpr <| by exact_mod_cast hip.one_lt.le
    exact le_add_of_nonneg_right (div_nonneg zero_le_one hsub)
  have hlow_prod : partial_euler_product ⌊y⌋₊ ≤ t.prod f := by
    calc
      partial_euler_product ⌊y⌋₊ = fy.prod f := hfy_eq.symm
      _ ≤ t.prod f := prod_of_subset_le_prod_of_ge_one hfy_subset ht_nonneg ht_one
  have hNnat : 2 ≤ N := by
    have : 1 < N := by exact_mod_cast (lt_trans hy hyN)
    omega
  have hupp' : partial_euler_product N ≤ u * |log N| := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hupp (N : ℝ) (by exact_mod_cast hNnat)
  have hlow' : l * |log y| ≤ partial_euler_product ⌊y⌋₊ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound)]
      using hlow y (le_of_lt hy)
  have hden : l * |log y| ≤ t.prod f := hlow'.trans hlow_prod
  have hnum_nonneg : 0 ≤ s.prod f := by
    rw [hs_eq]
    exact le_trans zero_le_one partial_euler_trivial_lower_bound
  have ht_pos : 0 < t.prod f := by
    refine Finset.prod_pos ?_
    intro i hi
    have hip : Nat.Prime i := (Finset.mem_filter.mp hi).2.1
    have hsub : 0 < (i : ℝ) - 1 := sub_pos.mpr <| by exact_mod_cast hip.one_lt
    exact add_pos zero_lt_one (one_div_pos.mpr hsub)
  have hylog_pos : 0 < |log y| := by
    rw [abs_of_pos (Real.log_pos hy)]
    exact Real.log_pos hy
  have hmain :
      s.prod f / t.prod f ≤ (u * |log N|) / (l * |log y|) := by
    refine (div_le_div_of_nonneg_left hnum_nonneg (mul_pos hl hylog_pos) hden).trans ?_
    exact div_le_div_of_nonneg_right (hs_eq ▸ hupp') (mul_nonneg (le_of_lt hl) (abs_nonneg _))
  have hrewrite :
      (u * |log N|) / (l * |log y|) = (u / l) * |log N| / |log y| := by
    field_simp [hl.ne', abs_ne_zero.mpr (Real.log_pos hy).ne']
  calc
    ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))
        = u'.prod f := by simp [u', f]
    _ = s.prod f / t.prod f := by
          rw [← hsdiff]
          apply (eq_div_iff ht_pos.ne').2
          simpa using (Finset.prod_sdiff (f := f) ht_subset)
    _ ≤ (u * |log N|) / (l * |log y|) := hmain
    _ = (u / l) * |log N| / |log y| := hrewrite

theorem useful_rec_aux2 :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ N k : ℕ,
            1 ≤ k →
              1 < y →
                y < N →
                  ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
                      (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
                    (C * |log N| / |log y|) ^ k := by
  rcases useful_rec_aux3 with ⟨C, hC, hN⟩
  refine ⟨C, hC, ?_⟩
  intro y N k hk hy hyN
  specialize hN y N hy hyN
  let s : Finset ℕ := (range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)
  change s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤ (C * |log N| / |log y|) ^ k
  have hprod :
      s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      exact add_nonneg zero_le_one (div_nonneg (by exact_mod_cast Nat.zero_le k) hi1_nonneg)
    · intro i hi
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_nonneg : 0 ≤ (i : ℝ) - 1 := by
        exact sub_nonneg.mpr (by exact_mod_cast hip.one_lt.le)
      have hden_nonneg : 0 ≤ (1 : ℝ) / ((i : ℝ) - 1) := by
        exact one_div_nonneg.2 hi1_nonneg
      have hstep := one_add_mul_le_pow (by linarith) k (a := (1 : ℝ) / ((i : ℝ) - 1))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hs_nonneg : 0 ≤ s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1))) := by
    exact le_of_lt <| Finset.prod_pos fun i hi ↦ by
      have hip := (Finset.mem_filter.mp hi).2.1
      have hi1_pos : 0 < (i : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast hip.one_lt)
      exact add_pos zero_lt_one (one_div_pos.2 hi1_pos)
  have hpow :
      (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k ≤ (C * |log N| / |log y|) ^ k := by
    exact pow_le_pow_left₀ hs_nonneg hN k
  calc
    s.prod (fun p ↦ ((1 : ℝ) + k / (p - 1))) ≤
        s.prod (fun p ↦ (((1 : ℝ) + 1 / (p - 1)) ^ k)) := hprod
    _ = (s.prod (fun p ↦ ((1 : ℝ) + 1 / (p - 1)))) ^ k := by
      simpa using (Finset.prod_pow s k (fun p ↦ ((1 : ℝ) + 1 / (p - 1))))
    _ ≤ (C * |log N| / |log y|) ^ k := hpow

theorem Nat.coprime_symmetric : Symmetric Nat.Coprime := by
  exact Nat.Coprime.symmetric

theorem ArithmeticFunction.IsMultiplicative.prod {ι : Type*} (g : ι → ℕ) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Nat.Coprime (g i) (g j)) :
    s.prod (fun i ↦ f (g i)) = f (s.prod g) := by
  simpa using (hf.map_prod g s hs).symm

theorem my_sum_lemma {α β γ : Type*} [AddCommMonoid γ] [Preorder γ] [IsOrderedAddMonoid γ]
    {s : Finset α} {t : Finset β} (f : α → γ) (g : β → γ) (r : ∀ i ∈ s, β)
    (r_inj : ∀ a₁ a₂ ha₁ ha₂, r a₁ ha₁ = r a₂ ha₂ → a₁ = a₂)
    (hg : ∀ i ∈ t, 0 ≤ g i) (rt : ∀ a ha, r a ha ∈ t) (fr : ∀ a ha, g (r a ha) = f a) :
    s.sum f ≤ t.sum g := by
  classical
  have hEq :
      Finset.sum s.attach (fun i => f i) = Finset.sum s.attach (fun i => g (r i i.prop)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact (fr i i.prop).symm
  rw [← Finset.sum_attach, hEq, ← Finset.sum_image]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ q _ ↦ hg _ q
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    exact rt a a.prop
  · intro a₁ _ a₂ _ h
    exact Subtype.ext (r_inj _ _ _ _ h)

theorem hcongr_thing {α β : Type*} (f g : α → β) :
    ∀ (p q : α → Prop),
      p = q →
        HEq (fun x (_ : p x) ↦ f x) (fun x (_ : q x) ↦ g x) →
          ∀ x, p x → f x = g x := by
  intro p q hpq h x hx
  subst hpq
  exact congrFun₂ (eq_of_heq h) x hx

theorem card_distinct_factors_apply' {m : ℕ} : ω m = m.primeFactorsList.toFinset.card := by
  simpa [ArithmeticFunction.cardDistinctFactors_apply] using
    (List.card_toFinset (l := m.primeFactorsList)).symm

theorem card_distinct_factors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    ω (m * n) = ω m + ω n := by
  exact ArithmeticFunction.cardDistinctFactors_mul hmn

theorem prod_one_add' {D : Finset ℕ} (hD : 0 ∉ D) (f : ArithmeticFunction ℝ)
    (hf' : f.IsMultiplicative) (hf'' : ∀ i, 0 ≤ f i) :
    D.sum f ≤
      (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
        (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum f) := by
  classical
  rw [Finset.prod_one_add]
  simp only [Finset.prod_sum]
  rw [Finset.sum_sigma']
  refine my_sum_lemma
      (f := f)
      (g := fun x : Σ x : Finset ℕ, ∀ a ∈ x, ℕ =>
        ∏ x_1 ∈ x.1.attach, f (x.2 x_1 x_1.prop))
      (r := fun d hd ↦ ⟨d.primeFactors, fun p hp ↦ p ^ d.factorization p⟩)
      ?_ ?_ ?_ ?_
  · intro d₁ d₂ hd₁ hd₂ h
    dsimp at h
    simp only [Sigma.mk.inj_iff] at h
    have hpow :
        ∀ p ∈ d₁.primeFactors, p ^ d₁.factorization p = p ^ d₂.factorization p := by
      intro p hp
      have hmem : (fun x ↦ x ∈ d₁.primeFactors) = fun x ↦ x ∈ d₂.primeFactors := by
        ext x
        rw [h.1]
      exact hcongr_thing _ _ _ _ hmem h.2 p hp
    apply Nat.eq_of_factorization_eq
    · exact ne_of_mem_of_not_mem hd₁ hD
    · exact ne_of_mem_of_not_mem hd₂ hD
    intro p
    by_cases hp : p ∈ d₁.primeFactors
    · apply Nat.pow_right_injective (Nat.prime_of_mem_primeFactors hp).two_le
      exact hpow p hp
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rwa [hp, eq_comm, ← Finsupp.notMem_support_iff, Nat.support_factorization, ← h.1,
        ← Nat.support_factorization, Finsupp.notMem_support_iff]
  · intro i hi
    apply Finset.prod_nonneg
    intro j hj
    exact hf'' _
  · intro d hd
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_pi, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨d, hd, hx⟩
    intro a had
    have hd₀ : d ≠ 0 := ne_of_mem_of_not_mem hd hD
    have hfac : d.factorization a ≠ 0 := by
      rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
    have had' : a.Prime ∧ a ∣ d := (Nat.mem_primeFactors_of_ne_zero hd₀).1 had
    rw [mem_ppowers_in_set' had'.1 hfac]
    exact ⟨⟨_, hd, rfl⟩, dvd_pow_self _ hfac⟩
  · intro d hd
    dsimp
    rw [Finset.prod_attach d.primeFactors (fun y ↦ f (y ^ d.factorization y))]
    rw [ArithmeticFunction.IsMultiplicative.prod _ hf']
    · congr 1
      rw [← Nat.support_factorization]
      change d.factorization.prod (· ^ ·) = d
      rw [Nat.prod_factorization_pow_eq_self]
      exact ne_of_mem_of_not_mem hd hD
    · intro p₁ hp₁ p₂ hp₂ hneq
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp₁)
        (Nat.prime_of_mem_primeFactors hp₂) hneq

@[simp] theorem card_distinct_factors_apply_is_prime_pow {q : ℕ} (hq : IsPrimePow q) : ω q = 1 := by
  exact ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hq

theorem Nat.le_pow_self {x y : ℕ} (hy : y ≠ 0) : x ≤ x ^ y := by
  exact Nat.le_self_pow hy x

theorem dvd_prime_powers {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 1 m) := by
  rcases S.eq_empty_or_nonempty with rfl | hS'
  · refine ⟨1, by simp⟩
  refine ⟨S.max' hS' + 1, ?_⟩
  intro x hx
  obtain ⟨p', k, hp', hk, rfl⟩ := (isPrimePow_nat_iff x).1 (hS x (Finset.filter_subset _ _ hx))
  simp only [Finset.mem_filter] at hx
  have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hx.2)
  subst p'
  refine Finset.mem_map.2 ⟨k, ?_, rfl⟩
  simp only [Finset.mem_Ico]
  constructor
  · exact hk
  · exact lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
      ((Finset.le_max' _ _ hx.1).trans (Nat.le_succ _))

theorem dvd_prime_powers' {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (hS : ∀ x ∈ S, IsPrimePow x)
    (hSp : p ∉ S) :
    ∃ m,
      S.filter (fun q ↦ p ∣ q) ⊆
        Finset.map ⟨_, Nat.pow_right_injective hp.two_le⟩ (Ico 2 m) := by
  obtain ⟨m, hm⟩ := dvd_prime_powers hp S hS
  refine ⟨m, ?_⟩
  intro x hx
  rcases Finset.mem_map.1 (hm hx) with ⟨n, hn, rfl⟩
  have hn1 : n ≠ 1 := by
    intro hn1
    apply hSp
    simpa [hn1] using hx
  refine Finset.mem_map.2 ⟨n, ?_, rfl⟩
  simp only [Finset.mem_Ico] at hn ⊢
  omega

theorem useful_rec_aux4' (y : ℝ) (k N : ℕ) (D : Finset ℕ) (hD' : 0 ∉ D)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  have h₁ :
      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        (D.biUnion fun n ↦ n.primeFactorsList.toFinset).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q)) := by
    let f : ArithmeticFunction ℝ := ⟨fun d ↦ (k : ℝ) ^ ω d / d, by simp⟩
    have hf' : f.IsMultiplicative := by
      refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.2 ⟨by simp [f], ?_⟩
      intro m n hm hn hmn
      change (k : ℝ) ^ ω (m * n) / ((m * n : ℕ) : ℝ) =
        ((k : ℝ) ^ ω m / (m : ℝ)) * ((k : ℝ) ^ ω n / (n : ℝ))
      rw [card_distinct_factors_mul_of_coprime hmn, div_mul_div_comm, Nat.cast_mul, pow_add]
    have hf'' : ∀ i, 0 ≤ f i := by
      intro i
      exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    refine (prod_one_add' hD' f hf' hf'').trans_eq ?_
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [add_right_inj]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hωq : ω q = 1 := by
      rw [Finset.mem_filter] at hq
      rw [mem_ppowers_in_set] at hq
      exact card_distinct_factors_apply_is_prime_pow hq.1.1
    simp [f, hωq]
  have hsubset :
      D.biUnion (fun n ↦ n.primeFactorsList.toFinset) ⊆
        (Finset.range (N + 1)).filter Nat.Prime := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨d, hd, hxd⟩
    have hdx : x ∈ d.primeFactors := by
      simpa using hxd
    have hd'' : d.factorization x ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hdx
    have hxN : x ≤ N := by
      exact (Nat.le_pow_self hd'').trans <|
        (hD (x ^ d.factorization x) (mem_ppowers_in_set'' hd hd'')).2
    refine Finset.mem_filter.mpr ⟨?_, Nat.prime_of_mem_primeFactors hdx⟩
    show x ∈ Finset.range (N + 1)
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hxN
  have h₃ :
      ∀ i,
        (0 : ℝ) ≤ ((ppowers_in_set D).filter (fun q ↦ i ∣ q)).sum (fun q ↦ (k : ℝ) / q) := by
    intro i
    refine Finset.sum_nonneg ?_
    intro q hq
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  apply h₁.trans
  refine (prod_of_subset_le_prod_of_one_le hsubset ?_ ?_).trans ?_
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i _ _
    exact le_add_of_nonneg_right (h₃ i)
  rw [← Finset.prod_filter_mul_prod_filter_not ((range (N + 1)).filter Nat.Prime) (fun n ↦ y < n),
    mul_comm]
  have hleft₁ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, not_lt, and_imp, Finset.mem_range, Nat.lt_succ_iff,
        add_le_add_iff_left, div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers' hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
        (fun h ↦ not_lt_of_ge hpy (hD _ h).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [pow_two, hp0, hp1]
  have hleft₂ :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ ¬ y < (n : ℝ))).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1)))
        ≤
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) := by
    exact prod_of_subset_le_prod_of_one_le (Finset.filter_subset _ _)
      (fun i hi ↦ by
        rw [mul_comm]
        exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
      (fun i _ _ ↦ by
        rw [mul_comm]
        exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) my_mul_thing))
  have hright :
      (((range (N + 1)).filter Nat.Prime).filter (fun n : ℕ ↦ y < (n : ℝ))).prod
          (fun p ↦ 1 + ((ppowers_in_set D).filter (fun q ↦ p ∣ q)).sum (fun q ↦ (k : ℝ) / q))
        ≤
      (((range (N + 1)).filter (fun n : ℕ ↦ Nat.Prime n ∧ y < (n : ℝ)))).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    rw [Finset.filter_filter]
    refine Finset.prod_le_prod ?_ ?_
    · intro i hi
      exact add_nonneg zero_le_one (h₃ i)
    · simp only [Finset.mem_filter, and_imp, Finset.mem_range, Nat.lt_succ_iff, add_le_add_iff_left,
        div_eq_mul_inv, ← mul_sum]
      intro p hpN hp hpy
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      obtain ⟨m, hm⟩ := dvd_prime_powers hp (ppowers_in_set D)
        (by
          intro x hx
          exact (mem_ppowers_in_set.mp hx).1)
      refine
        (Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun i _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg _))).trans ?_
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_pow, ← inv_pow]
      refine
        (geom_sum_Ico_le_of_lt_one (inv_nonneg.2 (Nat.cast_nonneg p))
          ((inv_lt_one₀ (by exact_mod_cast hp.pos)).2 (by exact_mod_cast hp.one_lt))).trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast hp.ne_zero
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
      field_simp [hp0, hp1]
  refine mul_le_mul (hleft₁.trans hleft₂) hright (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
  · intro i hi
    exact add_nonneg zero_le_one (h₃ i)
  · intro i hi
    rw [mul_comm]
    exact add_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) my_mul_thing)

theorem useful_rec_aux4 (y : ℝ) (k N : ℕ) (D : Finset ℕ)
    (hD : ∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) :
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
      ((range (N + 1)).filter Nat.Prime).prod (fun p ↦ ((1 : ℝ) + k / (p * (p - 1)))) *
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ (1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹))) := by
  by_cases h0 : 0 ∈ D
  · have hD' : 0 ∉ D.erase 0 := by simp
    rw [← Finset.sum_erase_add _ _ h0, Nat.cast_zero, div_zero, add_zero]
    apply useful_rec_aux4' y k N _ hD'
    rwa [ppowers_in_set_erase_zero]
  · exact useful_rec_aux4' y k N D h0 hD

theorem useful_rec_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∀ y : ℝ,
          ∀ k N : ℕ,
            ∀ D : Finset ℕ,
              (1 < y →
                y < N →
                  1 ≤ k →
                    (∀ q : ℕ, q ∈ ppowers_in_set D → y < q ∧ q ≤ N) →
                      D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C * |log N| / |log y|) ^ k) := by
  rcases useful_rec_aux1 with ⟨C₁, hC₁, haux₁⟩
  rcases useful_rec_aux2 with ⟨C₂, hC₂, haux₂⟩
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro y k N D hy hyN hk hD
  have hmain := useful_rec_aux4 y k N D hD
  have hleft :
      ((range (N + 1)).filter Nat.Prime).prod
          (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        C₁ ^ k := haux₁ N k hk
  have hright :
      ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        (C₂ * |log N| / |log y|) ^ k := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using haux₂ y N k hk hy hyN
  have hright_nonneg :
      0 ≤
        ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
          (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    have hp1_nonneg : 0 ≤ (p : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast hp'.one_lt.le)
    exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 hp1_nonneg))
  have hCpow_nonneg : 0 ≤ C₁ ^ k := by
    exact pow_nonneg hC₁.le _
  have hmul :
      ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) ≤
        C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := by
    exact mul_le_mul hleft hright hright_nonneg hCpow_nonneg
  calc
    D.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤
        ((range (N + 1)).filter Nat.Prime).prod
            (fun p ↦ 1 + k / ((p : ℝ) * ((p : ℝ) - 1))) *
          ((range (N + 1)).filter (fun n ↦ Nat.Prime n ∧ y < n)).prod
            (fun p ↦ 1 + (k : ℝ) * (((p : ℝ) - 1)⁻¹)) := hmain
    _ ≤ C₁ ^ k * (C₂ * |log N| / |log y|) ^ k := hmul
    _ = ((C₁ * C₂) * |log N| / |log y|) ^ k := by
      rw [← mul_pow]
      congr 1
      ring

open Classical in
theorem find_good_d_aux1 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M u y : ℝ,
        ∀ q : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                0 ≤ u →
                  ∀ d ∈
                      (range (N + 1)).filter
                        (fun d : ℕ ↦
                          (∀ r : ℕ, IsPrimePow r → r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
                            M * u < (q * d : ℝ) ∧ q * d ≤ N),
                    ((((local_part A q).filter
                          (fun n ↦ (q * d) ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
                        (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤
                      2 * log N / d := by
  filter_upwards [eventually_ge_atTop 0, harmonic_sum_bound_two] with N hN hharmonic
  intro M u y q A hA hM hMN hu d hd
  let X :=
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hdlt : M * u < (q * d : ℝ) := (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : d ≠ 0 := by
    intro hzd
    subst hzd
    have hdlt' : M * u < 0 := by simpa using hdlt
    exact (not_lt_of_ge (mul_nonneg hM.le hu)) hdlt'
  have hqd_pos : 0 < (q * d : ℝ) := lt_of_le_of_lt (mul_nonneg hM.le hu) hdlt
  have hqd0 : (q * d : ℝ) ≠ 0 := ne_of_gt hqd_pos
  have hrectrivialaux :
      X.sum (fun n ↦ (q : ℚ) / n) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      exact ⟨hA (local_part_subset hx.1), hx.2.1⟩
    · intro i _ _
      exact div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg i)
  have hrectrivial' :
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
        ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
    calc
      (((X.sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) ≤
          ((((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) := by
        exact_mod_cast hrectrivialaux
      _ = ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) := by
        rw [Rat.cast_sum]
        push_cast
        rfl
  have hrectrivial'' :
      ((range (N + 1)).filter (fun x ↦ q * d ∣ x)).sum (fun n ↦ (q : ℝ) / n) ≤
        (1 / d : ℝ) *
          (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) := by
    let g : ℕ → ℕ := fun n ↦ n / (q * d)
    rw [Finset.mul_sum]
    refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
    · intro n hn
      exact mul_nonneg (one_div_nonneg.2 (Nat.cast_nonneg d)) (one_div_nonneg.2 (Nat.cast_nonneg n))
    · intro n hn
      rw [Finset.mem_filter] at hn
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr <|
          lt_of_le_of_lt (Nat.div_le_self _ _) (Finset.mem_range.mp hn.1)
      · dsimp [g]
        simpa [Nat.mul_div_cancel' hn.2] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn.1)
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      calc
        a = (q * d) * g a := by simp [g, Nat.mul_div_cancel' ha.2]
        _ = (q * d) * g b := by rw [hab]
        _ = b := by simp [g, Nat.mul_div_cancel' hb.2]
    · intro n hn
      rw [Finset.mem_filter] at hn
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hDnotzero
      have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
        simpa [Nat.cast_mul] using hqd0
      have hcast : (g n : ℝ) = (n : ℝ) / (q * d : ℕ) := by
        dsimp [g]
        rw [Nat.cast_div hn.2 hqd0']
      rw [hcast, Nat.cast_mul, one_div_mul_one_div, mul_div, one_div_div, mul_comm (q : ℝ),
        mul_div_mul_left _ _ hd0]
  have hrectrivial''' :
      ((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum (fun m ↦ (1 : ℝ) / m) ≤
        (range (N + 1)).sum (fun n ↦ (1 : ℝ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
      one_div_nonneg.2 (Nat.cast_nonneg i)
  have hfinal :
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
        2 * log N / d := by
    have hstep1 :
        (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m) ≤
          (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := by
      exact mul_le_mul_of_nonneg_left hrectrivial''' (one_div_nonneg.2 (Nat.cast_nonneg d))
    have hstep2 :
        (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) ≤ (1 / d : ℝ) * (2 * log N) := by
      exact mul_le_mul_of_nonneg_left hharmonic (one_div_nonneg.2 (Nat.cast_nonneg d))
    calc
      (1 / d : ℝ) * (((range (N + 1)).filter (fun x ↦ q * d * x ≤ N)).sum fun m ↦ (1 : ℝ) / m)
          ≤ (1 / d : ℝ) * ((range (N + 1)).sum fun n ↦ (1 : ℝ) / n) := hstep1
      _ ≤ (1 / d : ℝ) * (2 * log N) := hstep2
      _ = 2 * log N / d := by ring
  simpa [X] using hrectrivial'.trans (hrectrivial''.trans hfinal)

open Classical in
theorem find_good_d_aux2 :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ k : ℕ,
          ∀ A ⊆ range (N + 1),
            0 < M →
              M ≤ N →
                1 ≤ k →
                  (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                    ∀ q ∈ ppowers_in_set A,
                      ∀ n ∈ local_part A q,
                        ∃ d ∈
                            (range (N + 1)).filter
                              (fun d : ℕ ↦
                                (∀ r : ℕ,
                                    IsPrimePow r →
                                      r ∣ d →
                                        Nat.Coprime r (d / r) →
                                          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r ∧ r ≤ N) ∧
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q * d : ℝ) ∧
                                    q * d ≤ N),
                          (q * d ∣ n) ∧ Nat.Coprime (q * d) (n / (q * d)) := by
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with
    N hlargeN M k A hA hM hMN hk hAreg q hq n hn
  have hqpp : IsPrimePow q := by
    rw [mem_ppowers_in_set] at hq
    exact hq.1
  have hN : 0 < N := by
    exact lt_trans zero_lt_one hlargeN
  let Q : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r
  let d : ℕ := Q.prod id
  have memQ {r : ℕ} :
      r ∈ Q ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < r := by
    simp [Q]
  have hnz : n ≠ 0 := by
    intro hnz2
    rw [local_part, hnz2] at hn
    have htemp := hAreg 0 (Finset.mem_of_mem_filter 0 hn)
    exact (not_le_of_gt hM) (by exact_mod_cast htemp.1)
  have hnN : n ≤ N := by
    have hnA : n ∈ A := Finset.mem_of_mem_filter n hn
    have hnRange : n ∈ range (N + 1) := hA hnA
    exact Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hnRange)
  have hqdcop : Nat.Coprime q d := by
    by_contra h
    rw [prime_pow_not_coprime_prod_iff hqpp] at h
    · rcases h with ⟨p, kq, kd, d', hd, hp, hkq, hkd, hpq, hpd⟩
      rw [local_part, Finset.mem_filter] at hn
      have hd' : d' ∈ n.divisors ∧ IsPrimePow d' ∧ Nat.Coprime d' (n / d') ∧ d' ≠ q ∧
          Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < d' := by
        simpa [memQ] using hd
      rcases hd' with ⟨hdDiv, hdProps⟩
      apply hdProps.2.2.1
      rw [← hpq, ← hpd]
      refine congrArg (fun t : ℕ => p ^ t) ?_
      calc
        kd = n.factorization p := by
          apply coprime_div_iff hp
          · rw [hpd]
            exact Nat.dvd_of_mem_divisors hdDiv
          · exact hkd
          · rw [hpd]
            exact hdProps.2.1
        _ = kq := by
          refine Eq.symm ?_
          apply coprime_div_iff hp
          · rw [hpq]
            exact hn.2.1
          · exact hkq
          · rw [hpq]
            exact hn.2.2
    · intro x hx
      exact (memQ.mp hx).2.1
  have hQcoprime :
      ∀ a ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
        ∀ b ∈ n.divisors.filter (fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)),
          a ≠ b → Nat.Coprime a b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    by_contra h
    rw [prime_pow_not_coprime_iff ha.2.1 hb.2.1] at h
    rcases h with ⟨p, ka, kb, hp, hka, hkb, hpa, hpb⟩
    apply hab
    rw [← hpa, ← hpb]
    refine congrArg (fun t : ℕ => p ^ t) ?_
    calc
      ka = n.factorization p := by
        apply coprime_div_iff hp
        · rw [hpa]
          exact Nat.dvd_of_mem_divisors ha.1
        · exact hka
        · rw [hpa]
          exact ha.2.2
      _ = kb := by
        refine Eq.symm ?_
        apply coprime_div_iff hp
        · rw [hpb]
          exact Nat.dvd_of_mem_divisors hb.1
        · exact hkb
        · rw [hpb]
          exact hb.2.2
  have hqd : q * d ∣ n := by
    rw [dvd_iff_ppowers_dvd]
    intro r hr1 hr2
    rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hr1 with hrq | hrd
    · rw [local_part, Finset.mem_filter] at hn
      exact dvd_trans hrq hn.2.1
    · rw [is_prime_pow_dvd_prod ?_ hr2] at hrd
      · rcases hrd with ⟨t, ht, hrt⟩
        exact dvd_trans hrt (Nat.dvd_of_mem_divisors (memQ.mp ht).1)
      · intro a ha b hb hab
        refine hQcoprime _ ?_ _ ?_ hab
        · exact Finset.mem_filter.mpr ⟨(memQ.mp ha).1, (memQ.mp ha).2.1, (memQ.mp ha).2.2.1⟩
        · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
  have hdupp : q * d ≤ N := by
    refine le_trans (Nat.le_of_dvd ?_ hqd) hnN
    have : (0 : ℝ) < n := by
      refine lt_of_lt_of_le hM ?_
      exact (hAreg n (Finset.mem_of_mem_filter n hn)).1
    exact_mod_cast this
  let Q' : Finset ℕ :=
    n.divisors.filter fun r ↦
      IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
        (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  have memQ' {r : ℕ} :
      r ∈ Q' ↔
        r ∈ n.divisors ∧ IsPrimePow r ∧ Nat.Coprime r (n / r) ∧ r ≠ q ∧
          (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
    simp [Q']
  have hQ'dcop : Nat.Coprime q (Q'.prod id) := by
    by_contra h
    rw [prime_pow_not_coprime_prod_iff hqpp] at h
    · rcases h with ⟨p, kq, kd, d', hd, hp, hkq, hkd, hpq, hpd⟩
      rw [local_part, Finset.mem_filter] at hn
      have hd' : d' ∈ n.divisors ∧ IsPrimePow d' ∧ Nat.Coprime d' (n / d') ∧ d' ≠ q ∧
          (d' : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
        simpa [memQ'] using hd
      rcases hd' with ⟨hdDiv, hdProps⟩
      apply hdProps.2.2.1
      rw [← hpq, ← hpd]
      refine congrArg (fun t : ℕ => p ^ t) ?_
      calc
        kd = n.factorization p := by
          apply coprime_div_iff hp
          · rw [hpd]
            exact Nat.dvd_of_mem_divisors hdDiv
          · exact hkd
          · rw [hpd]
            exact hdProps.2.1
        _ = kq := by
          refine Eq.symm ?_
          apply coprime_div_iff hp
          · rw [hpq]
            exact hn.2.1
          · exact hkq
          · rw [hpq]
            exact hn.2.2
    · intro x hx
      exact (memQ'.mp hx).2.1
  have hQ'qd : Nat.Coprime (q * d) (Q'.prod id) := by
    apply Nat.Coprime.symm
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.symm hQ'dcop
    · rw [prime_pow_prods_coprime]
      · intro a ha b hb
        refine hQcoprime _ ?_ _ ?_ ?_
        · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
        · exact Finset.mem_filter.mpr ⟨(memQ.mp hb).1, (memQ.mp hb).2.1, (memQ.mp hb).2.2.1⟩
        · intro hab
          have ha' := memQ'.mp ha
          have hb' := memQ.mp hb
          rw [hab] at ha'
          have hbnge : ¬ ((b : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))) := by
            exact (lt_iff_not_ge).mp hb'.2.2.2.2
          exact hbnge ha'.2.2.2.2
      · intro a ha
        exact (memQ'.mp ha).2.1
      · intro a ha
        exact (memQ.mp ha).2.1
  have hnqd : n = (Q'.prod id) * q * d := by
    rw [eq_iff_ppowers_dvd n ((Q'.prod id) * q * d) hnz ?_]
    · constructor
      · intro r hr1 hr2 hr3
        by_cases hrq : r = q
        · rw [mul_assoc, hrq]
          exact dvd_trans (dvd_mul_right q d) <|
            dvd_mul_of_dvd_right (dvd_refl (q * d)) (Q'.prod id)
        · by_cases hrsize : (r : ℝ) ≤ Real.exp (log N ^ ((1 : ℝ) - 2 / k))
          · have hrmem : r ∈ Q' := by
              exact memQ'.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            exact dvd_trans (Finset.dvd_prod_of_mem id hrmem) <|
              dvd_mul_of_dvd_left (dvd_mul_right (Q'.prod id) q) d
          · have hrmem : r ∈ Q := by
              rw [← lt_iff_not_ge] at hrsize
              exact memQ.mpr
                ⟨by simpa [Nat.mem_divisors] using And.intro hr1 hnz, hr2, hr3, hrq, hrsize⟩
            have hrd' : r ∣ q * d := by
              have : r ∣ Q.prod id := Finset.dvd_prod_of_mem id hrmem
              simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                dvd_trans this (dvd_mul_right (Q.prod id) q)
            exact dvd_trans hrd' <| by
              simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                dvd_mul_right (q * d) (Q'.prod id)
      · intro r hr1 hr2 hr3
        have hr1' : r ∣ (Q'.prod id) * (q * d) := by
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr1
        rcases (Nat.Coprime.symm hQ'qd).isPrimePow_dvd_mul hr2 |>.mp hr1' with hw1 | hw2
        · rw [is_prime_pow_dvd_prod ?_ hr2] at hw1
          · rcases hw1 with ⟨t, ht, hwt⟩
            exact dvd_trans hwt (Nat.dvd_of_mem_divisors (memQ'.mp ht).1)
          · intro a ha b hb hab
            refine hQcoprime _ ?_ _ ?_ hab
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp ha).1, (memQ'.mp ha).2.1, (memQ'.mp ha).2.2.1⟩
            · exact Finset.mem_filter.mpr ⟨(memQ'.mp hb).1, (memQ'.mp hb).2.1, (memQ'.mp hb).2.2.1⟩
        · rcases (hqdcop.isPrimePow_dvd_mul hr2).mp hw2 with hw3 | hw4
          · rw [local_part, Finset.mem_filter] at hn
            exact dvd_trans hw3 hn.2.1
          · exact dvd_trans hw4 (dvd_trans (dvd_mul_left _ _) hqd)
    · have hQ'ne : Q'.prod id ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro r hr
        exact Nat.ne_of_gt <| Nat.succ_le_iff.mp (memQ'.mp hr).2.1.pos
      have hqd0 : q * d ≠ 0 := by
        intro hbad
        apply hnz
        rw [hbad, zero_dvd_iff] at hqd
        exact hqd
      simpa [Nat.mul_assoc] using Nat.mul_ne_zero hQ'ne hqd0
  refine ⟨d, ?_, hqd, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_range, Nat.lt_succ_iff]
      refine le_trans ?_ hdupp
      exact Nat.le_mul_of_pos_left d (Nat.pos_of_ne_zero <| by
        intro h
        rw [h] at hq
        exact zero_not_mem_ppowers_in_set hq)
    · refine ⟨?_, ?_, hdupp⟩
      · intro r hr1 hr2 hr3
        have hrQ : r ∈ Q := by
          refine prime_pow_dvd_prod_prime_pow hr1 ?_ ?_ hr2 hr3
          · intro a ha b hb hab
            by_contra h
            have ha' := memQ.mp ha
            have hb' := memQ.mp hb
            have h' := prime_pow_not_coprime_prime_pow ha'.2.1 hb'.2.1 h
            rcases h' with ⟨p, k, l, hp, hkl, hpa, hpb⟩
            have hafac : n.factorization p = k := by
              rw [← factorization_eq_iff hp hkl.1, hpa]
              exact ⟨Nat.dvd_of_mem_divisors ha'.1, ha'.2.2.1⟩
            have hbfac : n.factorization p = l := by
              rw [← factorization_eq_iff hp hkl.2, hpb]
              exact ⟨Nat.dvd_of_mem_divisors hb'.1, hb'.2.2.1⟩
            apply hab
            rw [← hpa, ← hpb, ← hafac, ← hbfac]
          · intro t ht
            exact (memQ.mp ht).2.1
        refine ⟨(memQ.mp hrQ).2.2.2.2, ?_⟩
        exact le_trans (Nat.divisor_le (memQ.mp hrQ).1) hnN
      · have hstep :
            M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) ≤
              (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
            exact mul_le_mul_of_nonneg_right
              ((hAreg n (Finset.mem_of_mem_filter n hn)).1) (le_of_lt (Real.exp_pos _))
        have hstep' : (n : ℝ) * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < (q : ℝ) * d := by
          rw [hnqd]
          push_cast
          rw [← Nat.cast_prod]
          have hmul :
              ((((Q'.prod id : ℕ) : ℝ) * (q : ℝ) * (d : ℝ)) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) =
                ((((Q'.prod id : ℕ) : ℝ) *
                Real.exp (-log N ^ ((1 : ℝ) - 1 / k))) * ((q : ℝ) * d)) := by
            ring
          rw [hmul]
          have hqd0' : q * d ≠ 0 := by
            intro hzero
            rw [hzero, zero_dvd_iff] at hqd
            exact hnz hqd
          have hqdpos : 0 < (q : ℝ) * d := by
            exact_mod_cast Nat.pos_of_ne_zero hqd0'
          rw [mul_comm]
          apply mul_lt_of_lt_one_right hqdpos
          · rw [exp_neg, ← one_div, mul_one_div, div_lt_one]
            · calc
              (((Q'.prod id : ℕ) : ℝ)) = Q'.prod (fun i ↦ (i : ℝ)) := by
                simp
              _ ≤ (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ Q'.card := by
                refine prod_le_max_size ?_ _ ?_
                · intro i hi
                  exact Nat.cast_nonneg i
                · intro i hi
                  exact (memQ'.mp hi).2.2.2.2
              _ < (Real.exp (log N ^ ((1 : ℝ) - 2 / k))) ^ (log N ^ ((1 : ℝ) / k)) := by
                rw [← Real.rpow_natCast]
                apply Real.rpow_lt_rpow_of_exponent_lt
                · rw [one_lt_exp_iff]
                  apply Real.rpow_pos_of_pos
                  exact Real.log_pos (by exact_mod_cast hlargeN)
                · calc
                    (Q'.card : ℝ) ≤
                        (n.divisors.filter fun r ↦ IsPrimePow r ∧ Nat.Coprime r (n / r)).card := by
                          have hsubset : Q' ⊆ n.divisors.filter fun r ↦
                              IsPrimePow r ∧ Nat.Coprime r (n / r) := by
                            intro r hr
                            exact Finset.mem_filter.mpr
                              ⟨(memQ'.mp hr).1, (memQ'.mp hr).2.1, (memQ'.mp hr).2.2.1⟩
                          exact_mod_cast Finset.card_le_card hsubset
                    _ = (ω n : ℝ) := by
                      norm_num [omega_count_eq_ppowers]
                    _ < log N ^ ((1 : ℝ) / k) := by
                      rw [local_part] at hn
                      exact (hAreg n (Finset.mem_of_mem_filter n hn)).2
              _ = Real.exp (log N ^ ((1 : ℝ) - 1 / k)) := by
                rw [← Real.exp_mul, ← Real.rpow_add]
                · ring_nf
                exact Real.log_pos (by exact_mod_cast hlargeN)
            exact Real.exp_pos _
        exact lt_of_le_of_lt hstep hstep'
  · have hqd0 : q * d ≠ 0 := by
      intro hzero
      rw [hzero, zero_dvd_iff] at hqd
      exact hnz hqd
    have hquot : n / (q * d) = Q'.prod id := by
      rw [hnqd, Nat.mul_assoc]
      rw [Nat.mul_comm (Q'.prod id) (q * d)]
      exact Nat.mul_div_right (Q'.prod id) (Nat.pos_of_ne_zero hqd0)
    simpa [hquot] using hQ'qd

private theorem find_good_d_hc (C1 : ℝ) (_hC1 : 0 < C1) :
    0 < ((1 / 2 : ℝ) / Real.log (max C1 2)) := by
  refine div_pos (by norm_num) ?_
  apply Real.log_pos
  exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)

private theorem find_good_d_hC (C1 : ℝ) (hC1 : 0 < C1) :
    0 < (1 / (C1 * 2) : ℝ) := by
  rw [one_div_pos]
  exact mul_pos hC1 zero_lt_two

private theorem find_good_d_hC' (C1 : ℝ) (hC1 : 0 < C1) :
    C1 = 1 / (((1 / (C1 * 2) : ℝ)) * 2) := by
  have hC10 : C1 ≠ 0 := ne_of_gt hC1
  field_simp [hC10]

private theorem find_good_d_hC2 (C1 : ℝ) : 1 < max C1 2 := by
  exact lt_of_lt_of_le one_lt_two (le_max_right C1 2)

private theorem find_good_d_hlarge1 {N : ℕ} (hlarge : 1 < log N) : 0 < log N := by
  exact lt_trans zero_lt_one hlarge

private theorem find_good_d_hlarge2 {N : ℕ} (hlarge1 : 0 < log N) (hlarge'' : (16 : ℝ) ≤ log N) :
    4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
  have hsqrt : (4 : ℝ) ≤ log N ^ ((1 : ℝ) / 2) := by
    have hsqrt' : Real.sqrt (16 : ℝ) ≤ Real.sqrt (log N) := Real.sqrt_le_sqrt hlarge''
    norm_num [Real.sqrt_eq_rpow] at hsqrt' ⊢
    exact hsqrt'
  have hpowpos : 0 < log N ^ ((1 : ℝ) / 2) := by
    positivity
  have hlog0 : 0 ≤ log N := le_of_lt hlarge1
  calc
    4 * log N ^ (-((3 : ℝ) / 2) + 1) = 4 / log N ^ ((1 : ℝ) / 2) := by
      rw [show -((3 : ℝ) / 2) + 1 = -((1 : ℝ) / 2) by ring]
      rw [Real.rpow_neg hlog0, ← one_div]
      ring
    _ ≤ 1 := by
      exact (div_le_iff₀ hpowpos).2 (by simpa using hsqrt)

private theorem find_good_d_h1y {N k : ℕ} (hlarge1 : 0 < log N) :
    1 < Real.exp (log N ^ ((1 : ℝ) - 2 / k)) := by
  rw [Real.one_lt_exp_iff]
  exact Real.rpow_pos_of_pos hlarge1 _

private theorem find_good_d_hyN {N k : ℕ} (hlarge : 1 < log N) (hlarge' : 0 < N) (h1k : 1 < k) :
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < N := by
  have hexp : log N ^ ((1 : ℝ) - 2 / k) < log N ^ (1 : ℝ) := by
    refine Real.rpow_lt_rpow_of_exponent_lt hlarge ?_
    refine sub_lt_self 1 ?_
    refine div_pos zero_lt_two ?_
    exact_mod_cast (lt_trans zero_lt_one h1k)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hlarge'
  calc
    Real.exp (log N ^ ((1 : ℝ) - 2 / k)) < Real.exp (log N) := by
      simpa using Real.exp_lt_exp.mpr hexp
    _ = N := by rw [Real.exp_log hNpos]

private theorem find_good_d_h0k {k : ℕ} (h1k : 1 < k) : (0 : ℝ) < k := by
  exact_mod_cast (lt_trans zero_lt_one h1k)

private theorem find_good_d_hlocal2 {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (haux2 : ∀ n ∈ local_part A q, ∃ d ∈ D, q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))) :
    local_part A q ⊆ D.biUnion newLocal := by
  subst newLocal
  intro n hn
  rw [Finset.mem_biUnion]
  rcases haux2 n hn with ⟨d, hd, hlocal⟩
  refine ⟨d, hd, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hn, hlocal⟩

private theorem find_good_d_hrecbound {A : Finset ℕ} {q : ℕ} (D : Finset ℕ)
    (newLocal : ℕ → Finset ℕ)
    (hnewLocal :
      newLocal =
        fun d : ℕ ↦
          (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))))
    (hlocal2 : local_part A q ⊆ D.biUnion newLocal) :
    rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  subst newLocal
  rw [rec_sum_local]
  let s :=
    D.biUnion fun d ↦
      (local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))
  have h1 : (local_part A q).sum (fun n ↦ (q : ℚ) / n) ≤ s.sum (fun n ↦ (q : ℚ) / n) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hlocal2 (by
      intro i _ _
      positivity)
  have h2 :
      s.sum (fun n ↦ (q : ℚ) / n) ≤
        D.sum (fun d ↦
          ((local_part A q).filter fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d))).sum
            (fun n ↦ (q : ℚ) / n)) := by
    dsimp [s]
    refine sum_bUnion_le_sum_of_nonneg ?_
    intro i _
    positivity
  exact le_trans h1 h2

private theorem find_good_d_hDnotzero {M u : ℝ} {q : ℕ} {D : Finset ℕ}
    (hzM : 0 < M) (hu : 0 < u) (hDu : ∀ d ∈ D, M * u < q * d) :
    ∀ d ∈ D, d ≠ 0 := by
  intro d hd hd0
  have hd' := hDu d hd
  rw [hd0, Nat.cast_zero, mul_zero] at hd'
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hzM) (le_of_lt hu))) hd'

private theorem find_good_d_hbound1 {C1 c y ω0 : ℝ} {N q k : ℕ} {A D1 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hC1 : 0 < C1) (hc : c = (1 / 2 : ℝ) / Real.log (max C1 2))
    (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hkN : (k : ℝ) ≤ c * log (log N)) (hlarge1 : 0 < log N)
    (hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1) (h1k : 1 < k) (h0k : (0 : ℝ) < k)
    (hω0 : ω0 = (5 / log k) * log (log N)) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hωD1 : ∀ d ∈ D1, ω0 ≤ (ω d : ℝ))
    (haux1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d)
    (hrec1bound : D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k) :
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
      (rec_sum_local A q : ℝ) / 2 := by
  let C2 : ℝ := max C1 2
  have hC2 : 1 < C2 := lt_of_lt_of_le one_lt_two (le_max_right C1 2)
  have h1y : 1 < y := by
    rw [hy, Real.one_lt_exp_iff]
    exact Real.rpow_pos_of_pos hlarge1 _
  have hfac_nonneg : 0 ≤ 2 * log N := by positivity
  have hkpow_nonneg : 0 ≤ (k : ℝ) ^ (-ω0) := le_of_lt (Real.rpow_pos_of_pos h0k _)
  calc
    ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ)
        = D1.sum (fun d ↦ (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ)) := by
          rw [Rat.cast_sum]
    _ ≤ D1.sum (fun d ↦ 2 * log N / d) := by
          refine Finset.sum_le_sum ?_
          intro d hd
          exact haux1 d hd
    _ = 2 * log N * D1.sum (fun d ↦ (1 : ℝ) / d) := by
      rw [mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [div_eq_mul_one_div]
    _ ≤ 2 * log N * D1.sum (fun d ↦ (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d)) := by
      apply mul_le_mul_of_nonneg_left
      · refine Finset.sum_le_sum ?_
        intro d hd
        have hkge : 1 ≤ (k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d := by
          rw [← Real.rpow_natCast, ← Real.rpow_add]
          · apply one_le_rpow
            · exact_mod_cast (le_of_lt h1k)
            · linarith [hωD1 d hd]
          · exact h0k
        calc
          (1 : ℝ) / d = 1 * (1 / d) := by ring
          _ ≤ ((k : ℝ) ^ (-ω0) * (k : ℝ) ^ ω d) * (1 / d) := by
            exact mul_le_mul_of_nonneg_right hkge (by
              rw [one_div_nonneg]
              exact_mod_cast Nat.cast_nonneg d)
          _ = (k : ℝ) ^ (-ω0) * (((k : ℝ) ^ ω d) / d) := by
            rw [div_eq_mul_one_div]
            ring
      · exact hfac_nonneg
    _ = 2 * log N * (k : ℝ) ^ (-ω0) * D1.sum (fun d ↦ ((k : ℝ) ^ ω d / d)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * log N * (k : ℝ) ^ (-ω0) * (C1 * |log N| / |log y|) ^ k := by
      exact mul_le_mul_of_nonneg_left hrec1bound (mul_nonneg hfac_nonneg hkpow_nonneg)
    _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by
      have hkpow :
          (k : ℝ) ^ (-ω0) = log N ^ (-5 : ℝ) := by
        have hlogk : 0 < Real.log k := by
          exact Real.log_pos (by exact_mod_cast h1k)
        calc
          (k : ℝ) ^ (-ω0) = Real.exp (Real.log k * (-ω0)) := by
            rw [Real.rpow_def_of_pos h0k]
          _ = Real.exp (-5 * log (log N)) := by
            rw [hω0]
            field_simp [ne_of_gt hlogk]
          _ = Real.exp (log (log N) * (-5 : ℝ)) := by ring_nf
          _ = (Real.exp (log (log N))) ^ (-5 : ℝ) := by rw [Real.exp_mul]
          _ = log N ^ (-5 : ℝ) := by rw [Real.exp_log hlarge1]
      have hyabs : |log y| = log N ^ ((1 : ℝ) - 2 / k) := by
        rw [hy, Real.log_exp, abs_eq_self.mpr]
        exact le_of_lt (Real.rpow_pos_of_pos hlarge1 _)
      have hquot : log N / log N ^ ((1 : ℝ) - (2 : ℝ) / k) = log N ^ ((2 : ℝ) / k) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_sub hlarge1 (1 : ℝ) ((1 : ℝ) - (2 : ℝ) / k)]
        have hEq : (1 : ℝ) - ((1 : ℝ) - (2 : ℝ) / k) = (2 : ℝ) / k := by
          field_simp [ne_of_gt h0k]
          ring
        rw [hEq]
      have hpowLog : (log N ^ (((2 : ℝ) / k))) ^ k = log N ^ (2 : ℝ) := by
        have hk2 : (((2 : ℝ) / k)) * k = 2 := by
          field_simp [ne_of_gt h0k]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlarge1.le, hk2]
      have hpowFinal : log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ) = log N ^ (-2 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one (log N)]
        rw [← Real.rpow_add hlarge1, ← Real.rpow_add hlarge1]
        norm_num
      rw [hkpow, abs_eq_self.mpr hlarge1.le, hyabs, mul_div_assoc, hquot, mul_pow]
      change
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * (log N ^ (((2 : ℝ) / k))) ^ k) =
          2 * log N ^ (-2 : ℝ) * C1 ^ k
      rw [hpowLog]
      calc
        2 * log N * log N ^ (-5 : ℝ) * (C1 ^ k * log N ^ (2 : ℝ))
            = 2 * (log N * log N ^ (-5 : ℝ) * log N ^ (2 : ℝ)) * C1 ^ k := by
              ring
        _ = 2 * (log N ^ (-2 : ℝ)) * C1 ^ k := by rw [hpowFinal]
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * C2 ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (le_of_lt hC1) (le_max_left C1 2) _
      · positivity
    _ ≤ 2 * (log N ^ (-2 : ℝ)) * (log N ^ (Real.log C2 * c)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [← Real.rpow_natCast]
        refine (Real.le_rpow_iff_log_le
          (Real.rpow_pos_of_pos (show 0 < C2 by linarith) _) hlarge1).2 ?_
        rw [Real.log_rpow (show 0 < C2 by linarith), mul_comm (k : ℝ), mul_assoc]
        exact mul_le_mul_of_nonneg_left hkN (Real.log_pos hC2).le
      · positivity
    _ = 2 * (log N ^ (-(3 / 2 : ℝ))) := by
      rw [hc, show Real.log C2 = Real.log (max C1 2) by rfl]
      rw [mul_assoc, ← Real.rpow_add hlarge1]
      have hlogne : Real.log (max C1 2) ≠ 0 := ne_of_gt (Real.log_pos hC2)
      congr 1
      field_simp [hlogne]
      ring_nf
    _ ≤ (1 / log N) / 2 := by
      rw [le_div_iff₀ zero_lt_two, le_div_iff₀ hlarge1]
      calc
        2 * log N ^ (-(3 / 2 : ℝ)) * 2 * log N
            = 4 * log N ^ (-((3 : ℝ) / 2) + 1) := by
              rw [show (2 : ℝ) * log N ^ (-(3 / 2 : ℝ)) * 2 * log N =
                4 * (log N ^ (-(3 / 2 : ℝ)) * log N) by ring]
              nth_rewrite 2 [show (log N : ℝ) = log N ^ (1 : ℝ) by rw [Real.rpow_one]]
              rw [← Real.rpow_add hlarge1]
        _ ≤ 1 := hlarge2
    _ ≤ ((rec_sum_local A q : ℝ) / 2) := by
      have hhalf :
          (1 / log N) * (1 / 2 : ℝ) ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsumq (show (0 : ℝ) ≤ 1 / 2 by positivity)
      calc
        (1 / log N) / 2 = (1 / log N) * (1 / 2 : ℝ) := by ring
        _ ≤ (rec_sum_local A q : ℝ) * (1 / 2 : ℝ) := hhalf
        _ = (rec_sum_local A q : ℝ) / 2 := by ring

private theorem find_good_d_hbound2 {ω0 : ℝ} {A : Finset ℕ} {q : ℕ} {D D1 D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hD1 : D1 = D.filter (fun d ↦ ω0 ≤ (ω d : ℝ)))
    (hD2 : D2 = D.filter (fun d ↦ (ω d : ℝ) < ω0))
    (hrecbound : rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
  calc
    (rec_sum_local A q : ℚ) / 2 = rec_sum_local A q - (rec_sum_local A q : ℚ) / 2 := by
      exact Eq.symm (sub_self_div_two (rec_sum_local A q))
    _ ≤
        D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) -
          D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
      apply sub_le_sub
      · exact hrecbound
      · exact_mod_cast hbound1
    _ = D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
      have hDD : D = D1 ∪ D2 := by
        rw [hD1, hD2]
        ext d
        constructor
        · intro hd
          rw [Finset.mem_union]
          by_cases hdω : ω0 ≤ (ω d : ℝ)
          · exact Or.inl (Finset.mem_filter.mpr ⟨hd, hdω⟩)
          · exact Or.inr (Finset.mem_filter.mpr ⟨hd, lt_of_not_ge hdω⟩)
        · intro hd
          rcases Finset.mem_union.mp hd with hd | hd
          · exact Finset.mem_of_mem_filter d hd
          · exact Finset.mem_of_mem_filter d hd
      have hdisj : Disjoint D1 D2 := by
        rw [hD1, hD2, Finset.disjoint_left]
        intro x hx1 hx2
        exact not_lt_of_ge (Finset.mem_filter.mp hx1).2 (Finset.mem_filter.mp hx2).2
      rw [hDD, Finset.sum_union hdisj]
      simp

private theorem find_good_d_hbound3 {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)))
    (hDnotzero : ∀ d ∈ D2, d ≠ 0) :
    (rec_sum_local A q : ℚ) / 2 ≤
      D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
  apply le_trans hbound2
  refine Finset.sum_le_sum ?_
  intro d hd
  rw [mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  apply le_of_eq
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast hDnotzero d hd
  field_simp [hd0]

private theorem find_good_d_hDsumpos {A : Finset ℕ} {q : ℕ} {N : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))))
    (hDnotzero : ∀ d ∈ D2, d ≠ 0) (hlarge1 : 0 < log N)
    (hsumq : 1 / log N ≤ rec_sum_local A q) :
    0 < D2.sum (fun d ↦ (1 / d : ℚ)) := by
  refine Finset.sum_pos ?_ ?_
  · intro i hi
    rw [one_div_pos]
    exact_mod_cast Nat.pos_of_ne_zero (hDnotzero i hi)
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hempty2 :
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) = 0 := by
      rw [hempty, Finset.sum_empty]
    rw [hempty2] at hbound3
    have hpos : (0 : ℚ) < rec_sum_local A q / 2 := by
      refine div_pos ?_ zero_lt_two
      have : (0 : ℝ) < rec_sum_local A q := by
        refine lt_of_lt_of_le ?_ hsumq
        exact one_div_pos.mpr hlarge1
      exact_mod_cast this
    exact (not_le_of_gt hpos) hbound3

private theorem find_good_d_hfound0 {A : Finset ℕ} {q : ℕ} {N : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))))
    (hlarge1 : 0 < log N) (hsumq : 1 / log N ≤ rec_sum_local A q) :
    ∃ x ∈ D2,
      (rec_sum_local A q : ℚ) / 2 ≤
        (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) := by
  have hpos : (0 : ℚ) < rec_sum_local A q / 2 := by
    refine div_pos ?_ zero_lt_two
    have : (0 : ℝ) < rec_sum_local A q := by
      refine lt_of_lt_of_le ?_ hsumq
      exact one_div_pos.mpr hlarge1
    exact_mod_cast this
  rcases weighted_ph hpos (by
      intro d hd
      positivity) hbound3 with ⟨x, hx, hineq⟩
  exact ⟨x, hx, hineq⟩

private theorem find_good_d_hfound {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hfound0 :
      ∃ x ∈ D2,
        (rec_sum_local A q : ℚ) / 2 ≤
          (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)))
    (hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ))) :
    ∃ d ∈ D2,
      (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) := by
  rcases hfound0 with ⟨x, hx1, hx2⟩
  refine ⟨x, hx1, ?_⟩
  have hpos : (0 : ℚ) < 2 * D2.sum (fun d ↦ (1 / d : ℚ)) := by positivity
  refine (div_le_iff₀ hpos).2 ?_
  calc
    (rec_sum_local A q : ℚ) = 2 * ((rec_sum_local A q : ℚ) / 2) := by ring
    _ ≤ 2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n))) := by
      gcongr
    _ = (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) * (2 * D2.sum (fun d ↦ (1 / d : ℚ))) := by
      ring

private theorem find_good_d_hfound1 {A : Finset ℕ} {q : ℕ} {D2 : Finset ℕ}
    {newLocal : ℕ → Finset ℕ}
    (hfound :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) :
    ∃ d ∈ D2,
      (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
  rcases hfound with ⟨d, hd1, hd2⟩
  refine ⟨d, hd1, ?_⟩
  calc
    (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) =
        ((((rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ)))) : ℚ) : ℝ) := by
      simp [Rat.cast_sum]
    _ ≤ (((newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) : ℚ) : ℝ) := by
      exact_mod_cast hd2
    _ = (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
      simp [Rat.cast_sum]

private theorem find_good_d_hbound4 {C1 C : ℝ} {N k : ℕ} {y : ℝ} {D2 : Finset ℕ}
    (hC' : C1 = 1 / (C * 2)) (hy : y = Real.exp (log N ^ ((1 : ℝ) - 2 / k)))
    (hlarge1 : 0 < log N)
    (hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1) :
    D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
  calc
    D2.sum (fun d ↦ (1 / d : ℝ)) = D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp
    _ ≤ (C1 * |log N| / |log y|) ^ 1 := hrec2bound
    _ = C1 * log N ^ ((2 : ℝ) / k) := by
      have hy1 : 1 < y := by
        rw [hy, Real.one_lt_exp_iff]
        exact Real.rpow_pos_of_pos hlarge1 _
      rw [pow_one, abs_eq_self.mpr (le_of_lt hlarge1),
        abs_eq_self.mpr (le_of_lt (Real.log_pos hy1)),
        hy, Real.log_exp]
      rw [mul_div_assoc]
      have hdiv :
          log N / log N ^ ((1 : ℝ) - 2 / k) = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
        calc
          log N / log N ^ ((1 : ℝ) - 2 / k)
              = log N ^ (1 : ℝ) / log N ^ ((1 : ℝ) - 2 / k) := by rw [Real.rpow_one]
          _ = log N ^ ((1 : ℝ) - ((1 : ℝ) - 2 / k)) := by rw [← Real.rpow_sub hlarge1]
          _ = log N ^ ((2 : ℝ) / k) := by ring_nf
          _ = (log N ^ (1 : ℝ)) ^ ((2 : ℝ) / k) := by
            rw [← Real.rpow_mul (le_of_lt hlarge1)]
            ring_nf
      simpa [Real.rpow_one] using congrArg (fun t => C1 * t) hdiv
    _ = log N ^ ((2 : ℝ) / k) / (C * 2) := by
      rw [mul_comm C1, ← mul_one_div, hC']
      ring

private theorem find_good_d_hfinal {C : ℝ} {A : Finset ℕ} {q N k d : ℕ}
    {D2 : Finset ℕ} {newLocal : ℕ → Finset ℕ}
    (hC : 0 < C) (hlarge1 : 0 < log N) (hsumq : 1 / log N ≤ rec_sum_local A q)
    (hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ)))
    (hfound1 :
      (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)))
    (hbound4 : D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2)) :
    C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
      (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
  have hsumq' : (0 : ℝ) < rec_sum_local A q := by
    refine lt_of_lt_of_le ?_ hsumq
    exact one_div_pos.mpr hlarge1
  have haux :
      C / log N ^ ((2 : ℝ) / k) ≤
        1 / (2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ)) := by
    have hbound4' :
        (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
      simpa using hbound4
    have hbound4'' :
        (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) * (C * 2) ≤ log N ^ ((2 : ℝ) / k) := by
      exact (le_div_iff₀ (mul_pos hC zero_lt_two)).mp hbound4'
    have hmul : 2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) ≤ log N ^ ((2 : ℝ) / k) / C := by
      refine (le_div_iff₀ hC).2 ?_
      nlinarith
    have hrecip :=
      one_div_le_one_div_of_le
        (show 0 < 2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ) by
          exact mul_pos zero_lt_two (by exact_mod_cast hDsumpos))
        hmul
    simpa [one_div_div] using hrecip
  have hmul :
      (rec_sum_local A q : ℝ) * (C / log N ^ ((2 : ℝ) / k)) ≤
        (rec_sum_local A q : ℝ) *
          (1 / (2 * (((D2.sum (fun d ↦ (1 / d : ℚ))) : ℚ) : ℝ))) :=
    mul_le_mul_of_nonneg_left haux (le_of_lt hsumq')
  refine le_trans ?_ hfound1
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem find_good_d :
    ∃ c C : ℝ,
      0 < c ∧
        0 < C ∧
          ∀ᶠ N : ℕ in atTop,
            ∀ M : ℝ,
              ∀ k : ℕ,
                ∀ A ⊆ range (N + 1),
                  0 < M →
                    M ≤ N →
                      1 < k →
                        (k : ℝ) ≤ c * log (log N) →
                          (∀ n ∈ A, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k))) →
                            ∀ q ∈ ppowers_in_set A,
                              1 / log N ≤ rec_sum_local A q →
                                ∃ d : ℕ,
                                  M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d ∧
                                    ((ω d : ℝ) < (5 / log k) * log (log N)) ∧
                                      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
                                        ((local_part A q).filter
                                            (fun n ↦ q * d ∣ n ∧
                                              Nat.Coprime (q * d) (n / (q * d)))).sum
                                          (fun n ↦ (q * d / n : ℝ)) := by
  classical
  rcases useful_rec_bound with ⟨C1, hC1, hrec1⟩
  let C2 := max C1 2
  let c : ℝ := (1 / 2) / Real.log C2
  have hc : 0 < c := by
    simpa [c, C2] using find_good_d_hc C1 hC1
  let C : ℝ := 1 / (C1 * 2)
  have hC : 0 < C := by
    simpa [C] using find_good_d_hC C1 hC1
  have hC' : C1 = 1 / (C * 2) := by
    simpa [C] using find_good_d_hC' C1 hC1
  have hC2 : 1 < C2 := by
    dsimp [C2]
    exact find_good_d_hC2 C1
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards
    [ find_good_d_aux1
    , find_good_d_aux2
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (1 : ℝ))
    , eventually_gt_atTop (0 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (16 : ℝ)) ] with
    N haux1 haux2 hlarge hlarge' hlarge'' M k A hAN hzM hMN h1k hkN hAreg q hq hsumq
  dsimp at hlarge
  have hlarge1 : 0 < log N := by
    exact find_good_d_hlarge1 hlarge
  have hlarge2 : 4 * log N ^ (-((3 : ℝ) / 2) + 1) ≤ 1 := by
    exact find_good_d_hlarge2 hlarge1 hlarge''
  let y : ℝ := Real.exp (log N ^ ((1 : ℝ) - 2 / k))
  let u : ℝ := Real.exp (-log N ^ ((1 : ℝ) - 1 / k))
  have h1y : 1 < y := by
    simpa [y] using find_good_d_h1y (N := N) (k := k) hlarge1
  have hyN : y < N := by
    simpa [y] using find_good_d_hyN (N := N) (k := k) hlarge hlarge' h1k
  have h0k : (0 : ℝ) < k := by
    exact find_good_d_h0k h1k
  let D : Finset ℕ :=
    (range (N + 1)).filter
      (fun d : ℕ ↦
        (∀ r : ℕ,
            IsPrimePow r →
              r ∣ d → Nat.Coprime r (d / r) → y < r ∧ r ≤ N) ∧
          M * u < q * d ∧ q * d ≤ N)
  specialize haux2 M k A hAN hzM hMN (le_of_lt h1k) hAreg q hq
  specialize haux1 M u y q A hAN hzM hMN (le_of_lt (Real.exp_pos _))
  let newLocal : ℕ → Finset ℕ := fun d ↦
    (local_part A q).filter (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))
  have hlocal2 : local_part A q ⊆ D.biUnion newLocal := by
    exact find_good_d_hlocal2 (A := A) (q := q) D newLocal rfl haux2
  have hrecbound :
      rec_sum_local A q ≤ D.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hrecbound (A := A) (q := q) D newLocal rfl hlocal2
  have hDu : ∀ d ∈ D, M * u < q * d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2.2.1
  have hDnotzero : ∀ d ∈ D, d ≠ 0 := by
    exact find_good_d_hDnotzero hzM (by simpa [u] using Real.exp_pos _) hDu
  set ω0 : ℝ := (5 / log k) * log (log N) with hω0
  let D1 := D.filter (fun d ↦ ω0 ≤ (ω d : ℝ))
  have hrec2 := hrec1
  specialize hrec1 y k N D1 h1y hyN (le_of_lt h1k)
  have haux1D1 : ∀ d ∈ D1, (((newLocal d).sum (fun n ↦ (q : ℚ) / n) : ℚ) : ℝ) ≤ 2 * log N / d := by
    intro d hd
    exact haux1 d (Finset.mem_of_mem_filter d hd)
  have hrec1bound :
      D1.sum (fun d ↦ (k : ℝ) ^ ω d / d) ≤ (C1 * |log N| / |log y|) ^ k := by
    apply hrec1
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound1 :
      ((D1.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) : ℚ) : ℝ) ≤
        (rec_sum_local A q : ℝ) / 2 := by
    exact
      find_good_d_hbound1 (C1 := C1) (c := c) (y := y) (ω0 := ω0) (N := N) (q := q) (k := k)
        (A := A) (D1 := D1) (newLocal := newLocal) hC1 (by simp [c, C2]) rfl hkN hlarge1
        hlarge2 h1k h0k hω0 hsumq (by
          intro d hd
          exact (Finset.mem_filter.mp hd).2) haux1D1 hrec1bound
  let D2 := D.filter (fun d ↦ (ω d : ℝ) < ω0)
  specialize hrec2 y 1 N D2 h1y hyN (le_rfl : 1 ≤ 1)
  have hrec2bound :
      D2.sum (fun d ↦ (((1 : ℕ) : ℝ) ^ ω d) / d) ≤ (C1 * |log N| / |log y|) ^ 1 := by
    apply hrec2
    intro r hr
    rw [ppowers_in_set, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_filter, Finset.mem_filter] at ha
    rw [Finset.mem_filter] at hr
    exact ha.1.2.1 _ hr.2.1 (Nat.dvd_of_mem_divisors hr.1) hr.2.2
  have hbound2 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (newLocal d).sum (fun n ↦ (q : ℚ) / n)) := by
    exact find_good_d_hbound2 (A := A) (q := q) (D := D) (D1 := D1) (D2 := D2)
      (newLocal := newLocal) rfl rfl hrecbound hbound1
  have hD2notzero : ∀ d ∈ D2, d ≠ 0 := by
    intro d hd
    exact hDnotzero d (Finset.mem_of_mem_filter d hd)
  have hbound3 :
      (rec_sum_local A q : ℚ) / 2 ≤
        D2.sum (fun d ↦ (1 / d : ℚ) * (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n))) := by
    exact find_good_d_hbound3 (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hbound2 hD2notzero
  have hDsumpos : 0 < D2.sum (fun d ↦ (1 / d : ℚ)) := by
    exact find_good_d_hDsumpos (A := A) (q := q) (N := N) (D2 := D2) (newLocal := newLocal)
      hbound3 hD2notzero hlarge1 hsumq
  have hfound0 :
      ∃ x ∈ D2,
        (rec_sum_local A q : ℚ) / 2 ≤
          (D2.sum (fun d ↦ (1 / d : ℚ))) * (newLocal x).sum (fun n ↦ ((q * x : ℚ) / n)) := by
    exact find_good_d_hfound0 (A := A) (q := q) (N := N) (D2 := D2) (newLocal := newLocal)
      hbound3 hlarge1 hsumq
  have hfound :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℚ) / (2 * D2.sum (fun d ↦ (1 / d : ℚ))) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℚ) / n)) := by
    exact find_good_d_hfound (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hfound0 hDsumpos
  have hfound1 :
      ∃ d ∈ D2,
        (rec_sum_local A q : ℝ) / (2 * ((D2.sum (fun d ↦ (1 / d : ℚ))) : ℝ)) ≤
          (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    exact find_good_d_hfound1 (A := A) (q := q) (D2 := D2) (newLocal := newLocal) hfound
  have hbound4 :
      D2.sum (fun d ↦ (1 / d : ℝ)) ≤ log N ^ ((2 : ℝ) / k) / (C * 2) := by
    exact find_good_d_hbound4 (C1 := C1) (C := C) (N := N) (k := k) (y := y) (D2 := D2) hC'
      rfl hlarge1 hrec2bound
  rcases hfound1 with ⟨d, hd, hfound1⟩
  rcases Finset.mem_filter.mp hd with ⟨hdD, hdω⟩
  rcases Finset.mem_filter.mp hdD with ⟨_hdRange, hdProps⟩
  have hfinal :
      C * rec_sum_local A q / log N ^ ((2 : ℝ) / k) ≤
        (newLocal d).sum (fun n ↦ ((q * d : ℝ) / n)) := by
    exact find_good_d_hfinal (C := C) (A := A) (q := q) (N := N) (k := k) (d := d) (D2 := D2)
      (newLocal := newLocal) hC hlarge1 hsumq hDsumpos hfound1 hbound4
  refine ⟨d, ?_, ?_, ?_⟩
  · simpa [u] using hdProps.2.1
  · simpa [hω0] using hdω
  · simpa [newLocal] using hfinal

private theorem find_good_x_hlarge0 {N : ℕ} (hlarge7 : log 2 < log (log (log N))) :
    0 < log (log (log N)) := by
  exact lt_trans (Real.log_pos one_lt_two) hlarge7

private theorem find_good_x_hlarge1 {N : ℕ} (hlarge0 : 0 < log (log (log N)))
    (hlarge4 : 4 * log (log (log N)) ≤ log (log N)) :
    0 < log (log N) := by
  have hpos : 0 < 4 * log (log (log N)) := by positivity
  exact lt_of_lt_of_le hpos hlarge4

private theorem find_good_x_hlarge3 {N : ℕ} (hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N) :
    1 ≤ log N := by
  refine le_trans ?_ hlarge6
  refine one_le_rpow one_le_two ?_
  norm_num

private theorem find_good_x_hlarge2 {N : ℕ} (hlarge3 : 1 ≤ log N) : 0 < log N := by
  exact lt_of_lt_of_le zero_lt_one hlarge3

private theorem find_good_x_h1k {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊)
    (hlarge0 : 0 < log (log (log N))) (_hlarge1 : 0 < log (log N))
    (hlarge4 : 4 * log (log (log N)) ≤ log (log N)) :
    1 < k := by
  have htwo : (2 : ℝ) < (k : ℝ) + 1 := by
    calc
      (2 : ℝ) ≤ (log (log N)) / (2 * log (log (log N))) := by
        rw [_root_.le_div_iff₀ (show 0 < 2 * log (log (log N)) by positivity), ← mul_assoc]
        norm_num
        exact hlarge4
      _ < (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) + 1 := by
        exact_mod_cast Nat.lt_floor_add_one ((log (log N)) / (2 * log (log (log N))))
      _ = (k : ℝ) + 1 := by rw [hk]
  have htwo_nat : 2 < k + 1 := by
    exact_mod_cast htwo
  exact Nat.lt_of_succ_lt_succ htwo_nat

private theorem find_good_x_hkc {N k : ℕ} {c : ℝ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (hc : 0 < c)
    (hlarge5 : 1 / c / 2 ≤ log (log (log N))) (hlarge0 : 0 < log (log (log N)))
    (hlarge1 : 0 < log (log N)) :
    (k : ℝ) ≤ c * log (log N) := by
  calc
    (k : ℝ) = (⌊(log (log N)) / (2 * log (log (log N)))⌋₊ : ℝ) := by rw [hk]
    _ ≤ (log (log N)) / (2 * log (log (log N))) := by
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        positivity)
    _ ≤ c * log (log N) := by
      have haux : 1 / c ≤ 2 * log (log (log N)) := by
        have hmul := mul_le_mul_of_nonneg_left hlarge5 (show (0 : ℝ) ≤ 2 by positivity)
        calc
          1 / c = 2 * (1 / c / 2) := by ring
          _ ≤ 2 * log (log (log N)) := hmul
      have hinv : 1 / (2 * log (log (log N))) ≤ c := by
        exact (one_div_le (show 0 < 2 * log (log (log N)) by positivity) hc).2 haux
      rw [div_eq_mul_one_div, mul_comm c]
      exact mul_le_mul_of_nonneg_left hinv (le_of_lt hlarge1)

private theorem find_good_x_hlogNk {N k : ℕ}
    (hk : k = ⌊(log (log N)) / (2 * log (log (log N)))⌋₊) (h1k : 1 < k)
    (hlarge7 : log 2 < log (log (log N))) (hlarge1 : 0 < log (log N))
    (hlarge2 : 0 < log N) (hlarge3 : 1 ≤ log N) :
    2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
  have hlarge0 : 0 < log (log (log N)) := by
    exact lt_trans (Real.log_pos one_lt_two) hlarge7
  let u : ℝ := log (log (log N)) / log (log N)
  have hpowpos : 0 < log N ^ u := by
    exact Real.rpow_pos_of_pos hlarge2 _
  have hmid : (2 : ℝ) < log N ^ u := by
    rw [← Real.log_lt_log_iff zero_lt_two hpowpos, Real.log_rpow hlarge2]
    dsimp [u]
    have hmul :
        log (log (log N)) / log (log N) * log (log N) = log (log (log N)) := by
      field_simp [ne_of_gt hlarge1]
    rw [hmul]
    exact hlarge7
  have hlt2 : 2 * log N ^ u < log N ^ (2 * u) := by
    calc
      2 * log N ^ u < log N ^ u * log N ^ u := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
          mul_lt_mul_of_pos_right hmid hpowpos
      _ = log N ^ (u + u) := by
        rw [← Real.rpow_add hlarge2]
      _ = log N ^ (2 * u) := by ring_nf
  have hexp_le : 2 * log (log (log N)) / log (log N) ≤ (1 : ℝ) / k := by
    rw [le_one_div (show 0 < 2 * log (log (log N)) / log (log N) by
      refine div_pos ?_ hlarge1
      exact mul_pos zero_lt_two hlarge0)]
    · rw [one_div_div]
      rw [hk]
      exact Nat.floor_le (by
        refine div_nonneg (le_of_lt hlarge1) ?_
        exact mul_nonneg zero_le_two (le_of_lt hlarge0))
    · exact_mod_cast (lt_trans zero_lt_one h1k)
  have hu_eq : log N ^ u = log (log N) := by
    calc
      log N ^ u = Real.exp (Real.log (log N) * u) := by
        rw [Real.rpow_def_of_pos hlarge2]
      _ = Real.exp (log (log (log N))) := by
        dsimp [u]
        congr 1
        field_simp [ne_of_gt hlarge1]
      _ = log (log N) := by
        rw [Real.exp_log hlarge1]
  have hu2_eq : 2 * u = 2 * log (log (log N)) / log (log N) := by
    dsimp [u]
    field_simp [ne_of_gt hlarge1]
  calc
    2 * log (log N) = 2 * (log N ^ u) := by rw [hu_eq]
    _ < log N ^ (2 * u) := hlt2
    _ = log N ^ (2 * log (log (log N)) / log (log N)) := by rw [hu2_eq]
    _ ≤ log N ^ ((1 : ℝ) / k) := by
      exact Real.rpow_le_rpow_of_exponent_le hlarge3 hexp_le

private theorem find_good_x_hA_I {N : ℕ} {A : Finset ℕ} {I : Finset ℤ}
    (hA : A ⊆ range (N + 1)) :
    A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x) ⊆ range (N + 1) := by
  exact subset_trans (Finset.filter_subset _ _) hA

private theorem find_good_x_hA_I' {N k : ℕ} {M : ℝ} {A : Finset ℕ} {I : Finset ℤ}
    {A_I : Finset ℕ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hMA : ∀ n ∈ A, M ≤ (n : ℝ)) (hreg : arith_regular N A)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
  intro n hn
  rw [hA_I_def] at hn
  refine ⟨hMA n (Finset.mem_of_mem_filter n hn), ?_⟩
  rw [arith_regular] at hreg
  exact lt_of_le_of_lt (hreg n (Finset.mem_of_mem_filter n hn)).2 hlogNk

private theorem find_good_x_hqA_I {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hq : q ∈ ppowers_in_set A) (_h0A : 0 ∉ A)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge2 : 0 < log N) :
    q ∈ ppowers_in_set A_I := by
  rcases mem_ppowers_in_set.mp hq with ⟨hqpp, _⟩
  refine mem_ppowers_in_set.mpr ⟨hqpp, ?_⟩
  by_contra hlocalempty
  rw [Finset.not_nonempty_iff_eq_empty] at hlocalempty
  rw [rec_sum_local, hlocalempty, Finset.sum_empty, Rat.cast_zero] at hqlocal
  have hpos : 0 < (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) := by
    refine one_div_pos.mpr ?_
    positivity
  linarith

private theorem find_good_x_hqlocal2 {N q : ℕ} {A : Finset ℕ} {I : Finset ℤ} {A_I : Finset ℕ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x))
    (hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N) (hlarge2 : 0 < log N)
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q) :
    1 / log N ≤ rec_sum_local A_I q := by
  have hpow99 : (2 : ℝ) ≤ log N ^ ((99 : ℝ) / 100) := by
    have hpow99' : (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) ≤ log N ^ ((99 : ℝ) / 100) := by
      exact Real.rpow_le_rpow (by positivity) hlarge6 (by positivity)
    calc
      (2 : ℝ) = (2 ^ ((100 : ℝ) / 99) : ℝ) ^ ((99 : ℝ) / 100) := by
        rw [← Real.rpow_mul zero_le_two]
        norm_num
      _ ≤ log N ^ ((99 : ℝ) / 100) := hpow99'
  have hden : 2 * log N ^ ((1 : ℝ) / 100) ≤ log N := by
    calc
      2 * log N ^ ((1 : ℝ) / 100)
          ≤ log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100) := by
            exact mul_le_mul_of_nonneg_right hpow99 (by positivity)
      _ = log N := by
        calc
          log N ^ ((99 : ℝ) / 100) * log N ^ ((1 : ℝ) / 100)
              = log N ^ (((99 : ℝ) / 100) + ((1 : ℝ) / 100)) := by
                  rw [← Real.rpow_add hlarge2]
          _ = log N := by
            norm_num [Real.rpow_one]
  have hdenpos : 0 < 2 * log N ^ ((1 : ℝ) / 100) := by positivity
  exact le_trans (one_div_le_one_div_of_le hdenpos hden) hqlocal

private theorem find_good_x_hsum {N q k d : ℕ} {M C : ℝ} {A A_I A_I' A_I'' : Finset ℕ}
    {I : Finset ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hA_I : A_I ⊆ range (N + 1)) (hA_I_subA : A_I ⊆ A) (hq : q ∈ ppowers_in_set A)
    (h0A : 0 ∉ A) (hC : 0 < C)
    (hreg : arith_regular N A)
    (hlargerecbound :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤ rec_sum A_I'' →
        (∀ n ∈ A_I'', (1 - 2 / 99) * log (log N) ≤ ω n ∧ ((ω n : ℝ) ≤ 2 * log (log N))) →
          (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
            (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k))
    (hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N))
    (hgood2 : (ω d : ℝ) < (5 / log k) * log (log N))
    (hgood3 :
      C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) ≤
        ((local_part A_I q).filter
            (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
          (fun n ↦ (q * d / n : ℝ)))
    (hqlocal : 1 / (2 * log N ^ ((1 : ℝ) / 100)) ≤ rec_sum_local A_I q)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N) :
    ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
  let _ := M
  let _ := I
  have hqpp : IsPrimePow q := (mem_ppowers_in_set.mp hq).1
  have hmain :
      (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) ≤
        (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    refine hlargerecbound ?_ ?_
    · calc
        log N ^ (-((2 : ℝ) / 99) / 2)
            ≤ C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := hlogNk2
        _ ≤ C * rec_sum_local A_I q / log N ^ ((2 : ℝ) / k) := by
          have hmul : C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) ≤ C * rec_sum_local A_I q := by
            exact mul_le_mul_of_nonneg_left hqlocal (le_of_lt hC)
          exact div_le_div_of_nonneg_right hmul (by
            exact Real.rpow_nonneg (le_of_lt hlarge2) ((2 : ℝ) / k))
        _ ≤
            ((local_part A_I q).filter
                (fun n ↦ q * d ∣ n ∧ Nat.Coprime (q * d) (n / (q * d)))).sum
              (fun n ↦ (q * d / n : ℝ)) := hgood3
        _ ≤ rec_sum A_I'' := by
          rw [rec_sum, Rat.cast_sum]
          push_cast
          let g : ℕ → ℕ := fun n ↦ n / (q * d)
          refine sum_le_sum_of_inj g ?_ ?_ ?_ ?_
          · intro b hb
            exact one_div_nonneg.2 (Nat.cast_nonneg b)
          · intro a ha
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            rw [hA_I''_def, Finset.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Finset.mem_range]
              exact lt_of_le_of_lt (Nat.div_le_self a (q * d))
                (Finset.mem_range.mp (hA_I ha_local.1))
            · refine ⟨a, ?_, ?_, ?_⟩
              · rw [hA_I'_def, Finset.mem_filter]
                exact ⟨ha_local.1, ha'.2.1⟩
              · dsimp [g]
                exact Nat.div_mul_cancel ha'.2.1
              · simpa [g, Nat.coprime_comm] using ha'.2.2
          · intro a ha b hb hab
            have ha' := Finset.mem_filter.mp ha
            have hb' := Finset.mem_filter.mp hb
            calc
              a = (q * d) * g a := by
                simp [g, Nat.mul_div_cancel' ha'.2.1]
              _ = (q * d) * g b := by rw [hab]
              _ = b := by
                simp [g, Nat.mul_div_cancel' hb'.2.1]
          · intro a ha
            have ha' := Finset.mem_filter.mp ha
            have ha_local := Finset.mem_filter.mp ha'.1
            have haA : a ∈ A := hA_I_subA ha_local.1
            have ha0 : a ≠ 0 := by
              intro hzero
              exact h0A (hzero ▸ haA)
            have hqd0 : q * d ≠ 0 := by
              intro hzero
              have : a = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ ha'.2.1)
              exact ha0 this
            have hqd0' : ((q * d : ℕ) : ℝ) ≠ 0 := by
              exact_mod_cast hqd0
            have hcast : (g a : ℝ) = (a : ℝ) / (q * d : ℕ) := by
              dsimp [g]
              rw [Nat.cast_div ha'.2.1 hqd0']
            rw [hcast, one_div_div, Nat.cast_mul]
    · intro n hn
      rw [hA_I''_def, Finset.mem_filter] at hn
      rcases hn.2 with ⟨m, hm1, hm2, hm3⟩
      rw [hA_I'_def, Finset.mem_filter] at hm1
      have hmA : m ∈ A := hA_I_subA hm1.1
      have hm0 : m ≠ 0 := by
        intro hzero
        exact h0A (hzero ▸ hmA)
      have hqdpos : 0 < q * d := by
        refine Nat.pos_iff_ne_zero.mpr ?_
        intro hzero
        have : m = 0 := Nat.eq_zero_of_zero_dvd (hzero ▸ hm1.2)
        exact hm0 this
      have hmdiv : m / (q * d) = n := by
        apply Nat.div_eq_of_eq_mul_right hqdpos
        simpa [mul_comm] using hm2.symm
      have hmreg := hreg m hmA
      refine ⟨?_, ?_⟩
      · calc
          (1 - 2 / 99) * log (log N) ≤ (ω m : ℝ) - (1 + 5 / log k * log (log N)) := by
            rw [le_sub_iff_add_le]
            exact le_trans hNlogk hmreg.1
          _ ≤ (ω m : ℝ) - ω (q * d) := by
            apply sub_le_sub_left
            calc
              (ω (q * d) : ℝ) ≤ 1 + (ω d : ℝ) := by
                exact_mod_cast omega_mul_ppower (a := d) hqpp
              _ ≤ 1 + (5 / log k) * log (log N) := by
                linarith [le_of_lt hgood2]
          _ ≤ ω (m / (q * d)) := sub_le_omega_div hm1.2
          _ = ω n := by rw [hmdiv]
      · calc
          (ω n : ℝ) = ω (m / (q * d)) := by rw [← hmdiv]
          _ ≤ ω m := by exact_mod_cast omega_div_le hm1.2
          _ ≤ 2 * log (log N) := hmreg.2
  calc
    ((35 : ℝ) / 100) * log (log N)
        ≤ (1 - 2 * (2 / 99)) * Real.exp (-1) * log (log N) := by
          have hmul := mul_le_mul_of_nonneg_right useful_exp_estimate (le_of_lt hlarge1)
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    _ ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := hmain

private theorem find_good_x_hI'ne {N q d : ℕ} {A_I' A_I'' : Finset ℕ} {I I' : Finset ℤ}
    (hA_I'_witness : ∀ n ∈ A_I', ∃ x ∈ I, (n : ℤ) ∣ x)
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x))
    (hsum : ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hlarge1 : 0 < log (log N)) :
    I'.Nonempty := by
  rw [hI'_def, Finset.filter_nonempty_iff]
  have hA_I'_ne : A_I'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hem
    rw [Finset.eq_empty_iff_forall_notMem] at hem
    have hA_I''_empty : A_I'' = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro h
      rw [hA_I''_def, Finset.filter_nonempty_iff] at h
      rcases h with ⟨a, ha1, n, hn1, hn2⟩
      exact hem n hn1
    have hpp_empty : ppowers_in_set A_I'' = ∅ := by
      rw [hA_I''_empty]
      exact ppowers_in_set_empty
    rw [hpp_empty, Finset.sum_empty, ← not_lt] at hsum
    have hpos : 0 < ((35 : ℝ) / 100) * log (log N) := by positivity
    exact (hsum hpos).elim
  obtain ⟨n, hn⟩ := hA_I'_ne
  rcases hA_I'_witness n hn with ⟨x, hxI, hnx⟩
  exact ⟨x, hxI, n, hn, hnx⟩

private theorem find_good_x_hI'single {N q k d : ℕ} {M t : ℝ} {A A_I A_I' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (_hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') (hI :
      I =
        Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
          ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋)
    (h0M : 0 < M) (hMN : M ≤ N) (_h0A : 0 ∉ A)
    (hgood1 : M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) < q * d)
    (hlarge1 : 0 < log (log N)) (hlarge2 : 0 < log N)
    (hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k)) :
    ∀ y ∈ I', x = y := by
  intro y hy
  by_contra hxy
  have hx' := hx
  rw [hI'_def, Finset.mem_filter] at hx'
  rcases hx'.2 with ⟨mx, hmx, hmx'⟩
  have hmxqd : ((q * d : ℤ) ∣ (mx : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmx
    exact_mod_cast hmx.2
  have hdx : ((q * d : ℤ) ∣ x) := dvd_trans hmxqd hmx'
  have hy' := hy
  rw [hI'_def, Finset.mem_filter] at hy'
  rcases hy'.2 with ⟨my, hmy, hmy'⟩
  have hmyqd : ((q * d : ℤ) ∣ (my : ℤ)) := by
    rw [hA_I'_def, Finset.mem_filter] at hmy
    exact_mod_cast hmy.2
  have hdy : ((q * d : ℤ) ∣ y) := dvd_trans hmyqd hmy'
  let z : ℤ := |x - y|
  have hdz : ((q * d : ℤ) ∣ z) := by
    dsimp [z]
    rw [dvd_abs]
    exact dvd_sub hdx hdy
  have hzs :
      (z : ℝ) ≤ (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by
    let w : ℝ := M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))
    let b : ℤ := ⌊t + w / 2⌋
    let a : ℤ := ⌈t - w / 2⌉
    have hIab : I = Icc a b := by
      simpa [a, b, w] using hI
    have hIx : x ∈ Icc a b := by
      simpa [hIab] using hx'.1
    have hIy : y ∈ Icc a b := by
      simpa [hIab] using hy'.1
    calc
      (z : ℝ) ≤ b - a := by
        simpa [z, Int.cast_abs] using (two_in_Icc hIx hIy)
      _ ≤ w / 2 + w / 2 := by
        simpa [a, b, w] using (floor_sub_ceil (z := t) (x := w / 2) (y := w / 2))
      _ = w := by ring
      _ = (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) := by rfl
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le h0M hMN
  have hpow_bound :
      (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    calc
      (N : ℝ) ^ (-(2 : ℝ) / log (log N))
          = Real.exp (log N * (-(2 : ℝ) / log (log N))) := by
              rw [Real.exp_mul, Real.exp_log hNpos]
      _ ≤ Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
        refine Real.exp_le_exp.mpr ?_
        have hloglog_bound : log (log N) ≤ 2 * log N ^ ((1 : ℝ) / k) := by
          have haux1 : log (log N) ≤ 2 * log (log N) := by linarith
          have haux2 : log (log N) ≤ log N ^ ((1 : ℝ) / k) := by
            exact le_trans haux1 (le_of_lt hlogNk)
          linarith
        have hdiv : 1 ≤ 2 * log N ^ ((1 : ℝ) / k) / log (log N) := by
          rw [le_div_iff₀ hlarge1]
          simpa using hloglog_bound
        have hsplit : log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k) = log N := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k)
                = log N ^ (((1 : ℝ) - 1 / k) + ((1 : ℝ) / k)) := by
                    rw [← Real.rpow_add hlarge2]
            _ = log N ^ (1 : ℝ) := by ring_nf
            _ = log N := by rw [Real.rpow_one]
        have hpow_main :
            log N ^ ((1 : ℝ) - 1 / k) ≤ 2 * log N / log (log N) := by
          calc
            log N ^ ((1 : ℝ) - 1 / k) ≤
                log N ^ ((1 : ℝ) - 1 / k) * (2 * log N ^ ((1 : ℝ) / k) / log (log N)) := by
                  exact le_mul_of_one_le_right (by positivity) hdiv
            _ = (2 * (log N ^ ((1 : ℝ) - 1 / k) * log N ^ ((1 : ℝ) / k))) / log (log N) := by ring
            _ = 2 * log N / log (log N) := by rw [hsplit]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using neg_le_neg hpow_main
  have hwidth_bound :
      M * (N : ℝ) ^ (-(2 : ℝ) / log (log N)) ≤
        M * Real.exp (-log N ^ ((1 : ℝ) - 1 / k)) := by
    exact mul_le_mul_of_nonneg_left hpow_bound (le_of_lt h0M)
  have hzpos : 0 < z := by
    dsimp [z]
    exact abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hqdlez : ((q * d : ℤ)) ≤ z := by
    have hqdleabs : ((q * d : ℤ)) ≤ |z| := Int.le_abs_of_dvd (ne_of_gt hzpos) hdz
    simpa [abs_of_nonneg (le_of_lt hzpos)] using hqdleabs
  have hqdz : (q : ℝ) * d ≤ z := by
    exact_mod_cast hqdlez
  exact (not_le_of_gt hgood1) (le_trans hqdz (le_trans hzs hwidth_bound))

private theorem find_good_x_hxI {A_I' : Finset ℕ} {I I' : Finset ℤ} {x : ℤ}
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') :
    x ∈ I := by
  rw [hI'_def] at hx
  exact Finset.mem_of_mem_filter x hx

private theorem find_good_x_hqx {q d : ℕ} {A_I A_I' : Finset ℕ} {I I' : Finset ℤ} {x : ℤ}
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (hx : x ∈ I') :
    (q : ℤ) ∣ x := by
  rw [hI'_def] at hx
  rcases (Finset.mem_filter.mp hx).2 with ⟨n, hn, hnx⟩
  rw [hA_I'_def] at hn
  have hqdvdqd : (q : ℤ) ∣ (q * d : ℤ) := ⟨d, by simp⟩
  have hqdvdn_nat : q * d ∣ n := (Finset.mem_filter.mp hn).2
  have hqdvdn : ((q * d : ℤ) ∣ (n : ℤ)) := by
    rcases hqdvdn_nat with ⟨m, rfl⟩
    refine ⟨m, by simp [mul_assoc, mul_left_comm, mul_comm]⟩
  exact dvd_trans hqdvdqd (dvd_trans hqdvdn hnx)

private theorem find_good_x_hpp {N q d : ℕ} {A A_I A_I' A_I'' : Finset ℕ}
    {I I' : Finset ℤ} {x : ℤ}
    (hA_I_def : A_I = A.filter (fun n : ℕ ↦ ∃ z ∈ I, (n : ℤ) ∣ z))
    (hA_I'_def : A_I' = A_I.filter (fun n : ℕ ↦ q * d ∣ n))
    (hA_I''_def :
      A_I'' =
        (range (N + 1)).filter
          (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)))
    (hI'_def : I' = I.filter (fun z : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ z))
    (_hx : x ∈ I') (h0A : 0 ∉ A) (hI'single : ∀ y ∈ I', x = y) :
    ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
  intro r hr
  rw [ppowers_in_set, Finset.mem_biUnion] at hr
  rcases hr with ⟨a, ha, hr⟩
  rw [Finset.mem_filter] at hr
  rw [hA_I''_def] at ha
  rw [Finset.mem_filter]
  rw [Finset.mem_filter] at ha
  rcases ha.2 with ⟨m, hm1, hm2⟩
  have hm1' := hm1
  rw [hA_I'_def, Finset.mem_filter] at hm1
  rw [hA_I_def, Finset.mem_filter] at hm1
  rcases hm1.1.2 with ⟨y, hy1, hy2⟩
  have hyI' : y ∈ I' := by
    rw [hI'_def, Finset.mem_filter]
    exact ⟨hy1, m, hm1', hy2⟩
  have hyx : x = y := hI'single y hyI'
  rw [hyx, ppowers_in_set, Finset.mem_biUnion]
  refine ⟨?_, ?_⟩
  · refine ⟨m, hm1.1.1, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hr.2.1, ?_⟩
    · rw [Nat.mem_divisors]
      refine ⟨?_, ?_⟩
      · rw [← hm2.1]
        exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
      · intro h0m
        rw [h0m] at hm1
        exact h0A hm1.1.1
    · rw [← hm2.1, mul_comm, Nat.mul_div_assoc]
      · refine Nat.Coprime.mul_right ?_ hr.2.2
        exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hr.1) hm2.2
      · exact Nat.dvd_of_mem_divisors hr.1
  · refine dvd_trans ?_ hy2
    have hrdvdm : r ∣ m := by
      rw [← hm2.1]
      exact dvd_trans (Nat.dvd_of_mem_divisors hr.1) (dvd_mul_right a (q * d))
    exact_mod_cast hrdvdm

private theorem find_good_x_hfinal {N : ℕ} {A A_I'' : Finset ℕ} {x : ℤ}
    (hsum : ((35 : ℝ) / 100) * log (log N) ≤
      (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)))
    (hpp : ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)) :
    ((35 : ℝ) / 100) * log (log N) ≤
      ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)).sum (fun r ↦ (1 / r : ℝ)) := by
  exact le_trans hsum <|
    Finset.sum_le_sum_of_subset_of_nonneg hpp (by
      intro i _ _
      positivity)

theorem find_good_x :
    ∀ᶠ N : ℕ in atTop,
      ∀ M : ℝ,
        ∀ A ⊆ range (N + 1),
          0 < M →
            M ≤ N →
              0 ∉ A →
                (∀ n ∈ A, M ≤ (n : ℝ)) →
                  arith_regular N A →
                    ∀ t : ℝ, ∀ I : Finset ℤ, ∀ q ∈ ppowers_in_set A,
                      I =
                          Icc ⌈t - (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌉
                            ⌊t + (M * (N : ℝ) ^ (-(2 : ℝ) / log (log N))) / 2⌋ →
                        (1 : ℝ) / (2 * log N ^ ((1 : ℝ) / 100)) ≤
                            rec_sum_local (A.filter (fun n ↦ ∃ x ∈ I, (n : ℤ) ∣ x)) q →
                          ∃ xq, xq ∈ I ∧ (q : ℤ) ∣ xq ∧
                              ((35 : ℝ) / 100) * log (log N) ≤
                                ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ xq)).sum
                                  (fun r : ℕ ↦ (1 / r : ℝ)) := by
  classical
  obtain ⟨c, C, hc, hC, hgoodd⟩ := find_good_d
  have heasy1 : 0 < ((2 : ℝ) / 99) := by
    norm_num
  have heasy2 : ((2 : ℝ) / 99) < 1 / 2 := by
    norm_num
  obtain hlargerecbound := rec_qsum_lower_bound ((2 : ℝ) / 99) heasy1 heasy2
  filter_upwards [hgoodd, hlargerecbound, another_large_N c C hc hC] with
    N hgooddN hlargerecbound hlargegroup M A hA h0M hMN h0A hMA hreg t I q hq hI hqlocal
  have hlarge4 : 4 * log (log (log N)) ≤ log (log N) := by
    exact hlargegroup.2.2.1
  have hlarge5 : 1 / c / 2 ≤ log (log (log N)) := by
    exact hlargegroup.1
  have hlarge6 : 2 ^ ((100 : ℝ) / 99) ≤ log N := by
    exact hlargegroup.2.1
  have hlarge7 : log 2 < log (log (log N)) := by
    exact hlargegroup.2.2.2.1
  have hlarge0 : 0 < log (log (log N)) := by
    exact find_good_x_hlarge0 hlarge7
  have hlarge1 : 0 < log (log N) := by
    exact find_good_x_hlarge1 hlarge0 hlarge4
  have hlarge3 : 1 ≤ log N := by
    exact find_good_x_hlarge3 hlarge6
  have hlarge2 : 0 < log N := by
    exact find_good_x_hlarge2 hlarge3
  set A_I : Finset ℕ := A.filter (fun n : ℕ ↦ ∃ x ∈ I, (n : ℤ) ∣ x) with hA_I_def
  set k : ℕ := ⌊(log (log N)) / (2 * log (log (log N)))⌋₊ with hk
  have h1k : 1 < k := by
    simpa [hk] using find_good_x_h1k (N := N) (k := k) hk hlarge0 hlarge1 hlarge4
  have hkc : (k : ℝ) ≤ c * log (log N) := by
    simpa [hk] using find_good_x_hkc (N := N) (k := k) (c := c) hk hc hlarge5 hlarge0 hlarge1
  have hlogNk : 2 * log (log N) < log N ^ ((1 : ℝ) / k) := by
    simpa [hk] using find_good_x_hlogNk (N := N) (k := k) hk h1k hlarge7 hlarge1 hlarge2 hlarge3
  have hlogNk2 :
      log N ^ (-((2 : ℝ) / 99) / 2) ≤
        C * (1 / (2 * log N ^ ((1 : ℝ) / 100))) / log N ^ ((2 : ℝ) / k) := by
    simpa [hk] using hlargegroup.2.2.2.2.1
  have hNlogk :
      (1 - 2 / 99) * log (log N) + (1 + 5 / log k * log (log N)) ≤
        (99 / 100 : ℝ) * log (log N) := by
    simpa [hk] using hlargegroup.2.2.2.2.2
  have hA_I : A_I ⊆ range (N + 1) := by
    simpa [hA_I_def] using find_good_x_hA_I (N := N) (A := A) (I := I) hA
  have hA_I' : ∀ n ∈ A_I, M ≤ (n : ℝ) ∧ ((ω n : ℝ) < log N ^ ((1 : ℝ) / k)) := by
    simpa [hA_I_def] using
      find_good_x_hA_I' (N := N) (k := k) (M := M) (A := A) (I := I) (A_I := A_I) hA_I_def
        hMA hreg hlogNk
  have hqA_I : q ∈ ppowers_in_set A_I := by
    simpa [hA_I_def] using
      find_good_x_hqA_I (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def hq h0A
        hqlocal hlarge2
  have hqlocal2 : 1 / log N ≤ rec_sum_local A_I q := by
    simpa [hA_I_def] using
      find_good_x_hqlocal2 (N := N) (q := q) (A := A) (I := I) (A_I := A_I) hA_I_def
        hlarge6 hlarge2 hqlocal
  specialize hgooddN M k A_I hA_I h0M hMN h1k hkc hA_I' q hqA_I hqlocal2
  rcases hgooddN with ⟨d, hgood1, hgood2, hgood3⟩
  set A_I' : Finset ℕ := A_I.filter (fun n : ℕ ↦ q * d ∣ n) with hA_I'_def
  set A_I'' : Finset ℕ :=
    (range (N + 1)).filter
      (fun m : ℕ ↦ ∃ n ∈ A_I', m * (q * d) = n ∧ Nat.Coprime m (q * d)) with hA_I''_def
  have hsum :
      ((35 : ℝ) / 100) * log (log N) ≤ (ppowers_in_set A_I'').sum (fun r ↦ (1 / r : ℝ)) := by
    exact
      find_good_x_hsum (N := N) (q := q) (k := k) (d := d) (M := M) (C := C) (A := A)
        (A_I := A_I) (A_I' := A_I') (A_I'' := A_I'') (I := I) hA_I'_def hA_I''_def hA_I
        (by
          intro n hn
          rw [hA_I_def, Finset.mem_filter] at hn
          exact hn.1)
        hq
        h0A hC hreg
        (by
          intro hrec hreg'
          exact hlargerecbound A_I'' hrec hreg')
        hlogNk2 hNlogk hgood2 hgood3 hqlocal hlarge1 hlarge2
  set I' : Finset ℤ := I.filter (fun x : ℤ ↦ ∃ n ∈ A_I', (n : ℤ) ∣ x) with hI'_def
  have hI'ne : I'.Nonempty := by
    exact
      find_good_x_hI'ne (N := N) (q := q) (d := d) (A_I' := A_I') (A_I'' := A_I'')
        (I := I) (I' := I') (by
          intro n hn
          rw [hA_I'_def, Finset.mem_filter] at hn
          rcases (Finset.mem_filter.mp hn.1).2 with ⟨x, hxI, hnx⟩
          exact ⟨x, hxI, hnx⟩) hA_I''_def hI'_def hsum hlarge1
  obtain ⟨x, hx⟩ := hI'ne
  have hI'single : ∀ y ∈ I', x = y := by
    exact
      find_good_x_hI'single (N := N) (q := q) (k := k) (d := d) (M := M) (t := t) (A := A)
        (A_I := A_I) (A_I' := A_I') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hI'_def
        hx hI h0M hMN h0A hgood1 hlarge1 hlarge2 hlogNk
  have hxI : x ∈ I := by
    exact find_good_x_hxI (A_I' := A_I') (I := I) (I' := I') (x := x) hI'_def hx
  have hqx : (q : ℤ) ∣ x := by
    exact find_good_x_hqx (q := q) (d := d) (A_I := A_I) (A_I' := A_I') (I := I) (I' := I')
      (x := x) hA_I'_def hI'_def hx
  have hpp :
      ppowers_in_set A_I'' ⊆ (ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x) := by
    exact
      find_good_x_hpp (N := N) (q := q) (d := d) (A := A) (A_I := A_I) (A_I' := A_I')
        (A_I'' := A_I'') (I := I) (I' := I') (x := x) hA_I_def hA_I'_def hA_I''_def hI'_def
        hx h0A hI'single
  have hfinal :
      ((35 : ℝ) / 100) * log (log N) ≤
        ((ppowers_in_set A).filter (fun n : ℕ ↦ (n : ℤ) ∣ x)).sum (fun r ↦ (1 / r : ℝ)) := by
    exact find_good_x_hfinal (N := N) (A := A) (A_I'' := A_I'') (x := x) hsum hpp
  exact ⟨x, hxI, hqx, hfinal⟩

end

end UnitFractions
