/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Combinatorics.Hall.Basic
import ErdosProblems.Erdos387.AnalyticInputs

/-!
# The fixed-parameter BNPZ covering lemma

Ported from the public `slavanaprienko/erdos-387` formalization and adapted to
the axiom-free `Erdos387.ANT.PNT_fixed_modulus` proved in
`AnalyticInputs.lean`.  The original two local heartbeat increases are not
used: this module checks under the repository's default limits.
-/

namespace Erdos387

def primesLT (m : ℕ) : Finset ℕ := (Finset.range m).filter Nat.Prime

lemma mem_primesLT {p m : ℕ} : p ∈ primesLT m ↔ p < m ∧ p.Prime := by
  simp [primesLT]

def smoothFinset (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 k).filter (fun n => n.primeFactors ⊆ P)

lemma smoothFinset_card_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (k : ℕ) :
    (smoothFinset P k).card ≤ ∏ p ∈ P, (Nat.log p k + 1) := by
  classical
  by_cases hk : k = 0
  · subst hk
    simp [smoothFinset]
  let T : Finset (P → ℕ) :=
    Fintype.piFinset (fun p : P => Finset.range (Nat.log p.1 k + 1))
  have hTcard : T.card = ∏ p ∈ P, (Nat.log p k + 1) := by
    change (Fintype.piFinset _).card = _
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Finset.prod_attach P (fun p => Nat.log p k + 1)
  refine (Finset.card_le_card_of_injOn
    (fun n => fun p : P => n.factorization p.1) ?_ ?_).trans hTcard.le
  · intro n hn
    rw [Finset.mem_coe] at hn
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have ⟨hnk, _⟩ := Finset.mem_filter.mp hn
    have ⟨h1, hk'⟩ := Finset.mem_Icc.mp hnk
    have hp : p.1.Prime := hP _ p.2
    rw [Nat.le_log_iff_pow_le hp.one_lt hk]
    calc p.1 ^ n.factorization p.1
        ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p.1)
      _ ≤ k := hk'
  · intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have ⟨hna, hapf⟩ := Finset.mem_filter.mp ha
    have ⟨hnb, hbpf⟩ := Finset.mem_filter.mp hb
    have ha1 := (Finset.mem_Icc.mp hna).1
    have hb1 := (Finset.mem_Icc.mp hnb).1
    refine Nat.eq_of_factorization_eq (by omega) (by omega) (fun p => ?_)
    by_cases hpP : p ∈ P
    · exact congr_fun hab ⟨p, hpP⟩
    by_cases hpprime : p.Prime
    · have ha0 : a.factorization p = 0 :=
        (Nat.factorization_eq_zero_iff a p).mpr <| Or.inr <| Or.inl fun hdvd =>
          hpP (hapf (Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, by omega⟩))
      have hb0 : b.factorization p = 0 :=
        (Nat.factorization_eq_zero_iff b p).mpr <| Or.inr <| Or.inl fun hdvd =>
          hpP (hbpf (Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, by omega⟩))
      rw [ha0, hb0]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hpprime,
          Nat.factorization_eq_zero_of_not_prime _ hpprime]

noncomputable def piAP (x : ℝ) (q a : ℕ) : ℕ :=
  ((Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n.Prime ∧ n % q = a % q)).card

private lemma bad_count_le (P : Finset ℕ) (X R : ℕ) :
    ((smoothFinset P (2 * X)).biUnion (fun t => Finset.Ico t (t + 2 * R))).card ≤
      (smoothFinset P (2 * X)).card * (2 * R) := by
  classical
  calc ((smoothFinset P (2 * X)).biUnion (fun t => Finset.Ico t (t + 2 * R))).card
      ≤ ∑ t ∈ smoothFinset P (2 * X), (Finset.Ico t (t + 2 * R)).card :=
        Finset.card_biUnion_le
    _ = ∑ _t ∈ smoothFinset P (2 * X), 2 * R := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Nat.card_Ico]; omega
    _ = (smoothFinset P (2 * X)).card * (2 * R) := by
        rw [Finset.sum_const, smul_eq_mul]

private lemma Acount_le_R (q R k : ℕ) :
    ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card ≤ R := by
  calc ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card
      ≤ (Finset.Ioc (k - R) k).card := Finset.card_filter_le _ _
    _ ≤ R := by rw [Nat.card_Ioc]; omega

private lemma exists_good_large_A {K Bad : Finset ℕ} {A : ℕ → ℕ} {H : ℕ}
    (hH : 1 ≤ H) (hKne : K.Nonempty) (hBadSub : Bad ⊆ K)
    (hTotal : 8 * H * K.card ≤ ∑ k ∈ K, A k)
    (hBad : ∑ k ∈ Bad, A k ≤ H * K.card) :
    ∃ k ∈ K, k ∉ Bad ∧ 2 * H ≤ A k := by
  classical
  by_contra h_not
  rw [not_exists] at h_not
  have h_not' : ∀ k ∈ K, k ∉ Bad → A k < 2 * H := by
    intro k hkK hkBad
    have := h_not k
    rw [not_and, not_and, not_le] at this
    exact this hkK hkBad
  have h_split : ∑ k ∈ K, A k = ∑ k ∈ Bad, A k + ∑ k ∈ K \ Bad, A k := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    rw [Finset.union_sdiff_of_subset hBadSub]
  have h_good_bound : ∀ k ∈ K \ Bad, A k ≤ 2 * H - 1 := by
    intro k hk
    rw [Finset.mem_sdiff] at hk
    have h_lt : A k < 2 * H := h_not' k hk.1 hk.2
    omega
  have h_good_sum : ∑ k ∈ K \ Bad, A k ≤ (2 * H - 1) * (K \ Bad).card := by
    calc ∑ k ∈ K \ Bad, A k
        ≤ ∑ _k ∈ K \ Bad, (2 * H - 1) := Finset.sum_le_sum h_good_bound
      _ = (K \ Bad).card * (2 * H - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * H - 1) * (K \ Bad).card := by ring
  have h_KBad_card : (K \ Bad).card ≤ K.card := Finset.card_le_card Finset.sdiff_subset
  have h_total_le : ∑ k ∈ K, A k ≤ H * K.card + (2 * H - 1) * K.card := by
    rw [h_split]
    have h_mul_le : (2 * H - 1) * (K \ Bad).card ≤ (2 * H - 1) * K.card :=
      Nat.mul_le_mul_left _ h_KBad_card
    linarith
  have h_combined : 8 * H * K.card ≤ H * K.card + (2 * H - 1) * K.card :=
    hTotal.trans h_total_le
  have hK_pos : 0 < K.card := Finset.Nonempty.card_pos hKne
  have h_2H_le : (2 * H - 1) * K.card ≤ 2 * H * K.card :=
    Nat.mul_le_mul_right K.card (by omega)
  have h_3HK : 8 * H * K.card ≤ 3 * H * K.card := by
    have h_eq : H * K.card + 2 * H * K.card = 3 * H * K.card := by ring
    linarith
  have hHK_pos : 0 < H * K.card := by apply Nat.mul_pos <;> omega
  linarith

private lemma multiples_in_short_interval_lower (q R p : ℕ)
    (hqpos : 0 < q) (hR : 4 * q ≤ R) :
    R / (2 * q) ≤ ((Finset.Ico (p + 1) (p + R)).filter (fun k => q ∣ k)).card := by
  classical
  let f : ℕ → ℕ := fun i => q * (p / q + i)
  let src : Finset ℕ := Finset.Icc 1 (R / (2 * q))
  have h_mem : ∀ i ∈ src, f i ∈ (Finset.Ico (p + 1) (p + R)).filter (fun k => q ∣ k) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl⟩
    · have h1 : q * (p / q) ≤ p := Nat.mul_div_le p q
      have h2 : 1 ≤ i := hi.1
      have h3 : p < q * (p / q + 1) := by
        have h_eq : p = q * (p / q) + p % q := (Nat.div_add_mod p q).symm
        have h_mod : p % q < q := Nat.mod_lt p hqpos
        calc p = q * (p / q) + p % q := h_eq
          _ < q * (p / q) + q := by omega
          _ = q * (p / q + 1) := by ring
      have : p + 1 ≤ q * (p / q + 1) := h3
      calc p + 1 ≤ q * (p / q + 1) := this
        _ ≤ q * (p / q + i) := Nat.mul_le_mul_left q (by omega)
    · have h1 : q * (p / q) ≤ p := Nat.mul_div_le p q
      have h2 : i ≤ R / (2 * q) := hi.2
      have h3 : 2 * q * (R / (2 * q)) ≤ R := Nat.mul_div_le R (2 * q)
      have h_R_pos : 0 < R := by omega
      calc q * (p / q + i) = q * (p / q) + q * i := by ring
        _ ≤ p + q * (R / (2 * q)) := by
            have := Nat.mul_le_mul_left q h2
            omega
        _ < p + R := by
            have h4 : q * (R / (2 * q)) ≤ R / 2 := by
              rw [Nat.le_div_iff_mul_le (by norm_num : (0:ℕ) < 2)]
              have h5 : q * (R / (2 * q)) * 2 = 2 * q * (R / (2 * q)) := by ring
              rw [h5]; exact h3
            have hR2 : R / 2 < R := Nat.div_lt_self h_R_pos (by norm_num)
            omega
  have h_inj : Set.InjOn f src := by
    intro i _ j _ hij
    have : p / q + i = p / q + j :=
      Nat.eq_of_mul_eq_mul_left hqpos hij
    omega
  have h_card : src.card = R / (2 * q) := by
    rw [Nat.card_Icc]
    have : 1 ≤ R / (2 * q) := by
      have h_2q : 0 < 2 * q := by omega
      have : 2 * q ≤ R := by omega
      exact Nat.one_le_div_iff h_2q |>.mpr this
    omega
  calc R / (2 * q) = src.card := h_card.symm
    _ ≤ ((Finset.Ico (p + 1) (p + R)).filter (fun k => q ∣ k)).card :=
        Finset.card_le_card_of_injOn f h_mem h_inj

private lemma piAP_nat_sub (a b q r : ℕ) (hab : a ≤ b) :
    piAP (b : ℝ) q r - piAP (a : ℝ) q r =
      ((Finset.Ioc a b).filter
        (fun n => n.Prime ∧ n % q = r % q)).card := by
  classical
  unfold piAP
  rw [Nat.floor_natCast, Nat.floor_natCast]
  let P : ℕ → Prop := fun n => n.Prime ∧ n % q = r % q
  have h_split : (Finset.Ioc 0 b).filter P =
      ((Finset.Ioc 0 a).filter P) ∪ ((Finset.Ioc a b).filter P) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      rcases Nat.lt_or_ge x (a + 1) with hxa | hxa
      · exact Or.inl ⟨⟨h1, by omega⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, hp⟩
    · rintro (⟨⟨h1, h2⟩, hp⟩ | ⟨⟨h1, h2⟩, hp⟩)
      · exact ⟨⟨h1, h2.trans hab⟩, hp⟩
      · exact ⟨⟨Nat.lt_of_le_of_lt (Nat.zero_le _) h1, h2⟩, hp⟩
  have h_disj_base : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Ioc] at hx1 hx2
    omega
  have h_disj : Disjoint ((Finset.Ioc 0 a).filter P) ((Finset.Ioc a b).filter P) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) h_disj_base)
  change ((Finset.Ioc 0 b).filter P).card - ((Finset.Ioc 0 a).filter P).card =
      ((Finset.Ioc a b).filter P).card
  rw [h_split, Finset.card_union_of_disjoint h_disj]
  omega

private theorem log_half_pos {x : ℝ} (hx : 2 < x) : 0 < Real.log (x / 2) := by
  apply Real.log_pos
  linarith

private theorem log_le_two_log_half {x : ℝ} (hx : 4 ≤ x) :
    Real.log x ≤ 2 * Real.log (x / 2) := by
  have h_xdiv2_sq_ge_x : (x / 2) ^ 2 ≥ x := by nlinarith
  have h_xdiv2_pos : (0 : ℝ) < x / 2 := by linarith
  have h_log_sq : Real.log ((x / 2) ^ 2) = 2 * Real.log (x / 2) := by
    rw [Real.log_pow]; ring
  calc Real.log x ≤ Real.log ((x / 2) ^ 2) :=
          Real.log_le_log (by linarith) h_xdiv2_sq_ge_x
    _ = 2 * Real.log (x / 2) := h_log_sq

private theorem inv_log_half_le_two_inv_log {x : ℝ} (hx : 4 ≤ x) :
    1 / Real.log (x / 2) ≤ 2 / Real.log x := by
  have hx_gt_2 : 2 < x := by linarith
  have h_log_half_pos : 0 < Real.log (x / 2) := log_half_pos hx_gt_2
  have h_log_x_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have h_le : Real.log x ≤ 2 * Real.log (x / 2) := log_le_two_log_half hx
  rw [div_le_div_iff₀ h_log_half_pos h_log_x_pos]
  linarith
private lemma totient_prime_real (q : ℕ) (hq : q.Prime) :
    (q.totient : ℝ) = (q : ℝ) - 1 := by
  rw [Nat.totient_prime hq]
  have h_one_le : 1 ≤ q := hq.one_lt.le
  push_cast [Nat.cast_sub h_one_le]; rfl

private lemma piAP_mono {a b : ℝ} (q r : ℕ) (hab : a ≤ b) :
    piAP a q r ≤ piAP b q r := by
  unfold piAP
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
  refine ⟨⟨hn.1.1, ?_⟩, hn.2⟩
  exact hn.1.2.trans (Nat.floor_le_floor hab)

private lemma piAP_real_diff_eq (a b : ℕ) (q r : ℕ) (hab : a ≤ b) :
    ((piAP (b : ℝ) q r : ℕ) : ℝ) - ((piAP (a : ℝ) q r : ℕ) : ℝ) =
      (((Finset.Ioc a b).filter (fun n => n.Prime ∧ n % q = r % q)).card : ℝ) := by
  have h_mono : piAP (a : ℝ) q r ≤ piAP (b : ℝ) q r :=
    piAP_mono q r (by exact_mod_cast hab)
  have h_nat := piAP_nat_sub a b q r hab
  rw [← h_nat]
  rw [Nat.cast_sub h_mono]

private lemma piAP_eq_floor (x : ℝ) (q r : ℕ) :
    piAP x q r = piAP ((Nat.floor x : ℕ) : ℝ) q r := by
  unfold piAP
  rw [Nat.floor_natCast]

private lemma piAP_real_diff_floor (u v : ℝ) (q r : ℕ) (huv : u ≤ v) :
    ((piAP v q r : ℕ) : ℝ) - ((piAP u q r : ℕ) : ℝ) =
      (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n => n.Prime ∧ n % q = r % q)).card : ℝ) := by
  rw [piAP_eq_floor v, piAP_eq_floor u]
  exact piAP_real_diff_eq _ _ q r (Nat.floor_le_floor huv)

private lemma log_div_two_ratio_lower (k : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hk : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k) :
    Real.log 2 / Real.log k ≤ ε / 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_exp_pos : (0 : ℝ) < 2 * Real.exp (2 * Real.log 2 / ε) := by positivity
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_gt_1 : (1 : ℝ) < k := by
    have h1 : (1 : ℝ) < 2 * Real.exp (2 * Real.log 2 / ε) := by
      have h2 : 1 ≤ Real.exp (2 * Real.log 2 / ε) := Real.one_le_exp (by positivity)
      linarith
    linarith
  have hlogk_pos : 0 < Real.log k := Real.log_pos hk_gt_1
  have hk_log : Real.log 2 + 2 * Real.log 2 / ε ≤ Real.log k := by
    have h := Real.log_le_log h_exp_pos hk
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at h
    exact h
  rw [div_le_div_iff₀ hlogk_pos (by norm_num : (0 : ℝ) < 2)]
  have h_main : Real.log 2 * 2 ≤ Real.log k * ε := by
    have h_step : Real.log 2 * 2 ≤ (Real.log 2 + 2 * Real.log 2 / ε) * ε := by
      have : 2 * Real.log 2 / ε * ε = 2 * Real.log 2 := by field_simp
      nlinarith
    nlinarith
  linarith

private lemma log_2_over_log_k_div_2 (k : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hk : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k) :
    Real.log 2 / Real.log (k / 2) ≤ ε / 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_exp_pos : (0 : ℝ) < 2 * Real.exp (2 * Real.log 2 / ε) := by positivity
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_div2_ge : Real.exp (2 * Real.log 2 / ε) ≤ k / 2 := by linarith
  have h_exp_pos2 : 0 < Real.exp (2 * Real.log 2 / ε) := Real.exp_pos _
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by
    have h1 : 1 < Real.exp (2 * Real.log 2 / ε) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hlogkdiv2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  have hlogkdiv2_ge : 2 * Real.log 2 / ε ≤ Real.log (k / 2) := by
    have h := Real.log_le_log h_exp_pos2 hk_div2_ge
    rwa [Real.log_exp] at h
  have h_mult : 2 * Real.log 2 ≤ ε * Real.log (k / 2) := by
    have h := mul_le_mul_of_nonneg_left hlogkdiv2_ge hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at h
  rw [div_le_div_iff₀ hlogkdiv2_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

private lemma log_k_over_log_kdiv2_bound (k : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hk : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k) :
    Real.log k / Real.log (k / 2) ≤ 1 + ε / 2 := by
  have h_exp_pos : (0 : ℝ) < 2 * Real.exp (2 * Real.log 2 / ε) := by positivity
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_div2_pos : (0 : ℝ) < k / 2 := by linarith
  have hk_div2_ge : Real.exp (2 * Real.log 2 / ε) ≤ k / 2 := by linarith
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by
    have h1 : 1 < Real.exp (2 * Real.log 2 / ε) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hlogkdiv2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  have h_log_split : Real.log k = Real.log (k / 2) + Real.log 2 := by
    rw [← Real.log_mul hk_div2_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; field_simp
  rw [h_log_split, _root_.add_div, div_self hlogkdiv2_pos.ne']
  have h_ratio := log_2_over_log_k_div_2 k ε hε hk
  linarith

private lemma log_k_le_two_log_k_div_2_uncond (k : ℝ) (hk : 4 ≤ k) :
    Real.log k ≤ 2 * Real.log (k / 2) := by
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_div2_pos : (0 : ℝ) < k / 2 := by linarith
  have hk_div2_ge2 : (2 : ℝ) ≤ k / 2 := by linarith
  have h_log2 : Real.log 2 ≤ Real.log (k / 2) := Real.log_le_log (by norm_num) hk_div2_ge2
  have h_log_split : Real.log k = Real.log (k / 2) + Real.log 2 := by
    rw [← Real.log_mul hk_div2_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; field_simp
  linarith

private lemma log_k_over_log_k_div_2_le_two (k : ℝ) (hk : 4 ≤ k) :
    Real.log k / Real.log (k / 2) ≤ 2 := by
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by linarith
  have hlog_div2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  rw [div_le_iff₀ hlog_div2_pos]
  have := log_k_le_two_log_k_div_2_uncond k hk
  linarith

private lemma log_2_over_log_k_div_2_le_one (k : ℝ) (hk : 4 ≤ k) :
    Real.log 2 / Real.log (k / 2) ≤ 1 := by
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by linarith
  have hlog_div2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  have hk_div2_ge2 : (2 : ℝ) ≤ k / 2 := by linarith
  have h_log2 : Real.log 2 ≤ Real.log (k / 2) := Real.log_le_log (by norm_num) hk_div2_ge2
  rw [div_le_one hlog_div2_pos]; exact h_log2

private lemma x_div_diff_eq (X T D1 D2 : ℝ)
    (hT_pos : 0 < T) (hD1_pos : 0 < D1) (hD2_pos : 0 < D2) :
    X / (T * D1) - X / (T * D2) = X * (D2 - D1) / (T * D1 * D2) := by
  field_simp

private lemma abs_sub_div_T_logs_bound (X count T : ℝ) (k ε : ℝ)
    (hT_pos : 0 < T) (hε : 0 < ε) (hX_nn : 0 ≤ X)
    (hk : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k)
    (h_main : |count - X / (T * Real.log (k / 2))| ≤
      ε / 4 * X / (T * Real.log (k / 2))) :
    |count - X / (T * Real.log k)| ≤
      ε / 4 * X / (T * Real.log (k / 2)) +
        X * (Real.log k - Real.log (k / 2)) /
          (T * Real.log (k / 2) * Real.log k) := by
  have h_exp_pos : (0 : ℝ) < 2 * Real.exp (2 * Real.log 2 / ε) := by positivity
  have hk_pos : (0 : ℝ) < k := by linarith
  have hk_div2_ge : Real.exp (2 * Real.log 2 / ε) ≤ k / 2 := by linarith
  have h_exp_pos2 : 0 < Real.exp (2 * Real.log 2 / ε) := Real.exp_pos _
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by
    have h1 : 1 < Real.exp (2 * Real.log 2 / ε) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hk_gt_1 : (1 : ℝ) < k := by linarith
  have hlogkdiv2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  have hlogk_pos : 0 < Real.log k := Real.log_pos hk_gt_1
  have h_swap := x_div_diff_eq X T (Real.log (k / 2)) (Real.log k) hT_pos hlogkdiv2_pos hlogk_pos
  calc |count - X / (T * Real.log k)|
      = |(count - X / (T * Real.log (k / 2))) +
          (X / (T * Real.log (k / 2)) - X / (T * Real.log k))| := by ring_nf
    _ ≤ |count - X / (T * Real.log (k / 2))| +
          |X / (T * Real.log (k / 2)) - X / (T * Real.log k)| := by
        exact abs_add_le _ _
    _ ≤ ε / 4 * X / (T * Real.log (k / 2)) +
          |X / (T * Real.log (k / 2)) - X / (T * Real.log k)| := by linarith
    _ = ε / 4 * X / (T * Real.log (k / 2)) +
          X * (Real.log k - Real.log (k / 2)) /
            (T * Real.log (k / 2) * Real.log k) := by
        rw [h_swap]
        have h_nn : 0 ≤ X * (Real.log k - Real.log (k / 2)) /
            (T * Real.log (k / 2) * Real.log k) := by
          apply div_nonneg
          · apply mul_nonneg hX_nn
            have : Real.log (k / 2) ≤ Real.log k := Real.log_le_log (by linarith) (by linarith)
            linarith
          · positivity
        rw [abs_of_nonneg h_nn]

private lemma quarter_log_ratio_plus_log2_ratio_bound (k ε : ℝ) (hε : 0 < ε)
    (hk_ge_4 : 4 ≤ k)
    (hk : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k) :
    ε / 4 * (Real.log k / Real.log (k / 2)) + Real.log 2 / Real.log (k / 2) ≤ ε := by
  by_cases h_eps_le : ε ≤ 2
  · have h1 : Real.log k / Real.log (k / 2) ≤ 1 + ε / 2 :=
      log_k_over_log_kdiv2_bound k ε hε hk
    have h2 : Real.log 2 / Real.log (k / 2) ≤ ε / 2 :=
      log_2_over_log_k_div_2 k ε hε hk
    have h_div2_pos : 0 < Real.log (k / 2) := Real.log_pos (by linarith)
    have h_ratio_nn : 0 ≤ Real.log k / Real.log (k / 2) := by
      apply div_nonneg
      · exact Real.log_nonneg (by linarith)
      · linarith
    nlinarith
  · push_neg at h_eps_le
    have h1 : Real.log k / Real.log (k / 2) ≤ 2 := log_k_over_log_k_div_2_le_two k hk_ge_4
    have h2 : Real.log 2 / Real.log (k / 2) ≤ 1 := log_2_over_log_k_div_2_le_one k hk_ge_4
    have h_ratio_nn : 0 ≤ Real.log k / Real.log (k / 2) := by
      apply div_nonneg
      · exact Real.log_nonneg (by linarith)
      · have h_div2_pos : 0 < Real.log (k / 2) := Real.log_pos (by linarith)
        linarith
    nlinarith

private lemma q_minus_one_pos_real (q : ℕ) (hq : q.Prime) : (0 : ℝ) < (q : ℝ) - 1 := by
  have h_two_le : 2 ≤ q := hq.two_le
  have h_two_le_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h_two_le
  linarith

private lemma exp_log_eps_le_k_of_Kr_le (k : ℕ) (x₀ ε : ℝ) (hε : 0 < ε)
    (hKr_le_k : max (max (2 * x₀) 4) (2 * Real.exp (2 * Real.log 2 / ε)) ≤ (k : ℝ)) :
    2 * Real.exp (2 * Real.log 2 / ε) ≤ (k : ℝ) :=
  (le_max_right _ _).trans hKr_le_k

private lemma piAP_diff_nn (u v : ℝ) (q r : ℕ) (huv : u ≤ v) :
    (0 : ℝ) ≤ ((piAP v q r : ℕ) : ℝ) - ((piAP u q r : ℕ) : ℝ) := by
  rw [piAP_real_diff_floor u v q r huv]
  exact_mod_cast Nat.zero_le _

private lemma pnt_assembly_final (X T count : ℝ) (k ε : ℝ)
    (hε : 0 < ε) (hT_pos : 0 < T) (hX_nn : 0 ≤ X) (hk_ge_4 : 4 ≤ k)
    (hk_exp : 2 * Real.exp (2 * Real.log 2 / ε) ≤ k)
    (h_hPNT : |count - X / (T * Real.log (k / 2))| ≤ ε / 4 * X / (T * Real.log (k / 2))) :
    |count - X / (T * Real.log k)| ≤ ε * X / (T * Real.log k) := by
  have h_triangle := abs_sub_div_T_logs_bound X count T k ε hT_pos hε hX_nn hk_exp h_hPNT
  have hk_div2_gt_1 : (1 : ℝ) < k / 2 := by linarith
  have hk_gt_1 : (1 : ℝ) < k := by linarith
  have hlogk_pos : 0 < Real.log k := Real.log_pos hk_gt_1
  have hlog_div2_pos : 0 < Real.log (k / 2) := Real.log_pos hk_div2_gt_1
  have h_log_split : Real.log k = Real.log (k / 2) + Real.log 2 := by
    have hk_pos : (0 : ℝ) < k := by linarith
    have hk_div2_pos : (0 : ℝ) < k / 2 := by linarith
    rw [← Real.log_mul hk_div2_pos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; field_simp
  have h_ratio_bound := quarter_log_ratio_plus_log2_ratio_bound k ε hε hk_ge_4 hk_exp
  calc |count - X / (T * Real.log k)|
      ≤ ε / 4 * X / (T * Real.log (k / 2)) +
            X * (Real.log k - Real.log (k / 2)) /
              (T * Real.log (k / 2) * Real.log k) := h_triangle
    _ = X / (T * Real.log k) *
          (ε / 4 * (Real.log k / Real.log (k / 2)) + Real.log 2 / Real.log (k / 2)) := by
        have h_diff : Real.log k - Real.log (k / 2) = Real.log 2 := by linarith [h_log_split]
        rw [h_diff]; field_simp
    _ ≤ X / (T * Real.log k) * ε := by
        apply mul_le_mul_of_nonneg_left h_ratio_bound
        apply div_nonneg hX_nn
        positivity
    _ = ε * X / (T * Real.log k) := by ring
theorem PNT_AP_long (q : ℕ) (hq : q.Prime) (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ u v : ℝ,
        (k : ℝ) / 2 ≤ u → u < v → v ≤ (k : ℝ) →
        δ * (k : ℝ) ≤ v - u →
        |((piAP v q 1 : ℝ) - (piAP u q 1 : ℝ)) -
            (v - u) / ((q - 1 : ℝ) * Real.log k)| ≤
          ε * (v - u) / ((q - 1 : ℝ) * Real.log k) := by
  intro ε hε
  have hq_pos : 1 ≤ q := hq.one_lt.le
  have h1_lt_q : 1 < q := hq.one_lt
  have hcoprime : (1 : ℕ).Coprime q := Nat.coprime_one_left q
  obtain ⟨x₀, hx₀_ge, hx₀⟩ :=
    Erdos387.ANT.PNT_fixed_modulus q 1 hq_pos h1_lt_q hcoprime
      (2 * δ) (by linarith) (ε / 4) (by linarith)

  set Kr : ℝ := max (max (2 * x₀) 4) (2 * Real.exp (2 * Real.log 2 / ε))
  refine ⟨⌈Kr⌉₊, ?_⟩
  intro k hk u v hu_ge hu_v hv_le hδ_le
  have hKr_le_k : Kr ≤ (k : ℝ) := (Nat.le_ceil Kr).trans (by exact_mod_cast hk)
  have hk_ge_2x₀ : (2 * x₀ : ℝ) ≤ (k : ℝ) :=
    (le_max_left _ _).trans <| (le_max_left _ _).trans hKr_le_k
  have hk_ge_4 : (4 : ℝ) ≤ (k : ℝ) :=
    (le_max_right (2 * x₀) 4).trans <| (le_max_left _ _).trans hKr_le_k
  have hk_div2_ge_x₀ : x₀ ≤ (k : ℝ) / 2 := by linarith
  have hk_div2_ge_2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by linarith
  have hk_gt_2 : (2 : ℝ) < (k : ℝ) := by linarith
  have hk_div2_pos : (0 : ℝ) < (k : ℝ) / 2 := by linarith

  have h2δ_pos : 0 < 2 * δ := by linarith
  have h_window : (k : ℝ) / 2 ≤ u ∧ u < v ∧ v ≤ 2 * ((k : ℝ) / 2) ∧
      2 * δ * ((k : ℝ) / 2) ≤ v - u := by
    refine ⟨hu_ge, hu_v, ?_, ?_⟩
    · linarith
    · have : 2 * δ * ((k : ℝ) / 2) = δ * (k : ℝ) := by ring
      linarith
  obtain ⟨h_u_ge, h_u_v, h_v_le, h_δ_le⟩ := h_window

  have hPNT := hx₀ ((k : ℝ) / 2) hk_div2_ge_x₀ u v h_u_ge h_u_v h_v_le h_δ_le
  have h_kr : 2 * Real.exp (2 * Real.log 2 / ε) ≤ (k : ℝ) :=
    (le_max_right _ _).trans hKr_le_k
  have h_X_nn : (0 : ℝ) ≤ v - u := by linarith
  have h_T_pos : (0 : ℝ) < (q.totient : ℝ) := by
    rw [totient_prime_real q hq]; exact q_minus_one_pos_real q hq
  have h_count_eq : ((piAP v q 1 : ℕ) : ℝ) - ((piAP u q 1 : ℕ) : ℝ) =
      (({p ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ | Nat.Prime p ∧ p % q = 1} : Finset ℕ).card : ℝ) := by
    have h := piAP_real_diff_floor u v q 1 (le_of_lt h_u_v)
    have h_one_mod : (1 : ℕ) % q = 1 := Nat.one_mod_eq_one.mpr h1_lt_q.ne'
    simp only [h_one_mod] at h
    exact h
  rw [← h_count_eq] at hPNT
  have h_assembly := pnt_assembly_final (v - u) (q.totient : ℝ)
    (((piAP v q 1 : ℕ) : ℝ) - ((piAP u q 1 : ℕ) : ℝ))
    (k : ℝ) ε hε h_T_pos h_X_nn hk_ge_4 h_kr hPNT
  rw [totient_prime_real q hq] at h_assembly
  exact h_assembly
lemma central_primes_AP_lower (q : ℕ) (hq : q.Prime) (hq2 : 2 ≤ q) :
    ∃ X₀ : ℕ, ∀ X R : ℕ, X₀ ≤ X → R ≤ X / 4 →
      ((X : ℝ) / (8 * ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))))) ≤
        (((Finset.Ioc X (2 * X - R)).filter
          (fun p => p.Prime ∧ p % q = 1)).card : ℝ) := by
  classical
  obtain ⟨K_pnt, hK_pnt⟩ :=
    PNT_AP_long q hq (1/4 : ℝ) (by norm_num) (1/2 : ℝ) (by norm_num)
  refine ⟨max K_pnt 8, ?_⟩
  intro X R hXge hRle
  have h_X_ge_K : K_pnt ≤ X := (le_max_left _ _).trans hXge
  have h_X_ge_8 : 8 ≤ X := (le_max_right _ _).trans hXge
  have h_K_2X : K_pnt ≤ 2 * X := by omega
  have h_R_le_half : R ≤ X / 2 := by
    have : X / 4 ≤ X / 2 := Nat.div_le_div_left (by omega) (by omega)
    omega
  have h_XR_le : X ≤ 2 * X - R := by omega
  have hXR_nat : R ≤ 2 * X := by omega
  have h_R_real_le : (R : ℝ) ≤ (X : ℝ) / 2 := by
    have h1 : (R : ℝ) ≤ ((X / 2 : ℕ) : ℝ) := by exact_mod_cast h_R_le_half
    have h2 : (2 : ℝ) * ((X / 2 : ℕ) : ℝ) ≤ (X : ℝ) := by
      have : 2 * (X / 2) ≤ X := by omega
      exact_mod_cast this
    linarith
  have h_u_real : ((2 * X : ℕ) : ℝ) / 2 ≤ (X : ℝ) := by push_cast; linarith
  have h_u_lt_v : (X : ℝ) < ((2 * X - R : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : X < 2 * X - R)
  have h_v_le : ((2 * X - R : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : 2 * X - R ≤ 2 * X)
  have h_VU : ((2 * X - R : ℕ) : ℝ) - (X : ℝ) = (X : ℝ) - (R : ℝ) := by
    rw [Nat.cast_sub hXR_nat]; push_cast; ring
  have h_delta_le : (1/4 : ℝ) * ((2 * X : ℕ) : ℝ) ≤
      ((2 * X - R : ℕ) : ℝ) - (X : ℝ) := by
    rw [h_VU]; push_cast; linarith
  have h_pnt := hK_pnt (2 * X) h_K_2X (X : ℝ) ((2 * X - R : ℕ) : ℝ)
    h_u_real h_u_lt_v h_v_le h_delta_le
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have h_2X_real : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
  have h_log_eq : Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 * (X : ℝ)) := by
    rw [h_2X_real]
  have h_2X_pos : (1 : ℝ) < 2 * (X : ℝ) := by
    have h2X : (8 : ℕ) ≤ X := h_X_ge_8
    have : (8 : ℝ) ≤ X := by exact_mod_cast h2X
    linarith
  have h_log_pos : (0 : ℝ) < Real.log (2 * (X : ℝ)) := Real.log_pos h_2X_pos
  have h_q_pos : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have h_denom_pos : (0 : ℝ) < ((q : ℝ) - 1) * Real.log (2 * (X : ℝ)) :=
    mul_pos h_q_pos h_log_pos
  rw [h_VU, h_log_eq] at h_pnt
  have h_abs_lb := (abs_le.mp h_pnt).1
  have h_pi_real_diff :
      ((piAP ((2 * X - R : ℕ) : ℝ) q 1 : ℕ) : ℝ) - ((piAP (X : ℝ) q 1 : ℕ) : ℝ) =
        (((Finset.Ioc X (2 * X - R)).filter
          (fun n => n.Prime ∧ n % q = 1 % q)).card : ℝ) := by
    have h_eq_X : ((X : ℕ) : ℝ) = (X : ℝ) := by norm_cast
    have h := piAP_real_diff_eq X (2 * X - R) q 1 h_XR_le
    rw [h_eq_X] at h
    exact h
  have h_mod_eq : (1 % q : ℕ) = 1 := Nat.mod_eq_of_lt (by omega : 1 < q)
  have h_filter_simp :
      (Finset.Ioc X (2 * X - R)).filter (fun n => n.Prime ∧ n % q = 1 % q) =
      (Finset.Ioc X (2 * X - R)).filter (fun n => n.Prime ∧ n % q = 1) := by
    apply Finset.filter_congr
    intro x _; rw [h_mod_eq]
  rw [h_filter_simp] at h_pi_real_diff
  have h_lb_real :
      (1/2 : ℝ) * ((X : ℝ) - R) / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) ≤
        ((piAP ((2 * X - R : ℕ) : ℝ) q 1 : ℕ) : ℝ) -
          ((piAP (X : ℝ) q 1 : ℕ) : ℝ) := by
    have h_simp1 : (1 / 2 : ℝ) * (↑X - ↑R) / ((↑q - 1) * Real.log (2 * (X : ℝ))) =
        (1 / 2) * ((↑X - ↑R) / ((↑q - 1) * Real.log (2 * (X : ℝ)))) := by ring
    have h_eq : ((X : ℝ) - R) / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) -
        (1/2) * (((X : ℝ) - R) / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ)))) =
        (1/2 : ℝ) * ((X : ℝ) - R) / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) := by ring
    linarith
  rw [h_pi_real_diff] at h_lb_real
  have h_X_lower : (X : ℝ) - (R : ℝ) ≥ (X : ℝ) / 2 := by linarith
  have h_8X_le : (X : ℝ) / 8 ≤ (1 / 2 : ℝ) * ((X : ℝ) - R) := by linarith
  have h_div_mono : (X : ℝ) / 8 / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) ≤
      (1 / 2 : ℝ) * ((X : ℝ) - R) / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) := by
    apply div_le_div_of_nonneg_right h_8X_le h_denom_pos.le
  have h_eq_form : (X : ℝ) / 8 / ((q - 1 : ℝ) * Real.log (2 * (X : ℝ))) =
      (X : ℝ) / (8 * ((q - 1 : ℝ) * Real.log (2 * (X : ℝ)))) := by
    rw [div_div]
  linarith [h_eq_form ▸ h_div_mono]

private lemma sum_Acount_lower (q X R : ℕ) (hqpos : 0 < q) (hR : 4 * q ≤ R) :
    ((Finset.Ioc X (2 * X - R)).filter (fun p => p.Prime ∧ p % q = 1)).card * (R / (2 * q)) ≤
      ∑ k ∈ (Finset.Icc X (2 * X)).filter (fun k => q ∣ k),
        ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card := by
  classical
  set P : Finset ℕ := (Finset.Ioc X (2 * X - R)).filter (fun p => p.Prime ∧ p % q = 1)
  set K : Finset ℕ := (Finset.Icc X (2 * X)).filter (fun k => q ∣ k)
  have h_inner : ∀ k ∈ K,
      (P.filter (fun p => k - R < p ∧ p ≤ k)).card ≤
      ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card := by
    intro k _
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpP, hp_lo, hp_hi⟩ := hp
    rw [Finset.mem_filter] at hpP
    obtain ⟨_, hpprime, hpmod⟩ := hpP
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hp_lo, hp_hi⟩, hpprime, hpmod⟩
  have h_swap : ∑ k ∈ K, (P.filter (fun p => k - R < p ∧ p ≤ k)).card =
                ∑ p ∈ P, (K.filter (fun k => k - R < p ∧ p ≤ k)).card := by
    simp_rw [Finset.card_eq_sum_ones]
    exact Finset.sum_comm' (fun k p => by simp_rw [Finset.mem_filter]; tauto)
  have h_per_p : ∀ p ∈ P, R / (2 * q) ≤ (K.filter (fun k => k - R < p ∧ p ≤ k)).card := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpIoc, _, _⟩ := hp
    rw [Finset.mem_Ioc] at hpIoc
    have h_mult := multiples_in_short_interval_lower q R p hqpos hR
    apply h_mult.trans
    apply Finset.card_le_card
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ico] at hk
    obtain ⟨⟨hkp, hkR⟩, hqk⟩ := hk
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, hqk⟩, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
  calc P.card * (R / (2 * q))
      = ∑ _p ∈ P, R / (2 * q) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ p ∈ P, (K.filter (fun k => k - R < p ∧ p ≤ k)).card :=
          Finset.sum_le_sum h_per_p
    _ = ∑ k ∈ K, (P.filter (fun p => k - R < p ∧ p ≤ k)).card := h_swap.symm
    _ ≤ ∑ k ∈ K, ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card :=
          Finset.sum_le_sum h_inner

private lemma nat_log_two_le_real_log {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h_two_le : 2 ≤ n := hn
  have h_n_pos : 0 < n := by omega
  have h_n_real_pos : (0 : ℝ) < n := by exact_mod_cast h_n_pos
  have h_pow_le : (2 : ℕ) ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h_real_pow : (2 : ℝ) ^ (Nat.log 2 n) ≤ n := by exact_mod_cast h_pow_le
  have h_log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_le : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log n :=
    Real.log_le_log (by positivity) h_real_pow
  rw [Real.log_pow] at h_log_le
  rw [le_div_iff₀ h_log_two_pos]
  linarith

private lemma smoothFinset_card_real_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (N : ℕ) :
    ((smoothFinset P N).card : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ P.card := by
  have h1 : (smoothFinset P N).card ≤ ∏ p ∈ P, (Nat.log p N + 1) :=
    smoothFinset_card_le hP N
  have h2 : ∏ p ∈ P, (Nat.log p N + 1) ≤ (Nat.log 2 N + 1) ^ P.card := by
    classical
    calc ∏ p ∈ P, (Nat.log p N + 1)
        ≤ ∏ _p ∈ P, (Nat.log 2 N + 1) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro p hp
          have h_le : Nat.log p N ≤ Nat.log 2 N :=
            Nat.log_anti_left (c := 2) (b := p) (n := N) (by norm_num) (hP p hp).two_le
          omega
      _ = (Nat.log 2 N + 1) ^ P.card := by rw [Finset.prod_const]
  have h3 : (smoothFinset P N).card ≤ (Nat.log 2 N + 1) ^ P.card := h1.trans h2
  exact_mod_cast h3

private lemma exists_prime_ge_le_2m (m : ℕ) (hm : 3 ≤ m) :
    ∃ q : ℕ, q.Prime ∧ m ≤ q ∧ q ≤ 2 * m - 2 := by
  obtain ⟨q, hqp, hmq, hqle⟩ := Nat.bertrand (m - 1) (by omega)
  exact ⟨q, hqp, by omega, by omega⟩

lemma polylog_le_self (a d : ℕ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → a * (Nat.log 2 X + 1) ^ d ≤ X := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact ⟨0, by intro X _; simp [ha]⟩
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h_inv_pos : (0 : ℝ) < 1 / ((a : ℝ) * 4 ^ d * 2) := by positivity
  have hLO := (Real.isLittleO_pow_log_id_atTop (n := d)).bound
    (c := 1 / ((a : ℝ) * 4 ^ d * 2)) h_inv_pos
  rw [Filter.eventually_atTop] at hLO
  obtain ⟨N₀, hN₀⟩ := hLO
  refine ⟨max ⌈N₀⌉₊ 4, ?_⟩
  intro X hX
  have hX_ge_4 : 4 ≤ X := (le_max_right _ _).trans hX
  have hX_pos : 0 < X := by omega
  have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
  have hX_real_ge_N0 : (N₀ : ℝ) ≤ X := by
    have h1 : ((⌈N₀⌉₊ : ℕ) : ℝ) ≤ X := by exact_mod_cast (le_max_left _ _).trans hX
    have h2 : N₀ ≤ (⌈N₀⌉₊ : ℕ) := Nat.le_ceil _
    linarith
  have h_log_2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h_log_X_pos : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hX_real_ge_4 : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge_4
  have h_log_X_ge_1 : (1 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hX_real_ge_4
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; ring
      linarith
    linarith
  have h_nat_log_real : (Nat.log 2 X : ℝ) ≤ Real.log X / Real.log 2 := by
    have h_two_le : (2 : ℕ) ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
    have h_real_pow : (2 : ℝ) ^ Nat.log 2 X ≤ X := by exact_mod_cast h_two_le
    have h_log_le : Real.log ((2 : ℝ) ^ Nat.log 2 X) ≤ Real.log X :=
      Real.log_le_log (by positivity) h_real_pow
    rw [Real.log_pow] at h_log_le
    rw [le_div_iff₀ h_log_2_pos]
    linarith
  have h_div_le : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
    rw [div_le_iff₀ h_log_2_pos]
    nlinarith [h_log_X_pos.le, h_log_2_gt_half, h_log_X_ge_1]
  have h_L_bound : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 3 * Real.log X := by
    push_cast
    have h1 : (Nat.log 2 X : ℝ) ≤ 2 * Real.log X := le_trans h_nat_log_real h_div_le
    linarith
  have h_log_pow : Real.log X ^ d ≤ X * (1 / ((a : ℝ) * 4 ^ d * 2)) := by
    have h := hN₀ (X : ℝ) hX_real_ge_N0
    simp only [Real.norm_eq_abs, id_eq] at h
    have h_abs_X : |(X : ℝ)| = X := abs_of_pos hX_real_pos
    have h_pos_pow : (0 : ℝ) ≤ Real.log X ^ d := by positivity
    have h_abs_pow : |Real.log X ^ d| = Real.log X ^ d := abs_of_nonneg h_pos_pow
    rw [h_abs_pow, h_abs_X] at h
    linarith
  have h_L_pow : ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ d ≤ (3 * Real.log X) ^ d :=
    pow_le_pow_left₀ (by positivity) h_L_bound d
  have h_L_pow' : (3 * Real.log X) ^ d = 3^d * Real.log X ^ d := mul_pow _ _ _
  rw [h_L_pow'] at h_L_pow
  have h_a_nn : (0 : ℝ) ≤ a := ha'.le
  have h_3_le_4_real : (3 : ℝ) ^ d ≤ 4 ^ d :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h_3d_nn : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
  have h_final_real : (a : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ d ≤ X := by
    have h_step1 : (a : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ d ≤
        (a : ℝ) * (3 ^ d * Real.log X ^ d) :=
      mul_le_mul_of_nonneg_left h_L_pow h_a_nn
    have h_step2 : (a : ℝ) * (3 ^ d * Real.log X ^ d) ≤
        (a : ℝ) * (3 ^ d * (X * (1 / ((a : ℝ) * 4 ^ d * 2)))) := by
      apply mul_le_mul_of_nonneg_left _ h_a_nn
      exact mul_le_mul_of_nonneg_left h_log_pow h_3d_nn
    have h_step3 : (a : ℝ) * (3 ^ d * (X * (1 / ((a : ℝ) * 4 ^ d * 2)))) ≤ X := by
      have h_4d_pos : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
      have h_eq_div : (a : ℝ) * (3 ^ d * (X * (1 / ((a : ℝ) * 4 ^ d * 2)))) =
            (X * 3^d) / (4^d * 2) := by field_simp
      rw [h_eq_div, div_le_iff₀ (by positivity)]
      have hX_nn : (0 : ℝ) ≤ X := hX_real_pos.le
      have h1 : (X : ℝ) * 3^d ≤ X * 4^d := mul_le_mul_of_nonneg_left h_3_le_4_real hX_nn
      nlinarith [h1, h_4d_pos, hX_nn]
    linarith
  have h_cast_eq : ((a * (Nat.log 2 X + 1) ^ d : ℕ) : ℝ) =
      (a : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
  exact_mod_cast (h_cast_eq ▸ h_final_real)

private lemma loglog_ge (c : ℝ) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X → c ≤ Real.log (Real.log X) := by
  refine ⟨⌈Real.exp (Real.exp c)⌉₊ + 1, ?_⟩
  intro X hX
  have hX_pos : 0 < X := by omega
  have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
  have hM_le : Real.exp (Real.exp c) ≤ X := by
    have h_cast : ((⌈Real.exp (Real.exp c)⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    have h_ceil : Real.exp (Real.exp c) ≤ ((⌈Real.exp (Real.exp c)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    push_cast at h_cast
    linarith
  have hM_pos : 0 < Real.exp (Real.exp c) := Real.exp_pos _
  have hexpc_pos : 0 < Real.exp c := Real.exp_pos _
  have hexpc_le_logX : Real.exp c ≤ Real.log X := by
    have h_log_le : Real.log (Real.exp (Real.exp c)) ≤ Real.log X :=
      Real.log_le_log hM_pos hM_le
    rwa [Real.log_exp] at h_log_le
  have h_final : Real.log (Real.exp c) ≤ Real.log (Real.log X) :=
    Real.log_le_log hexpc_pos hexpc_le_logX
  rwa [Real.log_exp] at h_final

private lemma L_bound (X : ℕ) (hX : 4 ≤ X) :
    ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) ≤ 6 * Real.log X := by
  have hX_pos : 0 < X := by omega
  have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
  have h_log_2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h_log_X_pos : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hX_real_ge_4 : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h_log_X_ge_1 : (1 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hX_real_ge_4
    have h_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
    linarith
  have h_nat_log_2X : (Nat.log 2 (2 * X) : ℝ) ≤ Real.log (2 * X) / Real.log 2 := by
    have h_two_le : (2 : ℕ) ^ Nat.log 2 (2 * X) ≤ 2 * X :=
      Nat.pow_log_le_self 2 (by omega)
    have h_real_pow : (2 : ℝ) ^ Nat.log 2 (2 * X) ≤ ((2 * X : ℕ) : ℝ) := by
      exact_mod_cast h_two_le
    have h_log_le : Real.log ((2 : ℝ) ^ Nat.log 2 (2 * X)) ≤
        Real.log ((2 * X : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) h_real_pow
    rw [Real.log_pow] at h_log_le
    have h_eq : Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 * X) := by push_cast; rfl
    rw [h_eq] at h_log_le
    rw [le_div_iff₀ h_log_2_pos]
    linarith
  have h_log_2X : Real.log (2 * X : ℝ) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (by linarith)
  rw [h_log_2X] at h_nat_log_2X
  push_cast
  have h_div_combo :
      (Real.log 2 + Real.log X) / Real.log 2 = 1 + Real.log X / Real.log 2 := by
    field_simp
  rw [h_div_combo] at h_nat_log_2X
  have h_div_bd : Real.log X / Real.log 2 ≤ 2 * Real.log X := by
    rw [div_le_iff₀ h_log_2_pos]
    nlinarith [h_log_X_pos.le, h_log_2_gt_half, h_log_X_ge_1]
  linarith

set_option linter.style.longLine false in
private lemma loglog_growth (q r : ℕ) (hq : 1 ≤ q) :
    ∃ N₀ : ℕ, ∀ X : ℕ, N₀ ≤ X →
      ((Nat.log 2 (500 * q * (Nat.log 2 (2 * X) + 1) ^ (r + 2)) + 1 : ℕ) : ℝ) ≤
        10 * ((r : ℝ) + 4) * Real.log (Real.log X) := by
  have h_log_2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h_log_six_le_two : Real.log 6 ≤ 2 := by
    have h_e1_gt : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hexp2 : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
    have h_e2_ge : (6 : ℝ) ≤ Real.exp 2 := by rw [hexp2]; nlinarith [h_e1_gt]
    have := Real.log_le_log (show (0:ℝ) < 6 by norm_num) h_e2_ge
    rwa [Real.log_exp] at this
  have h_log_500_le_seven : Real.log 500 ≤ 7 := by
    have h_e1_gt : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have h_e1_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have h_e2 : (7 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith [h_e1_gt]
    have h_e4 : (49 : ℝ) ≤ Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      nlinarith [h_e2, h_e1_pos]
    have h_e7_ge : (500 : ℝ) ≤
        Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      nlinarith [h_e2, h_e4, h_e1_gt, h_e1_pos]
    have hexp7 : Real.exp (7 : ℝ) =
        Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [show (7 : ℝ) = 1+1+1+1+1+1+1 from by norm_num]
      repeat rw [Real.exp_add]
    have h_500 : (500 : ℝ) ≤ Real.exp 7 := hexp7.symm ▸ h_e7_ge
    have := Real.log_le_log (show (0:ℝ) < 500 by norm_num) h_500
    rwa [Real.log_exp] at this
  set bound : ℝ := (23 + 2 * Real.log q + 4 * (r : ℝ)) / (8 * (r : ℝ) + 36)
  obtain ⟨N₁, hN₁⟩ : ∃ N : ℕ, ∀ X : ℕ, N ≤ X → bound ≤ Real.log (Real.log X) := by
    refine ⟨⌈Real.exp (Real.exp bound)⌉₊ + 1, ?_⟩
    intro X hX
    have hX_pos : 0 < X := by omega
    have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
    have hM_le : Real.exp (Real.exp bound) ≤ X := by
      have h_cast : ((⌈Real.exp (Real.exp bound)⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
      have h_ceil : Real.exp (Real.exp bound) ≤ ((⌈Real.exp (Real.exp bound)⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      push_cast at h_cast
      linarith
    have hexpc_pos : 0 < Real.exp bound := Real.exp_pos _
    have hexpc_le_logX : Real.exp bound ≤ Real.log X := by
      have h_log_le : Real.log (Real.exp (Real.exp bound)) ≤ Real.log X :=
        Real.log_le_log (Real.exp_pos _) hM_le
      rwa [Real.log_exp] at h_log_le
    have h_final : Real.log (Real.exp bound) ≤ Real.log (Real.log X) :=
      Real.log_le_log hexpc_pos hexpc_le_logX
    rwa [Real.log_exp] at h_final
  refine ⟨max N₁ 4, ?_⟩
  intro X hX
  have hX_ge_4 : 4 ≤ X := (le_max_right _ _).trans hX
  have hX_pos : 0 < X := by omega
  have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
  have h_bound_le : bound ≤ Real.log (Real.log X) := hN₁ X ((le_max_left _ _).trans hX)
  have h_log_X_pos : (0 : ℝ) < Real.log X :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hX_real_ge_4 : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge_4
  have h_log_X_ge_1 : (1 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hX_real_ge_4
    have h_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
    linarith
  set L : ℕ := Nat.log 2 (2 * X) + 1 with hL_def
  have hL_pos : 0 < L := Nat.succ_pos _
  have hL_real_pos : (0 : ℝ) < L := by exact_mod_cast hL_pos
  have hL_real : (L : ℝ) ≤ 6 * Real.log X := L_bound X hX_ge_4
  have h_logL_bd : Real.log L ≤ 2 + Real.log (Real.log X) := by
    have h1 : Real.log L ≤ Real.log (6 * Real.log X) :=
      Real.log_le_log hL_real_pos hL_real
    have h2 : Real.log (6 * Real.log X) = Real.log 6 + Real.log (Real.log X) :=
      Real.log_mul (by norm_num) h_log_X_pos.ne'
    linarith
  set D2 : ℕ := 500 * q * L ^ (r + 2) with hD2_def
  have hD2_pos : 0 < D2 := by
    have h1 : 0 < 500 * q := Nat.mul_pos (by norm_num) hq
    exact Nat.mul_pos h1 (pow_pos hL_pos _)
  have hD2_real_pos : (0 : ℝ) < D2 := by exact_mod_cast hD2_pos
  have hq_real_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have h_q_ne_zero : (q : ℝ) ≠ 0 := hq_real_pos.ne'
  have h_logD2_bd : Real.log D2 ≤ Real.log 500 + Real.log q + (r + 2) * Real.log L := by
    have h_eq : ((D2 : ℕ) : ℝ) = 500 * q * (L : ℝ) ^ (r + 2) := by
      change ((500 * q * L ^ (r + 2) : ℕ) : ℝ) = _
      push_cast; ring
    rw [h_eq, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) h_q_ne_zero, Real.log_pow]
    push_cast; linarith
  have h_nat_log_D2 : (Nat.log 2 D2 : ℝ) ≤ Real.log D2 / Real.log 2 := by
    have h_two_le : (2 : ℕ) ^ Nat.log 2 D2 ≤ D2 := Nat.pow_log_le_self 2 (by omega)
    have h_real_pow : (2 : ℝ) ^ Nat.log 2 D2 ≤ ((D2 : ℕ) : ℝ) := by exact_mod_cast h_two_le
    have h_log_le : Real.log ((2 : ℝ) ^ Nat.log 2 D2) ≤ Real.log ((D2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) h_real_pow
    rw [Real.log_pow] at h_log_le
    rw [le_div_iff₀ h_log_2_pos]
    linarith
  have hq_log_nn : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have h_log_D2_nn : 0 ≤ Real.log D2 := Real.log_nonneg (by exact_mod_cast hD2_pos)
  have h_2_real_log_D2 : (Nat.log 2 D2 : ℝ) ≤ 2 * Real.log D2 := by
    have h1 : Real.log D2 / Real.log 2 ≤ 2 * Real.log D2 := by
      rw [div_le_iff₀ h_log_2_pos]
      nlinarith [h_log_2_gt_half, h_log_D2_nn]
    linarith
  have h_loglog_X_nn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg h_log_X_ge_1
  have h_logL_nn : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL_pos)
  have h_r_plus_2_nn : (0 : ℝ) ≤ ((r : ℝ) + 2) := by positivity
  push_cast
  have h_logD2_final :
      Real.log D2 ≤ 7 + Real.log q + (r + 2) * (2 + Real.log (Real.log X)) := by
    calc Real.log D2 ≤ Real.log 500 + Real.log q + (r + 2) * Real.log L := h_logD2_bd
      _ ≤ 7 + Real.log q + (r + 2) * (2 + Real.log (Real.log X)) := by
            have h_inner :
                ((r : ℝ) + 2) * Real.log L ≤ ((r : ℝ) + 2) * (2 + Real.log (Real.log X)) :=
              mul_le_mul_of_nonneg_left h_logL_bd h_r_plus_2_nn
            linarith
  have h_step2 : 2 * Real.log D2 + 1 ≤
      2 * (7 + Real.log q + (r + 2) * (2 + Real.log (Real.log X))) + 1 := by
    linarith [mul_le_mul_of_nonneg_left h_logD2_final (by norm_num : (0:ℝ) ≤ 2)]
  have h_rhs_eq : 10 * ((r : ℝ) + 4) * Real.log (Real.log X) =
      (2 * (r : ℝ) + 4) * Real.log (Real.log X) +
      (8 * (r : ℝ) + 36) * Real.log (Real.log X) := by ring
  have h_const_le : 23 + 2 * Real.log q + 4 * (r : ℝ) ≤
      (8 * (r : ℝ) + 36) * Real.log (Real.log X) := by
    have h_denom_pos : (0 : ℝ) < 8 * (r : ℝ) + 36 := by positivity
    have h1 : bound * (8 * (r : ℝ) + 36) = 23 + 2 * Real.log q + 4 * (r : ℝ) := by
      change ((23 + 2 * Real.log q + 4 * (r : ℝ)) / (8 * (r : ℝ) + 36)) * (8 * (r : ℝ) + 36) =
        23 + 2 * Real.log q + 4 * (r : ℝ)
      field_simp
    have h2 : bound * (8 * (r : ℝ) + 36) ≤
        (8 * (r : ℝ) + 36) * Real.log (Real.log X) := by
      rw [mul_comm bound _]
      exact mul_le_mul_of_nonneg_left h_bound_le h_denom_pos.le
    linarith
  linarith

private lemma smoothFinset_mono {P : Finset ℕ} {a b : ℕ} (hab : a ≤ b) :
    smoothFinset P a ⊆ smoothFinset P b := by
  intro n hn
  simp only [smoothFinset, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hab⟩, hn.2⟩

private lemma loglog_mono_nat {X k : ℕ} (hX4 : 4 ≤ X) (hXk : X ≤ k) :
    Real.log (Real.log X) ≤ Real.log (Real.log k) := by
  have hX_pos : 0 < X := by omega
  have hk_pos : 0 < k := by omega
  have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast hX_pos
  have hX_real_ge_4 : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX4
  have h_log_2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_2_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h_log_X_ge_1 : (1 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (show (0:ℝ) < 4 by norm_num) hX_real_ge_4
    have h_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; ring
    linarith
  have h_log_X_pos : 0 < Real.log X := by linarith
  have hXk_real : (X : ℝ) ≤ k := by exact_mod_cast hXk
  have h_log_le : Real.log X ≤ Real.log k :=
    Real.log_le_log hX_real_pos hXk_real
  exact Real.log_le_log h_log_X_pos h_log_le

set_option linter.style.longLine false in
private lemma Kset_card_upper (X q : ℕ) (hq_pos : 0 < q) :
    ((Finset.Icc X (2 * X)).filter (fun k => q ∣ k)).card ≤ X / q + 2 := by
  classical
  set Kset : Finset ℕ := (Finset.Icc X (2 * X)).filter (fun k => q ∣ k) with hKset_def
  set img : Finset ℕ := Finset.Icc (X / q) (2 * X / q) with himg_def
  set f : ℕ → ℕ := fun k => k / q
  have h_inj : Set.InjOn f Kset := by
    intro a ha b hb hab
    have ha_dvd : q ∣ a := (Finset.mem_filter.mp ha).2
    have hb_dvd : q ∣ b := (Finset.mem_filter.mp hb).2
    have ha_eq : q * (a / q) = a := Nat.mul_div_cancel' ha_dvd
    have hb_eq : q * (b / q) = b := Nat.mul_div_cancel' hb_dvd
    have h_div_eq : a / q = b / q := hab
    have : q * (a / q) = q * (b / q) := by rw [h_div_eq]
    omega
  have h_image_sub : Kset.image f ⊆ img := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, hjk⟩ := hj
    have hk_in : k ∈ Finset.Icc X (2*X) := (Finset.mem_filter.mp hk).1
    have ⟨hkX, hkX2⟩ := Finset.mem_Icc.mp hk_in
    rw [Finset.mem_Icc, ← hjk]
    exact ⟨Nat.div_le_div_right hkX, Nat.div_le_div_right hkX2⟩
  have h_card_eq : (Kset.image f).card = Kset.card :=
    Finset.card_image_of_injOn h_inj
  have h_card_le : Kset.card ≤ img.card := by
    rw [← h_card_eq]
    exact Finset.card_le_card h_image_sub
  have h_div_mono : X / q ≤ 2 * X / q :=
    Nat.div_le_div_right (by omega : X ≤ 2 * X)
  have h_img_card : img.card ≤ X / q + 2 := by
    have h := Nat.card_Icc (X / q) (2 * X / q)
    have h_2X_div : 2 * X / q ≤ 2 * (X / q) + 1 := by
      have h2 : X % q < q := Nat.mod_lt _ hq_pos
      have h3 : 2 * X = 2 * q * (X / q) + 2 * (X % q) := by
        have hh := Nat.div_add_mod X q; linarith
      have h5 : 2 * X ≤ 2 * q * (X / q) + 2 * q - 1 := by omega
      have h6 : 2 * X / q ≤ (2 * q * (X / q) + 2 * q - 1) / q := Nat.div_le_div_right h5
      have h_lt : 2 * q * (X / q) + 2 * q - 1 < q * (2 * (X / q) + 2) := by
        have : q * (2 * (X / q) + 2) = 2 * q * (X / q) + 2 * q := by ring
        omega
      have h_div_lt : (2 * q * (X / q) + 2 * q - 1) / q < 2 * (X / q) + 2 := by
        apply Nat.div_lt_iff_lt_mul hq_pos |>.mpr
        rw [show q * (2 * (X / q) + 2) = (2 * (X / q) + 2) * q from by ring] at h_lt
        exact h_lt
      omega
    change (Finset.Icc (X / q) (2 * X / q)).card ≤ _
    rw [h]; omega
  exact h_card_le.trans h_img_card

private lemma Kset_card_lower (X q : ℕ) (hq_pos : 0 < q) (hX_ge_q : q ≤ X) :
    X / q ≤ ((Finset.Icc X (2 * X)).filter (fun k => q ∣ k)).card := by
  classical
  let src : Finset ℕ := Finset.Icc 1 (X / q)
  let f : ℕ → ℕ := fun j => q * (X / q + j)
  have h_inj : Set.InjOn f src := by
    intro i _ j _ hij
    have h : q * (X / q + i) = q * (X / q + j) := hij
    have : X / q + i = X / q + j := Nat.eq_of_mul_eq_mul_left hq_pos h
    omega
  have h_mem : ∀ j ∈ src, f j ∈ (Finset.Icc X (2 * X)).filter (fun k => q ∣ k) := by
    intro j hj
    have hjk : 1 ≤ j ∧ j ≤ X / q := Finset.mem_Icc.mp hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl⟩
    · change X ≤ q * (X / q + j)
      have h1 : X = q * (X / q) + X % q := (Nat.div_add_mod X q).symm
      have h2 : X % q < q := Nat.mod_lt _ hq_pos
      have h3 : q * (X / q + j) = q * (X / q) + q * j := by ring
      have h5 : q ≤ q * j := by
        have hh := Nat.mul_le_mul_left q hjk.1
        omega
      omega
    · change q * (X / q + j) ≤ 2 * X
      have h2 : q * (X / q) ≤ X := Nat.mul_div_le _ _
      have h3 : q * (X / q + j) = q * (X / q) + q * j := by ring
      have h4 : j ≤ X / q := hjk.2
      have h5 : q * j ≤ q * (X / q) := Nat.mul_le_mul_left q h4
      omega
  have h_card_le := Finset.card_le_card_of_injOn f h_mem h_inj
  have h_src_card : src.card = X / q := by
    change (Finset.Icc 1 (X / q)).card = X / q
    rw [Nat.card_Icc]
    have h_pos : 1 ≤ X / q := Nat.one_le_div_iff hq_pos |>.mpr hX_ge_q
    omega
  rw [h_src_card] at h_card_le
  exact h_card_le

private lemma hall_from_uniform {ι α : Type*} [Fintype ι]
    (t : ι → Finset α) (h_bound : ∀ i, Fintype.card ι ≤ (t i).card) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  classical
  refine (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp ?_
  intro S
  by_cases hS : S = ∅
  · subst hS; simp
  obtain ⟨s, hs⟩ : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  calc S.card ≤ (Finset.univ : Finset ι).card := Finset.card_le_univ S
    _ = Fintype.card ι := rfl
    _ ≤ (t s).card := h_bound s
    _ ≤ (S.biUnion t).card :=
        Finset.card_le_card (Finset.subset_biUnion_of_mem t hs)

private lemma smooth_card_at (m q k : ℕ) (hq : q.Prime) :
    (smoothFinset (insert q (primesLT m)) k).card ≤
      (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) := by
  classical
  have hP : ∀ p ∈ insert q (primesLT m), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpLT
    · exact hq
    · exact ((Finset.mem_filter.mp hpLT).2)
  refine (smoothFinset_card_le hP k).trans ?_
  have h_card : (insert q (primesLT m)).card ≤ (primesLT m).card + 1 :=
    Finset.card_insert_le _ _
  have h_factor : ∀ p ∈ insert q (primesLT m), Nat.log p k + 1 ≤ Nat.log 2 k + 1 := by
    intro p hp
    have hp_prime : p.Prime := hP p hp
    have : Nat.log p k ≤ Nat.log 2 k := Nat.log_anti_left (by norm_num) hp_prime.two_le
    omega
  calc ∏ p ∈ insert q (primesLT m), (Nat.log p k + 1)
      ≤ ∏ _p ∈ insert q (primesLT m), (Nat.log 2 k + 1) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun p hp => h_factor p hp)
    _ = (Nat.log 2 k + 1) ^ (insert q (primesLT m)).card := by
        rw [Finset.prod_const]
    _ ≤ (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) :=
        Nat.pow_le_pow_right (by omega) h_card

private lemma smooth_DR_final
    (m q k R X : ℕ) (r : ℕ) (hq : q.Prime) (hr_def : r = (primesLT m).card)
    (hXk : X ≤ k) (hX4 : 4 ≤ X)
    (h_logR_le : ((Nat.log 2 R + 1 : ℕ) : ℝ) ≤
        10 * ((r : ℝ) + 4) * Real.log (Real.log X)) :
    ((smoothFinset (insert q (primesLT m)) R).card : ℝ) ≤
      (10 * ((r : ℝ) + 4)) ^ (r + 1) * (Real.log (Real.log k)) ^ (r + 1) := by
  have hP_prime : ∀ p ∈ insert q (primesLT m), p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hpLT
    · exact hq
    · exact (Finset.mem_filter.mp hpLT).2
  have h_smooth_bound := smoothFinset_card_real_bound (insert q (primesLT m)) hP_prime R
  have hP_card_le : (insert q (primesLT m)).card ≤ r + 1 := by
    rw [hr_def]; exact Finset.card_insert_le _ _
  have h_logR_nn : (0 : ℝ) ≤ ((Nat.log 2 R + 1 : ℕ) : ℝ) := by positivity
  have h_one_le : (1 : ℝ) ≤ ((Nat.log 2 R + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ Nat.log 2 R + 1 := by omega
    exact_mod_cast this
  have h_smooth_real_r1 : ((smoothFinset (insert q (primesLT m)) R).card : ℝ) ≤
      ((Nat.log 2 R + 1 : ℕ) : ℝ) ^ (r + 1) :=
    h_smooth_bound.trans (pow_le_pow_right₀ h_one_le hP_card_le)
  have h_loglog_k : Real.log (Real.log X) ≤ Real.log (Real.log k) :=
    loglog_mono_nat hX4 hXk
  have h_rhs_pos : (0 : ℝ) ≤ 10 * ((r : ℝ) + 4) := by positivity
  have h_logR_le_k : ((Nat.log 2 R + 1 : ℕ) : ℝ) ≤
      10 * ((r : ℝ) + 4) * Real.log (Real.log k) :=
    h_logR_le.trans (mul_le_mul_of_nonneg_left h_loglog_k h_rhs_pos)
  have h_pow_bd : ((Nat.log 2 R + 1 : ℕ) : ℝ) ^ (r + 1) ≤
      (10 * ((r : ℝ) + 4) * Real.log (Real.log k)) ^ (r + 1) :=
    pow_le_pow_left₀ h_logR_nn h_logR_le_k _
  calc ((smoothFinset (insert q (primesLT m)) R).card : ℝ)
      ≤ ((Nat.log 2 R + 1 : ℕ) : ℝ) ^ (r + 1) := h_smooth_real_r1
    _ ≤ (10 * ((r : ℝ) + 4) * Real.log (Real.log k)) ^ (r + 1) := h_pow_bd
    _ = (10 * ((r : ℝ) + 4)) ^ (r + 1) * (Real.log (Real.log k)) ^ (r + 1) := mul_pow _ _ _

set_option linter.style.longLine false in
private lemma avg_prime_supply (m q : ℕ) (hm : 3 ≤ m) (hq : q.Prime) (hmq : m ≤ q) :
    ∃ C_m : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ k D : ℕ, X ≤ k ∧ k ≤ 2 * X ∧ q ∣ k ∧ 2 * D ≤ k ∧
        k ∉ smoothFinset (insert q (primesLT m)) k ∧
        (∀ t ∈ smoothFinset (insert q (primesLT m)) k, t ≤ k - D) ∧
        2 * (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) ≤
          ((Finset.Ioc (k - D / 2) k).filter
              (fun p => p.Prime ∧ p % q = 1)).card ∧
        ((smoothFinset (insert q (primesLT m)) (D / 2)).card : ℝ) ≤
          C_m * (Real.log (Real.log k)) ^ ((primesLT m).card + 1) := by
  classical
  set r := (primesLT m).card with hr_def
  refine ⟨((10 * ((r : ℝ) + 4)) ^ (r + 1) : ℝ), ?_⟩
  obtain ⟨K_pnt, hK_pnt⟩ :=
    PNT_AP_long q hq (1 / 2 : ℝ) (by norm_num) (1 / 10 : ℝ) (by norm_num)
  obtain ⟨N_2D, hN_2D⟩ := polylog_le_self (2000 * q * 2^(r+2)) (r+2)
  obtain ⟨N_R2, hN_R2⟩ := polylog_le_self (1000000 * q^3 * 2^(2*r+4)) (2*r+4)
  obtain ⟨N_loglog, hN_loglog⟩ := loglog_growth q r hq.pos
  obtain ⟨N_central, hN_central⟩ := central_primes_AP_lower q hq hq.two_le
  refine ⟨max (max K_pnt 100) (max (max (2*q*q) N_2D) (max (max N_R2 N_loglog) N_central)), ?_⟩
  intro X hXge
  set H : ℕ := (Nat.log 2 (2 * X) + 1) ^ (r + 1) with hH_def
  set D : ℕ := 1000 * q * H * (Nat.log 2 (2 * X) + 1) with hD_def
  set L : ℕ := Nat.log 2 (2 * X) + 1 with hL_def
  set R : ℕ := D / 2 with hR_def
  have hX_ge_K : K_pnt ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hXge)
  have hX_ge_100 : 100 ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hXge)
  have hX_ge_2qq : 2 * q * q ≤ X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hXge))
  have hX_ge_N_2D : N_2D ≤ X :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hXge))
  have hX_ge_N_R2 : N_R2 ≤ X :=
    (le_max_left _ _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hXge)))
  have hX_ge_N_loglog : N_loglog ≤ X :=
    (le_max_right _ _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hXge)))
  have hX_ge_N_central : N_central ≤ X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hXge))
  have hq_pos : 0 < q := hq.pos
  have hq_two_le : 2 ≤ q := hq.two_le
  have hq_le_X : q ≤ X := by
    have : q ≤ q * q := Nat.le_mul_of_pos_left q hq_pos
    have h2 : q * q ≤ 2 * q * q := by linarith [Nat.mul_le_mul_right (q*q) (show 1 ≤ 2 from by norm_num)]
    linarith [this, h2, hX_ge_2qq]
  have hD_eq_2R : D = 2 * R := by
    rw [hR_def, hD_def]
    have heq : 1000 * q * H * (Nat.log 2 (2 * X) + 1) =
        2 * (500 * q * H * (Nat.log 2 (2 * X) + 1)) := by ring
    omega
  have hL_eq : L = Nat.log 2 X + 2 := by
    rw [hL_def]
    have h_2X : 2 * X = X * 2 := by ring
    rw [h_2X]
    have := Nat.log_mul_base (b := 2) (n := X) (by norm_num) (by omega)
    omega
  have hL_le_2M : L ≤ 2 * (Nat.log 2 X + 1) := by rw [hL_eq]; omega
  have hL_pow_bd : L ^ (r + 2) ≤ 2^(r+2) * (Nat.log 2 X + 1)^(r+2) := by
    calc L ^ (r + 2) ≤ (2 * (Nat.log 2 X + 1)) ^ (r + 2) :=
          Nat.pow_le_pow_left hL_le_2M _
      _ = 2 ^ (r+2) * (Nat.log 2 X + 1) ^ (r + 2) := by rw [Nat.mul_pow]
  have h_2D_le_X : 2 * D ≤ X := by
    have h1 : 2 * D = 2000 * q * L^(r+2) := by
      rw [hD_def, hH_def, hL_def]; ring
    have h2 : 2000 * q * L^(r+2) ≤ 2000 * q * 2^(r+2) * (Nat.log 2 X + 1)^(r+2) := by
      have hL_bd_mul : 2000 * q * L^(r+2) ≤
          2000 * q * (2^(r+2) * (Nat.log 2 X + 1)^(r+2)) :=
        Nat.mul_le_mul_left _ hL_pow_bd
      have h_eq : 2000 * q * (2^(r+2) * (Nat.log 2 X + 1)^(r+2)) =
          2000 * q * 2^(r+2) * (Nat.log 2 X + 1)^(r+2) := by ring
      linarith
    rw [h1]
    exact h2.trans (hN_2D X hX_ge_N_2D)
  have hD_le_X : D ≤ X := by omega
  have hR_le_X4 : R ≤ X / 4 := by
    rw [hR_def]
    have : D / 2 ≤ X / 4 := by
      have h1 : 2 * D ≤ X := h_2D_le_X
      omega
    exact this
  have hR_lower : 4 * q ≤ R := by
    have hL_ge_1 : 1 ≤ L := Nat.succ_pos _
    have hLpow_ge_1 : 1 ≤ L^(r+2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hD_lower : 1000 * q ≤ D := by
      rw [hD_def, hH_def, hL_def]
      have : H * L = L^(r+2) := by
        rw [hH_def, hL_def]
        ring
      calc 1000 * q = 1000 * q * 1 := by ring
        _ ≤ 1000 * q * L^(r+2) := by
              apply Nat.mul_le_mul_left
              exact hLpow_ge_1
        _ = 1000 * q * H * L := by
              rw [hH_def, hL_def]; ring
    have h1 : 500 * q ≤ D / 2 := by omega
    have h2 : 4 * q ≤ 500 * q := by linarith [Nat.mul_le_mul_right q (show 4 ≤ 500 from by norm_num)]
    rw [hR_def]; omega
  set good_k : Finset ℕ := (Finset.Icc X (2 * X)).filter
    (fun k => q ∣ k ∧ 2 * D ≤ k ∧
      k ∉ smoothFinset (insert q (primesLT m)) k ∧
      (∀ t ∈ smoothFinset (insert q (primesLT m)) k, t ≤ k - D) ∧
      2 * (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) ≤
        ((Finset.Ioc (k - D / 2) k).filter
            (fun p => p.Prime ∧ p % q = 1)).card ∧
      ((smoothFinset (insert q (primesLT m)) (D / 2)).card : ℝ) ≤
        ((10 * ((r : ℝ) + 4)) ^ (r + 1) : ℝ) *
          (Real.log (Real.log k)) ^ (r + 1)) with hgood_k_def
  have h_nonempty : good_k.Nonempty := by
    set P : Finset ℕ := insert q (primesLT m) with hP_def
    set Smooth2X : Finset ℕ := smoothFinset P (2 * X) with hSmooth_def
    set BadWindow : Finset ℕ := Smooth2X.biUnion (fun t => Finset.Ico t (t + D)) with hBW_def
    set Kset : Finset ℕ := (Finset.Icc X (2 * X)).filter (fun k => q ∣ k) with hKset_def
    set Bad : Finset ℕ := Kset.filter (fun k => k ∈ BadWindow) with hBad_def
    set Acount : ℕ → ℕ := fun k =>
      ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card with hAcount_def
    have hKne : Kset.Nonempty := by
      refine ⟨q * (X / q + 1), ?_⟩
      simp only [Kset, Finset.mem_filter, Finset.mem_Icc]
      have hXmod : X % q < q := Nat.mod_lt _ hq_pos
      have hXeq : X = q * (X / q) + X % q := (Nat.div_add_mod X q).symm
      refine ⟨⟨?_, ?_⟩, Dvd.intro _ rfl⟩
      · have h1 : q * (X / q + 1) = q * (X / q) + q := by ring
        omega
      · have h1 : q * (X / q + 1) = q * (X / q) + q := by ring
        have h2 : q * (X / q) ≤ X := Nat.mul_div_le X q
        omega
    have hBadSub : Bad ⊆ Kset := Finset.filter_subset _ _
    have hSmooth_card_le_H : Smooth2X.card ≤ H := by
      have h := smooth_card_at m q (2 * X) hq
      rw [hSmooth_def, hH_def, hL_def]
      rw [← hr_def] at h
      exact h
    have hH_pos : 1 ≤ H := by
      rw [hH_def]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hL_pos : 1 ≤ L := Nat.succ_pos _
    have hR_pos : 1 ≤ R := by
      have : 4 * q ≤ R := hR_lower
      omega
    have hD_pos : 1 ≤ D := by rw [hD_eq_2R]; omega
    have hKset_card_ge : X / q ≤ Kset.card := by
      rw [hKset_def]
      exact Kset_card_lower X q hq_pos hq_le_X
    have hHL_eq : H * L = L ^ (r + 2) := by
      rw [hH_def]
      show L ^ (r + 1) * L = L ^ (r + 2)
      rw [show r + 2 = (r + 1) + 1 from by omega]
      exact (pow_succ L (r + 1)).symm
    have hD_form : D = 1000 * q * L ^ (r + 2) := by
      rw [hD_def]
      have : 1000 * q * H * L = 1000 * q * (H * L) := by ring
      rw [this, hHL_eq]
    have hR_eq : R = 500 * q * L ^ (r + 2) := by
      rw [hR_def, hD_form]
      have h1 : 1000 * q * L ^ (r + 2) = 2 * (500 * q * L ^ (r + 2)) := by ring
      omega
    have h_2qR2_le_X : 2 * q * R^2 ≤ X := by
      have h_pow_eq : (L ^ (r + 2))^2 = L^(2*r+4) := by
        rw [← pow_mul]
        congr 1
        ring
      have h2qR2_eq : 2 * q * R^2 = 500000 * q^3 * L^(2*r+4) := by
        rw [hR_eq]
        have : 2 * q * (500 * q * L^(r+2))^2 = 500000 * q^3 * (L^(r+2))^2 := by ring
        rw [this, h_pow_eq]
      have hL2pow : L^(2*r+4) ≤ 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := by
        calc L^(2*r+4) ≤ (2 * (Nat.log 2 X + 1))^(2*r+4) :=
                Nat.pow_le_pow_left hL_le_2M _
          _ = 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := by rw [Nat.mul_pow]
      have h1 : 500000 * q^3 * L^(2*r+4) ≤
          1000000 * q^3 * 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := by
        have h_le1 : 500000 * q^3 * L^(2*r+4) ≤ 500000 * q^3 * (2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4)) :=
          Nat.mul_le_mul_left _ hL2pow
        have h_eq1 : 500000 * q^3 * (2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4)) =
            500000 * q^3 * 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := by ring
        have h_le2 : 500000 * q^3 * 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) ≤
            1000000 * q^3 * 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := by
          have : 500000 * q^3 * 2^(2*r+4) ≤ 1000000 * q^3 * 2^(2*r+4) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
          exact Nat.mul_le_mul_right _ this
        linarith [h_le1, h_eq1, h_le2]
      calc 2 * q * R^2 = 500000 * q^3 * L^(2*r+4) := h2qR2_eq
        _ ≤ 1000000 * q^3 * 2^(2*r+4) * (Nat.log 2 X + 1)^(2*r+4) := h1
        _ ≤ X := hN_R2 X hX_ge_N_R2
    have h_2R2_le_Xq : 2 * R^2 ≤ X / q := by
      rw [Nat.le_div_iff_mul_le hq_pos]
      have : 2 * R^2 * q = 2 * q * R^2 := by ring
      rw [this]
      exact h_2qR2_le_X
    have h_2R2_le_Kset : 2 * R^2 ≤ Kset.card := h_2R2_le_Xq.trans hKset_card_ge
    have hBadWindow_card : BadWindow.card ≤ Smooth2X.card * D := by
      rw [hBW_def]
      have h_D_eq_2R : D = 2 * R := hD_eq_2R
      have h := bad_count_le P X R
      rw [← h_D_eq_2R] at h
      exact h
    have hBad_card : Bad.card ≤ BadWindow.card := by
      apply Finset.card_le_card
      intro k hk
      rw [hBad_def, Finset.mem_filter] at hk
      exact hk.2
    have h_Acount_le_R : ∀ k, Acount k ≤ R := by
      intro k
      rw [hAcount_def]
      exact Acount_le_R q R k
    have hBadSum : (∑ k ∈ Bad, Acount k) ≤ H * Kset.card := by
      calc (∑ k ∈ Bad, Acount k) ≤ (∑ _k ∈ Bad, R) :=
              Finset.sum_le_sum (fun k _ => h_Acount_le_R k)
        _ = Bad.card * R := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ BadWindow.card * R := Nat.mul_le_mul_right _ hBad_card
        _ ≤ (Smooth2X.card * D) * R := Nat.mul_le_mul_right _ hBadWindow_card
        _ = Smooth2X.card * (D * R) := by ring
        _ ≤ H * (D * R) := Nat.mul_le_mul_right _ hSmooth_card_le_H
        _ = H * (2 * R * R) := by rw [hD_eq_2R]
        _ = H * (2 * R^2) := by ring
        _ ≤ H * Kset.card := Nat.mul_le_mul_left _ h_2R2_le_Kset
    have hKset_upper : Kset.card ≤ X / q + 2 := by
      rw [hKset_def]; exact Kset_card_upper X q hq_pos
    have hRq_eq : R / (2 * q) = 250 * H * L := by
      rw [hR_eq]
      have h_2q_pos : 0 < 2 * q := by omega
      have h_eq : 500 * q * L^(r+2) = (2 * q) * (250 * L^(r+2)) := by ring
      rw [h_eq, Nat.mul_div_cancel_left _ h_2q_pos]
      rw [show L^(r+2) = H * L from hHL_eq.symm]
      ring
    have hP_real := hN_central X R hX_ge_N_central hR_le_X4
    set P_card : ℕ := ((Finset.Ioc X (2 * X - R)).filter
        (fun p => p.Prime ∧ p % q = 1)).card with hP_card_def
    have h_log_2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h_log_2_le_1 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9; linarith
    have hX_real_pos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have h2X_real_pos : (0 : ℝ) < 2 * (X : ℝ) := by linarith
    have h_log_2X_lt : Real.log (2 * (X : ℝ)) < ((L : ℕ) : ℝ) := by
      have h_lt_pow : 2 * X < 2 ^ (Nat.log 2 (2 * X) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (2 * X)
      have h_real_lt : (2 * X : ℝ) < (2 : ℝ) ^ (Nat.log 2 (2 * X) + 1) := by
        exact_mod_cast h_lt_pow
      have h_log_lt : Real.log (2 * (X : ℝ)) <
          Real.log ((2 : ℝ) ^ (Nat.log 2 (2 * X) + 1)) := by
        have h_eq : Real.log (2 * (X : ℝ)) = Real.log ((2 * X : ℕ) : ℝ) := by push_cast; rfl
        rw [h_eq]
        apply Real.log_lt_log
        · exact_mod_cast (by omega : (0 : ℕ) < 2 * X)
        · push_cast; exact h_real_lt
      rw [Real.log_pow] at h_log_lt
      have h_log_2_nn : (0 : ℝ) ≤ Real.log 2 := h_log_2_pos.le
      have h_step : ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) * Real.log 2 ≤
          ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) := by
        have h_nn : (0 : ℝ) ≤ ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) := by positivity
        nlinarith
      have h_cast_eq :
          ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) = ((Nat.log 2 (2 * X) + 1 : ℝ)) := by push_cast; ring
      have h_L_eq : ((L : ℕ) : ℝ) = ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) := by
        rw [hL_def]
      rw [h_L_eq]
      calc Real.log (2 * (X : ℝ)) < ((Nat.log 2 (2 * X) + 1) : ℕ) * Real.log 2 := by
            push_cast at h_log_lt ⊢; linarith
        _ ≤ ((Nat.log 2 (2 * X) + 1 : ℕ) : ℝ) := h_step
    have h_log_2X_le_L : Real.log (2 * (X : ℝ)) ≤ (L : ℝ) := by
      have : ((L : ℕ) : ℝ) = (L : ℝ) := by push_cast; ring
      linarith [h_log_2X_lt, this]
    have hq_minus_one_pos : 0 < q - 1 := by omega
    have h_log_2X_pos : 0 < Real.log (2 * (X : ℝ)) := by
      apply Real.log_pos
      have : (1 : ℝ) < 2 := by norm_num
      have h2X_real_ge : (2 : ℝ) ≤ 2 * X := by
        have : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
        linarith
      linarith
    have hq_real : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq_two_le
      linarith
    have h_denom_pos : (0 : ℝ) < 8 * ((q - 1 : ℝ) * Real.log (2 * X)) := by
      positivity
    have h_X_le_real : (X : ℝ) ≤ 8 * (q - 1 : ℝ) * Real.log (2 * X) * P_card := by
      have h_mul := mul_le_mul_of_nonneg_right hP_real h_denom_pos.le
      have h_div_cancel :
          (X : ℝ) / (8 * ((q - 1 : ℝ) * Real.log (2 * X))) *
            (8 * ((q - 1 : ℝ) * Real.log (2 * X))) = X :=
        div_mul_cancel₀ _ h_denom_pos.ne'
      rw [h_div_cancel] at h_mul
      linarith [h_mul]
    have h_X_le_L_real : (X : ℝ) ≤ 8 * (q - 1 : ℝ) * (L : ℝ) * P_card := by
      have h_q1_nn : (0 : ℝ) ≤ 8 * (q - 1 : ℝ) := by linarith
      have h_P_nn : (0 : ℝ) ≤ (P_card : ℝ) := by positivity
      have h_step1 : 8 * (q - 1 : ℝ) * Real.log (2 * X) * P_card ≤
          8 * (q - 1 : ℝ) * (L : ℝ) * P_card := by
        have h1 : 8 * (q - 1 : ℝ) * Real.log (2 * X) ≤ 8 * (q - 1 : ℝ) * L :=
          mul_le_mul_of_nonneg_left h_log_2X_le_L h_q1_nn
        exact mul_le_mul_of_nonneg_right h1 h_P_nn
      linarith
    have h_X_le_nat : X ≤ 8 * (q - 1) * L * P_card := by
      have h_q_sub_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
      have h_eq : (((8 * (q - 1) * L * P_card : ℕ) : ℝ)) =
          8 * ((q : ℝ) - 1) * L * P_card := by
        push_cast [h_q_sub_cast]; ring
      have h_real : (X : ℝ) ≤ ((8 * (q - 1) * L * P_card : ℕ) : ℝ) := by
        rw [h_eq]; exact h_X_le_L_real
      exact_mod_cast h_real
    have h_X_le_qLP : X ≤ 8 * q * L * P_card := by
      have h_step : 8 * (q - 1) * L * P_card ≤ 8 * q * L * P_card := by
        have hp : 8 * (q - 1) ≤ 8 * q := by omega
        have h_eq1 : 8 * (q - 1) * L * P_card = (8 * (q - 1)) * (L * P_card) := by ring
        have h_eq2 : 8 * q * L * P_card = (8 * q) * (L * P_card) := by ring
        rw [h_eq1, h_eq2]
        exact Nat.mul_le_mul_right (L * P_card) hp
      omega
    have h_Xq_le : X / q ≤ 8 * L * P_card := by
      have h : X ≤ q * (8 * L * P_card) := by
        have h_eq : q * (8 * L * P_card) = 8 * q * L * P_card := by ring
        rw [h_eq]; exact h_X_le_qLP
      exact Nat.div_le_of_le_mul h
    have hP_card_pos : 1 ≤ P_card := by
      by_contra h
      push_neg at h
      have hP_card_zero : P_card = 0 := by omega
      rw [hP_card_zero] at h_X_le_nat
      omega
    have h_LP_pos : 1 ≤ L * P_card := by
      have hL_ge : 1 ≤ L := hL_pos
      have hP_ge : 1 ≤ P_card := hP_card_pos
      calc 1 = 1 * 1 := by ring
        _ ≤ L * P_card := Nat.mul_le_mul hL_ge hP_ge
    have h_HLP_pos : 1 ≤ H * L * P_card := by
      have h_eq : H * L * P_card = H * (L * P_card) := by ring
      rw [h_eq]
      calc 1 = 1 * 1 := by ring
        _ ≤ H * (L * P_card) := Nat.mul_le_mul hH_pos h_LP_pos
    have h_step_A : 8 * H * (X / q + 2) ≤ 80 * H * L * P_card := by
      have h_eq1 : 8 * H * (X / q + 2) = 8 * H * (X / q) + 16 * H := by ring
      have h_step_b : 8 * H * (X / q) ≤ 64 * H * L * P_card := by
        have h_eq2 : 64 * H * L * P_card = 8 * H * (8 * L * P_card) := by ring
        rw [h_eq2]
        exact Nat.mul_le_mul_left (8 * H) h_Xq_le
      have h_step_c : 16 * H ≤ 16 * H * L * P_card := by
        have h_eq3 : 16 * H = 16 * H * 1 := by ring
        calc 16 * H = 16 * H * 1 := h_eq3
          _ ≤ 16 * H * (L * P_card) := Nat.mul_le_mul_left _ h_LP_pos
          _ = 16 * H * L * P_card := by ring
      have h_eq4 : 80 * H * L * P_card = 64 * H * L * P_card + 16 * H * L * P_card := by ring
      rw [h_eq1, h_eq4]
      omega
    have h_step_B : 80 * H * L * P_card ≤ 250 * H * L * P_card := by
      have h_eq5 : 80 * H * L * P_card = 80 * (H * L * P_card) := by ring
      have h_eq6 : 250 * H * L * P_card = 250 * (H * L * P_card) := by ring
      rw [h_eq5, h_eq6]
      exact Nat.mul_le_mul_right _ (by norm_num : 80 ≤ 250)
    have h_main : 8 * H * Kset.card ≤ P_card * (R / (2 * q)) := by
      rw [hRq_eq]
      have h_eq_final : P_card * (250 * H * L) = 250 * H * L * P_card := by ring
      rw [h_eq_final]
      calc 8 * H * Kset.card ≤ 8 * H * (X / q + 2) :=
              Nat.mul_le_mul_left _ hKset_upper
        _ ≤ 80 * H * L * P_card := h_step_A
        _ ≤ 250 * H * L * P_card := h_step_B
    have hsum_raw := sum_Acount_lower q X R hq_pos hR_lower
    have hTotal : 8 * H * Kset.card ≤ ∑ k ∈ Kset, Acount k := by
      refine h_main.trans ?_
      have h_shape : P_card * (R / (2 * q)) =
          ((Finset.Ioc X (2 * X - R)).filter
            (fun p => p.Prime ∧ p % q = 1)).card * (R / (2 * q)) := rfl
      rw [h_shape]
      have h_kset_shape :
          (∑ k ∈ Kset, Acount k) =
          ∑ k ∈ (Finset.Icc X (2 * X)).filter (fun k => q ∣ k),
            ((Finset.Ioc (k - R) k).filter (fun p => p.Prime ∧ p % q = 1)).card := rfl
      rw [h_kset_shape]
      exact hsum_raw
    obtain ⟨k, hkK, hkNotBad, hAk⟩ :=
      exists_good_large_A hH_pos hKne hBadSub hTotal hBadSum
    refine ⟨k, ?_⟩
    rw [hgood_k_def, Finset.mem_filter, Finset.mem_Icc]
    have hkIcc_mem : k ∈ Finset.Icc X (2 * X) := by
      rw [hKset_def, Finset.mem_filter] at hkK; exact hkK.1
    have hkXl : X ≤ k := (Finset.mem_Icc.mp hkIcc_mem).1
    have hk2X : k ≤ 2 * X := (Finset.mem_Icc.mp hkIcc_mem).2
    have hqk_dvd : q ∣ k := by
      rw [hKset_def, Finset.mem_filter] at hkK; exact hkK.2
    refine ⟨⟨hkXl, hk2X⟩, hqk_dvd, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · intro hk_smooth
      apply hkNotBad
      rw [hBad_def, Finset.mem_filter]
      refine ⟨hkK, ?_⟩
      rw [hBW_def, Finset.mem_biUnion]
      refine ⟨k, ?_, ?_⟩
      · rw [hSmooth_def]; exact smoothFinset_mono hk2X hk_smooth
      · rw [Finset.mem_Ico]; exact ⟨le_rfl, by omega⟩
    · intro t ht
      by_contra hnot
      push_neg at hnot
      apply hkNotBad
      rw [hBad_def, Finset.mem_filter]
      refine ⟨hkK, ?_⟩
      rw [hBW_def, Finset.mem_biUnion]
      refine ⟨t, ?_, ?_⟩
      · rw [hSmooth_def]; exact smoothFinset_mono hk2X ht
      · rw [Finset.mem_Ico]
        have ht_le_k : t ≤ k := by
          have := (Finset.mem_filter.mp ht).1
          exact (Finset.mem_Icc.mp this).2
        refine ⟨ht_le_k, ?_⟩
        omega
    · have hDR : D / 2 = R := hR_def.symm
      rw [hDR]
      have h := hAk
      rw [hAcount_def] at h
      convert h using 2
    · have hDR : D / 2 = R := hR_def.symm
      rw [hDR]
      have h_logR_le : ((Nat.log 2 R + 1 : ℕ) : ℝ) ≤
          10 * ((r : ℝ) + 4) * Real.log (Real.log X) := by
        have h_log2_R_eq : Nat.log 2 R = Nat.log 2 (500 * q * L^(r+2)) := by rw [hR_eq]
        rw [h_log2_R_eq]
        exact hN_loglog X hX_ge_N_loglog
      exact smooth_DR_final m q k R X r hq hr_def hkXl (by omega : 4 ≤ X) h_logR_le
  obtain ⟨k, hk_mem⟩ := h_nonempty
  rw [hgood_k_def, Finset.mem_filter, Finset.mem_Icc] at hk_mem
  obtain ⟨⟨hkX, hk2X⟩, hqk, h2Dk, hkT, hTtail, hA, hSm⟩ := hk_mem
  exact ⟨k, D, hkX, hk2X, hqk, h2Dk, hkT, hTtail, hA, hSm⟩

theorem cover_lemma (m : ℕ) (hm : 3 ≤ m) :
    ∃ C_m : ℝ, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ m < k ∧ 4 * m + 4 ≤ k ∧
      ∃ (a : ℕ → ℕ) (q : ℕ), q.Prime ∧ m ≤ q ∧ q ≤ 2 * m - 2 ∧ q ∣ k ∧
        (∀ p, p.Prime → a p < p) ∧
        (∀ p, p.Prime → m ≤ p → p < k → a p < p - k % p) ∧
        (∀ j, 1 ≤ j → j ≤ k →
          ∃ p, p.Prime ∧ m ≤ p ∧ p ≤ k ∧ j % p = a p ∧
            (a p = 0 ∨ p ≤ k / 2 ∨ j ≤ p)) ∧
        ((Finset.Icc m k).filter (fun p => p.Prime ∧ a p ≠ 0)).card ≤
          (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) + 1 ∧
        (((Finset.Icc m k).filter
            (fun p => p.Prime ∧ a p ≠ 0 ∧ 1 ≤ a p ∧ a p ≤ k % p)).card : ℝ) ≤
          C_m * (Real.log (Real.log k)) ^ ((primesLT m).card + 1) ∧
        (∀ p, p.Prime → a p ≠ 0 →
          p = q ∨ (k / 2 < p ∧ p ≤ k ∧ p % q = 1)) := by
  classical
  obtain ⟨q, hq, hmq, hq2m⟩ := exists_prime_ge_le_2m m hm
  obtain ⟨C_m, X₀, hX⟩ := avg_prime_supply m q hm hq hmq
  refine ⟨C_m, fun N => ?_⟩
  set X : ℕ := max X₀ (max (N + 1) (4 * m + 4)) with hXdef
  have hX₀ : X₀ ≤ X := le_max_left _ _
  have hNX : N + 1 ≤ X := by
    calc N + 1 ≤ max (N + 1) (4 * m + 4) := le_max_left _ _
      _ ≤ X := le_max_right _ _
  have hmX : 4 * m + 4 ≤ X := by
    calc 4 * m + 4 ≤ max (N + 1) (4 * m + 4) := le_max_right _ _
      _ ≤ X := le_max_right _ _
  obtain ⟨k, D, hkXl, hkXu, hqk, h2Dk, hkT, hT_tail, hA, hSmoothD⟩ := hX X hX₀
  refine ⟨k, by omega, by omega, by omega, ?_⟩
  set T : Finset ℕ := smoothFinset (insert q (primesLT m)) k with hTdef
  set candidateSet : ↑T → Finset ℕ := fun _ =>
    (Finset.Ioc (k - D / 2) k).filter
      (fun p => p.Prime ∧ p % q = 1) with hcs_def
  have h_T_card_bound : T.card ≤
      (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) := by
    have h1 : T.card ≤ (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) :=
      smooth_card_at m q k hq
    have h2 : Nat.log 2 k ≤ Nat.log 2 (2 * X) := Nat.log_mono_right (by omega)
    calc T.card
        ≤ (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) := h1
      _ ≤ (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) :=
          Nat.pow_le_pow_left (by omega) _
  have h_hall_card : ∀ t : ↑T, Fintype.card ↑T ≤ (candidateSet t).card := by
    intro t
    rw [Fintype.card_coe]
    calc T.card
        ≤ (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) := h_T_card_bound
      _ ≤ 2 * (Nat.log 2 (2 * X) + 1) ^ ((primesLT m).card + 1) := by omega
      _ ≤ (candidateSet t).card := hA
  obtain ⟨f, hf_inj, hf_mem⟩ := hall_from_uniform candidateSet h_hall_card
  have hf_prime : ∀ t : ↑T, (f t).Prime := by
    intro t
    have := hf_mem t
    simp only [candidateSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.2.1
  have hf_mod : ∀ t : ↑T, f t % q = 1 := by
    intro t
    have := hf_mem t
    simp only [candidateSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.2.2
  have hf_le : ∀ t : ↑T, f t ≤ k := by
    intro t
    have := hf_mem t
    simp only [candidateSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.1.2
  have hf_lo : ∀ t : ↑T, k - D / 2 < f t := by
    intro t
    have := hf_mem t
    simp only [candidateSet, Finset.mem_filter, Finset.mem_Ioc] at this
    exact this.1.1
  have h_half_le : 2 * (D / 2) ≤ D := Nat.mul_div_le D 2
  have hf_gt_t : ∀ t : ↑T, t.val < f t := by
    intro t
    have ht_in : t.val ∈ T := t.2
    have ht_bound : t.val ≤ k - D := hT_tail t.val ht_in
    have ht_pos : 1 ≤ t.val :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ht_in).1).1
    have h1 : k - D / 2 < f t := hf_lo t
    omega
  let a : ℕ → ℕ := fun p =>
    if p = q then 1
    else if h : ∃ t : ↑T, f t = p then h.choose.val % p
    else 0
  have ha_def : ∀ p, a p =
      (if p = q then 1
       else if h : ∃ t : ↑T, f t = p then h.choose.val % p else 0) := fun _ => rfl
  refine ⟨a, q, hq, hmq, by omega, hqk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp_prime
    rw [ha_def]
    by_cases hpq : p = q
    · rw [if_pos hpq]; subst hpq; exact hp_prime.one_lt
    · rw [if_neg hpq]
      by_cases hex : ∃ t : ↑T, f t = p
      · rw [dif_pos hex]
        exact Nat.mod_lt _ hp_prime.pos
      · rw [dif_neg hex]
        exact hp_prime.pos
  · intro p hp hmp hpk
    rw [ha_def]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl]
      rw [Nat.mod_eq_zero_of_dvd hqk, Nat.sub_zero]
      exact hp.one_lt
    · rw [if_neg hpq]
      by_cases hex : ∃ t : ↑T, f t = p
      · rw [dif_pos hex]
        set t := hex.choose with ht_def
        have ht_eq : f t = p := hex.choose_spec
        have ht_in : t.val ∈ T := t.2
        have ht_pos : 1 ≤ t.val :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp ht_in).1).1
        have ht_bound : t.val ≤ k - D := hT_tail t.val ht_in
        have h_p_lo : k - D / 2 < p := ht_eq ▸ hf_lo t
        have h_ple : p ≤ k := ht_eq ▸ hf_le t
        have h_t_lt_p : t.val < p := ht_eq ▸ hf_gt_t t
        rw [Nat.mod_eq_of_lt h_t_lt_p]
        have h_k_mod : k % p = k - p := by
          rw [Nat.mod_eq_sub_mod h_ple]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_k_mod]
        omega
      · rw [dif_neg hex]
        have : k % p < p := Nat.mod_lt _ hp.pos
        omega
  · intro j h1j hjk
    classical
    by_cases hB : ∃ t : ↑T, f t ∣ j
    · obtain ⟨t, htdvd⟩ := hB
      have ht_pos : 1 ≤ t.val :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp t.2).1).1
      have ht_bound : t.val ≤ k - D := hT_tail t.val t.2
      have h_lo : k - D / 2 < f t := hf_lo t
      have hj_lt_2ft : j < 2 * f t := by omega
      have hj_eq : j = f t :=
        Nat.eq_of_dvd_of_lt_two_mul (by omega) htdvd hj_lt_2ft
      refine ⟨q, hq, hmq, by omega, ?_, ?_⟩
      · rw [ha_def, if_pos rfl, hj_eq]
        exact hf_mod t
      · right; left
        have hq_le_2m : q ≤ 2 * m - 2 := hq2m
        omega
    · by_cases hjT : j ∈ T
      · let tjcert : ↑T := ⟨j, hjT⟩
        have htjT : tjcert.val ∈ T := tjcert.2
        have htj_bound : tjcert.val ≤ k - D := hT_tail tjcert.val htjT
        have h_ft_gt_q : q < f tjcert := by
          have h1 : k - D / 2 < f tjcert := hf_lo tjcert
          omega
        refine ⟨f tjcert, hf_prime tjcert, by omega, hf_le tjcert, ?_, ?_⟩
        · rw [ha_def]
          have h_ft_neq_q : f tjcert ≠ q := by omega
          rw [if_neg h_ft_neq_q]
          have h_ex : ∃ t' : ↑T, f t' = f tjcert := ⟨tjcert, rfl⟩
          rw [dif_pos h_ex]
          have h_chosen : h_ex.choose = tjcert := hf_inj h_ex.choose_spec
          rw [h_chosen]
        · right; right
          have h_ft_gt_t : tjcert.val < f tjcert := hf_gt_t tjcert
          have htv_eq : tjcert.val = j := rfl
          rw [htv_eq] at h_ft_gt_t
          omega
      · have hjT' : ¬ (j.primeFactors ⊆ insert q (primesLT m)) := by
          intro hsub
          apply hjT
          simp only [T, smoothFinset, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨h1j, hjk⟩, hsub⟩
        obtain ⟨p, hp_pf, hp_notin⟩ := Finset.not_subset.mp hjT'
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
        have hp_dvd : p ∣ j := Nat.dvd_of_mem_primeFactors hp_pf
        have hp_not_q : p ≠ q := by
          intro h; apply hp_notin
          rw [h]; exact Finset.mem_insert_self _ _
        have hp_ge_m : m ≤ p := by
          by_contra h
          apply hp_notin
          apply Finset.mem_insert_of_mem
          exact mem_primesLT.mpr ⟨Nat.lt_of_not_le h, hp_prime⟩
        have hp_le_j : p ≤ j := Nat.le_of_dvd (by omega) hp_dvd
        have hp_le_k : p ≤ k := hp_le_j.trans hjk
        have hp_not_ft : ¬ ∃ t : ↑T, f t = p := by
          rintro ⟨t, hft⟩; apply hB
          exact ⟨t, hft ▸ hp_dvd⟩
        refine ⟨p, hp_prime, hp_ge_m, hp_le_k, ?_, ?_⟩
        · rw [ha_def, if_neg hp_not_q, dif_neg hp_not_ft]
          exact Nat.mod_eq_zero_of_dvd hp_dvd
        · left
          rw [ha_def, if_neg hp_not_q, dif_neg hp_not_ft]
  · let S := (Finset.Icc m k).filter (fun p => p.Prime ∧ a p ≠ 0)
    let S' : Finset ℕ := insert q (T.attach.image (fun t => f t))
    have hS_sub : S ⊆ S' := by
      intro p hp
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hp
      simp only [S', Finset.mem_insert, Finset.mem_image, Finset.mem_attach,
        true_and]
      obtain ⟨⟨_, _⟩, _, hap⟩ := hp
      by_cases hpq : p = q
      · left; exact hpq
      · right
        rw [ha_def, if_neg hpq] at hap
        by_cases hex : ∃ t : ↑T, f t = p
        · obtain ⟨t, hft⟩ := hex
          exact ⟨t, hft⟩
        · rw [dif_neg hex] at hap
          exact absurd rfl hap
    calc S.card ≤ S'.card := Finset.card_le_card hS_sub
      _ ≤ (T.attach.image (fun t => f t)).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ T.attach.card + 1 := Nat.add_le_add_right Finset.card_image_le _
      _ = T.card + 1 := by rw [Finset.card_attach]
      _ ≤ (Nat.log 2 k + 1) ^ ((primesLT m).card + 1) + 1 :=
          Nat.add_le_add_right (smooth_card_at m q k hq) _
  · classical
    let excess := (Finset.Icc m k).filter
      (fun p => p.Prime ∧ a p ≠ 0 ∧ 1 ≤ a p ∧ a p ≤ k % p)
    let smT := smoothFinset (insert q (primesLT m)) (D / 2)
    have h_excess_prop : ∀ p ∈ excess,
        ∃ t : ↑T, f t = p ∧ t.val < D / 2 := by
      intro p hp
      simp only [excess, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨_, _, hap_ne, _, hap_hi⟩ := hp
      have h_p_neq_q : p ≠ q := by
        intro hpeqq; subst hpeqq
        have h_a_eq : a p = 1 := by rw [ha_def, if_pos rfl]
        have h_kmod : k % p = 0 := Nat.mod_eq_zero_of_dvd hqk
        rw [h_a_eq, h_kmod] at hap_hi
        omega
      rw [ha_def, if_neg h_p_neq_q] at hap_ne hap_hi
      by_cases hex : ∃ t : ↑T, f t = p
      · rw [dif_pos hex] at hap_ne hap_hi
        set t := hex.choose
        have hft : f t = p := hex.choose_spec
        have ht_in : t.val ∈ T := t.2
        have ht_pos : 1 ≤ t.val :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp ht_in).1).1
        have ht_bound : t.val ≤ k - D := hT_tail t.val ht_in
        have h_p_lo : k - D / 2 < p := hft ▸ hf_lo t
        have h_p_le : p ≤ k := hft ▸ hf_le t
        have h_t_lt_p : t.val < p := hft ▸ hf_gt_t t
        have h_a_val : t.val % p = t.val := Nat.mod_eq_of_lt h_t_lt_p
        rw [h_a_val] at hap_hi
        have h_k_mod : k % p = k - p := by
          rw [Nat.mod_eq_sub_mod h_p_le]
          exact Nat.mod_eq_of_lt (by omega)
        rw [h_k_mod] at hap_hi
        exact ⟨t, hft, by omega⟩
      · rw [dif_neg hex] at hap_ne
        exact absurd rfl hap_ne
    let g : ℕ → ℕ := fun p =>
      if h : p ∈ excess then (h_excess_prop p h).choose.val else 0
    have h_g_in : ∀ p ∈ excess, g p ∈ smT := by
      intro p hp
      have h_g_eq : g p = (h_excess_prop p hp).choose.val := dif_pos hp
      rw [h_g_eq]
      have hspec := (h_excess_prop p hp).choose_spec
      have ht_in : ((h_excess_prop p hp).choose.val : ℕ) ∈ T :=
        (h_excess_prop p hp).choose.2
      have ht_pos : 1 ≤ ((h_excess_prop p hp).choose.val : ℕ) :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp ht_in).1).1
      have ht_pf : ((h_excess_prop p hp).choose.val : ℕ).primeFactors ⊆
          insert q (primesLT m) :=
        (Finset.mem_filter.mp ht_in).2
      have ht_lt : ((h_excess_prop p hp).choose.val : ℕ) < D / 2 := hspec.2
      simp only [smT, smoothFinset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨ht_pos, by omega⟩, ht_pf⟩
    have h_g_inj : Set.InjOn g excess := by
      intro p hp p' hp' heq
      have h_g_p : g p = (h_excess_prop p hp).choose.val := dif_pos hp
      have h_g_p' : g p' = (h_excess_prop p' hp').choose.val := dif_pos hp'
      rw [h_g_p, h_g_p'] at heq
      have h_eq : (h_excess_prop p hp).choose = (h_excess_prop p' hp').choose :=
        Subtype.ext heq
      have h_spec1 : f (h_excess_prop p hp).choose = p :=
        (h_excess_prop p hp).choose_spec.1
      have h_spec2 : f (h_excess_prop p' hp').choose = p' :=
        (h_excess_prop p' hp').choose_spec.1
      rw [h_eq] at h_spec1
      exact h_spec1.symm.trans h_spec2
    have h_card_le : excess.card ≤ smT.card :=
      Finset.card_le_card_of_injOn g h_g_in h_g_inj
    have h_real : (excess.card : ℝ) ≤ (smT.card : ℝ) := by exact_mod_cast h_card_le
    exact h_real.trans hSmoothD
  · intro p hp hap
    rw [ha_def] at hap
    by_cases hpq : p = q
    · left; exact hpq
    · right
      rw [if_neg hpq] at hap
      by_cases hex : ∃ t : ↑T, f t = p
      · obtain ⟨t, hft⟩ := hex
        have ht_pos : 1 ≤ t.val :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp t.2).1).1
        have ht_bound : t.val ≤ k - D := hT_tail t.val t.2
        have h1 : k - D / 2 < p := hft ▸ hf_lo t
        have h2 : p ≤ k := hft ▸ hf_le t
        have h3 : p % q = 1 := hft ▸ hf_mod t
        exact ⟨by omega, h2, h3⟩
      · rw [dif_neg hex] at hap
        exact absurd rfl hap

end Erdos387
