import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Factorization
import ErdosProblems.Erdos378.HighIndexCentered

open Filter Set
open scoped Topology BigOperators

namespace Erdos378

open HighIndexCentered CircleEquidistribution WeightedCircleEquidistribution

noncomputable section

lemma hi_sub_mod_of_mod_lt {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n)
    (hmod : n % q < k % q) :
    (n - k) % q = q + n % q - k % q := by
  have hle : k % q ≤ q + n % q := by
    have hklt := Nat.mod_lt k hq
    omega
  have hcong : q + n % q - k % q ≡ n - k [MOD q] := by
    apply Nat.ModEq.sub hle hkn
    · change (q + n % q) % q = n % q
      simp
    · exact Nat.mod_modEq k q
  have hcandlt : q + n % q - k % q < q := by omega
  change (q + n % q - k % q) % q = (n - k) % q at hcong
  rw [Nat.mod_eq_of_lt hcandlt] at hcong
  exact hcong.symm

lemma hi_carry_of_mod_lt {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n)
    (hmod : n % q < k % q) :
    q ≤ k % q + (n - k) % q := by
  rw [hi_sub_mod_of_mod_lt hq hkn hmod]
  omega

lemma hi_prime_sq_dvd_choose_of_two_mod_borrows {p n k : ℕ}
    (hp : p.Prime) (hkn : k ≤ n) (hp2n : p ^ 2 ≤ n)
    (h₁ : n % p < k % p) (h₂ : n % (p ^ 2) < k % (p ^ 2)) :
    p ^ 2 ∣ n.choose k := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkn).ne']
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  have hlog : 2 ≤ Nat.log p n :=
    Nat.le_log_of_pow_le hp.one_lt hp2n
  have hsub : ({1, 2} : Finset ℕ) ⊆
      (Finset.Ico 1 (Nat.log p n + 1)).filter
        (fun i ↦ p ^ i ≤ k % p ^ i + (n - k) % p ^ i) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp only [Finset.mem_filter, Finset.mem_Ico, pow_one]
      exact ⟨⟨by omega, by omega⟩, hi_carry_of_mod_lt hp.pos hkn h₁⟩
    · simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩,
        hi_carry_of_mod_lt (pow_pos hp.pos 2) hkn h₂⟩
  have hcard := Finset.card_le_card hsub
  norm_num at hcard ⊢
  exact hcard

lemma hi_no_low_carry_of_prime_sq_near_n {p n k : ℕ}
    (hp : p.Prime) (hhalf : k ≤ n / 2)
    (hlower : n - k < p ^ 2) (hupper : p ^ 2 ≤ n)
    (hsq : Squarefree (n.choose k)) :
    k % p + (n - k) % p < p := by
  have hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hother : k ≤ n - k := by omega
  have hklt : k < p ^ 2 := hother.trans_lt hlower
  by_contra hcarry
  have hlow : n % p < k % p := by
    by_contra hnborrow
    have hsumMod := Nat.add_mod_add_of_le_add_mod (Nat.le_of_not_gt hcarry)
        (a := k) (b := n - k) (c := p)
    rw [show k + (n - k) = n by omega] at hsumMod
    have hnkp : (n - k) % p < p := Nat.mod_lt (n - k) hp.pos
    omega
  have hnlt : n < 2 * p ^ 2 := by omega
  have hnmod : n % (p ^ 2) = n - p ^ 2 := by
    rw [Nat.mod_eq_sub_mod hupper,
      Nat.mod_eq_of_lt (by omega : n - p ^ 2 < p ^ 2)]
  have hhigh : n % (p ^ 2) < k % (p ^ 2) := by
    rw [hnmod, Nat.mod_eq_of_lt hklt]
    omega
  have hdiv := hi_prime_sq_dvd_choose_of_two_mod_borrows
    hp hkn hupper hlow hhigh
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by
    simpa only [pow_two] using hdiv)

def phaseContribution (p n k : ℕ) : ℝ :=
  centeredCoord (reciprocalCirclePoint k p) +
    centeredCoord (reciprocalCirclePoint (n - k) p) -
      centeredCoord (reciprocalCirclePoint n p)

lemma phaseContribution_eq_half_of_no_carry {p n k : ℕ}
    (hp : 0 < p) (hkn : k ≤ n)
    (hpk : ¬p ∣ k) (hpnk : ¬p ∣ n - k) (hpn : ¬p ∣ n)
    (hcarry : k % p + (n - k) % p < p) :
    phaseContribution p n k = 1 / 2 := by
  rw [phaseContribution,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpk,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpnk,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpn]
  have hnmod : n % p = k % p + (n - k) % p := by
    calc
      n % p = (k + (n - k)) % p := by rw [Nat.add_sub_of_le hkn]
      _ = (k % p + (n - k) % p) % p := Nat.add_mod _ _ _
      _ = k % p + (n - k) % p := Nat.mod_eq_of_lt hcarry
  have hnmodR : ((n % p : ℕ) : ℝ) =
      (k % p : ℕ) + ((n - k) % p : ℕ) := by exact_mod_cast hnmod
  rw [hnmodR]
  ring

lemma phaseContribution_eq_neg_half_of_carry {p n k : ℕ}
    (hp : 0 < p) (hkn : k ≤ n)
    (hpk : ¬p ∣ k) (hpnk : ¬p ∣ n - k) (hpn : ¬p ∣ n)
    (hcarry : p ≤ k % p + (n - k) % p) :
    phaseContribution p n k = -(1 / 2) := by
  rw [phaseContribution,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpk,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpnk,
    centeredCoord_reciprocalCirclePoint_of_not_dvd hp hpn]
  have hsumlt : k % p + (n - k) % p < 2 * p := by
    have h₁ := Nat.mod_lt k hp
    have h₂ := Nat.mod_lt (n - k) hp
    omega
  have hnmod : n % p = k % p + (n - k) % p - p := by
    calc
      n % p = (k + (n - k)) % p := by rw [Nat.add_sub_of_le hkn]
      _ = (k % p + (n - k) % p) % p := Nat.add_mod _ _ _
      _ = (k % p + (n - k) % p - p) % p :=
        Nat.mod_eq_sub_mod hcarry
      _ = k % p + (n - k) % p - p := Nat.mod_eq_of_lt (by omega)
  have hnmodR : ((n % p : ℕ) : ℝ) =
      (k % p : ℕ) + ((n - k) % p : ℕ) - p := by exact_mod_cast hnmod
  rw [hnmodR]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]
  ring

lemma phaseContribution_ge_neg_half_of_not_dvd {p n k : ℕ}
    (hp : 0 < p) (hkn : k ≤ n)
    (hpk : ¬p ∣ k) (hpnk : ¬p ∣ n - k) (hpn : ¬p ∣ n) :
    -(1 / 2 : ℝ) ≤ phaseContribution p n k := by
  by_cases hcarry : k % p + (n - k) % p < p
  · rw [phaseContribution_eq_half_of_no_carry hp hkn hpk hpnk hpn hcarry]
    norm_num
  · rw [phaseContribution_eq_neg_half_of_carry hp hkn hpk hpnk hpn
      (Nat.le_of_not_gt hcarry)]

lemma phaseContribution_ge_neg_three_halves (p n k : ℕ) :
    -(3 / 2 : ℝ) ≤ phaseContribution p n k := by
  have h₁ := norm_centeredCoord_le (reciprocalCirclePoint k p)
  have h₂ := norm_centeredCoord_le (reciprocalCirclePoint (n - k) p)
  have h₃ := norm_centeredCoord_le (reciprocalCirclePoint n p)
  rw [Real.norm_eq_abs] at h₁ h₂ h₃
  rcases abs_le.mp h₁ with ⟨h₁, _⟩
  rcases abs_le.mp h₂ with ⟨h₂, _⟩
  rcases abs_le.mp h₃ with ⟨_, h₃⟩
  unfold phaseContribution
  linarith

lemma no_low_carry_of_source_nonexceptional {p n k : ℕ}
    (hp : p.Prime) (hhalf : k ≤ n / 2)
    (hpSource : p ∈ ReciprocalPrimeSelection.sourcePrimeSet k)
    (hfar :
      (HighIndexCutoffs.farSeparation
          (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
        (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 ≤ n)
    (hnonexc : ¬81 * p ^ 2 ≤ 100 * (n % p ^ 2))
    (hsq : Squarefree (n.choose k)) :
    k % p + (n - k) % p < p := by
  have hpMem := Finset.mem_filter.mp hpSource
  have hpIoc := Finset.mem_Ioc.mp hpMem.1
  have hkn : k ≤ n := hhalf.trans (Nat.div_le_self n 2)
  have hsqrtSq : k < (Nat.sqrt k + 1) ^ 2 := by
    simpa only [pow_two] using Nat.lt_succ_sqrt k
  have hkpSq : k < p ^ 2 := by nlinarith
  have hsep : 1 ≤ HighIndexCutoffs.farSeparation
      (ReciprocalPrimeSelection.sourcePrimeUpper k) := by
    exact HighIndexCutoffs.logPowerCutoff_pos 8 _
  have hp2n : p ^ 2 ≤ n := by
    have hpUpperSq : p ^ 2 ≤
        ReciprocalPrimeSelection.sourcePrimeUpper k ^ 2 := by
      gcongr
      exact hpIoc.2
    have hnat : ReciprocalPrimeSelection.sourcePrimeUpper k ^ 2 ≤ n := by
      have hfarR :
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 ≤ (n : ℝ) := by
        have hsepR : (1 : ℝ) ≤ HighIndexCutoffs.farSeparation
            (ReciprocalPrimeSelection.sourcePrimeUpper k) := by exact_mod_cast hsep
        have hsepSq : (1 : ℝ) ≤
            (HighIndexCutoffs.farSeparation
              (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 := by
          nlinarith [sq_nonneg
            ((HighIndexCutoffs.farSeparation
              (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) - 1)]
        calc
          (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 ≤
              (HighIndexCutoffs.farSeparation
                (ReciprocalPrimeSelection.sourcePrimeUpper k) : ℝ) ^ 2 *
                (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ) ^ 2 := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hsepSq
              (sq_nonneg (ReciprocalPrimeSelection.sourcePrimeUpper k : ℝ))
          _ ≤ (n : ℝ) := hfar
      exact_mod_cast hfarR
    exact hpUpperSq.trans hnat
  have hhigh : n % (p ^ 2) < k % (p ^ 2) := by
    rw [Nat.mod_eq_of_lt hkpSq]
    have hsourceSize : 81 * p ^ 2 ≤ 100 * k := by
      have hpUpper := hpIoc.2
      have hs : Nat.sqrt k ^ 2 ≤ k := by
        simpa only [pow_two] using Nat.sqrt_le k
      have h9u : 9 * ReciprocalPrimeSelection.sourcePrimeUpper k ≤
          10 * Nat.sqrt k := by
        unfold ReciprocalPrimeSelection.sourcePrimeUpper
        omega
      nlinarith
    omega
  by_contra hcarry
  have hcarry' : p ≤ k % p + (n - k) % p := Nat.le_of_not_gt hcarry
  have hsumlt : k % p + (n - k) % p < 2 * p := by
    have h₁ := Nat.mod_lt k hp.pos
    have h₂ := Nat.mod_lt (n - k) hp.pos
    omega
  have hlow : n % p < k % p := by
    have hnmod : n % p = k % p + (n - k) % p - p := by
      calc
        n % p = (k + (n - k)) % p := by rw [Nat.add_sub_of_le hkn]
        _ = (k % p + (n - k) % p) % p := Nat.add_mod _ _ _
        _ = (k % p + (n - k) % p - p) % p :=
          Nat.mod_eq_sub_mod hcarry'
        _ = k % p + (n - k) % p - p := Nat.mod_eq_of_lt (by omega)
    have hother := Nat.mod_lt (n - k) hp.pos
    omega
  have hdiv := hi_prime_sq_dvd_choose_of_two_mod_borrows
    hp hkn hp2n hlow hhigh
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) (by
    simpa only [pow_two] using hdiv)

def divisorUnionLogMass (s : Finset ℕ) (n k : ℕ) : ℝ :=
  ∑ p ∈ s.filter (fun p ↦ p ∣ k ∨ p ∣ n - k ∨ p ∣ n), Real.log (p : ℝ)

lemma divisorUnionLogMass_le (s : Finset ℕ) (n k : ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    divisorUnionLogMass s n k ≤
      divisorPrimeLogMass s k + divisorPrimeLogMass s (n - k) +
        divisorPrimeLogMass s n := by
  unfold divisorUnionLogMass divisorPrimeLogMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hs p hp).one_lt.le)
  split_ifs <;> aesop

lemma sum_weight_phase_lower
    {α : Type*} [DecidableEq α] (s : Finset α)
    (w f : α → ℝ) (E D : α → Prop)
    [DecidablePred E] [DecidablePred D]
    (hw : ∀ p ∈ s, 0 ≤ w p)
    (hED : ∀ p ∈ s, E p → ¬D p)
    (hgood : ∀ p ∈ s, ¬E p → ¬D p → f p = 1 / 2)
    (hmid : ∀ p ∈ s, ¬D p → -(1 / 2 : ℝ) ≤ f p)
    (hall : ∀ p ∈ s, -(3 / 2 : ℝ) ≤ f p) :
    (∑ p ∈ s, w p) / 2 -
        (∑ p ∈ s.filter E, w p) -
        2 * (∑ p ∈ s.filter D, w p) ≤
      ∑ p ∈ s, w p * f p := by
  classical
  have hpoint : ∀ p ∈ s,
      w p / 2 - (if E p then w p else 0) -
          2 * (if D p then w p else 0) ≤ w p * f p := by
    intro p hp
    by_cases hD : D p
    · simp only [if_pos hD]
      by_cases hE : E p
      · exact False.elim ((hED p hp hE) hD)
      · simp only [if_neg hE]
        nlinarith [mul_le_mul_of_nonneg_left (hall p hp) (hw p hp)]
    · simp only [if_neg hD]
      by_cases hE : E p
      · simp only [if_pos hE]
        nlinarith [mul_le_mul_of_nonneg_left (hmid p hp hD) (hw p hp)]
      · simp only [if_neg hE, hgood p hp hE hD]
        simp only [mul_zero, sub_zero]
        rw [div_eq_mul_inv]
        norm_num
  calc
    (∑ p ∈ s, w p) / 2 - (∑ p ∈ s.filter E, w p) -
          2 * (∑ p ∈ s.filter D, w p) =
        ∑ p ∈ s, (w p / 2 - (if E p then w p else 0) -
          2 * (if D p then w p else 0)) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_div,
        Finset.mul_sum]
    _ ≤ ∑ p ∈ s, w p * f p := Finset.sum_le_sum hpoint

lemma sum_phaseContribution_eq (a b n k : ℕ) :
    (∑ p ∈ primeIntervalSet a b,
        Real.log (p : ℝ) * phaseContribution p n k) =
      centeredReciprocalPrimeSum a b k +
        centeredReciprocalPrimeSum a b (n - k) -
          centeredReciprocalPrimeSum a b n := by
  unfold phaseContribution centeredReciprocalPrimeSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

lemma abs_add_sub_lt_three_div_thousand {A B C W : ℝ}
    (hA : |A| < W / 1000) (hB : |B| < W / 1000)
    (hC : |C| < W / 1000) :
    |A + B - C| < 3 * W / 1000 := by
  calc
    |A + B - C| ≤ |A + B| + |C| := abs_sub _ _
    _ ≤ |A| + |B| + |C| := by gcongr; exact abs_add_le _ _
    _ < 3 * W / 1000 := by linarith

theorem eventually_high_index_squarefree_impossible :
    ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      k ≤ n / 2 →
      n ≤ ReciprocalPrimeSelection.sourcePrimeUpper k ^ 15 →
      ¬ Squarefree (n.choose k) := by
  have hsTop : Tendsto (fun k : ℕ ↦ Nat.sqrt k) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    exact ⟨B ^ 2, fun k hk ↦ Nat.le_sqrt'.mpr hk⟩
  rcases (eventually_const_mul_log_pow_le 1000000 (by norm_num) 1
      ).exists_forall_of_atTop with ⟨S₁, hS₁⟩
  rcases (eventually_const_mul_log_pow_le 1000000000000 (by norm_num) 17
      ).exists_forall_of_atTop with ⟨S₁₇, hS₁₇⟩
  filter_upwards [eventually_source_centered_small,
    eventually_near_centered_small,
    eventually_exceptionalPrimeLogMass_lt,
    ReciprocalPrimeSelection.eventually_sourcePrimeLogMass_lower,
    eventually_near_primeLogMass_lower_uniform,
    hsTop.eventually (eventually_ge_atTop (max 100 (max S₁ S₁₇)))] with
      k hsource hnearCenter hexception hsourceMass hnearMass hsLarge
  intro n hhalf hn15 hsq
  let s := Nat.sqrt k
  let u := ReciprocalPrimeSelection.sourcePrimeUpper k
  let H := HighIndexCutoffs.farSeparation u
  have hs100 : 100 ≤ s := (le_max_left _ _).trans hsLarge
  have hS₁s : S₁ ≤ s :=
    (le_max_left S₁ S₁₇).trans ((le_max_right 100 _).trans hsLarge)
  have hS₁₇s : S₁₇ ≤ s :=
    (le_max_right S₁ S₁₇).trans ((le_max_right 100 _).trans hsLarge)
  have hkpos : 0 < k := by
    have hsSq : s ^ 2 ≤ k := by
      simpa only [s, pow_two] using Nat.sqrt_le k
    nlinarith
  have h2kn : 2 * k ≤ n := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hhalf
  have hkn : k ≤ n := by omega
  have hkSub : k ≤ n - k := by omega
  have hnpos : 0 < n := hkpos.trans_le hkn
  have hsubpos : 0 < n - k := hkpos.trans_le hkSub
  by_cases hfar : (H : ℝ) ^ 2 * (u : ℝ) ^ 2 ≤ n
  · let P := ReciprocalPrimeSelection.sourcePrimeSet k
    let W := ReciprocalPrimeSelection.sourcePrimeLogMass k
    let D : ℕ → Prop := fun p ↦ p ∣ k ∨ p ∣ n - k ∨ p ∣ n
    let E : ℕ → Prop := fun p ↦
      p ∈ InverseSquareExceptionalArc.exceptionalPrimeSet n k ∧ ¬D p
    have hPu : P = primeIntervalSet s u := rfl
    have hprime : ∀ p ∈ P, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hw : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := by
      intro p hp
      exact Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)
    have hED : ∀ p ∈ P, E p → ¬D p := fun p hp hE ↦ hE.2
    have hgood : ∀ p ∈ P, ¬E p → ¬D p →
        phaseContribution p n k = 1 / 2 := by
      intro p hp hE hD
      have hpPrime := hprime p hp
      have hpNotExc :
          p ∉ InverseSquareExceptionalArc.exceptionalPrimeSet n k := by
        intro hpExc
        exact hE ⟨hpExc, hD⟩
      have hnonexc : ¬81 * p ^ 2 ≤ 100 * (n % p ^ 2) := by
        intro hbad
        apply hpNotExc
        rw [InverseSquareExceptionalArc.exceptionalPrimeSet,
          Finset.mem_filter]
        exact ⟨hp, hbad⟩
      have hcarry := no_low_carry_of_source_nonexceptional hpPrime hhalf hp hfar
        hnonexc hsq
      exact phaseContribution_eq_half_of_no_carry hpPrime.pos hkn
        (fun hd ↦ hD (Or.inl hd))
        (fun hd ↦ hD (Or.inr (Or.inl hd)))
        (fun hd ↦ hD (Or.inr (Or.inr hd))) hcarry
    have hmid : ∀ p ∈ P, ¬D p →
        -(1 / 2 : ℝ) ≤ phaseContribution p n k := by
      intro p hp hD
      exact phaseContribution_ge_neg_half_of_not_dvd (hprime p hp).pos hkn
        (fun hd ↦ hD (Or.inl hd))
        (fun hd ↦ hD (Or.inr (Or.inl hd)))
        (fun hd ↦ hD (Or.inr (Or.inr hd)))
    have hall : ∀ p ∈ P, -(3 / 2 : ℝ) ≤ phaseContribution p n k :=
      fun p hp ↦ phaseContribution_ge_neg_three_halves p n k
    have hlower := sum_weight_phase_lower P
      (fun p ↦ Real.log (p : ℝ)) (fun p ↦ phaseContribution p n k) E D
      hw hED hgood hmid hall
    have hEmass : (∑ p ∈ P.filter E, Real.log (p : ℝ)) ≤
        InverseSquareExceptionalArc.exceptionalPrimeLogMass n k := by
      unfold InverseSquareExceptionalArc.exceptionalPrimeLogMass
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact hp'.2.1
      · intro p hp hpnot
        exact Real.log_nonneg (by
          exact_mod_cast ((Finset.mem_filter.mp
            (Finset.mem_filter.mp hp).1).2).one_lt.le)
    have hDmass : (∑ p ∈ P.filter D, Real.log (p : ℝ)) ≤
        divisorPrimeLogMass P k + divisorPrimeLogMass P (n - k) +
          divisorPrimeLogMass P n := by
      exact divisorUnionLogMass_le P n k hprime
    have hsourceEach (X : ℕ) (hXpos : 0 < X) (hXu : X ≤ u ^ 15) :
        divisorPrimeLogMass P X ≤ 30 * Real.log (s : ℝ) := by
      have hdiv := divisorPrimeLogMass_le_log hXpos hprime
      have hu2s : u ≤ 2 * s := by
        dsimp only [u, s, ReciprocalPrimeSelection.sourcePrimeUpper]
        omega
      have h2sSq : 2 * s ≤ s ^ 2 := by nlinarith
      have hXuR : (X : ℝ) ≤ (u : ℝ) ^ 15 := by exact_mod_cast hXu
      have huR : (0 : ℝ) < u := by
        exact_mod_cast (show 0 < u by
          dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper, s]
          omega)
      have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
      have hlogX := Real.log_le_log hXR hXuR
      rw [Real.log_pow] at hlogX
      have husSq : u ≤ s ^ 2 := hu2s.trans h2sSq
      have husSqR : (u : ℝ) ≤ (s : ℝ) ^ 2 := by exact_mod_cast husSq
      have hlogu := Real.log_le_log huR husSqR
      rw [Real.log_pow] at hlogu
      norm_num at hlogu
      push_cast at hlogX
      linarith
    have hDsmall : divisorPrimeLogMass P k +
        divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n < W / 100 := by
      have hdk := hsourceEach k hkpos (hkn.trans hn15)
      have hdnk := hsourceEach (n - k) hsubpos (Nat.sub_le n k |>.trans hn15)
      have hdn := hsourceEach n hnpos hn15
      have hgrowth := hS₁ s hS₁s
      have hmass : (s : ℝ) / 20 ≤ W := hsourceMass
      have hlogpos : 0 < Real.log (s : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < s by omega))
      have hDle : divisorPrimeLogMass P k +
          divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n ≤
            90 * Real.log (s : ℝ) := by linarith
      norm_num [pow_one] at hgrowth
      have hGW : 50000 * Real.log (s : ℝ) ≤ W := by nlinarith
      have hstrict : 100 * (divisorPrimeLogMass P k +
          divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n) < W := by
        nlinarith
      nlinarith
    have hExc := hexception n hkn hfar hn15
    have hlower' : W / 2 - (43 / 100 : ℝ) * W - 2 * (W / 100) <
        ∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k := by
      have hPmass : (∑ p ∈ P, Real.log (p : ℝ)) = W := rfl
      rw [hPmass] at hlower
      exact lt_of_lt_of_le (by
        dsimp only [W]
        nlinarith [hEmass.trans_lt hExc, hDmass.trans_lt hDsmall]) hlower
    have hkU : k ≤ u ^ 15 := hkn.trans hn15
    have hnkU : n - k ≤ u ^ 15 := (Nat.sub_le n k).trans hn15
    have hkC := hsource k le_rfl hkU
    have hnkC := hsource (n - k) hkSub hnkU
    have hnC := hsource n hkn hn15
    have hupper := abs_add_sub_lt_three_div_thousand hkC hnkC hnC
    have hsumEq := sum_phaseContribution_eq s u n k
    rw [← hsumEq] at hupper
    have hmassPos : 0 < W := by
      have : 0 < (s : ℝ) / 20 := by positivity
      exact this.trans_le hsourceMass
    have habsLower :
        ∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k ≤
          |∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k| :=
      le_abs_self _
    rw [hPu] at hlower' habsLower
    nlinarith
  · have hnearCond : (n : ℝ) < (H : ℝ) ^ 2 * (u : ℝ) ^ 2 :=
      lt_of_not_ge hfar
    let x := Nat.sqrt (n - k)
    let y := Nat.sqrt n
    let P := primeIntervalSet x y
    let W := primeIntervalLogMass x y
    let D : ℕ → Prop := fun p ↦ p ∣ k ∨ p ∣ n - k ∨ p ∣ n
    let E : ℕ → Prop := fun _p ↦ False
    have hyS : s ≤ y := Nat.sqrt_le_sqrt hkn
    have hy100 : 100 ≤ y := hs100.trans hyS
    have hS₁₇y : S₁₇ ≤ y := hS₁₇s.trans hyS
    have hySq : y ^ 2 ≤ n := by
      simpa only [y, pow_two] using Nat.sqrt_le n
    have hnUpper : n < (y + 1) ^ 2 := by
      simpa only [y, pow_two] using Nat.lt_succ_sqrt n
    have hyBase : y + 1 ≤ y ^ 2 := by nlinarith
    have hyFour : (y + 1) ^ 2 ≤ y ^ 4 := by
      calc
        (y + 1) ^ 2 ≤ (y ^ 2) ^ 2 := by gcongr
        _ = y ^ 4 := by ring
    have hyPow : y ^ 4 ≤ y ^ 15 := by
      calc
        y ^ 4 = y ^ 4 * 1 := by simp
        _ ≤ y ^ 4 * y ^ 11 :=
          Nat.mul_le_mul_left _ (one_le_pow₀ (by omega : 1 ≤ y))
        _ = y ^ 15 := by ring
    have hnY : n ≤ y ^ 15 := hnUpper.le.trans (hyFour.trans hyPow)
    have hprime : ∀ p ∈ P, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hw : ∀ p ∈ P, 0 ≤ Real.log (p : ℝ) := by
      intro p hp
      exact Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)
    have hED : ∀ p ∈ P, E p → ¬D p := by simp [E]
    have hgood : ∀ p ∈ P, ¬E p → ¬D p →
        phaseContribution p n k = 1 / 2 := by
      intro p hp hE hD
      have hpMem := Finset.mem_filter.mp hp
      have hpIoc := Finset.mem_Ioc.mp hpMem.1
      have hpPrime := hpMem.2
      have hlower : n - k < p ^ 2 := by
        have hxUpper : n - k < (x + 1) ^ 2 := by
          simpa only [x, pow_two] using Nat.lt_succ_sqrt (n - k)
        have hxp : x + 1 ≤ p := by omega
        exact hxUpper.trans_le (by gcongr)
      have hupper : p ^ 2 ≤ n := by
        have hpY : p ^ 2 ≤ y ^ 2 := by
          gcongr
          exact hpIoc.2
        exact hpY.trans hySq
      have hcarry := hi_no_low_carry_of_prime_sq_near_n hpPrime hhalf
        hlower hupper hsq
      exact phaseContribution_eq_half_of_no_carry hpPrime.pos hkn
        (fun hd ↦ hD (Or.inl hd))
        (fun hd ↦ hD (Or.inr (Or.inl hd)))
        (fun hd ↦ hD (Or.inr (Or.inr hd))) hcarry
    have hmid : ∀ p ∈ P, ¬D p →
        -(1 / 2 : ℝ) ≤ phaseContribution p n k := by
      intro p hp hD
      exact phaseContribution_ge_neg_half_of_not_dvd (hprime p hp).pos hkn
        (fun hd ↦ hD (Or.inl hd))
        (fun hd ↦ hD (Or.inr (Or.inl hd)))
        (fun hd ↦ hD (Or.inr (Or.inr hd)))
    have hall : ∀ p ∈ P, -(3 / 2 : ℝ) ≤ phaseContribution p n k :=
      fun p hp ↦ phaseContribution_ge_neg_three_halves p n k
    have hlower := sum_weight_phase_lower P
      (fun p ↦ Real.log (p : ℝ)) (fun p ↦ phaseContribution p n k) E D
      hw hED hgood hmid hall
    have hDmass : (∑ p ∈ P.filter D, Real.log (p : ℝ)) ≤
        divisorPrimeLogMass P k + divisorPrimeLogMass P (n - k) +
          divisorPrimeLogMass P n := by
      exact divisorUnionLogMass_le P n k hprime
    have hnearEach (X : ℕ) (hXpos : 0 < X) (hXn : X ≤ n) :
        divisorPrimeLogMass P X ≤ 15 * Real.log (y : ℝ) := by
      have hdiv := divisorPrimeLogMass_le_log hXpos hprime
      have hXY : X ≤ y ^ 15 := hXn.trans hnY
      have hXYR : (X : ℝ) ≤ (y : ℝ) ^ 15 := by exact_mod_cast hXY
      have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
      have hlogX := Real.log_le_log hXR hXYR
      rw [Real.log_pow] at hlogX
      push_cast at hlogX
      linarith
    have hDsmall : divisorPrimeLogMass P k +
        divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n < W / 100 := by
      have hdk := hnearEach k hkpos hkn
      have hdnk := hnearEach (n - k) hsubpos (Nat.sub_le n k)
      have hdn := hnearEach n hnpos le_rfl
      have hgrowth := hS₁₇ y hS₁₇y
      have hmass : (y : ℝ) /
          (100000000 * Real.log (y : ℝ) ^ 16) ≤ W :=
        hnearMass n hhalf hnearCond
      have hlogpos : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      have hdenpos : 0 < 100000000 * Real.log (y : ℝ) ^ 16 := by positivity
      have hratio : 10000 * Real.log (y : ℝ) ≤
          (y : ℝ) / (100000000 * Real.log (y : ℝ) ^ 16) := by
        calc
          10000 * Real.log (y : ℝ) =
              (1000000000000 * Real.log (y : ℝ) ^ 17) /
                (100000000 * Real.log (y : ℝ) ^ 16) := by
                  field_simp
                  ring
          _ ≤ (y : ℝ) /
                (100000000 * Real.log (y : ℝ) ^ 16) := by
                  exact div_le_div_of_nonneg_right hgrowth hdenpos.le
      have hGW : 10000 * Real.log (y : ℝ) ≤ W := hratio.trans hmass
      have hDle : divisorPrimeLogMass P k +
          divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n ≤
            45 * Real.log (y : ℝ) := by linarith
      have hstrict : 100 * (divisorPrimeLogMass P k +
          divisorPrimeLogMass P (n - k) + divisorPrimeLogMass P n) < W := by
        nlinarith
      nlinarith
    have hlower' : W / 2 - 2 * (W / 100) <
        ∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k := by
      have hPmass : (∑ p ∈ P, Real.log (p : ℝ)) = W := rfl
      have hEmass : (∑ p ∈ P.filter E, Real.log (p : ℝ)) = 0 := by
        simp [E]
      rw [hPmass, hEmass, sub_zero] at hlower
      exact lt_of_lt_of_le (by nlinarith [hDmass.trans_lt hDsmall]) hlower
    have hkC := hnearCenter n k hhalf hnearCond le_rfl hkn
    have hnkC := hnearCenter n (n - k) hhalf hnearCond hkSub
      (Nat.sub_le n k)
    have hnC := hnearCenter n n hhalf hnearCond hkn le_rfl
    have hupper := abs_add_sub_lt_three_div_thousand hkC hnkC hnC
    have hsumEq := sum_phaseContribution_eq x y n k
    rw [← hsumEq] at hupper
    have hmassPos : 0 < W := by
      have hlogpos : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      have hleft : 0 < (y : ℝ) /
          (100000000 * Real.log (y : ℝ) ^ 16) := by positivity
      exact hleft.trans_le (hnearMass n hhalf hnearCond)
    have habsLower :
        ∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k ≤
          |∑ p ∈ P, Real.log (p : ℝ) * phaseContribution p n k| :=
      le_abs_self _
    nlinarith

end
end Erdos378
