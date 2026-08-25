import Mathlib

/-!
# Coprime counts in a residue class

The inclusion–exclusion argument from the original Erdős 1141 proof,
generalized to any nonzero progression modulus coprime to the integer being sieved.
-/

open scoped BigOperators
open Finset Real

namespace Erdos1141.Sieve

private lemma mem_finset_inf_iff {ι α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ι} {f : ι → Finset α} {a : α} :
    a ∈ s.inf f ↔ ∀ i ∈ s, a ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      simp [Finset.inf_insert, ih]

private lemma count_root_class_with_divisors
    {n p r K : ℕ} (_hp : p ≠ 0) (_hn0 : n ≠ 0) (hpn : p.Coprime n)
    (t : Finset ℕ) (ht : t ⊆ n.primeFactors) :
    ∃ v : ℕ,
      #{k ∈ (Finset.range K) | Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k}
        = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
  classical
  let d : ℕ := ∏ q ∈ t, q
  have hp_coprime_d : Nat.Coprime p d := by
    refine Nat.coprime_prod_right_iff.mpr ?_
    intro q hq
    have hqmem : q ∈ n.primeFactors := ht hq
    exact hpn.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hqmem)
  have hpair : Set.Pairwise (↑t : Set ℕ) (fun q q' : ℕ ↦ Nat.Coprime q q') := by
    intro q hq q' hq' hqq'
    exact (Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors (ht hq))
      (Nat.prime_of_mem_primeFactors (ht hq'))).2 hqq'
  have hlcm : t.lcm (fun q : ℕ ↦ q) = d := by
    simpa [d] using (Finset.lcm_eq_prod (s := t) (f := fun q : ℕ ↦ q) hpair)
  have hdiv_iff : ∀ k : ℕ, (∀ q ∈ t, q ∣ k) ↔ d ∣ k := by
    intro k
    simpa [d, hlcm] using
      (Finset.lcm_dvd_iff (s := t) (f := fun q : ℕ ↦ q) (a := k)).symm
  let v : ℕ := Nat.chineseRemainder hp_coprime_d r 0
  have hvp : Nat.ModEq p v r := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.1
  have hvd : Nat.ModEq d v 0 := by
    simpa [v] using (Nat.chineseRemainder hp_coprime_d r 0).prop.2
  refine ⟨v, ?_⟩
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hkK, hkpr, hkt⟩
    refine ⟨hkK, ?_⟩
    have hk0 : d ∣ k := (hdiv_iff k).1 hkt
    simpa [d, v] using
      (Nat.chineseRemainder_modEq_unique hp_coprime_d hkpr
        (Nat.modEq_zero_iff_dvd.2 hk0))
  · rintro ⟨hkK, hk⟩
    have hk' : Nat.ModEq p k v ∧ Nat.ModEq d k v := by
      have hk'' : Nat.ModEq (p * d) k v := by
        simpa [d] using hk
      exact (Nat.modEq_and_modEq_iff_modEq_mul hp_coprime_d).mpr hk''
    refine ⟨hkK, hk'.1.trans hvp, ?_⟩
    exact (hdiv_iff k).2 <| Nat.modEq_zero_iff_dvd.1 (hk'.2.trans hvd)

lemma root_class_good_count_lower_bound
    {n p r K : ℕ} (hn0 : n ≠ 0) (hp : p ≠ 0) (hpn : p.Coprime n) :
    let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
    let α := {k : ℕ // k ∈ U}
    let emb : α ↪ ℕ :=
      ⟨Subtype.val, by
        intro x y h
        exact Subtype.ext h⟩
    let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
    let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
    ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by
  classical
  let U : Finset ℕ := ((Finset.range K).filter fun k ↦ Nat.ModEq p k r)
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ :=
    ⟨Subtype.val, by
      intro x y h
      exact Subtype.ext h⟩
  let S : ℕ → Finset α := fun q ↦ (Finset.univ : Finset α).filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  change ((good.map emb).card : ℝ)
      ≥ (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card
  have hIE : ((good.map emb).card : ℤ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℤ) ^ t.card * ((t.inf S).card : ℤ) := by
    rw [Finset.card_map]
    simpa [good] using
      (Finset.inclusion_exclusion_card_inf_compl (s := n.primeFactors) (S := S))
  have hIE_real : ((good.map emb).card : ℝ) =
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact_mod_cast hIE
  have hterm :
      ∀ t ∈ n.primeFactors.powerset,
        (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1 ≤
          (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    intro t ht
    have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
    obtain ⟨v, hv⟩ :=
      count_root_class_with_divisors (n := n) (p := p) (r := r) (K := K) hp hn0 hpn t htsub
    have hmap :
        (t.inf S).map emb =
          (Finset.range K).filter fun k ↦ Nat.ModEq p k r ∧ ∀ q ∈ t, q ∣ k := by
      ext k
      constructor
      · intro hk
        rcases Finset.mem_map.mp hk with ⟨x, hx, rfl⟩
        have hxU : (x : ℕ) ∈ U := x.property
        rcases Finset.mem_filter.mp hxU with ⟨hxK, hxr⟩
        have hxdiv : ∀ q ∈ t, q ∣ (x : ℕ) := by
          intro q hq
          have hxq : x ∈ S q :=
            (mem_finset_inf_iff (s := t) (f := S) (a := x)).1 hx q hq
          simpa [S] using hxq
        exact Finset.mem_filter.mpr ⟨hxK, ⟨hxr, hxdiv⟩⟩
      · intro hk
        rcases Finset.mem_filter.mp hk with ⟨hkK, hkcond⟩
        rcases hkcond with ⟨hkr, hkdiv⟩
        have hkU : k ∈ U := Finset.mem_filter.mpr ⟨hkK, hkr⟩
        let x : α := ⟨k, hkU⟩
        have hx : x ∈ t.inf S := by
          refine (mem_finset_inf_iff (s := t) (f := S) (a := x)).2 ?_
          intro q hq
          simpa [x, S] using hkdiv q hq
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hcard_map :
        ((t.inf S).map emb).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa [hmap] using hv
    have hcard_eq_count :
        (t.inf S).card = K.count (· ≡ v [MOD p * ∏ q ∈ t, q]) := by
      simpa using hcard_map
    let m : ℕ := p * ∏ q ∈ t, q
    have hm_pos : 0 < m := by
      dsimp [m]
      refine Nat.mul_pos (Nat.pos_of_ne_zero hp) ?_
      refine Finset.prod_pos ?_
      intro q hq
      exact (Nat.prime_of_mem_primeFactors (htsub hq)).pos
    have hcount_formula :
        (t.inf S).card = K / m + if v % m < K % m then 1 else 0 := by
      rw [hcard_eq_count, Nat.count_modEq_card (b := K) (r := m) (hr := hm_pos) v]
    have hcount_formula_real :
        ((t.inf S).card : ℝ) =
          ((K / m : ℕ) : ℝ) + ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hcount_formula
    have hdiv_le : ((K / m : ℕ) : ℝ) ≤ (K : ℝ) / m := Nat.cast_div_le
    have hm_posR : (0 : ℝ) < m := by exact_mod_cast hm_pos
    have hlt_nat : K < (K / m + 1) * m := by
      exact (Nat.div_lt_iff_lt_mul hm_pos).mp (Nat.lt_succ_self _)
    have hlt_real : (K : ℝ) < ((((K / m : ℕ) : ℝ) + 1) * m) := by
      exact_mod_cast hlt_nat
    have hdiv_lt : (K : ℝ) / m < ((K / m : ℕ) : ℝ) + 1 := by
      exact (div_lt_iff₀ hm_posR).2 hlt_real
    have hbit_nonneg :
        (0 : ℝ) ≤ ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) := by
      by_cases h : v % m < K % m
      · simp [h]
      · simp [h]
    have hbit_le_one :
        ((if v % m < K % m then 1 else 0 : ℕ) : ℝ) ≤ 1 := by
      by_cases h : v % m < K % m
      · simp [h]
      · simp [h]
    have hlower : (K : ℝ) / m - 1 ≤ ((t.inf S).card : ℝ) := by
      rw [hcount_formula_real]
      have hq_ge : (K : ℝ) / m - 1 ≤ (K / m : ℝ) := by
        linarith
      linarith
    have hupper : ((t.inf S).card : ℝ) ≤ (K : ℝ) / m + 1 := by
      rw [hcount_formula_real]
      linarith
    rcases neg_one_pow_eq_or ℝ t.card with hsgn | hsgn
    · rw [hsgn]
      simpa [m] using hlower
    · rw [hsgn]
      have hupper' : ((t.inf S).card : ℝ) ≤ (K : ℝ) / (p * ∏ q ∈ t, q) + 1 := by
        simpa [m] using hupper
      linarith
  have hsum_lower :
      ∑ t ∈ n.primeFactors.powerset,
        ((-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q)) - 1)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    exact Finset.sum_le_sum (fun t ht ↦ hterm t ht)
  have hsum_lower' :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ)
        ≤ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := by
    simpa [Finset.sum_sub_distrib] using hsum_lower
  have hmain_expand :
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
        = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          = ∑ t ∈ n.primeFactors.powerset,
              (-1 : ℝ) ^ t.card * ((K : ℝ) / p * ∏ q ∈ t, (1 / (q : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              have htsub : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
              have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp
              have hprod_pos : 0 < ∏ q ∈ t, (q : ℝ) := by
                refine Finset.prod_pos ?_
                intro q hq
                exact_mod_cast (Nat.prime_of_mem_primeFactors (htsub hq)).pos
              have hprod_ne0 : (∏ q ∈ t, (q : ℝ)) ≠ 0 := by
                exact ne_of_gt hprod_pos
              have hprod_inv :
                  ∏ q ∈ t, (1 / (q : ℝ)) = 1 / ∏ q ∈ t, (q : ℝ) := by
                calc
                  ∏ q ∈ t, (1 / (q : ℝ)) = ∏ q ∈ t, ((q : ℝ)⁻¹) := by
                    simp [one_div]
                  _ = (∏ q ∈ t, (q : ℝ))⁻¹ := by
                    rw [Finset.prod_inv_distrib]
                  _ = 1 / ∏ q ∈ t, (q : ℝ) := by
                    simp [one_div]
              rw [hprod_inv]
              have hcast_prod : ((∏ q ∈ t, q : ℕ) : ℝ) = ∏ q ∈ t, (q : ℝ) := by
                simp
              rw [hcast_prod]
              field_simp [hp0, hprod_ne0]
      _ = ∑ t ∈ n.primeFactors.powerset,
            (K : ℝ) / p * ((-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
      _ = (K : ℝ) / p * ∑ t ∈ n.primeFactors.powerset,
            (-1 : ℝ) ^ t.card * ∏ q ∈ t, (1 / (q : ℝ)) := by
          symm
          rw [Finset.mul_sum]
      _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
          congr 1
          symm
          simpa using
            (Finset.prod_sub (s := n.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
              (g := fun q : ℕ => 1 / (q : ℝ)))
  have herror :
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (2 : ℝ) ^ n.primeFactors.card := by
    calc
      ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) = (n.primeFactors.powerset.card : ℝ) := by simp
      _ = (2 : ℝ) ^ n.primeFactors.card := by simp
  calc
    ((good.map emb).card : ℝ)
        = ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((t.inf S).card : ℝ) := hIE_real
    _ ≥ ∑ t ∈ n.primeFactors.powerset, (-1 : ℝ) ^ t.card * ((K : ℝ) / (p * ∏ q ∈ t, q))
          - ∑ t ∈ n.primeFactors.powerset, (1 : ℝ) := hsum_lower'
    _ = (K : ℝ) / p * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ))
          - (2 : ℝ) ^ n.primeFactors.card := by rw [hmain_expand, herror]

/-- Inclusion–exclusion for all integers in an initial interval. -/
lemma count_coprime_range_lower_bound (n K : ℕ) (hn0 : n ≠ 0) :
    (K : ℝ) * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) -
      (2 : ℝ) ^ n.primeFactors.card ≤
        (((Finset.range K).filter fun k ↦ k.Coprime n).card : ℝ) := by
  classical
  let U : Finset ℕ := (Finset.range K).filter fun k ↦ Nat.ModEq 1 k 0
  let α := {k : ℕ // k ∈ U}
  let emb : α ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let S : ℕ → Finset α := fun q ↦ Finset.univ.filter fun k ↦ q ∣ (k : ℕ)
  let good : Finset α := n.primeFactors.inf fun q ↦ (S q)ᶜ
  have hgood : good.map emb = (Finset.range K).filter fun k ↦ k.Coprime n := by
    ext k
    constructor
    · intro hk
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hk
      have hyK : (y : ℕ) < K := Finset.mem_range.mp (Finset.mem_filter.mp y.property).1
      have hnondvd : ∀ q ∈ n.primeFactors, ¬ q ∣ (y : ℕ) := by
        intro q hq
        have hyq := (mem_finset_inf_iff (a := y)).mp hy q hq
        simpa [S] using hyq
      have hcop : (y : ℕ).Coprime n := Nat.coprime_of_dvd fun q hq hqy hqn ↦
        hnondvd q (Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩) hqy
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyK, hcop⟩
    · intro hk
      obtain ⟨hkK, hcop⟩ := Finset.mem_filter.mp hk
      have hkU : k ∈ U := Finset.mem_filter.mpr ⟨hkK, by unfold Nat.ModEq; omega⟩
      let y : α := ⟨k, hkU⟩
      refine Finset.mem_map.mpr ⟨y, ?_, rfl⟩
      apply mem_finset_inf_iff.mpr
      intro q hq
      have hnot : ¬ q ∣ k := by
        intro hdvd
        have hgcd := Nat.dvd_gcd hdvd (Nat.dvd_of_mem_primeFactors hq)
        rw [hcop.gcd_eq_one] at hgcd
        exact (Nat.prime_of_mem_primeFactors hq).not_dvd_one hgcd
      simpa [S, y] using hnot
  have h := root_class_good_count_lower_bound (n := n) (p := 1) (r := 0) (K := K)
    hn0 (by decide) (by simp)
  change ((good.map emb).card : ℝ) ≥ _ at h
  rw [hgood] at h
  simpa using h

lemma inv_two_pow_le_prime_product (n : ℕ) :
    ((2 : ℝ) ^ n.primeFactors.card)⁻¹ ≤
      ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  rw [← inv_pow]
  calc
    (2⁻¹ : ℝ) ^ n.primeFactors.card = ∏ _q ∈ n.primeFactors, (2⁻¹ : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (by intros; positivity) (by
      intro q hq
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
      have hrecip := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq2
      norm_num at hrecip ⊢
      linarith)

lemma count_coprime_Icc_lower_bound (n A : ℕ) (hn : 2 ≤ n) :
    (A : ℝ) / (2 : ℝ) ^ n.primeFactors.card - (2 : ℝ) ^ n.primeFactors.card ≤
      (((Finset.Icc 1 A).filter fun k ↦ k.Coprime n).card : ℝ) := by
  have hsub : (Finset.range A).filter (fun k ↦ k.Coprime n) ⊆
      (Finset.Icc 1 A).filter (fun k ↦ k.Coprime n) := by
    intro k hk
    obtain ⟨hkA, hcop⟩ := Finset.mem_filter.mp hk
    have hk0 : k ≠ 0 := by
      intro hzero
      simp only [hzero, Nat.coprime_zero_left] at hcop
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
      (Finset.mem_range.mp hkA).le⟩, hcop⟩
  calc
    _ ≤ (A : ℝ) * ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) -
        (2 : ℝ) ^ n.primeFactors.card := by
      rw [div_eq_mul_inv]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left
        (inv_two_pow_le_prime_product n) (Nat.cast_nonneg A)) _
    _ ≤ (((Finset.range A).filter fun k ↦ k.Coprime n).card : ℝ) :=
      count_coprime_range_lower_bound n A (by omega)
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

/-- A power-sized interval has many admissible denominators. -/
theorem count_coprime_Icc_ge (n A : ℕ) (hn : 2 ≤ n)
    (hA : 2 * (2 ^ n.primeFactors.card) ^ 2 ≤ A) :
    (A : ℝ) / (2 * (2 : ℝ) ^ n.primeFactors.card) ≤
      (((Finset.Icc 1 A).filter fun k ↦ k.Coprime n).card : ℝ) := by
  have hW : 0 < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hAr : 2 * ((2 : ℝ) ^ n.primeFactors.card) ^ 2 ≤ A := by exact_mod_cast hA
  apply le_trans _ (count_coprime_Icc_lower_bound n A hn)
  apply (mul_le_mul_iff_of_pos_right (show 0 < 2 * (2 : ℝ) ^ n.primeFactors.card by positivity)).mp
  rw [div_mul_cancel₀ _ (by positivity)]
  have hdiv := div_mul_cancel₀ (A : ℝ) hW.ne'
  nlinarith

end Erdos1141.Sieve
