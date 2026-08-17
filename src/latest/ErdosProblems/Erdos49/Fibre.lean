import Mathlib

open scoped BigOperators

namespace Erdos49

open Finset

private lemma prod_totientFactors_eq_div (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 - (p : ℚ)⁻¹) =
      ((∏ p ∈ s, (p - 1 : ℕ) : ℕ) : ℚ) /
        ((∏ p ∈ s, p : ℕ) : ℚ) := by
  calc
    ∏ p ∈ s, (1 - (p : ℚ)⁻¹) =
        ∏ p ∈ s, (((p - 1 : ℕ) : ℚ) / (p : ℚ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hs p hp).ne_zero
      rw [Nat.cast_sub (hs p hp).one_le, Nat.cast_one]
      field_simp
    _ = (∏ p ∈ s, (((p - 1 : ℕ) : ℚ))) /
        ∏ p ∈ s, (p : ℚ) := Finset.prod_div_distrib _ _
    _ = ((∏ p ∈ s, (p - 1 : ℕ) : ℕ) : ℚ) /
        ((∏ p ∈ s, p : ℕ) : ℚ) := by simp only [Nat.cast_prod]

private lemma prod_totientFactors_injective_on_primeFinsets
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (h : ∏ p ∈ s, (1 - (p : ℚ)⁻¹) = ∏ p ∈ t, (1 - (p : ℚ)⁻¹)) :
    s = t := by
  classical
  let u := s \ t
  let v := t \ s
  have hu : ∀ p ∈ u, p.Prime := fun p hp ↦ hs p (Finset.mem_sdiff.mp hp).1
  have hv : ∀ p ∈ v, p.Prime := fun p hp ↦ ht p (Finset.mem_sdiff.mp hp).1
  have huv : Disjoint u v := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpu hpv
    exact (Finset.mem_sdiff.mp hpu).2 (Finset.mem_sdiff.mp hpv).1
  have hcancel :
      ∏ p ∈ u, (1 - (p : ℚ)⁻¹) = ∏ p ∈ v, (1 - (p : ℚ)⁻¹) := by
    let w := s ∩ t
    have hwu : Disjoint w u := by
      refine Finset.disjoint_left.mpr ?_
      intro p hpw hpu
      exact (Finset.mem_sdiff.mp hpu).2 (Finset.mem_inter.mp hpw).2
    have hwv : Disjoint w v := by
      refine Finset.disjoint_left.mpr ?_
      intro p hpw hpv
      exact (Finset.mem_sdiff.mp hpv).2 (Finset.mem_inter.mp hpw).1
    have hsu : w ∪ u = s := by
      ext p
      simp [w, u]
      tauto
    have htv : w ∪ v = t := by
      ext p
      simp [w, v]
      tauto
    have hwpos : 0 < ∏ p ∈ w, (1 - (p : ℚ)⁻¹) := by
      apply Finset.prod_pos
      intro p hp
      have hpq : (1 : ℚ) < p := by
        exact_mod_cast (hs p (Finset.mem_inter.mp hp).1).one_lt
      exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hpq)
    rw [← hsu, Finset.prod_union hwu, ← htv, Finset.prod_union hwv] at h
    exact mul_left_cancel₀ (ne_of_gt hwpos) h
  by_contra hst
  have huv_ne : (u ∪ v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hempty' : u = ∅ ∧ v = ∅ := Finset.union_eq_empty.mp hempty
    apply hst
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_eq_empty_iff_subset.mp hempty'.1
    · exact Finset.sdiff_eq_empty_iff_subset.mp hempty'.2
  let P := (u ∪ v).max' huv_ne
  have hPmem : P ∈ u ∪ v := (u ∪ v).max'_mem huv_ne
  have hPle : ∀ {r}, r ∈ u ∪ v → r ≤ P := fun {r} hr ↦
    (u ∪ v).le_max' r hr
  have hPprime : P.Prime := by
    rcases Finset.mem_union.mp hPmem with hPu | hPv
    · exact hu P hPu
    · exact hv P hPv
  have impossible_left (hPu : P ∈ u) : False := by
    have hPv : P ∉ v := Finset.disjoint_left.mp huv hPu
    have hden_u_nat : (∏ p ∈ u, p) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hu p hp).ne_zero
    have hden_v_nat : (∏ p ∈ v, p) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hv p hp).ne_zero
    have hden_u : ((∏ p ∈ u, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hden_u_nat
    have hden_v : ((∏ p ∈ v, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hden_v_nat
    have hcrossQ :
        ((∏ p ∈ u, (p - 1 : ℕ) : ℕ) : ℚ) * ((∏ p ∈ v, p : ℕ) : ℚ) =
          ((∏ p ∈ v, (p - 1 : ℕ) : ℕ) : ℚ) * ((∏ p ∈ u, p : ℕ) : ℚ) := by
      rw [prod_totientFactors_eq_div u hu, prod_totientFactors_eq_div v hv] at hcancel
      exact (div_eq_div_iff hden_u hden_v).mp hcancel
    have hcross :
        (∏ p ∈ u, (p - 1 : ℕ)) * (∏ p ∈ v, p) =
          (∏ p ∈ v, (p - 1 : ℕ)) * (∏ p ∈ u, p) := by
      exact_mod_cast hcrossQ
    have hPdvd_left : P ∣ (∏ p ∈ u, (p - 1 : ℕ)) * (∏ p ∈ v, p) := by
      rw [hcross]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p ↦ p) hPu) _
    have hPnot_u_pred : ¬P ∣ ∏ p ∈ u, (p - 1 : ℕ) := by
      apply hPprime.prime.not_dvd_finsetProd
      intro r hr
      apply Nat.not_dvd_of_pos_of_lt
      · exact Nat.sub_pos_of_lt (hu r hr).one_lt
      · exact lt_of_lt_of_le (Nat.sub_lt (hu r hr).pos zero_lt_one)
          (hPle (Finset.mem_union_left v hr))
    have hPnot_v : ¬P ∣ ∏ p ∈ v, p := by
      apply hPprime.prime.not_dvd_finsetProd
      intro r hr
      apply Nat.not_dvd_of_pos_of_lt (hv r hr).pos
      exact lt_of_le_of_ne (hPle (Finset.mem_union_right u hr))
        (fun heq ↦ hPv (heq ▸ hr))
    exact (hPprime.not_dvd_mul hPnot_u_pred hPnot_v) hPdvd_left
  rcases Finset.mem_union.mp hPmem with hPu | hPv
  · exact impossible_left hPu
  · have hPu : P ∉ u := Finset.disjoint_left.mp huv.symm hPv
    have hden_v_nat : (∏ p ∈ v, p) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hv p hp).ne_zero
    have hden_u_nat : (∏ p ∈ u, p) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hu p hp).ne_zero
    have hden_v : ((∏ p ∈ v, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hden_v_nat
    have hden_u : ((∏ p ∈ u, p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hden_u_nat
    have hcrossQ :
        ((∏ p ∈ v, (p - 1 : ℕ) : ℕ) : ℚ) * ((∏ p ∈ u, p : ℕ) : ℚ) =
          ((∏ p ∈ u, (p - 1 : ℕ) : ℕ) : ℚ) * ((∏ p ∈ v, p : ℕ) : ℚ) := by
      rw [prod_totientFactors_eq_div v hv, prod_totientFactors_eq_div u hu] at hcancel
      exact (div_eq_div_iff hden_v hden_u).mp hcancel.symm
    have hcross :
        (∏ p ∈ v, (p - 1 : ℕ)) * (∏ p ∈ u, p) =
          (∏ p ∈ u, (p - 1 : ℕ)) * (∏ p ∈ v, p) := by
      exact_mod_cast hcrossQ
    have hPdvd_left : P ∣ (∏ p ∈ v, (p - 1 : ℕ)) * (∏ p ∈ u, p) := by
      rw [hcross]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p ↦ p) hPv) _
    have hPnot_v_pred : ¬P ∣ ∏ p ∈ v, (p - 1 : ℕ) := by
      apply hPprime.prime.not_dvd_finsetProd
      intro r hr
      apply Nat.not_dvd_of_pos_of_lt
      · exact Nat.sub_pos_of_lt (hv r hr).one_lt
      · exact lt_of_lt_of_le (Nat.sub_lt (hv r hr).pos zero_lt_one)
          (hPle (Finset.mem_union_right u hr))
    have hPnot_u : ¬P ∣ ∏ p ∈ u, p := by
      apply hPprime.prime.not_dvd_finsetProd
      intro r hr
      apply Nat.not_dvd_of_pos_of_lt (hu r hr).pos
      exact lt_of_le_of_ne (hPle (Finset.mem_union_left v hr))
        (fun heq ↦ hPu (heq ▸ hr))
    exact (hPprime.not_dvd_mul hPnot_v_pred hPnot_u) hPdvd_left

/-- The value of `φ(n)/n` determines the set of prime divisors of a positive integer. -/
theorem primeFactors_eq_of_totient_div_eq {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : (m.totient : ℚ) / m = (n.totient : ℚ) / n) :
    m.primeFactors = n.primeFactors := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hmprod :
      (m.totient : ℚ) / m = ∏ p ∈ m.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors, mul_div_cancel_left₀ _ hmQ]
  have hnprod :
      (n.totient : ℚ) / n = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors, mul_div_cancel_left₀ _ hnQ]
  apply prod_totientFactors_injective_on_primeFinsets
  · exact fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  · exact fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  · rw [← hmprod, ← hnprod, h]

private lemma sum_inv_pow_succ_le_one (p D : ℕ) (hp : 2 ≤ p) :
    ∑ e ∈ Finset.range D, (1 / (p : ℚ)) ^ (e + 1) ≤ 1 := by
  let x : ℚ := 1 / p
  have hx0 : 0 ≤ x := by positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply one_div_le_one_div_of_le
    · norm_num
    · exact_mod_cast hp
  have hx_le : x ≤ 1 - x := by linarith
  have hsum0 : 0 ≤ ∑ e ∈ Finset.range D, x ^ e := by positivity
  have hgeom := geom_sum_mul_neg x D
  calc
    ∑ e ∈ Finset.range D, (1 / (p : ℚ)) ^ (e + 1) =
        x * ∑ e ∈ Finset.range D, x ^ e := by
          simp only [x, pow_succ', Finset.mul_sum]
    _ ≤ (1 - x) * ∑ e ∈ Finset.range D, x ^ e :=
      mul_le_mul_of_nonneg_right hx_le hsum0
    _ = 1 - x ^ D := by simpa [mul_comm] using hgeom
    _ ≤ 1 := sub_le_self _ (pow_nonneg hx0 D)

/-- A finite set of positive integers with one fixed prime support has reciprocal sum at most one. -/
theorem sum_reciprocal_primeFactors_fibre_le_one (P : Finset ℕ) (D : ℕ)
    (hPprime : ∀ p ∈ P, p.Prime) :
    ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d.primeFactors = P), (1 : ℚ) / d ≤ 1 := by
  classical
  let F := (Finset.Icc 1 D).filter (fun d ↦ d.primeFactors = P)
  let encode : ℕ → (P → ℕ) := fun d p ↦ d.factorization p - 1
  let weight : (P → ℕ) → ℚ := fun e ↦ ∏ p : P, (1 / (p : ℚ)) ^ (e p + 1)
  have hF_mem (d : ℕ) (hd : d ∈ F) : 1 ≤ d ∧ d ≤ D ∧ d.primeFactors = P := by
    simpa [F, and_assoc] using hd
  have hencode_mem (d : ℕ) (hd : d ∈ F) :
      encode d ∈ Fintype.piFinset (fun _ : P ↦ Finset.range D) := by
    rw [Fintype.mem_piFinset]
    intro p
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (Nat.sub_le _ _) <|
      (Nat.factorization_lt p (Nat.ne_of_gt (hF_mem d hd).1)).trans_le (hF_mem d hd).2.1
  have hencode_inj : Set.InjOn encode F := by
    intro a ha b hb hab
    apply Nat.eq_of_factorization_eq (Nat.ne_of_gt (hF_mem a ha).1)
      (Nat.ne_of_gt (hF_mem b hb).1)
    intro p
    by_cases hp : p ∈ P
    · have hpa : 0 < a.factorization p := by
        exact (Nat.prime_of_mem_primeFactors ((hF_mem a ha).2.2.symm ▸ hp)).factorization_pos_of_dvd
          (Nat.ne_of_gt (hF_mem a ha).1) (Nat.dvd_of_mem_primeFactors ((hF_mem a ha).2.2.symm ▸ hp))
      have hpb : 0 < b.factorization p := by
        exact (Nat.prime_of_mem_primeFactors ((hF_mem b hb).2.2.symm ▸ hp)).factorization_pos_of_dvd
          (Nat.ne_of_gt (hF_mem b hb).1) (Nat.dvd_of_mem_primeFactors ((hF_mem b hb).2.2.symm ▸ hp))
      have := congrFun hab ⟨p, hp⟩
      dsimp [encode] at this
      omega
    · have hpa : p ∉ a.primeFactors := by simpa [(hF_mem a ha).2.2] using hp
      have hpb : p ∉ b.primeFactors := by simpa [(hF_mem b hb).2.2] using hp
      have hpa0 : a.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff]
        simpa using hpa
      have hpb0 : b.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff]
        simpa using hpb
      rw [hpa0, hpb0]
  have hweight (d : ℕ) (hd : d ∈ F) : (1 : ℚ) / d = weight (encode d) := by
    have hd0 : d ≠ 0 := Nat.ne_of_gt (hF_mem d hd).1
    have hfac_pos : ∀ p : P, 0 < d.factorization p := by
      intro p
      have hp_mem : (p : ℕ) ∈ d.primeFactors := (hF_mem d hd).2.2.symm ▸ p.property
      exact (Nat.prime_of_mem_primeFactors hp_mem).factorization_pos_of_dvd hd0
        (Nat.dvd_of_mem_primeFactors hp_mem)
    have hdprod : (d : ℚ) = ∏ p : P, (p : ℚ) ^ d.factorization p := by
      have hdprodNat : d = ∏ p : P, (p : ℕ) ^ d.factorization p := by
        simpa [(hF_mem d hd).2.2] using
          (Nat.prod_primeFactors_coe_pow_factorization hd0)
      exact_mod_cast hdprodNat
    rw [hdprod]
    dsimp [weight, encode]
    rw [one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (hfac_pos p), one_div]
    exact (inv_pow (p : ℚ) (d.factorization p)).symm
  calc
    ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d.primeFactors = P), (1 : ℚ) / d =
        ∑ d ∈ F, weight (encode d) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hweight d hd
    _ = ∑ e ∈ F.image encode, weight e := by
      rw [Finset.sum_image]
      exact fun a ha b hb hab ↦ hencode_inj ha hb hab
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : P ↦ Finset.range D), weight e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [Finset.mem_image] at he
        obtain ⟨d, hd, rfl⟩ := he
        exact hencode_mem d hd
      · intro e he hnot
        dsimp [weight]
        positivity
    _ = ∏ p : P, ∑ e ∈ Finset.range D, (1 / (p : ℚ)) ^ (e + 1) := by
      exact Finset.sum_prod_piFinset (Finset.range D)
        (fun p : P ↦ fun e ↦ (1 / (p : ℚ)) ^ (e + 1))
    _ ≤ 1 := by
      apply Finset.prod_le_one
      · intro p hp
        apply Finset.sum_nonneg
        intro e he
        positivity
      · intro p hp
        exact sum_inv_pow_succ_le_one p D (hPprime p p.property).two_le

/-- Finite form of Tao's reciprocal-mass bound for a fibre of the totient ratio. -/
theorem sum_totientRatio_fibre_reciprocal_le_one (q : ℚ) (D : ℕ) :
    ∑ d ∈ (Finset.Icc 1 D).filter
      (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q),
      (1 : ℚ) / (d : ℚ) ≤ 1 := by
  classical
  let F := (Finset.Icc 1 D).filter
    (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q)
  by_cases hF : F = ∅
  · simp [F, hF]
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have ha_data : 1 ≤ a ∧ a ≤ D ∧ (a.totient : ℚ) / a = q := by
      simpa [F, and_assoc] using ha
    have hF_support : F = (Finset.Icc 1 D).filter (fun d ↦ d.primeFactors = a.primeFactors) := by
      ext d
      simp only [F, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, hratio⟩
        refine ⟨hd, primeFactors_eq_of_totient_div_eq (Nat.ne_of_gt hd.1)
          (Nat.ne_of_gt ha_data.1) ?_⟩
        rw [hratio, ha_data.2.2]
      · rintro ⟨hd, hsupport⟩
        refine ⟨hd, ?_⟩
        rw [← ha_data.2.2]
        have hd0 := Nat.ne_of_gt hd.1
        have ha0 := Nat.ne_of_gt ha_data.1
        rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors,
          mul_div_cancel_left₀ _ (by exact_mod_cast hd0), mul_div_cancel_left₀ _ (by exact_mod_cast ha0),
          hsupport]
    rw [show (Finset.Icc 1 D).filter
        (fun d : ℕ ↦ (d.totient : ℚ) / (d : ℚ) = q) = F from rfl,
      hF_support]
    exact sum_reciprocal_primeFactors_fibre_le_one a.primeFactors D
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)

#print axioms primeFactors_eq_of_totient_div_eq
#print axioms sum_reciprocal_primeFactors_fibre_le_one
#print axioms sum_totientRatio_fibre_reciprocal_le_one

end Erdos49
