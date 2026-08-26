import ErdosProblems.Erdos941.SpherePairCount

/-!
# Summing square content along the shadowing progressions

The progressions are centered at the excluded endpoints. Consequently the
multiple count has no additive boundary error, even when the norm has square factors.
-/

namespace Erdos941

open PairLocal

noncomputable def sphereResidueValues (n q : ℕ) (c : ℤ) : Finset ℤ :=
  (Finset.Ioo (-(n : ℤ)) n).filter fun e => (q : ℤ) ∣ e - c

theorem sphere_content_mem_squareDivisors {n : ℕ} (hn : 0 < n) (e : ℤ) :
    pairSquareContent (-(n : ℤ)) (-(2 * e)) ∈ squareDivisors n := by
  have hnZ : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn.ne')
  have hG : (-(n : ℤ)).natAbs.gcd (-(2 * e)).natAbs ≠ 0 := by
    intro hG
    exact (Int.natAbs_ne_zero.mpr hnZ) (Nat.gcd_eq_zero_iff.mp hG).1
  have hf0 := squareContentRoot_ne_zero _ hG
  apply (mem_squareDivisors hn.ne').mpr
  refine ⟨Nat.pos_of_ne_zero hf0, ?_⟩
  have hdiv := (pairSquareContent_sq_dvd (-(n : ℤ)) (-(2 * e)) hnZ).1
  have hh := dvd_neg.mp hdiv
  exact_mod_cast hh

theorem sphere_content_le_squareDivisor_sum {n : ℕ} (hn : 0 < n) (e : ℤ) :
    (pairSquareContent (-(n : ℤ)) (-(2 * e)) : ℝ) ≤
      ∑ f ∈ squareDivisors n, if (f : ℤ) ^ 2 ∣ 2 * e then (f : ℝ) else 0 := by
  classical
  have hmem := sphere_content_mem_squareDivisors hn e
  have hnZ : -(n : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hn.ne')
  have hdiv := dvd_neg.mp (pairSquareContent_sq_dvd (-(n : ℤ)) (-(2 * e)) hnZ).2
  have h := Finset.single_le_sum (s := squareDivisors n)
    (f := fun f : ℕ => if (f : ℤ) ^ 2 ∣ 2 * e then (f : ℝ) else 0)
    (fun f _ => by split_ifs <;> positivity) hmem
  simpa only [if_pos hdiv] using h

theorem weighted_noncentral_card_product_le {L : ℤ} {q f : ℕ}
    (hL : 0 ≤ L) (hq : 0 < q) (hf : 0 < f) :
    (f : ℝ) * (noncentralMultiples 0 L ((q : ℤ) * (f : ℤ) ^ 2)).card ≤
      2 * (L : ℝ) / q := by
  have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
  have hfZ : 0 < (f : ℤ) := by exact_mod_cast hf
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let m : ℤ := (q : ℤ) * (f : ℤ) ^ 2
  have hm : 0 < m := mul_pos hqZ (sq_pos_of_pos hfZ)
  have hcard := card_noncentralMultiples hL hm (dvd_zero m)
  have hcardZ : ((noncentralMultiples 0 L m).card : ℤ) = 2 * (L / m) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat,
      Int.toNat_of_nonneg (Int.ediv_nonneg hL hm.le)]
  have hboundZ : ((noncentralMultiples 0 L m).card : ℤ) * m ≤ 2 * L := by
    rw [hcardZ]
    nlinarith [Int.ediv_mul_le L hm.ne']
  have hfsmall : (f : ℤ) ≤ (f : ℤ) ^ 2 := by nlinarith
  have hsmall := mul_le_mul_of_nonneg_left hfsmall
    (show (0 : ℤ) ≤ (noncentralMultiples 0 L m).card * q by positivity)
  have hbound : ((noncentralMultiples 0 L m).card : ℤ) * (q : ℤ) * f ≤ 2 * L := by
    dsimp [m] at hboundZ
    nlinarith
  apply (le_div_iff₀ hqR).mpr
  have hR : ((noncentralMultiples 0 L m).card : ℝ) * (q : ℝ) * f ≤ 2 * (L : ℝ) := by
    exact_mod_cast hbound
  dsimp [m] at hR
  nlinarith

theorem sphere_residue_squareDivisor_card {n q f : ℕ} {c : ℤ}
    (hn : 0 < n) (hcop : q.Coprime n) (hf : f ∈ squareDivisors n)
    (hc : c = n ∨ c = -(n : ℤ)) :
    ((sphereResidueValues n q c).filter (fun e => (f : ℤ) ^ 2 ∣ 2 * e)).card ≤
      (noncentralMultiples 0 (4 * n) ((q : ℤ) * (f : ℤ) ^ 2)).card := by
  have hfsq : f ^ 2 ∣ n := ((mem_squareDivisors hn.ne').mp hf).2
  have hfsqZ : (f : ℤ) ^ 2 ∣ (n : ℤ) := by exact_mod_cast hfsq
  have hfc : (f : ℤ) ^ 2 ∣ c := by rcases hc with rfl | rfl; exact hfsqZ; exact dvd_neg.mpr hfsqZ
  have hcp : IsCoprime (q : ℤ) ((f : ℤ) ^ 2) := by
    simpa only [Nat.cast_pow] using (hcop.of_dvd_right hfsq).isCoprime
  apply Finset.card_le_card_of_injOn (fun e : ℤ => 2 * (e - c))
  · intro e he
    dsimp only
    obtain ⟨he, hf2e⟩ := Finset.mem_filter.mp he
    obtain ⟨he, hqe⟩ := Finset.mem_filter.mp he
    obtain ⟨hel, heu⟩ := Finset.mem_Ioo.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, ?_, ?_⟩
    · rcases hc with rfl | rfl <;> omega
    · apply hcp.mul_dvd (dvd_mul_of_dvd_right hqe 2)
      have hsub := dvd_sub hf2e (dvd_mul_of_dvd_right hfc 2)
      convert hsub using 1 <;> ring
    · rcases hc with rfl | rfl <;> omega
  · intro a _ b _ hab
    dsimp only at hab
    omega

theorem sum_sphere_progression_content_le {n q : ℕ} {c : ℤ}
    (hn : 0 < n) (hq : 0 < q) (hcop : q.Coprime n)
    (hc : c = n ∨ c = -(n : ℤ)) :
    (∑ e ∈ sphereResidueValues n q c,
      (pairSquareContent (-(n : ℤ)) (-(2 * e)) : ℝ)) ≤
        (8 * (n : ℝ) / q) * n.divisors.card := by
  classical
  calc
    _ ≤ ∑ e ∈ sphereResidueValues n q c,
        ∑ f ∈ squareDivisors n, if (f : ℤ) ^ 2 ∣ 2 * e then (f : ℝ) else 0 :=
      Finset.sum_le_sum (fun e _ => sphere_content_le_squareDivisor_sum hn e)
    _ = ∑ f ∈ squareDivisors n,
        (f : ℝ) * ((sphereResidueValues n q c).filter (fun e => (f : ℤ) ^ 2 ∣ 2 * e)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ _f ∈ squareDivisors n, 8 * (n : ℝ) / q := by
      apply Finset.sum_le_sum
      intro f hf
      have hcard : (((sphereResidueValues n q c).filter
          (fun e => (f : ℤ) ^ 2 ∣ 2 * e)).card : ℝ) ≤
          (noncentralMultiples 0 (4 * n) ((q : ℤ) * (f : ℤ) ^ 2)).card := by
        exact_mod_cast sphere_residue_squareDivisor_card hn hcop hf hc
      apply (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg f)).trans
      have h := weighted_noncentral_card_product_le (L := 4 * (n : ℤ))
        (by positivity) hq ((mem_squareDivisors hn.ne').mp hf).1
      push_cast at h
      have he : 2 * (4 * (n : ℝ)) / q = 8 * (n : ℝ) / q := by ring
      rw [he] at h
      exact h
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun f => f ^ 2 ∣ n) n.divisors)

end Erdos941
