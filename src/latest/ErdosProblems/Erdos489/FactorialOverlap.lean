import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Product of distances from one point to every point of a natural interval. -/
theorem prod_range_dist_eq_factorials (G u : ℕ) (hu : u ≤ G) :
    (∏ i ∈ Finset.range (G + 1), if i = u then 1 else Nat.dist i u) =
      u.factorial * (G - u).factorial := by
  have hsplit : G + 1 = (u + 1) + (G - u) := by omega
  rw [hsplit, Finset.prod_range_add]
  have hleft :
      (∏ i ∈ Finset.range (u + 1), if i = u then 1 else Nat.dist i u) = u.factorial := by
    rw [Finset.prod_range_succ]
    simp only [if_pos, mul_one]
    calc
      (∏ i ∈ Finset.range u, if i = u then 1 else Nat.dist i u) =
          ∏ i ∈ Finset.range u, (u - i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiu : i < u := Finset.mem_range.mp hi
        rw [if_neg (Nat.ne_of_lt hiu), Nat.dist_eq_sub_of_le hiu.le]
      _ = u.descFactorial u := (Nat.descFactorial_eq_prod_range u u).symm
      _ = u.factorial := Nat.descFactorial_self u
  rw [hleft]
  congr 1
  calc
    (∏ i ∈ Finset.range (G - u),
        if u + 1 + i = u then 1 else Nat.dist (u + 1 + i) u) =
        ∏ i ∈ Finset.range (G - u), (i + 1) := by
      apply Finset.prod_congr rfl
      intro i _
      have hle : u ≤ u + 1 + i := by omega
      rw [if_neg (by omega), Nat.dist_comm, Nat.dist_eq_sub_of_le hle]
      omega
    _ = (G - u).factorial := Finset.prod_range_add_one_eq_factorial _

/-- Prime-power overlap among compatible moduli in an interval costs only one
factorial: the product of all moduli divides their lcm times `G!`. -/
theorem prod_dvd_lcm_mul_factorial_of_gcd_dvd_dist
    (G : ℕ) (a : ℕ → ℕ)
    (ha : ∀ i ≤ G, a i ≠ 0)
    (hcompat : ∀ i ≤ G, ∀ j ≤ G, Nat.gcd (a i) (a j) ∣ Nat.dist i j) :
    (∏ i ∈ Finset.range (G + 1), a i) ∣
      (Finset.range (G + 1)).lcm a * G.factorial := by
  let S := Finset.range (G + 1)
  have haS : ∀ i ∈ S, a i ≠ 0 := by
    intro i hi
    exact ha i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hprod0 : (∏ i ∈ S, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr haS
  have hlcm0 : S.lcm a ≠ 0 := Finset.lcm_ne_zero_iff.mpr haS
  have hrhs0 : S.lcm a * G.factorial ≠ 0 :=
    mul_ne_zero hlcm0 G.factorial_ne_zero
  apply (Nat.factorization_prime_le_iff_dvd hprod0 hrhs0).mp
  intro p hp
  obtain ⟨u, huS, hmax⟩ :=
    Finset.exists_max_image S (fun i => (a i).factorization p)
      (by exact ⟨0, by simp [S]⟩)
  have huG : u ≤ G := Nat.le_of_lt_succ (Finset.mem_range.mp huS)
  have hsup : S.sup (fun i => (a i).factorization p) =
      (a u).factorization p := by
    apply le_antisymm
    · exact Finset.sup_le_iff.mpr hmax
    · exact Finset.le_sup (f := fun i => (a i).factorization p) huS
  have hterm : ∀ i ∈ S.erase u,
      (a i).factorization p ≤ (Nat.dist i u).factorization p := by
    intro i hi
    have hiS : i ∈ S := Finset.mem_of_mem_erase hi
    have hiu : i ≠ u := (Finset.mem_erase.mp hi).1
    have hiG : i ≤ G := Nat.le_of_lt_succ (Finset.mem_range.mp hiS)
    let e := (a i).factorization p
    have hpowi : p ^ e ∣ a i :=
      (hp.pow_dvd_iff_le_factorization (haS i hiS)).mpr le_rfl
    have hpowu : p ^ e ∣ a u :=
      (hp.pow_dvd_iff_le_factorization (haS u huS)).mpr (hmax i hiS)
    have hpowdist : p ^ e ∣ Nat.dist i u :=
      (Nat.dvd_gcd hpowi hpowu).trans (hcompat i hiG u huG)
    have hdist0 : Nat.dist i u ≠ 0 := fun hzero =>
      hiu (Nat.eq_of_dist_eq_zero hzero)
    exact (hp.pow_dvd_iff_le_factorization hdist0).mp hpowdist
  have hdistprod :
      (∏ i ∈ S.erase u, Nat.dist i u) =
        u.factorial * (G - u).factorial := by
    calc
      (∏ i ∈ S.erase u, Nat.dist i u) =
          ∏ i ∈ S.erase u, (if i = u then 1 else Nat.dist i u) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg (Finset.mem_erase.mp hi).1]
      _ = ∏ i ∈ S, (if i = u then 1 else Nat.dist i u) := by
        apply Finset.prod_erase
        simp
      _ = u.factorial * (G - u).factorial := by
        simpa [S] using prod_range_dist_eq_factorials G u huG
  have hdistfac : (∏ i ∈ S.erase u, Nat.dist i u) ∣ G.factorial := by
    rw [hdistprod]
    exact Nat.factorial_mul_factorial_dvd_factorial huG
  have hdistprod0 : (∏ i ∈ S.erase u, Nat.dist i u) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact fun hzero => (Finset.mem_erase.mp hi).1
      (Nat.eq_of_dist_eq_zero hzero)
  have hfacfactor :
      (∑ i ∈ S.erase u, (Nat.dist i u).factorization p) ≤
        G.factorial.factorization p := by
    rw [← Nat.factorization_prod_apply (fun i hi =>
      (fun hzero => (Finset.mem_erase.mp hi).1
        (Nat.eq_of_dist_eq_zero hzero)))]
    exact (Nat.factorization_prime_le_iff_dvd hdistprod0 G.factorial_ne_zero).mpr
      hdistfac p hp
  rw [Nat.factorization_prod_apply haS,
    Nat.factorization_mul hlcm0 G.factorial_ne_zero, Finsupp.add_apply,
    Finset.factorization_lcm haS, hsup]
  rw [← Finset.add_sum_erase S (fun i => (a i).factorization p) huS]
  exact Nat.add_le_add_left ((Finset.sum_le_sum hterm).trans hfacfactor) _

/-- Direct covered-number form: if the modulus at offset `i` divides `n+i`,
then the same factorial overlap bound follows automatically. -/
theorem prod_dvd_lcm_mul_factorial_of_shifted_divisibility
    (G n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ i ≤ G, a i ≠ 0)
    (hdiv : ∀ i ≤ G, a i ∣ n + i) :
    (∏ i ∈ Finset.range (G + 1), a i) ∣
      (Finset.range (G + 1)).lcm a * G.factorial := by
  apply prod_dvd_lcm_mul_factorial_of_gcd_dvd_dist G a ha
  intro i hi j hj
  let d := Nat.gcd (a i) (a j)
  have hdi : d ∣ n + i := (Nat.gcd_dvd_left (a i) (a j)).trans (hdiv i hi)
  have hdj : d ∣ n + j := (Nat.gcd_dvd_right (a i) (a j)).trans (hdiv j hj)
  rcases hdi with ⟨qi, hqi⟩
  rcases hdj with ⟨qj, hqj⟩
  refine ⟨Nat.dist qi qj, ?_⟩
  rw [← Nat.dist_add_add_left n i j, hqi, hqj, Nat.dist_mul_left]

end Erdos489
