import ErdosProblems.Erdos489.RoughCoprimePairs
import ErdosProblems.Erdos489.RoughPrimeSum

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- A finite set in an interval whose pairwise distances are multiples of `d`
has at most `G / d + 1` elements. -/
theorem spaced_interval_card_le
    (S : Finset ℕ) (L G d : ℕ) (hd : 0 < d)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, d ∣ Nat.dist x y) :
    S.card ≤ G / d + 1 := by
  let f : ℕ → ℕ := fun n => (n - L) / d
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro x hx y hy heq
    have hxL := (hinterval x hx).1
    have hyL := (hinterval y hy).1
    rcases le_total x y with hxy | hyx
    · have hddiv : d ∣ y - x := by
        simpa [Nat.dist_eq_sub_of_le hxy] using hsep x hx y hy
      have hxlow : d * ((x - L) / d) ≤ x - L := Nat.mul_div_le _ _
      have hyup : y - L < d * ((y - L) / d + 1) := Nat.lt_mul_div_succ _ hd
      have hdiffshift : (y - L) - (x - L) = y - x := by omega
      have hdiff : y - x < d := by
        dsimp [f] at heq
        rw [← heq, Nat.mul_add] at hyup
        simp only [mul_one] at hyup
        rw [← hdiffshift]
        omega
      have hz : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hddiv hdiff
      omega
    · apply Eq.symm
      apply Nat.le_antisymm hyx
      have hddiv : d ∣ x - y := by
        have hdxy := hsep x hx y hy
        rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx] at hdxy
        exact hdxy
      have hylow : d * ((y - L) / d) ≤ y - L := Nat.mul_div_le _ _
      have hxup : x - L < d * ((x - L) / d + 1) := Nat.lt_mul_div_succ _ hd
      have hdiffshift : (x - L) - (y - L) = x - y := by omega
      have hdiff : x - y < d := by
        dsimp [f] at heq
        rw [heq, Nat.mul_add] at hxup
        simp only [mul_one] at hxup
        rw [← hdiffshift]
        omega
      have hz : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hddiv hdiff
      omega
  have himage : S.image f ⊆ Finset.range (G / d + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnI := hinterval n hn
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsub : n - L ≤ G := by omega
    have := (Nat.div_le_div_right hsub : (n - L) / d ≤ G / d)
    omega
  calc
    S.card = (S.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (G / d + 1)).card := Finset.card_le_card himage
    _ = G / d + 1 := Finset.card_range _

/-- In one prime fiber of a progression `n ≡ 1 (mod Q)`, the points are
`Qp`-spaced. -/
theorem progression_primeFiber_card_le
    (S : Finset ℕ) (L G Q p : ℕ) (hQ : 0 < Q) (hp : Nat.Prime p)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hpQ : ¬p ∣ Q) :
    (multiplesIn S p).card ≤ G / (Q * p) + 1 := by
  let M := multiplesIn S p
  have hcop : Nat.Coprime Q p :=
    (hp.coprime_iff_not_dvd.mpr hpQ).symm
  apply spaced_interval_card_le M L G (Q * p) (Nat.mul_pos hQ hp.pos)
  · intro n hn
    exact hinterval n (Finset.mem_filter.mp hn).1
  · intro x hx y hy
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    have hQdist : Q ∣ Nat.dist x y := by
      rcases le_total x y with hxy | hyx
      · rw [Nat.dist_eq_sub_of_le hxy]
        apply (Nat.modEq_iff_dvd' hxy).mp
        exact (hcong x hxS).trans (hcong y hyS).symm
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
        apply (Nat.modEq_iff_dvd' hyx).mp
        exact (hcong y hyS).trans (hcong x hxS).symm
    have hpdist : p ∣ Nat.dist x y := by
      rcases le_total x y with hxy | hyx
      · rw [Nat.dist_eq_sub_of_le hxy]
        exact Nat.dvd_sub hpy hpx
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
        exact Nat.dvd_sub hpx hpy
    exact hcop.mul_dvd_of_dvd_of_dvd hQdist hpdist

/-- Prime-fiber union bound for points in `n ≡ 1 (mod Q)`, when every prime
at most `Y` divides `Q`. -/
theorem progression_noncoprimePairs_card_le_prime_sum
    (S : Finset ℕ) (L G Q Y : ℕ) (hQ : 0 < Q)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) :
    (noncoprimeOrderedPairs S).card ≤
      ∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (G / (Q * p) + 1) ^ 2 := by
  apply noncoprimeOrderedPairs_card_le_primeFiber_sum S Y G
    (fun p => G / (Q * p) + 1)
  · intro n hn p hp hpn
    by_contra hnot
    have hpY : p ≤ Y := by omega
    have hpQ : p ∣ Q := hsmall p hp hpY
    have hp1 : p ∣ 1 := ((hcong n hn).dvd_iff hpQ).mp hpn
    exact hp.ne_one (Nat.dvd_one.mp hp1)
  · intro x hx y hy
    have hxI := hinterval x hx
    have hyI := hinterval y hy
    rcases le_total x y with hxy | hyx
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
      omega
  · intro p hpP
    have hp : Nat.Prime p :=
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hpP).1).2
    by_cases hM : (multiplesIn S p).Nonempty
    · obtain ⟨n, hnM⟩ := hM
      have hnS : n ∈ S := (Finset.mem_filter.mp hnM).1
      have hpn : p ∣ n := (Finset.mem_filter.mp hnM).2
      have hpnotQ : ¬p ∣ Q := by
        intro hpQ
        have hp1 : p ∣ 1 := ((hcong n hnS).dvd_iff hpQ).mp hpn
        exact hp.ne_one (Nat.dvd_one.mp hp1)
      exact progression_primeFiber_card_le S L G Q p hQ hp hinterval hcong hpnotQ
    · rw [Finset.not_nonempty_iff_eq_empty.mp hM]
      simp

/-- The reciprocal-square estimate with a numerator `H` independent of the
upper prime cutoff `G`. -/
theorem prime_fiber_square_sum_num_cast_le
    (H Y G : ℕ) (hY : 0 < Y) :
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((H / p + 1) ^ 2 : ℕ) : ℝ)) ≤
      2 * (H : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  have hpLower : ∀ p ∈ P, Y < p := by
    intro p hp
    have hpG := Finset.mem_sdiff.mp hp
    have hpprime := (Nat.mem_primesBelow.mp hpG.1).2
    by_contra hnot
    have hpY : p < Y + 1 := by omega
    exact hpG.2 (Nat.mem_primesBelow.mpr ⟨hpY, hpprime⟩)
  have hpUpper : ∀ p ∈ P, p ≤ G := by
    intro p hp
    have := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
    omega
  have hrecip : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (Y : ℝ) :=
    finset_sum_one_div_sq_le P Y G hY hpLower hpUpper
  have hterm : ∀ p ∈ P,
      (((H / p + 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
    intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hq : ((H / p : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hq0 : (0 : ℝ) ≤ (H / p : ℕ) := by positivity
    have hratio0 : (0 : ℝ) ≤ (H : ℝ) / (p : ℝ) := by positivity
    have hsq : (((H / p : ℕ) : ℝ)) ^ 2 ≤ ((H : ℝ) / (p : ℝ)) ^ 2 :=
      (sq_le_sq₀ hq0 hratio0).2 hq
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hbasic : ((((H / p : ℕ) : ℝ)) + 1) ^ 2 ≤
        2 * (((H / p : ℕ) : ℝ)) ^ 2 + 2 := by
      nlinarith [sq_nonneg ((((H / p : ℕ) : ℝ)) - 1)]
    calc
      ((((H / p : ℕ) : ℝ)) + 1) ^ 2 ≤
          2 * (((H / p : ℕ) : ℝ)) ^ 2 + 2 := hbasic
      _ ≤ 2 * ((H : ℝ) / (p : ℝ)) ^ 2 + 2 := by nlinarith
      _ = 2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
        field_simp
  have hPsubset : P ⊆ Finset.range (G + 1) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
  have hcardNat : P.card ≤ G + 1 := by
    simpa using Finset.card_le_card hPsubset
  have hcard : (P.card : ℝ) ≤ ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((H / p + 1) ^ 2 : ℕ) : ℝ)) =
        ∑ p ∈ P, (((H / p + 1) ^ 2 : ℕ) : ℝ) := rfl
    _ ≤ ∑ p ∈ P,
        (2 * (H : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = 2 * (H : ℝ) ^ 2 *
          (∑ p ∈ P, ((1 : ℝ) / (p : ℝ) ^ 2)) + 2 * (P.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (H : ℝ) ^ 2 * (1 / (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      have hH0 : 0 ≤ 2 * (H : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecip hH0]
    _ = 2 * (H : ℝ) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := by ring

/-- Explicit progression version: ordered noncoprime pairs have quadratic
coefficient at most `2/(Q²Y)`, plus a linear endpoint term. -/
theorem noncoprimeOrderedPairs_cast_le_progression
    (S : Finset ℕ) (L G Q Y : ℕ) (hQ : 0 < Q) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hcong : ∀ n ∈ S, Nat.ModEq Q n 1)
    (hsmall : ∀ p, Nat.Prime p → p ≤ Y → p ∣ Q) :
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
      2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
        2 * ((G + 1 : ℕ) : ℝ) := by
  have hnat := progression_noncoprimePairs_card_le_prime_sum
    S L G Q Y hQ hinterval hcong hsmall
  have hcast : ((noncoprimeOrderedPairs S).card : ℝ) ≤
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) := by
    rw [show (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) =
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / (Q * p) + 1) ^ 2 : ℕ) : ℝ)) by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Nat.div_div_eq_div_mul]]
    exact_mod_cast hnat
  have hsum := prime_fiber_square_sum_num_cast_le (G / Q) Y G hY
  have hdiv : ((G / Q : ℕ) : ℝ) ≤ (G : ℝ) / (Q : ℝ) := Nat.cast_div_le
  have hdiv0 : (0 : ℝ) ≤ (G / Q : ℕ) := by positivity
  have hratio0 : (0 : ℝ) ≤ (G : ℝ) / (Q : ℝ) := by positivity
  have hsq : ((G / Q : ℕ) : ℝ) ^ 2 ≤ ((G : ℝ) / (Q : ℝ)) ^ 2 :=
    (sq_le_sq₀ hdiv0 hratio0).2 hdiv
  calc
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
        (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
          ((((G / Q) / p + 1) ^ 2 : ℕ) : ℝ)) := hcast
    _ ≤ 2 * ((G / Q : ℕ) : ℝ) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := hsum
    _ ≤ 2 * ((G : ℝ) / (Q : ℝ)) ^ 2 / (Y : ℝ) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      have hY0 : (0 : ℝ) ≤ (Y : ℝ) := by positivity
      have hnum : 2 * ((G / Q : ℕ) : ℝ) ^ 2 ≤
          2 * ((G : ℝ) / (Q : ℝ)) ^ 2 := by nlinarith
      have hquot := div_le_div_of_nonneg_right hnum hY0
      linarith
    _ = 2 * (G : ℝ) ^ 2 / ((Q : ℝ) ^ 2 * (Y : ℝ)) +
          2 * ((G + 1 : ℕ) : ℝ) := by
      field_simp <;> ring

end Erdos489
