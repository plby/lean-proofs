import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Local norm calculations for the three-square construction
-/

namespace Erdos941

theorem prime_dvd_norm_forces_coordinates {p : ℕ} [Fact p.Prime] {m x y : ℤ}
    (hm : ¬ IsSquare (-(m : ZMod p))) (h : (p : ℤ) ∣ x ^ 2 + m * y ^ 2) :
    (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 + m * y ^ 2) p).mpr h
  push_cast at hh
  have hy : (y : ZMod p) = 0 := by
    by_contra hny
    apply hm
    refine ⟨(x : ZMod p) / (y : ZMod p), ?_⟩
    field_simp
    linear_combination -hh
  have hx : (x : ZMod p) = 0 := by
    rw [hy] at hh
    simpa using hh
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy⟩

/-- At an anisotropic prime a binary norm has even valuation, including norm zero. -/
theorem even_padicValInt_norm {p : ℕ} [hp : Fact p.Prime] (m : ℤ)
    (hm : ¬ IsSquare (-(m : ZMod p))) (x y : ℤ) :
    Even (padicValInt p (x ^ 2 + m * y ^ 2)) := by
  generalize heq : (x ^ 2 + m * y ^ 2).natAbs = k
  induction k using Nat.strong_induction_on generalizing x y with
  | h k ih =>
    by_cases hz : x ^ 2 + m * y ^ 2 = 0
    · simp [hz]
    by_cases hd : (p : ℤ) ∣ x ^ 2 + m * y ^ 2
    · obtain ⟨hpx, hpy⟩ := prime_dvd_norm_forces_coordinates hm hd
      obtain ⟨u, rfl⟩ := hpx
      obtain ⟨v, rfl⟩ := hpy
      have hnorm : ((p : ℤ) * u) ^ 2 + m * ((p : ℤ) * v) ^ 2 =
          (p : ℤ) ^ 2 * (u ^ 2 + m * v ^ 2) := by ring
      have hnz : u ^ 2 + m * v ^ 2 ≠ 0 := by
        intro hzero
        apply hz
        rw [hnorm, hzero, mul_zero]
      have habs : p ^ 2 * (u ^ 2 + m * v ^ 2).natAbs = k := by
        rw [hnorm, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heq
        exact heq
      have hpos : 0 < (u ^ 2 + m * v ^ 2).natAbs := Int.natAbs_pos.mpr hnz
      have hlt : (u ^ 2 + m * v ^ 2).natAbs < k := by
        calc
          (u ^ 2 + m * v ^ 2).natAbs = 1 * (u ^ 2 + m * v ^ 2).natAbs := by simp
          _ < p ^ 2 * (u ^ 2 + m * v ^ 2).natAbs :=
            mul_lt_mul_of_pos_right (by nlinarith [hp.out.two_le]) hpos
          _ = k := habs
      have hi := ih _ hlt u v rfl
      have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
      have hval : padicValInt p ((p : ℤ) ^ 2) = 2 := by
        rw [pow_two, padicValInt.mul hp0 hp0, padicValInt_self]
      rw [hnorm, padicValInt.mul (pow_ne_zero _ hp0) hnz, hval]
      exact (by decide : Even (2 : ℕ)).add hi
    · rw [padicValInt.eq_zero_of_not_dvd hd]
      exact Even.zero

theorem not_isSquare_neg_of_square {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3)
    {m : ZMod p} (hm : m ≠ 0) (hs : IsSquare m) : ¬ IsSquare (-m) := by
  obtain ⟨r, hr⟩ := hs
  rintro ⟨s, hs⟩
  have hr0 : r ≠ 0 := by
    intro h
    simp only [h, mul_zero] at hr
    exact hm hr
  have heq : s ^ 2 = -r ^ 2 := by
    rw [pow_two, ← hs, hr, pow_two]
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hr0 heq) hp3

/-- The ramified-prime step of the lattice construction. -/
theorem ankeny_ramified_square {p : ℕ} [hp : Fact p.Prime]
    {m a k R U y : ℤ} (hpm : (p : ℤ) ∣ m) (hpk : (p : ℤ) ∣ k)
    (hm2 : ¬ (p : ℤ) ^ 2 ∣ m) (hm : m = R ^ 2 + k)
    (hk : a * k = U ^ 2 + m * y ^ 2) : IsSquare (a : ZMod p) := by
  have pm0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr hpm
  have pk0 := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr hpk
  have hmz := congrArg (fun z : ℤ => (z : ZMod p)) hm
  have hkz := congrArg (fun z : ℤ => (z : ZMod p)) hk
  push_cast at hmz hkz
  have pr0 : (R : ZMod p) = 0 := by
    rw [pm0, pk0] at hmz
    simpa using hmz.symm
  have pu0 : (U : ZMod p) = 0 := by
    rw [pm0, pk0] at hkz
    simpa using hkz.symm
  obtain ⟨r, hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp pr0
  obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd U p).mp pu0
  obtain ⟨m', hm'⟩ := hpm
  obtain ⟨k', hk'⟩ := hpk
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.out.ne_zero
  have hfirst : m' = (p : ℤ) * r ^ 2 + k' := by
    apply mul_left_cancel₀ hp0
    rw [hm', hr, hk'] at hm
    linear_combination hm
  have hsecond : a * k' = (p : ℤ) * u ^ 2 + m' * y ^ 2 := by
    apply mul_left_cancel₀ hp0
    rw [hm', hu, hk'] at hk
    linear_combination hk
  have hm'0 : (m' : ZMod p) ≠ 0 := by
    intro hh
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m' p).mp hh
    apply hm2
    refine ⟨t, ?_⟩
    rw [hm', ht]
    ring
  have hfirstz := congrArg (fun z : ℤ => (z : ZMod p)) hfirst
  have hsecondz := congrArg (fun z : ℤ => (z : ZMod p)) hsecond
  push_cast at hfirstz hsecondz
  simp only [ZMod.natCast_self, zero_mul, zero_add] at hfirstz hsecondz
  rw [← hfirstz] at hsecondz
  refine ⟨(y : ZMod p), ?_⟩
  apply mul_left_cancel₀ hm'0
  linear_combination hsecondz

theorem ankeny_ramified_not_dvd {p : ℕ} [hp : Fact p.Prime]
    (hp3 : p % 4 = 3) {m a k R U y : ℤ} (hpm : (p : ℤ) ∣ m)
    (hpa : ¬ (p : ℤ) ∣ a) (hm2 : ¬ (p : ℤ) ^ 2 ∣ m)
    (hs : IsSquare (-(a : ZMod p))) (hm : m = R ^ 2 + k)
    (hk : a * k = U ^ 2 + m * y ^ 2) : ¬ (p : ℤ) ∣ k := by
  intro hpk
  have ha0 : (a : ZMod p) ≠ 0 := by
    exact fun hh => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hh)
  exact not_isSquare_neg_of_square hp3 ha0
    (ankeny_ramified_square hpm hpk hm2 hm hk) hs

/-- The complete local arithmetic conclusion from an Ankeny lattice point.
The prime-selection and geometry steps supply the displayed hypotheses. -/
theorem ankeny_two_squares {m k a : ℕ} {R U y : ℤ}
    (ha : 0 < a) (hm : Squarefree m)
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 3 →
      ¬ p ∣ a ∧ (p ∣ m → IsSquare (-(a : ZMod p))))
    (hR : (m : ℤ) = R ^ 2 + k) (hU : (a : ℤ) * k = U ^ 2 + m * y ^ 2) :
    ∃ x z : ℕ, k = x ^ 2 + z ^ 2 := by
  apply Nat.eq_sq_add_sq_iff.mpr
  intro p hp hp3
  have hpp := Nat.prime_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hpa, hres⟩ := hprime p hpp hp3
  have hpa' : ¬ (p : ℤ) ∣ (a : ℤ) := by exact_mod_cast hpa
  by_cases hpm : p ∣ m
  · have hm2 : ¬ (p : ℤ) ^ 2 ∣ (m : ℤ) := by
      have hh := Nat.squarefree_iff_prime_squarefree.mp hm p hpp
      simpa only [pow_two, ← Int.natCast_mul, Int.natCast_dvd_natCast] using hh
    have hnot := ankeny_ramified_not_dvd hp3 (by exact_mod_cast hpm) hpa' hm2
      (by simpa only [Int.cast_natCast] using hres hpm) hR hU
    exact (hnot (by exact_mod_cast Nat.dvd_of_mem_primeFactors hp)).elim
  · have hpm0 : (m : ZMod p) ≠ 0 := by
      exact fun hh => hpm ((ZMod.natCast_eq_zero_iff m p).mp hh)
    have hk0 : (k : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff k p).mpr (Nat.dvd_of_mem_primeFactors hp)
    have hRz := congrArg (fun z : ℤ => (z : ZMod p)) hR
    push_cast at hRz
    rw [hk0, add_zero] at hRz
    have hsq : IsSquare (m : ZMod p) := ⟨(R : ZMod p), by simpa [pow_two] using hRz⟩
    have hms : ¬ IsSquare (-((m : ℤ) : ZMod p)) := by
      simpa only [Int.cast_natCast] using not_isSquare_neg_of_square hp3 hpm0 hsq
    have heven := even_padicValInt_norm (m : ℤ) hms U y
    rw [← hU] at heven
    have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have hkne : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).2.2
    rw [padicValInt.mul ha0 hkne, padicValInt.eq_zero_of_not_dvd hpa',
      zero_add, padicValInt.of_nat] at heven
    exact heven

end Erdos941
