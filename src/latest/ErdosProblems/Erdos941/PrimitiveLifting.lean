import ErdosProblems.Erdos941.TripleRotations
import Mathlib.NumberTheory.SumFourSquares

/-! # Primitive three-square representations survive multiplication by odd prime squares -/

namespace Erdos941

theorem PrimitiveTriple.not_divisible {v : Triple} (hv : PrimitiveTriple v)
    {p : ℕ} (hp : p.Prime) : ¬TripleDivisible p v := by
  intro hd
  obtain ⟨a, b, c, h⟩ := hv
  have h1 : (p : ℤ) ∣ 1 := by
    rw [← h]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right hd.1 a)
      (dvd_mul_of_dvd_right hd.2.1 b)) (dvd_mul_of_dvd_right hd.2.2 c)
  have hN : p ∣ 1 := by exact_mod_cast h1
  exact hp.ne_one (Nat.dvd_one.mp hN)

theorem primitiveTriple_of_no_prime_divisor {v : Triple}
    (hv : ∀ p : ℕ, p.Prime → ¬TripleDivisible p v) : PrimitiveTriple v := by
  let h : ℤ := Int.gcd v.2.1 v.2.2
  let g : ℕ := Int.gcd v.1 h
  have hA : (g : ℤ) ∣ v.1 := Int.gcd_dvd_left _ _
  have hh : (g : ℤ) ∣ h := Int.gcd_dvd_right _ _
  have hB : (g : ℤ) ∣ v.2.1 := dvd_trans hh (Int.gcd_dvd_left _ _)
  have hC : (g : ℤ) ∣ v.2.2 := dvd_trans hh (Int.gcd_dvd_right _ _)
  have hg : g = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hpg
    have hpgI : (p : ℤ) ∣ (g : ℤ) := by exact_mod_cast hpg
    exact hv p hp ⟨dvd_trans hpgI hA, dvd_trans hpgI hB, dvd_trans hpgI hC⟩
  have h₁ := Int.gcd_eq_gcd_ab v.1 h
  have h₂ := Int.gcd_eq_gcd_ab v.2.1 v.2.2
  change (g : ℤ) = _ at h₁
  change h = _ at h₂
  rw [hg, Nat.cast_one] at h₁
  refine ⟨Int.gcdA v.1 h, Int.gcdA v.2.1 v.2.2 * Int.gcdB v.1 h,
    Int.gcdB v.2.1 v.2.2 * Int.gcdB v.1 h, ?_⟩
  linear_combination -h₁ - (Int.gcdB v.1 h) * h₂

theorem eulerTripleMap_primitive {p : ℕ} (hp : p.Prime)
    {a b c d : ℤ} (hn : fourNorm a b c d = p)
    {v : Triple} (hv : PrimitiveTriple v)
    (hnew : ¬TripleDivisible p (eulerTripleMap a b c d v)) :
    PrimitiveTriple (eulerTripleMap a b c d v) := by
  apply primitiveTriple_of_no_prime_divisor
  intro r hr hdiv
  by_cases hrp : r = p
  · subst r
    exact hnew hdiv
  · have hrI : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    have hrpI : ¬(r : ℤ) ∣ (p : ℤ) := by
      intro h
      have hN : r ∣ p := by exact_mod_cast h
      exact hrp ((Nat.dvd_prime hp).mp hN |>.resolve_left hr.ne_one)
    have hrpp : ¬(r : ℤ) ∣ (p : ℤ) ^ 2 := fun h => hrpI (hrI.dvd_of_dvd_pow h)
    have hh := hdiv.linearMap (eulerTripleMap a (-b) (-c) (-d))
    rw [eulerTripleMap_inverse, hn] at hh
    exact hv.not_divisible hr ⟨(hrI.dvd_mul.mp hh.1).resolve_left hrpp,
      (hrI.dvd_mul.mp hh.2.1).resolve_left hrpp,
      (hrI.dvd_mul.mp hh.2.2).resolve_left hrpp⟩

theorem exists_primitive_prime_square_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {v : Triple} (hv : PrimitiveTriple v) :
    ∃ w : Triple, PrimitiveTriple w ∧ tripleNorm w = (p : ℤ) ^ 2 * tripleNorm v := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares p
  have hn : fourNorm a b c d = p := by
    dsimp [fourNorm]
    exact_mod_cast habcd
  obtain ⟨u, hu, hpu, hnot⟩ := exists_primitive_rotate_nondvd hp hp2 hv
    (eulerTripleMap a b c d) (eulerTripleMap_nonzero_mod_prime hp hp2 hn)
  refine ⟨eulerTripleMap a b c d u, eulerTripleMap_primitive hp hn hpu hnot, ?_⟩
  rw [eulerTripleMap_norm, hn, hu]

end Erdos941
