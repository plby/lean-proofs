import ErdosProblems.Erdos941.HurwitzDivision

/-! # Norm congruences in the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

theorem hurwitz_trace_integral {q : ℍ[ℚ]} (hq : q ∈ hurwitzOrder) :
    ∃ t : ℤ, (t : ℚ) = 2 * q.re := by
  obtain ⟨a, b, c, d, rfl⟩ := hq
  refine ⟨2 * a + d, ?_⟩
  dsimp [hurwitzCoordinates]
  push_cast
  ring

theorem hurwitzNorm_natCast (a : ℕ) : hurwitzNorm (a : hurwitzOrder) = a ^ 2 := by
  apply Nat.cast_injective (R := ℚ)
  rw [hurwitzNorm_cast, Nat.cast_pow]
  exact Quaternion.normSq_natCast a

theorem hurwitzNorm_intCast (a : ℤ) : (hurwitzNorm (a : hurwitzOrder) : ℤ) = a ^ 2 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hurwitzNorm_cast]
  exact Quaternion.normSq_intCast a

theorem hurwitzNorm_scalar_add (a : ℕ) (r s : hurwitzOrder) :
    ∃ t : ℤ, (hurwitzNorm (r * (a : hurwitzOrder) + s) : ℤ) =
      (a : ℤ) * t + (hurwitzNorm s : ℤ) := by
  obtain ⟨t, ht⟩ := hurwitz_trace_integral
    (hurwitzOrder.mul_mem r.property (hurwitz_star_mem s.property))
  refine ⟨(a : ℤ) * hurwitzNorm r + t, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hurwitzNorm_cast, hurwitzNorm_cast, hurwitzNorm_cast]
  have heq : ((r * (a : hurwitzOrder) + s : hurwitzOrder) : ℍ[ℚ]) =
      (a : ℚ) • (r : ℍ[ℚ]) + (s : ℍ[ℚ]) := by
    change (r : ℍ[ℚ]) * (a : ℍ[ℚ]) + (s : ℍ[ℚ]) = _
    rw [← Quaternion.coe_natCast, Quaternion.mul_coe_eq_smul]
  rw [heq, Quaternion.normSq_add, Quaternion.normSq_smul,
    smul_mul_assoc, Quaternion.re_smul]
  change _ = _ + _
  linear_combination -(a : ℚ) * ht

def hurwitzRootIdeal (a : ℕ) (u : hurwitzOrder) : Ideal hurwitzOrder :=
  Ideal.span {(a : hurwitzOrder), u}

theorem mem_hurwitzRootIdeal {a : ℕ} {u q : hurwitzOrder} :
    q ∈ hurwitzRootIdeal a u ↔
      ∃ r s : hurwitzOrder, r * (a : hurwitzOrder) + s * u = q := by
  rw [hurwitzRootIdeal, Ideal.span_insert, Ideal.mem_span_singleton_sup]
  constructor
  · rintro ⟨r, v, hv, heq⟩
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    exact ⟨r, s, heq⟩
  · rintro ⟨r, s, heq⟩
    exact ⟨r, s * u, Ideal.mem_span_singleton'.mpr ⟨s, rfl⟩, heq⟩

theorem hurwitzRootIdeal_norm_dvd {a : ℕ} {u q : hurwitzOrder}
    (hu : a ∣ hurwitzNorm u) (hq : q ∈ hurwitzRootIdeal a u) : a ∣ hurwitzNorm q := by
  obtain ⟨r, s, rfl⟩ := mem_hurwitzRootIdeal.mp hq
  obtain ⟨t, ht⟩ := hurwitzNorm_scalar_add a r (s * u)
  have hs : a ∣ hurwitzNorm (s * u) := by
    rw [hurwitzNorm_mul]
    exact dvd_mul_of_dvd_right hu _
  have hh : (a : ℤ) ∣ (hurwitzNorm (r * (a : hurwitzOrder) + s * u) : ℤ) := by
    rw [ht]
    exact dvd_add (dvd_mul_right _ _) (by exact_mod_cast hs)
  exact_mod_cast hh

theorem hurwitzRootIdeal_generator_norm {a k : ℕ} (ha : 0 < a) {u : hurwitzOrder}
    (hu : hurwitzNorm u = a * k) (hak : a.Coprime k) :
    ∃ q : hurwitzOrder, q ≠ 0 ∧ hurwitzRootIdeal a u = Ideal.span {q} ∧
      hurwitzNorm q = a := by
  obtain ⟨q, hq⟩ := hurwitz_left_ideal_principal (hurwitzRootIdeal a u)
  have hqmem : q ∈ hurwitzRootIdeal a u := by
    rw [hq]
    exact Ideal.mem_span_singleton_self q
  have hamem : (a : hurwitzOrder) ∈ hurwitzRootIdeal a u :=
    mem_hurwitzRootIdeal.mpr ⟨1, 0, by simp⟩
  have humem : u ∈ hurwitzRootIdeal a u :=
    mem_hurwitzRootIdeal.mpr ⟨0, 1, by simp⟩
  rw [hq] at hamem humem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hamem
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp humem
  have hdA : hurwitzNorm q ∣ a ^ 2 := by
    rw [← hurwitzNorm_natCast, ← hr, hurwitzNorm_mul]
    exact dvd_mul_left _ _
  have hdU : hurwitzNorm q ∣ a * k := by
    rw [← hu, ← hs, hurwitzNorm_mul]
    exact dvd_mul_left _ _
  have hd : hurwitzNorm q ∣ a := by
    have hh := Nat.dvd_gcd hdA hdU
    rwa [pow_two, Nat.gcd_mul_left, hak.gcd_eq_one, mul_one] at hh
  have hd' : a ∣ hurwitzNorm q :=
    hurwitzRootIdeal_norm_dvd (by rw [hu]; exact dvd_mul_right _ _) hqmem
  have hnorm : hurwitzNorm q = a := Nat.dvd_antisymm hd hd'
  refine ⟨q, ?_, hq, hnorm⟩
  intro hz
  have hh := (hurwitzNorm_eq_zero q).mpr hz
  omega

end Erdos941
