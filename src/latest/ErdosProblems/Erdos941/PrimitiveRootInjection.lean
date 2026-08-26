import ErdosProblems.Erdos941.RootQuaternionInjection
import ErdosProblems.Erdos941.HurwitzParity
import ErdosProblems.Erdos941.PrimitiveTriples

/-!
# Root injection without a squarefree-modulus restriction

Primitivity of the initial sphere point makes the scalar intersection saturated
at odd moduli. Thus the geometric count can also include roots at prime powers.+-/

namespace Erdos941

open scoped Quaternion

theorem scalar_root_divisibility {v : Triple} (hv : PrimitiveTriple v)
    {a B : ℕ} (ha : a.Coprime 2) {d : ℤ} {z : ℍ[ℚ]} (hz : z ∈ hurwitzOrder)
    (heq : (a : ℍ[ℚ]) * z = (d : ℍ[ℚ]) * (rootHurwitz B v : ℍ[ℚ])) :
    (a : ℤ) ∣ d := by
  obtain ⟨r, i, j, k, hzcoord, _⟩ := (hurwitz_mem_iff_half_coordinates z).mp hz
  have hI := congrArg (fun q : ℍ[ℚ] => q.imI) heq
  have hJ := congrArg (fun q : ℍ[ℚ] => q.imJ) heq
  have hK := congrArg (fun q : ℍ[ℚ] => q.imK) heq
  rw [Quaternion.imI_mul, Quaternion.imI_mul] at hI
  rw [Quaternion.imJ_mul, Quaternion.imJ_mul] at hJ
  rw [Quaternion.imK_mul, Quaternion.imK_mul] at hK
  simp only [Quaternion.re_natCast, Quaternion.imI_natCast, Quaternion.imJ_natCast,
    Quaternion.imK_natCast, Quaternion.re_intCast, Quaternion.imI_intCast,
    Quaternion.imJ_intCast, Quaternion.imK_intCast, zero_mul, add_zero,
    sub_zero] at hI hJ hK
  rw [hzcoord] at hI hJ hK
  change (a : ℚ) * ((i : ℚ) / 2) =
    (d : ℚ) * ((B : ℍ[ℚ]) + pureQuaternion v).imI at hI
  change (a : ℚ) * ((j : ℚ) / 2) =
    (d : ℚ) * ((B : ℍ[ℚ]) + pureQuaternion v).imJ at hJ
  change (a : ℚ) * ((k : ℚ) / 2) =
    (d : ℚ) * ((B : ℍ[ℚ]) + pureQuaternion v).imK at hK
  rw [Quaternion.imI_add, Quaternion.imI_natCast, zero_add] at hI
  rw [Quaternion.imJ_add, Quaternion.imJ_natCast, zero_add] at hJ
  rw [Quaternion.imK_add, Quaternion.imK_natCast, zero_add] at hK
  change (a : ℚ) * ((i : ℚ) / 2) = (d : ℚ) * v.1 at hI
  change (a : ℚ) * ((j : ℚ) / 2) = (d : ℚ) * v.2.1 at hJ
  change (a : ℚ) * ((k : ℚ) / 2) = (d : ℚ) * v.2.2 at hK
  have hi : (a : ℤ) ∣ 2 * d * v.1 := ⟨i, by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith⟩
  have hj : (a : ℤ) ∣ 2 * d * v.2.1 := ⟨j, by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith⟩
  have hk : (a : ℤ) ∣ 2 * d * v.2.2 := ⟨k, by
    apply Int.cast_injective (α := ℚ)
    push_cast
    linarith⟩
  obtain ⟨x, y, w, hprim⟩ := hv
  have hdiv : (a : ℤ) ∣ 2 * d := by
    have hh := dvd_add (dvd_add (dvd_mul_of_dvd_right hi x)
      (dvd_mul_of_dvd_right hj y)) (dvd_mul_of_dvd_right hk w)
    have he : 2 * d = x * (2 * d * v.1) + y * (2 * d * v.2.1) +
        w * (2 * d * v.2.2) := by linear_combination -2 * d * hprim
    rwa [← he] at hh
  exact ha.isCoprime.dvd_of_dvd_mul_left hdiv

theorem rootHurwitz_factor_unique_mod_primitive {a B C : ℕ}
    (ha : a.Coprime 2) {v : Triple} (hv : PrimitiveTriple v)
    {q s t : hurwitzOrder} (hq : hurwitzNorm q = a)
    (hs : s * q = rootHurwitz B v) (ht : t * q = rootHurwitz C v) :
    B % a = C % a := by
  let d : ℤ := (B : ℤ) - C
  let r : ℍ[ℚ] := (s : ℍ[ℚ]) - t
  have hsub : r * (q : ℍ[ℚ]) = (d : ℍ[ℚ]) := by
    change (((s - t) * q : hurwitzOrder) : ℍ[ℚ]) = _
    rw [sub_mul, hs, ht, rootHurwitz_sub]
    rfl
  have hstar : star (q : ℍ[ℚ]) * star r = (d : ℍ[ℚ]) := by
    rw [← star_mul, hsub, star_intCast]
  have hnorm : (q : ℍ[ℚ]) * star (q : ℍ[ℚ]) = (a : ℍ[ℚ]) := by
    rw [Quaternion.self_mul_star, ← hurwitzNorm_cast, hq, Quaternion.coe_natCast]
  have hs' : (s : ℍ[ℚ]) * q = rootHurwitz B v := congrArg Subtype.val hs
  have heq : (a : ℍ[ℚ]) * ((s : ℍ[ℚ]) * star r) =
      (d : ℍ[ℚ]) * (rootHurwitz B v : ℍ[ℚ]) := by
    calc
      _ = (s : ℍ[ℚ]) * ((a : ℍ[ℚ]) * star r) := by
        rw [← mul_assoc, (Nat.cast_commute a (s : ℍ[ℚ])).eq, mul_assoc]
      _ = (s : ℍ[ℚ]) * (((q : ℍ[ℚ]) * star (q : ℍ[ℚ])) * star r) := by rw [hnorm]
      _ = (s : ℍ[ℚ]) * ((q : ℍ[ℚ]) * d) := by rw [mul_assoc, hstar]
      _ = (d : ℍ[ℚ]) * ((s : ℍ[ℚ]) * q) := by
        rw [← mul_assoc, ← (Int.cast_commute d ((s : ℍ[ℚ]) * q)).eq]
      _ = _ := by rw [hs']
  have hz : (s : ℍ[ℚ]) * star r ∈ hurwitzOrder :=
    hurwitzOrder.mul_mem s.property (hurwitz_star_mem (hurwitzOrder.sub_mem s.property t.property))
  exact (Nat.modEq_iff_dvd.mpr (scalar_root_divisibility hv ha hz heq)).symm

end Erdos941
