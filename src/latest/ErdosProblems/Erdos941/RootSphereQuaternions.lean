import ErdosProblems.Erdos941.HurwitzNormCongruence
import ErdosProblems.Erdos941.HurwitzSpheres
import ErdosProblems.Erdos941.RootLifting

/-! # Quadratic roots produce quaternions intertwining integral sphere points -/

namespace Erdos941

open scoped Quaternion

def pureHurwitz (v : Triple) : hurwitzOrder := ⟨pureQuaternion v, pureQuaternion_mem v⟩

def rootHurwitz (b : ℕ) (v : Triple) : hurwitzOrder := (b : hurwitzOrder) + pureHurwitz v

theorem rootHurwitz_norm {v : Triple} {n : ℕ} (hv : tripleNorm v = n) (b : ℕ) :
    hurwitzNorm (rootHurwitz b v) = b ^ 2 + n := by
  apply Nat.cast_injective (R := ℚ)
  rw [hurwitzNorm_cast, Nat.cast_add, Nat.cast_pow]
  change Quaternion.normSq ((b : ℍ[ℚ]) + pureQuaternion v) = _
  rw [Quaternion.normSq_def']
  rw [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add]
  simp only [Quaternion.re_natCast, Quaternion.imI_natCast, Quaternion.imJ_natCast,
    Quaternion.imK_natCast, pureQuaternion, zero_add, add_zero]
  have hvQ : (v.1 : ℚ) ^ 2 + (v.2.1 : ℚ) ^ 2 + (v.2.2 : ℚ) ^ 2 = n := by
    exact_mod_cast hv
  linear_combination hvQ

theorem hurwitzRootIdeal_stable (a b : ℕ) (v : Triple) {q : hurwitzOrder}
    (hq : q ∈ hurwitzRootIdeal a (rootHurwitz b v)) :
    q * pureHurwitz v ∈ hurwitzRootIdeal a (rootHurwitz b v) := by
  obtain ⟨r, s, rfl⟩ := mem_hurwitzRootIdeal.mp hq
  apply mem_hurwitzRootIdeal.mpr
  refine ⟨r * pureHurwitz v, s * pureHurwitz v, ?_⟩
  have ha : (a : hurwitzOrder) * pureHurwitz v = pureHurwitz v * a :=
    (Nat.cast_commute a (pureHurwitz v)).eq
  have hb : rootHurwitz b v * pureHurwitz v = pureHurwitz v * rootHurwitz b v := by
    dsimp [rootHurwitz]
    rw [add_mul, mul_add, (Nat.cast_commute b (pureHurwitz v)).eq]
  simp only [add_mul, mul_assoc, ha, hb]

theorem exists_root_sphere_quaternion {v : Triple} {n a b : ℕ}
    (hv : tripleNorm v = n) (ha : 0 < a) (hroot : a ∣ b ^ 2 + n)
    (han : a.Coprime (2 * n)) :
    ∃ (B : ℕ) (q s : hurwitzOrder) (w : Triple), B % a = b % a ∧
      hurwitzNorm q = a ∧ s * q = rootHurwitz B v ∧ w ∈ spherePoints n ∧
      (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q := by
  obtain ⟨B, k, hB, hBk, hak⟩ := exists_coprime_root_lift ha hroot
    (root_coprime_twice hroot han)
  have hu : hurwitzNorm (rootHurwitz B v) = a * k := by rw [rootHurwitz_norm hv, hBk]
  obtain ⟨q, hq0, hqI, hqn⟩ := hurwitzRootIdeal_generator_norm ha hu hak
  have hqmem : q ∈ hurwitzRootIdeal a (rootHurwitz B v) := by
    rw [hqI]
    exact Ideal.mem_span_singleton_self q
  have humem : rootHurwitz B v ∈ hurwitzRootIdeal a (rootHurwitz B v) :=
    mem_hurwitzRootIdeal.mpr ⟨0, 1, by simp⟩
  rw [hqI] at humem
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp humem
  have hqv := hurwitzRootIdeal_stable a B v hqmem
  rw [hqI] at hqv
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hqv
  have hq0' : (q : ℍ[ℚ]) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have hr' : (r : ℍ[ℚ]) * (q : ℍ[ℚ]) = (q : ℍ[ℚ]) * pureQuaternion v :=
    congrArg Subtype.val hr
  have hconj : (q : ℍ[ℚ]) * pureQuaternion v / (q : ℍ[ℚ]) = (r : ℍ[ℚ]) := by
    rw [← hr', mul_div_cancel_right₀ _ hq0']
  obtain ⟨w, hw, hqw⟩ := integral_conjugate_to_sphere hv hq0' (hconj ▸ r.property)
  exact ⟨B, q, s, w, hB, hqn, hs, hw, hqw⟩

end Erdos941
