import ErdosProblems.Erdos941.HurwitzDivision
import ErdosProblems.Erdos941.Spheres

/-! # Pure Hurwitz quaternions and integral spheres -/

namespace Erdos941

open scoped Quaternion

def pureQuaternion (v : Triple) : ℍ[ℚ] :=
  ⟨0, (v.1 : ℚ), (v.2.1 : ℚ), (v.2.2 : ℚ)⟩

theorem pureQuaternion_mem (v : Triple) : pureQuaternion v ∈ hurwitzOrder :=
  integralQuaternion_mem 0 v.1 v.2.1 v.2.2

theorem pureQuaternion_norm (v : Triple) :
    Quaternion.normSq (pureQuaternion v) = (tripleNorm v : ℚ) := by
  rw [Quaternion.normSq_def']
  dsimp [pureQuaternion, tripleNorm, norm3]
  push_cast
  ring

theorem pureQuaternion_injective : Function.Injective pureQuaternion := by
  intro v w h
  have hA := congrArg (fun q : ℍ[ℚ] => q.imI) h
  have hB := congrArg (fun q : ℍ[ℚ] => q.imJ) h
  have hC := congrArg (fun q : ℍ[ℚ] => q.imK) h
  dsimp [pureQuaternion] at hA hB hC
  apply Prod.ext
  · exact_mod_cast hA
  · apply Prod.ext
    · exact_mod_cast hB
    · exact_mod_cast hC

theorem pure_hurwitz_integral {q : ℍ[ℚ]} (hq : q ∈ hurwitzOrder) (hre : q.re = 0) :
    ∃ v : Triple, q = pureQuaternion v := by
  obtain ⟨a, b, c, d, rfl⟩ := hq
  change (a : ℚ) + (d : ℚ) / 2 = 0 at hre
  refine ⟨(b - a, c - a, -a), ?_⟩
  apply Quaternion.ext <;> dsimp [hurwitzCoordinates, pureQuaternion]
  · exact hre
  · push_cast; linarith
  · push_cast; linarith
  · push_cast; linarith

theorem quaternion_re_mul_comm (q r : ℍ[ℚ]) : (q * r).re = (r * q).re := by
  rw [Quaternion.re_mul, Quaternion.re_mul]
  ring

theorem quaternion_conjugate_re (q v : ℍ[ℚ]) (hq : q ≠ 0) :
    (q * v / q).re = v.re := by
  rw [div_eq_mul_inv, quaternion_re_mul_comm, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

theorem quaternion_conjugate_norm (q v : ℍ[ℚ]) (hq : q ≠ 0) :
    Quaternion.normSq (q * v / q) = Quaternion.normSq v := by
  rw [Quaternion.normSq_div, map_mul]
  exact mul_div_cancel_left₀ _ (Quaternion.normSq_ne_zero.mpr hq)

theorem integral_conjugate_to_sphere {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    {q : ℍ[ℚ]} (hq : q ≠ 0) (hint : q * pureQuaternion v / q ∈ hurwitzOrder) :
    ∃ w : Triple, w ∈ spherePoints n ∧ q * pureQuaternion v = pureQuaternion w * q := by
  have hre : (q * pureQuaternion v / q).re = 0 := by
    rw [quaternion_conjugate_re _ _ hq]
    rfl
  obtain ⟨w, hw⟩ := pure_hurwitz_integral hint hre
  refine ⟨w, ?_, ?_⟩
  · rw [mem_spherePoints]
    have hn := quaternion_conjugate_norm q (pureQuaternion v) hq
    rw [hw, pureQuaternion_norm, pureQuaternion_norm, hv] at hn
    exact_mod_cast hn
  · rw [← hw, div_mul_cancel₀ _ hq]

/-- Right stability of a left ideal produces an integral conjugate of the pure quaternion. -/
theorem stable_hurwitz_ideal_to_sphere {v : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (I : Ideal hurwitzOrder)
    (hI : ∃ q : hurwitzOrder, q ∈ I ∧ q ≠ 0)
    (hstable : ∀ q : hurwitzOrder, q ∈ I →
      q * (⟨pureQuaternion v, pureQuaternion_mem v⟩ : hurwitzOrder) ∈ I) :
    ∃ (q : hurwitzOrder) (w : Triple), q ≠ 0 ∧ I = Ideal.span {q} ∧
      w ∈ spherePoints n ∧ (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q := by
  obtain ⟨q, hq⟩ := hurwitz_left_ideal_principal I
  have hqI : q ∈ I := by rw [hq]; exact Ideal.mem_span_singleton_self q
  have hq0 : q ≠ 0 := by
    intro heq
    obtain ⟨r, hrI, hr0⟩ := hI
    rw [hq] at hrI
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hrI
    exact hr0 (by simpa only [heq, mul_zero] using ha.symm)
  have hq0' : (q : ℍ[ℚ]) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have hmem := hstable q hqI
  rw [hq] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hr' : (r : ℍ[ℚ]) * (q : ℍ[ℚ]) = (q : ℍ[ℚ]) * pureQuaternion v :=
    congrArg Subtype.val hr
  have hconj : (q : ℍ[ℚ]) * pureQuaternion v / (q : ℍ[ℚ]) = (r : ℍ[ℚ]) := by
    rw [← hr', mul_div_cancel_right₀ _ hq0']
  have hre : (r : ℍ[ℚ]).re = 0 := by
    rw [← hconj, quaternion_conjugate_re _ _ hq0']
    rfl
  obtain ⟨w, hw⟩ := pure_hurwitz_integral r.property hre
  refine ⟨q, w, hq0, hq, ?_, ?_⟩
  · rw [mem_spherePoints]
    have hn := quaternion_conjugate_norm (q : ℍ[ℚ]) (pureQuaternion v) hq0'
    rw [hconj, hw, pureQuaternion_norm, pureQuaternion_norm, hv] at hn
    exact_mod_cast hn
  · rw [← hw]
    exact hr'.symm

theorem quaternion_intertwiner_commutes {q r v w : ℍ[ℚ]} (hq : q ≠ 0)
    (hqv : q * v = w * q) (hrv : r * v = w * r) :
    (q⁻¹ * r) * v = v * (q⁻¹ * r) := by
  apply mul_left_cancel₀ hq
  calc
    q * (q⁻¹ * r * v) = r * v := by
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
    _ = w * r := hrv
    _ = (w * q) * (q⁻¹ * r) := by
      rw [mul_assoc w, ← mul_assoc q, mul_inv_cancel₀ hq, one_mul]
    _ = q * (v * (q⁻¹ * r)) := by rw [← hqv, mul_assoc]

end Erdos941
