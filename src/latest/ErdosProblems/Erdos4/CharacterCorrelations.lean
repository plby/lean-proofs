import ErdosProblems.Erdos4.PeriodicCancellation
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Elementary correlations of distinct primitive characters

Characters are compared at their common multiple level. Equality of lifted
primitive characters forces equality of the original conductors, preventing
imprimitive duplicates in the later mean-square family.
-/

open scoped BigOperators

namespace Erdos4.CharacterCorrelations

theorem inv_apply_eq_star {d : ℕ} (chi : DirichletCharacter ℂ d) (a : ZMod d) :
    chi⁻¹ a = star (chi a) := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have hn : ‖chi a‖ = 1 := by simpa only [IsUnit.unit_spec] using chi.unit_norm_eq_one ha.unit
    simpa only [starRingEnd_apply] using Complex.inv_eq_conj hn
  · rw [chi.map_nonunit ha]
    simp

theorem distinct_correlation_le {d : ℕ} [NeZero d]
    (chi psi : DirichletCharacter ℂ d) (hne : chi ≠ psi) (a N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      star (chi ((a + n : ℕ) : ZMod d)) * psi ((a + n : ℕ) : ZMod d)‖ ≤ d := by
  have hnonprincipal : chi⁻¹ * psi ≠ 1 := by
    intro heq
    exact hne (inv_mul_eq_one.mp heq)
  simpa only [MulChar.mul_apply, inv_apply_eq_star] using
    PeriodicCancellation.character_norm_sum_interval_le (chi⁻¹ * psi) hnonprincipal a N

theorem primitive_lifts_ne_of_level_ne {d e L : ℕ} [NeZero L]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive)
    (hd : d ∣ L) (he : e ∣ L) (hne : d ≠ e) :
    DirichletCharacter.changeLevel hd chi ≠ DirichletCharacter.changeLevel he psi := by
  intro heq
  have hc := congrArg DirichletCharacter.conductor heq
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hc
  exact hne (hchi.symm.trans (hc.trans hpsi))

theorem primitive_lift_correlation_le {d e L : ℕ} [NeZero L]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive)
    (hd : d ∣ L) (he : e ∣ L) (hne : d ≠ e) (a N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      star ((DirichletCharacter.changeLevel hd chi) ((a + n : ℕ) : ZMod L)) *
        (DirichletCharacter.changeLevel he psi) ((a + n : ℕ) : ZMod L)‖ ≤ L :=
  distinct_correlation_le _ _ (primitive_lifts_ne_of_level_ne chi psi hchi hpsi hd he hne) a N

theorem changeLevel_natCast_of_coprime {d L : ℕ}
    (chi : DirichletCharacter ℂ d) (hd : d ∣ L) {n : ℕ} (hn : n.Coprime L) :
    DirichletCharacter.changeLevel hd chi (n : ZMod L) = chi (n : ZMod d) := by
  simpa only [Int.cast_natCast] using
    DirichletCharacter.changeLevel_eq_cast_of_dvd' chi hd
      (Nat.isCoprime_iff_coprime.mpr hn)

/-- Passing to the lcm does not change the product, even on nonunits: one
of the original character values then vanishes. -/
theorem correlation_eq_lcm_lifts {d e : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (n : ℕ) :
    star (chi (n : ZMod d)) * psi (n : ZMod e) =
      star ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left d e) chi)
        (n : ZMod (Nat.lcm d e))) *
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right d e) psi)
        (n : ZMod (Nat.lcm d e)) := by
  by_cases hn : n.Coprime (Nat.lcm d e)
  · rw [changeLevel_natCast_of_coprime chi _ hn, changeLevel_natCast_of_coprime psi _ hn]
  · have hunit : ¬ IsUnit (n : ZMod (Nat.lcm d e)) :=
      fun hh => hn ((ZMod.isUnit_iff_coprime n _).mp hh)
    have hzero := (DirichletCharacter.changeLevel (Nat.dvd_lcm_left d e) chi).map_nonunit hunit
    rw [hzero, star_zero, zero_mul]
    by_cases hnd : n.Coprime d
    · have hne : ¬ n.Coprime e := by
        intro hne
        exact hn (Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul d e) (hnd.mul_right hne))
      have hz := psi.map_nonunit (fun hu => hne ((ZMod.isUnit_iff_coprime n e).mp hu))
      rw [hz, mul_zero]
    · have hz := chi.map_nonunit (fun hu => hnd ((ZMod.isUnit_iff_coprime n d).mp hu))
      rw [hz, star_zero, zero_mul]

/-- The raw correlation of primitive characters of different conductors is
bounded by the lcm of their conductors. -/
theorem primitive_correlation_le {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive) (hne : d ≠ e) (a N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      star (chi ((a + n : ℕ) : ZMod d)) * psi ((a + n : ℕ) : ZMod e)‖ ≤ Nat.lcm d e := by
  let : NeZero (Nat.lcm d e) := ⟨Nat.lcm_ne_zero (NeZero.ne d) (NeZero.ne e)⟩
  simp_rw [correlation_eq_lcm_lifts chi psi]
  exact primitive_lift_correlation_le chi psi hchi hpsi
    (Nat.dvd_lcm_left d e) (Nat.dvd_lcm_right d e) hne a N

theorem correlation_multiples_eq {d e : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (r a N : ℕ) :
    (∑ n ∈ Finset.range N,
      star (chi ((r * (a + n) : ℕ) : ZMod d)) * psi ((r * (a + n) : ℕ) : ZMod e)) =
      (star (chi (r : ZMod d)) * psi (r : ZMod e)) *
        ∑ n ∈ Finset.range N,
          star (chi ((a + n : ℕ) : ZMod d)) * psi ((a + n : ℕ) : ZMod e) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [Nat.cast_mul, map_mul, star_mul]
  ring

/-- The multiplier need not be coprime to the conductors: if it is not,
its prefactor simply vanishes. -/
theorem correlation_multiples_le {d e : ℕ}
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e) (r a N : ℕ)
    (L : ℝ)
    (hbound : ‖∑ n ∈ Finset.range N,
      star (chi ((a + n : ℕ) : ZMod d)) * psi ((a + n : ℕ) : ZMod e)‖ ≤ L) :
    ‖∑ n ∈ Finset.range N,
      star (chi ((r * (a + n) : ℕ) : ZMod d)) * psi ((r * (a + n) : ℕ) : ZMod e)‖ ≤ L := by
  have hc : ‖star (chi (r : ZMod d)) * psi (r : ZMod e)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_mul (chi.norm_le_one _) (psi.norm_le_one _)
      (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  rw [correlation_multiples_eq, norm_mul]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa only [one_mul] using hbound)

theorem primitive_correlation_multiples_le {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive) (hne : d ≠ e) (r a N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      star (chi ((r * (a + n) : ℕ) : ZMod d)) * psi ((r * (a + n) : ℕ) : ZMod e)‖ ≤
        Nat.lcm d e :=
  correlation_multiples_le chi psi r a N _ (primitive_correlation_le chi psi hchi hpsi hne a N)

end Erdos4.CharacterCorrelations
