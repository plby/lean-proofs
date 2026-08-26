import ErdosProblems.Erdos380.PrimeCounts
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

open scoped BigOperators Topology

namespace Erdos380

noncomputable section

def primeReciprocalSum (N : ℕ) : ℝ := ∑ p ∈ N.primesLE, 1 / (p : ℝ)

lemma primesLE_eq_filter_Ioc (N : ℕ) : N.primesLE = (Finset.Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpN, hp⟩
    exact ⟨⟨hp.pos, hpN⟩, hp⟩
  · rintro ⟨⟨_hp0, hpN⟩, hp⟩
    exact ⟨hpN, hp⟩

theorem exists_primeReciprocalSum_error_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    |primeReciprocalSum N - Real.log (Real.log N)| ≤ C := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨max C 0, le_max_right _ _, fun N hN => ?_⟩
  have h := hC (N : ℝ) (by exact_mod_cast hN)
  simp only [Nat.floor_natCast] at h
  have hh : |primeReciprocalSum N - Real.log (Real.log N)| ≤ C := by
    simpa only [primeReciprocalSum, primesLE_eq_filter_Ioc] using h
  exact hh.trans (le_max_left C 0)

lemma primeBand_eq_sdiff (L H : ℕ) :
    (Finset.Ioc L H).filter Nat.Prime = H.primesLE \ L.primesLE := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpL, hpH⟩, hp⟩
    exact ⟨⟨hpH, hp⟩, fun h => (not_le_of_gt hpL) h.1⟩
  · rintro ⟨⟨hpH, hp⟩, hnot⟩
    have hlo : ¬ p ≤ L := fun h => hnot ⟨h, hp⟩
    exact ⟨⟨Nat.lt_of_not_ge hlo, hpH⟩, hp⟩

lemma primeBand_reciprocal_sum {L H : ℕ} (hLH : L ≤ H) :
    (∑ p ∈ (Finset.Ioc L H).filter Nat.Prime, 1 / (p : ℝ)) =
      primeReciprocalSum H - primeReciprocalSum L := by
  rw [primeBand_eq_sdiff]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff (Nat.primesLE_mono hLH))

lemma prime_reciprocal_totient_le {p : ℕ} (hp : p.Prime) :
    1 / (p.totient : ℝ) ≤ 2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpφ : 0 < (p.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  apply (div_le_div_iff₀ hpφ (by positivity)).mpr
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  linarith

lemma sum_prime_band_totient_le (t : Finset ℕ) {L H : ℕ} (hLH : L ≤ H)
    (ht : ∀ p ∈ t, p.Prime) (hL : ∀ p ∈ t, L < p) (hH : ∀ p ∈ t, p ≤ H) :
    (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ 2 * (primeReciprocalSum H - primeReciprocalSum L) := by
  have hsub : t ⊆ (Finset.Ioc L H).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hL p hp, hH p hp⟩, ht p hp⟩
  calc
    _ ≤ ∑ p ∈ t, 2 / (p : ℝ) := Finset.sum_le_sum fun p hp => prime_reciprocal_totient_le (ht p hp)
    _ ≤ ∑ p ∈ (Finset.Ioc L H).filter Nat.Prime, 2 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      congr 1
      simpa only [one_div] using primeBand_reciprocal_sum hLH

/-- A constant bound for reciprocal totients in a prime band with bounded
ratio of logarithmic endpoints. -/
theorem exists_prime_band_totient_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L H : ℕ) (D : ℝ) (t : Finset ℕ), 2 ≤ L → L ≤ H → 1 ≤ D →
      Real.log (H : ℝ) ≤ D * Real.log L →
      (∀ p ∈ t, p.Prime) → (∀ p ∈ t, L < p) → (∀ p ∈ t, p ≤ H) →
      (∑ p ∈ t, 1 / (p.totient : ℝ)) ≤ 2 * Real.log D + C := by
  obtain ⟨C, hC0, hC⟩ := exists_primeReciprocalSum_error_bound
  refine ⟨4 * C, by positivity, fun L H D t hL hLH hD hlog ht htL htH => ?_⟩
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hDpos : 0 < D := by linarith
  have hlogs := Real.log_le_log hlogH hlog
  rw [Real.log_mul hDpos.ne' hlogL.ne'] at hlogs
  have hlow := (abs_le.mp (hC L hL)).1
  have hhigh := (abs_le.mp (hC H (by omega))).2
  have hsum := sum_prime_band_totient_le t hLH ht htL htH
  linarith

lemma prime_band_reciprocal_totient_le {L p : ℕ} (hL : 0 < L) (hp : p.Prime) (hLp : L < p) :
    1 / (p.totient : ℝ) ≤ 1 / (L : ℝ) := by
  apply one_div_le_one_div_of_le (by exact_mod_cast hL)
  rw [Nat.totient_prime hp]
  exact_mod_cast (by omega : L ≤ p - 1)

end

end Erdos380
