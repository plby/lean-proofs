import ErdosProblems.Erdos587.HooleyDyadicModel
import ErdosProblems.Erdos587.NaturalSubsetBridge

/-! # Full-width subset-sum extraction in arbitrary integer intervals -/

open Filter

namespace Erdos587.CFP

lemma delta_tendsto_dyadic_interval_scale (b : ℕ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => Nat.log (2 ^ (1000 * b)) N + 1) atTop atTop := by
  have hbase : 1 < 2 ^ (1000 * b) := Nat.one_lt_pow (by omega) (by omega)
  apply tendsto_atTop.mpr
  intro T
  filter_upwards [eventually_ge_atTop ((2 ^ (1000 * b)) ^ T)] with N hN
  have hh := Nat.le_log_of_pow_le hbase hN
  omega

lemma delta_dyadic_interval_scale_bounds (b N : ℕ) (hb : 0 < b) (hN : 0 < N)
    (ht : 2 ≤ Nat.log (2 ^ (1000 * b)) N + 1) :
    let t := Nat.log (2 ^ (1000 * b)) N + 1
    N ≤ 2 ^ (1000 * b * t) ∧ 2 ^ (60 * b * t) ≤ N := by
  let l := Nat.log (2 ^ (1000 * b)) N
  have hbase : 1 < 2 ^ (1000 * b) := Nat.one_lt_pow (by omega) (by omega)
  have hl : 1 ≤ l := by omega
  constructor
  · have hh := (Nat.lt_pow_succ_log_self hbase N).le
    simpa only [← pow_mul] using hh
  · have hexp : 60 * b * (l + 1) ≤ (1000 * b) * l := by
      have hsmall : 60 * (l + 1) ≤ 1000 * l := by omega
      have hh := Nat.mul_le_mul_right b hsmall
      nlinarith only [hh]
    have hh := Nat.pow_log_le_self (2 ^ (1000 * b)) hN.ne'
    rw [← pow_mul] at hh
    exact (Nat.pow_le_pow_right (by omega) hexp).trans hh

theorem exists_delta_interval_full_width :
    ∃ R d₀ F C : ℕ, 0 < R ∧ 0 < d₀ ∧ 0 < F ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → N ≤ A.card ^ 3 →
        ∃ m : ℕ, 0 < m ∧ A.card ≤ R * m ∧ m ≤ A.card ∧
          ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ d₀ ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
            Q.carrier ⊆ natToIntFinset A.subsetSum ∧
            (∀ i, m ≤ F * Q.length i) ∧ m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
            (Q.upperEndpoint : ℝ) ≤ (C : ℝ) * Q.coefficientSpan := by
  obtain ⟨b, R, d₀, F, C, hb, hR, hd₀, hF, hC, hextract⟩ := exists_delta_dyadic_full_width
  refine ⟨R, d₀, F, C, hR, hd₀, hF, hC, ?_⟩
  have htendsto := delta_tendsto_dyadic_interval_scale b hb
  filter_upwards [eventually_ge_atTop 1, htendsto.eventually (eventually_ge_atTop 2),
    htendsto.eventually hextract] with N hN ht hmodel
  intro A hA hcubic
  let t := Nat.log (2 ^ (1000 * b)) N + 1
  obtain ⟨hupper, hlower⟩ := delta_dyadic_interval_scale_bounds b N hb hN ht
  have hAint : natToIntFinset A ⊆ Finset.Icc 1 ((2 ^ (1000 * b * t) : ℕ) : ℤ) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    have ha' := Finset.mem_Icc.mp (hA ha)
    apply Finset.mem_Icc.mpr
    change 1 ≤ (a : ℤ) ∧ (a : ℤ) ≤ ((2 ^ (1000 * b * t) : ℕ) : ℤ)
    exact ⟨by exact_mod_cast ha'.1, by exact_mod_cast ha'.2.trans hupper⟩
  have hthreshold : 2 ^ (20 * b * t) ≤ (natToIntFinset A).card := by
    rw [card_natToIntFinset]
    apply (Nat.pow_le_pow_iff_left (by omega : (3 : ℕ) ≠ 0)).mp
    have heq : (2 ^ (20 * b * t)) ^ 3 = 2 ^ (60 * b * t) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [heq]
    exact hlower.trans hcubic
  obtain ⟨m, hm, hretain, hmA, Q, hQpos, hQrank, hQproper, hQhom, hQsub,
      hside, hsize, hheight⟩ := hmodel (natToIntFinset A) hAint hthreshold
  rw [card_natToIntFinset] at hretain hmA
  have hQsub' : Q.carrier ⊆ natToIntFinset A.subsetSum := by
    rw [← subsetSum_natToIntFinset]
    exact hQsub
  exact ⟨m, hm, hretain, hmA, Q, hQpos, hQrank, hQproper, hQhom, hQsub', hside, hsize, hheight⟩

end Erdos587.CFP
