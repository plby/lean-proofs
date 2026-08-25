import Util.Bernays.LocalDilation
import Util.Bernays.FiniteVariance

/-!
# Pairwise independent prime divisibility in the local norm set
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

noncomputable def localValues (S : ℕ → Prop) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (ParityAdmissible S)

theorem localValues_card (S : ℕ → Prop) (N : ℕ) : (localValues S N).card = localCount S N := rfl

theorem eventCount_localValues_dvd (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) (N : ℕ) :
    eventCount (localValues S N) (fun n => m ∣ n) = localCount S (N / m) := by
  unfold eventCount localValues
  convert localCount_divisible S hm hS N using 1
  congr

theorem unobstructed_prime (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) (hSp : ¬S p) :
    ∀ q : ℕ, q.Prime → S q → ¬q ∣ p := by
  intro q hq hSq hdvd
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
  exact hSp (heq ▸ hSq)

theorem localValues_card_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ((localValues (fun p : ℕ => χ p = -1) N).card : ℝ) / scale N)
      atTop (𝓝 (characterLocalConstant χ / sqrt π)) := by
  simpa only [Nat.div_one, Nat.cast_one, div_one, localValues_card] using
    localCount_dilation_limit χ hχ₂ hχ (m := 1) (by decide)

theorem local_prime_divisor_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {p : ℕ} (hp : p.Prime) (hχp : χ p ≠ -1) :
    Tendsto (fun N : ℕ =>
      (eventCount (localValues (fun r : ℕ => χ r = -1) N) (fun n => p ∣ n) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) * (p : ℝ)⁻¹)) := by
  simp_rw [eventCount_localValues_dvd _ hp.pos
    (unobstructed_prime (fun r : ℕ => χ r = -1) hp hχp)]
  simpa only [div_eq_mul_inv] using localCount_dilation_limit χ hχ₂ hχ hp.pos

theorem local_prime_pair_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hχp : χ p ≠ -1) (hχr : χ r ≠ -1) :
    Tendsto (fun N : ℕ =>
      (eventCount (localValues (fun l : ℕ => χ l = -1) N) (fun n => p ∣ n ∧ r ∣ n) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) *
        (if p = r then (p : ℝ)⁻¹ else (p : ℝ)⁻¹ * (r : ℝ)⁻¹))) := by
  by_cases hpr : p = r
  · subst r
    simpa only [and_self, if_true] using local_prime_divisor_limit χ hχ₂ hχ hp hχp
  · have hcop : p.Coprime r := hp.coprime_iff_not_dvd.mpr fun h =>
      hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h)
    have heq : (fun n : ℕ => p ∣ n ∧ r ∣ n) = (fun n : ℕ => p * r ∣ n) := by
      funext n
      exact propext ⟨fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2,
        fun h => ⟨(dvd_mul_right p r).trans h, (dvd_mul_left r p).trans h⟩⟩
    rw [heq, if_neg hpr]
    have hS : ∀ l : ℕ, l.Prime → χ l = -1 → ¬l ∣ p * r := by
      intro l hl hχl hdiv
      rcases hl.dvd_mul.mp hdiv with h | h
      · exact unobstructed_prime (fun r : ℕ => χ r = -1) hp hχp l hl hχl h
      · exact unobstructed_prime (fun r : ℕ => χ r = -1) hr hχr l hl hχl h
    simp_rw [eventCount_localValues_dvd _ (Nat.mul_pos hp.pos hr.pos) hS]
    simpa only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, mul_comm] using
      localCount_dilation_limit χ hχ₂ hχ (Nat.mul_pos hp.pos hr.pos)

theorem eventually_local_fewPacketCount_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ χ p ≠ -1)
    {k : ℝ} (hk₀ : 0 ≤ k) (hM : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (hk : 2 * k ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    ∀ᶠ N in atTop,
      (eventCount (localValues (fun p : ℕ => χ p = -1) N)
        (fun n => packetCount P (fun p n => p ∣ n) n ≤ k) : ℝ) ≤
      (8 * (characterLocalConstant χ / sqrt π) / (∑ p ∈ P, (p : ℝ)⁻¹)) * scale N := by
  apply eventually_fewPacketCount_le _ P (fun p n => p ∣ n) (fun p => (p : ℝ)⁻¹)
    (fun N => scale N) (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos))
    ?_ hM hk hk₀ (localValues_card_limit χ hχ₂ hχ)
    (fun p hp => local_prime_divisor_limit χ hχ₂ hχ (hP p hp).1 (hP p hp).2)
    (fun p hp r hr => by
      have h := local_prime_pair_limit χ hχ₂ hχ
        (hP p hp).1 (hP r hr).1 (hP p hp).2 (hP r hr).2
      by_cases hpr : p = r
      · simpa only [if_pos hpr] using h
      · simpa only [if_neg hpr] using h)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact scale_pos (by exact_mod_cast (show 1 < N by omega))

end Bernays
