import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# A finite second-moment bound for rare event packets

Pairwise asymptotic independence is enough to make packets with large expected
size unlikely to contain only a bounded number of events.
-/

open Filter Topology
open scoped Classical

namespace Bernays

noncomputable def eventCount {α : Type*} (A : Finset α) (E : α → Prop) : ℕ :=
  (A.filter E).card

theorem sum_event_indicator {α : Type*} (A : Finset α) (E : α → Prop) [DecidablePred E] :
    (∑ x ∈ A, if E x then (1 : ℝ) else 0) = (eventCount A E : ℝ) := by
  rw [Finset.sum_boole, eventCount]
  congr

noncomputable def packetCount {α ι : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) : ℝ :=
  ∑ p ∈ P, if E p x then 1 else 0

theorem packetCount_eq_eventCount {α ι : Type*} (P : Finset ι) (E : ι → α → Prop) (x : α) :
    packetCount P E x = (eventCount P (fun p => E p x) : ℝ) := by
  unfold packetCount
  convert sum_event_indicator P (fun p => E p x) using 1

noncomputable def packetVariance {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) : ℝ :=
  ∑ x ∈ A, (packetCount P E x - ∑ p ∈ P, u p) ^ 2

theorem centered_event_sum {α : Type*} (A : Finset α) (E F : α → Prop) (u v : ℝ) :
    (∑ x ∈ A, ((if E x then 1 else 0) - u) * ((if F x then 1 else 0) - v)) =
      (eventCount A (fun x => E x ∧ F x) : ℝ) - v * eventCount A E -
        u * eventCount A F + u * v * A.card := by
  classical
  have hpoint (x : α) : ((if E x then 1 else 0) - u) * ((if F x then 1 else 0) - v) =
      (if E x ∧ F x then 1 else 0) - v * (if E x then 1 else 0) -
        u * (if F x then 1 else 0) + u * v := by
    by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF] <;> ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_event_indicator, Finset.sum_const, nsmul_eq_mul]
  ring

theorem packetVariance_eq {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) :
    packetVariance A P E u = ∑ p ∈ P, ∑ q ∈ P,
      ((eventCount A (fun x => E p x ∧ E q x) : ℝ) - u q * eventCount A (E p) -
        u p * eventCount A (E q) + u p * u q * A.card) := by
  unfold packetVariance packetCount
  simp_rw [← Finset.sum_sub_distrib, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun q _ => centered_event_sum A (E p) (E q) (u p) (u q))

theorem packetVariance_limit {α ι : Type*} (A : ℕ → Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) (s : ℕ → ℝ) (C : ℝ)
    (hA : Tendsto (fun N => (A N).card / s N) atTop (𝓝 C))
    (h₁ : ∀ p ∈ P, Tendsto (fun N => (eventCount (A N) (E p) : ℝ) / s N)
      atTop (𝓝 (C * u p)))
    (h₂ : ∀ p ∈ P, ∀ q ∈ P,
      Tendsto (fun N => (eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) / s N)
        atTop (𝓝 (C * (if p = q then u p else u p * u q)))) :
    Tendsto (fun N => packetVariance (A N) P E u / s N) atTop
      (𝓝 (C * ∑ p ∈ P, (u p - (u p) ^ 2))) := by
  have hpair (p) (hp : p ∈ P) (q) (hq : q ∈ P) :
      Tendsto (fun N =>
        ((eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) - u q * eventCount (A N) (E p) -
          u p * eventCount (A N) (E q) + u p * u q * (A N).card) / s N) atTop
        (𝓝 (if p = q then C * (u p - (u p) ^ 2) else 0)) := by
    have h := (((h₂ p hp q hq).sub ((h₁ p hp).const_mul (u q))).sub
      ((h₁ q hq).const_mul (u p))).add (hA.const_mul (u p * u q))
    have heq : C * (if p = q then u p else u p * u q) - u q * (C * u p) -
        u p * (C * u q) + u p * u q * C =
        (if p = q then C * (u p - (u p) ^ 2) else 0) := by
      by_cases hpq : p = q
      · subst q; simp only [if_true]; ring
      · simp only [if_neg hpq]; ring
    rw [heq] at h
    convert h using 1 <;> ext N <;> ring
  have h := tendsto_finsetSum P (fun p hp => tendsto_finsetSum P (fun q hq => hpair p hp q hq))
  have heq : (∑ p ∈ P, ∑ q ∈ P, if p = q then C * (u p - (u p) ^ 2) else 0) =
      C * ∑ p ∈ P, (u p - (u p) ^ 2) := by
    simp only [Finset.sum_ite_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [if_pos hp]
  rw [heq] at h
  convert h using 1
  · ext N
    rw [packetVariance_eq, Finset.sum_div]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_div _ _ _)

theorem fewPacketCount_mul_sq_le_variance {α ι : Type*} (A : Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) {k : ℝ} (hk : k ≤ ∑ p ∈ P, u p) :
    (eventCount A (fun x => packetCount P E x ≤ k) : ℝ) * ((∑ p ∈ P, u p) - k) ^ 2 ≤
      packetVariance A P E u := by
  have hpoint (x : α) (hx : packetCount P E x ≤ k) :
      ((∑ p ∈ P, u p) - k) ^ 2 ≤ (packetCount P E x - ∑ p ∈ P, u p) ^ 2 := by
    nlinarith
  calc
    _ = ∑ x ∈ A.filter (fun x => packetCount P E x ≤ k), ((∑ p ∈ P, u p) - k) ^ 2 := by
      simp [eventCount]
    _ ≤ ∑ x ∈ A.filter (fun x => packetCount P E x ≤ k),
        (packetCount P E x - ∑ p ∈ P, u p) ^ 2 :=
      Finset.sum_le_sum fun x hx => hpoint x (Finset.mem_filter.mp hx).2
    _ ≤ packetVariance A P E u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

theorem eventually_fewPacketCount_le {α ι : Type*} (A : ℕ → Finset α) (P : Finset ι)
    (E : ι → α → Prop) (u : ι → ℝ) (s : ℕ → ℝ) {C k : ℝ}
    (hC : 0 < C) (hs : ∀ᶠ N in atTop, 0 < s N)
    (hM : 0 < ∑ p ∈ P, u p) (hk : 2 * k ≤ ∑ p ∈ P, u p) (hk₀ : 0 ≤ k)
    (hA : Tendsto (fun N => (A N).card / s N) atTop (𝓝 C))
    (h₁ : ∀ p ∈ P, Tendsto (fun N => (eventCount (A N) (E p) : ℝ) / s N)
      atTop (𝓝 (C * u p)))
    (h₂ : ∀ p ∈ P, ∀ q ∈ P,
      Tendsto (fun N => (eventCount (A N) (fun x => E p x ∧ E q x) : ℝ) / s N)
        atTop (𝓝 (C * (if p = q then u p else u p * u q)))) :
    ∀ᶠ N in atTop, (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) ≤
      (8 * C / (∑ p ∈ P, u p)) * s N := by
  let M := ∑ p ∈ P, u p
  have hlim := packetVariance_limit A P E u s C hA h₁ h₂
  have hlimle : C * ∑ p ∈ P, (u p - (u p) ^ 2) ≤ C * M := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Finset.sum_le_sum fun p _ => sub_le_self _ (sq_nonneg _)
  have hlt : C * ∑ p ∈ P, (u p - (u p) ^ 2) < 2 * C * M := by nlinarith
  filter_upwards [hs, hlim.eventually (gt_mem_nhds hlt)] with N hsN hV
  have hV' : packetVariance (A N) P E u ≤ 2 * C * M * s N :=
    ((div_lt_iff₀ hsN).mp hV).le
  have hrare := fewPacketCount_mul_sq_le_variance (A N) P E u (by linarith : k ≤ M)
  have hgap : M ^ 2 / 4 ≤ (M - k) ^ 2 := by nlinarith
  have hrare₀ : 0 ≤ (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) := Nat.cast_nonneg _
  have hbound := (mul_le_mul_of_nonneg_left hgap hrare₀).trans (hrare.trans hV')
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hM).mpr
  change _ * M ≤ 8 * C * s N
  have hcancel : (eventCount (A N) (fun x => packetCount P E x ≤ k) : ℝ) * M * M ≤
      (8 * C * s N) * M := by nlinarith [hbound]
  exact le_of_mul_le_mul_right hcancel hM

end Bernays
