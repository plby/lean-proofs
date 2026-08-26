import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- The shifted tail sum of a summable real sequence tends to zero. -/
theorem tendsto_tsum_nat_add_zero
    (f : ℕ → ℝ) (hf : Summable f) :
    Tendsto (fun R : ℕ => ∑' n : ℕ, f (n + R)) atTop (𝓝 0) := by
  have hpartial := hf.tendsto_sum_tsum_nat
  have hsub : Tendsto
      (fun R : ℕ => (∑' n, f n) - ∑ n ∈ Finset.range R, f n)
      atTop (𝓝 ((∑' n, f n) - ∑' n, f n)) :=
    tendsto_const_nhds.sub hpartial
  have heq : ∀ R : ℕ,
      (∑' n : ℕ, f (n + R)) =
        (∑' n, f n) - ∑ n ∈ Finset.range R, f n := by
    intro R
    have h := hf.sum_add_tsum_nat_add R
    linarith
  simpa only [heq, sub_self] using hsub

/-- Every finite subset of a sufficiently remote nonnegative summable tail has
small total mass. -/
theorem eventually_finset_tail_sum_le_of_summable
    (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, ∀ T : Finset ℕ,
      (∀ r ∈ T, R ≤ r) → (∑ r ∈ T, f r) ≤ ε := by
  have htend := tendsto_tsum_nat_add_zero f hf
  have hev : ∀ᶠ R : ℕ in atTop, (∑' n : ℕ, f (n + R)) < ε :=
    (tendsto_order.1 htend).2 ε hε
  filter_upwards [hev] with R hR
  intro T hTR
  let U := T.image fun r => r - R
  have hinj : Set.InjOn (fun r => r - R) (T : Set ℕ) := by
    intro r hr s hs hrs
    have hrR := hTR r hr
    have hsR := hTR s hs
    calc
      r = (r - R) + R := (Nat.sub_add_cancel hrR).symm
      _ = (s - R) + R := congrArg (fun n => n + R) hrs
      _ = s := Nat.sub_add_cancel hsR
  have hsum : (∑ n ∈ U, f (n + R)) = ∑ r ∈ T, f r := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.sub_add_cancel (hTR r hr)]
  have hshift : Summable (fun n => f (n + R)) :=
    (summable_nat_add_iff R).2 hf
  have hle : (∑ n ∈ U, f (n + R)) ≤ ∑' n : ℕ, f (n + R) :=
    hshift.sum_le_tsum U (fun n hn => hf0 (n + R))
  rw [hsum] at hle
  exact hle.trans hR.le

end Erdos489
