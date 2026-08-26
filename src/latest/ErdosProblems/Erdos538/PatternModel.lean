import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicity-weighted deletion model

A pattern is a multiset of cost-bin labels.  Deleting one occurrence of every
part models deleting one of the distinct primes in that bin.  Consequently the
filter below counts equal labels with their full multiplicity.
-/

namespace Erdos538

open scoped Classical

/-- Number of one-part deletions of `μ` whose remaining pattern is selected.
Equal parts are counted separately. -/
noncomputable def patternDeletionCount {α : Type*} [DecidableEq α]
    (F : Multiset α → Prop) (μ : Multiset α) : ℕ := by
  classical
  exact (μ.filter fun c => F (μ.erase c)).card

/-- The multiplicity-weighted deletion-shadow cap. -/
def PatternCap {α : Type*} [DecidableEq α]
    (r : ℕ) (F : Multiset α → Prop) : Prop :=
  ∀ μ, patternDeletionCount F μ ≤ r

/-- A selected pattern cannot already contain `r` copies of any one cost:
adding one more copy would produce at least `r+1` selected deletion facets. -/
theorem selected_pattern_count_lt_cap {α : Type*} [DecidableEq α]
    {r : ℕ} {F : Multiset α → Prop}
    (hcap : PatternCap r F) {s : Multiset α} (hs : F s) (c : α) :
    s.count c < r := by
  classical
  let μ : Multiset α := c ::ₘ s
  let P : α → Prop := fun d => F (μ.erase d)
  have hPc : P c := by
    simp [P, μ, hs]
  have hcountFilter : (μ.filter P).count c = μ.count c := by
    simp [hPc]
  have hcountLe : μ.count c ≤ (μ.filter P).card := by
    rw [← hcountFilter]
    exact Multiset.count_le_card c (μ.filter P)
  have htotal : (μ.filter P).card ≤ r := by
    simpa [patternDeletionCount, P] using hcap μ
  have hc : μ.count c = s.count c + 1 := by simp [μ]
  omega

/-- At cap one, the empty multiset is the only pattern that can be selected. -/
theorem pattern_cap_one_selected_eq_zero {α : Type*} [DecidableEq α]
    {F : Multiset α → Prop} (hcap : PatternCap 1 F)
    {s : Multiset α} (hs : F s) : s = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons c t _ =>
      have h := selected_pattern_count_lt_cap hcap hs c
      simp at h

/-- At cap two, every selected cost pattern has distinct parts. -/
theorem pattern_cap_two_selected_nodup {α : Type*} [DecidableEq α]
    {F : Multiset α → Prop} (hcap : PatternCap 2 F)
    {s : Multiset α} (hs : F s) : s.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro c
  have h := selected_pattern_count_lt_cap hcap hs c
  omega

end Erdos538
