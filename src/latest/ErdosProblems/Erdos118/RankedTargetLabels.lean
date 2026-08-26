import ErdosProblems.Erdos118.RankedLeafLabels

/-! The actual target parameter may be zero. Preserve the prescribed
source rank; only the positive target needs a second selected index. -/

namespace Erdos118.RankedTargetLabels

open LabelledExtensions LabelledFrames DecisionStates

structure Labels (H : Set ℕ) (b k l s : ℕ) where
  lower : List ℕ
  upper : List ℕ
  lowerCard : lower.length = k + 1
  upperCard : upper.length = l + 1
  lowerIncreasing : lower.Pairwise (· < ·)
  upperIncreasing : upper.Pairwise (· < ·)
  selected : upper.headD 0 ∈ lower
  rank : LabelRanks.rank lower (upper.headD 0) = s
  lastCase : s = k + 1 → lower.getLastD 0 = upper.headD 0
  nonlastCase : s < k + 1 → upper.headD 0 < lower.getLastD 0 ∧
    (0 < l → lower.getLastD 0 ∈ upper) ∧
      ∀ x ∈ upper, upper.headD 0 < x → lower.getLastD 0 ≤ x
  singleton : l = 0 → upper = [upper.headD 0]
  lowerFresh : ∀ x ∈ lower, x ∈ H ∧ b < x
  upperFresh : ∀ x ∈ upper, x ∈ H ∧ b < x

private def ofPositive {H : Set ℕ} {b k l s : ℕ} (L : RankedLeafLabels.Labels H b k l s)
    (hl : 0 < l) : Labels H b k l s where
  lower := L.lower
  upper := L.upper
  lowerCard := L.lowerCard
  upperCard := L.upperCard
  lowerIncreasing := L.lowerIncreasing
  upperIncreasing := L.upperIncreasing
  selected := L.selected
  rank := L.rank
  lastCase := L.lastCase
  nonlastCase := fun hs ↦ ⟨(L.nonlastCase hs).1, fun _ ↦ (L.nonlastCase hs).2.1,
    (L.nonlastCase hs).2.2⟩
  singleton := by omega
  lowerFresh := L.lowerFresh
  upperFresh := L.upperFresh

private def ofSingleton {H : Set ℕ} {b k s : ℕ} (L : RankedLeafLabels.Labels H b k 1 s) :
    Labels H b k 0 s where
  lower := L.lower
  upper := [L.upper.headD 0]
  lowerCard := L.lowerCard
  upperCard := rfl
  lowerIncreasing := L.lowerIncreasing
  upperIncreasing := by simp
  selected := L.selected
  rank := L.rank
  lastCase := L.lastCase
  nonlastCase := by
    intro hs
    refine ⟨(L.nonlastCase hs).1, by omega, ?_⟩
    intro x hx hlt
    have he := List.mem_singleton.mp hx
    exact (not_lt_of_ge he.le hlt).elim
  singleton := fun _ ↦ rfl
  lowerFresh := L.lowerFresh
  upperFresh := by
    intro x hx
    rw [List.mem_singleton.mp hx]
    apply L.upperFresh
    apply first_mem
    intro he
    have hc := L.upperCard
    simp [he] at hc

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l s : ℕ)
    (hs : 0 < s) (hsk : s ≤ k + 1) : Nonempty (Labels H b k l s) := by
  by_cases hl : l = 0
  · subst l
    obtain ⟨L⟩ := RankedLeafLabels.labels hH b k 1 s hs hsk (by omega)
    exact ⟨ofSingleton L⟩
  · obtain ⟨L⟩ := RankedLeafLabels.labels hH b k l s hs hsk (Nat.pos_of_ne_zero hl)
    exact ⟨ofPositive L (Nat.pos_of_ne_zero hl)⟩

theorem body_setup (S : Stem) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b k l s : ℕ) (hs : 0 < s) (hsk : s ≤ k + 1) :
    ∃ A : BodyResponses.Setup S k, ∃ L : Labels H b k l s,
      A.position.label = L.lower ∧ (∀ x ∈ L.upper, x < A.position.size) ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) := by
  by_cases hl : l = 0
  · subst l
    obtain ⟨A, L, hA, hbelow, hf⟩ :=
      RankedLeafLabels.body_setup S hroom hH b k 1 s hs hsk (by omega)
    refine ⟨A, ofSingleton L, hA, ?_, hf⟩
    intro x hx
    change x ∈ [L.upper.headD 0] at hx
    rw [List.mem_singleton.mp hx]
    apply hbelow
    apply first_mem
    intro he
    have hc := L.upperCard
    simp [he] at hc
  · obtain ⟨A, L, hA, hbelow, hf⟩ :=
      RankedLeafLabels.body_setup S hroom hH b k l s hs hsk (Nat.pos_of_ne_zero hl)
    exact ⟨A, ofPositive L (Nat.pos_of_ne_zero hl), hA, hbelow, hf⟩

end Erdos118.RankedTargetLabels
