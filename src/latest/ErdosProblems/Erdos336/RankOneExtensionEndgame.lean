import Mathlib
import ErdosProblems.Erdos336.IntervalAggregateBound
import ErdosProblems.Erdos336.RankOneEndgame

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Automatic rank-one endgame from an outer interval
-/

namespace Erdos336

/-- Cost adapted to the determinant-extension interval bound. -/
def extensionRankOneCost (H : ℕ) : ℕ := ((H + 3) ^ 2 + 2) / 3

lemma extensionRankOneCost_ceiling (H : ℕ) :
    (H + 3) ^ 2 ≤ 3 * extensionRankOneCost H := by
  dsimp [extensionRankOneCost]
  omega

/-- The extension version still has leading coefficient exactly `1/3`. -/
theorem extensionRankOneCost_bound (H : ℕ) :
    3 * extensionRankOneCost H ≤ H ^ 2 + 6 * H + 11 := by
  have hd := Nat.mul_div_le ((H + 3) ^ 2 + 2) 3
  dsimp [extensionRankOneCost]
  nlinarith

/-- Endpoint smoothing with the slightly larger boundary error supplied by the
lattice extension. -/
theorem full_coverage_of_rankOne_core_and_extension_bound
    {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 0 < m)
    (π : G →+ ZMod m) {A : Set G} {β : ZMod m}
    {p q : G} {M L t H : ℕ}
    (hp : p ∈ A) (hq : q ∈ A)
    (hstep : π q = π p + (L : ZMod m))
    (hcore : ∀ s : ℕ, s ≤ M → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly A t y)
    (hLM : L ≤ M) (hLpos : 0 < L)
    (hinterval : 3 * m ≤ L * (H + 1) ^ 2 + 4 * (H + 1) + 4) :
    ∀ y : G,
      GroupRepExactly A (t + extensionRankOneCost H) y := by
  have hceil := extensionRankOneCost_ceiling H
  have herr :
      L * (H + 1) ^ 2 + 4 * (H + 1) + 4 ≤ L * (H + 3) ^ 2 := by
    nlinarith
  have hscaled : 3 * m ≤ 3 * (extensionRankOneCost H * L) := by
    calc
      3 * m ≤ L * (H + 1) ^ 2 + 4 * (H + 1) + 4 := hinterval
      _ ≤ L * (H + 3) ^ 2 := herr
      _ ≤ L * (3 * extensionRankOneCost H) :=
        Nat.mul_le_mul_left L hceil
      _ = 3 * (extensionRankOneCost H * L) := by ring
  have hmKL : m ≤ extensionRankOneCost H * L := by omega
  have hwidth : m - 1 ≤ extensionRankOneCost H * L + M := by omega
  exact cyclic_full_fiber_endpoint_smoothing hm π hp hq hstep hcore
    hwidth hLM

/-- Projecting a list whose terms lie in an interval gives aggregate
coordinates `j≤H`, `k≤Lj`. -/
lemma exists_projected_interval_count
    {G : Type*} [AddCommGroup G]
    {m : ℕ} (π : G →+ ZMod m) (A : Set G)
    (α : ZMod m) (L : ℕ)
    (houter : ∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m))
    (xs : List G) (hxs : ∀ x ∈ xs, x ∈ A) :
    ∃ K : ℕ, K ≤ L * xs.length ∧
      π xs.sum = xs.length • α + (K : ZMod m) := by
  induction xs with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons x xs ih =>
      have hxA := hxs x (by simp)
      obtain ⟨k, hk, hx⟩ := houter x hxA
      have htail : ∀ z ∈ xs, z ∈ A := by
        intro z hz
        exact hxs z (by simp [hz])
      obtain ⟨K, hK, hsum⟩ := ih htail
      refine ⟨k + K, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simp only [List.sum_cons, map_add, hx, hsum, List.length_cons,
          Nat.cast_add, add_nsmul, one_nsmul]
        push_cast
        ring

/-- Weak coverage by a set whose projection lies in a length-`L` cyclic
interval implies the aggregate interval-cover hypothesis. -/
theorem intervalAggregateCover_of_outer_interval
    {G : Type*} [AddCommGroup G]
    {m : ℕ} (π : G →+ ZMod m) (hπ : Function.Surjective π)
    {A : Set G} (α : ZMod m) {L H : ℕ}
    (houter : ∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m))
    (hweak : ∀ y : G, GroupRepAtMost A H y) :
    IntervalAggregateCover (intPairLabelHom α 1) L H := by
  intro z
  obtain ⟨y, hy⟩ := hπ z
  obtain ⟨j, hj, xs, hlen, hxmem, hxsum⟩ := hweak y
  obtain ⟨K, hK, hproj⟩ :=
    exists_projected_interval_count π A α L houter xs hxmem
  refine ⟨j, K, hj, ?_, ?_⟩
  · simpa [hlen] using hK
  · dsimp [intPairLabelHom]
    rw [← hy, ← hxsum, hproj, hlen]
    norm_cast
    simp

/-- Complete rank-one endgame: an outer interval plus a full-fibre inner core
imply full exact coverage at cost `t + (1/3+o(1))H²`. -/
theorem full_coverage_of_outer_interval_and_core
    {G : Type*} [AddCommGroup G] {m : ℕ} (hm : 0 < m)
    (π : G →+ ZMod m) (hπ : Function.Surjective π)
    {A : Set G} {α β : ZMod m}
    {p q : G} {M L t H : ℕ}
    (hweak : ∀ y : G, GroupRepAtMost A H y)
    (houter : ∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m))
    (hp : p ∈ A) (hq : q ∈ A)
    (hstep : π q = π p + (L : ZMod m))
    (hcore : ∀ s : ℕ, s ≤ M → ∀ y : G,
      π y = β + (s : ZMod m) → GroupRepExactly A t y)
    (hLM : L ≤ M) (hLpos : 0 < L) :
    ∀ y : G,
      GroupRepExactly A (t + extensionRankOneCost H) y := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hagg := intervalAggregateCover_of_outer_interval π hπ α houter hweak
  have hcard := intervalAggregate_card_bound
    (intPairLabelHom α 1) hLpos hagg
  have hinterval :
      3 * m ≤ L * (H + 1) ^ 2 + 4 * (H + 1) + 4 := by
    have hmul :
        L * (3 * m) ≤ L * (L * (H + 1) ^ 2 + 4 * (H + 1) + 4) := by
      calc
        L * (3 * m) = 3 * (L * m) := by ring
        _ ≤ (L * (H + 1) + 2) ^ 2 := by
          simpa [Nat.card_zmod, mul_comm, mul_left_comm, mul_assoc] using hcard
        _ ≤ L * (L * (H + 1) ^ 2 + 4 * (H + 1) + 4) := by
          nlinarith
    exact Nat.le_of_mul_le_mul_left hmul hLpos
  exact full_coverage_of_rankOne_core_and_extension_bound hm π hp hq hstep
    hcore hLM hLpos hinterval

end Erdos336
