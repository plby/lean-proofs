import ErdosProblems.Erdos336.Basic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An elementary bounded-hole sumset lemma

A finite/infinite set of naturals that contains both endpoints `0,L` and a
whole interval `[a,a+M]` has long intervals in each sufficiently high exact
sumset.  This is the elementary fibre-filling step in the finite cyclic route
to Erdős Problem 336.
-/

namespace Erdos336

/-- Every `r ≤ q*M` is a sum of exactly `q` numbers, each at most `M`. -/
lemma exists_list_sum_eq_of_le_mul {q M r : ℕ} (hr : r ≤ q * M) :
    ∃ xs : List ℕ, xs.length = q ∧ (∀ x ∈ xs, x ≤ M) ∧ xs.sum = r := by
  induction q generalizing r with
  | zero =>
      have : r = 0 := by simpa using hr
      subst r
      exact ⟨[], rfl, by simp, rfl⟩
  | succ q ih =>
      by_cases h : r ≤ M
      · refine ⟨r :: List.replicate q 0, ?_, ?_, ?_⟩
        · simp
        · intro x hx
          simp only [List.mem_cons, List.mem_replicate] at hx
          rcases hx with rfl | ⟨_, rfl⟩
          · exact h
          · exact Nat.zero_le M
        · simp
      · have hMr : M ≤ r := Nat.le_of_lt (Nat.lt_of_not_ge h)
        have hrem : r - M ≤ q * M := by
          rw [Nat.sub_le_iff_le_add]
          simpa [Nat.succ_mul, add_comm] using hr
        obtain ⟨xs, hlen, hbound, hsum⟩ := ih hrem
        refine ⟨M :: xs, by simp [hlen], ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_rfl
          · exact hbound x hx
        · simp only [List.sum_cons, hsum]
          omega

lemma sum_map_nat_add_left (a : ℕ) (xs : List ℕ) :
    (xs.map (fun z => a + z)).sum = xs.length * a + xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      rw [Nat.succ_mul]
      omega

/-- If `A` contains `0`, `L`, and every integer from `a` through `a+M`, then
using `q` interval terms and all remaining terms as endpoints realizes a long
interval inside every exact `t`-fold sumset. -/
theorem interval_smoothing
    {A : Set ℕ} {a M L q t p r : ℕ}
    (hzero : 0 ∈ A) (hL : L ∈ A)
    (hcore : ∀ z : ℕ, a ≤ z → z ≤ a + M → z ∈ A)
    (hqM : L ≤ q * M) (hqt : q ≤ t)
    (hp : p ≤ t - q) (hr : r ≤ q * M) :
    RepresentsExactly A t (q * a + p * L + r) := by
  obtain ⟨rs, hrslen, hrsbound, hrssum⟩ := exists_list_sum_eq_of_le_mul hr
  let core : List ℕ := rs.map (fun z => a + z)
  let highs : List ℕ := List.replicate p L
  let zeros : List ℕ := List.replicate (t - q - p) 0
  refine ⟨core ++ highs ++ zeros, ?_, ?_, ?_⟩
  · dsimp [core, highs, zeros]
    simp [hrslen]
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hxch | hxz
    · rcases List.mem_append.mp hxch with hxc | hxh
      · dsimp [core] at hxc
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hxc
        apply hcore
        · omega
        · have := hrsbound z hz
          omega
      · dsimp [highs] at hxh
        have : x = L := (List.mem_replicate.mp hxh).2
        simpa [this] using hL
    · dsimp [zeros] at hxz
      have : x = 0 := (List.mem_replicate.mp hxz).2
      simpa [this] using hzero
  · dsimp [core, highs, zeros]
    simp only [List.sum_append]
    rw [sum_map_nat_add_left, hrslen, hrssum]
    simp [nsmul_eq_mul]
    omega

/-- The overlap condition used in `interval_smoothing`: choosing
`q = ceil(L/M)` (encoded by the two inequalities below) makes adjacent
endpoint-indexed intervals overlap. -/
lemma smoothing_overlap {L M q p : ℕ} (hq : L ≤ q * M) :
    p * L + q * M + 1 ≥ (p + 1) * L := by
  nlinarith

end Erdos336
