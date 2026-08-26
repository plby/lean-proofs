import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Thick exact powers absorb one exceptional summand

This is the elementary local-to-global step used in the transference plan for
Erdős Problem 336.  If an exact power of a translated basis contains every
finite pattern (equivalently, arbitrarily long intervals suffice on `ℤ`), then
one removable exceptional element can be synchronized at a cost of at most the
old variable order.
-/

namespace Erdos336

/-- Exact-length additive representation in `ℤ`. -/
def ZRepExactly (D : Set ℤ) (k : ℕ) (n : ℤ) : Prop :=
  ∃ xs : List ℤ,
    xs.length = k ∧
    (∀ x ∈ xs, x ∈ D) ∧
    xs.sum = n

/-- Every sufficiently large integer has an exact `k`-term representation. -/
def EventuallyExactlyZ (D : Set ℤ) (k : ℕ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ZRepExactly D k n

/-- The exact `k`-fold sumset of `D` is thick: it contains a translate of
 every finite pattern. -/
def ExactPowerThick (D : Set ℤ) (k : ℕ) : Prop :=
  ∀ F : Finset ℤ, ∃ a : ℤ, ∀ x ∈ F, ZRepExactly D k (a + x)

/-- Eventual exact `h`-term coverage using elements of `D` and one exceptional
 element `c`.  The witness `j` is the number of copies of `c`; the remaining
 `h-j` terms lie in `D`. -/
def EventuallyWithOneExtra (D : Set ℤ) (c : ℤ) (h : ℕ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ j : ℕ, j ≤ h ∧ ZRepExactly D (h - j) (n - (j : ℤ) * c)

/-- If `0 ∈ D`, a thick exact `k`-fold sumset synchronizes all possible
numbers of copies of one exceptional element.  Consequently eventual
`h`-term coverage by `D ∪ {c}` upgrades to eventual exact `(k+h)`-term
coverage by `D` alone. -/
theorem eventuallyExactlyZ_of_thick_of_oneExtra
    {D : Set ℤ} {c : ℤ} {h k : ℕ}
    (hzero : 0 ∈ D)
    (hthick : ExactPowerThick D k)
    (hparent : EventuallyWithOneExtra D c h) :
    EventuallyExactlyZ D (k + h) := by
  let F : Finset ℤ := (Finset.range (h + 1)).image (fun j : ℕ => (j : ℤ) * c)
  obtain ⟨a, ha⟩ := hthick F
  obtain ⟨N, hN⟩ := hparent
  refine ⟨N + a, ?_⟩
  intro n hn
  have hbase : N ≤ n - a := by omega
  obtain ⟨j, hjh, ds, hdslen, hdsmem, hdssum⟩ := hN (n - a) hbase
  have hjmem : (j : ℤ) * c ∈ F := by
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjh), rfl⟩
  obtain ⟨ys, hyslen, hysmem, hyssum⟩ := ha ((j : ℤ) * c) hjmem
  refine ⟨ys ++ ds ++ List.replicate j 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, hyslen, hdslen, List.length_replicate]
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with (hx | hx) | ⟨_, rfl⟩
    · exact hysmem x hx
    · exact hdsmem x hx
    · exact hzero
  · simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_zero,
      add_zero, hyssum, hdssum]
    ring

end Erdos336
