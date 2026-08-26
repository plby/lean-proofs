import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 336: faithful formal target

This file fixes the meanings of variable-length (`at most r`) and exact
asymptotic additive bases.  A final solution must prove
`HasProblem336Value c` for an explicit real constant `c`.

The fidelity audit is in `check_answer/README.md`.
-/

namespace Erdos336

/-- `n` is a sum of exactly `k` (not necessarily distinct) members of `A`.
The list model deliberately permits repeated summands. -/
def RepresentsExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ xs : List ℕ,
    xs.length = k ∧
    (∀ x ∈ xs, x ∈ A) ∧
    xs.sum = n

/-- Every sufficiently large natural is a sum of exactly `k` members of `A`. -/
def EventuallyExactly (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RepresentsExactly A k n

/-- Every sufficiently large natural is a sum of at most `r` members of `A`. -/
def EventuallyAtMost (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ k : ℕ, k ≤ r ∧ RepresentsExactly A k n

/-- `A` has exact asymptotic order `k`: `k` works and no smaller number of
summands works eventually. -/
def HasExactOrder (A : Set ℕ) (k : ℕ) : Prop :=
  EventuallyExactly A k ∧ ∀ j : ℕ, j < k → ¬ EventuallyExactly A j

/-- `k` is achievable at variable order at most `r` and exact order `k`. -/
def Admissible (r k : ℕ) : Prop :=
  ∃ A : Set ℕ, EventuallyAtMost A r ∧ HasExactOrder A k

/-- `h` is the Erdős--Graham extremal function.  This relational definition
neither assumes nor silently manufactures existence/boundedness of a maximum. -/
def IsExtremalFunction (h : ℕ → ℕ) : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    Admissible r (h r) ∧ ∀ k : ℕ, Admissible r k → k ≤ h r

/-- The statement that the answer to Problem 336 is the explicit constant `c`.
It asserts both that the finite attained maxima genuinely define an extremal
function and that every such function has the required limit, so the limit
clause cannot hold vacuously. -/
def HasProblem336Value (c : ℝ) : Prop :=
  (∃ h : ℕ → ℕ, IsExtremalFunction h) ∧
    ∀ h : ℕ → ℕ, IsExtremalFunction h →
      Filter.Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2)
        Filter.atTop (nhds c)

/-- Sanity check: the formal extremal function, if it exists, is unique on
all arguments `r ≥ 2`. -/
theorem extremalFunction_unique_on_ge_two
    {h₁ h₂ : ℕ → ℕ} (H₁ : IsExtremalFunction h₁)
    (H₂ : IsExtremalFunction h₂) {r : ℕ} (hr : 2 ≤ r) :
    h₁ r = h₂ r := by
  apply Nat.le_antisymm
  · exact (H₂ r hr).2 (h₁ r) (H₁ r hr).1
  · exact (H₁ r hr).2 (h₂ r) (H₂ r hr).1

/-- If zero is available, every eventually-at-most-`r` representation can be
padded with zeros to an exact `r`-term representation. -/
theorem eventuallyExactly_of_eventuallyAtMost_of_zero
    {A : Set ℕ} {r : ℕ} (hA : EventuallyAtMost A r) (hzero : 0 ∈ A) :
    EventuallyExactly A r := by
  obtain ⟨N, hN⟩ := hA
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, hkr, xs, hlen, hmem, hsum⟩ := hN n hn
  refine ⟨xs ++ List.replicate (r - k) 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, hlen, List.length_replicate]
    omega
  · intro x hx
    simp only [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact hmem x hx
    · exact hzero
  · simp only [List.sum_append, hsum, List.sum_replicate, smul_eq_mul,
      mul_zero, add_zero]

/-- Consequently, a set containing zero cannot have exact order larger than
its variable-length order. -/
theorem exactOrder_le_atMostOrder_of_zero
    {A : Set ℕ} {r k : ℕ} (hatMost : EventuallyAtMost A r)
    (hexact : HasExactOrder A k) (hzero : 0 ∈ A) : k ≤ r := by
  by_contra hnot
  have hrk : r < k := Nat.lt_of_not_ge hnot
  exact (hexact.2 r hrk) (eventuallyExactly_of_eventuallyAtMost_of_zero hatMost hzero)

/-- In particular, any admissible example whose exact order exceeds `r` must
omit zero. -/
theorem zero_not_mem_of_admissible_of_lt
    {r k : ℕ} (hrk : r < k) {A : Set ℕ}
    (hA : EventuallyAtMost A r ∧ HasExactOrder A k) : 0 ∉ A := by
  intro hzero
  exact (Nat.not_le_of_gt hrk)
    (exactOrder_le_atMostOrder_of_zero hA.1 hA.2 hzero)

-- Final-answer shape (replace `c` by a numeral/rational and supply a proof):
-- theorem problem336 : HasProblem336Value c := by ...

section FiniteDictionary

variable {G : Type*} [AddCommGroup G]

/-- Exact-length representation in an arbitrary additive commutative group. -/
def GroupRepExactly (A : Set G) (k : ℕ) (x : G) : Prop :=
  ∃ xs : List G, xs.length = k ∧ (∀ y ∈ xs, y ∈ A) ∧ xs.sum = x

/-- Variable-length representation using at most `k` terms. -/
def GroupRepAtMost (A : Set G) (k : ℕ) (x : G) : Prop :=
  ∃ j ≤ k, GroupRepExactly A j x

/-- Translate `A` so that the distinguished element `e` becomes zero. -/
def ShiftToZero (A : Set G) (e : G) : Set G :=
  {y | y + e ∈ A}

lemma zero_mem_shiftToZero {A : Set G} {e : G} (he : e ∈ A) :
    0 ∈ ShiftToZero A e := by
  simpa [ShiftToZero]

lemma sum_map_sub_right (xs : List G) (e : G) :
    (xs.map (fun x => x - e)).sum = xs.sum - xs.length • e := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp [add_smul]
      abel

lemma sum_map_add_right (xs : List G) (e : G) :
    (xs.map (fun x => x + e)).sum = xs.sum + xs.length • e := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      simp [add_smul]
      abel

/-- Translating every summand by `-e` translates a `k`-term sum by
`-(k • e)`, and conversely. -/
theorem groupRepExactly_shift_iff {A : Set G} {e x : G} {k : ℕ} :
    GroupRepExactly A k x ↔
      GroupRepExactly (ShiftToZero A e) k (x - k • e) := by
  constructor
  · rintro ⟨xs, hlen, hmem, hsum⟩
    refine ⟨xs.map (fun z => z - e), by simp [hlen], ?_, ?_⟩
    · intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simp only [ShiftToZero, Set.mem_setOf_eq, sub_add_cancel]
      exact hmem z hz
    · simpa [hlen, hsum] using sum_map_sub_right xs e
  · rintro ⟨ys, hlen, hmem, hsum⟩
    refine ⟨ys.map (fun z => z + e), by simp [hlen], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hmem y hy
    · rw [sum_map_add_right, hlen, hsum]
      simp

/-- A zero in the translated generating set pads every at-most-`k`
representation to length exactly `k`. -/
theorem groupRepExactly_of_atMost_of_zero {A : Set G} {k : ℕ} {x : G}
    (h : GroupRepAtMost A k x) (hzero : 0 ∈ A) :
    GroupRepExactly A k x := by
  obtain ⟨j, hjk, xs, hlen, hmem, hsum⟩ := h
  refine ⟨xs ++ List.replicate (k - j) 0, ?_, ?_, ?_⟩
  · simp only [List.length_append, hlen, List.length_replicate]
    omega
  · intro y hy
    simp only [List.mem_append, List.mem_replicate] at hy
    rcases hy with hy | ⟨_, rfl⟩
    · exact hmem y hy
    · exact hzero
  · simp [hsum]

/-- The exact power of `A` at time `k` is full exactly when the radius-`k`
positive ball for `A-e` is full.  Pointwise, the target is translated by
`k • e`; this is the exponent/diameter dictionary for Cayley digraphs. -/
theorem exact_iff_shifted_atMost {A : Set G} {e : G} (he : e ∈ A)
    {k : ℕ} {x : G} :
    GroupRepExactly A k x ↔
      GroupRepAtMost (ShiftToZero A e) k (x - k • e) := by
  rw [groupRepExactly_shift_iff]
  constructor
  · intro hx
    exact ⟨k, le_rfl, hx⟩
  · intro hx
    exact groupRepExactly_of_atMost_of_zero hx (zero_mem_shiftToZero he)

/-- Surjectivity of the exact `k`-fold sumset is equivalent to surjectivity
of the translated at-most-`k` ball. -/
theorem all_exact_iff_all_shifted_atMost {A : Set G} {e : G} (he : e ∈ A)
    (k : ℕ) :
    (∀ x : G, GroupRepExactly A k x) ↔
      (∀ y : G, GroupRepAtMost (ShiftToZero A e) k y) := by
  constructor
  · intro h y
    have := (exact_iff_shifted_atMost he (x := y + k • e)).mp (h (y + k • e))
    simpa using this
  · intro h x
    exact (exact_iff_shifted_atMost he).mpr (h (x - k • e))

end FiniteDictionary

end Erdos336
