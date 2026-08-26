import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.CyclicCompactApproximation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite removal normalization to a weak-basis problem
-/

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma sum_filter_ne_zero (xs : List G) :
    (xs.filter fun x => x != 0).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x = 0
      · simp [hx, ih]
      · simp [hx, ih]

/-- Adjoining zero does not change at-most representability: zero terms can
simply be deleted. -/
theorem groupRepAtMost_union_zero_iff
    {B : Set G} {h : ℕ} {y : G} :
    GroupRepAtMost (B ∪ {0}) h y ↔ GroupRepAtMost B h y := by
  constructor
  · rintro ⟨j, hjh, xs, hlen, hxmem, hxsum⟩
    let ys := xs.filter fun x => x != 0
    refine ⟨ys.length, ?_, ys, rfl, ?_, ?_⟩
    · exact le_trans (List.length_filter_le _ _) (by simpa [hlen] using hjh)
    · intro z hz
      have hz' := List.mem_of_mem_filter hz
      have hzne : z ≠ 0 := by
        simpa using (List.mem_filter.mp hz).2
      rcases hxmem z hz' with hzB | hz0
      · exact hzB
      · exact (hzne (Set.mem_singleton_iff.mp hz0)).elim
    · simpa [ys, sum_filter_ne_zero, hxsum]
  · rintro ⟨j, hjh, xs, hlen, hxmem, hxsum⟩
    exact ⟨j, hjh, xs, hlen, fun z hz => Or.inl (hxmem z hz), hxsum⟩

/-- Translating the one-extra parent by the exceptional element turns exact
parent coverage into weak coverage by the translated removed set. -/
theorem all_atMost_shift_of_exact_parent
    {A : Set G} {x : G} {h : ℕ}
    (hparent : ∀ y : G, GroupRepExactly (A ∪ {x}) h y) :
    ∀ y : G, GroupRepAtMost (ShiftToZero A x) h y := by
  have hxparent : x ∈ A ∪ {x} := Or.inr rfl
  have hweakParent : ∀ y : G,
      GroupRepAtMost (ShiftToZero (A ∪ {x}) x) h y :=
    (all_exact_iff_all_shifted_atMost hxparent h).mp hparent
  intro y
  apply groupRepAtMost_union_zero_iff.mp
  have hset : ShiftToZero (A ∪ {x}) x = ShiftToZero A x ∪ {0} := by
    ext z
    simp only [ShiftToZero, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro hz
      rcases hz with hzA | hzx
      · exact Or.inl hzA
      · right
        apply add_right_cancel (b := x)
        simpa using hzx
    · intro hz
      rcases hz with hzA | rfl
      · exact Or.inl hzA
      · exact Or.inr (by simp)
  rw [← hset]
  exact hweakParent y

/-- Full exact powers are invariant, up to a target translation, when all
summands are translated. -/
theorem all_exact_shift_iff
    {A : Set G} {x : G} (k : ℕ) :
    (∀ y : G, GroupRepExactly A k y) ↔
      ∀ y : G, GroupRepExactly (ShiftToZero A x) k y := by
  constructor
  · intro h y
    simpa using (groupRepExactly_shift_iff.mp (h (y + k • x)) :
      GroupRepExactly (ShiftToZero A x) k ((y + k • x) - k • x))
  · intro h y
    apply groupRepExactly_shift_iff.mpr
    simpa using h (y - k • x)

/-- A uniform weak-to-strong bound for finite cyclic groups. -/
def CyclicWeakStrongBound (h M : ℕ) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ B : Set (ZMod N),
    (∀ y : ZMod N, GroupRepAtMost B h y) →
    (∃ q : ℕ, ∀ y : ZMod N, GroupRepExactly B q y) →
    ∀ y : ZMod N, GroupRepExactly B M y

/-- Every cyclic weak-to-strong bound implies the finite removal bound used by
the compact transference theorem, with no loss. -/
theorem cyclicRemovalBound_of_weakStrongBound
    {h M : ℕ} (H : CyclicWeakStrongBound h M) :
    CyclicRemovalBound h M := by
  intro N hN A x hzero hparent hexact
  let B : Set (ZMod N) := ShiftToZero A x
  have hweak : ∀ y : ZMod N, GroupRepAtMost B h y :=
    all_atMost_shift_of_exact_parent hparent
  obtain ⟨q, hq⟩ := hexact
  have hqB : ∀ y : ZMod N, GroupRepExactly B q y :=
    (all_exact_shift_iff q).mp hq
  have hMB := H N hN B hweak ⟨q, hqB⟩
  exact (all_exact_shift_iff M).mpr hMB

end Erdos336
