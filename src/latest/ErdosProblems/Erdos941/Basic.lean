import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic

/-!
# Powerful numbers and representations by at most three positive terms

The divisibility predicate includes zero. The representation predicate explicitly
requires positive summands, so zero terms in a quadratic form must be removed.
-/

namespace Erdos941

/-- Every prime divisor occurs at least twice. -/
def Powerful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- A nonempty sum of at most three positive powerful natural numbers. -/
def Representable (n : ℕ) : Prop :=
  ∃ l : List ℕ, 1 ≤ l.length ∧ l.length ≤ 3 ∧
    (∀ a ∈ l, 0 < a ∧ Powerful a) ∧ l.sum = n

theorem powerful_zero : Powerful 0 := fun _ _ _ => dvd_zero _

theorem powerful_one : Powerful 1 := by
  intro p hp hd
  exact (hp.not_dvd_one hd).elim

theorem powerful_sq (n : ℕ) : Powerful (n ^ 2) := by
  intro p hp hd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2

theorem powerful_cube (n : ℕ) : Powerful (n ^ 3) := by
  intro p hp hd
  have hpn := hp.dvd_of_dvd_pow hd
  exact (pow_dvd_pow p (by omega : 2 ≤ 3)).trans (pow_dvd_pow_of_dvd hpn 3)

theorem Powerful.mul {a b : ℕ} (ha : Powerful a) (hb : Powerful b) :
    Powerful (a * b) := by
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (ha p hp h) b
  · exact dvd_mul_of_dvd_right (hb p hp h) a

theorem powerful_cube_mul_sq (a x : ℕ) : Powerful (a ^ 3 * x ^ 2) :=
  (powerful_cube a).mul (powerful_sq x)

private theorem sum_filter_pos (l : List ℕ) :
    (l.filter fun a => 0 < a).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : 0 < a
    · simp [ha, ih]
    · have : a = 0 := by omega
      simp [this, ih]

theorem representable_of_list {n : ℕ} (hn : 0 < n) (l : List ℕ)
    (hlen : l.length ≤ 3) (hp : ∀ a ∈ l, Powerful a) (hs : l.sum = n) :
    Representable n := by
  let l' := l.filter fun a => 0 < a
  have hsum : l'.sum = n := (sum_filter_pos l).trans hs
  refine ⟨l', ?_, (List.length_filter_le _ _).trans hlen, ?_, hsum⟩
  · have hne : l' ≠ [] := by
      intro h
      simp [h] at hsum
      omega
    exact List.length_pos_iff.mpr hne
  · intro a ha
    obtain ⟨ham, hap⟩ := List.mem_filter.mp ha
    exact ⟨by simpa using hap, hp a ham⟩

theorem representable_of_three {n a b c : ℕ} (hn : 0 < n)
    (ha : Powerful a) (hb : Powerful b) (hc : Powerful c)
    (hs : a + b + c = n) : Representable n := by
  apply representable_of_list hn [a, b, c] (by simp)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · simpa [add_assoc] using hs

theorem Representable.pos {n : ℕ} (h : Representable n) : 0 < n := by
  obtain ⟨l, hl, _, hp, rfl⟩ := h
  cases l with
  | nil => simp at hl
  | cons a l =>
    have := (hp a (by simp)).1
    simp only [List.sum_cons]
    omega

theorem Representable.mul {n k : ℕ} (hn : Representable n) (hk : Powerful k)
    (hkpos : 0 < k) : Representable (k * n) := by
  obtain ⟨l, hlow, hhigh, hp, hs⟩ := hn
  refine ⟨l.map (k * ·), by simpa using hlow, by simpa using hhigh, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ⟨Nat.mul_pos hkpos (hp b hb).1, hk.mul (hp b hb).2⟩
  · rw [List.sum_map_mul_left]
    simpa using congrArg (k * ·) hs

theorem Representable.mul_sq {n k : ℕ} (hn : Representable n) (hk : 0 < k) :
    Representable (k ^ 2 * n) := hn.mul (powerful_sq k) (pow_pos hk _)

theorem representable_of_cube_form {n : ℕ} (hn : 0 < n)
    (a b c x y z : ℕ) (h : a ^ 3 * x ^ 2 + b ^ 3 * y ^ 2 + c ^ 3 * z ^ 2 = n) :
    Representable n :=
  representable_of_three hn (powerful_cube_mul_sq a x)
    (powerful_cube_mul_sq b y) (powerful_cube_mul_sq c z) h

theorem representable_of_int_cube_form {n : ℕ} (hn : 0 < n)
    (a b c : ℕ) (x y z : ℤ)
    (h : (a : ℤ) ^ 3 * x ^ 2 + (b : ℤ) ^ 3 * y ^ 2 + (c : ℤ) ^ 3 * z ^ 2 = n) :
    Representable n := by
  apply representable_of_cube_form hn a b c x.natAbs y.natAbs z.natAbs
  apply Int.natCast_inj.mp
  push_cast
  simpa only [sq_abs] using h

theorem representable_of_three_squares {n : ℕ} (hn : 0 < n) (x y z : ℤ)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = n) : Representable n := by
  apply representable_of_int_cube_form hn 1 1 1 x y z
  simpa using h

theorem Representable.exists_three {n : ℕ} (h : Representable n) :
    ∃ a b c : ℕ, Powerful a ∧ Powerful b ∧ Powerful c ∧ a + b + c = n := by
  obtain ⟨l, hlow, hhigh, hp, hs⟩ := h
  cases l with
  | nil => simp at hlow
  | cons a l =>
    have ha := (hp a (by simp)).2
    cases l with
    | nil => exact ⟨a, 0, 0, ha, powerful_zero, powerful_zero, by simpa using hs⟩
    | cons b l =>
      have hb := (hp b (by simp)).2
      cases l with
      | nil => exact ⟨a, b, 0, ha, hb, powerful_zero, by simpa using hs⟩
      | cons c l =>
        have hc := (hp c (by simp)).2
        have hl : l = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hhigh
          omega
        subst l
        exact ⟨a, b, c, ha, hb, hc, by simpa [add_assoc] using hs⟩

theorem representable_iff_three {n : ℕ} (hn : 0 < n) :
    Representable n ↔
      ∃ a b c : ℕ, Powerful a ∧ Powerful b ∧ Powerful c ∧ a + b + c = n := by
  refine ⟨Representable.exists_three, ?_⟩
  rintro ⟨a, b, c, ha, hb, hc, hs⟩
  exact representable_of_three hn ha hb hc hs

private theorem powerful_le_seven {n : ℕ} (hn : n ≤ 7) (hp : Powerful n) :
    n = 0 ∨ n = 1 ∨ n = 4 := by
  interval_cases n
  · simp
  · simp
  · have := hp 2 (by norm_num) (by norm_num)
    norm_num at this
  · have := hp 3 (by norm_num) (by norm_num)
    norm_num at this
  · simp
  · have := hp 5 (by norm_num) (by norm_num)
    norm_num at this
  · have := hp 2 (by norm_num) (by norm_num)
    norm_num at this
  · have := hp 7 (by norm_num) (by norm_num)
    norm_num at this

/-- The sufficiently-large qualification cannot be discarded. -/
theorem not_representable_seven : ¬ Representable 7 := by
  intro h
  obtain ⟨a, b, c, ha, hb, hc, hs⟩ := h.exists_three
  have ha' := powerful_le_seven (by omega : a ≤ 7) ha
  have hb' := powerful_le_seven (by omega : b ≤ 7) hb
  have hc' := powerful_le_seven (by omega : c ≤ 7) hc
  omega

end Erdos941
