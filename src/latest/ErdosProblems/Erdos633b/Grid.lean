import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The finite triangular grid, including all boundary vertices. -/

namespace Erdos633b

abbrev UpCell (n : ℕ) := {p : Fin n × Fin n // p.1.val + p.2.val < n}
abbrev DownCell (n : ℕ) := {p : Fin n × Fin n // p.1.val + p.2.val + 2 ≤ n}
abbrev GridCell (n : ℕ) := UpCell n ⊕ DownCell n

namespace GridCell

def ix {n : ℕ} : GridCell n → ℕ
  | .inl p => p.val.1.val
  | .inr p => p.val.1.val

def iy {n : ℕ} : GridCell n → ℕ
  | .inl p => p.val.2.val
  | .inr p => p.val.2.val

def Closed {n : ℕ} (c : GridCell n) (x y : ℝ) : Prop :=
  match c with
  | .inl p => (p.val.1 : ℝ) ≤ x ∧ (p.val.2 : ℝ) ≤ y ∧
      x + y ≤ (p.val.1 : ℝ) + (p.val.2 : ℝ) + 1
  | .inr p => x ≤ (p.val.1 : ℝ) + 1 ∧ y ≤ (p.val.2 : ℝ) + 1 ∧
      (p.val.1 : ℝ) + (p.val.2 : ℝ) + 1 ≤ x + y

def Inside {n : ℕ} (c : GridCell n) (x y : ℝ) : Prop :=
  match c with
  | .inl p => (p.val.1 : ℝ) < x ∧ (p.val.2 : ℝ) < y ∧
      x + y < (p.val.1 : ℝ) + (p.val.2 : ℝ) + 1
  | .inr p => x < (p.val.1 : ℝ) + 1 ∧ y < (p.val.2 : ℝ) + 1 ∧
      (p.val.1 : ℝ) + (p.val.2 : ℝ) + 1 < x + y

def up (n i j : ℕ) (h : i + j < n) : GridCell n :=
  .inl ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), h⟩

def down (n i j : ℕ) (h : i + j + 2 ≤ n) : GridCell n :=
  .inr ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), h⟩

theorem closed_subset {n : ℕ} (c : GridCell n) {x y : ℝ} (h : c.Closed x y) :
    0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ n := by
  cases c with
  | inl p =>
    have hb : (p.val.1 : ℝ) + (p.val.2 : ℝ) + 1 ≤ n := by exact_mod_cast p.property
    change _ ∧ _ ∧ _ at h
    exact ⟨le_trans (Nat.cast_nonneg _) h.1, le_trans (Nat.cast_nonneg _) h.2.1,
      h.2.2.trans hb⟩
  | inr p =>
    have hb : (p.val.1 : ℝ) + (p.val.2 : ℝ) + 2 ≤ n := by exact_mod_cast p.property
    have hi : 0 ≤ (p.val.1 : ℝ) := Nat.cast_nonneg _
    have hj : 0 ≤ (p.val.2 : ℝ) := Nat.cast_nonneg _
    change _ ∧ _ ∧ _ at h
    constructor
    · linarith [h.2.1, h.2.2]
    constructor
    · linarith [h.1, h.2.2]
    · linarith [h.1, h.2.1]

theorem exists_closed (n : ℕ) (hn : 0 < n) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ n) :
    ∃ c : GridCell n, c.Closed x y := by
  let i := ⌊x⌋₊
  let j := ⌊y⌋₊
  have hi : (i : ℝ) ≤ x := Nat.floor_le hx
  have hj : (j : ℝ) ≤ y := Nat.floor_le hy
  have hi' : x < (i : ℝ) + 1 := Nat.lt_floor_add_one x
  have hj' : y < (j : ℝ) + 1 := Nat.lt_floor_add_one y
  have hsum : i + j ≤ n := by
    have h : (i : ℝ) + (j : ℝ) ≤ n := by linarith
    exact_mod_cast h
  by_cases hlt : i + j < n
  · by_cases hup : x + y ≤ (i : ℝ) + (j : ℝ) + 1
    · exact ⟨up n i j hlt, hi, hj, hup⟩
    · have hd : i + j + 2 ≤ n := by
        have h : (i : ℝ) + (j : ℝ) + 1 < n := by linarith
        have h' : i + j + 1 < n := by exact_mod_cast h
        omega
      exact ⟨down n i j hd, hi'.le, hj'.le, le_of_not_ge hup⟩
  · have he : i + j = n := by omega
    have he' : (i : ℝ) + (j : ℝ) = n := by exact_mod_cast he
    have hxi : x = i := by linarith
    have hyj : y = j := by linarith
    by_cases hip : 0 < i
    · have hb : i - 1 + j < n := by omega
      refine ⟨up n (i - 1) j hb, ?_⟩
      change ((i - 1 : ℕ) : ℝ) ≤ x ∧ (j : ℝ) ≤ y ∧
        x + y ≤ ((i - 1 : ℕ) : ℝ) + (j : ℝ) + 1
      rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
      exact ⟨by linarith, hj, by linarith⟩
    · have hjp : 0 < j := by omega
      have hb : i + (j - 1) < n := by omega
      refine ⟨up n i (j - 1) hb, ?_⟩
      change (i : ℝ) ≤ x ∧ ((j - 1 : ℕ) : ℝ) ≤ y ∧
        x + y ≤ (i : ℝ) + ((j - 1 : ℕ) : ℝ) + 1
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      exact ⟨hi, by linarith, by linarith⟩

theorem inside_bounds {n : ℕ} (c : GridCell n) {x y : ℝ} (h : c.Inside x y) :
    (c.ix : ℝ) < x ∧ x < (c.ix : ℝ) + 1 ∧
      (c.iy : ℝ) < y ∧ y < (c.iy : ℝ) + 1 := by
  cases c with
  | inl p =>
    change _ ∧ _ ∧ _ at h
    change (p.val.1 : ℝ) < x ∧ x < (p.val.1 : ℝ) + 1 ∧
      (p.val.2 : ℝ) < y ∧ y < (p.val.2 : ℝ) + 1
    exact ⟨h.1, by linarith [h.2.1, h.2.2], h.2.1, by linarith [h.1, h.2.2]⟩
  | inr p =>
    change _ ∧ _ ∧ _ at h
    change (p.val.1 : ℝ) < x ∧ x < (p.val.1 : ℝ) + 1 ∧
      (p.val.2 : ℝ) < y ∧ y < (p.val.2 : ℝ) + 1
    exact ⟨by linarith [h.2.1, h.2.2], h.1, by linarith [h.1, h.2.2], h.2.1⟩

theorem lower_endpoint_unique (i j : ℕ) (x : ℝ)
    (hi : (i : ℝ) < x) (hi' : x < (i : ℝ) + 1)
    (hj : (j : ℝ) < x) (hj' : x < (j : ℝ) + 1) : i = j := by
  have hij : i < j + 1 := by exact_mod_cast (hi.trans hj')
  have hji : j < i + 1 := by exact_mod_cast (hj.trans hi')
  omega

theorem inside_unique {n : ℕ} (c d : GridCell n) {x y : ℝ}
    (hc : c.Inside x y) (hd : d.Inside x y) : c = d := by
  obtain ⟨hcx, hcx', hcy, hcy'⟩ := c.inside_bounds hc
  obtain ⟨hdx, hdx', hdy, hdy'⟩ := d.inside_bounds hd
  have hi := lower_endpoint_unique c.ix d.ix x hcx hcx' hdx hdx'
  have hj := lower_endpoint_unique c.iy d.iy y hcy hcy' hdy hdy'
  cases c with
  | inl p =>
    cases d with
    | inl q =>
      apply congrArg Sum.inl
      apply Subtype.ext
      exact Prod.ext (Fin.ext hi) (Fin.ext hj)
    | inr q =>
      have hi' : (p.val.1 : ℝ) = (q.val.1 : ℝ) := by exact_mod_cast hi
      have hj' : (p.val.2 : ℝ) = (q.val.2 : ℝ) := by exact_mod_cast hj
      change _ ∧ _ ∧ _ at hc hd
      exfalso
      linarith [hc.2.2, hd.2.2]
  | inr p =>
    cases d with
    | inl q =>
      have hi' : (p.val.1 : ℝ) = (q.val.1 : ℝ) := by exact_mod_cast hi
      have hj' : (p.val.2 : ℝ) = (q.val.2 : ℝ) := by exact_mod_cast hj
      change _ ∧ _ ∧ _ at hc hd
      exfalso
      linarith [hc.2.2, hd.2.2]
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (Fin.ext hi) (Fin.ext hj)

end GridCell

end Erdos633b
