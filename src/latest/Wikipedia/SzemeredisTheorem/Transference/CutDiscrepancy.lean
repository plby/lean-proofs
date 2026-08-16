import Wikipedia.SzemeredisTheorem.Finite.Mean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Delete coordinate `i` from an `r`-tuple. The impossible `r = 0`
case is discharged by eliminating `i : Fin 0`. -/
def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)

@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl

/-- On a nonempty tuple, `eraseCoordinate` is Mathlib's `Fin.removeNth`. -/
theorem eraseCoordinate_eq_removeNth
    {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) :
    eraseCoordinate i x = Fin.removeNth i x :=
  rfl

@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

/-- A family of cut tests, one for each deleted coordinate. -/
abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

/-- Every member of a cut-test family takes values in `[0,1]`. -/
def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

theorem IsBoundedCutTest.nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

theorem isBoundedCutTest_const
    {G : Type*} {r : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsBoundedCutTest (fun _ : Fin r => fun _ : Fin (r - 1) → G => c) :=
  ⟨fun _ _ => hc0, fun _ _ => hc1⟩

@[simp]
theorem isBoundedCutTest_zero
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (0 : ℝ)) :=
  isBoundedCutTest_const (by positivity) (by norm_num)

@[simp]
theorem isBoundedCutTest_one
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) :=
  isBoundedCutTest_const (by positivity) le_rfl

theorem IsBoundedCutTest.mono
    {G : Type*} {r : ℕ} {u v : CutTestFamily G r}
    (hu : IsBoundedCutTest u)
    (hv0 : ∀ i x, 0 ≤ v i x)
    (hvu : ∀ i x, v i x ≤ u i x) :
    IsBoundedCutTest v :=
  ⟨hv0, fun i x => (hvu i x).trans (hu.le_one i x)⟩

theorem IsBoundedCutTest.mul
    {G : Type*} {r : ℕ} {u v : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (hv : IsBoundedCutTest v) :
    IsBoundedCutTest (fun i x => u i x * v i x) := by
  constructor
  · exact fun i x => mul_nonneg (hu.nonneg i x) (hv.nonneg i x)
  · exact fun i x => mul_le_one₀ (hu.le_one i x)
      (hv.nonneg i x) (hv.le_one i x)

/-- The cut correlation of `f-g` with a family of deleted-coordinate
tests. -/
noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

/-- `f` and `g` differ by at most `ε` against every product of
`[0,1]`-valued deleted-coordinate tests. -/
def CutDiscrepancyLe
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |cutCorrelation r f g u| ≤ ε

theorem CutDiscrepancyLe.apply_bounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε)
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    |cutCorrelation r f g u| ≤ ε :=
  h u hu.nonneg hu.le_one

@[simp]
theorem cutCorrelation_self
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f f u = 0 := by
  simp [cutCorrelation]

theorem cutCorrelation_swap
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r g f u = -cutCorrelation r f g u := by
  calc
    cutCorrelation r g f u =
        mean (fun x : Fin r → G =>
          (-1 : ℝ) *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              ∏ i, u i (eraseCoordinate i x))) := by
      apply congrArg mean
      funext x
      ring
    _ = (-1 : ℝ) *
        mean (fun x : Fin r → G =>
          (f (∑ i, x i) - g (∑ i, x i)) *
            ∏ i, u i (eraseCoordinate i x)) :=
      mean_smul _ _
    _ = -cutCorrelation r f g u := by
      simp [cutCorrelation]

theorem cutCorrelation_add_middle
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g h : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f h u =
      cutCorrelation r f g u + cutCorrelation r g h u := by
  rw [cutCorrelation, cutCorrelation, cutCorrelation, ← mean_add]
  apply congrArg mean
  funext x
  ring

theorem CutDiscrepancyLe.mono
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε ε' : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hε : ε ≤ ε') :
    CutDiscrepancyLe r f g ε' := by
  intro u hu0 hu1
  exact (h u hu0 hu1).trans hε

theorem CutDiscrepancyLe.refl
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) :
    CutDiscrepancyLe r f f 0 := by
  intro u _ _
  simp

theorem CutDiscrepancyLe.refl_of_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    CutDiscrepancyLe r f f ε :=
  (CutDiscrepancyLe.refl r f).mono hε

theorem CutDiscrepancyLe.of_eq
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} (hfg : f = g) :
    CutDiscrepancyLe r f g 0 := by
  subst g
  exact CutDiscrepancyLe.refl r f

theorem CutDiscrepancyLe.symm
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    CutDiscrepancyLe r g f ε := by
  intro u hu0 hu1
  rw [cutCorrelation_swap, abs_neg]
  exact h u hu0 hu1

theorem CutDiscrepancyLe.triangle
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g h : G → ℝ} {ε δ : ℝ}
    (hfg : CutDiscrepancyLe r f g ε)
    (hgh : CutDiscrepancyLe r g h δ) :
    CutDiscrepancyLe r f h (ε + δ) := by
  intro u hu0 hu1
  calc
    |cutCorrelation r f h u| =
        |cutCorrelation r f g u + cutCorrelation r g h u| := by
      rw [cutCorrelation_add_middle]
    _ ≤ |cutCorrelation r f g u| + |cutCorrelation r g h u| :=
      abs_add_le _ _
    _ ≤ ε + δ :=
      add_le_add (hfg u hu0 hu1) (hgh u hu0 hu1)

theorem CutDiscrepancyLe.epsilon_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    0 ≤ ε := by
  exact (abs_nonneg (cutCorrelation r f g
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)))).trans
      (h (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
        (fun _ _ => by norm_num) (fun _ _ => le_rfl))

/-- Translation does not change normalized averaging on a finite additive
group. -/
theorem mean_add_right
    {G : Type*} [Fintype G] [AddCommGroup G]
    (h : G → ℝ) (c : G) :
    mean (fun x => h (x + c)) = mean h := by
  unfold mean
  exact Fintype.expect_equiv (Equiv.addRight c)
    (fun x => h (x + c)) h (fun _ => rfl)

/-- For a nonempty tuple, its coordinate sum is uniformly distributed on a
finite additive group. -/
theorem mean_sum_fin_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) = mean h := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) =
        mean (fun p : G × (Fin n → G) =>
          h (p.1 + ∑ i, p.2 i)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) 0).symm
      intro x
      congr 1
      rw [Fin.sum_univ_succ]
      rfl
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          h (a + ∑ i, y i)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) => h (p.1 + ∑ i, p.2 i)))
    _ = mean₂ (fun y : Fin n → G => fun a : G =>
          h (a + ∑ i, y i)) := mean₂_comm _
    _ = mean (fun _ : Fin n → G => mean h) := by
      apply congrArg mean
      funext y
      exact mean_add_right h (∑ i, y i)
    _ = mean h := mean_const _

theorem mean_sum_fin_of_pos
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i)) = mean h := by
  cases r with
  | zero => simp at hr
  | succ n => exact mean_sum_fin_succ n h

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

theorem cutCorrelation_one_eq_mean_sub
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean f - mean g := by
  calc
    cutCorrelation r f g
        (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
      mean (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) :=
      cutCorrelation_one r f g
    _ = mean (fun z : G => f z - g z) :=
      mean_sum_fin_of_pos hr (fun z => f z - g z)
    _ = mean f - mean g := mean_sub f g

/-- The constant-one tests show that cut discrepancy controls the difference
of the means whenever at least one coordinate is present. -/
theorem CutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hr : 0 < r) :
    |mean f - mean g| ≤ ε := by
  have hone := h
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
    (fun _ _ => by norm_num) (fun _ _ => le_rfl)
  simpa [cutCorrelation_one_eq_mean_sub hr f g] using hone

end Wikipedia.SzemeredisTheorem
