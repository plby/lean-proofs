import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Order.Partition.Finpartition
import Wikipedia.SzemeredisTheorem.Finite.Mean

/-!
# Conditional averages on finite partitions

Hypergraph regularity in this project is finite.  A partition of `univ`
therefore carries an elementary conditional average: on each atom, replace a
function by its normalized average over that atom.  This file establishes the
algebraic facts needed by the later energy-increment argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Average `f` on the atom of `P` containing `x`. -/
noncomputable def conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) : ℝ :=
  Finset.expect (P.part x) f

theorem conditionalMean_eq_of_part_eq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hxy : P.part x = P.part y) :
    conditionalMean P f x = conditionalMean P f y := by
  rw [conditionalMean, conditionalMean, hxy]

/-- Conditional averages are constant on every partition atom. -/
theorem conditionalMean_eq_of_mem_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {x y : Ω}
    (hy : y ∈ P.part x) :
    conditionalMean P f y = conditionalMean P f x := by
  apply conditionalMean_eq_of_part_eq
  apply P.part_eq_of_mem
  · simp
  · exact hy

theorem conditionalMean_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    0 ≤ conditionalMean P f x := by
  exact Finset.expect_nonneg fun y _ => hf y

theorem conditionalMean_add {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y + g y) x =
      conditionalMean P f x + conditionalMean P g x := by
  exact Finset.expect_add_distrib (P.part x) f g

theorem conditionalMean_sub {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f g : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => f y - g y) x =
      conditionalMean P f x - conditionalMean P g x := by
  exact Finset.expect_sub_distrib (P.part x) f g

theorem conditionalMean_smul {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (fun y => c * f y) x =
      c * conditionalMean P f x := by
  exact (Finset.mul_expect (P.part x) f c).symm

theorem conditionalMean_le_one {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ} (hf : ∀ x, f x ≤ 1) (x : Ω) :
    conditionalMean P f x ≤ 1 := by
  apply Finset.expect_le
  · simp
  · exact fun y _ => hf y

@[simp]
theorem conditionalMean_const {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (c : ℝ) (x : Ω) :
    conditionalMean P (fun _ => c) x = c := by
  rw [conditionalMean]
  exact Finset.expect_const (by simp) c

/-- Averaging a conditional average over the same partition does nothing. -/
@[simp]
theorem conditionalMean_idem {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P (conditionalMean P f) x =
      conditionalMean P f x := by
  rw [conditionalMean]
  calc
    Finset.expect (P.part x) (conditionalMean P f) =
        Finset.expect (P.part x)
          (fun _ => conditionalMean P f x) := by
      apply Finset.expect_congr rfl
      intro y hy
      exact conditionalMean_eq_of_mem_part P f hy
    _ = conditionalMean P f x :=
      Finset.expect_const (by simp) _

/-- On one atom, summing its conditional average recovers the original
sum on that atom. -/
theorem sum_conditionalMean_on_part {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) {s : Finset Ω} (hs : s ∈ P.parts) :
    ∑ x ∈ s, conditionalMean P f x = ∑ x ∈ s, f x := by
  calc
    ∑ x ∈ s, conditionalMean P f x =
        ∑ x ∈ s, Finset.expect s f := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [conditionalMean, P.part_eq_of_mem hs hx]
    _ = (s.card : ℝ) * Finset.expect s f := by
      simp
    _ = ∑ x ∈ s, f x := Finset.card_mul_expect s f

/-- Conditional averaging preserves the total sum. -/
theorem sum_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    ∑ x, conditionalMean P f x = ∑ x, f x := by
  classical
  have hparts :
      P.parts.biUnion id = (Finset.univ : Finset Ω) :=
    P.biUnion_parts
  calc
    ∑ x, conditionalMean P f x =
        ∑ x ∈ P.parts.biUnion id, conditionalMean P f x := by
      exact Finset.sum_congr hparts.symm fun _ _ => rfl
    _ =
        ∑ s ∈ P.parts, ∑ x ∈ s, conditionalMean P f x := by
      exact Finset.sum_biUnion P.disjoint
    _ = ∑ s ∈ P.parts, ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro s hs
      exact sum_conditionalMean_on_part P f hs
    _ = ∑ x ∈ P.parts.biUnion id, f x :=
      (Finset.sum_biUnion P.disjoint).symm
    _ = ∑ x, f x := by
      exact Finset.sum_congr hparts fun _ _ => rfl

/-- Conditional averaging preserves the normalized global mean. -/
theorem mean_conditionalMean {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    mean (conditionalMean P f) = mean f := by
  change (𝔼 x, conditionalMean P f x) = 𝔼 x, f x
  rw [Fintype.expect_eq_sum_div_card,
    Fintype.expect_eq_sum_div_card, sum_conditionalMean P f]

/-- Finite Jensen/Cauchy--Schwarz on the atom containing `x`. -/
theorem conditionalMean_sq_le {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) (x : Ω) :
    conditionalMean P f x ^ 2 ≤
      conditionalMean P (fun y => f y ^ 2) x := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      (P.part x) f (fun _ : Ω => (1 : ℝ))
  simpa [conditionalMean,
    Finset.expect_const (s := P.part x) (by simp) (1 : ℝ)] using h

/-- The `L²` energy of a function relative to a finite partition. -/
noncomputable def partitionEnergy {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) : ℝ :=
  mean fun x => conditionalMean P f x ^ 2

theorem partitionEnergy_nonneg {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    0 ≤ partitionEnergy P f := by
  exact mean_nonneg fun x => sq_nonneg _

/-- Conditional expectation is an `L²` contraction. -/
theorem partitionEnergy_le_mean_sq {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    (f : Ω → ℝ) :
    partitionEnergy P f ≤ mean fun x => f x ^ 2 := by
  calc
    partitionEnergy P f ≤
        mean (conditionalMean P fun x => f x ^ 2) :=
      mean_mono fun x => conditionalMean_sq_le P f x
    _ = mean (fun x => f x ^ 2) :=
      mean_conditionalMean P fun x => f x ^ 2

theorem partitionEnergy_le_one {Ω : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : Finpartition (Finset.univ : Finset Ω))
    {f : Ω → ℝ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    partitionEnergy P f ≤ 1 := by
  apply mean_le_of_le_const
  intro x
  have h0 := conditionalMean_nonneg P hf0 x
  have h1 := conditionalMean_le_one P hf1 x
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

end Wikipedia.SzemeredisTheorem
