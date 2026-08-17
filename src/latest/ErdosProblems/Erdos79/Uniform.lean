import Mathlib

/-!
# Exact counting in a finite uniform product space

This file supplies the elementary finite probability space used in the
probabilistic part of the proof of Erdős Problem 79.  An outcome assigns one
of `q` labels to every coordinate.  We work with cardinalities rather than a
measure: dividing all displayed cardinalities by `q ^ Fintype.card ι` gives
the corresponding uniform probabilities.

The main exact calculation is `card_cylinder`.  It says that requiring the
labels on a set `s` of coordinates to lie in a fixed allowed set `A` leaves
`A.card` choices on each coordinate of `s` and `q` choices everywhere else.
The final lemmas are finite union-bound / first-moment existence principles.
-/

open scoped BigOperators

namespace Erdos79.Uniform

noncomputable section

/-- The finite product space of `q`-valued labels on `ι`. -/
abbrev Outcome (ι : Type*) (q : ℕ) := ι → Fin q

/-- Outcomes whose labels on every coordinate of `s` belong to `A`. -/
def cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) : Finset (Outcome ι q) :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ s, ω i ∈ A

@[simp]
theorem mem_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}
    {s : Finset ι} {A : Finset (Fin q)} {ω : Outcome ι q} :
    ω ∈ cylinder q s A ↔ ∀ i ∈ s, ω i ∈ A := by
  simp [cylinder]

/-- There are exactly `q ^ |ι|` outcomes. -/
@[simp]
theorem card_outcome (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) :
    Fintype.card (Outcome ι q) = q ^ Fintype.card ι := by
  simp [Outcome]

/-- Split a constrained labeling into its restrictions to `s` and to the
complement of `s`. -/
private def cylinderEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) :
    ↑(cylinder q s A) ≃ ((i : ↑s) → ↑A) × ((i : ↑sᶜ) → Fin q) where
  toFun ω :=
    (⟨fun i ↦ ⟨ω.1 i.1, (mem_cylinder.mp ω.2) i.1 i.2⟩,
      fun i ↦ ω.1 i.1⟩)
  invFun x :=
    ⟨fun i ↦ if hi : i ∈ s then (x.1 ⟨i, hi⟩).1
      else x.2 ⟨i, by simpa using hi⟩,
    mem_cylinder.mpr (by
      intro i hi
      simp [hi, (x.1 ⟨i, hi⟩).2])⟩
  left_inv ω := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi]
    · simp [hi]
  right_inv x := by
    rcases x with ⟨a, b⟩
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simp [i.2]
    · funext i
      have hi : (i.1 : ι) ∉ s := Finset.mem_compl.mp i.2
      simp [hi]

/-- Exact cardinality of a finite uniform-product cylinder. -/
theorem card_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    (s : Finset ι) (A : Finset (Fin q)) :
    (cylinder q s A).card =
      A.card ^ s.card * q ^ (Fintype.card ι - s.card) := by
  calc
    (cylinder q s A).card = Fintype.card ↑(cylinder q s A) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (((i : ↑s) → ↑A) × ((i : ↑sᶜ) → Fin q)) :=
      Fintype.card_congr (cylinderEquiv q s A)
    _ = A.card ^ s.card * q ^ (Fintype.card ι - s.card) := by
      simp

/-- The first `r` labels in `Fin q`. -/
def below (q r : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun x ↦ (x : ℕ) < r

@[simp]
theorem mem_below {q r : ℕ} {x : Fin q} :
    x ∈ below q r ↔ (x : ℕ) < r := by
  simp [below]

/-- If `r ≤ q`, exactly `r` members of `Fin q` are below `r`. -/
@[simp]
theorem card_below {q r : ℕ} (hrq : r ≤ q) : (below q r).card = r := by
  let e : Fin r ≃ ↑(below q r) :=
    { toFun := fun x ↦
        ⟨⟨x.1, lt_of_lt_of_le x.2 hrq⟩, by simp⟩
      invFun := fun x ↦ ⟨x.1.1, mem_below.mp x.2⟩
      left_inv := fun x ↦ by apply Fin.ext; rfl
      right_inv := fun x ↦ by apply Subtype.ext; apply Fin.ext; rfl }
  calc
    (below q r).card = Fintype.card ↑(below q r) := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin r) := (Fintype.card_congr e).symm
    _ = r := Fintype.card_fin r

/-- Outcomes with label `< r` at every coordinate of `s`. -/
def thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q r : ℕ) (s : Finset ι) : Finset (Outcome ι q) :=
  cylinder q s (below q r)

@[simp]
theorem mem_thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q r : ℕ} {s : Finset ι} {ω : Outcome ι q} :
    ω ∈ thresholdCylinder q r s ↔ ∀ i ∈ s, (ω i : ℕ) < r := by
  simp [thresholdCylinder]

/-- Exact cardinality of a threshold cylinder. -/
theorem card_thresholdCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q r : ℕ} (hrq : r ≤ q) (s : Finset ι) :
    (thresholdCylinder q r s).card =
      r ^ s.card * q ^ (Fintype.card ι - s.card) := by
  simp [thresholdCylinder, card_cylinder, card_below hrq]

/-- The labels other than a specified label. -/
def exceptLabel {q : ℕ} (a : Fin q) : Finset (Fin q) :=
  Finset.univ.erase a

@[simp]
theorem mem_exceptLabel {q : ℕ} {a x : Fin q} :
    x ∈ exceptLabel a ↔ x ≠ a := by
  simp [exceptLabel]

@[simp]
theorem card_exceptLabel {q : ℕ} (a : Fin q) :
    (exceptLabel a).card = q - 1 := by
  simp [exceptLabel]

/-- A cylinder requiring every coordinate in `s` to avoid one specified
label.  This is the form used to count a completely blue vertex set when one
label is interpreted as red. -/
def avoidingLabelCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (a : Fin q) (s : Finset ι) : Finset (Outcome ι q) :=
  cylinder q s (exceptLabel a)

@[simp]
theorem mem_avoidingLabelCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} {a : Fin q} {s : Finset ι} {ω : Outcome ι q} :
    ω ∈ avoidingLabelCylinder a s ↔ ∀ i ∈ s, ω i ≠ a := by
  simp [avoidingLabelCylinder]

theorem card_avoidingLabelCylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ℕ} (a : Fin q) (s : Finset ι) :
    (avoidingLabelCylinder a s).card =
      (q - 1) ^ s.card * q ^ (Fintype.card ι - s.card) := by
  simp [avoidingLabelCylinder, card_cylinder]

/-- Cardinality form of the finite union bound. -/
theorem card_biUnion_le {J Ω : Type*} [DecidableEq Ω]
    (I : Finset J) (B : J → Finset Ω) :
    (I.biUnion B).card ≤ ∑ j ∈ I, (B j).card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Finset.card_union_le (B a) (I.biUnion B)).trans
        (Nat.add_le_add_left ih (B a).card)

/-- First-moment principle: if the sum of the sizes of the bad events is
smaller than the sample space, some outcome avoids every bad event. -/
theorem exists_avoiding_of_sum_card_lt {J Ω : Type*}
    [Fintype Ω] (I : Finset J) (B : J → Finset Ω)
    (h : (∑ j ∈ I, (B j).card) < Fintype.card Ω) :
    ∃ ω : Ω, ∀ j ∈ I, ω ∉ B j := by
  classical
  have hcard : (I.biUnion B).card < (Finset.univ : Finset Ω).card := by
    simpa using (card_biUnion_le I B).trans_lt h
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ω, ?_⟩
  intro j hj hmem
  exact hω (Finset.mem_biUnion.mpr ⟨j, hj, hmem⟩)

/-- Predicate version of the first-moment principle. -/
theorem exists_avoiding_predicates_of_sum_card_lt {J Ω : Type*}
    [Fintype Ω] (I : Finset J) (bad : J → Ω → Prop)
    [∀ j, DecidablePred (bad j)]
    (h : (∑ j ∈ I, (Finset.univ.filter (bad j)).card) < Fintype.card Ω) :
    ∃ ω : Ω, ∀ j ∈ I, ¬ bad j ω := by
  classical
  obtain ⟨ω, hω⟩ := exists_avoiding_of_sum_card_lt I
    (fun j ↦ Finset.univ.filter (bad j)) h
  exact ⟨ω, fun j hj hbad ↦ hω j hj (by simp [hbad])⟩

/-- Cylinder-specialized first-moment principle. -/
theorem exists_avoiding_cylinders_of_sum_lt {ι J : Type*}
    [Fintype ι] (q : ℕ) (I : Finset J)
    (support : J → Finset ι) (allowed : J → Finset (Fin q))
    (h : (∑ j ∈ I,
        (allowed j).card ^ (support j).card *
          q ^ (Fintype.card ι - (support j).card)) <
        q ^ Fintype.card ι) :
    ∃ ω : Outcome ι q,
      ∀ j ∈ I, ∃ i ∈ support j, ω i ∉ allowed j := by
  classical
  have h' : (∑ j ∈ I, (cylinder q (support j) (allowed j)).card) <
      Fintype.card (Outcome ι q) := by
    simpa [card_cylinder, card_outcome] using h
  obtain ⟨ω, hω⟩ := exists_avoiding_of_sum_card_lt I
    (fun j ↦ cylinder q (support j) (allowed j)) h'
  refine ⟨ω, ?_⟩
  intro j hj
  by_contra hno
  apply hω j hj
  rw [mem_cylinder]
  intro i hi
  by_contra hbad
  exact hno ⟨i, hi, hbad⟩

/-- Double-counting identity underlying finite first-moment calculations:
sum event sizes by event, or sum the number of events containing each
outcome. -/
theorem sum_card_eq_sum_memberships {J Ω : Type*}
    [Fintype J] [Fintype Ω] [DecidableEq Ω] (B : J → Finset Ω) :
    ∑ j, (B j).card =
      ∑ ω, ((Finset.univ.filter fun j ↦ ω ∈ B j).card) := by
  classical
  calc
    ∑ j ∈ (Finset.univ : Finset J), (B j).card =
        ∑ j ∈ (Finset.univ : Finset J),
          ∑ ω ∈ (Finset.univ : Finset Ω), if ω ∈ B j then 1 else 0 := by
      simp
    _ = ∑ ω ∈ (Finset.univ : Finset Ω),
        ∑ j ∈ (Finset.univ : Finset J), if ω ∈ B j then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ ω ∈ (Finset.univ : Finset Ω),
        ((Finset.univ.filter fun j ↦ ω ∈ B j).card) := by
      simp

section ExponentialBounds

/-- Raising `1 - x ≤ exp (-x)` to a natural power.  This is the elementary
exponential estimate used for the blue-clique term in a union bound. -/
theorem one_sub_pow_le_exp_neg_mul {x : ℝ} (_hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (n : ℕ) :
    (1 - x) ^ n ≤ Real.exp (-(n : ℝ) * x) := by
  calc
    (1 - x) ^ n ≤ Real.exp (-x) ^ n :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx₁) (Real.one_sub_le_exp_neg x) n
    _ = Real.exp ((n : ℝ) * (-x)) := (Real.exp_nat_mul (-x) n).symm
    _ = Real.exp (-(n : ℝ) * x) := by ring_nf

/-- Crude exponential upper bound for a binomial coefficient. -/
theorem cast_choose_le_exp_mul_log {n k : ℕ} (hn : 0 < n) :
    (n.choose k : ℝ) ≤ Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
  calc
    (n.choose k : ℝ) ≤ (n ^ k : ℕ) := by
      exact_mod_cast Nat.choose_le_pow n k
    _ = (n : ℝ) ^ k := by norm_num
    _ = Real.exp (Real.log (n : ℝ)) ^ k := by
      rw [Real.exp_log (by positivity : (0 : ℝ) < n)]
    _ = Real.exp ((k : ℝ) * Real.log (n : ℝ)) :=
      (Real.exp_nat_mul (Real.log (n : ℝ)) k).symm

end ExponentialBounds

end

end Erdos79.Uniform
