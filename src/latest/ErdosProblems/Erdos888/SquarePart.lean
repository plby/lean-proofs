import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Erdős Problem 888: canonical squarefree parts

Every natural number is a square times a squarefree number.  This module
chooses such a decomposition and proves that, for a positive integer, both
factors are forced.  Thus the apparently choice-based definitions below are
canonical on the positive naturals.

The final section records finite-fiber facts in a form convenient for the
counting arguments used in the proof of Erdős Problem 888.
-/

namespace Erdos888

open scoped BigOperators

/-- A chosen square-times-squarefree decomposition, stored as
`(square root, squarefree cofactor)`. -/
private theorem exists_squareDecomposition (n : ℕ) :
    ∃ p : ℕ × ℕ, p.1 ^ 2 * p.2 = n ∧ Squarefree p.2 := by
  obtain ⟨s, k, hk, hs⟩ := Nat.sq_mul_squarefree n
  exact ⟨(k, s), ⟨hk, hs⟩⟩

noncomputable def squareDecomposition (n : ℕ) : ℕ × ℕ :=
  Classical.choose (exists_squareDecomposition n)

/-- The root of the largest square factor in the canonical decomposition. -/
noncomputable def squarePartRoot (n : ℕ) : ℕ :=
  (squareDecomposition n).1

/-- The canonical squarefree cofactor. -/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  (squareDecomposition n).2

private theorem squareDecomposition_spec (n : ℕ) :
    (squareDecomposition n).1 ^ 2 * (squareDecomposition n).2 = n ∧
      Squarefree (squareDecomposition n).2 := by
  exact Classical.choose_spec (exists_squareDecomposition n)

/-- The canonical factors reconstruct the original natural number. -/
theorem squarePart_decomposition (n : ℕ) :
    squarePartRoot n ^ 2 * squarefreePart n = n := by
  simpa [squarePartRoot, squarefreePart] using (squareDecomposition_spec n).1

/-- The chosen cofactor is squarefree, including at zero. -/
theorem squarefreePart_squarefree (n : ℕ) :
    Squarefree (squarefreePart n) := by
  simpa [squarefreePart] using (squareDecomposition_spec n).2

/-- Compatibility spelling for clients that only use the positive case. -/
theorem squarefree_squarefreePart {n : ℕ} (_hn : n ≠ 0) :
    Squarefree (squarefreePart n) :=
  squarefreePart_squarefree n

/-- The canonical square root is positive when the integer is positive. -/
theorem squarePartRoot_pos {n : ℕ} (hn : 0 < n) :
    0 < squarePartRoot n := by
  by_contra h
  have hz : squarePartRoot n = 0 := Nat.eq_zero_of_not_pos h
  have hdecomp := squarePart_decomposition n
  rw [hz] at hdecomp
  simp at hdecomp
  omega

/-- The canonical squarefree cofactor is positive when the integer is positive. -/
theorem squarefreePart_pos {n : ℕ} (hn : 0 < n) :
    0 < squarefreePart n := by
  by_contra h
  have hz : squarefreePart n = 0 := Nat.eq_zero_of_not_pos h
  have hdecomp := squarePart_decomposition n
  rw [hz, Nat.mul_zero] at hdecomp
  omega

/-! ## Uniqueness -/

/-- The squarefree cofactors in two positive square-times-squarefree
decompositions agree. -/
theorem squarefree_cofactor_unique {n k l s t : ℕ} (hn : 0 < n)
    (hs : Squarefree s) (ht : Squarefree t)
    (hks : k ^ 2 * s = n) (hlt : l ^ 2 * t = n) :
    s = t := by
  have hn0 : n ≠ 0 := hn.ne'
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    simp at hks
    exact hn0 hks.symm
  have hl0 : l ≠ 0 := by
    intro hl
    subst l
    simp at hlt
    exact hn0 hlt.symm
  have hs0 : s ≠ 0 := by
    intro hs0
    subst s
    simp at hks
    exact hn0 hks.symm
  have ht0 : t ≠ 0 := by
    intro ht0
    subst t
    simp at hlt
    exact hn0 hlt.symm
  apply Nat.eq_of_factorization_eq hs0 ht0
  intro p
  have hsf := hs.natFactorization_le_one p
  have htf := ht.natFactorization_le_one p
  have hkfac :
      n.factorization p = 2 * k.factorization p + s.factorization p := by
    rw [← hks, Nat.factorization_mul (pow_ne_zero 2 hk0) hs0,
      Nat.factorization_pow]
    simp [Finsupp.add_apply]
  have hlfac :
      n.factorization p = 2 * l.factorization p + t.factorization p := by
    rw [← hlt, Nat.factorization_mul (pow_ne_zero 2 hl0) ht0,
      Nat.factorization_pow]
    simp [Finsupp.add_apply]
  omega

/-- A positive square-times-squarefree decomposition has the canonical
squarefree cofactor. -/
theorem squarefree_cofactor_eq_squarefreePart {n k s : ℕ} (hn : 0 < n)
    (hs : Squarefree s) (hks : k ^ 2 * s = n) :
    s = squarefreePart n := by
  exact squarefree_cofactor_unique hn hs (squarefreePart_squarefree n) hks
    (squarePart_decomposition n)

/-- Once the squarefree cofactor is fixed, the square root is fixed as well. -/
theorem square_root_unique_of_same_cofactor {n k l s : ℕ} (hn : 0 < n)
    (hks : k ^ 2 * s = n) (hls : l ^ 2 * s = n) :
    k = l := by
  have hs0 : s ≠ 0 := by
    intro hs0
    subst s
    simp at hks
    exact hn.ne' hks.symm
  apply Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < s) (hks.trans hls.symm)

/-- A positive square-times-squarefree decomposition has the canonical root. -/
theorem squarePartRoot_unique {n k s : ℕ} (hn : 0 < n)
    (hs : Squarefree s) (hks : k ^ 2 * s = n) :
    k = squarePartRoot n := by
  have hsEq := squarefree_cofactor_eq_squarefreePart hn hs hks
  subst s
  exact square_root_unique_of_same_cofactor hn hks (squarePart_decomposition n)

/-- Both entries of a positive square-times-squarefree decomposition are
unique. -/
theorem square_decomposition_unique {n k l s t : ℕ} (hn : 0 < n)
    (hs : Squarefree s) (ht : Squarefree t)
    (hks : k ^ 2 * s = n) (hlt : l ^ 2 * t = n) :
    k = l ∧ s = t := by
  have hst := squarefree_cofactor_unique hn hs ht hks hlt
  subst t
  exact ⟨square_root_unique_of_same_cofactor hn hks hlt, rfl⟩

/-- The canonical decomposition itself is the unique positive
square-times-squarefree decomposition. -/
theorem eq_canonical_square_decomposition {n k s : ℕ} (hn : 0 < n)
    (hs : Squarefree s) (hks : k ^ 2 * s = n) :
    k = squarePartRoot n ∧ s = squarefreePart n :=
  ⟨squarePartRoot_unique hn hs hks,
    squarefree_cofactor_eq_squarefreePart hn hs hks⟩

/-! ## Elementary bounds -/

/-- The squarefree cofactor of a positive integer is no larger than it. -/
theorem squarefreePart_le {n : ℕ} (hn : 0 < n) :
    squarefreePart n ≤ n := by
  calc
    squarefreePart n ≤ squarePartRoot n ^ 2 * squarefreePart n :=
      Nat.le_mul_of_pos_left _ (pow_pos (squarePartRoot_pos hn) 2)
    _ = n := squarePart_decomposition n

/-- The canonical square factor is no larger than the integer. -/
theorem squarePart_sq_le {n : ℕ} (hn : 0 < n) :
    squarePartRoot n ^ 2 ≤ n := by
  calc
    squarePartRoot n ^ 2 ≤ squarePartRoot n ^ 2 * squarefreePart n :=
      Nat.le_mul_of_pos_right _ (squarefreePart_pos hn)
    _ = n := squarePart_decomposition n

/-- The canonical square root of a positive integer is no larger than the
integer itself. -/
theorem squarePartRoot_le {n : ℕ} (hn : 0 < n) :
    squarePartRoot n ≤ n := by
  calc
    squarePartRoot n ≤ squarePartRoot n * squarePartRoot n :=
      Nat.le_mul_of_pos_right _ (squarePartRoot_pos hn)
    _ = squarePartRoot n ^ 2 := by simp [pow_two]
    _ ≤ n := squarePart_sq_le hn

/-- Equality of both canonical coordinates recovers the original integer. -/
theorem eq_of_squarePartRoot_eq_of_squarefreePart_eq {a b : ℕ}
    (hroot : squarePartRoot a = squarePartRoot b)
    (hfree : squarefreePart a = squarefreePart b) :
    a = b := by
  rw [← squarePart_decomposition a, ← squarePart_decomposition b,
    hroot, hfree]

/-! ## Finite fibers -/

/-- The elements of `A` having a prescribed canonical square root. -/
noncomputable def squarePartFiber (A : Finset ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact A.filter fun n ↦ squarePartRoot n = q

theorem mem_squarePartFiber {A : Finset ℕ} {q n : ℕ} :
    n ∈ squarePartFiber A q ↔ n ∈ A ∧ squarePartRoot n = q := by
  classical
  simp [squarePartFiber]

/-- Fibers over distinct roots are disjoint. -/
theorem disjoint_squarePartFiber {A : Finset ℕ} {q r : ℕ} (hqr : q ≠ r) :
    Disjoint (squarePartFiber A q) (squarePartFiber A r) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro n hnq hnr
  have hq := (mem_squarePartFiber.mp hnq).2
  have hr := (mem_squarePartFiber.mp hnr).2
  exact hqr (hq.symm.trans hr)

/-- On a fixed-root fiber, the squarefree cofactor determines the integer. -/
theorem squarefreePart_injOn_squarePartFiber (A : Finset ℕ) (q : ℕ) :
    Set.InjOn squarefreePart (squarePartFiber A q) := by
  intro a ha b hb hab
  apply eq_of_squarePartRoot_eq_of_squarefreePart_eq
  · exact (mem_squarePartFiber.mp ha).2.trans (mem_squarePartFiber.mp hb).2.symm
  · exact hab

/-- Exact cardinality partition of a finite set by its canonical square root. -/
theorem card_eq_sum_card_squarePartFiber (A : Finset ℕ) :
    A.card = ∑ q ∈ A.image squarePartRoot, (squarePartFiber A q).card := by
  classical
  simpa [squarePartFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := A) (t := A.image squarePartRoot) (f := squarePartRoot)
      (fun n hn ↦ Finset.mem_image_of_mem squarePartRoot hn))

/-- If `A ⊆ {1, …, n}`, its canonical roots also lie in `{1, …, n}`. -/
theorem image_squarePartRoot_subset_Icc {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) :
    A.image squarePartRoot ⊆ Finset.Icc 1 n := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have haIoc := Finset.mem_Ioc.mp (hA ha)
  exact Finset.mem_Icc.mpr
    ⟨squarePartRoot_pos haIoc.1, squarePartRoot_le haIoc.1 |>.trans haIoc.2⟩

/-- For a positive bounded set, the root-fiber cardinalities may be summed
over the fixed interval `{1, …, n}` rather than over a data-dependent image. -/
theorem card_eq_sum_Icc_card_squarePartFiber {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) :
    A.card = ∑ q ∈ Finset.Icc 1 n, (squarePartFiber A q).card := by
  classical
  simpa [squarePartFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := A) (t := Finset.Icc 1 n) (f := squarePartRoot)
      (fun a ha ↦ image_squarePartRoot_subset_Icc hA
        (Finset.mem_image_of_mem squarePartRoot ha)))

/-- The elements of `A` having a prescribed squarefree cofactor. -/
noncomputable def squarefreePartFiber (A : Finset ℕ) (s : ℕ) : Finset ℕ := by
  classical
  exact A.filter fun n ↦ squarefreePart n = s

theorem mem_squarefreePartFiber {A : Finset ℕ} {s n : ℕ} :
    n ∈ squarefreePartFiber A s ↔ n ∈ A ∧ squarefreePart n = s := by
  classical
  simp [squarefreePartFiber]

/-- Fibers over distinct squarefree cofactors are disjoint. -/
theorem disjoint_squarefreePartFiber {A : Finset ℕ} {s t : ℕ} (hst : s ≠ t) :
    Disjoint (squarefreePartFiber A s) (squarefreePartFiber A t) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro n hns hnt
  exact hst ((mem_squarefreePartFiber.mp hns).2.symm.trans
    (mem_squarefreePartFiber.mp hnt).2)

/-- On a fixed-squarefree-part fiber, the canonical square root determines
the integer. -/
theorem squarePartRoot_injOn_squarefreePartFiber (A : Finset ℕ) (s : ℕ) :
    Set.InjOn squarePartRoot (squarefreePartFiber A s) := by
  intro a ha b hb hab
  apply eq_of_squarePartRoot_eq_of_squarefreePart_eq hab
  exact (mem_squarefreePartFiber.mp ha).2.trans
    (mem_squarefreePartFiber.mp hb).2.symm

/-- Exact cardinality partition of a finite set by squarefree cofactor. -/
theorem card_eq_sum_card_squarefreePartFiber (A : Finset ℕ) :
    A.card = ∑ s ∈ A.image squarefreePart, (squarefreePartFiber A s).card := by
  classical
  simpa [squarefreePartFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := A) (t := A.image squarefreePart) (f := squarefreePart)
      (fun n hn ↦ Finset.mem_image_of_mem squarefreePart hn))

/-- If `A ⊆ {1, …, n}`, all squarefree cofactors of its elements also lie
in `{1, …, n}`. -/
theorem image_squarefreePart_subset_Icc {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) :
    A.image squarefreePart ⊆ Finset.Icc 1 n := by
  intro s hs
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  have haIoc := Finset.mem_Ioc.mp (hA ha)
  exact Finset.mem_Icc.mpr
    ⟨squarefreePart_pos haIoc.1, squarefreePart_le haIoc.1 |>.trans haIoc.2⟩

/-- For a positive bounded set, the squarefree-part fiber cardinalities may
be summed over the fixed interval `{1, …, n}`. -/
theorem card_eq_sum_Icc_card_squarefreePartFiber {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) :
    A.card = ∑ s ∈ Finset.Icc 1 n, (squarefreePartFiber A s).card := by
  classical
  simpa [squarefreePartFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := A) (t := Finset.Icc 1 n) (f := squarefreePart)
      (fun a ha ↦ image_squarefreePart_subset_Icc hA
        (Finset.mem_image_of_mem squarefreePart ha)))

end Erdos888
