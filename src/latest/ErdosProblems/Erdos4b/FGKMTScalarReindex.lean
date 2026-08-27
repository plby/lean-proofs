/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentReindex

/-!
# Optional-prime products as one-dimensional arithmetic sums

Unique factorization gives a bijection on nonzero summands. The finite
prime universe may be larger than the summation interval, and the rough
modulus may be any multiple of the modulus excluded by that universe.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem assignmentPrimeTuple_unit (p : α → ℕ) (a : α → Option Unit) :
    assignmentPrimeTuple p a () = assignmentPrimeProduct p a := by
  simpa using prod_assignmentPrimeTuple p a

theorem assignmentPrimeProduct_unit_injective {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) :
    Function.Injective (assignmentPrimeProduct p : (α → Option Unit) → ℕ) := by
  intro a b hab
  apply assignmentPrimeTuple_injective hp hinj
  funext i
  cases i
  simpa only [assignmentPrimeTuple_unit] using hab

theorem assignmentPrimeProduct_assignmentOfUnit {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) {n : ℕ}
    (hn : Squarefree n) (hcover : ∀ l : ℕ, l.Prime → l ∣ n → ∃ q, p q = l) :
    assignmentPrimeProduct p (assignmentOfTuple p (fun _ : Unit => n)) = n := by
  have h := assignmentPrimeTuple_assignmentOfTuple hp hinj
    (r := fun _ : Unit => n) (by simpa using hn) (by simpa using hcover)
  simpa only [assignmentPrimeTuple_unit] using congrFun h ()

theorem sum_unit_assignments_eq_sum_Icc [DecidableEq α] {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (B : ℕ) (F : ℕ → ℝ)
    (hF : ∀ n, F n ≠ 0 → Squarefree n ∧ n ≤ B ∧
      ∀ l : ℕ, l.Prime → l ∣ n → ∃ q, p q = l) :
    (∑ a : α → Option Unit, F (assignmentPrimeProduct p a)) =
      ∑ n ∈ Finset.Icc 0 B, F n := by
  classical
  let f := fun n : Fin (B + 1) => F n.val
  let G := fun a : α → Option Unit => F (assignmentPrimeProduct p a)
  have hrecover (n : ℕ) (hn : F n ≠ 0) :
      assignmentPrimeProduct p (assignmentOfTuple p (fun _ : Unit => n)) = n :=
    assignmentPrimeProduct_assignmentOfUnit hp hinj (hF n hn).1 (hF n hn).2.2
  have hsum : (∑ n, f n) = ∑ a, G a := by
    apply Finset.sum_bij_ne_zero
      (fun n _hn _hzero => assignmentOfTuple p (fun _ : Unit => n.val))
    · intro n _hn _hzero
      exact Finset.mem_univ _
    · intro n₁ _hn₁ hz₁ n₂ _hn₂ hz₂ heq
      apply Fin.ext
      rw [← hrecover n₁.val hz₁, ← hrecover n₂.val hz₂, heq]
    · intro a _ha hGa
      have hle := (hF (assignmentPrimeProduct p a) hGa).2.1
      let n : Fin (B + 1) := ⟨assignmentPrimeProduct p a, by omega⟩
      refine ⟨n, Finset.mem_univ n, hGa, ?_⟩
      apply assignmentPrimeProduct_unit_injective hp hinj
      exact hrecover n.val hGa
    · intro n _hn hz
      dsimp only [f, G]
      rw [hrecover n.val hz]
  rw [← hsum]
  simp only [f, Fin.sum_univ_eq_sum_range, Nat.range_succ_eq_Icc_zero]

theorem sum_unit_assignments_rough_eq_sum_Icc {M M' N B : ℕ}
    (hMM' : M ∣ M') (hBN : B ≤ N) (g F : ℕ → ℝ)
    (hF : ∀ n, 0 < n → B ≤ n → F n = 0) :
    (∑ a : commonPrimeUniverse M N → Option Unit,
      F (assignmentPrimeProduct (fun q => q.val) a) *
        roughSieveWeight M' g (assignmentPrimeProduct (fun q => q.val) a)) =
      ∑ n ∈ Finset.Icc 0 B, F n * roughSieveWeight M' g n := by
  apply sum_unit_assignments_eq_sum_Icc commonPrimeUniverse_prime Subtype.val_injective B
    (fun n => F n * roughSieveWeight M' g n)
  intro n hn
  have hs := roughSieveWeight_support (mul_ne_zero_iff.mp hn).2
  have hnB : n < B := by
    by_contra hh
    exact (mul_ne_zero_iff.mp hn).1 (hF n (Nat.pos_of_ne_zero hs.1.ne_zero) (by omega))
  refine ⟨hs.1, hnB.le, ?_⟩
  intro l hl hln
  have hlN := (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.1.ne_zero) hln).trans
    (hnB.le.trans hBN)
  have hlM : ¬l ∣ M := fun hlM => hl.ne_one
    (Nat.eq_one_of_dvd_coprimes hs.2 (hlM.trans hMM') hln)
  exact ⟨⟨l, mem_commonPrimeUniverse.mpr ⟨hl, hlN, hlM⟩⟩, rfl⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_unit_assignments_eq_sum_Icc
#print axioms Erdos4b.FGKMT.sum_unit_assignments_rough_eq_sum_Icc
