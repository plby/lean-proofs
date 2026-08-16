import Wikipedia.SzemeredisTheorem.Finite.Mean

/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)

/-- Split the normalized mean over an `(n + 1)`-tuple into the head
coordinate and the remaining `n` coordinates. -/
theorem mean_fin_cons
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G => F (Fin.cons a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.cons p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.consEquiv (fun _ : Fin (n + 1) => G)).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.cons a y)) :=
      mean_prod_type
        (fun a : G => fun y : Fin n → G => F (Fin.cons a y))

/-- A product of normalized means is the normalized mean over an independent
choice of one input for every factor. -/
theorem prod_mean
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β]
    (F : ι → β → ℝ) :
    (∏ i, mean (F i)) =
      mean (fun y : ι → β => ∏ i, F i (y i)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

end Wikipedia.SzemeredisTheorem
