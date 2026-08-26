import ErdosProblems.Erdos336.EnergyNegation

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise Combinatorics.Additive

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def differenceOverlap (A : Finset G) (x : G) : Finset G :=
  A ∩ (x +ᵥ A)

noncomputable def differenceRepFiber (A : Finset G) (x : G) : Finset (G × G) :=
  (A ×ˢ (-A)).filter fun p => p.1 + p.2 = x

/-- The overlap `A∩(x+A)` is in bijection with representations of `x` as an
element of `A+(-A)`. -/
theorem card_differenceOverlap_eq_card_differenceRepFiber
    (A : Finset G) (x : G) :
    (differenceOverlap A x).card = (differenceRepFiber A x).card := by
  apply Finset.card_bij (fun y _ => (y, x - y))
  · intro y hy
    obtain ⟨hyA, hyU⟩ := Finset.mem_inter.mp hy
    obtain ⟨a, ha, hay⟩ := Finset.mem_vadd_finset.mp hyU
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hyA, ?_⟩, ?_⟩
    · simp only [Finset.mem_neg]
      refine ⟨a, ha, ?_⟩
      simp only [vadd_eq_add] at hay
      rw [← hay]
      abel
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro y₁ hy₁ y₂ hy₂ heq
    exact congrArg Prod.fst heq
  · intro p hp
    obtain ⟨hpProd, hpSum⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpNeg⟩ := Finset.mem_product.mp hpProd
    simp only [Finset.mem_neg] at hpNeg
    obtain ⟨a, ha, hpa⟩ := hpNeg
    refine ⟨p.1, ?_, ?_⟩
    · apply Finset.mem_inter.mpr
      refine ⟨hpA, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨a, ha, ?_⟩
      simp only [vadd_eq_add]
      rw [← hpa] at hpSum
      have : p.1 = x + a := by
        calc
          p.1 = (p.1 + -a) + a := by abel
          _ = x + a := by rw [hpSum]
      exact this.symm
    · apply Prod.ext
      · rfl
      · dsimp
        calc
          x - p.1 = p.2 := by
            rw [← hpSum]
            abel

/-- The squared overlap multiplicities sum to additive energy. -/
theorem sum_card_differenceOverlap_sq_eq_addEnergy (A : Finset G) :
    ∑ x : G, (differenceOverlap A x).card ^ 2 = A.addEnergy A := by
  calc
    ∑ x : G, (differenceOverlap A x).card ^ 2 =
        ∑ x : G, (differenceRepFiber A x).card ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [card_differenceOverlap_eq_card_differenceRepFiber]
    _ = A.addEnergy (-A) := by
      rw [Finset.addEnergy_eq_sum_sq]
      apply Finset.sum_congr rfl
      intro x hx
      rfl
    _ = A.addEnergy A := addEnergy_neg_right A

/-- The total overlap multiplicity is `|A|²`. -/
theorem sum_card_differenceOverlap (A : Finset G) :
    ∑ x : G, (differenceOverlap A x).card = A.card ^ 2 := by
  calc
    ∑ x : G, (differenceOverlap A x).card =
        ∑ x : G, (differenceRepFiber A x).card := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [card_differenceOverlap_eq_card_differenceRepFiber]
    _ = (A ×ˢ (-A)).card := by
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      simp
    _ = A.card ^ 2 := by simp [pow_two]

noncomputable def overlapSigma (A : Finset G) : ℕ :=
  ∑ x : G, (differenceOverlap A x).card *
    (A + differenceOverlap A x).card

/-- Katz--Koester: adding `A` to an `x`-overlap stays inside the corresponding
`x`-overlap of `2A`. -/
theorem differenceOverlap_add_subset_double_overlap
    (A : Finset G) (x : G) :
    differenceOverlap A x + A ⊆ differenceOverlap (A + A) x := by
  intro z hz
  obtain ⟨y, hy, a, ha, hya⟩ := Finset.mem_add.mp hz
  obtain ⟨hyA, hyShift⟩ := Finset.mem_inter.mp hy
  obtain ⟨b, hb, hxb⟩ := Finset.mem_vadd_finset.mp hyShift
  apply Finset.mem_inter.mpr
  constructor
  · exact Finset.mem_add.mpr ⟨y, hyA, a, ha, hya⟩
  · apply Finset.mem_vadd_finset.mpr
    refine ⟨b + a, Finset.mem_add.mpr ⟨b, hb, a, ha, rfl⟩, ?_⟩
    simp only [vadd_eq_add] at hxb ⊢
    rw [← hya, ← hxb]
    abel

/-- The weighted overlap sigma is bounded by the overlap correlation of `A`
and `2A`. -/
theorem overlapSigma_le_overlap_correlation (A : Finset G) :
    overlapSigma A ≤ ∑ x : G,
      (differenceOverlap A x).card *
        (differenceOverlap (A + A) x).card := by
  unfold overlapSigma
  apply Finset.sum_le_sum
  intro x hx
  have hsub : A + differenceOverlap A x ⊆
      differenceOverlap (A + A) x := by
    simpa [add_comm] using differenceOverlap_add_subset_double_overlap A x
  exact Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

/-- Almost expansion of every nonempty subset of `A` gives the weighted
Katz--Koester lower bound, with only an `|A|²` error. -/
theorem card_cube_add_addEnergy_le_overlapSigma_add_sq
    (A : Finset G)
    (hexpand : ∀ B : Finset G, B.Nonempty → B ⊆ A →
      A.card + B.card ≤ (A + B).card + 1) :
    A.card ^ 3 + A.addEnergy A ≤ overlapSigma A + A.card ^ 2 := by
  have hpoint (x : G) :
      A.card * (differenceOverlap A x).card +
          (differenceOverlap A x).card ^ 2 ≤
        (differenceOverlap A x).card *
            (A + differenceOverlap A x).card +
          (differenceOverlap A x).card := by
    by_cases hr : (differenceOverlap A x).card = 0
    · simp [hr]
    · have hne : (differenceOverlap A x).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hr)
      have he := hexpand (differenceOverlap A x) hne Finset.inter_subset_left
      have hm := Nat.mul_le_mul_left (differenceOverlap A x).card he
      nlinarith
  have hsum := Finset.sum_le_sum fun x (_hx : x ∈ (Finset.univ : Finset G)) => hpoint x
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.mul_sum] at hsum
  rw [sum_card_differenceOverlap,
    sum_card_differenceOverlap_sq_eq_addEnergy] at hsum
  change A.card ^ 3 + A.addEnergy A ≤ overlapSigma A + A.card ^ 2
  simpa [overlapSigma, pow_succ, mul_assoc] using hsum

/-- Cauchy--Schwarz gives the standard energy lower bound. -/
theorem card_four_le_card_double_mul_addEnergy (A : Finset G) :
    A.card ^ 4 ≤ (A + A).card * A.addEnergy A := by
  simpa [pow_two, pow_succ, mul_assoc] using
    (Finset.le_card_add_mul_addEnergy A A)

end Erdos336
