/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRawCrtKernel

/-!
# The raw Fourier divisor box as a literal four-tuple sum

An explicit equivalence joins the four divisor tuples in the original
CRT kernel. The finite prime cutoff is unchanged by this reindexing.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def fourDivisorPackEquiv (ι : Type*) :
    ((ι → ℕ) × (ι → ℕ) × (ι → ℕ) × (ι → ℕ)) ≃ ((ι ⊕ ι) → Bool → ℕ) where
  toFun x i b := match i, b with
    | .inl j, false => x.1 j
    | .inr j, false => x.2.1 j
    | .inl j, true => x.2.2.1 j
    | .inr j, true => x.2.2.2 j
  invFun d := (fun i ↦ d (.inl i) false, fun i ↦ d (.inr i) false,
    fun i ↦ d (.inl i) true, fun i ↦ d (.inr i) true)
  left_inv x := rfl
  right_inv d := by
    funext i b
    cases i <;> cases b <;> rfl

def cutoffDivisorTupleSupport (ι : Type*) [Fintype ι] (P : Finset ℕ) : Finset (ι → ℕ) := by
  classical
  exact Fintype.piFinset fun _ : ι ↦ (∏ p ∈ P, p).divisors

theorem mem_cutoffDivisorTupleSupport {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (d : ι → ℕ) :
    d ∈ cutoffDivisorTupleSupport ι P ↔ ∀ i, d i ∣ ∏ p ∈ P, p := by
  classical
  simp [cutoffDivisorTupleSupport, Fintype.mem_piFinset, Nat.mem_divisors,
    (primeFinsetProduct_pos P hP).ne']

theorem mem_rawDoubledCutoffDivisorTuples_pack
    {ι : Type*} [Fintype ι] (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : (ι → ℕ) × (ι → ℕ) × (ι → ℕ) × (ι → ℕ)) :
    fourDivisorPackEquiv ι x ∈ rawDoubledCutoffDivisorTuples ι P ↔
      x ∈ (cutoffDivisorTupleSupport ι P) ×ˢ ((cutoffDivisorTupleSupport ι P) ×ˢ
        ((cutoffDivisorTupleSupport ι P) ×ˢ (cutoffDivisorTupleSupport ι P))) := by
  rw [mem_rawDoubledCutoffDivisorTuples P hP]
  simp only [Finset.mem_product, mem_cutoffDivisorTupleSupport P hP]
  constructor
  · intro h
    exact ⟨fun i ↦ h (.inl i) false, fun i ↦ h (.inr i) false,
      fun i ↦ h (.inl i) true, fun i ↦ h (.inr i) true⟩
  · rintro ⟨hd, he, hd', he'⟩ i b
    cases i with
    | inl i =>
        cases b
        · exact hd i
        · exact hd' i
    | inr i =>
        cases b
        · exact he i
        · exact he' i

theorem sum_rawDoubledCutoffDivisorTuples
    {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ((ι ⊕ ι) → Bool → ℕ) → M) :
    (∑ d ∈ rawDoubledCutoffDivisorTuples ι P, f d) =
      ∑ d ∈ cutoffDivisorTupleSupport ι P, ∑ e ∈ cutoffDivisorTupleSupport ι P,
      ∑ d' ∈ cutoffDivisorTupleSupport ι P, ∑ e' ∈ cutoffDivisorTupleSupport ι P,
        f (fourDivisorPackEquiv ι (d, e, d', e')) := by
  classical
  have heq : rawDoubledCutoffDivisorTuples ι P =
      ((cutoffDivisorTupleSupport ι P) ×ˢ ((cutoffDivisorTupleSupport ι P) ×ˢ
        ((cutoffDivisorTupleSupport ι P) ×ˢ (cutoffDivisorTupleSupport ι P)))).image
          (fourDivisorPackEquiv ι) := by
    ext d
    constructor
    · intro hd
      refine Finset.mem_image.mpr ⟨(fourDivisorPackEquiv ι).symm d, ?_,
        (fourDivisorPackEquiv ι).apply_symm_apply d⟩
      exact (mem_rawDoubledCutoffDivisorTuples_pack P hP _).mp
        (by simpa only [Equiv.apply_symm_apply] using hd)
    · intro hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
      exact (mem_rawDoubledCutoffDivisorTuples_pack P hP x).mpr hx
  rw [heq, Finset.sum_image (fun a ha b hb hab ↦ (fourDivisorPackEquiv ι).injective hab)]
  simp only [Finset.sum_product]

theorem coprime_nat_lcm_iff (m a b : ℕ) :
    m.Coprime (Nat.lcm a b) ↔ m.Coprime a ∧ m.Coprime b := by
  constructor
  · intro h
    exact ⟨h.coprime_dvd_right (Nat.dvd_lcm_left _ _),
      h.coprime_dvd_right (Nat.dvd_lcm_right _ _)⟩
  · rintro ⟨ha, hb⟩
    exact (ha.mul_right hb).coprime_dvd_right (Nat.lcm_dvd_mul _ _)

def cutoffCompanionDivisorTupleSupport (ι : Type*) [Fintype ι] (P : Finset ℕ) (m : ℕ) :
    Finset (ι → ℕ) := by
  classical
  exact (cutoffDivisorTupleSupport ι P).filter (fun e ↦ ∀ i, m.Coprime (e i))

theorem rawAffineDivisorKernel_eq_coordinateLcmKernel
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m q : ℕ)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) :
    rawAffineDivisorKernel H P m q
        (fun d ↦ (lambda (fun i ↦ d (.inl i)) (fun i ↦ d (.inr i)) : ℂ))
        (fun d ↦ (lambda (fun i ↦ d (.inl i)) (fun i ↦ d (.inr i)) : ℂ)) =
      (doubledSelbergCoordinateLcmKernel H (cutoffDivisorTupleSupport H P)
        (cutoffCompanionDivisorTupleSupport H P m) lambda m q : ℂ) := by
  classical
  unfold rawAffineDivisorKernel doubledSelbergCoordinateLcmKernel
  rw [sum_rawDoubledCutoffDivisorTuples P hP]
  simp only [cutoffCompanionDivisorTupleSupport, Finset.sum_filter,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    apply_ite (Complex.ofReal), Complex.ofReal_zero]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hecop : ∀ i : H, m.Coprime (e i)
  · rw [if_pos hecop]
    apply Finset.sum_congr rfl
    intro d' hd'
    apply Finset.sum_congr rfl
    intro e' he'
    have hcop : (∀ i : H, m.Coprime (Nat.lcm (e i) (e' i))) ↔
        ∀ i : H, m.Coprime (e' i) := by
      constructor
      · exact fun h i ↦ ((coprime_nat_lcm_iff _ _ _).mp (h i)).2
      · exact fun h i ↦ (coprime_nat_lcm_iff _ _ _).mpr ⟨hecop i, h i⟩
    simp only [fourDivisorPackEquiv, Equiv.coe_fn_mk, hcop]
    split_ifs <;> simp_all
  · rw [if_neg hecop]
    apply Finset.sum_eq_zero
    intro d' hd'
    apply Finset.sum_eq_zero
    intro e' he'
    have hnot : ¬∀ i : H, m.Coprime (Nat.lcm (e i) (e' i)) := by
      intro h
      exact hecop fun i ↦ ((coprime_nat_lcm_iff _ _ _).mp (h i)).1
    simp only [fourDivisorPackEquiv, Equiv.coe_fn_mk, hnot, false_and, if_false]

end

end Erdos4b
