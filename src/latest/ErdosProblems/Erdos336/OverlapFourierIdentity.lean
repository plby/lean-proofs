import ErdosProblems.Erdos336.FiniteFourier
import ErdosProblems.Erdos336.OverlapEnergy

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise BigOperators ComplexConjugate

variable {N : ℕ} [NeZero N]

noncomputable def orderedDifferenceFiber
    (A : Finset (ZMod N)) (x : ZMod N) : Finset (ZMod N × ZMod N) :=
  (A ×ˢ A).filter fun p => p.1 - p.2 = x

lemma card_differenceOverlap_eq_card_orderedDifferenceFiber
    (A : Finset (ZMod N)) (x : ZMod N) :
    (differenceOverlap A x).card = (orderedDifferenceFiber A x).card := by
  apply Finset.card_bij (fun y _ => (y, y - x))
  · intro y hy
    obtain ⟨hyA, hyU⟩ := Finset.mem_inter.mp hy
    obtain ⟨a, ha, hay⟩ := Finset.mem_vadd_finset.mp hyU
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hyA, ?_⟩, by ring⟩
    simp only [vadd_eq_add] at hay
    have : y - x = a := by rw [← hay]; abel
    simpa [this] using ha
  · intro y₁ hy₁ y₂ hy₂ heq
    exact congrArg Prod.fst heq
  · intro p hp
    obtain ⟨hpProd, hpDiff⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpProd
    refine ⟨p.1, ?_, ?_⟩
    · apply Finset.mem_inter.mpr
      refine ⟨hp1, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨p.2, hp2, ?_⟩
      simp only [vadd_eq_add]
      have : p.1 = x + p.2 := by
        calc
          p.1 = (p.1 - p.2) + p.2 := by abel
          _ = x + p.2 := by rw [hpDiff]
      exact this.symm
    · apply Prod.ext
      · rfl
      · dsimp
        rw [← hpDiff]
        ring

lemma sum_card_fiber_mul_card_fiber_eq_card_equal
    {α β γ : Type*} [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : Finset α) (Q : Finset β) (f : α → γ) (g : β → γ) :
    ∑ x : γ, (P.filter fun p => f p = x).card *
        (Q.filter fun q => g q = x).card =
      ((P ×ˢ Q).filter fun pq => f pq.1 = g pq.2).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_mul_sum]
  simp_rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  simp
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  ext q
  simp [eq_comm]

noncomputable def equalDifferenceQuadruples
    (A S : Finset (ZMod N)) : Finset ((ZMod N × ZMod N) × (ZMod N × ZMod N)) :=
  ((A ×ˢ A) ×ˢ (S ×ˢ S)).filter fun p =>
    p.1.1 - p.1.2 = p.2.1 - p.2.2

/-- The overlap correlation counts pairs of ordered differences with the same
value. -/
theorem overlap_correlation_eq_card_equalDifferenceQuadruples
    (A S : Finset (ZMod N)) :
    ∑ x : ZMod N, (differenceOverlap A x).card *
        (differenceOverlap S x).card =
      (equalDifferenceQuadruples A S).card := by
  simp_rw [card_differenceOverlap_eq_card_orderedDifferenceFiber]
  exact sum_card_fiber_mul_card_fiber_eq_card_equal
    (A ×ˢ A) (S ×ˢ S) (fun p => p.1 - p.2) (fun p => p.1 - p.2)

lemma cyclicFourier_mul_conj_eq_sum_difference
    (A : Finset (ZMod N)) (k : ZMod N) :
    cyclicFinsetFourier A k * conj (cyclicFinsetFourier A k) =
      ∑ p ∈ A ×ˢ A, ZMod.stdAddChar ((p.2 - p.1) * k) := by
  classical
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp only [cyclicFinsetFourier, map_sum, Finset.sum_mul_sum]
  simp_rw [hconj]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

lemma conj_mul_cyclicFourier_eq_sum_difference
    (A : Finset (ZMod N)) (k : ZMod N) :
    conj (cyclicFinsetFourier A k) * cyclicFinsetFourier A k =
      ∑ p ∈ A ×ˢ A, ZMod.stdAddChar ((p.1 - p.2) * k) := by
  classical
  have hconj (y : ZMod N) :
      conj (ZMod.stdAddChar (-y)) = ZMod.stdAddChar y := by
    rw [AddChar.map_neg_eq_conj, Complex.conj_conj]
  simp only [cyclicFinsetFourier, map_sum, Finset.sum_mul_sum]
  simp_rw [hconj]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

lemma product_difference_character_sums
    (A S : Finset (ZMod N)) (k : ZMod N) :
    (∑ p ∈ A ×ˢ A, ZMod.stdAddChar ((p.2 - p.1) * k)) *
      (∑ q ∈ S ×ˢ S, ZMod.stdAddChar ((q.1 - q.2) * k)) =
    ∑ r ∈ (A ×ˢ A) ×ˢ (S ×ˢ S),
      ZMod.stdAddChar ((r.1.2 - r.1.1 + (r.2.1 - r.2.2)) * k) := by
  rw [Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Exact Fourier identity for the `A`/`S` overlap correlation. -/
theorem sum_fourier_overlap_identity_complex
    (A S : Finset (ZMod N)) :
    (∑ k : ZMod N,
      (cyclicFinsetFourier A k * conj (cyclicFinsetFourier A k)) *
      (conj (cyclicFinsetFourier S k) * cyclicFinsetFourier S k)) =
      (N : ℂ) * (equalDifferenceQuadruples A S).card := by
  simp_rw [cyclicFourier_mul_conj_eq_sum_difference,
    conj_mul_cyclicFourier_eq_sum_difference,
    product_difference_character_sums]
  rw [Finset.sum_comm]
  simp_rw [cyclic_character_orthogonality]
  have hziff (r : (ZMod N × ZMod N) × (ZMod N × ZMod N)) :
      r.1.2 - r.1.1 + (r.2.1 - r.2.2) = 0 ↔
        r.1.1 - r.1.2 = r.2.1 - r.2.2 := by
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h
  simp_rw [hziff]
  change (∑ r ∈ (A ×ˢ A) ×ˢ (S ×ˢ S),
      if r.1.1 - r.1.2 = r.2.1 - r.2.2 then (N : ℂ) else 0) =
    (N : ℂ) * (((A ×ˢ A) ×ˢ (S ×ˢ S)).filter fun r =>
      r.1.1 - r.1.2 = r.2.1 - r.2.2).card
  rw [← Finset.sum_filter]
  simp [mul_comm]

/-- Real norm-square form of the exact overlap Fourier identity. -/
theorem sum_normSq_fourier_eq_overlap_correlation
    (A S : Finset (ZMod N)) :
    (∑ k : ZMod N, ‖cyclicFinsetFourier A k‖ ^ 2 *
      ‖cyclicFinsetFourier S k‖ ^ 2) =
      (N : ℝ) * (∑ x : ZMod N,
        (differenceOverlap A x).card * (differenceOverlap S x).card) := by
  have hc := sum_fourier_overlap_identity_complex A S
  have hr := congrArg Complex.re hc
  rw [Complex.re_sum] at hr
  have hterm (z w : ℂ) :
      ((z * conj z) * (conj w * w)).re = ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
    rw [show conj w * w = w * conj w by ring,
      Complex.mul_conj, Complex.mul_conj, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_eq_norm_sq]
  simp_rw [hterm] at hr
  rw [← overlap_correlation_eq_card_equalDifferenceQuadruples] at hr
  norm_num at hr ⊢
  exact hr

end Erdos336
