import ErdosProblems.Erdos421.FiniteCoefficients

/-! # Reindexing finite convolution sums over products -/

namespace Erdos421

def convolutionPairs (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p ↦ p.1 * p.2 ≤ X)

theorem divisorsAntidiagonal_pairwise_disjoint (X : ℕ) :
    (↑(Finset.Icc 1 X) : Set ℕ).PairwiseDisjoint Nat.divisorsAntidiagonal := by
  intro n _ m _ hnm
  apply Finset.disjoint_left.mpr
  intro p hp hn
  exact hnm ((Nat.mem_divisorsAntidiagonal.mp hp).1.symm.trans
    (Nat.mem_divisorsAntidiagonal.mp hn).1)

theorem convolutionPairs_eq_biUnion (X : ℕ) :
    convolutionPairs X = (Finset.Icc 1 X).biUnion Nat.divisorsAntidiagonal := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hpX⟩ := Finset.mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hp
    have hprod : 0 < p.1 * p.2 :=
      Nat.mul_pos (Finset.mem_Icc.mp h₁).1 (Finset.mem_Icc.mp h₂).1
    exact Finset.mem_biUnion.mpr ⟨p.1 * p.2, Finset.mem_Icc.mpr ⟨hprod, hpX⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt hprod⟩⟩
  · intro hp
    obtain ⟨n, hn, hpn⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hnpos, hnX⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hpn
    have hp₁ := Nat.fst_mem_divisors_of_mem_antidiagonal hpn
    have hp₂ := Nat.snd_mem_divisors_of_mem_antidiagonal hpn
    have hp0 := Nat.ne_zero_of_mem_divisorsAntidiagonal hpn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hprod ▸ hnX⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hp0.1,
        (Nat.le_of_dvd hnpos (Nat.mem_divisors.mp hp₁).1).trans hnX⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hp0.2,
        (Nat.le_of_dvd hnpos (Nat.mem_divisors.mp hp₂).1).trans hnX⟩

theorem sum_convolution_weighted_prefix {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (w : ℕ → R) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f * g) n * w n) =
      ∑ p ∈ convolutionPairs X, f p.1 * g p.2 * w (p.1 * p.2) := by
  rw [convolutionPairs_eq_biUnion, Finset.sum_biUnion (divisorsAntidiagonal_pairwise_disjoint X)]
  apply Finset.sum_congr rfl
  intro n _
  rw [ArithmeticFunction.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]

theorem sum_convolutionPairs_eq_hyperbola {R : Type*} [AddCommMonoid R]
    (F : ℕ × ℕ → R) (X : ℕ) :
    (∑ p ∈ convolutionPairs X, F p) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), F (a, b) := by
  unfold convolutionPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  have hapos : 0 < a := (Finset.mem_Icc.mp ha).1
  have hfilter : (Finset.Icc 1 X).filter (fun b ↦ a * b ≤ X) = Finset.Icc 1 (X / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb, _⟩, hab⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le hapos).mpr (by simpa only [Nat.mul_comm] using hab)⟩
    · rintro ⟨hb, hbdiv⟩
      refine ⟨⟨hb, hbdiv.trans (Nat.div_le_self X a)⟩, ?_⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hapos).mp hbdiv
  rw [← hfilter, Finset.sum_filter]

theorem sum_convolution_hyperbola {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (w : ℕ → R) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f * g) n * w n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f a * g b * w (a * b) := by
  rw [sum_convolution_weighted_prefix, sum_convolutionPairs_eq_hyperbola]

end Erdos421
