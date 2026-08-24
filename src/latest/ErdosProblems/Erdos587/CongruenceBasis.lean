import ErdosProblems.Erdos587.PrimitiveParameters

/-! Explicit integral bases of a two-dimensional congruence lattice. -/

namespace Erdos587

def latticeDet (p q : ℤ × ℤ) : ℤ := p.1 * q.2 - p.2 * q.1

def latticeLinear (u v : ℤ) (p : ℤ × ℤ) : ℤ := u * p.1 + v * p.2

def latticeCombination (m n : ℤ) (p q : ℤ × ℤ) : ℤ × ℤ :=
  (m * p.1 + n * q.1, m * p.2 + n * q.2)

def latticeShift (p q : ℤ × ℤ) (k : ℤ) : ℤ × ℤ :=
  (q.1 + k * p.1, q.2 + k * p.2)

/-- Both the determinant and the exact integral span are retained. -/
def IsCongruenceBasis (g u v : ℤ) (p q : ℤ × ℤ) : Prop :=
  |latticeDet p q| = g ∧
    ∀ z : ℤ × ℤ, g ∣ latticeLinear u v z ↔
      ∃ m n : ℤ, z = latticeCombination m n p q

lemma latticeDet_swap (p q : ℤ × ℤ) : latticeDet q p = -latticeDet p q := by
  unfold latticeDet
  ring

lemma latticeDet_shift (p q : ℤ × ℤ) (k : ℤ) :
    latticeDet p (latticeShift p q k) = latticeDet p q := by
  simp only [latticeDet, latticeShift]
  ring

theorem IsCongruenceBasis.swap {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) : IsCongruenceBasis g u v q p := by
  refine ⟨by rw [latticeDet_swap, abs_neg]; exact h.1, ?_⟩
  intro z
  rw [h.2 z]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨n, m, ?_⟩
    ext <;> simp only [latticeCombination] <;> ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨n, m, ?_⟩
    ext <;> simp only [latticeCombination] <;> ring

theorem IsCongruenceBasis.shift {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) (k : ℤ) :
    IsCongruenceBasis g u v p (latticeShift p q k) := by
  refine ⟨by rw [latticeDet_shift]; exact h.1, ?_⟩
  intro z
  rw [h.2 z]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m - k * n, n, ?_⟩
    ext <;> simp only [latticeCombination, latticeShift] <;> ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨m + k * n, n, ?_⟩
    ext <;> simp only [latticeCombination, latticeShift] <;> ring

lemma IsCongruenceBasis.first_mem {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) : g ∣ latticeLinear u v p := by
  apply (h.2 p).mpr
  exact ⟨1, 0, by simp [latticeCombination]⟩

lemma IsCongruenceBasis.second_mem {g u v : ℤ} {p q : ℤ × ℤ}
    (h : IsCongruenceBasis g u v p q) : g ∣ latticeLinear u v q := h.swap.first_mem

theorem exists_congruence_basis_of_bezout {g u v a b : ℤ}
    (hg : 0 ≤ g) (hab : u * a + v * b = 1) :
    ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q := by
  refine ⟨(g * a, g * b), (-v, u), ?_, ?_⟩
  · have hdet : latticeDet (g * a, g * b) (-v, u) = g := by
      simp only [latticeDet]
      linear_combination g * hab
    rw [hdet, abs_of_nonneg hg]
  · intro z
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨m, a * z.2 - b * z.1, ?_⟩
      change u * z.1 + v * z.2 = g * m at hm
      ext <;> simp only [latticeCombination]
      · linear_combination a * hm - z.1 * hab
      · linear_combination b * hm - z.2 * hab
    · rintro ⟨m, n, rfl⟩
      refine ⟨m, ?_⟩
      simp only [latticeLinear, latticeCombination]
      linear_combination (g * m) * hab

theorem exists_congruence_basis {g u v : ℕ} (huv : u.Coprime v) :
    ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q := by
  have hab : (u : ℤ) * u.gcdA v + (v : ℤ) * u.gcdB v = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, huv.gcd_eq_one]
    rfl
  exact exists_congruence_basis_of_bezout (Int.natCast_nonneg g) hab

end Erdos587
