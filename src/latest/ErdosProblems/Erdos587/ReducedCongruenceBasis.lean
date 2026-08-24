import ErdosProblems.Erdos587.CongruenceBasis
import ErdosProblems.Erdos587.LatticeQuadratic

/-! A reduced plane-lattice basis obtained by minimizing an integral energy. -/

namespace Erdos587

theorem exists_minimal_congruence_basis (g u v H J : ℕ) (huv : u.Coprime v) :
    ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q ∧
      ∀ r s : ℤ × ℤ, IsCongruenceBasis g u v r s →
        latticeSizeSq H J p + latticeSizeSq H J q ≤ latticeSizeSq H J r + latticeSizeSq H J s := by
  classical
  obtain ⟨p₀, q₀, h₀⟩ := exists_congruence_basis (g := g) huv
  have hex : ∃ n : ℕ, ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q ∧
      latticeSizeSq H J p + latticeSizeSq H J q = n :=
    ⟨_, p₀, q₀, h₀, rfl⟩
  obtain ⟨p, q, hpq, heq⟩ := Nat.find_spec hex
  refine ⟨p, q, hpq, ?_⟩
  intro r s hrs
  rw [heq]
  exact Nat.find_min' hex ⟨r, s, hrs, rfl⟩

theorem exists_ordered_minimal_congruence_basis (g u v H J : ℕ) (huv : u.Coprime v) :
    ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q ∧
      latticeSizeSq H J p ≤ latticeSizeSq H J q ∧
      ∀ r s : ℤ × ℤ, IsCongruenceBasis g u v r s →
        latticeSizeSq H J p + latticeSizeSq H J q ≤ latticeSizeSq H J r + latticeSizeSq H J s := by
  obtain ⟨p, q, hpq, hmin⟩ := exists_minimal_congruence_basis g u v H J huv
  by_cases hpqsize : latticeSizeSq H J p ≤ latticeSizeSq H J q
  · exact ⟨p, q, hpq, hpqsize, hmin⟩
  · refine ⟨q, p, hpq.swap, (lt_of_not_ge hpqsize).le, ?_⟩
    intro r s hrs
    simpa only [Nat.add_comm (latticeSizeSq H J p) (latticeSizeSq H J q)] using hmin r s hrs

lemma latticeScaledSq_shift (H J : ℝ) (p q : ℤ × ℤ) (k : ℤ) :
    latticeScaledSq H J (latticeShift p q k) = latticeScaledSq H J q +
      2 * (k : ℝ) * latticeScaledInner H J p q + (k : ℝ) ^ 2 * latticeScaledSq H J p := by
  simp only [latticeScaledSq, latticeScaledInner, latticeShift, Int.cast_add, Int.cast_mul]
  ring

lemma latticeScaledSq_le_of_sizeSq_le {H J : ℕ} (hH : 0 < H) (hJ : 0 < J)
    {p q : ℤ × ℤ} (h : latticeSizeSq H J p ≤ latticeSizeSq H J q) :
    latticeScaledSq H J p ≤ latticeScaledSq H J q := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hh : (latticeSizeSq H J p : ℝ) ≤ latticeSizeSq H J q := by exact_mod_cast h
  rw [latticeSizeSq_scaled hH hJ, latticeSizeSq_scaled hH hJ] at hh
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (H : ℝ) ^ 2 * (J : ℝ) ^ 2)).mp hh

theorem exists_reduced_congruence_basis {g u v H J : ℕ}
    (huv : u.Coprime v) (hH : 0 < H) (hJ : 0 < J) :
    ∃ p q : ℤ × ℤ, IsCongruenceBasis g u v p q ∧
      latticeScaledSq H J p ≤ latticeScaledSq H J q ∧
      |latticeScaledInner H J p q| ≤ latticeScaledSq H J p / 2 := by
  obtain ⟨p, q, hpq, horder, hmin⟩ := exists_ordered_minimal_congruence_basis g u v H J huv
  have hshift (k : ℤ) : latticeScaledSq H J q ≤ latticeScaledSq H J (latticeShift p q k) := by
    apply latticeScaledSq_le_of_sizeSq_le hH hJ
    have hh := hmin p (latticeShift p q k) (hpq.shift k)
    omega
  have hplus := hshift 1
  have hminus := hshift (-1)
  rw [latticeScaledSq_shift] at hplus hminus
  norm_num at hplus hminus
  refine ⟨p, q, hpq, latticeScaledSq_le_of_sizeSq_le hH hJ horder, ?_⟩
  rw [abs_le]
  constructor <;> linarith

end Erdos587
