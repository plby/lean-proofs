import ErdosProblems.Erdos587.CongruenceBasis

/-! Exact image and primitive steps of a congruence-lattice basis. -/

namespace Erdos587

lemma latticeLinear_combination (u v m n : ℤ) (p q : ℤ × ℤ) :
    latticeLinear u v (latticeCombination m n p q) =
      m * latticeLinear u v p + n * latticeLinear u v q := by
  unfold latticeLinear latticeCombination
  ring

lemma latticeLinear_add (u v : ℤ) (p q : ℤ × ℤ) :
    latticeLinear u v (p + q) = latticeLinear u v p + latticeLinear u v q := by
  simp only [latticeLinear, Prod.fst_add, Prod.snd_add]
  ring

lemma latticeLinear_sub (u v : ℤ) (p q : ℤ × ℤ) :
    latticeLinear u v (p - q) = latticeLinear u v p - latticeLinear u v q := by
  simp only [latticeLinear, Prod.fst_sub, Prod.snd_sub]
  ring

theorem IsCongruenceBasis.image_isCoprime {g u v : ℤ} {p q : ℤ × ℤ}
    (hbasis : IsCongruenceBasis g u v p q) (hg : g ≠ 0) (huv : IsCoprime u v) :
    IsCoprime (latticeLinear u v p / g) (latticeLinear u v q / g) := by
  obtain ⟨a, b, hab⟩ := huv
  have hz : latticeLinear u v (g * a, g * b) = g := by
    simp only [latticeLinear]
    linear_combination g * hab
  obtain ⟨m, n, hrepr⟩ := (hbasis.2 (g * a, g * b)).mp (by rw [hz])
  have himage : g = m * latticeLinear u v p + n * latticeLinear u v q := by
    rw [← hz, hrepr, latticeLinear_combination]
  have hpdiv : g * (latticeLinear u v p / g) = latticeLinear u v p :=
    Int.mul_ediv_cancel' hbasis.first_mem
  have hqdiv : g * (latticeLinear u v q / g) = latticeLinear u v q :=
    Int.mul_ediv_cancel' hbasis.second_mem
  refine ⟨m, n, ?_⟩
  apply (mul_left_cancel₀ hg)
  calc
    g * (m * (latticeLinear u v p / g) + n * (latticeLinear u v q / g)) =
        m * (g * (latticeLinear u v p / g)) + n * (g * (latticeLinear u v q / g)) := by ring
    _ = m * latticeLinear u v p + n * latticeLinear u v q := by rw [hpdiv, hqdiv]
    _ = g * 1 := by simpa only [mul_one] using himage.symm

theorem IsCongruenceBasis.image_natAbs_coprime {g u v : ℤ} {p q : ℤ × ℤ}
    (hbasis : IsCongruenceBasis g u v p q) (hg : g ≠ 0) (huv : IsCoprime u v) :
    (latticeLinear u v p / g).natAbs.Coprime (latticeLinear u v q / g).natAbs := by
  exact Int.isCoprime_iff_gcd_eq_one.mp (hbasis.image_isCoprime hg huv)

theorem exists_congruence_coset_point {u v : ℤ} (huv : IsCoprime u v) (t g : ℤ) :
    ∃ z : ℤ × ℤ, g ∣ t + latticeLinear u v z := by
  obtain ⟨a, b, hab⟩ := huv
  refine ⟨(-t * a, -t * b), ?_⟩
  have hh : t + latticeLinear u v (-t * a, -t * b) = 0 := by
    simp only [latticeLinear]
    linear_combination -t * hab
  rw [hh]
  exact dvd_zero g

lemma congruence_coset_add_basis {g u v t : ℤ} {p q z : ℤ × ℤ}
    (hbasis : IsCongruenceBasis g u v p q) (hz : g ∣ t + latticeLinear u v z)
    (m n : ℤ) : g ∣ t + latticeLinear u v (z + latticeCombination m n p q) := by
  rw [latticeLinear_add, ← add_assoc]
  apply dvd_add hz
  exact (hbasis.2 _).mpr ⟨m, n, rfl⟩

end Erdos587
