import ErdosProblems.Erdos587.LatticeBoxProjection
import ErdosProblems.Erdos587.LatticeBox

/-! The centered affine-lattice box gives a natural rectangle inside the original progression. -/

namespace Erdos587

def latticeBoxStep (g u v : ℕ) (p : ℤ × ℤ) : ℕ := (latticeLinear u v p / (g : ℤ)).natAbs

def latticeBoxNaturalBase (g u v t : ℕ) (p q z : ℤ × ℤ) (ell₁ ell₂ : ℕ) : ℕ :=
  (latticeBoxBase g u v t p q z ell₁ ell₂).toNat

lemma natural_coordinates_of_central_quarter {H J : ℕ} {w : ℤ × ℤ}
    (hw : ((w.1 : ℝ) ∈ Set.Icc ((H : ℝ) / 4) (3 * H / 4)) ∧
      ((w.2 : ℝ) ∈ Set.Icc ((J : ℝ) / 4) (3 * J / 4))) :
    w.1.toNat ≤ H ∧ w.2.toNat ≤ J ∧ (w.1.toNat : ℤ) = w.1 ∧ (w.2.toNat : ℤ) = w.2 := by
  have hx0 : (0 : ℤ) ≤ w.1 := by
    have hh : (0 : ℝ) ≤ w.1 := by linarith [Nat.cast_nonneg (α := ℝ) H, hw.1.1]
    exact_mod_cast hh
  have hy0 : (0 : ℤ) ≤ w.2 := by
    have hh : (0 : ℝ) ≤ w.2 := by linarith [Nat.cast_nonneg (α := ℝ) J, hw.2.1]
    exact_mod_cast hh
  have hxH : w.1 ≤ (H : ℤ) := by
    have hh : (w.1 : ℝ) ≤ H := by linarith [Nat.cast_nonneg (α := ℝ) H, hw.1.2]
    exact_mod_cast hh
  have hyJ : w.2 ≤ (J : ℤ) := by
    have hh : (w.2 : ℝ) ≤ J := by linarith [Nat.cast_nonneg (α := ℝ) J, hw.2.2]
    exact_mod_cast hh
  exact ⟨Int.toNat_le.mpr hxH, Int.toNat_le.mpr hyJ,
    Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0⟩

theorem latticeBoxBase_nonneg {g u v t H J : ℕ} {p q z : ℤ × ℤ} {ell₁ ell₂ : ℕ}
    (hg : 0 < g) (hbasis : IsCongruenceBasis g u v p q) (hz : (g : ℤ) ∣ t + latticeLinear u v z)
    (hbox : ∀ x ≤ 2 * ell₁, ∀ y ≤ 2 * ell₂,
      let w := positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y
      ((w.1 : ℝ) ∈ Set.Icc ((H : ℝ) / 4) (3 * H / 4)) ∧
        ((w.2 : ℝ) ∈ Set.Icc ((J : ℝ) / 4) (3 * J / 4))) :
    0 ≤ latticeBoxBase g u v t p q z ell₁ ell₂ := by
  let w := positiveLatticeBoxPoint g u v p q z ell₁ ell₂ 0 0
  obtain ⟨_, _, hwx, hwy⟩ := natural_coordinates_of_central_quarter (hbox 0 (by omega) 0 (by omega))
  have hx0 : 0 ≤ w.1 := by rw [← hwx]; exact Int.natCast_nonneg _
  have hy0 : 0 ≤ w.2 := by rw [← hwy]; exact Int.natCast_nonneg _
  have hi := lattice_box_image_identity hbasis hz ell₁ ell₂ 0 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hi
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hnonneg : (0 : ℤ) ≤ t + latticeLinear u v w := by
    unfold latticeLinear
    positivity
  change (g : ℤ) * latticeBoxBase g u v t p q z ell₁ ell₂ = t + latticeLinear u v w at hi
  nlinarith

theorem lattice_box_natural_image_identity {g u v t : ℕ} {p q z : ℤ × ℤ} {ell₁ ell₂ x y : ℕ}
    (hbasis : IsCongruenceBasis g u v p q) (hz : (g : ℤ) ∣ t + latticeLinear u v z)
    (hbase : 0 ≤ latticeBoxBase g u v t p q z ell₁ ell₂)
    (hwx : (((positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).1.toNat : ℕ) : ℤ) =
      (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).1)
    (hwy : (((positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).2.toNat : ℕ) : ℤ) =
      (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).2) :
    g ^ 2 * (latticeBoxNaturalBase g u v t p q z ell₁ ell₂ + latticeBoxStep g u v p * x +
      latticeBoxStep g u v q * y) =
      g * (t + u * (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).1.toNat +
        v * (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).2.toNat) := by
  have hi := lattice_box_image_identity hbasis hz ell₁ ell₂ x y
  have hbaseCast : (latticeBoxNaturalBase g u v t p q z ell₁ ell₂ : ℤ) =
      latticeBoxBase g u v t p q z ell₁ ell₂ := Int.toNat_of_nonneg hbase
  have hh : ((g ^ 2 * (latticeBoxNaturalBase g u v t p q z ell₁ ell₂ +
      latticeBoxStep g u v p * x + latticeBoxStep g u v q * y) : ℕ) : ℤ) =
      ((g * (t + u * (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).1.toNat +
        v * (positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y).2.toNat) : ℕ) : ℤ) := by
    push_cast
    rw [hbaseCast, hwx, hwy]
    simp only [latticeBoxStep, Int.natCast_natAbs]
    have hscaled := congrArg (fun a : ℤ => (g : ℤ) * a) hi
    simpa only [latticeLinear, pow_two, mul_assoc, add_assoc] using hscaled
  exact_mod_cast hh

theorem lattice_box_natural_image {g u v t H J : ℕ} {p q z : ℤ × ℤ} {ell₁ ell₂ : ℕ}
    (hg : 0 < g) (hbasis : IsCongruenceBasis g u v p q) (hz : (g : ℤ) ∣ t + latticeLinear u v z)
    (hbox : ∀ x ≤ 2 * ell₁, ∀ y ≤ 2 * ell₂,
      let w := positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y
      ((w.1 : ℝ) ∈ Set.Icc ((H : ℝ) / 4) (3 * H / 4)) ∧
        ((w.2 : ℝ) ∈ Set.Icc ((J : ℝ) / 4) (3 * J / 4))) :
    ∀ x ≤ 2 * ell₁, ∀ y ≤ 2 * ell₂,
      let w := positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y
      w.1.toNat ≤ H ∧ w.2.toNat ≤ J ∧
        g ^ 2 * (latticeBoxNaturalBase g u v t p q z ell₁ ell₂ +
          latticeBoxStep g u v p * x + latticeBoxStep g u v q * y) =
          g * (t + u * w.1.toNat + v * w.2.toNat) := by
  have hbase := latticeBoxBase_nonneg hg hbasis hz hbox
  intro x hx y hy
  obtain ⟨hX, hY, hwx, hwy⟩ := natural_coordinates_of_central_quarter (hbox x hx y hy)
  exact ⟨hX, hY, lattice_box_natural_image_identity hbasis hz hbase hwx hwy⟩

theorem lattice_box_natural_proper {g u v t H J : ℕ} {p q z : ℤ × ℤ} {ell₁ ell₂ : ℕ}
    (hg : 0 < g) (hbasis : IsCongruenceBasis g u v p q) (hz : (g : ℤ) ∣ t + latticeLinear u v z)
    (hbox : ∀ x ≤ 2 * ell₁, ∀ y ≤ 2 * ell₂,
      let w := positiveLatticeBoxPoint g u v p q z ell₁ ell₂ x y
      ((w.1 : ℝ) ∈ Set.Icc ((H : ℝ) / 4) (3 * H / 4)) ∧
        ((w.2 : ℝ) ∈ Set.Icc ((J : ℝ) / 4) (3 * J / 4)))
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) :
    ∀ x₁ ≤ 2 * ell₁, ∀ y₁ ≤ 2 * ell₂, ∀ x₂ ≤ 2 * ell₁, ∀ y₂ ≤ 2 * ell₂,
      latticeBoxNaturalBase g u v t p q z ell₁ ell₂ + latticeBoxStep g u v p * x₁ +
          latticeBoxStep g u v q * y₁ =
        latticeBoxNaturalBase g u v t p q z ell₁ ell₂ + latticeBoxStep g u v p * x₂ +
          latticeBoxStep g u v q * y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
  have himage := lattice_box_natural_image hg hbasis hz hbox
  have hdet : latticeDet p q ≠ 0 := by
    intro hh
    have hgnz : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
    have hd := hbasis.1
    rw [hh, abs_zero] at hd
    exact hgnz hd.symm
  intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ heq
  obtain ⟨hX₁, hY₁, hi₁⟩ := himage x₁ hx₁ y₁ hy₁
  obtain ⟨hX₂, hY₂, hi₂⟩ := himage x₂ hx₂ y₂ hy₂
  have hscaled := hi₁.symm.trans ((congrArg (fun n : ℕ => g ^ 2 * n) heq).trans hi₂)
  have hvalues := Nat.eq_of_mul_eq_mul_left hg hscaled
  obtain ⟨hX, hY⟩ := hproper _ hX₁ _ hY₁ _ hX₂ _ hY₂ hvalues
  obtain ⟨_, _, hwx₁, hwy₁⟩ := natural_coordinates_of_central_quarter (hbox x₁ hx₁ y₁ hy₁)
  obtain ⟨_, _, hwx₂, hwy₂⟩ := natural_coordinates_of_central_quarter (hbox x₂ hx₂ y₂ hy₂)
  apply positiveLatticeBoxPoint_injective hdet ell₁ ell₂
  ext
  · rw [← hwx₁, ← hwx₂, hX]
  · rw [← hwy₁, ← hwy₂, hY]

end Erdos587
