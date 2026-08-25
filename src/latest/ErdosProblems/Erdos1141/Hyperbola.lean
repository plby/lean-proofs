import Mathlib

/-!
# The Dirichlet hyperbola decomposition
-/

open scoped BigOperators

namespace Erdos1141

def hyperbolaBox (L R X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 L).product (Finset.Icc 1 R)).filter fun z ↦ z.1 * z.2 ≤ X

lemma mem_hyperbolaBox {L R X d a : ℕ} :
    (d, a) ∈ hyperbolaBox L R X ↔
      (1 ≤ d ∧ d ≤ L) ∧ (1 ≤ a ∧ a ≤ R) ∧ d * a ≤ X := by
  simp only [hyperbolaBox, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

lemma sum_hyperbolaBox_left {R : Type*} [CommSemiring R] (f g : ℕ → R) (L X : ℕ) :
    (∑ z ∈ hyperbolaBox L X X, f z.1 * g z.2) =
      ∑ d ∈ Finset.Icc 1 L, f d * ∑ a ∈ Finset.Icc 1 (X / d), g a := by
  rw [hyperbolaBox, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hfilter : (Finset.Icc 1 X).filter (fun a ↦ d * a ≤ X) = Finset.Icc 1 (X / d) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1.1, (Nat.le_div_iff_mul_le hdpos).mpr (by simpa only [Nat.mul_comm] using h.2)⟩
    · intro h
      exact ⟨⟨h.1, h.2.trans (Nat.div_le_self X d)⟩,
        by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp h.2⟩
  rw [← Finset.sum_filter, hfilter, Finset.mul_sum]

lemma sum_hyperbolaBox_right {R : Type*} [CommSemiring R] (f g : ℕ → R) (L X : ℕ) :
    (∑ z ∈ hyperbolaBox X L X, f z.1 * g z.2) =
      ∑ a ∈ Finset.Icc 1 L, g a * ∑ d ∈ Finset.Icc 1 (X / a), f d := by
  calc
    _ = ∑ z ∈ hyperbolaBox L X X, g z.1 * f z.2 := by
      simp only [hyperbolaBox, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = _ := sum_hyperbolaBox_left g f L X

/-- The two short strips cover the hyperbola, with their rectangle counted twice. -/
theorem sum_hyperbola_split {R : Type*} [CommSemiring R] (f g : ℕ → R)
    (X D E : ℕ) (hDX : D ≤ X) (hEX : E ≤ X)
    (hDE : D * E ≤ X) (hcover : X < (D + 1) * (E + 1)) :
    (∑ d ∈ Finset.Icc 1 X, f d * ∑ a ∈ Finset.Icc 1 (X / d), g a) +
        (∑ d ∈ Finset.Icc 1 D, f d) * (∑ a ∈ Finset.Icc 1 E, g a) =
      (∑ d ∈ Finset.Icc 1 D, f d * ∑ a ∈ Finset.Icc 1 (X / d), g a) +
        ∑ a ∈ Finset.Icc 1 E, g a * ∑ d ∈ Finset.Icc 1 (X / a), f d := by
  have hunion : hyperbolaBox D X X ∪ hyperbolaBox X E X = hyperbolaBox X X X := by
    ext ⟨d, a⟩
    simp only [Finset.mem_union, mem_hyperbolaBox]
    constructor
    · rintro (h | h)
      · exact ⟨⟨h.1.1, h.1.2.trans hDX⟩, h.2⟩
      · exact ⟨h.1, ⟨h.2.1.1, h.2.1.2.trans hEX⟩, h.2.2⟩
    · intro h
      by_cases hd : d ≤ D
      · exact Or.inl ⟨⟨h.1.1, hd⟩, h.2⟩
      · have ha : a ≤ E := by
          by_contra ha
          have hprod := Nat.mul_le_mul (show D + 1 ≤ d by omega) (show E + 1 ≤ a by omega)
          omega
        exact Or.inr ⟨h.1, ⟨h.2.1.1, ha⟩, h.2.2⟩
  have hinter : hyperbolaBox D X X ∩ hyperbolaBox X E X =
      (Finset.Icc 1 D).product (Finset.Icc 1 E) := by
    ext ⟨d, a⟩
    simp only [Finset.mem_inter, mem_hyperbolaBox, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨h.1.1, h.2.2.1⟩
    · intro h
      have hprod := (Nat.mul_le_mul h.1.2 h.2.2).trans hDE
      exact ⟨⟨h.1, ⟨h.2.1, h.2.2.trans hEX⟩, hprod⟩,
        ⟨⟨h.1.1, h.1.2.trans hDX⟩, h.2, hprod⟩⟩
  have h := Finset.sum_union_inter (f := fun z : ℕ × ℕ ↦ f z.1 * g z.2)
    (s₁ := hyperbolaBox D X X) (s₂ := hyperbolaBox X E X)
  rw [hunion, hinter, sum_hyperbolaBox_left, sum_hyperbolaBox_left,
    sum_hyperbolaBox_right, Finset.product_eq_sprod, Finset.sum_product] at h
  simpa only [← Finset.mul_sum, ← Finset.sum_mul] using h

lemma sum_mul_div_split {R : Type*} [CommSemiring R] (f : ℕ → R)
    (X D : ℕ) (hD : 0 < D) (hDX : D ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, f d * (X / d : ℕ)) +
        (∑ d ∈ Finset.Icc 1 D, f d) * (X / D : ℕ) =
      (∑ d ∈ Finset.Icc 1 D, f d * (X / d : ℕ)) +
        ∑ a ∈ Finset.Icc 1 (X / D), ∑ d ∈ Finset.Icc 1 (X / a), f d := by
  have hcover : X < (D + 1) * (X / D + 1) := by
    have hmod := Nat.mod_lt X hD
    have hdecomp := Nat.div_add_mod X D
    nlinarith
  have h := sum_hyperbola_split f (fun _ ↦ (1 : R)) X D (X / D)
    hDX (Nat.div_le_self X D) (Nat.mul_div_le X D) hcover
  simpa using h

lemma norm_natCast_div_sub_div_le (X d : ℕ) :
    ‖((X / d : ℕ) : ℂ) - (X : ℂ) / d‖ ≤ 1 := by
  have h := Nat.abs_sub_floor_le (show (0 : ℝ) ≤ (X : ℝ) / d by positivity)
  rw [Nat.floor_div_eq_div] at h
  have heq : ((X / d : ℕ) : ℂ) - (X : ℂ) / d =
      ((((X / d : ℕ) : ℝ) - (X : ℝ) / d : ℝ) : ℂ) := by push_cast; rfl
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact h

lemma norm_sum_mul_div_sub_reciprocal_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (X D : ℕ) :
    ‖(∑ d ∈ Finset.Icc 1 D, f d * (X / d : ℕ)) -
      (X : ℂ) * ∑ d ∈ Finset.Icc 1 D, f d / d‖ ≤ D := by
  have hid : (∑ d ∈ Finset.Icc 1 D, f d * (X / d : ℕ)) -
      (X : ℂ) * (∑ d ∈ Finset.Icc 1 D, f d / d) =
        ∑ d ∈ Finset.Icc 1 D, f d * (((X / d : ℕ) : ℂ) - (X : ℂ) / d) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hid]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ‖f d * (((X / d : ℕ) : ℂ) - (X : ℂ) / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul]
      exact (mul_le_mul (hf d) (norm_natCast_div_sub_div_le X d)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = _ := by simp

/-- A hyperbola estimate with an arbitrary bound on character prefixes and reciprocal tails. -/
theorem norm_sum_mul_div_sub_main_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (C T : ℝ) (L : ℂ)
    (hprefix : ∀ Y : ℕ, ‖∑ n ∈ Finset.Icc 1 Y, f n‖ ≤ C)
    (X D : ℕ) (hD : 0 < D) (hDX : D ≤ X)
    (htail : ‖L - ∑ n ∈ Finset.Icc 1 D, f n / n‖ ≤ T) :
    ‖(∑ n ∈ Finset.Icc 1 X, f n * (X / n : ℕ)) - (X : ℂ) * L‖ ≤
      (D : ℝ) + 2 * (X / D : ℕ) * C + X * T := by
  let E := X / D
  let V := ∑ n ∈ Finset.Icc 1 D, f n
  let U := ∑ a ∈ Finset.Icc 1 E, ∑ n ∈ Finset.Icc 1 (X / a), f n
  let P := ∑ n ∈ Finset.Icc 1 D, f n / n
  have hsplit := sum_mul_div_split f X D hD hDX
  have hid : (∑ n ∈ Finset.Icc 1 X, f n * (X / n : ℕ)) - (X : ℂ) * L =
      ((∑ n ∈ Finset.Icc 1 D, f n * (X / n : ℕ)) - (X : ℂ) * P) +
        (U - V * E) + (X : ℂ) * (P - L) := by
    dsimp [U, V, P, E]
    linear_combination hsplit
  have hU : ‖U‖ ≤ (E : ℝ) * C := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 E, ‖∑ n ∈ Finset.Icc 1 (X / a), f n‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Finset.Icc 1 E, C := Finset.sum_le_sum fun a _ ↦ hprefix (X / a)
      _ = _ := by simp
  have hVE : ‖V * (E : ℂ)‖ ≤ C * E := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (hprefix D) (Nat.cast_nonneg E)
  have hmiddle : ‖U - V * E‖ ≤ 2 * (E : ℝ) * C := by
    have htri := norm_sub_le U (V * E)
    nlinarith
  have hlast : ‖(X : ℂ) * (P - L)‖ ≤ (X : ℝ) * T := by
    rw [norm_mul, Complex.norm_natCast, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sum_mul_div_sub_reciprocal_le f hf X D) hmiddle))
    hlast)

theorem norm_sum_mul_div_sub_main_le_of_linear_prefix
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (K T : ℝ) (hK : 0 ≤ K) (L : ℂ)
    (X D : ℕ) (hD : 0 < D) (hDX : D ≤ X)
    (hprefix : ∀ Y : ℕ, D ≤ Y → ‖∑ n ∈ Finset.Icc 1 Y, f n‖ ≤ (Y : ℝ) * K)
    (htail : ‖L - ∑ n ∈ Finset.Icc 1 D, f n / n‖ ≤ T) :
    ‖(∑ n ∈ Finset.Icc 1 X, f n * (X / n : ℕ)) - (X : ℂ) * L‖ ≤
      (D : ℝ) + (X : ℝ) * K * (2 + Real.log (X : ℝ)) + X * T := by
  let E := X / D
  let V := ∑ n ∈ Finset.Icc 1 D, f n
  let U := ∑ a ∈ Finset.Icc 1 E, ∑ n ∈ Finset.Icc 1 (X / a), f n
  let P := ∑ n ∈ Finset.Icc 1 D, f n / n
  have hsplit := sum_mul_div_split f X D hD hDX
  have hid : (∑ n ∈ Finset.Icc 1 X, f n * (X / n : ℕ)) - (X : ℂ) * L =
      ((∑ n ∈ Finset.Icc 1 D, f n * (X / n : ℕ)) - (X : ℂ) * P) +
        (U - V * E) + (X : ℂ) * (P - L) := by
    dsimp [U, V, P, E]
    linear_combination hsplit
  have hterm : ∀ a ∈ Finset.Icc 1 E,
      ‖∑ n ∈ Finset.Icc 1 (X / a), f n‖ ≤ (X : ℝ) * K * (a : ℝ)⁻¹ := by
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hDa : D ≤ X / a := by
      apply (Nat.le_div_iff_mul_le ha0).mpr
      have h := (Nat.le_div_iff_mul_le hD).mp (Finset.mem_Icc.mp ha).2
      simpa only [Nat.mul_comm] using h
    calc
      _ ≤ (X / a : ℕ) * K := hprefix (X / a) hDa
      _ ≤ ((X : ℝ) / a) * K := mul_le_mul_of_nonneg_right Nat.cast_div_le hK
      _ = _ := by ring
  have hU : ‖U‖ ≤ (X : ℝ) * K * (1 + Real.log (X : ℝ)) := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 E, ‖∑ n ∈ Finset.Icc 1 (X / a), f n‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 E, (X : ℝ) * K * (a : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ ≤ ∑ a ∈ Finset.Icc 1 X, (X : ℝ) * K * (a : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right (Nat.div_le_self X D)
        · intro a _ _; positivity
      _ = (X : ℝ) * K * ∑ a ∈ Finset.Icc 1 X, (a : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
          harmonic_le_one_add_log X) (by positivity)
  have hVE : ‖V * (E : ℂ)‖ ≤ (X : ℝ) * K := by
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((D : ℝ) * K) * E :=
        mul_le_mul_of_nonneg_right (hprefix D le_rfl) (Nat.cast_nonneg E)
      _ = ((D : ℝ) * E) * K := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_div_le X D) hK
  have hmiddle : ‖U - V * E‖ ≤ (X : ℝ) * K * (2 + Real.log (X : ℝ)) := by
    have htri := norm_sub_le U (V * E)
    linarith
  have hlast : ‖(X : ℂ) * (P - L)‖ ≤ (X : ℝ) * T := by
    rw [norm_mul, Complex.norm_natCast, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg X)
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_sum_mul_div_sub_reciprocal_le f hf X D) hmiddle))
    hlast)

end Erdos1141
