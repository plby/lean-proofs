import ErdosProblems.Erdos4.DivisorCoefficients

/-!
# Reciprocal prime mass under the actual coefficient energy

A one-coordinate erasure gives a bound for every occupied label. Summing
these bounds controls the energy of coefficient labels with excessive
reciprocal prime mass. This is a finite estimate, uniform in the cutoff.
-/

open scoped BigOperators

namespace Erdos4.CoefficientMass

open DivisorCoefficients RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem localWeight_some_sq {ell : ℕ} (hell : 1 ≤ ell) (i : Fin k) :
    localWeight ell (some i) ^ 2 = ((ell : ℝ) - 1)⁻¹ := by
  have hp : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  simp only [localWeight, inv_pow, Real.sq_sqrt (by linarith : 0 ≤ (ell : ℝ) - 1)]

theorem occupied_label_energy_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (p : P) (i : Fin k) :
    (∑ a : P → Option (Fin k), if a p = some i then coefficient m R ell a ^ 2 else 0) ≤
      ((ell p : ℝ) - 1)⁻¹ * energy (coefficient (k := k) m R ell) := by
  let S : Finset (P → Option (Fin k)) := Finset.univ.filter (fun a => a p = some i)
  let E : (P → Option (Fin k)) → P → Option (Fin k) := erase {p}
  have hinj : ∀ a ∈ S, ∀ b ∈ S, E a = E b → a = b := by
    intro a ha b hb hab
    have hap := (Finset.mem_filter.mp ha).2
    have hbp := (Finset.mem_filter.mp hb).2
    funext q
    by_cases hq : q = p
    · subst q
      exact hap.trans hbp.symm
    · have hh := congrFun hab q
      simpa only [E, erase, Finset.mem_singleton, if_neg hq] using hh
  have hpoint : ∀ a ∈ S, coefficient m R ell a ^ 2 ≤
      localWeight (ell p) (some i) ^ 2 * coefficient m R ell (E a) ^ 2 := by
    intro a ha
    have hap := (Finset.mem_filter.mp ha).2
    have hh := coefficient_le_removedFactor_mul_erase hm hR ell hell {p} a
    simp only [removedFactor, Finset.prod_singleton, hap] at hh
    have hs := (sq_le_sq₀ (coefficient_nonneg (by linarith) hR ell a)
      (mul_nonneg (localWeight_nonneg (ell p) (some i))
        (coefficient_nonneg (by linarith) hR ell (E a)))).mpr hh
    simpa only [mul_pow] using hs
  have himage : (∑ a ∈ S, coefficient m R ell (E a) ^ 2) ≤
      energy (coefficient (k := k) m R ell) := by
    rw [← Finset.sum_image (f := fun a => coefficient m R ell a ^ 2) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ha _hnot => sq_nonneg _)
  rw [← Finset.sum_filter]
  change (∑ a ∈ S, coefficient m R ell a ^ 2) ≤ _
  calc
    (∑ a ∈ S, coefficient m R ell a ^ 2) ≤
        ∑ a ∈ S, localWeight (ell p) (some i) ^ 2 * coefficient m R ell (E a) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = localWeight (ell p) (some i) ^ 2 * ∑ a ∈ S, coefficient m R ell (E a) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ localWeight (ell p) (some i) ^ 2 * energy (coefficient (k := k) m R ell) :=
      mul_le_mul_of_nonneg_left himage (sq_nonneg _)
    _ = _ := by rw [localWeight_some_sq (hell p) i]

noncomputable def reciprocalMass (ell : P → ℕ) (a : P → Option (Fin k)) : ℝ :=
  ∑ p, if a p = none then 0 else ((ell p : ℝ) - 1)⁻¹

omit [DecidableEq P] in
theorem reciprocalMass_nonneg (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (a : P → Option (Fin k)) : 0 ≤ reciprocalMass ell a := by
  apply Finset.sum_nonneg
  intro p _hp
  split_ifs
  · exact le_rfl
  · have hp : (1 : ℝ) ≤ ell p := by exact_mod_cast hell p
    exact inv_nonneg.mpr (by linarith)

theorem reciprocalMass_energy_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) :
    (∑ a : P → Option (Fin k), coefficient m R ell a ^ 2 * reciprocalMass ell a) ≤
      energy (coefficient (k := k) m R ell) * k * ∑ p, (((ell p : ℝ) - 1)⁻¹) ^ 2 := by
  have hpoint (p : P) (a : P → Option (Fin k)) :
      coefficient m R ell a ^ 2 * (if a p = none then 0 else ((ell p : ℝ) - 1)⁻¹) =
        ((ell p : ℝ) - 1)⁻¹ *
          ∑ i : Fin k, if a p = some i then coefficient m R ell a ^ 2 else 0 := by
    cases hp : a p with
    | none => simp
    | some i => simp [mul_comm]
  have hsum (p : P) :
      (∑ i : Fin k, ∑ a : P → Option (Fin k),
        if a p = some i then coefficient m R ell a ^ 2 else 0) ≤
          (k : ℝ) * (((ell p : ℝ) - 1)⁻¹ * energy (coefficient (k := k) m R ell)) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
      (fun i _hi => occupied_label_energy_le hm hR ell hell p i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  unfold reciprocalMass
  simp_rw [Finset.mul_sum, hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p _hp
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hp : (1 : ℝ) ≤ ell p := by exact_mod_cast hell p
  have hh := mul_le_mul_of_nonneg_left (hsum p)
    (inv_nonneg.mpr (by linarith : 0 ≤ (ell p : ℝ) - 1))
  exact hh.trans_eq (by ring)

/-- Markov's inequality in the exact coefficient energy. -/
theorem excessive_mass_energy_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) {η : ℝ} (hη : 0 < η) :
    (∑ a ∈ (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => η < reciprocalMass ell a),
      coefficient m R ell a ^ 2) ≤
      (energy (coefficient (k := k) m R ell) * k * ∑ p, (((ell p : ℝ) - 1)⁻¹) ^ 2) / η := by
  apply (le_div_iff₀ hη).mpr
  have htotal := reciprocalMass_energy_le (k := k) hm hR ell hell
  apply le_trans _ htotal
  rw [Finset.sum_mul]
  calc
    (∑ a ∈ (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => η < reciprocalMass ell a),
        coefficient m R ell a ^ 2 * η) ≤
        ∑ a ∈ (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => η < reciprocalMass ell a),
          coefficient m R ell a ^ 2 * reciprocalMass ell a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp ha).2.le (sq_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ha _hnot => mul_nonneg (sq_nonneg _) (reciprocalMass_nonneg ell hell a))

end Erdos4.CoefficientMass
