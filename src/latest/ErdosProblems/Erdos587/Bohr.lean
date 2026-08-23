import ErdosProblems.Erdos587.FiniteBogolyubov

open scoped BigOperators ComplexConjugate Pointwise

namespace Erdos587

noncomputable def cyclicBohrSet {N : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (rho : ℝ) : Finset (ZMod N) :=
  Finset.univ.filter fun x => ∀ k ∈ Gamma,
    ‖ZMod.stdAddChar (x * k) - 1‖ ≤ rho

@[simp] lemma mem_cyclicBohrSet {N : ℕ} [NeZero N]
    {Gamma : Finset (ZMod N)} {rho : ℝ} {x : ZMod N} :
    x ∈ cyclicBohrSet Gamma rho ↔
      ∀ k ∈ Gamma, ‖ZMod.stdAddChar (x * k) - 1‖ ≤ rho := by
  simp [cyclicBohrSet]

lemma zmodInFourfoldDifference_iff_mem_pointwise
    {N : ℕ} [NeZero N] {A : Finset (ZMod N)} {x : ZMod N} :
    ZModInFourfoldDifference A x ↔ x ∈ 2 • A - 2 • A := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨a + b, ?_, c + d, ?_, by ring⟩
    · rw [show 2 • A = A + A by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩
    · rw [show 2 • A = A + A by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨c, hc, d, hd, rfl⟩
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • A = A + A by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
    rw [← huv, ← hab, ← hcd]
    ring

theorem cyclicBohrSet_subset_fourfoldDifference
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) :
    cyclicBohrSet
        (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))) (1 / 2) ⊆
      2 • A - 2 • A := by
  intro x hx
  rw [← zmodInFourfoldDifference_iff_mem_pointwise]
  exact (finite_cyclic_bogolyubov_uniform q hq A hA hdense x
    (mem_cyclicBohrSet.mp hx)).1

theorem card_largeSpectrum_le_of_density
    {N : ℕ} [NeZero N] (q : ℕ) (hq : 1 ≤ q)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hdense : N ≤ q * A.card) :
    (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))).card ≤
      16 * q ^ 3 := by
  have hzero : (0 : ZMod N) ∈ cyclicBohrSet
      (cyclicLargeSpectrum A ((A.card : ℝ) / (4 * q))) (1 / 2) := by
    simp
  exact (finite_cyclic_bogolyubov_uniform q hq A hA hdense 0
    (mem_cyclicBohrSet.mp hzero)).2

/-- A residue represented by an integer of absolute value at most `N / 16`
lies in the analytic radius-`1/2` Bohr neighborhood. -/
lemma stdAddChar_intCast_close {N : ℕ} [NeZero N] (t : ℤ)
    (hsmall : 16 * t.natAbs ≤ N) :
    ‖ZMod.stdAddChar (t : ZMod N) - 1‖ ≤ (1 / 2 : ℝ) := by
  rw [ZMod.stdAddChar_coe]
  have hformula : (2 * Real.pi * Complex.I * (t : ℂ) / (N : ℂ)) =
      Complex.I * ((2 * Real.pi * (t : ℝ) / N : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hformula]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := 2 * Real.pi * (t : ℝ) / N)).trans ?_
  have htAbs : |(t : ℝ)| = (t.natAbs : ℝ) := by
    rw [← Int.cast_abs]
    simpa using congrArg (fun z : ℤ => (z : ℝ))
      (Int.natCast_natAbs t).symm
  have hNAbs : |(N : ℝ)| = (N : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg N)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_nonneg Real.pi_pos.le, htAbs, hNAbs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hsmallR : (16 : ℝ) * t.natAbs ≤ N := by
    exact_mod_cast hsmall
  rw [div_le_iff₀ hN]
  nlinarith

end Erdos587
