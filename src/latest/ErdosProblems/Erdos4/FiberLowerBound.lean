import ErdosProblems.Erdos4.ArithmeticFibers

/-! The arithmetic completions form an injective subsum of the positive
ideal projection fiber, with the original product cutoff retained. -/

open scoped BigOperators

namespace Erdos4.FiberLowerBound

open DivisorCoefficients IdealAction CutoffSimplex ArithmeticFibers

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def admissible (W T : ℕ) (ell : P → ℕ) (j : Fin k)
    (a : P → Option (Fin k)) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 T).filter (fun u =>
    Squarefree u ∧ u.Coprime W ∧ AvoidsFrozen ell j a u)

omit [Fintype P] [DecidableEq P] in
theorem mem_admissible {W T u : ℕ} {ell : P → ℕ} {j : Fin k}
    {a : P → Option (Fin k)} :
    u ∈ admissible W T ell j a ↔
      1 ≤ u ∧ u ≤ T ∧ Squarefree u ∧ u.Coprime W ∧ AvoidsFrozen ell j a u := by
  classical
  simp only [admissible, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def admissibleSum (W : ℕ) (m : ℝ) (R T : ℕ)
    (ell : P → ℕ) (j : Fin k) (a : P → Option (Fin k)) : ℝ :=
  ∑ u ∈ admissible W T ell j a,
    ProfileSmooth.scaled m k R u / (Nat.totient u : ℝ)

theorem admissibleSum_le_fiberSum {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (W T : ℕ) (ell : P → ℕ) (hprime : ∀ p, (ell p).Prime)
    (hinj : Function.Injective ell) (j : Fin k) (a : P → Option (Fin k))
    (hcutoff : cofactor ell j a * T ≤ R)
    (hcover : ∀ u, Squarefree u → u.Coprime W → u ≤ T →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q) :
    admissibleSum W m R T ell j a ≤ fiberSum m R ell j a := by
  classical
  let S := admissible W T ell j a
  let F : (P → Option (Fin k)) → ℝ := fun b =>
    if Compatible j a b ∧ totalDivisor ell b ≤ R then
      PrimitiveProfile.profile m k (Real.log (coordinateDivisor ell b j) / Real.log R) *
        fiberWeight ell j a b else 0
  have hF : ∀ b, 0 ≤ F b := by
    intro b
    dsimp [F]
    split_ifs
    · apply mul_nonneg
      · exact (PrimitiveProfile.profile_pos hm (Nat.cast_nonneg k)
          (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))).le
      · exact Finset.prod_nonneg (fun p _hp => by split_ifs <;> positivity)
    · exact le_rfl
  have hcoord : ∀ u ∈ S, coordinateDivisor ell (completion ell j a u) j = u := by
    intro u hu
    have hh := mem_admissible.mp hu
    exact coordinateDivisor_completion ell hprime hinj j a hh.2.2.1
      (hcover u hh.2.2.1 hh.2.2.2.1 hh.2.1)
  have hinjective : ∀ u ∈ S, ∀ v ∈ S,
      completion ell j a u = completion ell j a v → u = v := by
    intro u hu v hv huv
    rw [← hcoord u hu, ← hcoord v hv, huv]
  have hterm : ∀ u ∈ S,
      ProfileSmooth.scaled m k R u / (Nat.totient u : ℝ) = F (completion ell j a u) := by
    intro u hu
    have hh := mem_admissible.mp hu
    have hcov := hcover u hh.2.2.1 hh.2.2.2.1 hh.2.1
    have hcompatible := compatible_completion ell j a hh.2.2.2.2
    have htotal : totalDivisor ell (completion ell j a u) ≤ R := by
      rw [totalDivisor_completion ell hprime hinj j a hh.2.2.1 hcov hh.2.2.2.2]
      exact (Nat.mul_le_mul_left _ hh.2.1).trans hcutoff
    dsimp [F]
    rw [if_pos ⟨hcompatible, htotal⟩, hcoord u hu,
      fiberWeight_completion ell hprime hinj j a hh.2.2.1 hcov hh.2.2.2.2]
    unfold ProfileSmooth.scaled
    ring
  calc
    admissibleSum W m R T ell j a = ∑ u ∈ S, F (completion ell j a u) :=
      Finset.sum_congr rfl hterm
    _ = ∑ b ∈ S.image (completion ell j a), F b := (Finset.sum_image hinjective).symm
    _ ≤ ∑ b, F b := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _hb _hnot => hF b)
    _ = fiberSum m R ell j a := rfl

/-- The entire prime window contains every prime needed by each
squarefree completion; dividing by the frozen cofactor enforces the
genuine product cutoff exactly. -/
theorem primeWindow_admissibleSum_le {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (K : ℕ) (j : Fin k) (a : primeWindow K R → Option (Fin k)) :
    admissibleSum (primorial K) m R
      (R / cofactor (fun p : primeWindow K R => (p : ℕ)) j a)
      (fun p : primeWindow K R => (p : ℕ)) j a ≤
    fiberSum m R (fun p : primeWindow K R => (p : ℕ)) j a := by
  apply admissibleSum_le_fiberSum hm hR
  · intro p
    exact (mem_primeWindow.mp p.property).1
  · exact Subtype.val_injective
  · exact Nat.mul_div_le _ _
  · intro u _hu huW huT
    exact primeFactors_covered (huT.trans (Nat.div_le_self _ _)) huW

end Erdos4.FiberLowerBound
