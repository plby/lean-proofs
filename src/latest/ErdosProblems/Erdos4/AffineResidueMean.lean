import ErdosProblems.Erdos4.AffineWeights

/-!
# Exact residue means of the affine states

At a nonzero source residue the affine forms have distinct roots.
Counting those roots gives precisely the state distribution used in the
orthonormal basis. This identifies the complete residue mean with the
same coefficient energy that appears in the principal and Fourier bounds.
-/

open scoped BigOperators

namespace Erdos4.AffineResidueMean

variable {k : ℕ}

theorem sum_rootState {T : Type*} [Fintype T] (root : Fin k → T)
    (hroot : Function.Injective root) (f : Option (Fin k) → ℝ) :
    (∑ t : T, f (RootStates.rootState Finset.univ root t)) =
      ((Fintype.card T : ℝ) - k) * f none + ∑ i : Fin k, f (some i) := by
  classical
  have hinj : Function.Injective (fun i : (Finset.univ : Finset (Fin k)) => root i) :=
    hroot.comp Subtype.val_injective
  have hc := RootStates.sum_weighted_rootState Finset.univ root hinj
    (fun s => (f s : ℂ)) (fun _ : T => 1)
  have hr : (∑ t : T, f (RootStates.rootState Finset.univ root t)) =
      (Fintype.card T : ℝ) * f none +
        ∑ i : (Finset.univ : Finset (Fin k)), (f (some i.val) - f none) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hc
  rw [Finset.sum_coe_sort Finset.univ (fun i : Fin k => f (some i) - f none),
    Finset.sum_sub_distrib] at hr
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  linarith

theorem state_eq_scaledRoot {F : Type*} [Field F] (h : Fin k → F)
    (hh : Function.Injective h) (p n : F) (hp : p ≠ 0) :
    AffineWeights.state h n p =
      RootStates.rootState Finset.univ (fun i => -(h i * p)) n := by
  have hinj : Function.Injective (fun i : (Finset.univ : Finset (Fin k)) => -(h i * p)) := by
    intro i j hij
    exact Subtype.ext (hh (mul_right_cancel₀ hp (neg_injective hij)))
  apply AffineWeights.option_eq_of_some_iff
  intro i
  rw [AffineWeights.state_eq_some_iff h hh n p hp,
    RootStates.rootState_eq_some_iff _ _ hinj]
  simp only [Finset.mem_univ, true_and]
  constructor <;> intro hx <;> linear_combination -hx

theorem sum_affine_state {F : Type*} [Field F] [Fintype F] (h : Fin k → F)
    (hh : Function.Injective h) (p : F) (hp : p ≠ 0) (f : Option (Fin k) → ℝ) :
    (∑ n : F, f (AffineWeights.state h n p)) =
      ((Fintype.card F : ℝ) - k) * f none + ∑ i : Fin k, f (some i) := by
  simp_rw [state_eq_scaledRoot h hh p _ hp]
  apply sum_rootState
  intro i j hij
  exact hh (mul_right_cancel₀ hp (neg_injective hij))

theorem local_mean {ell : ℕ} [Fact ell.Prime] (h : Fin k → ZMod ell)
    (hh : Function.Injective h) (p : ZMod ell) (hp : p ≠ 0) (f : Option (Fin k) → ℝ) :
    (ell : ℝ)⁻¹ * (∑ n : ZMod ell, f (AffineWeights.state h n p)) =
      LocalOrthogonality.mean (ell : ℝ) f := by
  rw [sum_affine_state h hh p hp, ZMod.card]
  unfold LocalOrthogonality.mean
  ring

theorem local_basis_mean {ell : ℕ} [Fact ell.Prime] (hell : (k : ℝ) < ell)
    (h : Fin k → ZMod ell) (hh : Function.Injective h)
    (p : ZMod ell) (hp : p ≠ 0) (a b : Option (Fin k)) :
    (ell : ℝ)⁻¹ * (∑ n : ZMod ell,
      LocalOrthogonality.extendedBasis (ell : ℝ) a (AffineWeights.state h n p) *
        LocalOrthogonality.extendedBasis (ell : ℝ) b (AffineWeights.state h n p)) =
      if a = b then 1 else 0 := by
  rw [local_mean h hh p hp (fun s =>
    LocalOrthogonality.extendedBasis (ell : ℝ) a s * LocalOrthogonality.extendedBasis (ell : ℝ) b s),
    LocalOrthogonality.mean_extendedBasis_mul hell]

variable {P : Type*} [Fintype P] [DecidableEq P]
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def mean (f : (∀ l, ZMod (ell l)) → ℝ) : ℝ :=
  (∏ l, (ell l : ℝ)⁻¹) * ∑ u, f u

noncomputable def basis (h : ∀ l, Fin k → ZMod (ell l)) (p : ∀ l, ZMod (ell l))
    (a : P → Option (Fin k)) (u : ∀ l, ZMod (ell l)) : ℝ :=
  ∏ l, LocalOrthogonality.extendedBasis (ell l : ℝ) (a l) (AffineWeights.state (h l) (u l) (p l))

theorem mean_basis_mul (hell : ∀ l, (k : ℝ) < ell l)
    (h : ∀ l, Fin k → ZMod (ell l)) (hh : ∀ l, Function.Injective (h l))
    (p : ∀ l, ZMod (ell l)) (hp : ∀ l, p l ≠ 0) (a b : P → Option (Fin k)) :
    mean ell (fun u => basis ell h p a u * basis ell h p b u) = if a = b then 1 else 0 := by
  classical
  have hfactor : ∀ u : ∀ l, ZMod (ell l),
      (∏ l, (ell l : ℝ)⁻¹) * (basis ell h p a u * basis ell h p b u) =
        ∏ l, (ell l : ℝ)⁻¹ *
          (LocalOrthogonality.extendedBasis (ell l : ℝ) (a l) (AffineWeights.state (h l) (u l) (p l)) *
            LocalOrthogonality.extendedBasis (ell l : ℝ) (b l) (AffineWeights.state (h l) (u l) (p l))) := by
    intro u
    simp only [basis, Finset.prod_mul_distrib]
  unfold mean
  rw [Finset.mul_sum]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun l (n : ZMod (ell l)) => (ell l : ℝ)⁻¹ *
    (LocalOrthogonality.extendedBasis (ell l : ℝ) (a l) (AffineWeights.state (h l) n (p l)) *
      LocalOrthogonality.extendedBasis (ell l : ℝ) (b l) (AffineWeights.state (h l) n (p l))))]
  have hlocal : ∀ l, (∑ n : ZMod (ell l), (ell l : ℝ)⁻¹ *
      (LocalOrthogonality.extendedBasis (ell l : ℝ) (a l) (AffineWeights.state (h l) n (p l)) *
        LocalOrthogonality.extendedBasis (ell l : ℝ) (b l) (AffineWeights.state (h l) n (p l)))) =
      if a l = b l then 1 else 0 := by
    intro l
    rw [← Finset.mul_sum]
    exact local_basis_mean (hell l) (h l) (hh l) (p l) (hp l) (a l) (b l)
  simp_rw [hlocal]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨l, hl⟩ : ∃ l, a l ≠ b l := by
      by_contra hn
      apply hab
      funext l
      exact not_ne_iff.mp (fun hne => hn ⟨l, hne⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

theorem mean_sum {I : Type*} (S : Finset I) (f : I → (∀ l, ZMod (ell l)) → ℝ) :
    mean ell (fun u => ∑ i ∈ S, f i u) = ∑ i ∈ S, mean ell (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.mul_sum]

theorem mean_const_mul (c : ℝ) (f : (∀ l, ZMod (ell l)) → ℝ) :
    mean ell (fun u => c * f u) = c * mean ell f := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

theorem mean_expansion_sq (hell : ∀ l, (k : ℝ) < ell l)
    (h : ∀ l, Fin k → ZMod (ell l)) (hh : ∀ l, Function.Injective (h l))
    (p : ∀ l, ZMod (ell l)) (hp : ∀ l, p l ≠ 0) (v : (P → Option (Fin k)) → ℝ) :
    mean ell (fun u => (∑ a, v a * basis ell h p a u) ^ 2) =
      RestrictedProductNorm.energy v := by
  classical
  have heq : ∀ u : ∀ l, ZMod (ell l), (∑ a, v a * basis ell h p a u) ^ 2 =
      ∑ a, ∑ b, (v a * v b) * (basis ell h p a u * basis ell h p b u) := by
    intro u
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _hb => by ring)
  simp_rw [heq]
  rw [mean_sum]
  simp_rw [mean_sum, mean_const_mul, mean_basis_mul ell hell h hh p hp]
  simp [RestrictedProductNorm.energy, pow_two]

end Erdos4.AffineResidueMean
