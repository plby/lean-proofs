/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.External.Erdos88.Concentration
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Real

namespace Erdos88
namespace FiniteSliceConcentration

open Classical Finset

variable {β : Type*} [Fintype β] [Nonempty β]

/-- Hoeffding's lemma for the uniform distribution on a finite type, in the
unnormalized sum form used by the recursive permutation sampler. -/
lemma finite_uniform_centered_exp_le (g : β → ℝ) (a lam : ℝ)
    (ha : 0 ≤ a) (hpair : ∀ x y, |g x - g y| ≤ a) :
    ∑ x, Real.exp (lam *
        (Concentration.uniformExpectation g - g x)) ≤
      Fintype.card β * Real.exp (a ^ 2 * lam ^ 2 / 2) := by
  letI : MeasurableSpace β := ⊤
  let p : PMF β := PMF.uniformOfFintype β
  let μ : Measure β := p.toMeasure
  let m : ℝ := Concentration.uniformExpectation g
  let X : β → ℝ := fun x => m - g x
  have hcard : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hmean : ∫ x, g x ∂μ = m := by
    calc
      ∫ x, g x ∂μ = ∑ x, (p x).toReal • g x := by
        simpa [μ] using PMF.integral_eq_sum p g
      _ = ∑ x, (Fintype.card β : ℝ)⁻¹ * g x := by
        apply Finset.sum_congr rfl
        intro x _
        simp [p, ENNReal.toReal_inv]
      _ = (∑ x, g x) / Fintype.card β := by
        rw [← Finset.mul_sum]
        rw [div_eq_mul_inv]
        ring
      _ = m := by rfl
  have hXmean : ∫ x, X x ∂μ = 0 := by
    simp only [X]
    rw [integral_sub (integrable_const _) (by fun_prop), integral_const, hmean]
    simp [μ]
  have hm_lower : ∀ x, g x - a ≤ m := by
    intro x
    dsimp [m, Concentration.uniformExpectation]
    apply (le_div_iff₀ hcard).2
    have hs : ∑ y : β, (g x - a) ≤ ∑ y : β, g y := by
      apply Finset.sum_le_sum
      intro y _
      have := hpair x y
      rw [abs_le] at this
      linarith
    calc
      (g x - a) * Fintype.card β = ∑ _y : β, (g x - a) := by
        simp
        ring
      _ ≤ ∑ y : β, g y := hs
  have hm_upper : ∀ x, m ≤ g x + a := by
    intro x
    dsimp [m, Concentration.uniformExpectation]
    apply (div_le_iff₀ hcard).2
    have hs : ∑ y : β, g y ≤ ∑ y : β, (g x + a) := by
      apply Finset.sum_le_sum
      intro y _
      have := hpair y x
      rw [abs_le] at this
      linarith
    calc
      ∑ y : β, g y ≤ ∑ _y : β, (g x + a) := hs
      _ = (g x + a) * Fintype.card β := by
        simp
        ring
  have hbound : ∀ x, X x ∈ Set.Icc (-a) a := by
    intro x
    exact ⟨by dsimp [X]; linarith [hm_lower x],
      by dsimp [X]; linarith [hm_upper x]⟩
  have hsg : ProbabilityTheory.HasSubgaussianMGF X
      ((‖a - (-a)‖₊ / 2) ^ 2) μ :=
    ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (by fun_prop) (Filter.Eventually.of_forall hbound) hXmean
  have hparam : ((‖a - (-a)‖₊ / 2) ^ 2) = (Real.toNNReal a) ^ 2 := by
    rw [sub_neg_eq_add, Real.nnnorm_of_nonneg (add_nonneg ha ha)]
    rw [Real.toNNReal_of_nonneg ha]
    congr 1
    apply NNReal.eq
    simp
  have hmgf := hsg.mgf_le lam
  have hmgf_integral :
      ∫ x, Real.exp (lam * X x) ∂μ ≤
        Real.exp (a ^ 2 * lam ^ 2 / 2) := by
    rw [ProbabilityTheory.mgf] at hmgf
    rw [hparam] at hmgf
    simpa [ha] using hmgf
  have hint :
      ∫ x, Real.exp (lam * X x) ∂μ =
        (∑ x, Real.exp (lam * X x)) / Fintype.card β := by
    calc
      ∫ x, Real.exp (lam * X x) ∂μ =
          ∑ x, (p x).toReal • Real.exp (lam * X x) := by
        simpa [μ] using PMF.integral_eq_sum p (fun x => Real.exp (lam * X x))
      _ = ∑ x, (Fintype.card β : ℝ)⁻¹ * Real.exp (lam * X x) := by
        apply Finset.sum_congr rfl
        intro x _
        simp [p, ENNReal.toReal_inv]
      _ = (∑ x, Real.exp (lam * X x)) / Fintype.card β := by
        rw [← Finset.mul_sum]
        rw [div_eq_mul_inv]
        ring
  have hmgf' :
      (∑ x, Real.exp (lam * (m - g x))) / Fintype.card β ≤
        Real.exp (a ^ 2 * lam ^ 2 / 2) := by
    rw [← hint]
    exact hmgf_integral
  simpa [m, mul_comm] using (div_le_iff₀ hcard).1 hmgf'

lemma sum_perm_decompose {N : ℕ} (g : Equiv.Perm (Fin (N + 1)) → ℝ) :
    ∑ σ, g σ = ∑ p : Fin (N + 1), ∑ e : Equiv.Perm (Fin N),
      g (Equiv.Perm.decomposeFin.symm (p, e)) := by
  rw [Finset.univ_perm_fin_succ, Finset.sum_map]
  rw [Fintype.sum_prod_type]
  rfl

/-- The `p`-branch of the standard decomposition of a permutation of
`Fin (N+1)`. -/
def permBranchEquiv {N : ℕ} (p : Fin (N + 1)) :
    Equiv.Perm (Fin N) ≃
      {σ : Equiv.Perm (Fin (N + 1)) // σ 0 = p} where
  toFun e := ⟨Equiv.Perm.decomposeFin.symm (p, e), by simp⟩
  invFun σ := (Equiv.Perm.decomposeFin σ.1).2
  left_inv e := by
    have h := Equiv.Perm.decomposeFin.apply_symm_apply (p, e)
    exact congr_arg Prod.snd h
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.Perm.decomposeFin.injective
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]
    have hfirst : σ.1 0 = (Equiv.Perm.decomposeFin σ.1).1 := by
      calc
        σ.1 0 = (Equiv.Perm.decomposeFin.symm
            (Equiv.Perm.decomposeFin σ.1)) 0 :=
          (congrArg (fun τ : Equiv.Perm (Fin (N + 1)) => τ 0)
            (Equiv.Perm.decomposeFin.symm_apply_apply σ.1)).symm
        _ = (Equiv.Perm.decomposeFin σ.1).1 :=
          Equiv.Perm.decomposeFin_symm_apply_zero _ _
    apply Prod.ext
    · exact σ.2.symm.trans hfirst
    · rfl

/-- Left multiplication by `(p q)` identifies the `p` and `q` branches. -/
def permBranchLeftSwapEquiv {N : ℕ} (p q : Fin (N + 1)) :
    {σ : Equiv.Perm (Fin (N + 1)) // σ 0 = p} ≃
      {σ : Equiv.Perm (Fin (N + 1)) // σ 0 = q} where
  toFun σ := ⟨Equiv.swap p q * σ.1, by
    simp [Equiv.Perm.mul_apply, σ.2]⟩
  invFun σ := ⟨Equiv.swap p q * σ.1, by
    simp [Equiv.Perm.mul_apply, σ.2]⟩
  left_inv σ := by
    apply Subtype.ext
    simp
  right_inv σ := by
    apply Subtype.ext
    simp

/-- The tail-permutation coupling between two possible first choices. -/
def permBranchSwapEquiv {N : ℕ} (p q : Fin (N + 1)) :
    Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
  (permBranchEquiv p).trans
    ((permBranchLeftSwapEquiv p q).trans (permBranchEquiv q).symm)

lemma permBranchSwapEquiv_spec {N : ℕ} (p q : Fin (N + 1))
    (e : Equiv.Perm (Fin N)) :
    Equiv.Perm.decomposeFin.symm (q, permBranchSwapEquiv p q e) =
      Equiv.swap p q * Equiv.Perm.decomposeFin.symm (p, e) := by
  change ((permBranchEquiv q)
      ((permBranchEquiv q).symm
        ((permBranchLeftSwapEquiv p q) ((permBranchEquiv p) e)))).1 =
    (permBranchLeftSwapEquiv p q (permBranchEquiv p e)).1
  rw [Equiv.apply_symm_apply]

/-- Switching two possible first images couples their conditional branches;
hence a switch-Lipschitz statistic has branch means at distance at most `a`. -/
lemma permBranchExpectation_diff_le {N : ℕ}
    (F : Equiv.Perm (Fin (N + 1)) → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hswitch : ∀ (σ : Equiv.Perm (Fin (N + 1))) p q,
      |F σ - F (Equiv.swap p q * σ)| ≤ a)
    (p q : Fin (N + 1)) :
    |Concentration.uniformExpectation
          (fun e : Equiv.Perm (Fin N) =>
            F (Equiv.Perm.decomposeFin.symm (p, e))) -
      Concentration.uniformExpectation
          (fun e : Equiv.Perm (Fin N) =>
            F (Equiv.Perm.decomposeFin.symm (q, e)))| ≤ a := by
  classical
  let c : ℝ := Fintype.card (Equiv.Perm (Fin N))
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast Fintype.card_pos
  rw [Concentration.uniformExpectation, Concentration.uniformExpectation,
    ← sub_div]
  rw [← (permBranchSwapEquiv p q).sum_comp
    (fun e : Equiv.Perm (Fin N) =>
      F (Equiv.Perm.decomposeFin.symm (q, e)))]
  rw [← Finset.sum_sub_distrib, abs_div]
  calc
    |∑ e : Equiv.Perm (Fin N),
        (F (Equiv.Perm.decomposeFin.symm (p, e)) -
          F (Equiv.Perm.decomposeFin.symm
            (q, permBranchSwapEquiv p q e)))| / |c| ≤
        (∑ e : Equiv.Perm (Fin N),
          |F (Equiv.Perm.decomposeFin.symm (p, e)) -
            F (Equiv.Perm.decomposeFin.symm
              (q, permBranchSwapEquiv p q e))|) / |c| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _e : Equiv.Perm (Fin N), a) / |c| := by
      gcongr with e
      rw [permBranchSwapEquiv_spec]
      exact hswitch _ p q
    _ = a := by
      rw [abs_of_pos hc]
      simp [c, hc.ne']

/-- A transposition of two tail images in a fixed branch is a transposition
of the corresponding two full images. -/
lemma decomposeFin_tail_swap {N : ℕ} (p : Fin (N + 1))
    (u v : Fin N) (e : Equiv.Perm (Fin N)) :
    Equiv.Perm.decomposeFin.symm (p, Equiv.swap u v * e) =
      Equiv.swap (Equiv.swap 0 p u.succ) (Equiv.swap 0 p v.succ) *
        Equiv.Perm.decomposeFin.symm (p, e) := by
  let ι : Fin N → Fin (N + 1) := fun x => Equiv.swap 0 p x.succ
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Fin.succ_injective N ((Equiv.swap 0 p).injective hxy)
  have hιp (x : Fin N) : ι x ≠ p := by
    intro hx
    have hx' : x.succ = 0 := (Equiv.swap 0 p).injective (by
      simpa [ι] using hx)
    exact Fin.succ_ne_zero x hx'
  ext i
  refine Fin.cases ?_ (fun x => ?_) i
  · simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
      Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (hιp u).symm (hιp v).symm]
  · simp only [Equiv.Perm.decomposeFin_symm_apply_succ,
      Equiv.Perm.mul_apply]
    by_cases hxu : e x = u
    · simp [hxu, ι]
    by_cases hxv : e x = v
    · simp [hxv, hxu, ι]
    · have hιu : ι (e x) ≠ ι u := fun h => hxu (hι h)
      have hιv : ι (e x) ≠ ι v := fun h => hxv (hι h)
      rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]
      rw [Equiv.swap_apply_of_ne_of_ne hιu hιv]

/-- A recursive certificate for the first `L` exposure steps of a uniform
permutation. At a successor step every conditional branch has a certificate,
and any two branch conditional means are at distance at most `a`. -/
noncomputable def PermRevealBounded :
    (N L : ℕ) → (Equiv.Perm (Fin N) → ℝ) → ℝ → Prop
  | N, 0, F, _ => ∀ σ τ, F σ = F τ
  | 0, _ + 1, _, _ => False
  | N + 1, L + 1, F, a =>
      (∀ p : Fin (N + 1),
        PermRevealBounded N L
          (fun e => F (Equiv.Perm.decomposeFin.symm (p, e))) a) ∧
      (∀ p q : Fin (N + 1),
        |Concentration.uniformExpectation
              (fun e : Equiv.Perm (Fin N) =>
                F (Equiv.Perm.decomposeFin.symm (p, e))) -
          Concentration.uniformExpectation
              (fun e : Equiv.Perm (Fin N) =>
                F (Equiv.Perm.decomposeFin.symm (q, e)))| ≤ a)

/-- Prefix-dependence together with left-transposition Lipschitzness produces
the recursive reveal certificate. -/
theorem permRevealBounded_of_prefix_of_switch :
    ∀ {L N : ℕ} (hLN : L ≤ N) (F : Equiv.Perm (Fin N) → ℝ) (a : ℝ),
      (∀ σ τ, (∀ i : Fin L,
          σ (Fin.castLE hLN i) = τ (Fin.castLE hLN i)) → F σ = F τ) →
      (∀ σ p q, |F σ - F (Equiv.swap p q * σ)| ≤ a) →
      PermRevealBounded N L F a := by
  intro L
  induction L with
  | zero =>
      intro N hLN F a hprefix hswitch
      simp only [PermRevealBounded]
      intro σ τ
      exact hprefix σ τ (fun i => Fin.elim0 i)
  | succ L ih =>
      intro N hLN F a hprefix hswitch
      cases N with
      | zero => omega
      | succ N =>
          change (∀ p : Fin (N + 1),
              PermRevealBounded N L
                (fun e => F (Equiv.Perm.decomposeFin.symm (p, e))) a) ∧ _
          constructor
          · intro p
            apply ih (Nat.le_of_succ_le_succ hLN)
            · intro e₁ e₂ he
              apply hprefix
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · have hcast : Fin.castLE hLN (0 : Fin (L + 1)) =
                    (0 : Fin (N + 1)) := by apply Fin.ext; rfl
                rw [hcast]
                simp
              · have hcast : Fin.castLE hLN (Fin.succ j) =
                    Fin.succ (Fin.castLE (Nat.le_of_succ_le_succ hLN) j) := by
                  apply Fin.ext
                  rfl
                rw [hcast]
                simp only [Equiv.Perm.decomposeFin_symm_apply_succ]
                rw [he j]
            · intro e u v
              rw [decomposeFin_tail_swap]
              exact hswitch _ _ _
          · exact permBranchExpectation_diff_le F a
              (le_trans (abs_nonneg _) (hswitch 1 0 0)) hswitch

/-- Exact exponential-moment Azuma bound for a certified `L`-step uniform
permutation reveal. -/
theorem permReveal_exp_moment_bound :
    ∀ (L N : ℕ) (F : Equiv.Perm (Fin N) → ℝ) (a lam : ℝ),
      0 ≤ a → PermRevealBounded N L F a →
      ∑ σ, Real.exp (lam * (Concentration.uniformExpectation F - F σ)) ≤
        Fintype.card (Equiv.Perm (Fin N)) *
          Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2) := by
  intro L
  induction L with
  | zero =>
      intro N F a lam ha hcert
      classical
      simp only [PermRevealBounded] at hcert
      let σ₀ : Equiv.Perm (Fin N) := 1
      have hconst : ∀ σ, F σ = F σ₀ := fun σ => hcert σ σ₀
      have hmean : Concentration.uniformExpectation F = F σ₀ := by
        rw [Concentration.uniformExpectation]
        simp_rw [hconst]
        simp
      simp [hmean, hconst]
  | succ L ih =>
      intro N F a lam ha hcert
      cases N with
      | zero => simp [PermRevealBounded] at hcert
      | succ N =>
          classical
          rcases hcert with ⟨htail, hbranch⟩
          let B : Fin (N + 1) → ℝ := fun p =>
            Concentration.uniformExpectation
              (fun e : Equiv.Perm (Fin N) =>
                F (Equiv.Perm.decomposeFin.symm (p, e)))
          have hglobal : Concentration.uniformExpectation B =
              Concentration.uniformExpectation F := by
            rw [Concentration.uniformExpectation, Concentration.uniformExpectation]
            rw [show (∑ p, B p) =
                (∑ σ : Equiv.Perm (Fin (N + 1)), F σ) /
                  Fintype.card (Equiv.Perm (Fin N)) by
              simp_rw [B, Concentration.uniformExpectation]
              rw [← Finset.sum_div]
              congr 1
              exact (sum_perm_decompose F).symm]
            simp only [Fintype.card_fin, Fintype.card_perm]
            rw [Nat.factorial_succ]
            push_cast
            field_simp
          have houter :
              ∑ p : Fin (N + 1),
                  Real.exp (lam * (Concentration.uniformExpectation F - B p)) ≤
                Fintype.card (Fin (N + 1)) *
                  Real.exp (a ^ 2 * lam ^ 2 / 2) := by
            rw [← hglobal]
            exact finite_uniform_centered_exp_le B a lam ha hbranch
          have hinner (p : Fin (N + 1)) :
              ∑ e : Equiv.Perm (Fin N),
                  Real.exp (lam * (B p -
                    F (Equiv.Perm.decomposeFin.symm (p, e)))) ≤
                Fintype.card (Equiv.Perm (Fin N)) *
                  Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2) := by
            exact ih N _ a lam ha (htail p)
          rw [sum_perm_decompose]
          calc
            ∑ p : Fin (N + 1), ∑ e : Equiv.Perm (Fin N),
                Real.exp (lam * (Concentration.uniformExpectation F -
                  F (Equiv.Perm.decomposeFin.symm (p, e)))) =
                ∑ p : Fin (N + 1),
                  (Real.exp (lam *
                    (Concentration.uniformExpectation F - B p)) *
                  ∑ e : Equiv.Perm (Fin N),
                    Real.exp (lam * (B p -
                      F (Equiv.Perm.decomposeFin.symm (p, e))))) := by
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _
              rw [← Real.exp_add]
              congr 1
              ring
            _ ≤ ∑ p : Fin (N + 1),
                (Real.exp (lam *
                    (Concentration.uniformExpectation F - B p)) *
                  (Fintype.card (Equiv.Perm (Fin N)) *
                    Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2))) := by
              apply Finset.sum_le_sum
              intro p _
              exact mul_le_mul_of_nonneg_left (hinner p) (Real.exp_nonneg _)
            _ = (Fintype.card (Equiv.Perm (Fin N)) *
                  Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
                ∑ p : Fin (N + 1),
                  Real.exp (lam *
                    (Concentration.uniformExpectation F - B p)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              ring
            _ ≤ (Fintype.card (Equiv.Perm (Fin N)) *
                  Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
                (Fintype.card (Fin (N + 1)) *
                  Real.exp (a ^ 2 * lam ^ 2 / 2)) :=
              mul_le_mul_of_nonneg_left houter (by positivity)
            _ = Fintype.card (Equiv.Perm (Fin (N + 1))) *
                Real.exp (((L + 1 : ℕ) : ℝ) * a ^ 2 * lam ^ 2 / 2) := by
              simp only [Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
              push_cast
              calc
                ((N.factorial : ℝ) *
                    Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2)) *
                    (((N : ℝ) + 1) *
                      Real.exp (a ^ 2 * lam ^ 2 / 2)) =
                    (((N : ℝ) + 1) * (N.factorial : ℝ)) *
                      (Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2) *
                        Real.exp (a ^ 2 * lam ^ 2 / 2)) := by ring
                _ = (((N : ℝ) + 1) * (N.factorial : ℝ)) *
                      Real.exp ((L : ℝ) * a ^ 2 * lam ^ 2 / 2 +
                        a ^ 2 * lam ^ 2 / 2) := by
                    rw [Real.exp_add]
                _ = (((N : ℝ) + 1) * (N.factorial : ℝ)) *
                      Real.exp (((L : ℝ) + 1) * a ^ 2 * lam ^ 2 / 2) := by
                    congr 1
                    ring

/-- One-sided lower-tail Azuma bound for a certified uniform permutation
reveal. -/
theorem permReveal_lower_tail {L N : ℕ}
    (F : Equiv.Perm (Fin N) → ℝ) (a t : ℝ)
    (hL : 0 < L) (ha : 0 < a) (ht : 0 ≤ t)
    (hcert : PermRevealBounded N L F a) :
    ((Finset.univ.filter fun σ =>
        t ≤ Concentration.uniformExpectation F - F σ).card : ℝ) ≤
      Fintype.card (Equiv.Perm (Fin N)) *
        Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by
  classical
  let V : ℝ := (L : ℝ) * a ^ 2
  let lam : ℝ := t / V
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hlam : 0 ≤ lam := div_nonneg ht hV.le
  have hmom := permReveal_exp_moment_bound L N F a lam ha.le hcert
  let A : Finset (Equiv.Perm (Fin N)) := Finset.univ.filter fun σ =>
    t ≤ Concentration.uniformExpectation F - F σ
  have hsub : A ⊆ Finset.univ.filter (fun σ =>
      Real.exp (lam * t) ≤ Real.exp (lam *
        (Concentration.uniformExpectation F - F σ))) := by
    intro σ hσ
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hlam)
  have hcard : (A.card : ℝ) ≤
      ((Finset.univ.filter (fun σ =>
        Real.exp (lam * t) ≤ Real.exp (lam *
          (Concentration.uniformExpectation F - F σ)))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hmarkov : (A.card : ℝ) * Real.exp (lam * t) ≤
      ∑ σ, Real.exp (lam *
        (Concentration.uniformExpectation F - F σ)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)) ?_
    exact Concentration.counting_markov
      (Ω := Equiv.Perm (Fin N))
      (fun σ => Real.exp (lam *
        (Concentration.uniformExpectation F - F σ)))
      (Real.exp (lam * t)) (Real.exp_pos _) (fun _ => Real.exp_nonneg _)
  have hcombined : (A.card : ℝ) * Real.exp (lam * t) ≤
      Fintype.card (Equiv.Perm (Fin N)) *
        Real.exp (V * lam ^ 2 / 2) := by
    exact hmarkov.trans (by simpa [V] using hmom)
  change (A.card : ℝ) ≤ _
  calc
    (A.card : ℝ) ≤
        (Fintype.card (Equiv.Perm (Fin N)) *
          Real.exp (V * lam ^ 2 / 2)) / Real.exp (lam * t) :=
      (le_div_iff₀ (Real.exp_pos (lam * t))).2 hcombined
    _ = Fintype.card (Equiv.Perm (Fin N)) *
        Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by
      rw [mul_div_assoc]
      rw [← Real.exp_sub]
      congr 1
      dsimp [lam, V]
      field_simp
      ring

/-- Two-sided Azuma--Hoeffding bound for a statistic depending on the first
`L` images of a uniform permutation and Lipschitz under left transpositions. -/
theorem permutationPrefix_two_sided_tail {L N : ℕ}
    (hLN : L ≤ N) (F : Equiv.Perm (Fin N) → ℝ) (a t : ℝ)
    (hL : 0 < L) (ha : 0 < a) (ht : 0 ≤ t)
    (hprefix : ∀ σ τ, (∀ i : Fin L,
      σ (Fin.castLE hLN i) = τ (Fin.castLE hLN i)) → F σ = F τ)
    (hswitch : ∀ σ p q, |F σ - F (Equiv.swap p q * σ)| ≤ a) :
    ((Finset.univ.filter fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|).card : ℝ) ≤
      2 * Fintype.card (Equiv.Perm (Fin N)) *
        Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by
  classical
  have hcert : PermRevealBounded N L F a :=
    permRevealBounded_of_prefix_of_switch hLN F a hprefix hswitch
  let G : Equiv.Perm (Fin N) → ℝ := fun σ => -F σ
  have hGprefix : ∀ σ τ, (∀ i : Fin L,
      σ (Fin.castLE hLN i) = τ (Fin.castLE hLN i)) → G σ = G τ := by
    intro σ τ h
    simp only [G]
    rw [hprefix σ τ h]
  have hGswitch : ∀ σ p q, |G σ - G (Equiv.swap p q * σ)| ≤ a := by
    intro σ p q
    calc
      |G σ - G (Equiv.swap p q * σ)| =
          |-(F σ - F (Equiv.swap p q * σ))| := by
            congr 1
            simp only [G]
            ring
      _ = |F σ - F (Equiv.swap p q * σ)| := abs_neg _
      _ ≤ a := hswitch σ p q
  have hGcert : PermRevealBounded N L G a :=
    permRevealBounded_of_prefix_of_switch hLN G a hGprefix hGswitch
  have hGmean : Concentration.uniformExpectation G =
      -Concentration.uniformExpectation F := by
    simp only [G, Concentration.uniformExpectation, Finset.sum_neg_distrib]
    ring
  let A : Finset (Equiv.Perm (Fin N)) := Finset.univ.filter fun σ =>
    t ≤ Concentration.uniformExpectation F - F σ
  let B : Finset (Equiv.Perm (Fin N)) := Finset.univ.filter fun σ =>
    t ≤ F σ - Concentration.uniformExpectation F
  have hA : (A.card : ℝ) ≤ Fintype.card (Equiv.Perm (Fin N)) *
      Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by
    simpa [A] using permReveal_lower_tail F a t hL ha ht hcert
  have hB : (B.card : ℝ) ≤ Fintype.card (Equiv.Perm (Fin N)) *
      Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by
    have h := permReveal_lower_tail G a t hL ha ht hGcert
    have hset :
        Finset.univ.filter (fun σ =>
          t ≤ Concentration.uniformExpectation G - G σ) = B := by
      ext σ
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hGmean]
      simp only [G]
      constructor <;> intro hσ <;> linarith
    rw [← hset]
    exact h
  have hsubset :
      Finset.univ.filter (fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|) ⊆ A ∪ B := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [le_abs] at hσ
    rw [Finset.mem_union]
    rcases hσ with hσ | hσ
    · right
      simpa [B] using hσ
    · left
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      linarith
  calc
    ((Finset.univ.filter fun σ =>
        t ≤ |F σ - Concentration.uniformExpectation F|).card : ℝ) ≤
        ((A ∪ B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (A.card : ℝ) + B.card := by exact_mod_cast Finset.card_union_le A B
    _ ≤ 2 * Fintype.card (Equiv.Perm (Fin N)) *
        Real.exp (-t ^ 2 / (2 * L * a ^ 2)) := by linarith

end FiniteSliceConcentration
end Erdos88
