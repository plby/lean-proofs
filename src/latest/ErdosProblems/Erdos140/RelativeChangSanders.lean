import ErdosProblems.Erdos140.RelativeChangDefinitions
import ErdosProblems.Erdos140.RelativeSpectrumBridge
import ErdosProblems.Erdos140.RelativeDissociation
import ErdosProblems.Erdos140.BourgainRegular

/-!
# The relative Chang--Sanders lemma

This file develops the local spectral input used in the Bohr-set form of
Schoen--Sisask almost-periodicity.  The analytic notion of dissociativity is
relative to a probability measure.  This is the formulation introduced by
Sanders: unlike ordinary dissociativity it gives bounds in terms of the
relative density inside a Bohr set, with no ambient-density loss.
-/

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos140.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem IsWeightedDissociated.mono_K {mu : G → ℝ} {K L : ℝ}
    {Delta : Finset (AddChar G ℂ)}
    (h : IsWeightedDissociated mu K Delta) (hKL : K ≤ L) :
    IsWeightedDissociated mu L Delta := by
  intro u hu
  exact (h u hu).trans (Real.exp_le_exp.mpr hKL)

theorem IsWeightedDissociated.mono_subset {mu : G → ℝ} {K : ℝ}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : IsWeightedDissociated mu K Delta) (hsub : Gamma ⊆ Delta) :
    IsWeightedDissociated mu K Gamma := by
  intro u hu
  let v : AddChar G ℂ → ℂ := fun psi ↦ if psi ∈ Gamma then u psi else 0
  have hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1 := by
    intro psi hpsi
    by_cases hp : psi ∈ Gamma
    · simpa [v, hp] using hu psi hp
    · simp [v, hp]
  have heq (x : G) :
      ∏ psi ∈ Delta, (1 + (v psi * psi x).re) =
        ∏ psi ∈ Gamma, (1 + (u psi * psi x).re) := by
    rw [← Finset.prod_subset hsub]
    · apply prod_congr rfl
      intro psi hpsi
      simp [v, hpsi]
    · intro psi hpsiDelta hpsiGamma
      simp [v, hpsiGamma]
  simpa only [heq] using h v hv

/-- Jensen's inequality for an arbitrary nonnegative finite probability
weight.  Keeping this lemma in finite-sum form avoids introducing a second
measure-theoretic normalization layer. -/
theorem exp_weightedAverage_le_weightedAverage_exp
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw_sum : ∑ x : G, w x = 1)
    (f : G → ℝ) :
    exp (∑ x : G, w x * f x) ≤ ∑ x : G, w x * exp (f x) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset G))
    (p := f) (fun x _ ↦ hw x) (by simpa using hw_sum)
    (fun x _ ↦ Set.mem_univ (f x))
  simpa using h

/-- Weighted exponential Rudin inequality.  Ordinary Rudin is the special
case in which `mu` is uniform and `K = 0`; the proof only uses the defining
Riesz-product estimate, so it works verbatim for Sanders' local notion. -/
theorem weighted_rudin_exp_ineq
    (mu : G → ℝ) (K : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x)
    (hDelta : IsWeightedDissociated mu K Delta)
    (c : AddChar G ℂ → ℂ) :
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
      exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (x : G) :
      exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
    calc
      exp ((∑ psi ∈ Delta, c psi * psi x).re) =
          ∏ psi ∈ Delta, exp ((c psi * psi x).re) := by
            simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi ∈ Delta,
          (cosh ‖c psi * psi x‖ +
            ((c psi * psi x) / ‖c psi * psi x‖).re *
              sinh ‖c psi * psi x‖) := by
        gcongr with psi hpsi
        exact hexp _
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ +
            (u psi * (c psi * psi x) / (u psi * ↑‖c psi‖)).re *
              sinh ‖c psi‖) := by
        apply prod_congr rfl
        intro psi hpsi
        rw [norm_mul, AddChar.norm_apply, mul_one,
          mul_div_mul_left _ _ (hu0 psi)]
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
        apply prod_congr rfl
        intro psi hpsi
        obtain hc | hc := eq_or_ne (c psi) 0
        · simp [hc]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hc,
          ← Complex.re_mul_ofReal, mul_right_comm]
  let q : AddChar G ℂ → ℝ := fun psi ↦ sinh ‖c psi‖ / cosh ‖c psi‖
  let v : AddChar G ℂ → ℂ := fun psi ↦ (q psi : ℂ) * u psi
  have hfactor (x : G) :
      (∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re)) =
        (∏ psi ∈ Delta, cosh ‖c psi‖) *
          (∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
    rw [← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro psi hpsi
    have hcosh : cosh ‖c psi‖ ≠ 0 := ne_of_gt (cosh_pos _)
    have hsinh_re :
        (u psi * (sinh ‖c psi‖ : ℂ) * psi x).re =
          sinh ‖c psi‖ * (u psi * psi x).re := by
      rw [show u psi * (sinh ‖c psi‖ : ℂ) * psi x =
          (sinh ‖c psi‖ : ℂ) * (u psi * psi x) by ring]
      exact Complex.re_ofReal_mul _ _
    have hv_re : (v psi * psi x).re = q psi * (u psi * psi x).re := by
      rw [show v psi * psi x = (q psi : ℂ) * (u psi * psi x) by
        simp [v]; ring]
      exact Complex.re_ofReal_mul _ _
    rw [hsinh_re, hv_re]
    dsimp [q]
    field_simp
  calc
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∑ x : G, mu x * ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmu x)
    _ = (∏ psi ∈ Delta, cosh ‖c psi‖) *
        (∑ x : G, mu x *
          ∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [hfactor]
      ring
    _ ≤ (∏ psi ∈ Delta, cosh ‖c psi‖) * exp K := by
      gcongr
      apply hDelta v
      intro psi hpsi
      have hq : |q psi| ≤ 1 := by
        simpa [q, Real.tanh_eq_sinh_div_cosh] using (Real.abs_tanh_lt_one ‖c psi‖).le
      simpa [v, norm_mul, hu psi, Complex.norm_real, Real.norm_eq_abs] using hq
    _ ≤ exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) * exp K := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        ∏ psi ∈ Delta, cosh ‖c psi‖ ≤
            ∏ psi ∈ Delta, exp (‖c psi‖ ^ 2 / 2) := by
          gcongr with psi hpsi
          exact cosh_le_exp_half_sq _
        _ = exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
          simp_rw [← exp_sum, ← sum_div]
    _ = exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
      rw [← exp_add]
      congr 1
      ring

/-! ## The relative logarithmic dimension bound -/

/-- A measure-dissociated subset of the relative large spectrum has
cardinality controlled by the density relative to that measure.  Crucially,
the right side contains no occurrence of `Fintype.card G`.

The explicit constant is deliberately coarse.  In the application `K = 1`
and `f` is an indicator, so `a = |X|/|B|`. -/
theorem card_weightedDissociated_relativeLargeSpectrum_le
    (mu f : G → ℝ) (K eta : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (heta : 0 < eta)
    (hDelta : IsWeightedDissociated mu K Delta)
    (hsub : Delta ⊆ relativeLargeSpectrum mu f eta)
    (hmass : 0 < ∑ x : G, f x * mu x) :
    (Delta.card : ℝ) ≤
      2 * (K + log ((∑ x : G, f x * mu x)⁻¹)) / eta ^ 2 := by
  let a : ℝ := ∑ x : G, f x * mu x
  have ha : 0 < a := by simpa [a] using hmass
  let spec : AddChar G ℂ → ℂ := fun psi ↦
    ∑ x : G, (f x * mu x : ℝ) * psi x
  choose u hu huspec using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spec psi)
  let c : AddChar G ℂ → ℂ := fun psi ↦ (eta : ℂ) * u psi
  let P : G → ℝ := fun x ↦ (∑ psi ∈ Delta, c psi * psi x).re
  have hc_norm (psi : AddChar G ℂ) : ‖c psi‖ ^ 2 = eta ^ 2 := by
    simp [c, hu, abs_of_pos heta]
  have hc_sq : ∑ psi ∈ Delta, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm]
    simp
    ring
  have hcomplex :
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
    calc
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
          ∑ psi ∈ Delta,
            c psi * ∑ x : G, ((f x * mu x : ℝ) : ℂ) * psi x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro psi hpsi
        apply sum_congr rfl
        intro x hx
        ring
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spec psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        dsimp [c, spec]
        rw [mul_assoc, ← huspec]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
        rw [Finset.mul_sum]
  have hmeanP :
      ∑ x : G, f x * mu x * P x =
        eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
    have hre := congrArg Complex.re hcomplex
    calc
      ∑ x : G, f x * mu x * P x =
          (∑ x : G, ((f x * mu x : ℝ) : ℂ) *
            (∑ psi ∈ Delta, c psi * psi x)).re := by
        simp [P, Complex.re_sum, Complex.mul_re]
      _ = ((eta : ℂ) *
          ∑ psi ∈ Delta, (‖spec psi‖ : ℂ)).re := hre
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by simp
  have hmean_lower :
      eta ^ 2 * a * Delta.card ≤ ∑ x : G, f x * mu x * P x := by
    rw [hmeanP]
    calc
      eta ^ 2 * a * (Delta.card : ℝ) =
          ∑ psi ∈ Delta, eta * (eta * a) := by
        simp
        ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spec psi‖ := by
        gcongr with psi hpsi
        have hs := mem_relativeLargeSpectrum.mp (hsub hpsi)
        simpa [a, spec] using hs
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
        rw [Finset.mul_sum]
  let w : G → ℝ := fun x ↦ f x * mu x / a
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (mul_nonneg (hf0 x) (hmu x)) ha.le
  have hw_sum : ∑ x : G, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    dsimp [a]
    exact div_self ha.ne'
  have hmean_w : eta ^ 2 * Delta.card ≤ ∑ x : G, w x * P x := by
    calc
      eta ^ 2 * (Delta.card : ℝ) ≤
          (∑ x : G, f x * mu x * P x) / a := by
        rw [le_div_iff₀ ha]
        calc
          eta ^ 2 * (Delta.card : ℝ) * a =
              eta ^ 2 * a * (Delta.card : ℝ) := by ring
          _ ≤ _ := hmean_lower
      _ = ∑ x : G, w x * P x := by
        dsimp [w]
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro x hx
        ring
  have hJensen :
      exp (eta ^ 2 * Delta.card) ≤
        ∑ x : G, w x * exp (P x) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (∑ x : G, w x * P x) := by
        exact Real.exp_le_exp.mpr hmean_w
      _ ≤ _ := exp_weightedAverage_le_weightedAverage_exp w hw0 hw_sum P
  have hweighted_le :
      ∑ x : G, w x * exp (P x) ≤
        a⁻¹ * ∑ x : G, mu x * exp (P x) := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x hx
    rw [div_eq_inv_mul]
    calc
      a⁻¹ * (f x * mu x) * exp (P x) ≤
          a⁻¹ * (1 * mu x) * exp (P x) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact mul_le_mul_of_nonneg_right (hf1 x) (hmu x)
      _ = a⁻¹ * (mu x * exp (P x)) := by ring
  have hRudin :
      ∑ x : G, mu x * exp (P x) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    have hr := weighted_rudin_exp_ineq mu K Delta hmu hDelta c
    simpa [P, hc_sq] using hr
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2) :=
    hJensen.trans (hweighted_le.trans
      (mul_le_mul_of_nonneg_left hRudin (inv_nonneg.mpr ha.le)))
  have hmul :
      a * exp (eta ^ 2 * Delta.card) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    calc
      a * exp (eta ^ 2 * Delta.card) ≤
          a * (a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2)) := by
        gcongr
      _ = exp (K + eta ^ 2 * Delta.card / 2) := by
        field_simp
  have hlinear :
      log a + eta ^ 2 * Delta.card ≤
        K + eta ^ 2 * Delta.card / 2 := by
    rw [← exp_log ha, ← exp_add] at hmul
    exact Real.exp_le_exp.mp hmul
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  rw [log_inv]
  nlinarith

/-- Constant-on-a-set specialization of the relative dimension bound.  The
parameter `R` is any upper bound for the reciprocal weighted mass of `X`;
in the smoothed-Bohr application it is `2 * |B| / |X|`. -/
theorem card_weightedDissociated_finsetIndicator_le
    [DecidableEq G] (B X : Finset G) (hXB : X ⊆ B) (hX : X.Nonempty)
    (w : G → ℝ) (c R eta : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∈ B, w x = c)
    (hc : 0 < c) (hR : (c * X.card)⁻¹ ≤ R)
    (heta : 0 < eta) (Delta : Finset (AddChar G ℂ))
    (hDelta : IsWeightedDissociated w 1 Delta)
    (hsub : Delta ⊆ Chang.largeSpectrum X eta) :
    (Delta.card : ℝ) ≤ 2 * (1 + log R) / eta ^ 2 := by
  have hmass_eq :
      ∑ x : G, finsetIndicator X x * w x = c * X.card :=
    RelativeSpectrumBridge.sum_finsetIndicator_mul_eq_const_mul_card hXB hw
  have hmass : 0 < ∑ x : G, finsetIndicator X x * w x := by
    rw [hmass_eq]
    have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have hsub' : Delta ⊆
      relativeLargeSpectrum w (finsetIndicator X) eta := by
    intro psi hpsi
    exact (RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
      hXB hw hc eta psi).2 (hsub hpsi)
  have hdim := card_weightedDissociated_relativeLargeSpectrum_le
    w (finsetIndicator X) 1 eta Delta hw0
    (by intro x; unfold finsetIndicator; split <;> norm_num)
    (by intro x; unfold finsetIndicator; split <;> norm_num)
    heta hDelta hsub' hmass
  have hmassInv :
      ((∑ x : G, finsetIndicator X x * w x)⁻¹) ≤ R := by
    simpa [hmass_eq] using hR
  have hlog :
      log ((∑ x : G, finsetIndicator X x * w x)⁻¹) ≤ log R :=
    Real.log_le_log (inv_pos.mpr hmass) hmassInv
  calc
    (Delta.card : ℝ) ≤
        2 * (1 + log ((∑ x : G, finsetIndicator X x * w x)⁻¹)) /
          eta ^ 2 := by simpa using hdim
    _ ≤ 2 * (1 + log R) / eta ^ 2 := by
      gcongr

/-- The finite capped-maximality step used by the local Chang argument. -/
theorem exists_capped_addDissociatedMod
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hneg : ∀ s ∈ S, -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  classical
  obtain ⟨Delta, hDeltaT, hDeltaMod, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hneg
  have hDeltaCard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_not_ge hnot
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaDim := hdim Gamma (hGammaDelta.trans hDeltaT)
      (hDeltaMod.mono hGammaDelta) (by simpa [hGammaCard])
    rw [hGammaCard] at hGammaDim
    exact (not_le_of_gt hDk) hGammaDim
  exact ⟨Delta, hDeltaT, hdim Delta hDeltaT hDeltaMod hDeltaCard, hcover⟩

/-! ## The unconditional local selector -/

/-- The local logarithmic dimension parameter.  Only the density of `X`
inside `B` occurs; there is no ambient-group cardinality. -/
def localChangDimension (B : BohrData G) (X : Finset G) (eta : ℝ) : ℝ :=
  2 * (1 + log (2 * (B.carrier.card : ℝ) / X.card)) / eta ^ 2

/-- The cap used to remove the apparent circularity in the smoothing
argument. -/
def localChangCap (B : BohrData G) (X : Finset G) (eta : ℝ) : ℕ :=
  ⌈localChangDimension B X eta⌉₊ + 1

/-- An explicit scale at which Bourgain's regular-dilate lemma is applied. -/
def localChangBaseScale (B : BohrData G) (X : Finset G)
    (eta : ℝ) : NNReal :=
  (100 * ((max B.rank 1 : ℕ) : NNReal) *
    (((2 * localChangCap B X eta + 1 : ℕ) : NNReal)))⁻¹

/-- **Relative Chang--Sanders selector.**  If `X` is nonempty inside a
rank-regular Bohr set `B`, then its `eta`-large spectrum is covered by the
signed span of at most

`2 * (1 + log (2 * |B| / |X|)) / eta^2`

new characters, modulo the half-large spectrum of an explicit regular
dilate of `B`.  In particular the logarithm contains no ambient-group
cardinality. -/
theorem exists_relativeLargeSpectrum_cover
    [DecidableEq G] (B : BohrData G) (hBreg : B.IsRankRegular)
    (X : Finset G) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ rho : NNReal, ∃ C : BohrData G,
      ∃ Delta : Finset (AddChar G ℂ),
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.dilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        ∀ psi ∈ Chang.largeSpectrum X eta,
          ∃ z ∈ Delta.addSpan,
            ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s := by
  classical
  let D : ℝ := localChangDimension B X eta
  let k : ℕ := localChangCap B X eta
  let d : ℕ := max B.rank 1
  let a : NNReal := localChangBaseScale B X eta
  obtain ⟨rho, hrhoHalf, hrhoOne, hregular⟩ :=
    (B.dilate a).exists_rankRegular_dilate
  let tau : NNReal := rho * a
  let C : BohrData G := B.dilate tau
  have hCreg : C.IsRankRegular := by
    simpa [C, tau] using hregular
  have hd : 0 < d := by simp [d]
  have hk : 0 < k := by simp [k, localChangCap]
  have ha : a =
      (100 * (d : NNReal) * (((2 * k + 1 : ℕ) : NNReal)))⁻¹ := by
    simp [a, localChangBaseScale, d, k]
  have hsmall : (((2 * k : ℕ) : NNReal) * tau) ≤
      1 / (100 * (d : NNReal)) := by
    have hkden : (0 : NNReal) < (((2 * k + 1 : ℕ) : NNReal)) := by positivity
    have hdb : (0 : NNReal) < 100 * (d : NNReal) := by positivity
    calc
      (((2 * k : ℕ) : NNReal) * tau) =
          ((2 * k : ℕ) : NNReal) * (rho * a) := rfl
      _ ≤ ((2 * k : ℕ) : NNReal) * (1 * a) := by gcongr
      _ = (((2 * k : ℕ) : NNReal) /
          (((2 * k + 1 : ℕ) : NNReal))) /
            (100 * (d : NNReal)) := by rw [ha]; field_simp
      _ ≤ 1 / (100 * (d : NNReal)) := by
        gcongr
        exact (div_le_one hkden).2 (by
          exact_mod_cast Nat.le_add_right (2 * k) 1)
  let T : Finset (AddChar G ℂ) := Chang.largeSpectrum X eta
  let S : Finset (AddChar G ℂ) :=
    Chang.largeSpectrum C.carrier (1 / 2)
  let w : G → ℝ := Erdos140.bohrSmoothingMeasure B tau (2 * k)
  let outer : Finset G :=
    (B.dilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier
  let c : ℝ := (outer.card : ℝ)⁻¹
  let R : ℝ := 2 * (B.carrier.card : ℝ) / X.card
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact Erdos140.bohrSmoothingMeasure_nonneg B tau (2 * k) x
  have hw1 : ∑ x : G, w x = 1 := by
    exact Erdos140.sum_bohrSmoothingMeasure B tau (2 * k)
  have hwconst : ∀ x ∈ B.carrier, w x = c := by
    intro x hx
    simpa [w, c, outer] using
      (Erdos140.bohrSmoothingMeasure_apply_of_mem B tau (2 * k) hx)
  have hOuterCard : outer.card ≤ 2 * B.carrier.card := by
    simpa [outer, d] using
      (Erdos140.card_dilate_one_add_le_two_mul hBreg (2 * k) hsmall)
  have hOuterPos : 0 < outer.card := by
    exact outer.card_pos.mpr (by
      simpa [outer] using
        (B.dilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier_nonempty)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hR : (c * X.card)⁻¹ ≤ R := by
    have hOr : (0 : ℝ) < outer.card := by exact_mod_cast hOuterPos
    have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hOr' : (outer.card : ℝ) ≤ 2 * B.carrier.card := by
      exact_mod_cast hOuterCard
    calc
      (c * (X.card : ℝ))⁻¹ = (outer.card : ℝ) / X.card := by
        dsimp [c]
        field_simp
      _ ≤ (2 * B.carrier.card : ℝ) / X.card :=
        (div_le_div_iff_of_pos_right hXr).2 hOr'
      _ = R := by simp [R]
  have hzero : (0 : AddChar G ℂ) ∈ S := by
    exact zero_mem_chang_largeSpectrum_half C.carrier
  have hneg : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    exact neg_mem_chang_largeSpectrum hs
  have hDk : D < (k : ℝ) := by
    calc
      D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
      _ < ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self ⌈D⌉₊
      _ = (k : ℝ) := by simp [k, localChangCap, D]
  have hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D := by
    intro Gamma hGammaT hGammaMod hGammaCard
    have hq : ∀ psi, psi ∉ S →
        ‖Erdos140.massCoeff w psi‖ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
      intro psi hpsi
      calc
        ‖Erdos140.massCoeff w psi‖ ≤
            ‖Erdos140.massCoeff
              (normalizedIndicator (B.dilate tau).carrier) psi‖ ^ (2 * k) := by
          exact Erdos140.norm_massCoeff_bohrSmoothingMeasure_le
            B tau (2 * k) psi
        _ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
          gcongr
          exact (Erdos140.norm_massCoeff_normalizedIndicator_lt_half_of_not_mem_largeSpectrum
            (B.dilate tau) psi (by simpa [S, C] using hpsi)).le
    have hweighted : IsWeightedDissociated w 1 Gamma := by
      apply hGammaMod.isWeightedDissociated_of_le_quarter_pow
        hw0 hw1 (by positivity) hq hGammaCard
      rw [pow_mul]
      norm_num
    have hcard := card_weightedDissociated_finsetIndicator_le
      B.carrier X hXB hX w c R eta hw0 hwconst hc hR heta Gamma
        hweighted (by simpa [T] using hGammaT)
    simpa [D, localChangDimension, R] using hcard
  obtain ⟨Delta, hDeltaT, hDeltaCard, hcover⟩ :=
    exists_capped_addDissociatedMod S T hzero hneg D k hDk hdim
  refine ⟨rho, C, Delta, hrhoHalf, hrhoOne, ?_, hCreg, ?_, ?_, ?_⟩
  · simp [C, tau, a]
  · simpa [D] using hDeltaCard
  · simpa [T] using hDeltaT
  · simpa [T, S] using hcover

#print axioms weighted_rudin_exp_ineq
#print axioms card_weightedDissociated_relativeLargeSpectrum_le
#print axioms card_weightedDissociated_finsetIndicator_le
#print axioms exists_capped_addDissociatedMod
#print axioms exists_relativeLargeSpectrum_cover

end Erdos140.RelativeChangSanders
