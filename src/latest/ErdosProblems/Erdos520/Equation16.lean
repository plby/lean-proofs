import ErdosProblems.Erdos520.ConditionalFiber
import ErdosProblems.Erdos520.FreshDoob
import ErdosProblems.Erdos520.MinkowskiIntegral
import ErdosProblems.Erdos520.RealSmooth
import ErdosProblems.Erdos520.ThinMomentAssembly
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# The concrete conditional thin-block moment estimate

This file joins the finite fresh-coordinate conditional expectation, Doob,
Bonami, inverse-square scaling, and thin Euler-product estimates.  The main
point of the first part is that the finite cube used in `FreshDoob` is not an
auxiliary probability model: it is exactly the conditional fiber of the
original infinite product measure over the old prime sigma algebra.
-/

/-- Real-valued integral Minkowski, derived from the nonnegative extended-real
form in `IntegralMinkowski`.  The explicit integrability assumptions are the
standard conditions needed to convert! all four `lintegral`s back to Bochner
integrals without an `∞` case. -/
theorem integral_Lp_integral_le
    {Z Ω' : Type*} [MeasurableSpace Z] [MeasurableSpace Ω']
    {ν : Measure Z} {μ' : Measure Ω'} [SFinite ν] [SFinite μ']
    {F : Z → Ω' → ℝ}
    (hF : Measurable (fun x : Z × Ω' ↦ F x.1 x.2))
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    {p : ℝ} (hp : 1 ≤ p)
    (h_integrable_inner : ∀ ω, Integrable (fun z ↦ F z ω) ν)
    (h_integrable_outer : Integrable
      (fun ω ↦ (∫ z, F z ω ∂ν) ^ p) μ')
    (h_integrable_slice : ∀ z, Integrable (fun ω ↦ F z ω ^ p) μ')
    (h_integrable_rhs : Integrable
      (fun z ↦ (∫ ω, F z ω ^ p ∂μ') ^ (1 / p)) ν) :
    (∫ ω, (∫ z, F z ω ∂ν) ^ p ∂μ') ^ (1 / p) ≤
      ∫ z, (∫ ω, F z ω ^ p ∂μ') ^ (1 / p) ∂ν := by
  let G : Z → Ω' → ℝ≥0∞ := fun z ω ↦ ENNReal.ofReal (F z ω)
  let A : Ω' → ℝ := fun ω ↦ ∫ z, F z ω ∂ν
  let B : Z → ℝ := fun z ↦ ∫ ω, F z ω ^ p ∂μ'
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hp_pos : 0 < p := zero_lt_one.trans_le hp
  have hG : Measurable (fun x : Z × Ω' ↦ G x.1 x.2) := by
    exact ENNReal.measurable_ofReal.comp hF
  have hA_nonneg (ω : Ω') : 0 ≤ A ω :=
    integral_nonneg fun z ↦ hF_nonneg z ω
  have hB_nonneg (z : Z) : 0 ≤ B z :=
    integral_nonneg fun ω ↦ Real.rpow_nonneg (hF_nonneg z ω) p
  have hinner (ω : Ω') :
      (∫⁻ z, G z ω ∂ν) = ENNReal.ofReal (A ω) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal (h_integrable_inner ω)
      (ae_of_all ν fun z ↦ hF_nonneg z ω)
  have hslice (z : Z) :
      (∫⁻ ω, G z ω ^ p ∂μ') = ENNReal.ofReal (B z) := by
    calc
      (∫⁻ ω, G z ω ^ p ∂μ') =
          ∫⁻ ω, ENNReal.ofReal (F z ω ^ p) ∂μ' := by
        apply lintegral_congr
        intro ω
        exact ENNReal.ofReal_rpow_of_nonneg (hF_nonneg z ω) hp0
      _ = ENNReal.ofReal (∫ ω, F z ω ^ p ∂μ') :=
        (ofReal_integral_eq_lintegral_ofReal (h_integrable_slice z)
          (ae_of_all μ' fun ω ↦ Real.rpow_nonneg (hF_nonneg z ω) p)).symm
      _ = ENNReal.ofReal (B z) := rfl
  have hleft :
      (∫⁻ ω, (∫⁻ z, G z ω ∂ν) ^ p ∂μ') =
        ENNReal.ofReal (∫ ω, A ω ^ p ∂μ') := by
    calc
      (∫⁻ ω, (∫⁻ z, G z ω ∂ν) ^ p ∂μ') =
          ∫⁻ ω, ENNReal.ofReal (A ω ^ p) ∂μ' := by
        apply lintegral_congr
        intro ω
        rw [hinner]
        exact ENNReal.ofReal_rpow_of_nonneg (hA_nonneg ω) hp0
      _ = ENNReal.ofReal (∫ ω, A ω ^ p ∂μ') :=
        (ofReal_integral_eq_lintegral_ofReal h_integrable_outer
          (ae_of_all μ' fun ω ↦ Real.rpow_nonneg (hA_nonneg ω) p)).symm
  have hright :
      (∫⁻ z, (∫⁻ ω, G z ω ^ p ∂μ') ^ (1 / p) ∂ν) =
        ENNReal.ofReal (∫ z, B z ^ (1 / p) ∂ν) := by
    calc
      (∫⁻ z, (∫⁻ ω, G z ω ^ p ∂μ') ^ (1 / p) ∂ν) =
          ∫⁻ z, ENNReal.ofReal (B z ^ (1 / p)) ∂ν := by
        apply lintegral_congr
        intro z
        rw [hslice]
        exact ENNReal.ofReal_rpow_of_nonneg (hB_nonneg z) (by positivity)
      _ = ENNReal.ofReal (∫ z, B z ^ (1 / p) ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal h_integrable_rhs
          (ae_of_all ν fun z ↦ Real.rpow_nonneg (hB_nonneg z) (1 / p))).symm
  have hmink := IntegralMinkowski.lintegral_Lp_lintegral_le hG hp (by
    rw [hleft]
    exact ENNReal.ofReal_ne_top)
  rw [hleft, hright] at hmink
  rw [ENNReal.ofReal_rpow_of_nonneg
    (integral_nonneg fun ω ↦ Real.rpow_nonneg (hA_nonneg ω) p)
    (by positivity)] at hmink
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg fun z ↦ Real.rpow_nonneg (hB_nonneg z) (1 / p))).mp hmink

/-- Natural-power specialization of `integral_Lp_integral_le`. -/
theorem integral_natLp_integral_le
    {Z Ω' : Type*} [MeasurableSpace Z] [MeasurableSpace Ω']
    {ν : Measure Z} {μ' : Measure Ω'} [SFinite ν] [SFinite μ']
    {F : Z → Ω' → ℝ}
    (hF : Measurable (fun x : Z × Ω' ↦ F x.1 x.2))
    (hF_nonneg : ∀ z ω, 0 ≤ F z ω)
    (r : ℕ) (hr : 1 ≤ r)
    (h_integrable_inner : ∀ ω, Integrable (fun z ↦ F z ω) ν)
    (h_integrable_outer : Integrable
      (fun ω ↦ (∫ z, F z ω ∂ν) ^ r) μ')
    (h_integrable_slice : ∀ z, Integrable (fun ω ↦ F z ω ^ r) μ')
    (h_integrable_rhs : Integrable
      (fun z ↦ (∫ ω, F z ω ^ r ∂μ') ^ (1 / (r : ℝ))) ν) :
    (∫ ω, (∫ z, F z ω ∂ν) ^ r ∂μ') ^ (1 / (r : ℝ)) ≤
      ∫ z, (∫ ω, F z ω ^ r ∂μ') ^ (1 / (r : ℝ)) ∂ν := by
  have hout : Integrable
      (fun ω ↦ (∫ z, F z ω ∂ν) ^ (r : ℝ)) μ' := by
    simpa only [Real.rpow_natCast] using! h_integrable_outer
  have hslice : ∀ z, Integrable (fun ω ↦ F z ω ^ (r : ℝ)) μ' := by
    intro z
    simpa only [Real.rpow_natCast] using! h_integrable_slice z
  have hrhs : Integrable
      (fun z ↦ (∫ ω, F z ω ^ (r : ℝ) ∂μ') ^ (1 / (r : ℝ))) ν := by
    simpa only [Real.rpow_natCast] using! h_integrable_rhs
  simpa only [Real.rpow_natCast] using!
    integral_Lp_integral_le hF hF_nonneg
      (show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr)
      h_integrable_inner hout hslice hrhs

private theorem Ψ_eq_of_eq_on_primesBelow {omega omega' : Omega}
    {z a : ℕ}
    (h : ∀ p ∈ (a + 1).primesBelow, omega p = omega' p) :
    Ψ omega z a = Ψ omega' z a := by
  classical
  simp_rw [Ψ_eq_sum_squarefreeSmoothSets]
  apply Finset.sum_congr rfl
  intro S hS
  unfold freshCharacter
  apply Finset.prod_congr rfl
  intro p hp
  have hpold : p ∈ (a + 1).primesBelow :=
    (mem_squarefreeSmoothSets.mp hS).1 hp
  simp only [ε, h p hpold]

/-- Replacing the signs in `(a,b]` does not change an `a`-smooth sum. -/
theorem Ψ_spliceFresh_old {a b z : ℕ} (old : Omega)
    (v : FreshCube a b) :
    Ψ (spliceFresh old v) z a = Ψ old z a := by
  apply Ψ_eq_of_eq_on_primesBelow
  intro p hpold
  have hpfresh : p ∉ freshPrimes a b := fun hpfresh =>
    Finset.disjoint_left.mp (primesBelow_succ_disjoint_freshPrimes a b)
      hpold hpfresh
  exact spliceFresh_of_not_mem old v hpfresh

/-- The terminal frozen smooth sum is literally the powerset-indexed Walsh
polynomial to which the concrete Bonami theorem applies. -/
theorem frozenSmoothTerminal_eq_freshFiberExpansion {a b : ℕ}
    (old : Omega) (z : ℕ) (hab : a ≤ b) (v : FreshCube a b) :
    frozenSmoothTerminal (a := a) (b := b) old z v =
      freshFiberExpansion old z a b v := by
  rw [frozenSmoothTerminal_eq_freshWalshExpansion old z hab]
  unfold freshWalshExpansion freshFiberExpansion powersetWalshEval
  apply Finset.sum_congr rfl
  intro S hS
  have hSsub : S ⊆ freshPrimes a b := Finset.mem_powerset.mp hS
  have hcharacter : finsetFiberCharacter (freshPrimes a b) v S =
      freshCharacter (spliceFresh old v) S := by
    unfold finsetFiberCharacter freshCharacter
    apply Finset.prod_congr rfl
    intro p hp
    rw [dif_pos (hSsub hp)]
    change (if v ⟨p, hSsub hp⟩ then (1 : ℝ) else -1) =
      (if spliceFresh old v p then (1 : ℝ) else -1)
    rw [spliceFresh_of_mem old v (hSsub hp)]
  rw [hcharacter]
  unfold freshCoefficient
  rw [Ψ_spliceFresh_old]
  ring

/-- `spliceFresh` is the `updateFinset` operation used by the conditional
fiber API. -/
theorem spliceFresh_eq_updateFinset {a b : ℕ} (old : Omega)
    (v : FreshCube a b) :
    spliceFresh old v = Function.updateFinset old (freshPrimes a b) v := by
  funext p
  by_cases hp : p ∈ freshPrimes a b
  · simp [spliceFresh, Function.updateFinset, hp]
  · simp [spliceFresh, Function.updateFinset, hp]

/-- A nonnegative finite maximum commutes with natural powers. -/
private theorem finset_sup'_pow_of_nonneg {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (n : ℕ) :
    (s.sup' hs f) ^ n = s.sup' hs (fun i ↦ f i ^ n) := by
  let g : ℝ → ℝ := fun x ↦ (max x 0) ^ n
  have hg_sup : ∀ x y : ℝ, g (x ⊔ y) = g x ⊔ g y := by
    intro x y
    rcases le_total x y with hxy | hyx
    · have hm : max x 0 ≤ max y 0 := max_le_max_right 0 hxy
      simp only [g, max_eq_right hxy]
      rw [max_eq_right (pow_le_pow_left₀ (by positivity) hm n)]
    · have hm : max y 0 ≤ max x 0 := max_le_max_right 0 hyx
      simp only [g, max_eq_left hyx]
      rw [max_eq_left (pow_le_pow_left₀ (by positivity) hm n)]
  have hsup_nonneg : 0 ≤ s.sup' hs f := by
    rcases hs with ⟨i, hi⟩
    exact (hf i hi).trans (Finset.le_sup' f hi)
  calc
    (s.sup' hs f) ^ n = g (s.sup' hs f) := by
      simp [g, max_eq_left hsup_nonneg]
    _ = s.sup' hs (g ∘ f) :=
      Finset.comp_sup'_eq_sup'_comp hs g hg_sup
    _ = s.sup' hs (fun i ↦ f i ^ n) := by
      apply Finset.sup'_congr hs rfl
      intro i hi
      simp [g, hf i hi]

/-- The square of the running maximum of the `r`th powers is the `r`th
power of the running maximum of the squares. -/
theorem finiteRunningMax_abs_pow_sq_eq
    {Ω' : Type*} (X : ℕ → Ω' → ℝ) (n r : ℕ) (v : Ω') :
    finiteRunningMax (fun k v ↦ |X k v| ^ r) n v ^ 2 =
      finiteRunningMax (fun k v ↦ |X k v| ^ 2) n v ^ r := by
  unfold finiteRunningMax
  rw [finset_sup'_pow_of_nonneg _ _ _
      (fun k _ ↦ pow_nonneg (abs_nonneg _) _) 2,
    finset_sup'_pow_of_nonneg _ _ _
      (fun k _ ↦ pow_nonneg (abs_nonneg _) _) r]
  apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
  intro k hk
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

/-- The actual (clamped) smooth-path maximum squared on a frozen fresh-prime
fiber.  The running range includes the old endpoint `a`; this harmlessly
dominates the paper's maximum over fresh primes only and is the natural
finite-time Doob process. -/
noncomputable def frozenSmoothPathMaxSq {a b : ℕ}
    (old : Omega) (z : ℕ) (v : FreshCube a b) : ℝ :=
  finiteRunningMax
    (fun k v ↦ |frozenSmoothPath (a := a) (b := b) old z k v| ^ 2) b v

/-- The squared `L^(2r)` root of the frozen smooth-path maximum. -/
noncomputable def frozenSmoothPathMaxMoment {a b : ℕ}
    (old : Omega) (z r : ℕ) : ℝ :=
  (∫ v, frozenSmoothPathMaxSq (a := a) (b := b) old z v ^ r
      ∂freshCubeLaw a b) ^ (1 / (r : ℝ))

/-- The squared `L^(2r)` root of the terminal smooth sum. -/
noncomputable def frozenSmoothTerminalMoment {a b : ℕ}
    (old : Omega) (z r : ℕ) : ℝ :=
  (∫ v, |frozenSmoothTerminal (a := a) (b := b) old z v| ^ (2 * r)
      ∂freshCubeLaw a b) ^ (1 / (r : ℝ))

theorem frozenSmoothPathMaxMoment_nonneg {a b : ℕ}
    (old : Omega) (z r : ℕ) :
    0 ≤ frozenSmoothPathMaxMoment (a := a) (b := b) old z r := by
  unfold frozenSmoothPathMaxMoment
  apply Real.rpow_nonneg
  exact integral_nonneg fun v ↦ pow_nonneg
    (by
      unfold frozenSmoothPathMaxSq finiteRunningMax
      exact (pow_nonneg (abs_nonneg (frozenSmoothPath old z 0 v)) 2).trans (Finset.le_sup'
        (fun k ↦ |frozenSmoothPath old z k v| ^ 2)
        (Finset.mem_range.mpr (Nat.zero_lt_succ b)))) _

theorem frozenSmoothTerminalMoment_nonneg {a b : ℕ}
    (old : Omega) (z r : ℕ) :
    0 ≤ frozenSmoothTerminalMoment (a := a) (b := b) old z r := by
  unfold frozenSmoothTerminalMoment
  apply Real.rpow_nonneg
  exact integral_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) _

/-- Rooted form of the concrete finite-fiber Doob estimate (17). -/
theorem frozenSmoothPathMaxMoment_le_terminal {a b : ℕ}
    (old : Omega) (z r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    frozenSmoothPathMaxMoment (a := a) (b := b) old z r ≤
      4 * frozenSmoothTerminalMoment (a := a) (b := b) old z r := by
  let A : ℝ := ∫ v, frozenSmoothPathMaxSq (a := a) (b := b) old z v ^ r
      ∂freshCubeLaw a b
  let B : ℝ := ∫ v, |frozenSmoothTerminal (a := a) (b := b) old z v| ^ (2 * r)
      ∂freshCubeLaw a b
  have hA : 0 ≤ A := integral_nonneg fun v ↦ pow_nonneg
    (by
      unfold frozenSmoothPathMaxSq finiteRunningMax
      exact (pow_nonneg (abs_nonneg (frozenSmoothPath old z 0 v)) 2).trans (Finset.le_sup'
        (fun k ↦ |frozenSmoothPath old z k v| ^ 2)
        (Finset.mem_range.mpr (Nat.zero_lt_succ b)))) _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ pow_nonneg (abs_nonneg _) _
  have hraw : A ≤ 4 * B := by
    have h := frozenSmoothPath_evenMoment_le old z r hab
    simpa only [A, B, frozenSmoothPathMaxSq,
      finiteRunningMax_abs_pow_sq_eq] using! h
  have hrReal : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hexp : 0 ≤ 1 / (r : ℝ) := by positivity
  have hroot : A ^ (1 / (r : ℝ)) ≤ (4 * B) ^ (1 / (r : ℝ)) :=
    Real.rpow_le_rpow hA hraw hexp
  have hquarter : (4 : ℝ) ^ (1 / (r : ℝ)) ≤ 4 := by
    apply Real.rpow_le_self_of_one_le (by norm_num)
    exact (div_le_one hrReal).2 (by exact_mod_cast hr)
  change A ^ (1 / (r : ℝ)) ≤ 4 * B ^ (1 / (r : ℝ))
  calc
    A ^ (1 / (r : ℝ)) ≤ (4 * B) ^ (1 / (r : ℝ)) := hroot
    _ = 4 ^ (1 / (r : ℝ)) * B ^ (1 / (r : ℝ)) :=
      Real.mul_rpow (by norm_num) hB
    _ ≤ 4 * B ^ (1 / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right hquarter (Real.rpow_nonneg hB _)

/-- Bonami (19) for the terminal frozen smooth sum, with the old
coefficients genuinely frozen at `old`. -/
theorem frozenSmoothTerminalMoment_le_bonami {a b : ℕ}
    (old : Omega) (z r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    frozenSmoothTerminalMoment (a := a) (b := b) old z r ≤
      ∑ S ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ S.card *
          freshCoefficient old z a S ^ 2 := by
  have hbon := freshFiberExpansion_bonami_integral r hr old z a b
  unfold frozenSmoothTerminalMoment
  have hint :
      (∫ v, |frozenSmoothTerminal (a := a) (b := b) old z v| ^ (2 * r)
          ∂freshCubeLaw a b) =
        ∫ v, |freshFiberExpansion old z a b v| ^ (2 * r)
          ∂Measure.pi (fun _ : freshPrimes a b ↦ coin) := by
    unfold freshCubeLaw
    apply integral_congr_ae
    exact ae_of_all _ fun v ↦ by
      change |frozenSmoothTerminal old z v| ^ (2 * r) =
        |freshFiberExpansion old z a b v| ^ (2 * r)
      rw [frozenSmoothTerminal_eq_freshFiberExpansion old z hab v]
  rw [hint]
  exact hbon

/-- The complete pointwise old-fiber Doob--Bonami composition.  This is the
probability-theoretic core of (16), before the `z`-integral is moved through
the moment root. -/
theorem frozenSmoothPathMaxMoment_le_bonami {a b : ℕ}
    (old : Omega) (z r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    frozenSmoothPathMaxMoment (a := a) (b := b) old z r ≤
      4 * ∑ S ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ S.card *
          freshCoefficient old z a S ^ 2 := by
  exact (frozenSmoothPathMaxMoment_le_terminal old z r hab hr).trans
    (mul_le_mul_of_nonneg_left
      (frozenSmoothTerminalMoment_le_bonami old z r hab hr) (by norm_num))

/-! ## Real cutoffs and the integrated block energy -/

/-- The frozen smooth-path maximum at a real cutoff. -/
noncomputable def realFrozenSmoothPathMaxSq {a b : ℕ}
    (old : Omega) (z : ℝ) (v : FreshCube a b) : ℝ :=
  frozenSmoothPathMaxSq (a := a) (b := b) old ⌊z⌋₊ v

/-- The rooted fresh-fiber moment at a real cutoff. -/
noncomputable def realFrozenSmoothPathMaxMoment {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) : ℝ :=
  frozenSmoothPathMaxMoment (a := a) (b := b) old ⌊z⌋₊ r

/-- The rooted terminal moment at a real cutoff. -/
noncomputable def realFrozenSmoothTerminalMoment {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) : ℝ :=
  frozenSmoothTerminalMoment (a := a) (b := b) old ⌊z⌋₊ r

theorem realFrozenSmoothPathMaxMoment_le_terminal {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r ≤
      4 * realFrozenSmoothTerminalMoment (a := a) (b := b) old z r := by
  exact frozenSmoothPathMaxMoment_le_terminal old ⌊z⌋₊ r hab hr

theorem realFrozenSmoothTerminalMoment_le_bonami {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    realFrozenSmoothTerminalMoment (a := a) (b := b) old z r ≤
      ∑ S ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ S.card *
          realFreshCoefficient old z a S ^ 2 := by
  have h := frozenSmoothTerminalMoment_le_bonami old ⌊z⌋₊ r hab hr
  simpa only [realFrozenSmoothTerminalMoment,
    realFreshCoefficient_eq_freshCoefficient_floor] using! h

theorem realFrozenSmoothPathMaxMoment_le_bonami {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r ≤
      4 * ∑ S ∈ (freshPrimes a b).powerset,
        ((2 * r - 1 : ℕ) : ℝ) ^ S.card *
          realFreshCoefficient old z a S ^ 2 := by
  exact (realFrozenSmoothPathMaxMoment_le_terminal old z r hab hr).trans
    (mul_le_mul_of_nonneg_left
      (realFrozenSmoothTerminalMoment_le_bonami old z r hab hr) (by norm_num))

/-- The global real-cutoff maximum for the clamped smooth path over the prime
block `(a,b]`. -/
noncomputable def realSmoothBlockMaxSq (a b : ℕ) (omega : Omega) (z : ℝ) : ℝ :=
  finiteRunningMax
    (fun k omega ↦ |ΨReal omega z (freshCutoff a b k)| ^ 2) b omega

/-- The concrete real-cutoff smooth block energy.  It is the (slightly
enlarged) version of (11) which includes the old endpoint `a`; hence it
dominates the strict fresh-prime maximum used in the paper. -/
noncomputable def realSmoothBlockEnergy (a b : ℕ) (omega : Omega) : ℝ :=
  (Real.log (b : ℝ))⁻¹ *
    ∫ z in Ioi (0 : ℝ), realSmoothBlockMaxSq a b omega z / z ^ 2

/-- The same block energy after the old coordinates are frozen and the fresh
coordinates are exposed as an explicit finite cube. -/
noncomputable def realFrozenSmoothBlockEnergy {a b : ℕ}
    (old : Omega) (v : FreshCube a b) : ℝ :=
  (Real.log (b : ℝ))⁻¹ *
    ∫ z in Ioi (0 : ℝ), realFrozenSmoothPathMaxSq old z v / z ^ 2

/-- The conditional `L^r` root of the concrete frozen block energy. -/
noncomputable def realFrozenSmoothBlockMomentRoot {a b : ℕ}
    (old : Omega) (r : ℕ) : ℝ :=
  (∫ v, realFrozenSmoothBlockEnergy (a := a) (b := b) old v ^ r
      ∂freshCubeLaw a b) ^ (1 / (r : ℝ))

theorem realFrozenSmoothPathMaxSq_nonneg {a b : ℕ}
    (old : Omega) (z : ℝ) (v : FreshCube a b) :
    0 ≤ realFrozenSmoothPathMaxSq old z v := by
  unfold realFrozenSmoothPathMaxSq frozenSmoothPathMaxSq finiteRunningMax
  exact (pow_nonneg
    (abs_nonneg (frozenSmoothPath old ⌊z⌋₊ 0 v)) 2).trans
      (Finset.le_sup'
        (fun k ↦ |frozenSmoothPath old ⌊z⌋₊ k v| ^ 2)
        (Finset.mem_range.mpr (Nat.zero_lt_succ b)))

theorem measurable_realFrozenSmoothPathMaxSq_cutoff {a b : ℕ}
    (old : Omega) (v : FreshCube a b) :
    Measurable fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v := by
  have hmeas : Measurable ((Finset.range (b + 1)).sup'
      Finset.nonempty_range_add_one (fun k z ↦
        |ΨReal (spliceFresh old v) z (freshCutoff a b k)| ^ 2)) := by
    apply Finset.measurable_sup' Finset.nonempty_range_add_one
    intro k hk
    exact ((measurable_ΨReal_cutoff (spliceFresh old v)
      (freshCutoff a b k)).norm.pow_const 2)
  convert! hmeas using 1
  funext z
  unfold realFrozenSmoothPathMaxSq frozenSmoothPathMaxSq finiteRunningMax
  rw [Finset.sup'_apply]
  rfl

theorem measurable_realFrozenSmoothPathMaxSq_joint {a b : ℕ}
    (old : Omega) :
    Measurable fun x : ℝ × FreshCube a b ↦
      realFrozenSmoothPathMaxSq old x.1 x.2 := by
  apply measurable_from_prod_countable_left
  intro v
  exact measurable_realFrozenSmoothPathMaxSq_cutoff old v

/-- Pulling a nonnegative constant out of a finite `L^r` moment root. -/
private theorem integral_pow_const_mul_root
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    (c : ℝ) (hc : 0 ≤ c) (g : Ω' → ℝ) (hg : ∀ ω, 0 ≤ g ω)
    (r : ℕ) (hr : 1 ≤ r) :
    (∫ ω, (c * g ω) ^ r ∂μ') ^ (1 / (r : ℝ)) =
      c * (∫ ω, g ω ^ r ∂μ') ^ (1 / (r : ℝ)) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hcPow : 0 ≤ c ^ r := pow_nonneg hc r
  have hInt : 0 ≤ ∫ ω, g ω ^ r ∂μ' :=
    integral_nonneg fun ω ↦ pow_nonneg (hg ω) r
  simp_rw [mul_pow]
  rw [integral_const_mul]
  rw [Real.mul_rpow hcPow hInt]
  have hroot : (c ^ r) ^ (1 / (r : ℝ)) = c := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hc]
    have hmul : (r : ℝ) * (1 / (r : ℝ)) = 1 := by
      field_simp
    rw [hmul]
    exact Real.rpow_one c
  rw [hroot]

/-- The `L^r` root of a slice of the inverse-square kernel is exactly the
pointwise rooted maximum divided by `z²`. -/
theorem realFrozenSmoothKernelMomentRoot {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) (hz : 0 < z) (hr : 1 ≤ r) :
    (∫ v, (realFrozenSmoothPathMaxSq old z v / z ^ 2) ^ r
        ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) =
      realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r / z ^ 2 := by
  have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
  calc
    (∫ v, (realFrozenSmoothPathMaxSq old z v / z ^ 2) ^ r
        ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) =
      (∫ v, ((z ^ 2)⁻¹ * realFrozenSmoothPathMaxSq old z v) ^ r
        ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) := by
          congr 2
          funext v
          rw [inv_mul_eq_div]
    _ = (z ^ 2)⁻¹ *
        (∫ v, realFrozenSmoothPathMaxSq old z v ^ r
          ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) :=
      integral_pow_const_mul_root (z ^ 2)⁻¹ (inv_nonneg.mpr hzsq.le)
        (realFrozenSmoothPathMaxSq old z) (realFrozenSmoothPathMaxSq_nonneg old z)
        r hr
    _ = realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r / z ^ 2 := by
      unfold realFrozenSmoothPathMaxMoment frozenSmoothPathMaxMoment
        realFrozenSmoothPathMaxSq
      rw [inv_mul_eq_div]

/-- Integral Minkowski for the concrete real-cutoff frozen smooth block.
This directly instantiates `IntegralMinkowski.lintegral_Lp_lintegral_le` via
the real-valued wrapper above. -/
theorem realFrozenSmoothBlock_minkowski {a b : ℕ}
    (old : Omega) (r : ℕ) (hr : 1 ≤ r)
    (hlog : 0 < Real.log (b : ℝ))
    (hkernel_integrable : ∀ v : FreshCube a b, IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v / z ^ 2)
      (Ioi (0 : ℝ)))
    (hmax_integrable : IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxMoment
        (a := a) (b := b) old z r / z ^ 2)
      (Ioi (0 : ℝ))) :
    realFrozenSmoothBlockMomentRoot (a := a) (b := b) old r ≤
      (Real.log (b : ℝ))⁻¹ *
        ∫ z in Ioi (0 : ℝ),
          realFrozenSmoothPathMaxMoment
            (a := a) (b := b) old z r / z ^ 2 := by
  let kernel : ℝ → FreshCube a b → ℝ := fun z v ↦
    realFrozenSmoothPathMaxSq old z v / z ^ 2
  let inner : FreshCube a b → ℝ := fun v ↦
    ∫ z in Ioi (0 : ℝ), kernel z v
  have hkernel_joint : Measurable fun x : ℝ × FreshCube a b ↦
      kernel x.1 x.2 := by
    exact (measurable_realFrozenSmoothPathMaxSq_joint old).div
      (measurable_fst.pow_const 2)
  have hkernel_nonneg : ∀ z v, 0 ≤ kernel z v := by
    intro z v
    exact div_nonneg (realFrozenSmoothPathMaxSq_nonneg old z v) (sq_nonneg z)
  have hrhs : Integrable
      (fun z ↦ (∫ v, kernel z v ^ r ∂freshCubeLaw a b) ^
        (1 / (r : ℝ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply hmax_integrable.congr
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun z hz ↦ by
      exact (realFrozenSmoothKernelMomentRoot
        (a := a) (b := b) old z r hz hr).symm
  have hmink :
      (∫ v, inner v ^ r ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) ≤
        ∫ z in Ioi (0 : ℝ),
          (∫ v, kernel z v ^ r ∂freshCubeLaw a b) ^
            (1 / (r : ℝ)) := by
    exact integral_natLp_integral_le
      (ν := volume.restrict (Ioi (0 : ℝ)))
      (μ' := freshCubeLaw a b) hkernel_joint hkernel_nonneg r hr
      hkernel_integrable Integrable.of_finite (fun _ ↦ Integrable.of_finite) hrhs
  have hrhs_eq :
      (∫ z in Ioi (0 : ℝ),
          (∫ v, kernel z v ^ r ∂freshCubeLaw a b) ^
            (1 / (r : ℝ))) =
        ∫ z in Ioi (0 : ℝ),
          realFrozenSmoothPathMaxMoment
            (a := a) (b := b) old z r / z ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    exact realFrozenSmoothKernelMomentRoot (a := a) (b := b) old z r hz hr
  rw [hrhs_eq] at hmink
  have hc : 0 ≤ (Real.log (b : ℝ))⁻¹ := inv_nonneg.mpr hlog.le
  have hinner_nonneg (v : FreshCube a b) : 0 ≤ inner v := by
    exact integral_nonneg fun z ↦ hkernel_nonneg z v
  have hroot_eq :
      realFrozenSmoothBlockMomentRoot (a := a) (b := b) old r =
        (Real.log (b : ℝ))⁻¹ *
          (∫ v, inner v ^ r ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) := by
    unfold realFrozenSmoothBlockMomentRoot realFrozenSmoothBlockEnergy
    change (∫ v, ((Real.log (b : ℝ))⁻¹ * inner v) ^ r
      ∂freshCubeLaw a b) ^ (1 / (r : ℝ)) = _
    exact integral_pow_const_mul_root _ hc inner hinner_nonneg r hr
  rw [hroot_eq]
  exact mul_le_mul_of_nonneg_left hmink hc

/-! ## Automatic inverse-square integrability -/

/-- A measurable function which vanishes below `1` and is `O(z⁻²)` above
`1` is integrable on the positive half-line. -/
private theorem integrableOn_Ioi_of_zero_below_one_of_bound_inv_sq
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hzero : ∀ z, 0 < z → z < 1 → f z = 0)
    (hbound : ∀ z, 1 < z → |f z| ≤ C / z ^ 2) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  have hnear : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo' (μ := volume) (by simp)]
    have heq : EqOn f 0 (Ioo (0 : ℝ) 1) := by
      intro z hz
      exact hzero z hz.1 hz.2
    exact (integrableOn_zero (μ := volume) (s := Ioo (0 : ℝ) 1)).congr_fun
      heq.symm measurableSet_Ioo
  have hfarMajor : IntegrableOn
      (fun z : ℝ ↦ C * z ^ (-2 : ℝ)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
  have hfar : IntegrableOn f (Ioi (1 : ℝ)) := by
    refine Integrable.mono' hfarMajor hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 < z := zero_lt_one.trans hz
    calc
      ‖f z‖ = |f z| := Real.norm_eq_abs _
      _ ≤ C / z ^ 2 := hbound z hz
      _ = C * z ^ (-2 : ℝ) := by
        rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
          Real.rpow_neg hz0.le, Real.rpow_two]
        ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hnear.union hfar

private theorem Ψ_zero_natCutoff (omega : Omega) (y : ℕ) :
    Ψ omega 0 y = 0 := by
  have hempty : Nat.smoothNumbersUpTo 0 (y + 1) = ∅ := by
    ext n
    simp only [Nat.mem_smoothNumbersUpTo, Finset.notMem_empty, iff_false]
    rintro ⟨hn, hsmooth⟩
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    exact (Nat.ne_zero_of_mem_smoothNumbers hsmooth) rfl
  unfold Ψ
  rw [hempty]
  simp

theorem ΨReal_eq_zero_of_lt_one (omega : Omega) (z : ℝ) (y : ℕ)
    (hz : z < 1) :
    ΨReal omega z y = 0 := by
  unfold ΨReal
  rw [Nat.floor_eq_zero.mpr hz]
  exact Ψ_zero_natCutoff omega y

/-- Uniform cutoff-independent bound by all subsets of the primes up to a
larger smoothness endpoint. -/
theorem abs_ΨReal_le_powerset_card_of_le (omega : Omega) (z : ℝ)
    {c b : ℕ} (hcb : c ≤ b) :
    |ΨReal omega z c| ≤ (((b + 1).primesBelow.powerset.card : ℕ) : ℝ) := by
  have hsub : squarefreeSmoothSets ⌊z⌋₊ c ⊆
      (b + 1).primesBelow.powerset := by
    intro S hS
    rw [Finset.mem_powerset]
    intro p hp
    have hpc := (mem_squarefreeSmoothSets.mp hS).1 hp
    have hpinfo := Nat.mem_primesBelow.mp hpc
    exact Nat.mem_primesBelow.mpr
      ⟨lt_of_lt_of_le hpinfo.1 (Nat.add_le_add_right hcb 1), hpinfo.2⟩
  have hcard := Finset.card_le_card hsub
  calc
    |ΨReal omega z c| = ‖Ψ omega ⌊z⌋₊ c‖ := by
      rw [ΨReal, Real.norm_eq_abs]
    _ ≤ (squarefreeSmoothSets ⌊z⌋₊ c).card :=
      norm_Ψ_le_card omega ⌊z⌋₊ c
    _ ≤ (((b + 1).primesBelow.powerset.card : ℕ) : ℝ) := by
      exact_mod_cast hcard

theorem realFrozenSmoothPathMaxSq_eq_zero_of_lt_one {a b : ℕ}
    (old : Omega) (v : FreshCube a b) {z : ℝ} (hz : z < 1) :
    realFrozenSmoothPathMaxSq old z v = 0 := by
  unfold realFrozenSmoothPathMaxSq frozenSmoothPathMaxSq finiteRunningMax
  calc
    (Finset.range (b + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ |frozenSmoothPath old ⌊z⌋₊ k v| ^ 2) =
      (Finset.range (b + 1)).sup' Finset.nonempty_range_add_one
        (fun _ ↦ (0 : ℝ)) := by
          apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
          intro k hk
          change |ΨReal (spliceFresh old v) z (freshCutoff a b k)| ^ 2 = 0
          rw [ΨReal_eq_zero_of_lt_one _ _ _ hz]
          norm_num
    _ = 0 := Finset.sup'_const Finset.nonempty_range_add_one 0

theorem realFrozenSmoothPathMaxSq_le_uniform {a b : ℕ}
    (old : Omega) (v : FreshCube a b) (z : ℝ) (hab : a ≤ b) :
    realFrozenSmoothPathMaxSq old z v ≤
      ((((b + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2 := by
  unfold realFrozenSmoothPathMaxSq frozenSmoothPathMaxSq finiteRunningMax
  apply Finset.sup'_le
  intro k hk
  change |ΨReal (spliceFresh old v) z (freshCutoff a b k)| ^ 2 ≤ _
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_ΨReal_le_powerset_card_of_le _ _ (freshCutoff_le hab)) 2

/-- The inverse-square path-maximum kernel is automatically integrable. -/
theorem integrableOn_realFrozenSmoothPathMaxSq_div_sq {a b : ℕ}
    (old : Omega) (v : FreshCube a b) (hab : a ≤ b) :
    IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v / z ^ 2)
      (Ioi (0 : ℝ)) := by
  let C : ℝ := ((((b + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2
  apply integrableOn_Ioi_of_zero_below_one_of_bound_inv_sq
    (fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v / z ^ 2)
    ((measurable_realFrozenSmoothPathMaxSq_cutoff old v).div
      (measurable_id.pow_const 2)) C (by positivity)
  · intro z hz0 hz1
    rw [realFrozenSmoothPathMaxSq_eq_zero_of_lt_one old v hz1]
    simp
  · intro z hz
    rw [abs_of_nonneg (div_nonneg
      (realFrozenSmoothPathMaxSq_nonneg old z v) (sq_nonneg z))]
    exact div_le_div_of_nonneg_right
      (by simpa only [C] using! realFrozenSmoothPathMaxSq_le_uniform old v z hab)
      (sq_nonneg z)

theorem measurable_realFrozenSmoothPathMaxMoment_cutoff {a b : ℕ}
    (old : Omega) (r : ℕ) :
    Measurable fun z : ℝ ↦
      realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r := by
  let J : ℝ → ℝ := fun z ↦
    ∫ v, realFrozenSmoothPathMaxSq old z v ^ r ∂freshCubeLaw a b
  have hJ : Measurable J := by
    have heq : J = fun z ↦ fintypeAverage
        (fun v : FreshCube a b ↦ realFrozenSmoothPathMaxSq old z v ^ r) := by
      funext z
      unfold J freshCubeLaw
      rw [integral_coin_eq_fintypeAverage]
    rw [heq]
    unfold fintypeAverage
    apply Measurable.div_const
    exact Finset.measurable_fun_sum Finset.univ fun v hv ↦
      (measurable_realFrozenSmoothPathMaxSq_cutoff old v).pow_const r
  change Measurable fun z : ℝ ↦ J z ^ (1 / (r : ℝ))
  exact hJ.pow measurable_const

theorem realFrozenSmoothPathMaxMoment_nonneg_real {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) :
    0 ≤ realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r := by
  exact frozenSmoothPathMaxMoment_nonneg old ⌊z⌋₊ r

theorem realFrozenSmoothPathMaxMoment_eq_zero_of_lt_one {a b : ℕ}
    (old : Omega) {z : ℝ} (r : ℕ) (hr : 1 ≤ r) (hz : z < 1) :
    realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r = 0 := by
  unfold realFrozenSmoothPathMaxMoment frozenSmoothPathMaxMoment
  have hzero : ∀ v : FreshCube a b,
      frozenSmoothPathMaxSq old ⌊z⌋₊ v = 0 := by
    intro v
    exact realFrozenSmoothPathMaxSq_eq_zero_of_lt_one old v hz
  simp_rw [hzero]
  have hrpos : 0 < r := lt_of_lt_of_le Nat.zero_lt_one hr
  have hrRealNe : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
  rw [zero_pow hrpos.ne', integral_zero]
  exact Real.zero_rpow (one_div_ne_zero hrRealNe)

theorem realFrozenSmoothPathMaxMoment_le_uniform {a b : ℕ}
    (old : Omega) (z : ℝ) (r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    realFrozenSmoothPathMaxMoment (a := a) (b := b) old z r ≤
      ((((b + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2 := by
  let C : ℝ := ((((b + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2
  let J : ℝ := ∫ v, realFrozenSmoothPathMaxSq old z v ^ r
    ∂freshCubeLaw a b
  have hC : 0 ≤ C := by positivity
  have hJ : 0 ≤ J := integral_nonneg fun v ↦
    pow_nonneg (realFrozenSmoothPathMaxSq_nonneg old z v) r
  have hle : J ≤ C ^ r := by
    calc
      J ≤ ∫ _v : FreshCube a b, C ^ r ∂freshCubeLaw a b := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro v
        exact pow_le_pow_left₀ (realFrozenSmoothPathMaxSq_nonneg old z v)
          (by simpa only [C] using!
            realFrozenSmoothPathMaxSq_le_uniform old v z hab) r
      _ = C ^ r := by simp
  have hroot := Real.rpow_le_rpow hJ hle (by positivity : 0 ≤ 1 / (r : ℝ))
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hCr : (C ^ r) ^ (1 / (r : ℝ)) = C := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
    have hmul : (r : ℝ) * (1 / (r : ℝ)) = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  unfold realFrozenSmoothPathMaxMoment frozenSmoothPathMaxMoment
  change J ^ (1 / (r : ℝ)) ≤ C
  exact hroot.trans_eq hCr

/-- The rooted maximal-moment inverse-square kernel is also automatically
integrable. -/
theorem integrableOn_realFrozenSmoothPathMaxMoment_div_sq_uniform {a b : ℕ}
    (old : Omega) (r : ℕ) (hab : a ≤ b) (hr : 1 ≤ r) :
    IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxMoment
        (a := a) (b := b) old z r / z ^ 2)
      (Ioi (0 : ℝ)) := by
  let C : ℝ := ((((b + 1).primesBelow.powerset.card : ℕ) : ℝ)) ^ 2
  apply integrableOn_Ioi_of_zero_below_one_of_bound_inv_sq
    (fun z : ℝ ↦ realFrozenSmoothPathMaxMoment
      (a := a) (b := b) old z r / z ^ 2)
    ((measurable_realFrozenSmoothPathMaxMoment_cutoff old r).div
      (measurable_id.pow_const 2)) C (by positivity)
  · intro z hz0 hz1
    rw [realFrozenSmoothPathMaxMoment_eq_zero_of_lt_one old r hr hz1]
    simp
  · intro z hz
    rw [abs_of_nonneg (div_nonneg
      (realFrozenSmoothPathMaxMoment_nonneg_real old z r) (sq_nonneg z))]
    exact div_le_div_of_nonneg_right
      (by simpa only [C] using!
        realFrozenSmoothPathMaxMoment_le_uniform old z r hab hr)
      (sq_nonneg z)

theorem realSmoothBlockMaxSq_spliceFresh {a b : ℕ}
    (old : Omega) (v : FreshCube a b) (z : ℝ) :
    realSmoothBlockMaxSq a b (spliceFresh old v) z =
      realFrozenSmoothPathMaxSq old z v := by
  rfl

theorem realSmoothBlockEnergy_spliceFresh {a b : ℕ}
    (old : Omega) (v : FreshCube a b) :
    realSmoothBlockEnergy a b (spliceFresh old v) =
      realFrozenSmoothBlockEnergy old v := by
  rfl

/-- The finite-cube moment is exactly the fresh-coordinate fiber average of
the global block energy. -/
theorem finiteCoinFiberIntegral_realSmoothBlockEnergy_pow {a b r : ℕ}
    (old : Omega) :
    finiteCoinFiberIntegral (freshPrimes a b)
        (fun omega ↦ realSmoothBlockEnergy a b omega ^ r) old =
      ∫ v, realFrozenSmoothBlockEnergy (a := a) (b := b) old v ^ r
        ∂freshCubeLaw a b := by
  unfold finiteCoinFiberIntegral freshCubeLaw
  apply integral_congr_ae
  exact ae_of_all _ fun v ↦ by
    change realSmoothBlockEnergy a b
        (Function.updateFinset old (freshPrimes a b) v) ^ r =
      realFrozenSmoothBlockEnergy old v ^ r
    rw [← spliceFresh_eq_updateFinset old v,
      realSmoothBlockEnergy_spliceFresh]

/-- Exact conditional-fiber identity for the concrete block energy.  This is
the bridge that turns every pointwise old-assignment estimate below into an
almost-everywhere conditional-expectation estimate on the original product
space. -/
theorem condExp_realSmoothBlockEnergy_pow_ae_eq_fiber {a b r : ℕ}
    (hdep : StronglyMeasurable[Filtration.piFinset
      ((a + 1).primesBelow ∪ freshPrimes a b)]
        (fun omega ↦ realSmoothBlockEnergy a b omega ^ r)) :
    μ[(fun omega ↦ realSmoothBlockEnergy a b omega ^ r) |
        Filtration.piFinset ((a + 1).primesBelow)] =ᵐ[μ]
      fun old ↦ ∫ v,
        realFrozenSmoothBlockEnergy (a := a) (b := b) old v ^ r
          ∂freshCubeLaw a b := by
  have hfiber := freshPrimeFiberIntegral_ae_eq_condExp (a := a) (b := b) hdep
  filter_upwards [hfiber] with old hold
  rw [← hold]
  exact finiteCoinFiberIntegral_realSmoothBlockEnergy_pow old

/-! ## Pointwise analytic assembly -/

/-- All probability-theoretic inputs to (16), including integral Minkowski,
are now concrete.  This lower-level assembly theorem keeps the routine kernel
integrability conditions explicit, alongside the Parseval/`I` comparison and
the thin-schedule reciprocal-prime bound. -/
theorem realFrozenSmoothBlockMomentRoot_le
    {ell r a b : ℕ} (hell : 0 < ell) (hr : 2 ≤ r)
    (old : Omega) {I Cparseval Crecip : ℝ}
    (hab : a ≤ b) (hlog : 0 < Real.log (b : ℝ))
    (hI : 0 ≤ I) (hCparseval : 0 ≤ Cparseval)
    (hCrecip : 0 ≤ Crecip)
    (hkernel_integrable : ∀ v : FreshCube a b, IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v / z ^ 2)
      (Ioi (0 : ℝ)))
    (hmax_integrable : IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxMoment
        (a := a) (b := b) old z r / z ^ 2)
      (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ S ∈ (freshPrimes a b).powerset,
      IntegrableOn
        (fun z : ℝ ↦ |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 / z ^ 2)
        (Ioi (0 : ℝ)))
    (hparseval :
      (∫ w in Ioi (0 : ℝ), |ΨReal old w a| ^ 2 / w ^ 2) /
          Real.log (b : ℝ) ≤ Cparseval * I)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    let C := max (4 * Cparseval) (2 * Crecip)
    realFrozenSmoothBlockMomentRoot (a := a) (b := b) old r ≤
      C * Real.exp (C * r / ell) * I := by
  have hminkowski := realFrozenSmoothBlock_minkowski old r (by omega)
    hlog hkernel_integrable hmax_integrable
  refine thinMoment_analytic_assembly_of_dilations
    (ell := ell) (r := r) (a := a) (b := b)
    (momentRoot := realFrozenSmoothBlockMomentRoot
      (a := a) (b := b) old r)
    (maxMoment := fun z ↦ realFrozenSmoothPathMaxMoment
      (a := a) (b := b) old z r)
    (terminalMoment := fun z ↦ realFrozenSmoothTerminalMoment
      (a := a) (b := b) old z r)
    (baseSq := fun w ↦ |ΨReal old w a| ^ 2)
    hell hr hlog hI hCparseval hCrecip hminkowski ?_ ?_
      hmax_integrable hcoeff_integrable hparseval hrecip
  · intro z hz
    exact realFrozenSmoothPathMaxMoment_le_terminal old z r hab (by omega)
  · intro z hz
    simpa only [realFreshCoefficient, sq_abs] using!
      realFrozenSmoothTerminalMoment_le_bonami old z r hab (by omega)

/-- Conditional form of the concrete thin-block estimate (16).

The random variable on the left is the actual real-cutoff smooth-block
energy, and its conditional expectation is taken in the original infinite
Rademacher product space.  Doob, coefficient-weighted Bonami, the finite
fiber/conditional-expectation identification, inverse-square scaling, and the
thin Euler product have all been discharged.  This lower-level form keeps the
routine kernel-integrability side conditions visible, together with the
paper-facing Parseval/energy comparison and reciprocal-prime estimate; the
`autoIntegrable` wrapper below removes the first two kernel conditions. -/
theorem conditional_realSmoothBlockMoment_le
    {ell r a b : ℕ} (hell : 0 < ell) (hr : 2 ≤ r)
    (Iold : Omega → ℝ) {Cparseval Crecip : ℝ}
    (hab : a ≤ b) (hlog : 0 < Real.log (b : ℝ))
    (hCparseval : 0 ≤ Cparseval) (hCrecip : 0 ≤ Crecip)
    (hI_nonneg : ∀ old, 0 ≤ Iold old)
    (hdep : StronglyMeasurable[Filtration.piFinset
      ((a + 1).primesBelow ∪ freshPrimes a b)]
        (fun omega ↦ realSmoothBlockEnergy a b omega ^ r))
    (hkernel_integrable : ∀ old (v : FreshCube a b), IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxSq old z v / z ^ 2)
      (Ioi (0 : ℝ)))
    (hmax_integrable : ∀ old, IntegrableOn
      (fun z : ℝ ↦ realFrozenSmoothPathMaxMoment
        (a := a) (b := b) old z r / z ^ 2)
      (Ioi (0 : ℝ)))
    (hcoeff_integrable : ∀ old S,
      S ∈ (freshPrimes a b).powerset →
      IntegrableOn
        (fun z : ℝ ↦ |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 / z ^ 2)
        (Ioi (0 : ℝ)))
    (hparseval : ∀ old,
      (∫ w in Ioi (0 : ℝ), |ΨReal old w a| ^ 2 / w ^ 2) /
          Real.log (b : ℝ) ≤ Cparseval * Iold old)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    let C := max (4 * Cparseval) (2 * Crecip)
    ∀ᵐ old ∂μ,
      (μ[(fun omega ↦ realSmoothBlockEnergy a b omega ^ r) |
          Filtration.piFinset ((a + 1).primesBelow)] old) ^
            (1 / (r : ℝ)) ≤
        C * Real.exp (C * r / ell) * Iold old := by
  let C := max (4 * Cparseval) (2 * Crecip)
  have hfiber := condExp_realSmoothBlockEnergy_pow_ae_eq_fiber hdep
  filter_upwards [hfiber] with old hold
  rw [hold]
  exact realFrozenSmoothBlockMomentRoot_le hell hr old hab hlog
    (hI_nonneg old) hCparseval hCrecip (hkernel_integrable old)
    (hmax_integrable old) (hcoeff_integrable old) (hparseval old) hrecip

/-- Public equation-(16) endpoint with the Minkowski kernel and maximal-root
integrability discharged automatically.  Only finite-coordinate
measurability, coefficient integrability, and the two paper-facing schedule
comparisons remain as arguments; the companion `Equation16Helpers` file
closes the first two. -/
theorem conditional_realSmoothBlockMoment_le_autoIntegrable
    {ell r a b : ℕ} (hell : 0 < ell) (hr : 2 ≤ r)
    (Iold : Omega → ℝ) {Cparseval Crecip : ℝ}
    (hab : a ≤ b) (hlog : 0 < Real.log (b : ℝ))
    (hCparseval : 0 ≤ Cparseval) (hCrecip : 0 ≤ Crecip)
    (hI_nonneg : ∀ old, 0 ≤ Iold old)
    (hdep : StronglyMeasurable[Filtration.piFinset
      ((a + 1).primesBelow ∪ freshPrimes a b)]
        (fun omega ↦ realSmoothBlockEnergy a b omega ^ r))
    (hcoeff_integrable : ∀ old S,
      S ∈ (freshPrimes a b).powerset →
      IntegrableOn
        (fun z : ℝ ↦ |ΨReal old (z / (freshProduct S : ℝ)) a| ^ 2 / z ^ 2)
        (Ioi (0 : ℝ)))
    (hparseval : ∀ old,
      (∫ w in Ioi (0 : ℝ), |ΨReal old w a| ^ 2 / w ^ 2) /
          Real.log (b : ℝ) ≤ Cparseval * Iold old)
    (hrecip : freshReciprocalSum a b ≤ Crecip / ell) :
    let C := max (4 * Cparseval) (2 * Crecip)
    ∀ᵐ old ∂μ,
      (μ[(fun omega ↦ realSmoothBlockEnergy a b omega ^ r) |
          Filtration.piFinset ((a + 1).primesBelow)] old) ^
            (1 / (r : ℝ)) ≤
        C * Real.exp (C * r / ell) * Iold old := by
  exact conditional_realSmoothBlockMoment_le hell hr Iold hab hlog
    hCparseval hCrecip hI_nonneg hdep
    (fun old v ↦ integrableOn_realFrozenSmoothPathMaxSq_div_sq old v hab)
    (fun old ↦ integrableOn_realFrozenSmoothPathMaxMoment_div_sq_uniform
      old r hab (by omega))
    hcoeff_integrable hparseval hrecip

end Problem520
end Erdos
