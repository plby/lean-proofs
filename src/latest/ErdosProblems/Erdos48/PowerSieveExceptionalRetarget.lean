/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveExceptionalWitness
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap

/-!
# Retargeting the Page-exceptional conductor

A Page zero at scale `Q` remains in the (wider) Page window when the scale
is lowered to its own conductor.  Because the endpoint construction now
selects the conductor canonically from the whole Page window, rerunning it
at that conductor excludes exactly the same modulus, rather than the empty
window sentinel `0`.

The retained Page width also makes every such character quadratic.  The
effective quadratic real-zero gap therefore forces exceptional conductors
to tend to infinity with the original Page scale.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators
open BoundedGaps.Maynard

noncomputable section

/-- The explicit denominator from the effective quadratic real-zero gap. -/
def retargetQuadraticGapDenom (m : ℕ) : ℝ :=
  (2 ^ 22 : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) ^ 4

theorem retargetQuadraticGapDenom_pos {m : ℕ} (hm : 1 < m) :
    0 < retargetQuadraticGapDenom m := by
  unfold retargetQuadraticGapDenom
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm)
  positivity

/-- Lowering the Page scale from `Q` to the conductor of the retained zero
only widens the real interval. -/
theorem PageExceptionalWitness.retarget_to_modulus
    {Q m : ℕ} {c : ℝ} (hc : 0 < c)
    (h : PageExceptionalWitness Q m c) :
    PageExceptionalWitness m m c := by
  obtain ⟨z, hzmod, hzQ, hzbeta⟩ := h
  have hmgt : 1 < m := by simpa only [hzmod] using z.modulus_gt_one
  have hQgt : 1 < Q := hmgt.trans_le (hzmod ▸ hzQ)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hmgt)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQgt)
  have hlogle : Real.log (m : ℝ) ≤ Real.log (Q : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (hzmod ▸ hzQ)
  have hdiv : c / Real.log (Q : ℝ) ≤ c / Real.log (m : ℝ) := by
    rw [div_le_div_iff₀ hlogQ hlogm]
    exact mul_le_mul_of_nonneg_left hlogle hc.le
  refine ⟨z, hzmod, ?_, ?_⟩
  · simpa only [hzmod] using (le_refl m)
  · linarith

/-- A canonical Page selection must equal the conductor of every supplied
witness in its window. -/
theorem PageConductorSelection.eq_of_witness
    {Q selected m : ℕ} {c : ℝ}
    (hselection : PageConductorSelection Q selected c)
    (hwitness : PageExceptionalWitness Q m c) :
    m = selected := by
  obtain ⟨z, hzmod, hzPage⟩ := hwitness
  exact hzmod.symm.trans (hselection.1 z hzPage)

/-- The `1/40` complementary-mass form used by the literal bad-root
prefix argument.  In the good branch every conductor in the interval has
endpoint mass at most `x/20`; otherwise the unique omitted conductor is
retained together with its Page witness. -/
theorem endpoint_pointwise_twentieth_or_exceptional_with_pageWitness
    {Q x selected : ℕ} {c : ℝ}
    (_hselectedQ : selected ≤ Q)
    (hsum :
      (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ selected),
          primitiveEndpointMass x q) ≤ ((x : ℝ) / 40))
    (hwitness : selected = 0 ∨ PageExceptionalWitness Q selected c) :
    (∀ q ∈ Finset.Ioc 1 Q,
        primitiveEndpointMass x q ≤ (x : ℝ) / 20) ∨
      ∃ m ∈ Finset.Ioc 1 Q,
        (x : ℝ) / 20 < primitiveEndpointMass x m ∧
          (∑ q ∈ (Finset.Ioc 1 Q).filter (fun q ↦ q ≠ m),
              primitiveEndpointMass x q) ≤ ((x : ℝ) / 40) ∧
          PageExceptionalWitness Q m c := by
  by_cases hselected : selected ∈ Finset.Ioc 1 Q
  · by_cases hselectedGood :
        primitiveEndpointMass x selected ≤ (x : ℝ) / 20
    · left
      intro q hq
      by_cases hqSelected : q = selected
      · simpa only [hqSelected] using hselectedGood
      · have hqFilter :
            q ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ selected) :=
          Finset.mem_filter.mpr ⟨hq, hqSelected⟩
        have hqSum : primitiveEndpointMass x q ≤
            ∑ d ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ selected),
              primitiveEndpointMass x d :=
          Finset.single_le_sum
            (fun d _ ↦ primitiveEndpointMass_nonneg x d) hqFilter
        exact hqSum.trans (hsum.trans (by
          have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
          linarith))
    · right
      have hw : PageExceptionalWitness Q selected c := by
        rcases hwitness with hzero | hw
        · have hgt := (Finset.mem_Ioc.mp hselected).1
          omega
        · exact hw
      exact ⟨selected, hselected, lt_of_not_ge hselectedGood, hsum, hw⟩
  · left
    intro q hq
    have hqSelected : q ≠ selected := fun h ↦ hselected (h ▸ hq)
    have hqFilter :
        q ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ selected) :=
      Finset.mem_filter.mpr ⟨hq, hqSelected⟩
    have hqSum : primitiveEndpointMass x q ≤
        ∑ d ∈ (Finset.Ioc 1 Q).filter (fun d ↦ d ≠ selected),
          primitiveEndpointMass x d :=
      Finset.single_le_sum
        (fun d _ ↦ primitiveEndpointMass_nonneg x d) hqFilter
    exact hqSum.trans (hsum.trans (by
      have hx : (0 : ℝ) ≤ (x : ℝ) := by positivity
      linarith))

/-- A retained Page witness for the canonically selected width satisfies
the effective logarithmic conductor bound. -/
theorem PageExceptionalWitness.log_scale_lt_quadraticGapDenom
    {Q m : ℕ} {c : ℝ} (hQ : 3 ≤ Q) (hc : 0 < c)
    (hquadratic : PageWindowIsQuadratic c)
    (h : PageExceptionalWitness Q m c) :
    Real.log (Q : ℝ) < c * retargetQuadraticGapDenom m := by
  obtain ⟨z, hzmod, hzPage⟩ := h
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hD : 0 < retargetQuadraticGapDenom z.modulus :=
    retargetQuadraticGapDenom_pos z.modulus_gt_one
  have hgap :
      1 / retargetQuadraticGapDenom z.modulus ≤ 1 - z.beta := by
    simpa only [retargetQuadraticGapDenom] using
      BoundedGaps.Maynard.effectiveQuadraticRealZeroGap
        z.modulus_gt_one z.character z.ne_one
          (hquadratic Q hQ z hzPage) z.beta_lt_one.le z.isZero
  have hpage : 1 - z.beta < c / Real.log (Q : ℝ) := by
    linarith [hzPage.2]
  have hquot :
      1 / retargetQuadraticGapDenom z.modulus <
        c / Real.log (Q : ℝ) := hgap.trans_lt hpage
  rw [div_lt_div_iff₀ hD hlogQ] at hquot
  simpa only [one_mul, hzmod] using hquot

theorem retargetQuadraticGapDenom_nonneg (m : ℕ) :
    0 ≤ retargetQuadraticGapDenom m := by
  unfold retargetQuadraticGapDenom
  positivity

/-- Uniform conductor growth: for every fixed bound `M`, all Page witnesses
at sufficiently large scales have conductor at least `M`. -/
theorem eventually_pageExceptionalWitness_modulus_ge
    {c : ℝ} (hc : 0 < c) (hquadratic : PageWindowIsQuadratic c)
    (M : ℕ) :
    ∀ᶠ Q : ℕ in atTop, ∀ m : ℕ,
      PageExceptionalWitness Q m c → M ≤ m := by
  let D : ℝ := c * ∑ k ∈ Finset.range (M + 1), retargetQuadraticGapDenom k
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop D
  filter_upwards [hlog, eventually_ge_atTop (3 : ℕ)] with Q hlogQ hQ m hm
  by_contra hMm
  have hmM : m < M := by omega
  have hmRange : m ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have hsingle : retargetQuadraticGapDenom m ≤
      ∑ k ∈ Finset.range (M + 1), retargetQuadraticGapDenom k :=
    Finset.single_le_sum
      (fun k _ ↦ retargetQuadraticGapDenom_nonneg k) hmRange
  have hscaled : c * retargetQuadraticGapDenom m ≤ D := by
    dsimp [D]
    exact mul_le_mul_of_nonneg_left hsingle hc.le
  have hstrict :=
    PageExceptionalWitness.log_scale_lt_quadraticGapDenom hQ hc hquadratic hm
  have hlogQ' : D ≤ Real.log (Q : ℝ) := by
    simpa only [Function.comp_apply] using hlogQ
  linarith

/-- The same conductor-growth statement at the power-sieve Page scale
`Q = n^240`. -/
theorem eventually_powerSieve_pageExceptionalWitness_modulus_ge
    {c : ℝ} (hc : 0 < c) (hquadratic : PageWindowIsQuadratic c)
    (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      PageExceptionalWitness (n ^ 240) m c → M ≤ m := by
  have hpow : Tendsto (fun n : ℕ ↦ n ^ 240) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with n hn
    exact (le_max_right 1 b).trans hn |>.trans
      (Nat.le_pow (by norm_num : 0 < (240 : ℕ)))
  exact hpow.eventually
    (eventually_pageExceptionalWitness_modulus_ge hc hquadratic M)

/-- Retargeting a Page witness to its own conductor identifies the omitted
conductor in the endpoint estimate and hence gives the small complementary
endpoint mass there.  The exponent is written as `240 * L`, exactly the
power-sieve scale `powerSieveX m L`. -/
theorem eventually_powerSieveEndpoint_retarget_exceptional_above
    (Lmin : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧ PageWindowIsQuadratic cPage ∧
      ∃ L : ℕ, Lmin ≤ L ∧
        ∀ᶠ m : ℕ in atTop, ∀ Q : ℕ,
          PageExceptionalWitness Q m cPage →
            (∑ q ∈ (Finset.Ioc 1 m).filter (fun q ↦ q ≠ m),
                primitiveEndpointMass (powerSieveX m L) q) ≤
              ((powerSieveX m L : ℕ) : ℝ) / 20 := by
  obtain ⟨cPage, hcPage, hquadratic, E, _hE64, hEmin, hEdiv, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_selection
      (1 / 20 : ℝ) (by norm_num) (240 * Lmin)
  obtain ⟨L, hEL⟩ := hEdiv
  have hLmin : Lmin ≤ L := by
    rw [hEL] at hEmin
    omega
  refine ⟨cPage, hcPage, hquadratic, L, hLmin, ?_⟩
  filter_upwards [hscale] with m hm Q hQm
  obtain ⟨selected, hselected, hmass, _hwitness, hselection⟩ := hm
  have hretarget := hQm.retarget_to_modulus hcPage
  have heq : m = selected := hselection.eq_of_witness hretarget
  subst selected
  simpa only [one_div, inv_mul_eq_div, hEL, pow_mul, powerSieveX] using hmass

/-- A synchronized power-sieve endpoint dichotomy.  The original endpoint
estimate, its Page witness, conductor growth, and the retargeted estimate all
come from one invocation of the canonical-selection theorem, so the Page
width is definitionally the same in both branches. -/
theorem eventually_powerSieveEndpoint_good_or_exceptional_with_retarget_above
    (Lmin : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧ PageWindowIsQuadratic cPage ∧
      ∃ L Lretarget : ℕ,
        64 ≤ L ∧ Lmin ≤ L ∧ L = 240 * Lretarget ∧
        ∀ᶠ n : ℕ in atTop,
          (∀ q ∈ Finset.Ioc 1 (n ^ 240),
              primitiveEndpointMass (powerSieveX n L) q ≤
                ((powerSieveX n L : ℕ) : ℝ) / 10) ∨
            ∃ m ∈ Finset.Ioc 1 (n ^ 240),
              ((powerSieveX n L : ℕ) : ℝ) / 10 <
                  primitiveEndpointMass (powerSieveX n L) m ∧
                (∑ q ∈ (Finset.Ioc 1 (n ^ 240)).filter (fun q ↦ q ≠ m),
                    primitiveEndpointMass (powerSieveX n L) q) ≤
                  ((powerSieveX n L : ℕ) : ℝ) / 20 ∧
                PageExceptionalWitness (n ^ 240) m cPage ∧
                (∑ q ∈ (Finset.Ioc 1 m).filter (fun q ↦ q ≠ m),
                    primitiveEndpointMass (powerSieveX m Lretarget) q) ≤
                  ((powerSieveX m Lretarget : ℕ) : ℝ) / 20 := by
  obtain ⟨cPage, hcPage, hquadratic, L, hL64, hLmin, hLdiv, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_selection
      (1 / 20 : ℝ) (by norm_num) Lmin
  obtain ⟨Lretarget, hLretarget⟩ := hLdiv
  obtain ⟨N, hscaleN⟩ := eventually_atTop.1 hscale
  have hgrowth :=
    eventually_powerSieve_pageExceptionalWitness_modulus_ge
      hcPage hquadratic N
  have hpow : Tendsto (fun n : ℕ ↦ n ^ 240) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with n hn
    exact (le_max_right 1 b).trans hn |>.trans
      (Nat.le_pow (by norm_num : 0 < (240 : ℕ)))
  have horiginal := hpow.eventually hscale
  refine ⟨cPage, hcPage, hquadratic, L, Lretarget,
    hL64, hLmin, hLretarget, ?_⟩
  filter_upwards [horiginal, hgrowth] with n hn hgrowthN
  obtain ⟨selected, hselected, hmass, hwitness, _hselection⟩ := hn
  have hmassOriginal :
      (∑ q ∈ (Finset.Ioc 1 (n ^ 240)).filter (fun q ↦ q ≠ selected),
          primitiveEndpointMass (powerSieveX n L) q) ≤
        ((powerSieveX n L : ℕ) : ℝ) / 20 := by
    simpa only [one_div, inv_mul_eq_div, powerSieveX, pow_mul] using hmass
  rcases endpoint_good_or_exceptional_with_pageWitness
      hselected hmassOriginal hwitness with hgood | hexceptional
  · exact Or.inl hgood
  · right
    obtain ⟨m, hmMem, hmbad, hmComplement, hmWitness⟩ := hexceptional
    have hmN : N ≤ m := hgrowthN m hmWitness
    obtain ⟨retargetSelected, _hretargetSelected, hretargetMass,
        _hretargetWitness, hretargetSelection⟩ := hscaleN m hmN
    have hmRetargetWitness := hmWitness.retarget_to_modulus hcPage
    have heq : m = retargetSelected :=
      hretargetSelection.eq_of_witness hmRetargetWitness
    subst retargetSelected
    have hretargetMass' :
        (∑ q ∈ (Finset.Ioc 1 m).filter (fun q ↦ q ≠ m),
            primitiveEndpointMass (powerSieveX m Lretarget) q) ≤
          ((powerSieveX m Lretarget : ℕ) : ℝ) / 20 := by
      simpa only [one_div, inv_mul_eq_div, hLretarget,
        powerSieveX] using hretargetMass
    exact ⟨m, hmMem, hmbad, hmComplement, hmWitness, hretargetMass'⟩

/-- Pointwise endpoint packaging for `PowerSieveBadRootPrefix`.  The first
branch supplies the literal constructor's endpoint-good predicate on the
original Page range.  In the retargeted branch the exceptional conductor
is at least the arbitrarily prescribed `M`, and every other conductor up to
that new base has endpoint mass at most one twentieth of the retargeted
power-sieve scale. -/
theorem eventually_powerSieveEndpoint_pointwise_or_retarget_uniform_above
    (Lmin : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧ PageWindowIsQuadratic cPage ∧
      ∃ L Lretarget : ℕ,
        64 ≤ L ∧ 64 ≤ Lretarget ∧ Lmin ≤ Lretarget ∧
          L = 240 * Lretarget ∧
        ∀ M : ℕ, ∀ᶠ n : ℕ in atTop,
          (∀ q ∈ Finset.Ioc 1 (n ^ 240),
              primitiveEndpointMass (powerSieveX n L) q ≤
                ((powerSieveX n L : ℕ) : ℝ) / 20) ∨
            ∃ m ∈ Finset.Ioc 1 (n ^ 240),
              M ≤ m ∧
                ((powerSieveX n L : ℕ) : ℝ) / 20 <
                  primitiveEndpointMass (powerSieveX n L) m ∧
                PageExceptionalWitness (n ^ 240) m cPage ∧
                ∀ q ∈ Finset.Ioc 1 m, q ≠ m →
                  primitiveEndpointMass (powerSieveX m Lretarget) q ≤
                    ((powerSieveX m Lretarget : ℕ) : ℝ) / 20 := by
  obtain ⟨cPage, hcPage, hquadratic, L, hL64, hLmin, hLdiv, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_selection
      (1 / 40 : ℝ) (by norm_num) (240 * max 64 Lmin)
  obtain ⟨Lretarget, hLretarget⟩ := hLdiv
  have hLretargetMax : max 64 Lmin ≤ Lretarget := by
    rw [hLretarget] at hLmin
    omega
  have hLretarget64 : 64 ≤ Lretarget :=
    (le_max_left 64 Lmin).trans hLretargetMax
  have hLretargetMin : Lmin ≤ Lretarget :=
    (le_max_right 64 Lmin).trans hLretargetMax
  obtain ⟨N, hscaleN⟩ := eventually_atTop.1 hscale
  have hpow : Tendsto (fun n : ℕ ↦ n ^ 240) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with n hn
    exact (le_max_right 1 b).trans hn |>.trans
      (Nat.le_pow (by norm_num : 0 < (240 : ℕ)))
  have horiginal := hpow.eventually hscale
  refine ⟨cPage, hcPage, hquadratic, L, Lretarget,
    hL64, hLretarget64, hLretargetMin, hLretarget, ?_⟩
  intro M
  have hgrowth :=
    eventually_powerSieve_pageExceptionalWitness_modulus_ge
      hcPage hquadratic (max N M)
  filter_upwards [horiginal, hgrowth] with n hn hgrowthN
  obtain ⟨selected, hselected, hmass, hwitness, _hselection⟩ := hn
  have hmassOriginal :
      (∑ q ∈ (Finset.Ioc 1 (n ^ 240)).filter (fun q ↦ q ≠ selected),
          primitiveEndpointMass (powerSieveX n L) q) ≤
        ((powerSieveX n L : ℕ) : ℝ) / 40 := by
    simpa only [one_div, inv_mul_eq_div, powerSieveX, pow_mul] using hmass
  rcases endpoint_pointwise_twentieth_or_exceptional_with_pageWitness
      hselected hmassOriginal hwitness with hgood | hexceptional
  · exact Or.inl hgood
  · right
    obtain ⟨m, hmMem, hmbad, _hmComplement, hmWitness⟩ := hexceptional
    have hmMax : max N M ≤ m := hgrowthN m hmWitness
    have hmN : N ≤ m := (le_max_left N M).trans hmMax
    have hmM : M ≤ m := (le_max_right N M).trans hmMax
    obtain ⟨retargetSelected, _hretargetSelected, hretargetMass,
        _hretargetWitness, hretargetSelection⟩ := hscaleN m hmN
    have hmRetargetWitness := hmWitness.retarget_to_modulus hcPage
    have heq : m = retargetSelected :=
      hretargetSelection.eq_of_witness hmRetargetWitness
    subst retargetSelected
    have hretargetMass' :
        (∑ q ∈ (Finset.Ioc 1 m).filter (fun q ↦ q ≠ m),
            primitiveEndpointMass (powerSieveX m Lretarget) q) ≤
          ((powerSieveX m Lretarget : ℕ) : ℝ) / 40 := by
      simpa only [one_div, inv_mul_eq_div, hLretarget,
        powerSieveX] using hretargetMass
    refine ⟨m, hmMem, hmM, hmbad, hmWitness, ?_⟩
    intro q hq hqm
    have hqFilter : q ∈
        (Finset.Ioc 1 m).filter (fun d ↦ d ≠ m) :=
      Finset.mem_filter.mpr ⟨hq, hqm⟩
    have hqSum : primitiveEndpointMass (powerSieveX m Lretarget) q ≤
        ∑ d ∈ (Finset.Ioc 1 m).filter (fun d ↦ d ≠ m),
          primitiveEndpointMass (powerSieveX m Lretarget) d :=
      Finset.single_le_sum
        (fun d _ ↦ primitiveEndpointMass_nonneg
          (powerSieveX m Lretarget) d) hqFilter
    exact hqSum.trans (hretargetMass'.trans (by
      have hx : (0 : ℝ) ≤ ((powerSieveX m Lretarget : ℕ) : ℝ) := by
        positivity
      linarith))

/-- Fixed-cutoff projection of
`eventually_powerSieveEndpoint_pointwise_or_retarget_uniform_above`. -/
theorem eventually_powerSieveEndpoint_pointwise_or_retarget_above
    (Lmin M : ℕ) :
    ∃ cPage : ℝ, 0 < cPage ∧ PageWindowIsQuadratic cPage ∧
      ∃ L Lretarget : ℕ,
        64 ≤ L ∧ 64 ≤ Lretarget ∧ Lmin ≤ Lretarget ∧
          L = 240 * Lretarget ∧
        ∀ᶠ n : ℕ in atTop,
          (∀ q ∈ Finset.Ioc 1 (n ^ 240),
              primitiveEndpointMass (powerSieveX n L) q ≤
                ((powerSieveX n L : ℕ) : ℝ) / 20) ∨
            ∃ m ∈ Finset.Ioc 1 (n ^ 240),
              M ≤ m ∧
                ((powerSieveX n L : ℕ) : ℝ) / 20 <
                  primitiveEndpointMass (powerSieveX n L) m ∧
                PageExceptionalWitness (n ^ 240) m cPage ∧
                ∀ q ∈ Finset.Ioc 1 m, q ≠ m →
                  primitiveEndpointMass (powerSieveX m Lretarget) q ≤
                    ((powerSieveX m Lretarget : ℕ) : ℝ) / 20 := by
  obtain ⟨cPage, hcPage, hquadratic, L, Lretarget,
      hL64, hLretarget64, hLretargetMin, hLretarget, hmain⟩ :=
    eventually_powerSieveEndpoint_pointwise_or_retarget_uniform_above Lmin
  exact ⟨cPage, hcPage, hquadratic, L, Lretarget,
    hL64, hLretarget64, hLretargetMin, hLretarget, hmain M⟩

end

end Erdos48
