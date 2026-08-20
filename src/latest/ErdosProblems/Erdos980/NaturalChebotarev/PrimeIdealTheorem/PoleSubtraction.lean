/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.ContinuedZeta.Basic
import Mathlib.Analysis.Meromorphic.LogDeriv

/-!
# Removing the pole of the Dedekind zeta logarithmic derivative

If `Z` has a simple pole at `1`, the logarithmic derivative of
`H(s) = (s - 1) Z(s)` is

`H'/H = 1 / (s - 1) + Z'/Z`.

Consequently `-H'/H` is the continuous extension of
`-Z'/Z - 1 / (s - 1)` across `1`, provided that the regularized function `H`
does not vanish.  This file isolates that analytic argument.  The arithmetic
zero-free theorem is deliberately passed as an explicit hypothesis, so that the
argument can be reused independently of the particular proof of nonvanishing.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem.PoleSubtraction

open Complex Filter NumberField
open scoped Topology

noncomputable section

/-- The closed half-plane on which the pole-subtracted logarithmic derivative is
continued. -/
def closedOneHalfPlane : Set ℂ := {s : ℂ | 1 ≤ s.re}

/-- The half-plane of absolute convergence of a Dedekind zeta function. -/
def openOneHalfPlane : Set ℂ := {s : ℂ | 1 < s.re}

/-- A nonvanishing holomorphic function has a continuous negative logarithmic
derivative on every smaller set.  Requiring holomorphy on an open set is enough to
obtain continuity of the derivative by the complex Cauchy integral theorem. -/
theorem continuousOn_neg_logDeriv_of_differentiableOn_open
    {H : ℂ → ℂ} {U S : Set ℂ} (hU : IsOpen U)
    (hH : DifferentiableOn ℂ H U) (hSU : S ⊆ U)
    (hH0 : ∀ s ∈ S, H s ≠ 0) :
    ContinuousOn (fun s : ℂ ↦ -logDeriv H s) S := by
  have hderiv : ContinuousOn (deriv H) S :=
    (hH.deriv hU).continuousOn.mono hSU
  have hfun : ContinuousOn H S := hH.continuousOn.mono hSU
  change ContinuousOn (-(deriv H / H)) S
  exact (hderiv.div hfun hH0).neg

/-- The canonical pole-subtracted logarithmic derivative.  It is defined at the
pole by differentiating the analytic regularization, rather than by assigning a
special value by hand. -/
def poleSubtractedDedekindLogDeriv
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  -logDeriv (ContinuedZeta.continuedDedekindZetaOneRegularized K) s

/-- Nonvanishing of the continued zeta function on the closed half-plane away
from `1` implies nonvanishing of its one-pole regularization everywhere on that
half-plane. -/
theorem regularized_ne_zero_of_continuedDedekindZeta_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (hζ : ∀ s : ℂ, 1 ≤ s.re → s ≠ 1 →
      ContinuedZeta.continuedDedekindZeta K s ≠ 0) :
    ∀ s ∈ closedOneHalfPlane,
      ContinuedZeta.continuedDedekindZetaOneRegularized K s ≠ 0 := by
  intro s hs
  by_cases hs1 : s = 1
  · simpa only [hs1] using
      ContinuedZeta.continuedDedekindZetaOneRegularized_one_ne_zero K
  · have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      norm_num [closedOneHalfPlane] at hs
    rw [ContinuedZeta.continuedDedekindZetaOneRegularized_eq K hs0 hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (hζ s hs hs1)

/-- The canonical pole-subtracted logarithmic derivative is continuous on the
closed half-plane once the continued zeta function is known to be zero-free there
away from its pole. -/
theorem continuousOn_poleSubtractedDedekindLogDeriv
    (K : Type*) [Field K] [NumberField K]
    (hζ : ∀ s : ℂ, 1 ≤ s.re → s ≠ 1 →
      ContinuedZeta.continuedDedekindZeta K s ≠ 0) :
    ContinuousOn (poleSubtractedDedekindLogDeriv K) closedOneHalfPlane := by
  apply continuousOn_neg_logDeriv_of_differentiableOn_open
      (U := ({0} : Set ℂ)ᶜ)
  · exact isClosed_singleton.isOpen_compl
  · intro s hs
    exact (ContinuedZeta.differentiableAt_continuedDedekindZetaOneRegularized K
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs)).differentiableWithinAt
  · intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hs0
    subst s
    norm_num [closedOneHalfPlane] at hs
  · exact regularized_ne_zero_of_continuedDedekindZeta_ne_zero K hζ

/-- On the open half-plane, the canonical continuous function is the expected
pole-subtracted logarithmic derivative of the ordinary Dedekind zeta function. -/
theorem poleSubtractedDedekindLogDeriv_eq
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    poleSubtractedDedekindLogDeriv K s =
      -logDeriv (NumberField.dedekindZeta K) s - 1 / (s - 1) := by
  have hopen : IsOpen openOneHalfPlane := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hs_mem : s ∈ openOneHalfPlane := hs
  have hright : ∀ᶠ z in 𝓝 s, z ∈ openOneHalfPlane := hopen.mem_nhds hs_mem
  have hreg : ContinuedZeta.continuedDedekindZetaOneRegularized K =ᶠ[𝓝 s]
      fun z : ℂ ↦ (z - 1) * NumberField.dedekindZeta K z := by
    filter_upwards [hright] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      norm_num [openOneHalfPlane] at hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num [openOneHalfPlane] at hz
    rw [ContinuedZeta.continuedDedekindZetaOneRegularized_eq K hz0 hz1,
      ContinuedZeta.continuedDedekindZeta_eq_dedekindZeta K hz]
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hζ0 : NumberField.dedekindZeta K s ≠ 0 :=
    DedekindResidue.dedekindZeta_ne_zero_of_one_lt_re K hs
  have hHdiff : DifferentiableAt ℂ
      (ContinuedZeta.continuedDedekindZetaOneRegularized K) s :=
    ContinuedZeta.differentiableAt_continuedDedekindZetaOneRegularized K (by
      intro h
      subst s
      norm_num at hs)
  have hquot : NumberField.dedekindZeta K =ᶠ[𝓝 s] (fun z : ℂ ↦
      ContinuedZeta.continuedDedekindZetaOneRegularized K z / (z - 1)) := by
    filter_upwards [hreg, eventually_ne_nhds hs1] with z hz hz1
    symm
    rw [hz]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz1)
  have hζdiff : DifferentiableAt ℂ (NumberField.dedekindZeta K) s :=
    (hHdiff.div (differentiableAt_id.sub_const 1) hsub).congr_of_eventuallyEq hquot
  have hlogreg : logDeriv
      (ContinuedZeta.continuedDedekindZetaOneRegularized K) s =
      logDeriv (fun z : ℂ ↦ (z - 1) * NumberField.dedekindZeta K z) s :=
    (logDeriv_congr_nhds hreg).self_of_nhds
  have hmul :
      logDeriv (fun z : ℂ ↦ (z - 1) * NumberField.dedekindZeta K z) s =
        logDeriv (fun z : ℂ ↦ z - 1) s +
          logDeriv (NumberField.dedekindZeta K) s :=
    logDeriv_mul (f := fun z : ℂ ↦ z - 1)
      (g := NumberField.dedekindZeta K) s hsub hζ0
        (differentiableAt_id.sub_const 1) hζdiff
  rw [poleSubtractedDedekindLogDeriv, hlogreg, hmul]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  ring

/-- Existential interface used by Tauberian arguments: the pole-subtracted
logarithmic derivative has a continuous extension to `Re s ≥ 1`, and this
extension agrees with the Dirichlet-series expression on `Re s > 1`. -/
theorem exists_continuous_poleSubtractedDedekindLogDeriv
    (K : Type*) [Field K] [NumberField K]
    (hζ : ∀ s : ℂ, 1 ≤ s.re → s ≠ 1 →
      ContinuedZeta.continuedDedekindZeta K s ≠ 0) :
    ∃ G : ℂ → ℂ,
      ContinuousOn G closedOneHalfPlane ∧
      Set.EqOn G
        (fun s : ℂ ↦ -logDeriv (NumberField.dedekindZeta K) s - 1 / (s - 1))
        openOneHalfPlane := by
  refine ⟨poleSubtractedDedekindLogDeriv K,
    continuousOn_poleSubtractedDedekindLogDeriv K hζ, ?_⟩
  intro s hs
  exact poleSubtractedDedekindLogDeriv_eq K hs

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem.PoleSubtraction
