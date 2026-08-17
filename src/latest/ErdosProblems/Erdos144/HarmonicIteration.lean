/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.Harmonic

/-!
# Finite stage iteration for the harmonic model

This file joins the exact old/fresh block factorization with the affine
bad-mass recurrence.  The analytic regularity estimate remains an explicit
hypothesis.  Unused coordinates between the old and fresh blocks only help:
failure is antitone when the ambient Bernoulli coordinate set is enlarged.
-/

open scoped BigOperators

namespace Erdos144.HarmonicIteration

noncomputable section

attribute [local instance] Classical.propDecidable

open HarmonicProb

/-- For a monotone success property, enlarging the ambient coordinate set
can only decrease its failure probability. -/
theorem failure_prob_le_of_ambient_subset
    {I K : Finset ℕ} (hIK : I ⊆ K) (hK : ∀ n ∈ K, 1 ≤ n)
    (Success : Finset ℕ → Prop)
    (hmono : ∀ S T : Finset ℕ, S ⊆ T → Success S → Success T) :
    prob K (fun T ↦ ¬ Success T) ≤ prob I (fun T ↦ ¬ Success T) := by
  calc
    prob K (fun T ↦ ¬ Success T) ≤
        prob K (fun T ↦ ¬ Success (T ∩ I)) := by
      apply prob_mono K (fun T ↦ ¬ Success T)
        (fun T ↦ ¬ Success (T ∩ I)) hK
      intro T hfail hsuccess
      exact hfail (hmono (T ∩ I) T Finset.inter_subset_left hsuccess)
    _ = prob I (fun T ↦ ¬ Success T) :=
      Erdos144.HarmonicRegularity.prob_inter_eq K I
        (fun T ↦ ¬ Success T) hIK

/-- One stage of a nested block iteration, including marginalization across
any gap between `I j ∪ J j` and `I (j+1)`. -/
theorem failure_probability_stage_recurrence
    (I J : ℕ → Finset ℕ)
    (Success : Finset ℕ → Prop)
    (Irregular : ℕ → Finset ℕ → Prop)
    (Samples : ℕ → Finset ℕ → Finset (Finset ℕ))
    (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hdisj : ∀ j, Disjoint (I j) (J j))
    (hIpos : ∀ j n, n ∈ I j → 1 ≤ n)
    (hJpos : ∀ j n, n ∈ J j → 1 ≤ n)
    (hnested : ∀ j, I j ∪ J j ⊆ I (j + 1))
    (hmono : ∀ S T : Finset ℕ, S ⊆ T → Success S → Success T)
    (hSamples : ∀ j B, B ∈ (I j).powerset → Samples j B ⊆ (J j).powerset)
    (hforce : ∀ j B, B ∈ (I j).powerset → ¬ Success B →
      ¬ Irregular j B → ∀ F ∈ Samples j B, Success (B ∪ F))
    (hmass : ∀ j B, B ∈ (I j).powerset → ¬ Success B →
      ¬ Irregular j B →
        q ≤ prob (J j) (fun F ↦ F ∈ Samples j B))
    (hIrregular : ∀ j,
      prob (I j) (fun B ↦ ¬ Success B ∧ Irregular j B) ≤ δ) :
    ∀ j, prob (I (j + 1)) (fun T ↦ ¬ Success T) ≤
      (1 - q) * prob (I j) (fun T ↦ ¬ Success T) + q * δ := by
  intro j
  calc
    prob (I (j + 1)) (fun T ↦ ¬ Success T) ≤
        prob (I j ∪ J j) (fun T ↦ ¬ Success T) :=
      failure_prob_le_of_ambient_subset (hnested j) (hIpos (j + 1))
        Success hmono
    _ ≤ (1 - q) * prob (I j) (fun T ↦ ¬ Success T) + q * δ :=
      Erdos144.HarmonicFactorization.extension_bad_bound_of_sampleFamilies
        (hdisj j) (hIpos j) (hJpos j) Success (Irregular j)
        (Samples j) q δ hq0 hq1
        (fun {_S _T} hST hS ↦ hmono _S _T hST hS)
        (hSamples j) (hforce j)
        (hmass j) (hIrregular j)

/-- End-to-end finite iteration.  If every regular bad history has fresh
success mass at least `q`, while irregular bad histories have mass at most
`δ`, then after `L` stages the failure mass is at most
`(1-q)^L + δ`. -/
theorem failure_probability_after_stages
    (I J : ℕ → Finset ℕ)
    (Success : Finset ℕ → Prop)
    (Irregular : ℕ → Finset ℕ → Prop)
    (Samples : ℕ → Finset ℕ → Finset (Finset ℕ))
    (q δ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hδ0 : 0 ≤ δ)
    (hdisj : ∀ j, Disjoint (I j) (J j))
    (hIpos : ∀ j n, n ∈ I j → 1 ≤ n)
    (hJpos : ∀ j n, n ∈ J j → 1 ≤ n)
    (hnested : ∀ j, I j ∪ J j ⊆ I (j + 1))
    (hmono : ∀ S T : Finset ℕ, S ⊆ T → Success S → Success T)
    (hSamples : ∀ j B, B ∈ (I j).powerset → Samples j B ⊆ (J j).powerset)
    (hforce : ∀ j B, B ∈ (I j).powerset → ¬ Success B →
      ¬ Irregular j B → ∀ F ∈ Samples j B, Success (B ∪ F))
    (hmass : ∀ j B, B ∈ (I j).powerset → ¬ Success B →
      ¬ Irregular j B →
        q ≤ prob (J j) (fun F ↦ F ∈ Samples j B))
    (hIrregular : ∀ j,
      prob (I j) (fun B ↦ ¬ Success B ∧ Irregular j B) ≤ δ)
    (L : ℕ) :
    prob (I L) (fun T ↦ ¬ Success T) ≤ (1 - q) ^ L + δ := by
  let b : ℕ → ℝ := fun j ↦ prob (I j) (fun T ↦ ¬ Success T)
  have hb0 : b 0 ≤ 1 := prob_le_one (I 0) _ (hIpos 0)
  have hstep : ∀ j, b (j + 1) ≤ (1 - q) * b j + q * δ :=
    failure_probability_stage_recurrence I J Success Irregular Samples q δ
      hq0 hq1 hdisj hIpos hJpos hnested hmono hSamples hforce hmass hIrregular
  simpa [b] using
    (Erdos144.HarmonicBlocks.affine_recurrence_bound_one
      hq0 hq1 hδ0 hb0 hstep L)

/-! ## The concrete Maier--Tenenbaum rate -/

/-- Fresh success rate used in the explicit iteration. -/
def xiFreshRate (xi : ℕ) : ℝ :=
  1 / (27 * (xi : ℝ) ^ 2)

theorem xiFreshRate_nonneg (xi : ℕ) : 0 ≤ xiFreshRate xi := by
  simp [xiFreshRate]

theorem xiFreshRate_le_one {xi : ℕ} (hxi : 0 < xi) :
    xiFreshRate xi ≤ 1 := by
  have hxiR : (1 : ℝ) ≤ xi := by exact_mod_cast hxi
  rw [xiFreshRate]
  apply (div_le_one₀ (by positivity)).2
  nlinarith [sq_nonneg ((xi : ℝ) - 1)]

theorem xiFreshRate_mul_cube {xi : ℕ} (hxi : 0 < xi) :
    xiFreshRate xi * (xi ^ 3 : ℕ) = (xi : ℝ) / 27 := by
  have hxiR : (xi : ℝ) ≠ 0 := by exact_mod_cast hxi.ne'
  simp only [xiFreshRate, Nat.cast_pow]
  field_simp

/-- The geometric remainder after `xi^3` stages is exponentially small. -/
theorem xi_cube_geometric_le_exp {xi : ℕ} (hxi : 0 < xi) :
    (1 - xiFreshRate xi) ^ (xi ^ 3) ≤
      Real.exp (-(xi : ℝ) / 27) := by
  let q := xiFreshRate xi
  have hq1 : q ≤ 1 := xiFreshRate_le_one hxi
  have hbase0 : 0 ≤ 1 - q := by linarith
  have hbase : 1 - q ≤ Real.exp (-q) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-q)
  calc
    (1 - xiFreshRate xi) ^ (xi ^ 3) = (1 - q) ^ (xi ^ 3) := rfl
    _ ≤ Real.exp (-q) ^ (xi ^ 3) :=
      pow_le_pow_left₀ hbase0 hbase _
    _ = Real.exp (-(q * (xi ^ 3 : ℕ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (-(xi : ℝ) / 27) := by
      rw [show q * (xi ^ 3 : ℕ) = (xi : ℝ) / 27 by
        simpa [q] using xiFreshRate_mul_cube hxi]
      congr 1
      ring

/-! ## Concrete harmonic stages -/

/-- One concrete Maier--Tenenbaum stage.  The old reservoir is the full
interval `(C, D j]`, the fresh block is `(xi * D j, 3 * xi * D j]`, and
unused coordinates in the next reservoir are removed by marginalization. -/
theorem harmonic_failure_probability_stage_recurrence
    (C s xi : ℕ) (D R : ℕ → ℕ) (delta : ℝ)
    (hD : ∀ j, 0 < D j) (hxi2 : 2 ≤ xi)
    (hxiD : ∀ j, xi < D j)
    (hnested : ∀ j,
      Finset.Ioc C (D j) ∪ Finset.Ioc (xi * D j) (3 * (xi * D j)) ⊆
        Finset.Ioc C (D (j + 1)))
    (hstates : ∀ j B, B ∈ (Finset.Ioc C (D j)).powerset →
      ¬ Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi B →
        8 * D j ≤ xi * 3 ^ B.card)
    (hirregular : ∀ j,
      prob (Finset.Ioc C (D j))
        (Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi) ≤ delta) :
    ∀ j, prob (Finset.Ioc C (D (j + 1)))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
      (1 - xiFreshRate xi) *
          prob (Finset.Ioc C (D j))
            (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) +
        xiFreshRate xi * delta := by
  intro j
  calc
    prob (Finset.Ioc C (D (j + 1)))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
        prob (Finset.Ioc C (D j) ∪
          Finset.Ioc (xi * D j) (3 * (xi * D j)))
          (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) := by
      apply failure_prob_le_of_ambient_subset (hnested j)
      · intro n hn
        have hnC := (Finset.mem_Ioc.mp hn).1
        omega
      · intro S T hST hS
        exact hS.mono hST
    _ ≤ (1 - xiFreshRate xi) *
          prob (Finset.Ioc C (D j))
            (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) +
        xiFreshRate xi * delta := by
      simpa [xiFreshRate] using
        (Erdos144.Harmonic.harmonic_extension_bad_bound
          (hD j) hxi2 (hxiD j) delta (hstates j) (hirregular j))

/-- Iterating the concrete harmonic extension bound across nested full
reservoirs gives the usual affine geometric estimate. -/
theorem harmonic_failure_probability_after_stages
    (C s xi : ℕ) (D R : ℕ → ℕ) (delta : ℝ)
    (hD : ∀ j, 0 < D j) (hxi2 : 2 ≤ xi)
    (hxiD : ∀ j, xi < D j) (hdelta : 0 ≤ delta)
    (hnested : ∀ j,
      Finset.Ioc C (D j) ∪ Finset.Ioc (xi * D j) (3 * (xi * D j)) ⊆
        Finset.Ioc C (D (j + 1)))
    (hstates : ∀ j B, B ∈ (Finset.Ioc C (D j)).powerset →
      ¬ Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi B →
        8 * D j ≤ xi * 3 ^ B.card)
    (hirregular : ∀ j,
      prob (Finset.Ioc C (D j))
        (Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi) ≤ delta)
    (L : ℕ) :
    prob (Finset.Ioc C (D L))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
      (1 - xiFreshRate xi) ^ L + delta := by
  let b : ℕ → ℝ := fun j ↦
    prob (Finset.Ioc C (D j))
      (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T)
  have hb0 : b 0 ≤ 1 := by
    apply prob_le_one
    intro n hn
    have hnC := (Finset.mem_Ioc.mp hn).1
    omega
  have hxi : 0 < xi := by omega
  have hstep : ∀ j, b (j + 1) ≤
      (1 - xiFreshRate xi) * b j + xiFreshRate xi * delta := by
    simpa [b] using
      harmonic_failure_probability_stage_recurrence C s xi D R delta
        hD hxi2 hxiD hnested hstates hirregular
  simpa [b] using
    (Erdos144.HarmonicBlocks.affine_recurrence_bound_one
      (xiFreshRate_nonneg xi) (xiFreshRate_le_one hxi) hdelta hb0 hstep L)

/-- After `xi^3` concrete stages, failure is bounded by the advertised
geometric remainder plus the supplied irregular mass. -/
theorem harmonic_failure_probability_after_xi_cube
    (C s xi : ℕ) (D R : ℕ → ℕ) (delta : ℝ)
    (hD : ∀ j, 0 < D j) (hxi2 : 2 ≤ xi)
    (hxiD : ∀ j, xi < D j) (hdelta : 0 ≤ delta)
    (hnested : ∀ j,
      Finset.Ioc C (D j) ∪ Finset.Ioc (xi * D j) (3 * (xi * D j)) ⊆
        Finset.Ioc C (D (j + 1)))
    (hstates : ∀ j B, B ∈ (Finset.Ioc C (D j)).powerset →
      ¬ Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi B →
        8 * D j ≤ xi * 3 ^ B.card)
    (hirregular : ∀ j,
      prob (Finset.Ioc C (D j))
        (Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi) ≤ delta) :
    prob (Finset.Ioc C (D (xi ^ 3)))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
      (1 - xiFreshRate xi) ^ (xi ^ 3) + delta := by
  exact harmonic_failure_probability_after_stages C s xi D R delta
    hD hxi2 hxiD hdelta hnested hstates hirregular (xi ^ 3)

/-- Exponential form of the concrete `xi^3`-stage estimate. -/
theorem harmonic_failure_probability_after_xi_cube_le_exp
    (C s xi : ℕ) (D R : ℕ → ℕ) (delta : ℝ)
    (hD : ∀ j, 0 < D j) (hxi2 : 2 ≤ xi)
    (hxiD : ∀ j, xi < D j) (hdelta : 0 ≤ delta)
    (hnested : ∀ j,
      Finset.Ioc C (D j) ∪ Finset.Ioc (xi * D j) (3 * (xi * D j)) ⊆
        Finset.Ioc C (D (j + 1)))
    (hstates : ∀ j B, B ∈ (Finset.Ioc C (D j)).powerset →
      ¬ Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi B →
        8 * D j ≤ xi * 3 ^ B.card)
    (hirregular : ∀ j,
      prob (Finset.Ioc C (D j))
        (Erdos144.Harmonic.ReservoirIrregular (D j) (R j) s xi) ≤ delta) :
    prob (Finset.Ioc C (D (xi ^ 3)))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
      Real.exp (-(xi : ℝ) / 27) + delta := by
  calc
    prob (Finset.Ioc C (D (xi ^ 3)))
        (fun T ↦ ¬ Erdos144.Harmonic.HasEqualSubsums T) ≤
        (1 - xiFreshRate xi) ^ (xi ^ 3) + delta :=
      harmonic_failure_probability_after_xi_cube C s xi D R delta
        hD hxi2 hxiD hdelta hnested hstates hirregular
    _ ≤ Real.exp (-(xi : ℝ) / 27) + delta :=
      by
        simpa [add_comm] using
          add_le_add_right (xi_cube_geometric_le_exp (by omega : 0 < xi)) delta

end

end Erdos144.HarmonicIteration
