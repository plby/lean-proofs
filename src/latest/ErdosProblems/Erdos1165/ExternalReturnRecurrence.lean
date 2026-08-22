/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalGreenRenewal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The exact return-coefficient recurrence for the external walk

This file derives the recurrence used in the external Green-function
coefficient estimates from the exact binomial transform.  The proof is
entirely algebraic: the binomial transform is encoded as a substitution of
formal power series, the standard central-binomial recurrence gives a
differential equation, and the inverse Möbius change of variables gives the
external recurrence.
-/

open scoped BigOperators

namespace Erdos1165.ExternalReturnRecurrence

open ExternalWalk ExternalOnePoint ExternalGreenRenewal LazyDecomposition
open PowerSeries

noncomputable section

/-- The return-count series for the retained-block walk. -/
def externalCountSeries (o : Orientation) : ℝ⟦X⟧ :=
  PowerSeries.mk fun n ↦ ((externalReturningWords o n).card : ℝ)

/-- The squared central-binomial series. -/
def centralBinomSqSeries : ℝ⟦X⟧ :=
  PowerSeries.mk fun n ↦ ((Nat.centralBinom n : ℝ) ^ 2)

/-- The geometric series `1 + X + X² + ⋯`. -/
def geom : ℝ⟦X⟧ := PowerSeries.mk 1

/-- The Möbius parameter `X / (1-X)`, represented without division. -/
def mobius : ℝ⟦X⟧ := X * geom

@[simp] lemma coeff_externalCountSeries (o : Orientation) (n : ℕ) :
    coeff n (externalCountSeries o) = ((externalReturningWords o n).card : ℝ) := by
  simp [externalCountSeries]

@[simp] lemma coeff_centralBinomSqSeries (n : ℕ) :
    coeff n centralBinomSqSeries = ((Nat.centralBinom n : ℝ) ^ 2) := by
  simp [centralBinomSqSeries]

@[simp] lemma coeff_geom (n : ℕ) : coeff n geom = 1 := by
  simp [geom]

lemma geom_mul_one_sub_X : geom * (1 - X) = (1 : ℝ⟦X⟧) := by
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℝ

lemma one_sub_X_mul_geom : (1 - X) * geom = (1 : ℝ⟦X⟧) := by
  rw [mul_comm, geom_mul_one_sub_X]

lemma constantCoeff_mobius : constantCoeff mobius = 0 := by
  simp [mobius]

lemma hasSubst_mobius : HasSubst mobius :=
  HasSubst.of_constantCoeff_zero' constantCoeff_mobius

lemma coeff_geom_pow_succ (j k : ℕ) :
    coeff k (geom ^ (j + 1)) = (Nat.choose (j + k) j : ℝ) := by
  rw [geom, PowerSeries.mk_one_pow_eq_mk_choose_add]
  simp

lemma coeff_mobius_pow (n j : ℕ) :
    coeff n (mobius ^ j) =
      if j = 0 then (if n = 0 then 1 else 0)
      else if j ≤ n then (Nat.choose (n - 1) (j - 1) : ℝ) else 0 := by
  rw [mobius, mul_pow, mul_comm, PowerSeries.coeff_mul_X_pow']
  rcases j with _ | j
  · simp
  · simp only [Nat.succ_ne_zero, ↓reduceIte]
    split_ifs with hj
    · rw [coeff_geom_pow_succ]
      have harg : j + (n - (j + 1)) = n - 1 := by omega
      rw [harg]
      simp
    · rfl

lemma binomialTransform_succ (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℝ) * a j) =
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a j) +
        ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a (j + 1) := by
  calc
    (∑ j ∈ Finset.range (n + 2), ((n + 1).choose j : ℝ) * a j) =
        (∑ j ∈ Finset.range (n + 1),
          (((n + 1).choose (j + 1) : ℝ) * a (j + 1))) + a 0 := by
      rw [Finset.sum_range_succ']
      simp
    _ = (∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) + (n.choose (j + 1) : ℝ)) * a (j + 1)) + a 0 := by
      apply congrArg (fun s : ℝ ↦ s + a 0)
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Nat.cast_add, ← Nat.choose_succ_succ]
    _ = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a (j + 1)) +
          ((∑ j ∈ Finset.range (n + 1), (n.choose (j + 1) : ℝ) * a (j + 1)) +
            a 0) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring
    _ = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a (j + 1)) +
          (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a j) := by
      congr 1
      calc
        (∑ j ∈ Finset.range (n + 1), (n.choose (j + 1) : ℝ) * a (j + 1)) +
              a 0 =
            (∑ j ∈ Finset.range n, (n.choose (j + 1) : ℝ) * a (j + 1)) +
              a 0 := by
          rw [Finset.sum_range_succ]
          simp
        _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * a j := by
          rw [Finset.sum_range_succ']
          simp
    _ = _ := by ring

lemma coeff_subst_mobius_zero (f : ℝ⟦X⟧) :
    coeff 0 (f.subst mobius) = coeff 0 f := by
  rw [PowerSeries.coeff_subst' hasSubst_mobius]
  rw [finsum_eq_single _ 0]
  · simp [coeff_mobius_pow]
  · intro j hj
    simp [coeff_mobius_pow, hj]

lemma coeff_subst_mobius_succ (f : ℝ⟦X⟧) (n : ℕ) :
    coeff (n + 1) (f.subst mobius) =
      ∑ j ∈ Finset.range (n + 1),
        coeff (j + 1) f * (n.choose j : ℝ) := by
  rw [PowerSeries.coeff_subst' hasSubst_mobius]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 2))]
  · rw [Finset.sum_range_succ']
    have hzero : (coeff 0 f) • coeff (n + 1) (mobius ^ 0) = (0 : ℝ) := by
      simp [coeff_mobius_pow]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_mobius_pow, if_neg (Nat.succ_ne_zero j),
      if_pos (by rw [Finset.mem_range] at hj; omega)]
    simp only [Nat.add_sub_cancel, smul_eq_mul]
  · intro j hj
    simp only [Function.mem_support] at hj
    by_contra hmem
    have hge : n + 2 ≤ j := by
      exact Nat.le_of_not_gt (fun hlt ↦ hmem (Finset.mem_range.mpr hlt))
    have hjlarge : n + 1 < j := by
      omega
    have hj0 : j ≠ 0 := by omega
    have hjnot : ¬j ≤ n + 1 := by omega
    exact hj (by simp [coeff_mobius_pow, hj0, hjnot])

lemma coeff_one_sub_X_mul (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n ((1 - X) * f) =
      if n = 0 then coeff 0 f else coeff n f - coeff (n - 1) f := by
  rcases n with _ | n
  · simp
  · simp [sub_mul, PowerSeries.coeff_X_pow_mul']

/-- Formal-series form of the exact binomial transform. -/
theorem one_sub_X_mul_central_eq_subst_external (o : Orientation) :
    (1 - X) * centralBinomSqSeries =
      (externalCountSeries o).subst mobius := by
  ext (_ | n)
  · rw [coeff_one_sub_X_mul, if_pos rfl, coeff_subst_mobius_zero]
    have hzero := centralBinom_sq_eq_sum_choose_mul_externalReturns o 0
    simpa using congrArg (fun m : ℕ ↦ (m : ℝ)) hzero
  · rw [coeff_one_sub_X_mul, if_neg (Nat.succ_ne_zero n),
      coeff_subst_mobius_succ]
    simp only [coeff_centralBinomSqSeries, coeff_externalCountSeries,
      Nat.succ_sub_one]
    have hn1 := centralBinom_sq_eq_sum_choose_mul_externalReturns o (n + 1)
    have hn := centralBinom_sq_eq_sum_choose_mul_externalReturns o n
    have hn1R : ((Nat.centralBinom (n + 1) : ℝ) ^ 2) =
        ∑ j ∈ Finset.range (n + 2),
          ((n + 1).choose j : ℝ) * ((externalReturningWords o j).card : ℝ) := by
      exact_mod_cast hn1
    have hnR : ((Nat.centralBinom n : ℝ) ^ 2) =
        ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ((externalReturningWords o j).card : ℝ) := by
      exact_mod_cast hn
    rw [hn1R, hnR, binomialTransform_succ]
    rw [add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private noncomputable def D (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.derivative ℝ f

lemma coeff_D (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (D f) = coeff (n + 1) f * (n + 1 : ℝ) := by
  simp [D, PowerSeries.coeff_derivative]

lemma centralBinomSq_recurrence (n : ℕ) :
    ((n + 1 : ℝ) ^ 2) * ((Nat.centralBinom (n + 1) : ℝ) ^ 2) =
      4 * ((2 * n + 1 : ℝ) ^ 2) * ((Nat.centralBinom n : ℝ) ^ 2) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hR : ((n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ)) =
      (2 * (2 * n + 1 : ℝ)) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  calc
    ((n + 1 : ℝ) ^ 2) * ((Nat.centralBinom (n + 1) : ℝ) ^ 2) =
        (((n + 1 : ℝ) * (Nat.centralBinom (n + 1) : ℝ)) ^ 2) := by ring
    _ = ((2 * (2 * n + 1 : ℝ)) * (Nat.centralBinom n : ℝ)) ^ 2 := by rw [hR]
    _ = 4 * ((2 * n + 1 : ℝ) ^ 2) * ((Nat.centralBinom n : ℝ) ^ 2) := by ring

private noncomputable def centralDifferentialExpression : ℝ⟦X⟧ :=
  X * D (D centralBinomSqSeries) -
      (16 : ℝ) • (X ^ 2 * D (D centralBinomSqSeries)) +
    D centralBinomSqSeries -
      (32 : ℝ) • (X * D centralBinomSqSeries) -
    (4 : ℝ) • centralBinomSqSeries

lemma coeff_centralDifferentialExpression (n : ℕ) :
    coeff n centralDifferentialExpression =
      ((n + 1 : ℝ) ^ 2) * ((Nat.centralBinom (n + 1) : ℝ) ^ 2) -
        4 * ((2 * n + 1 : ℝ) ^ 2) * ((Nat.centralBinom n : ℝ) ^ 2) := by
  rcases n with _ | _ | n
  · norm_num [centralDifferentialExpression, D, PowerSeries.coeff_derivative,
      centralBinomSqSeries]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative]
    simp [centralBinomSqSeries]
  · norm_num [centralDifferentialExpression, coeff_D, centralBinomSqSeries,
      PowerSeries.coeff_X_pow_mul']
    ring
  · simp only [centralDifferentialExpression, map_sub, map_add, map_smul,
      coeff_D, coeff_centralBinomSqSeries]
    simp [D, PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow_mul']
    ring

/-- Differential equation for the squared central-binomial series. -/
theorem centralBinomSq_differential :
    centralDifferentialExpression = 0 := by
  ext n
  rw [coeff_centralDifferentialExpression, centralBinomSq_recurrence]
  simp

lemma centralBinomSqSeries_eq_geom_mul_subst (o : Orientation) :
    centralBinomSqSeries = geom * (externalCountSeries o).subst mobius := by
  calc
    centralBinomSqSeries = 1 * centralBinomSqSeries := by simp
    _ = (geom * (1 - X)) * centralBinomSqSeries := by rw [geom_mul_one_sub_X]
    _ = geom * ((1 - X) * centralBinomSqSeries) := by ring
    _ = geom * (externalCountSeries o).subst mobius := by
      rw [one_sub_X_mul_central_eq_subst_external]

lemma D_geom : D geom = geom ^ 2 := by
  ext n
  rw [coeff_D]
  simp only [coeff_geom, one_mul]
  rw [pow_two, PowerSeries.coeff_mul]
  simp [geom]

lemma D_mobius : D mobius = geom ^ 2 := by
  change PowerSeries.derivative ℝ (X * geom) = geom ^ 2
  rw [Derivation.leibniz, PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one]
  change X * D geom + geom = geom ^ 2
  rw [D_geom]
  have hgeom : geom = 1 + X * geom := by
    have h := one_sub_X_mul_geom
    rw [sub_mul] at h
    linear_combination h
  calc
    X * geom ^ 2 + geom = geom * (X * geom + 1) := by ring
    _ = geom * geom := by rw [add_comm, ← hgeom]
    _ = geom ^ 2 := by ring

lemma D_subst_mobius (f : ℝ⟦X⟧) :
    D (f.subst mobius) = (D f).subst mobius * geom ^ 2 := by
  change PowerSeries.derivative ℝ (f.subst mobius) =
    (D f).subst mobius * geom ^ 2
  rw [PowerSeries.derivative_subst hasSubst_mobius]
  change (D f).subst mobius * D mobius = _
  rw [D_mobius]

lemma D_geom_mul_subst (f : ℝ⟦X⟧) :
    D (geom * f.subst mobius) =
      geom ^ 2 * f.subst mobius + geom ^ 3 * (D f).subst mobius := by
  change PowerSeries.derivative ℝ (geom * f.subst mobius) = _
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [show PowerSeries.derivative ℝ (f.subst mobius) =
      (D f).subst mobius * geom ^ 2 from D_subst_mobius f,
    show PowerSeries.derivative ℝ geom = geom ^ 2 from D_geom]
  ring

lemma D_D_geom_mul_subst (f : ℝ⟦X⟧) :
    D (D (geom * f.subst mobius)) =
      2 • (geom ^ 3 * f.subst mobius) +
        4 • (geom ^ 4 * (D f).subst mobius) +
          geom ^ 5 * (D (D f)).subst mobius := by
  rw [D_geom_mul_subst]
  change PowerSeries.derivative ℝ
    (geom ^ 2 * f.subst mobius + geom ^ 3 * (D f).subst mobius) = _
  rw [map_add, Derivation.leibniz, Derivation.leibniz,
    PowerSeries.derivative_pow, PowerSeries.derivative_pow]
  simp only [smul_eq_mul]
  rw [show PowerSeries.derivative ℝ (f.subst mobius) =
      (D f).subst mobius * geom ^ 2 from D_subst_mobius f,
    show PowerSeries.derivative ℝ ((D f).subst mobius) =
      (D (D f)).subst mobius * geom ^ 2 from D_subst_mobius (D f),
    show PowerSeries.derivative ℝ geom = geom ^ 2 from D_geom]
  ring

/-- The differential operator whose coefficient recurrence is the retained
block return-count recurrence. -/
noncomputable def externalDifferentialExpression (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  X * D (D f) - (13 : ℝ) • (X ^ 2 * D (D f)) -
      (29 : ℝ) • (X ^ 3 * D (D f)) -
      (15 : ℝ) • (X ^ 4 * D (D f)) +
    D f - (26 : ℝ) • (X * D f) -
      (87 : ℝ) • (X ^ 2 * D f) -
      (60 : ℝ) • (X ^ 3 * D f) -
    (3 : ℝ) • f - (29 : ℝ) • (X * f) -
      (30 : ℝ) • (X ^ 2 * f)

lemma subst_externalDifferentialExpression (f : ℝ⟦X⟧) :
    (externalDifferentialExpression f).subst mobius =
      mobius * (D (D f)).subst mobius -
          (13 : ℝ) • (mobius ^ 2 * (D (D f)).subst mobius) -
          (29 : ℝ) • (mobius ^ 3 * (D (D f)).subst mobius) -
          (15 : ℝ) • (mobius ^ 4 * (D (D f)).subst mobius) +
        (D f).subst mobius -
          (26 : ℝ) • (mobius * (D f).subst mobius) -
          (87 : ℝ) • (mobius ^ 2 * (D f).subst mobius) -
          (60 : ℝ) • (mobius ^ 3 * (D f).subst mobius) -
        (3 : ℝ) • f.subst mobius -
          (29 : ℝ) • (mobius * f.subst mobius) -
          (30 : ℝ) • (mobius ^ 2 * f.subst mobius) := by
  unfold externalDifferentialExpression
  simp only [PowerSeries.subst_add hasSubst_mobius,
    PowerSeries.subst_sub hasSubst_mobius,
    PowerSeries.subst_mul hasSubst_mobius,
    PowerSeries.subst_pow hasSubst_mobius,
    PowerSeries.subst_smul hasSubst_mobius,
    PowerSeries.subst_X hasSubst_mobius]

lemma subst_mobius_injective :
    Function.Injective (fun f : ℝ⟦X⟧ ↦ f.subst mobius) := by
  have hc : coeff 1 mobius = (1 : ℝ) := by
    simpa using coeff_mobius_pow 1 1
  letI : Invertible (coeff 1 mobius) := hc ▸ invertibleOne
  intro f g hfg
  have hsub := congrArg (fun q : ℝ⟦X⟧ ↦ q.subst mobius.substInv) hfg
  rw [PowerSeries.subst_comp_subst_apply hasSubst_mobius
      (PowerSeries.HasSubst.substInv mobius),
    PowerSeries.subst_comp_subst_apply hasSubst_mobius
      (PowerSeries.HasSubst.substInv mobius),
    PowerSeries.subst_substInv_right mobius constantCoeff_mobius,
    PowerSeries.X_subst, PowerSeries.X_subst] at hsub
  exact hsub

/-- The central differential equation transported through the exact
binomial Möbius transform. -/
theorem externalCountSeries_differential (o : Orientation) :
    externalDifferentialExpression (externalCountSeries o) = 0 := by
  let A := externalCountSeries o
  have hcentral := centralBinomSq_differential
  unfold centralDifferentialExpression at hcentral
  have hseries : centralBinomSqSeries = geom * A.subst mobius := by
    simpa [A] using centralBinomSqSeries_eq_geom_mul_subst o
  rw [hseries,
    D_D_geom_mul_subst A, D_geom_mul_subst A] at hcentral
  have hrel : X * geom - geom + 1 = 0 := by
    calc
      X * geom - geom + 1 = -(geom * (1 - X) - 1) := by ring
      _ = 0 := by rw [geom_mul_one_sub_X]; ring
  have htransport :
      X * (2 • (geom ^ 3 * A.subst mobius) +
              4 • (geom ^ 4 * (D A).subst mobius) +
                geom ^ 5 * (D (D A)).subst mobius) -
          (16 : ℝ) •
            (X ^ 2 * (2 • (geom ^ 3 * A.subst mobius) +
              4 • (geom ^ 4 * (D A).subst mobius) +
                geom ^ 5 * (D (D A)).subst mobius)) +
        (geom ^ 2 * A.subst mobius +
          geom ^ 3 * (D A).subst mobius) -
          (32 : ℝ) • (X * (geom ^ 2 * A.subst mobius +
            geom ^ 3 * (D A).subst mobius)) -
        (4 : ℝ) • (geom * A.subst mobius) =
          geom * (externalDifferentialExpression A).subst mobius := by
    rw [subst_externalDifferentialExpression]
    rw [mobius]
    simp only [Algebra.smul_def, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self]
    rw [← sub_eq_zero]
    let q : ℝ⟦X⟧ :=
      -(2 : ℝ) • (A.subst mobius * geom * X) - A.subst mobius +
        (60 : ℝ) • ((D A).subst mobius * geom ^ 2 * X ^ 2) -
        (4 : ℝ) • ((D A).subst mobius * geom ^ 2 * X) +
        (27 : ℝ) • ((D A).subst mobius * geom * X) -
        (D A).subst mobius * geom - (D A).subst mobius +
        (15 : ℝ) • ((D (D A)).subst mobius * geom ^ 3 * X ^ 3) +
        (15 : ℝ) • ((D (D A)).subst mobius * geom ^ 3 * X ^ 2) -
        (D (D A)).subst mobius * geom ^ 3 * X +
        (14 : ℝ) • ((D (D A)).subst mobius * geom ^ 2 * X ^ 2) -
        (D (D A)).subst mobius * geom ^ 2 * X -
        (D (D A)).subst mobius * geom * X
    calc
      _ = geom * (X * geom - geom + 1) * q := by
        dsimp [q, mobius]
        simp only [Algebra.smul_def, PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        simp only [PowerSeries.C_eq_algebraMap, map_neg, map_ofNat]
        ring
      _ = 0 := by rw [hrel]; ring
  rw [htransport] at hcentral
  have hsubst : (externalDifferentialExpression A).subst mobius = 0 := by
    have hmul := congrArg (fun q : ℝ⟦X⟧ ↦ (1 - X) * q) hcentral
    rw [← mul_assoc, one_sub_X_mul_geom] at hmul
    simpa using hmul
  apply subst_mobius_injective
  have hzero : (0 : ℝ⟦X⟧).subst mobius = 0 := by
    rw [← PowerSeries.coe_substAlgHom hasSubst_mobius]
    exact map_zero _
  change (externalDifferentialExpression (externalCountSeries o)).subst mobius =
    (0 : ℝ⟦X⟧).subst mobius
  rw [hzero]
  simpa [A] using hsubst

lemma coeff_X_mul (f : ℝ⟦X⟧) (n : ℕ) :
    coeff n (X * f) = if 1 ≤ n then coeff (n - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 n

lemma coeff_externalDifferentialExpression (f : ℝ⟦X⟧) (n : ℕ) (hn : 2 ≤ n) :
    coeff n (externalDifferentialExpression f) =
      (n + 1 : ℝ) ^ 2 * coeff (n + 1) f -
        ((13 : ℝ) * n ^ 2 + 13 * n + 3) * coeff n f -
        29 * n ^ 2 * coeff (n - 1) f -
        15 * n * (n - 1) * coeff (n - 2) f := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold externalDifferentialExpression
  simp only [map_add, map_sub, map_smul, coeff_D]
  rcases m with _ | _ | m
  · simp [PowerSeries.coeff_X_pow_mul', coeff_D]
    ring
  · simp [PowerSeries.coeff_X_pow_mul', coeff_D]
    ring
  · have hsub3 : 2 + (m + 1 + 1) - 3 = m + 1 := by omega
    have hsub4' : 2 + (m + 1 + 1) - 4 = m := by omega
    simp [coeff_X_mul, PowerSeries.coeff_X_pow_mul', coeff_D]
    split_ifs <;> try omega
    rw [hsub3, hsub4']
    simp only [Nat.cast_add, Nat.cast_one]
    simp only [Nat.add_assoc]
    push_cast
    ring

/-- Exact recurrence for the retained-block return counts, in real form. -/
theorem externalReturningWords_card_recurrence_real (o : Orientation)
    (n : ℕ) (hn : 2 ≤ n) :
    (n + 1 : ℝ) ^ 2 * ((externalReturningWords o (n + 1)).card : ℝ) =
      ((13 : ℝ) * n ^ 2 + 13 * n + 3) *
          ((externalReturningWords o n).card : ℝ) +
        29 * n ^ 2 * ((externalReturningWords o (n - 1)).card : ℝ) +
        15 * n * (n - 1) *
          ((externalReturningWords o (n - 2)).card : ℝ) := by
  have h := congrArg (coeff n) (externalCountSeries_differential o)
  rw [coeff_externalDifferentialExpression _ n hn] at h
  simp only [coeff_externalCountSeries, map_zero] at h
  linarith

/-- Exact recurrence for the natural return-word counts. -/
theorem externalReturningWords_card_recurrence (o : Orientation)
    (n : ℕ) (hn : 2 ≤ n) :
    (n + 1) ^ 2 * (externalReturningWords o (n + 1)).card =
      (13 * n ^ 2 + 13 * n + 3) * (externalReturningWords o n).card +
        29 * n ^ 2 * (externalReturningWords o (n - 1)).card +
        15 * n * (n - 1) * (externalReturningWords o (n - 2)).card := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  have h := externalReturningWords_card_recurrence_real o n hn
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  simpa using h

/-- Exact recurrence for the retained-block return probabilities. -/
theorem externalReturnProbability_recurrence (o : Orientation)
    (n : ℕ) (hn : 2 ≤ n) :
    225 * (n + 1 : ℝ) ^ 2 * externalReturnProbability o (n + 1) =
      ((195 : ℝ) * n ^ 2 + 195 * n + 45) * externalReturnProbability o n +
        29 * n ^ 2 * externalReturnProbability o (n - 1) +
        n * (n - 1) * externalReturnProbability o (n - 2) := by
  have hcount := externalReturningWords_card_recurrence_real o n hn
  have hp3 : (15 : ℝ) ^ (n + 1) = 15 ^ (n - 2) * 15 ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hp2 : (15 : ℝ) ^ n = 15 ^ (n - 2) * 15 ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hp1 : (15 : ℝ) ^ (n - 1) = 15 ^ (n - 2) * 15 := by
    rw [← pow_succ]
    congr 1
    omega
  unfold ExternalGreenRenewal.externalReturnProbability
  rw [hp3, hp2, hp1]
  field_simp
  linear_combination 225 * hcount

end

end Erdos1165.ExternalReturnRecurrence
