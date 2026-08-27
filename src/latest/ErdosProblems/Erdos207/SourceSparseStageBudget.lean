/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FrozenPreparedLawConditioning
import ErdosProblems.Erdos207.SourceStageErrorBudgets

/-! # Numeric data for the actual frozen preliminary kernel -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure SourceSparseStageBudget
    (q stage b B k t Rmin c R m n N : ℕ)
    (p eta Caux Cprior beta priorCoefficient error : ℝ≥0) (z : ℕ → ℝ≥0) : Prop where
  p_pos : 0 < p
  p_le_one : p ≤ 1
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  current_pos : 1 ≤ n
  large : 49152 ≤ t
  binomial : 2^q ≤ t
  order : q ≤ t
  scale : t ^ ksssPowerDenominatorExponent q b B k Rmin ≤ n
  edge_floor : (n : ℝ≥0)^2/(t : ℝ≥0)^b ≤ p*(n : ℝ≥0)^2/8
  ratio_floor : (n : ℝ≥0)/(t : ℝ≥0)^b ≤ p^2*eta*n/24
  auxiliary_pos : 1 ≤ Caux
  auxiliary_small : Caux*t*p ≤ eta
  coefficient : KSSSPowerCoefficientBounds q (fun d ↦ 9*24^d) B t
  envelope : 4*q ≤ B
  pair : ksssPairDriftCoefficient q (fun d ↦ 9*24^d) +
    ksssPairTaylorCoefficient (ksssOrders q) (fun d ↦ 9*24^d) ≤ 3*(B : ℝ)
  configuration : ∀ i : CrudeOrderIndex q 4,
    ksssIndexedConfigurationDriftCoefficient q (fun d ↦ 9*24^d) i +
      ksssConfigurationTaylorCoefficient (ksssOrders q) (fun d ↦ 9*24^d)
        (i.order-3) i.chosen ≤ 3*(B : ℝ)/2
  density_exponent : 2*c ≤ b
  prior_pos : 1 ≤ Cprior
  augmented_z : ∀ j ∈ Icc 4 q, z j + 3*(t : ℝ≥0)^4 ≤ (t : ℝ≥0)^(5*c)
  crude_constant : sourceCrudeUniformCoefficient stage q (Icc 4 q).card 1 1 ≤ t
  cutoff : 2*(5*c)+2*q*(5*b+3)+2 ≤ k
  ambient : N ≤ t^R
  incoming_error : beta ≤ priorCoefficient/(t : ℝ≥0)^sourceStageRequiredError q c R m
  delta_pos : 0 < 1/(t : ℝ≥0)^(c*m)
  delta_lt_one : 1/(t : ℝ≥0)^(c*m) < 1
  geometric : (1/2 : ℝ≥0)^t ≤ 1/(t : ℝ≥0)^(c*m)
  band : 2*((n : ℝ≥0)^2+(q+1 : ℝ≥0)^2*(n : ℝ≥0)^3)*(1/2 : ℝ≥0)^t ≤
    1/(t : ℝ≥0)^(c*m+3*c)
  prior_budget : (((Icc 4 q).card : ℝ≥0)/(t : ℝ≥0)^(c*m+3*c)+1/(t : ℝ≥0)^(c*m+3*c)+
    sourceSparseCrudeFailure q (6*R+(c*m+3*c)) (Icc 4 q).card t (c*m+3*c)
      Cprior priorCoefficient)/(1/(t : ℝ≥0)^(c*m)) ≤ error
  error_lt_one : error < 1

end

end Erdos207
