import Util.MaynardTao.BFT.CandidateTransport
import ErdosProblems.Erdos6.GenericDiagonal
import BoundedGaps.Maynard.MaynardYDiagonalExplicit
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

/-!
# The large-candidate Y-diagonal limit

The independent product moment is the actual squarefree Maynard diagonal
plus the coordinate-collision moment.  The former therefore has limit
`I_k(F)` after the collision contribution is removed.
-/

namespace MaynardBFT.Sieve

open Erdos6.Maynard

open Filter Set
open scoped BigOperators

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def tupleMaynardDiagonal (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N),
    F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u

def normalizedTupleMaynardDiagonal (H : Finset ℕ) (alpha : ℝ)
    (F : (H → ℝ) → ℝ) (N : ℕ) : ℝ :=
  tupleMaynardDiagonal H alpha F N / tupleNaturalScale H alpha N

theorem tupleWeightedMoment_sq_eq_diagonal_add_collision
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ}
    {F G : (H → ℝ) → ℝ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hFG : ∀ t ∈ BoundedGaps.Maynard.finiteSimplexOf H, G t = F t) :
    tupleWeightedMoment H alpha (fun t => G t ^ 2) N =
      tupleMaynardDiagonal H alpha F N +
        tupleCollisionMoment H alpha (fun t => G t ^ 2) N := by
  have hsum := BoundedGaps.Maynard.sum_preSievedSimplex_eq_maynard_add_collision
    H
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
    (fun u => F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight H u)
  unfold tupleWeightedMoment tupleMaynardDiagonal tupleCollisionMoment
  calc
    _ = ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexTupleSupport
          H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight
            H u := by
      apply Finset.sum_congr rfl
      intro u hu
      have hpoint := tupleNormalizedLogPoint_mem_finiteSimplex hR hu
      change G (tupleNormalizedLogPoint H alpha N u) ^ 2 *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight H u =
        F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight H u
      rw [hFG _ hpoint]
    _ = (∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
          H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight
            H u) +
        ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport
          H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N),
        F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
          BoundedGaps.Maynard.reciprocalTotientTupleWeight
            H u := hsum
    _ = _ := by
      have hcollision :
          (∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.engelsmaMaynardModulus N),
            F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
              BoundedGaps.Maynard.reciprocalTotientTupleWeight H u) =
          ∑ u ∈ BoundedGaps.Maynard.preSievedSimplexCollisionSupport H
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.engelsmaMaynardModulus N),
            G (tupleNormalizedLogPoint H alpha N u) ^ 2 *
              BoundedGaps.Maynard.reciprocalTotientTupleWeight H u := by
        apply Finset.sum_congr rfl
        intro u hu
        have huPre : u ∈ BoundedGaps.Maynard.preSievedSimplexTupleSupport
          H
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
          (BoundedGaps.Maynard.engelsmaMaynardModulus N) :=
          (Finset.mem_filter.mp hu).1
        have hpoint := tupleNormalizedLogPoint_mem_finiteSimplex hR huPre
        rw [hFG _ hpoint]
      exact congrArg
        (fun z =>
          (∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H
              (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
              (BoundedGaps.Maynard.engelsmaMaynardModulus N),
            F (tupleNormalizedLogPoint H alpha N u) ^ 2 *
              BoundedGaps.Maynard.reciprocalTotientTupleWeight H u) + z)
        hcollision

theorem tupleWeightedMoment_largeProduct_sq_eq_diagonal_add_collision
    {alpha : ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :
    tupleWeightedMoment largePowerTuple alpha
        (fun t => largeTupleContinuousProduct t ^ 2) N =
      tupleMaynardDiagonal largePowerTuple alpha largeTupleCandidate N +
        tupleCollisionMoment largePowerTuple alpha
          (fun t => largeTupleContinuousProduct t ^ 2) N :=
  tupleWeightedMoment_sq_eq_diagonal_add_collision hR
    (fun t ht =>
      largeTupleContinuousProduct_eq_largeTupleCandidate_of_mem_simplex ht)

theorem normalizedTupleMaynardDiagonal_eq_independent_sub_collision
    {alpha : ℝ} {N : ℕ}
    (hR : 1 < BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (hscale : tupleNaturalScale largePowerTuple alpha N ≠ 0) :
    normalizedTupleMaynardDiagonal largePowerTuple alpha largeTupleCandidate N =
      normalizedTupleWeightedMoment largePowerTuple alpha
          (fun t => largeTupleContinuousProduct t ^ 2) N -
        normalizedTupleCollisionMoment largePowerTuple alpha
          (fun t => largeTupleContinuousProduct t ^ 2) N := by
  have hsplit := tupleWeightedMoment_largeProduct_sq_eq_diagonal_add_collision hR
  unfold normalizedTupleMaynardDiagonal normalizedTupleWeightedMoment
    normalizedTupleCollisionMoment
  rw [hsplit]
  field_simp [hscale]
  ring

theorem tendsto_normalizedLargeTupleMaynardDiagonal
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedTupleMaynardDiagonal largePowerTuple alpha
        largeTupleCandidate N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  let h0 : largePowerTuple :=
    ⟨largePowerTuple_nonempty.choose, largePowerTuple_nonempty.choose_spec⟩
  have hind := tendsto_normalizedTupleWeightedMoment
    (f := fun t => largeTupleContinuousProduct t ^ 2) h0 halpha
    (continuous_largeTupleContinuousProduct.pow 2)
    largeTupleContinuousProduct_sq_bounds
  rw [integral_largeTupleContinuousProduct_sq_eq_maynardI] at hind
  have hcoll := tendsto_normalizedTupleCollisionMoment_zero halpha
    (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (largeTupleContinuousProduct_sq_bounds x hx).2)
  have hdiff := hind.sub hcoll
  simpa using hdiff.congr' (by
    filter_upwards [BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius
        halpha,
      eventually_tupleNaturalScale_pos
        (H := largePowerTuple) halpha] with N hR hscale
    exact (normalizedTupleMaynardDiagonal_eq_independent_sub_collision
      hR hscale.ne').symm)

def largeTupleYDiagonal (alpha : ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.maynardYDiagonalSum largePowerTuple
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
    (BoundedGaps.Maynard.engelsmaMaynardModulus N)
    (BoundedGaps.Maynard.maynardYValue largePowerTuple
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (BoundedGaps.Maynard.engelsmaMaynardModulus N)
      largeTupleCandidate)

theorem reciprocalTotientTupleWeight_eq_one_div_product
    {H : Finset ℕ} (u : H → ℕ) :
    BoundedGaps.Maynard.reciprocalTotientTupleWeight H u =
      (1 : ℝ) / ∏ h : H, (Nat.totient (u h) : ℝ) := by
  unfold BoundedGaps.Maynard.reciprocalTotientTupleWeight
  simp only [one_div, Finset.prod_inv_distrib]

theorem largeTupleYDiagonal_eq_tupleMaynardDiagonal
    (alpha : ℝ) (n : ℕ) :
    largeTupleYDiagonal alpha n =
      tupleMaynardDiagonal largePowerTuple alpha largeTupleCandidate n := by
  unfold largeTupleYDiagonal
  rw [BoundedGaps.Maynard.maynardYDiagonalSum_maynardYValue_eq_explicit]
  unfold tupleMaynardDiagonal tupleNormalizedLogPoint
  apply Finset.sum_congr rfl
  intro u hu
  change largeTupleCandidate
      (fun h => Real.log (u h) /
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha n)) ^ 2 /
        ∏ h : largePowerTuple, (Nat.totient (u h) : ℝ) =
    largeTupleCandidate
      (fun h => Real.log (u h) /
        Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha n)) ^ 2 *
      BoundedGaps.Maynard.reciprocalTotientTupleWeight largePowerTuple u
  rw [reciprocalTotientTupleWeight_eq_one_div_product]
  ring

theorem eventually_tupleMaynardScale_pos
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < tupleMaynardScale H alpha N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  unfold tupleMaynardScale
  apply BoundedGaps.Maynard.maynardSieveScale_pos
  · exact primorial_pos _
  · omega
  · apply BoundedGaps.Maynard.maynardRealCutoff_gt_one
    · omega
    · exact halpha

theorem normalized_maynardScale_eq_natural_mul_logRatio
    {H : Finset ℕ} {D N Rnat : ℕ} {Rreal Y : ℝ}
    (hN : 0 < (N : ℝ)) (hW : 0 < (primorial D : ℝ))
    (hphi : 0 < (Nat.totient (primorial D) : ℝ))
    (hLnat : 0 < Real.log Rnat) (hLreal : 0 < Real.log Rreal) :
    ((((N : ℝ) / primorial D) * Y) /
        BoundedGaps.Maynard.maynardSieveScale (Fintype.card H)
          (primorial D) N Rreal) =
      (Y / ((BoundedGaps.Maynard.preSieveSingularSeries D *
          Real.log Rnat) ^ Fintype.card H)) *
        (Real.log Rnat / Real.log Rreal) ^ Fintype.card H := by
  rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
  unfold BoundedGaps.Maynard.maynardSieveScale
  simp only [mul_pow, div_pow]
  field_simp [hN.ne', hW.ne', hphi.ne', hLnat.ne', hLreal.ne']
  ring

theorem eventually_normalizedLargeTupleYDiagonal_eq_natural_mul_logRatio
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
          largeTupleYDiagonal alpha N) /
          tupleMaynardScale largePowerTuple alpha N =
        normalizedTupleMaynardDiagonal largePowerTuple alpha
            largeTupleCandidate N *
          (Real.log (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) /
            Real.log (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)) ^
              Fintype.card largePowerTuple := by
  have hR := BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR, eventually_ge_atTop 3] with N hRN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : (0 : ℝ) < BoundedGaps.Maynard.engelsmaMaynardModulus N := by
    exact_mod_cast primorial_pos
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
  have hphi : (0 : ℝ) < Nat.totient
      (BoundedGaps.Maynard.engelsmaMaynardModulus N) := by
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)))
  have hLnat : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  have hRreal : 1 < BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N := by
    unfold BoundedGaps.Maynard.engelsmaMaynardRealRadius
      BoundedGaps.Maynard.maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  have hLreal : 0 < Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N) :=
    Real.log_pos hRreal
  rw [largeTupleYDiagonal_eq_tupleMaynardDiagonal]
  unfold normalizedTupleMaynardDiagonal tupleNaturalScale tupleMaynardScale
  simpa only [BoundedGaps.Maynard.engelsmaMaynardModulus] using
    (normalized_maynardScale_eq_natural_mul_logRatio
      (H := largePowerTuple)
      (D := BoundedGaps.Maynard.tripleLogCutoff (N - 1))
      (N := N)
      (Rnat := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
      (Rreal := BoundedGaps.Maynard.engelsmaMaynardRealRadius alpha N)
      (Y := tupleMaynardDiagonal largePowerTuple alpha largeTupleCandidate N)
      hNpos hW hphi hLnat hLreal)

theorem tendsto_normalizedLargeTupleYDiagonal
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (((N : ℝ) / BoundedGaps.Maynard.engelsmaMaynardModulus N) *
        largeTupleYDiagonal alpha N) /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  have hnatural := tendsto_normalizedLargeTupleMaynardDiagonal halpha
  have hratio :=
    (BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_div_realRadius
      halpha).pow (Fintype.card largePowerTuple)
  have hmul := hnatural.mul hratio
  simpa using hmul.congr' (by
    filter_upwards [
      eventually_normalizedLargeTupleYDiagonal_eq_natural_mul_logRatio halpha]
      with N hN
    exact hN.symm)

end

end MaynardBFT.Sieve
