/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.JohnDifferenceComparison

/-!
# The rank dichotomy contradiction for a dense thin candidate

This is the quantitative core of the separating-hyperplane part of PZ
Lemma 14.  Lemma 7 supplies a John progression for the thin region.  If its
rank drops, the CFP dimension-increase estimate saves one dilation factor;
if its rank is full, Lemma 7 supplies the small-volume factor.  Either
alternative contradicts irreducibility once the two displayed scalar
hierarchies hold.
-/

namespace Erdos186.PZ.Intersection

open OneStepAssembly

noncomputable section

set_option autoImplicit false

/-- Constants from PZ Lemma 7 also control the rank-dichotomy contradiction
for every selected CFP witness whose core lies in the thin region. -/
theorem exists_slabJohnContradictionConstants
    (hJohn : PZLemmaSevenStatement) (d : ℕ) (hd : 0 < d) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {s D k loss referenceVolume boxFactor : ℕ}
        {A : Finset (LatticePoint d)}
        (W : CFP.EnhancedCFPWitness A s D k loss)
        (hrank : W.rank = d)
        (B : IntegerBox d)
        (Omega : Set (ConvexDensity.EuclideanPoint d))
        (eta gamma : ℝ),
        ConvexDensity.IsConvexBody (boxRealization B) →
        0 < eta → Convex ℝ Omega → Omega ⊆ boxRealization B →
        (boxLatticePointsIn B Omega).Nonempty →
        ConvexDensity.relativeVolume Omega (boxRealization B) ≤
          ENNReal.ofReal eta →
        1 ≤ eta * (B.carrier.card : ℝ) →
        W.core ⊆ boxLatticePointsIn B Omega →
        (0 : LatticePoint d) ∈ boxLatticePointsIn B Omega →
        B.carrier.card ≤ boxFactor * referenceVolume →
        0 < referenceVolume →
        0 < gamma →
        gamma * (referenceVolume : ℝ) ≤
          (W.progression.volume : ℝ) →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * boxFactor < (k : ℝ) * gamma →
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * eta * boxFactor < gamma →
        False := by
  obtain ⟨factorBound, constant, hconstant, hLemma⟩ := hJohn d hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro s D k loss referenceVolume boxFactor A W hrank B Omega eta gamma
    hB heta hOmega hsub hnonempty hrelative hscale hcore hzero hbox
    hrefPos hgamma hlower hlowHierarchy hfullHierarchy
  obtain ⟨J, hfactor, hcoarse, hbranch⟩ :=
    hLemma B Omega eta hB heta hOmega hsub hnonempty hrelative hscale
  have hJrank : J.rank ≤ d := J.rank_le
  have hWrank : J.rank ≤ W.rank := by simpa [hrank] using hJrank
  have hestimate := cfpWitness_dimensionIncrease_centeredDiscreteJohn_real
    W J hcore hzero hWrank
  have hboxReal : (B.carrier.card : ℝ) ≤
      (boxFactor : ℝ) * referenceVolume := by
    exact_mod_cast hbox
  have hrefRealPos : (0 : ℝ) < referenceVolume := by exact_mod_cast hrefPos
  have hdenOne : (1 : ℝ) ≤ 2 * (W.scaleDen : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * W.scaleDen by
      have := W.scaleDen_pos
      omega)
  have hdenPow : (2 * (W.scaleDen : ℝ)) ^ J.rank ≤
      (2 * (W.scaleDen : ℝ)) ^ d :=
    pow_le_pow_right₀ hdenOne hJrank
  have hthreePow : (3 : ℝ) ^ J.rank ≤ (3 : ℝ) ^ d :=
    pow_le_pow_right₀ (by norm_num) hJrank
  rcases hbranch with hrankLow | ⟨hrankFull, hsharp⟩
  · have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast W.k_pos
    have hkPow : (k : ℝ) ≤ (k : ℝ) ^ (W.rank - J.rank) := by
      calc
        (k : ℝ) = (k : ℝ) ^ 1 := by simp
        _ ≤ (k : ℝ) ^ (W.rank - J.rank) := by
          apply pow_le_pow_right₀ hkOne
          simpa [hrank] using (show 1 ≤ d - J.rank by omega)
    have hupper :
        (2 : ℝ) ^ W.rank * (2 * (W.scaleDen : ℝ)) ^ J.rank *
            ((3 : ℝ) ^ J.rank * J.certificate.outer.volume) ≤
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * ((boxFactor : ℝ) * referenceVolume) := by
      have hleft :
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ J.rank ≤
            (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d :=
        mul_le_mul_of_nonneg_left hdenPow (by positivity)
      have hcoeff :
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ J.rank *
              (3 : ℝ) ^ J.rank ≤
            (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d :=
        mul_le_mul hleft hthreePow (by positivity) (by positivity)
      calc
        (2 : ℝ) ^ W.rank * (2 * (W.scaleDen : ℝ)) ^ J.rank *
              ((3 : ℝ) ^ J.rank * J.certificate.outer.volume) =
            ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ J.rank *
              (3 : ℝ) ^ J.rank) * J.certificate.outer.volume := by
          rw [hrank]
          ring
        _ ≤ ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d) * (constant * B.carrier.card) :=
          mul_le_mul hcoeff hcoarse (by positivity) (by positivity)
        _ ≤ ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d) *
                (constant * ((boxFactor : ℝ) * referenceVolume)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hboxReal (by positivity)
        _ = (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * ((boxFactor : ℝ) * referenceVolume) := by ring
    have hstrict :
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * ((boxFactor : ℝ) * referenceVolume) <
            ((k : ℝ) * gamma) * referenceVolume := by
      calc
        _ = ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * boxFactor) * referenceVolume := by ring
        _ < ((k : ℝ) * gamma) * referenceVolume :=
          mul_lt_mul_of_pos_right hlowHierarchy hrefRealPos
    have hlower' : ((k : ℝ) * gamma) * referenceVolume ≤
        (k : ℝ) ^ (W.rank - J.rank) * W.progression.volume := by
      calc
        ((k : ℝ) * gamma) * referenceVolume =
            (k : ℝ) * (gamma * referenceVolume) := by ring
        _ ≤ (k : ℝ) * W.progression.volume := by gcongr
        _ ≤ (k : ℝ) ^ (W.rank - J.rank) * W.progression.volume := by
          gcongr
    exact (not_lt_of_ge (hlower'.trans (hestimate.trans hupper))) hstrict
  · have hestimate' : (W.progression.volume : ℝ) ≤
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
          ((3 : ℝ) ^ d * J.certificate.outer.volume) := by
      simpa [hrank, hrankFull] using hestimate
    have hupper :
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
            ((3 : ℝ) ^ d * J.certificate.outer.volume) ≤
          (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
            constant * eta * ((boxFactor : ℝ) * referenceVolume) := by
      calc
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              ((3 : ℝ) ^ d * J.certificate.outer.volume) =
            ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d) * J.certificate.outer.volume := by ring
        _ ≤ ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d) *
                (constant * eta * (B.carrier.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsharp (by positivity)
        _ ≤ ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d *
              (3 : ℝ) ^ d) *
                (constant * eta * ((boxFactor : ℝ) * referenceVolume)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hboxReal (by positivity)
        _ = (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * eta * ((boxFactor : ℝ) * referenceVolume) := by ring
    have hstrict :
        (2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * eta * ((boxFactor : ℝ) * referenceVolume) <
            gamma * referenceVolume := by
      calc
        _ = ((2 : ℝ) ^ d * (2 * (W.scaleDen : ℝ)) ^ d * (3 : ℝ) ^ d *
              constant * eta * boxFactor) * referenceVolume := by ring
        _ < gamma * referenceVolume :=
          mul_lt_mul_of_pos_right hfullHierarchy hrefRealPos
    exact (not_lt_of_ge (hlower.trans (hestimate'.trans hupper))) hstrict

end

end Erdos186.PZ.Intersection
