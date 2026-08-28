import Wikipedia.NoExoticSixSphere.RankOneOperators
import Wikipedia.NoExoticSixSphere.SardTheorem

/-!
# Generic avoidance of rank at most one

Every bad parameter has the form `ℓ.smulRight w - D x`. If the space of
triples `(x,ℓ,w)` has smaller dimension than the operator space, every value
of this smooth parametrization is critical. The proved Sard theorem makes
its image null, and hence almost every actual operator translation avoids
rank at most one at every source point.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.OperatorRank

variable {X V W : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

def rankOneParameter (D : X → V →L[ℝ] W) (q : X × ((V →L[ℝ] ℝ) × W)) : V →L[ℝ] W :=
  q.2.1.smulRight q.2.2 - D q.1

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem contDiff_rankOneParameter (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D) :
    ContDiff ℝ ∞ (rankOneParameter D) :=
  ((contDiff_fst.comp contDiff_snd).smulRight (contDiff_snd.comp contDiff_snd)).sub
    (hD.comp contDiff_fst)

theorem ae_rank_gt_one [MeasurableSpace (V →L[ℝ] W)] [BorelSpace (V →L[ℝ] W)]
    (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D)
    (hd : finrank ℝ X + (finrank ℝ V + finrank ℝ W) <
      finrank ℝ V * finrank ℝ W) :
    ∀ᵐ A ∂μ, ∀ x, 1 < finrank ℝ (D x + A).range := by
  have hdim : finrank ℝ (X × ((V →L[ℝ] ℝ) × W)) < finrank ℝ (V →L[ℝ] W) := by
    simpa only [finrank_prod, finrank_operator, finrank_self, mul_one] using hd
  have hcrit (q : X × ((V →L[ℝ] ℝ) × W)) :
      ¬ Surjective (fderiv ℝ (rankOneParameter D) q) := by
    intro hs
    have hle := LinearMap.finrank_le_finrank_of_surjective
      (f := (fderiv ℝ (rankOneParameter D) q).toLinearMap) hs
    omega
  have hnull := Sard.measure_criticalValues_eq_zero μ isOpen_univ
    (contDiff_rankOneParameter D hD).contDiffOn
  rw [ae_iff]
  apply measure_mono_null _ hnull
  intro A hA
  simp only [mem_ofPred_eq, not_forall, not_lt] at hA
  obtain ⟨x, hx⟩ := hA
  obtain ⟨ℓ, w, hfactor⟩ := exists_smulRight_of_rank_le_one (D x + A) hx
  refine ⟨(x, ℓ, w), ⟨mem_univ _, hcrit _⟩, ?_⟩
  change ℓ.smulRight w - D x = A
  rw [← hfactor]
  abel

end NoExoticSixSphere.OperatorRank
