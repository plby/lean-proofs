import Wikipedia.NoExoticSixSphere.GenericFamilyClosedCurve
import Wikipedia.NoExoticSixSphere.UnorderedFamilyDoublePoints
import Wikipedia.NoExoticSixSphere.ReflectionQuotientChart

/-!
# A genuine boundary chart on the unordered generic-family double curve

At each singular diagonal point the actual unordered double-point closure
has an open partial homeomorphism to a half-line. The chart source is the
quotient image of an actual ordered chart, and its coordinate is the absolute
value of the ordered coordinate. Zero corresponds exactly to diagonal pairs.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

open OperatorRank InvolutionQuotient

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_unordered_closed_curve_chart (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2))
    (p : ℝ × V) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    ∃ hc : (p.1, (p.2, p.2)) ∈ closure (doublePoints f),
    ∃ c : OpenPartialHomeomorph (closure (doublePoints f)) ℝ,
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints f) HalfLine,
      (⟨(p.1, (p.2, p.2)), hc⟩ : closure (doublePoints f)) ∈ c.source ∧
      c ⟨(p.1, (p.2, p.2)), hc⟩ = 0 ∧
      unorderedProj f ⟨(p.1, (p.2, p.2)), hc⟩ ∈ d.source ∧
      d (unorderedProj f ⟨(p.1, (p.2, p.2)), hc⟩) = ⟨0, le_rfl⟩ ∧
      d.source = unorderedProj f '' c.source ∧ d.target = Subtype.val ⁻¹' c.target ∧
      (∀ r ∈ c.source, (d (unorderedProj f r)).val = |c r|) ∧
      (∀ r ∈ c.source, (d (unorderedProj f r)).val = 0 ↔ r.val.2.1 = r.val.2.2) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (c.symm s).val) c.target := by
  obtain ⟨a, hc, c, hcp, hcz, hca, hcswap, hcneg, hcsmooth⟩ :=
    FamilyLinearCoordinates.exists_closed_curve_of_regular_three_six f hf hreg p hp
  let k : ReflectionChart (swapClosure f) := ⟨c, hcswap, hcneg⟩
  let d := k.quotientChart (swapClosure_involutive f) (swapClosure f).continuous
  have hdcenter := k.quotientChart_center (swapClosure_involutive f)
    (swapClosure f).continuous hcp hcz
  refine ⟨hc, c, d, hcp, hcz, hdcenter.1, hdcenter.2, rfl, rfl, ?_, ?_, hcsmooth⟩
  · intro r hr
    exact k.quotientChart_apply (swapClosure_involutive f) (swapClosure f).continuous hr
  · intro r hr
    exact (k.quotientChart_zero_iff_fixed (swapClosure_involutive f)
      (swapClosure f).continuous hr).trans (swapClosure_fixed_iff f r)

end NoExoticSixSphere.FamilyEmbedding
