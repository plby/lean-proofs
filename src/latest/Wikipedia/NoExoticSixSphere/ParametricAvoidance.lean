import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Generic avoidance of a smooth image of sufficiently small dimension

For a submersive joint parameter/source family, parametric Sard applied to
the actual incidence equation excludes a lower-dimensional smooth image for
almost every parameter. The open domain may couple parameters and source.
-/

noncomputable section

open Set Function Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.ParametricAvoidance

variable {P X Z F : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def incidence (D : P × X → F) (G : Z → F) (q : P × (X × Z)) : F :=
  D (q.1, q.2.1) - G q.2.2

def domain (U : Opens (P × X)) : Opens (P × (X × Z)) :=
  ⟨{q | (q.1, q.2.1) ∈ U},
    U.isOpen.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))⟩

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F] in
theorem contDiffOn_incidence (D : P × X → F) (G : Z → F) (U : Opens (P × X))
    (hD : ContDiffOn ℝ ∞ D U) (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (incidence D G) (domain (Z := Z) U) :=
  (hD.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
    (fun _ hq ↦ hq)).sub ((hG.comp (contDiff_snd.comp contDiff_snd)).contDiffOn)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Z] [FiniteDimensional ℝ F] in
theorem surjective_fderiv_incidence (D : P × X → F) (G : Z → F) (U : Opens (P × X))
    (hD : ContDiffOn ℝ ∞ D U) (hG : ContDiff ℝ ∞ G)
    (q : P × (X × Z)) (hq : q ∈ domain U)
    (hs : Surjective (fderiv ℝ D (q.1, q.2.1))) :
    Surjective (fderiv ℝ (incidence D G) q) := by
  let k : P × X → P × (X × Z) := fun r ↦ (r.1, (r.2, q.2.2))
  have hk : ContDiff ℝ ∞ k := contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hIa := (contDiffOn_incidence D G U hD hG).contDiffAt
    ((domain U).isOpen.mem_nhds hq)
  have hI : DifferentiableAt ℝ (incidence D G) q := hIa.differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ D (q.1, q.2.1) :=
    (hD.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun r ↦ D r - G q.2.2)
      ((fderiv ℝ (incidence D G) q).comp (fderiv ℝ k (q.1, q.2.1))) (q.1, q.2.1) := by
    have hc := hI.hasFDerivAt.comp (q.1, q.2.1)
      ((hk.differentiable (by simp) (q.1, q.2.1)).hasFDerivAt)
    exact hc
  have he := hc.unique (hDd.hasFDerivAt.sub_const (G q.2.2))
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨fderiv ℝ k (q.1, q.2.1) v,
    (congrArg (fun L : P × X →L[ℝ] F ↦ L v) he).trans hv⟩

theorem ae_avoids_image_on [MeasurableSpace P] [BorelSpace P]
    (μ : Measure P) [IsAddHaarMeasure μ] (D : P × X → F) (G : Z → F)
    (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U) (hG : ContDiff ℝ ∞ G)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q))
    (hd : finrank ℝ X + finrank ℝ Z < finrank ℝ F) :
    ∀ᵐ p ∂μ, ∀ x, (p, x) ∈ U → ∀ z, D (p, x) ≠ G z := by
  have h := ParametricRegular.ae_parameters_on μ (incidence D G) (domain U)
    (contDiffOn_incidence D G U hD hG)
    (fun q hq _ ↦ surjective_fderiv_incidence D G U hD hG q hq (hs _ hq))
  apply h.mono
  intro p hp x hx z he
  have hz : incidence D G (p, x, z) = 0 := sub_eq_zero.mpr he
  have hsurj := hp (x, z) hx hz
  have hle := LinearMap.finrank_le_finrank_of_surjective
    (f := (fderiv ℝ (fun r : X × Z ↦ incidence D G (p, r)) (x, z)).toLinearMap) hsurj
  rw [finrank_prod] at hle
  omega

end NoExoticSixSphere.ParametricAvoidance
