import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverSections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyProjectiveCocycle

/-!
# Actual one-cocycle splitting on the zero-ray three-open cover

Actual overlap sections pull back through the genuine inverse-blowdown
coordinates to the literal projective analytic cocycle. The constructed
entire cochain pulls back through actual blowdown to holomorphic sections
on the three whole blowup opens. Their differences are the original
sections, not merely equal classes in a replacement cohomology model.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

theorem coefficient01_triple (s : Section (pairOpen 0 1)) (q : tripleDomain) :
    coefficient pair01Biholomorph s q = s (tripleToPair01 (tripleBiholomorph q)) := by
  calc
    _ = coefficient pair01Biholomorph s
        (pair01Biholomorph.symm (tripleToPair01 (tripleBiholomorph q))) :=
      congrArg (coefficient pair01Biholomorph s) (pair01_symm_triple q).symm
    _ = _ := coefficient_apply_symm _ _ _

theorem coefficient02_triple (s : Section (pairOpen 0 2)) (q : tripleDomain) :
    coefficient pair02Biholomorph s q = s (tripleToPair02 (tripleBiholomorph q)) := by
  calc
    _ = coefficient pair02Biholomorph s
        (pair02Biholomorph.symm (tripleToPair02 (tripleBiholomorph q))) :=
      congrArg (coefficient pair02Biholomorph s) (pair02_symm_triple q).symm
    _ = _ := coefficient_apply_symm _ _ _

theorem coefficient12_triple (s : Section (pairOpen 1 2)) (q : tripleDomain) :
    coefficient pair12Biholomorph s ((q : ℂ × ℂ).1⁻¹, (q : ℂ × ℂ).2 / (q : ℂ × ℂ).1) =
      s (tripleToPair12 (tripleBiholomorph q)) := by
  calc
    _ = coefficient pair12Biholomorph s
        (pair12Biholomorph.symm (tripleToPair12 (tripleBiholomorph q))) :=
      congrArg (coefficient pair12Biholomorph s) (pair12_symm_triple q).symm
    _ = _ := coefficient_apply_symm _ _ _

/-- The actual section cocycle in its proved literal projective coordinates. -/
def chartCocycle (c01 : Section (pairOpen 0 1)) (c02 : Section (pairOpen 0 2))
    (c12 : Section (pairOpen 1 2))
    (hc : ThreeCover.cochainDifferential componentSheaf cover (c01, c02, c12) = 0) :
    ProjectiveCocycle.ChartCocycle where
  zeroOne := coefficient pair01Biholomorph c01
  zeroTwo := coefficient pair02Biholomorph c02
  oneTwo := coefficient pair12Biholomorph c12
  zeroOne_analytic := coefficient_analytic pair01Biholomorph c01
  zeroTwo_analytic := coefficient_analytic pair02Biholomorph c02
  oneTwo_analytic := coefficient_analytic pair12Biholomorph c12
  cocycle := by
    intro x y hx hy
    let q : tripleDomain := ⟨(x, y), hx, hy⟩
    change coefficient pair01Biholomorph c01 (q : ℂ × ℂ) +
      coefficient pair12Biholomorph c12 ((q : ℂ × ℂ).1⁻¹, (q : ℂ × ℂ).2 / (q : ℂ × ℂ).1) =
        coefficient pair02Biholomorph c02 (q : ℂ × ℂ)
    rw [coefficient01_triple, coefficient12_triple, coefficient02_triple]
    have he := congrArg (fun s : Section tripleOpen => s (tripleBiholomorph q)) hc
    change c01 (tripleToPair01 (tripleBiholomorph q)) -
      c02 (tripleToPair02 (tripleBiholomorph q)) +
        c12 (tripleToPair12 (tripleBiholomorph q)) = 0 at he
    linear_combination he

/-- The genuine finite-cover one-cocycle condition holds for actual O on E₀. -/
theorem cechOneExact : ThreeCover.CechOneExact componentSheaf cover := by
  intro c01 c02 c12 hc
  change Section (pairOpen 0 1) at c01
  change Section (pairOpen 0 2) at c02
  change Section (pairOpen 1 2) at c12
  let h := chartCocycle c01 c02 c12 hc
  obtain ⟨g0, g1, g2, hg0, hg1, hg2, h01, h02, h12⟩ := h.exists_entire_cochain
  refine ⟨entireSection 0 g0 hg0, entireSection 1 g1 hg1, entireSection 2 g2 hg2, ?_, ?_, ?_⟩
  · apply ContMDiffMap.ext
    intro x
    obtain ⟨q, rfl⟩ := pair01Biholomorph.surjective x
    change g0 (coordinates 0 (pair01Biholomorph q)) -
      g1 (coordinates 1 (pair01Biholomorph q)) = c01 (pair01Biholomorph q)
    rw [coordinates_pair01_zero, coordinates_pair01_one]
    have he := h01 (q : ℂ × ℂ).1 (q : ℂ × ℂ).2 q.property
    change coefficient pair01Biholomorph c01 (q : ℂ × ℂ) = _ at he
    exact he.symm.trans (coefficient_apply pair01Biholomorph c01 q)
  · apply ContMDiffMap.ext
    intro x
    obtain ⟨q, rfl⟩ := pair02Biholomorph.surjective x
    change g0 (coordinates 0 (pair02Biholomorph q)) -
      g2 (coordinates 2 (pair02Biholomorph q)) = c02 (pair02Biholomorph q)
    rw [coordinates_pair02_zero, coordinates_pair02_two]
    have he := h02 (q : ℂ × ℂ).1 (q : ℂ × ℂ).2 q.property
    change coefficient pair02Biholomorph c02 (q : ℂ × ℂ) = _ at he
    exact he.symm.trans (coefficient_apply pair02Biholomorph c02 q)
  · apply ContMDiffMap.ext
    intro x
    obtain ⟨q, rfl⟩ := pair12Biholomorph.surjective x
    change g1 (coordinates 1 (pair12Biholomorph q)) -
      g2 (coordinates 2 (pair12Biholomorph q)) = c12 (pair12Biholomorph q)
    rw [coordinates_pair12_one, coordinates_pair12_two]
    have he := h12 (q : ℂ × ℂ).1 (q : ℂ × ℂ).2 q.property
    change coefficient pair12Biholomorph c12 (q : ℂ × ℂ) = _ at he
    exact he.symm.trans (coefficient_apply pair12Biholomorph c12 q)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
