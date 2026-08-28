import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverOverlaps

/-! # Literal coordinate transitions and restrictions on the actual cover intersections -/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

@[simp] theorem coordinates_pair01_zero (q : firstDomain) :
    coordinates 0 (pair01Biholomorph q) = q :=
  coordinates_liftMap 0 firstDomain pair01_domain_punctured q

theorem coordinates_pair01_one (q : firstDomain) :
    coordinates 1 (pair01Biholomorph q) = ((q : ℂ × ℂ).1⁻¹, (q : ℂ × ℂ).2 / (q : ℂ × ℂ).1) := by
  change standardProjectiveCoords 1 (ToricComponent.blowdown (pair01Biholomorph q)) = _
  rw [blowdown_pair01Biholomorph, standardProjectiveCoords_zero_one]

@[simp] theorem coordinates_pair02_zero (q : secondDomain) :
    coordinates 0 (pair02Biholomorph q) = q :=
  coordinates_liftMap 0 secondDomain pair02_domain_punctured q

theorem coordinates_pair02_two (q : secondDomain) :
    coordinates 2 (pair02Biholomorph q) = ((q : ℂ × ℂ).1 / (q : ℂ × ℂ).2, (q : ℂ × ℂ).2⁻¹) := by
  change standardProjectiveCoords 2 (ToricComponent.blowdown (pair02Biholomorph q)) = _
  rw [blowdown_pair02Biholomorph, standardProjectiveCoords_zero_two]

@[simp] theorem coordinates_pair12_one (q : secondDomain) :
    coordinates 1 (pair12Biholomorph q) = q :=
  coordinates_liftMap 1 secondDomain pair12_domain_punctured q

theorem coordinates_pair12_two (q : secondDomain) :
    coordinates 2 (pair12Biholomorph q) = ((q : ℂ × ℂ).2⁻¹, (q : ℂ × ℂ).1 / (q : ℂ × ℂ).2) := by
  change standardProjectiveCoords 2 (ToricComponent.blowdown (pair12Biholomorph q)) = _
  rw [blowdown_pair12Biholomorph, standardProjectiveCoords_one_two]

@[simp] theorem coordinates_triple_zero (q : tripleDomain) :
    coordinates 0 (tripleBiholomorph q) = q :=
  coordinates_liftMap 0 tripleDomain triple_domain_punctured q

theorem coordinates_triple_one (q : tripleDomain) :
    coordinates 1 (tripleBiholomorph q) = ((q : ℂ × ℂ).1⁻¹, (q : ℂ × ℂ).2 / (q : ℂ × ℂ).1) := by
  change standardProjectiveCoords 1 (ToricComponent.blowdown (tripleBiholomorph q)) = _
  rw [blowdown_tripleBiholomorph, standardProjectiveCoords_zero_one]

def tripleToPair01 (x : tripleOpen) : pairOpen 0 1 := ⟨x, x.property.1⟩
def tripleToPair02 (x : tripleOpen) : pairOpen 0 2 := ⟨x, x.property.1.1, x.property.2⟩
def tripleToPair12 (x : tripleOpen) : pairOpen 1 2 := ⟨x, x.property.1.2, x.property.2⟩

@[simp] theorem pair01_symm_triple (q : tripleDomain) :
    (pair01Biholomorph.symm (tripleToPair01 (tripleBiholomorph q)) : ℂ × ℂ) = q :=
  coordinates_triple_zero q

@[simp] theorem pair02_symm_triple (q : tripleDomain) :
    (pair02Biholomorph.symm (tripleToPair02 (tripleBiholomorph q)) : ℂ × ℂ) = q :=
  coordinates_triple_zero q

theorem pair12_symm_triple (q : tripleDomain) :
    (pair12Biholomorph.symm (tripleToPair12 (tripleBiholomorph q)) : ℂ × ℂ) =
      ((q : ℂ × ℂ).1⁻¹, (q : ℂ × ℂ).2 / (q : ℂ × ℂ).1) :=
  coordinates_triple_one q

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
