/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCenterSelection
import ErdosProblems.Erdos984.HunterFinite

/-!
# Construction of Hunter's finite recurrence datum
-/

open Set Function MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

/-- The Fourier and probabilistic constructions supply the exact recurrence
datum required by the finite coloring argument. -/
lemma exists_hunterRecurrenceData (D : ℕ) (hD : 400 ≤ D) :
    Nonempty (HunterRecurrenceData D) := by
  classical
  obtain ⟨theta, htheta, hstep⟩ :=
    exists_hunter_full_rotation D (by omega)
  obtain ⟨center₀, hseparated₀, hhits⟩ :=
    exists_hunter_center_groups D hD htheta
  choose chosenL hchosenL using hhits
  have hopportunity : ∀
      (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)),
      ∃ t < hunterX D, ∃ u : EuclideanSpace ℝ (Fin D),
        additiveOrbit theta (P.start + t * P.step) =
          center₀ (y, chosenL P y) + euclideanToTorus u ∧
        radialBin (hunterDelta D) u ≤ hunterK D := by
    intro P y
    exact radial_opportunity_of_mem_positiveSet D (by omega) theta
      P.start P.step (hchosenL P y)
  choose chosenT hchosenT chosenU hchosenOrbit hchosenBin using hopportunity
  let I := Fin (hunterY D) × Fin (hunterGroupSize D)
  have hcardI : Fintype.card I = hunterM D := by
    simp only [I, Fintype.card_prod, Fintype.card_fin]
    exact hunterY_mul_groupSize D
  let e : I ≃ Fin (hunterM D) :=
    Fintype.equivOfCardEq (by simpa using hcardI)
  let chosenIndex (P : BoundedAP (hunterN D) (hunterX D))
      (y : Fin (hunterY D)) : Fin (hunterM D) :=
    e (y, chosenL P y)
  have chosenIndex_injective
      (P : BoundedAP (hunterN D) (hunterX D)) :
      Injective (chosenIndex P) := by
    intro y z hyz
    have hpairs : (y, chosenL P y) = (z, chosenL P z) :=
      e.injective hyz
    exact congrArg Prod.fst hpairs
  let center : Fin (hunterM D) → UnitAddTorus (Fin D) :=
    fun j ↦ center₀ (e.symm j)
  let selected : BoundedAP (hunterN D) (hunterX D) →
      Finset (Fin (hunterM D)) :=
    fun P ↦ Finset.univ.image (chosenIndex P)
  let target : BoundedAP (hunterN D) (hunterX D) →
      Fin (hunterM D) → Fin (hunterK D + 1) :=
    fun P j ↦ ⟨radialBin (hunterDelta D) (chosenU P (e.symm j).1),
      Nat.lt_succ_of_le (hchosenBin P (e.symm j).1)⟩
  have hcardSelected : ∀ P, (selected P).card = hunterY D := by
    intro P
    change (Finset.univ.image (chosenIndex P)).card = hunterY D
    rw [Finset.card_image_of_injective _ (chosenIndex_injective P)]
    simp
  have hopportunities :
      RadialOpportunities center (hunterDelta D) theta selected target := by
    intro P j hj
    change j ∈ Finset.univ.image (chosenIndex P) at hj
    obtain ⟨y, _hy, hyj⟩ := Finset.mem_image.mp hj
    subst j
    refine ⟨chosenT P y, hchosenT P y, chosenU P y, ?_, ?_⟩
    · simpa only [center, chosenIndex, Equiv.symm_apply_apply] using
        hchosenOrbit P y
    · simp only [target, chosenIndex, Equiv.symm_apply_apply]
  have hseparated : TorusCenterThreeSeparated center (hunterRho D) := by
    intro j₀ j₁ j₂ hclose
    have hsep := hseparated₀ (e.symm j₀) (e.symm j₁) (e.symm j₂) (by
      simpa only [center] using hclose)
    exact ⟨e.symm.injective hsep.1, e.symm.injective hsep.2⟩
  exact ⟨{
    center := center
    theta := theta
    selected := selected
    target := target
    card_selected := hcardSelected
    opportunities := hopportunities
    separated := hseparated
    step := hstep }⟩

end

end Erdos984
