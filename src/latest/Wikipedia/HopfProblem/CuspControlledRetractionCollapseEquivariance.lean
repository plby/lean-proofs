import Wikipedia.HopfProblem.CuspControlledRetractionCollapse
import Wikipedia.HopfProblem.CuspPositiveRetractionEquivariance

/-!
# Equivariance of the independently prescribed collapse

The actual punctured polar factors transform by compact multiplication
and by the frozen phase shear.  Normalized positive coordinates transform
by the ordinary honeycomb lattice, so the prescribed collapse commutes
with the full compact torus and the genuine frozen lattice action.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction CuspCollapse CuspHoneycomb CuspPositive

def puncturedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : PuncturedPositiveTube η) : PuncturedPositiveTube η :=
  ⟨closedPositiveTranslate C₀ η v q.1, by
    change time (twistedTranslate (positiveTwist C₀) v (q.1.1 : Space)) ≠ 0
    rw [time_twistedTranslate]
    exact q.2⟩

def puncturedFrozenTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : PuncturedClosedTube η) : PuncturedClosedTube η :=
  ⟨closedTranslate (fun _ => C₀) η v x.1, by
    change time (twistedTranslate (fun _ => C₀) v (x.1 : Space)) ≠ 0
    rw [time_twistedTranslate]
    exact x.2⟩

@[simp] theorem puncturedFrozenTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (x : PuncturedClosedTube η) :
    ((puncturedFrozenTranslate C₀ η v x).1 : Space) =
      twistedTranslate (fun _ => C₀) v (x.1 : Space) := rfl

theorem puncturedFrozenTranslate_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (u : CompactTorus) (q : PuncturedPositiveTube η) :
    puncturedFrozenTranslate C₀ η v (puncturedPolarMap η (u, q)) =
      puncturedPolarMap η (phaseTransform C₀ v u, puncturedPositiveTranslate C₀ η v q) :=
  Subtype.ext (Subtype.ext (twistedTranslate_constant_polar C₀ v u (q.1.1 : Space)))

def puncturedCompactAction (η : ℝ) (u : CompactTorus) (x : PuncturedClosedTube η) :
    PuncturedClosedTube η :=
  ⟨closedCompactAction η u x.1, by
    change time (compactTorusAction u (x.1 : Space)) ≠ 0
    rw [← norm_ne_zero_iff, norm_time_compactTorusAction, norm_ne_zero_iff]
    exact x.2⟩

@[simp] theorem puncturedCompactAction_coe (η : ℝ) (u : CompactTorus)
    (x : PuncturedClosedTube η) :
    ((puncturedCompactAction η u x).1 : Space) = compactTorusAction u (x.1 : Space) := rfl

theorem puncturedCompactAction_polar (η : ℝ) (u w : CompactTorus)
    (q : PuncturedPositiveTube η) :
    puncturedCompactAction η u (puncturedPolarMap η (w, q)) =
      puncturedPolarMap η (u * w, q) :=
  Subtype.ext (Subtype.ext (compactTorusAction_mul u w (q.1.1 : Space)))

/-- Compact equivariance is unconditional: the map keeps the unique
compact phase and changes only the positive coordinate. -/
theorem prescribedCollapse_compact_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (u : CompactTorus) (x : PuncturedClosedTube η) :
    (prescribedCollapse C₀ η (puncturedCompactAction η u x) : Space) =
      compactTorusAction u (prescribedCollapse C₀ η x : Space) := by
  obtain ⟨⟨w, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  rw [puncturedCompactAction_polar, prescribedCollapse_polar, prescribedCollapse_polar,
    compactTorusAction_mul]

section Frozen

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ}
    (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε) (hηε : η < ε)

include hε1 hR hηε

theorem prescribedPositiveCollapse_equivariant (v : Fin 2 → ℤ)
    (q : PuncturedPositiveTube η) :
    prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q) =
      positiveCentralTranslate C₀ v (prescribedPositiveCollapse C₀ η q) := by
  change honeycombHomeomorph C₀
      (normalizedPosition C₀ ((closedPositiveTranslate C₀ η v q.1).1 : Space)) =
    positiveCentralTranslate C₀ v
      (honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1.1 : Space)))
  rw [normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v q.2,
    honeycombHomeomorph_equivariant]

/-- The prescribed collapse commutes with the genuine frozen action on
every nonzero small time fibre, independently of any constructed homotopy. -/
theorem prescribedCollapse_frozen_equivariant (v : Fin 2 → ℤ)
    (x : PuncturedClosedTube η) :
    (prescribedCollapse C₀ η (puncturedFrozenTranslate C₀ η v x) : Space) =
      twistedTranslate (fun _ => C₀) v (prescribedCollapse C₀ η x : Space) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := puncturedPolarMap_surjective η x
  rw [puncturedFrozenTranslate_polar, prescribedCollapse_puncturedPolarMap,
    prescribedCollapse_puncturedPolarMap]
  change compactTorusAction (phaseTransform C₀ v u)
      ((prescribedPositiveCollapse C₀ η (puncturedPositiveTranslate C₀ η v q)).1 : Space) =
    twistedTranslate (fun _ => C₀) v
      (compactTorusAction u ((prescribedPositiveCollapse C₀ η q).1 : Space))
  rw [prescribedPositiveCollapse_equivariant C₀ hε1 hR hηε]
  exact (twistedTranslate_constant_polar C₀ v u
    ((prescribedPositiveCollapse C₀ η q).1 : Space)).symm

end Frozen

end Wikipedia.HopfProblem.CuspControlledRetraction
