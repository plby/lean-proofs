import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactLowDegrees

/-!
# Uniform exactness at the incident-axis term

The alternating evaluation is present only when all three coordinate
branches are active. For smaller active sets the difference is surjective,
so its image is the kernel of the zero augmentation. This gives one exactness
statement for the actual source-oriented branch and incident-curve labels.
-/

noncomputable section

open Set CategoryTheory

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- A source curve label regarded as incident when all planes are active. -/
def fullIncidentCurve (s : Triangle) (S : Finset (Fin 3)) (hS : S = Finset.univ)
    (k : Fin 3) : IncidentCurve s S :=
  ⟨k, by rw [hS]; exact Finset.subset_univ _⟩

/-- Actual alternating axis-germ evaluation at a triple point, and zero
when the active branch set is not the full triple. -/
def orientedAugmentation (s : Triangle) (S : Finset (Fin 3)) :
    (IncidentCurve s S → AxisGerm) →+ ℂ where
  toFun g := if hS : S = Finset.univ then
    eval (0 : ℂ) (g (fullIncidentCurve s S hS 0)) -
      eval (0 : ℂ) (g (fullIncidentCurve s S hS 1)) +
      eval (0 : ℂ) (g (fullIncidentCurve s S hS 2)) else 0
  map_zero' := by
    dsimp
    split_ifs <;> simp
  map_add' f g := by
    dsimp
    split_ifs
    · simp only [map_add]
      abel
    · simp

theorem orientedAugmentation_eq_zero_of_ne (s : Triangle) (S : Finset (Fin 3))
    (hS : S ≠ Finset.univ) (g : IncidentCurve s S → AxisGerm) :
    orientedAugmentation s S g = 0 := by
  simp [orientedAugmentation, hS]

@[simp] theorem orientedAugmentation_univ (s : Triangle)
    (g : IncidentCurve s (Finset.univ : Finset (Fin 3)) → AxisGerm) :
    orientedAugmentation s Finset.univ g =
      tripleAugmentation (fun k => g ⟨k, Finset.subset_univ _⟩) := by
  simp [orientedAugmentation, tripleAugmentation, fullIncidentCurve]

theorem activeSet_card_le_two_of_ne_univ (S : Finset (Fin 3)) (hS : S ≠ Finset.univ) :
    S.card ≤ 2 := by
  have hle : S.card ≤ 3 := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  by_contra h
  have hc : S.card = 3 := by omega
  exact hS (Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simp [hc]))

/-- Uniform middle exactness, using actual analytic restriction differences
and the source's single alternating sign convention. -/
theorem orientedDifference_aug_exact (s : Triangle) (S : Finset (Fin 3)) :
    Function.Exact (orientedDifference s S) (orientedAugmentation s S) := by
  intro g
  by_cases hS : S = Finset.univ
  · subst S
    change orientedAugmentation s Finset.univ g = 0 ↔
      ∃ f, orientedDifference s Finset.univ f = g
    rw [orientedAugmentation_univ]
    constructor
    · intro hg
      obtain ⟨f, hf⟩ := (orientedTripleDifference_exact s
        (fun k => g ⟨k, Finset.subset_univ _⟩)).mp hg
      refine ⟨fun j => f j.val, ?_⟩
      funext k
      exact congrFun hf k.val
    · rintro ⟨f, rfl⟩
      exact orientedTripleAugmentation_difference s (fun j => f (tripleLabel j))
  · constructor
    · intro _
      exact orientedDifference_surjective_of_card_le_two s S
        (activeSet_card_le_two_of_ne_univ S hS) g
    · intro _
      exact orientedAugmentation_eq_zero_of_ne s S hS g

theorem orientedAugmentation_difference (s : Triangle) (S : Finset (Fin 3))
    (f : S → BranchGerm) : orientedAugmentation s S (orientedDifference s S f) = 0 :=
  (orientedDifference_aug_exact s S).apply_apply_eq_zero f

theorem orientedAugmentation_ker (s : Triangle) (S : Finset (Fin 3)) :
    (orientedAugmentation s S).ker = (orientedDifference s S).range :=
  AddMonoidHom.exact_iff.mp (orientedDifference_aug_exact s S)

/-- At an actual full triple, alternating evaluation is surjective. -/
theorem orientedAugmentation_surjective_of_eq_univ (s : Triangle) (S : Finset (Fin 3))
    (hS : S = Finset.univ) : Function.Surjective (orientedAugmentation s S) := by
  subst S
  intro c
  obtain ⟨g, hg⟩ := tripleAugmentation_surjective c
  refine ⟨fun k => g k.val, ?_⟩
  rw [orientedAugmentation_univ]
  exact hg

/-- The actual oriented branch-to-axis-to-point germ maps. Exactness is at
the axis term; off the full triple the last map is zero, not surjective. -/
def orientedAxisComplex (s : Triangle) (S : Finset (Fin 3)) : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (S → BranchGerm)
  X₂ := AddCommGrpCat.of (IncidentCurve s S → AxisGerm)
  X₃ := AddCommGrpCat.of ℂ
  f := AddCommGrpCat.ofHom (orientedDifference s S)
  g := AddCommGrpCat.ofHom (orientedAugmentation s S)
  zero := AddCommGrpCat.ext (orientedAugmentation_difference s S)

theorem orientedAxisComplex_exact (s : Triangle) (S : Finset (Fin 3)) :
    (orientedAxisComplex s S).Exact :=
  (ShortComplex.ab_exact_iff_function_exact (orientedAxisComplex s S)).mpr
    (orientedDifference_aug_exact s S)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
