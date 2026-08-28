import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactUniformBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactPairs
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactLowDegrees

/-!
# Uniform exactness at the normalization branch term

For every active subset of the three coordinate planes, genuine singular
analytic germs are exactly the tuples whose actual source-oriented axis
differences vanish. The smooth, double, and triple cases are handled inside
the proof, so the sheaf comparison needs no coordinate-label casts.
-/

noncomputable section

open Set CategoryTheory

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- Genuine singular restriction and actual incident-axis difference form
an exact pair for every set of active branches, including the empty set. -/
theorem orientedDifference_exact (s : Triangle) (S : Finset (Fin 3)) :
    Function.Exact (restrictionToBranches S).toAddMonoidHom (orientedDifference s S) := by
  intro f
  constructor
  · intro hf
    by_cases hS : S = ∅
    · subst S
      refine ⟨0, ?_⟩
      funext j
      exact isEmptyElim j
    have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hle : S.card ≤ 3 := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    have hcard : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
    rcases hcard with hcard | hcard | hcard
    · obtain ⟨j, hS⟩ := Finset.card_eq_one.mp hcard
      subst S
      obtain ⟨φ, hφ⟩ := restrictionToBranches_coordinate_surjective {j}
        ⟨j, Finset.mem_singleton_self j⟩ (f ⟨j, Finset.mem_singleton_self j⟩)
      refine ⟨φ, ?_⟩
      funext l
      have hl : l = ⟨j, Finset.mem_singleton_self j⟩ :=
        Subtype.ext (Finset.mem_singleton.mp l.property)
      rw [hl]
      exact hφ
    · obtain ⟨k, hk⟩ := (sourcePairEquiv s).surjective ⟨S, hcard⟩
      have hS : sourcePair s k = S := congrArg Subtype.val hk
      subst S
      let g : Fin 2 → BranchGerm := fun i => f (pairLabel s k i)
      have hg : pairDifference s k g = 0 :=
        congrFun hf ⟨k, Finset.Subset.refl _⟩
      obtain ⟨φ, hφ⟩ := (pairRestriction_exact s k g).mp hg
      refine ⟨φ, ?_⟩
      funext j
      obtain ⟨i, rfl⟩ := pairLabel_surjective s k j
      exact congrFun hφ i
    · have hS : S = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simp [hcard])
      subst S
      let g : Fin 3 → BranchGerm := fun j => f (tripleLabel j)
      have hg : orientedTripleDifference s g = 0 := by
        funext k
        exact congrFun hf ⟨k, Finset.subset_univ _⟩
      obtain ⟨φ, hφ⟩ := (orientedTripleRestriction_exact s g).mp hg
      refine ⟨φ, ?_⟩
      funext j
      exact congrFun hφ j.val
  · rintro ⟨φ, rfl⟩
    exact orientedDifference_restriction s S φ

/-- The compatibility criterion in the source's geometric labels, with
an actual restricted ambient-analytic germ as the extension. -/
theorem exists_restriction_iff_pair_compatible (s : Triangle) (S : Finset (Fin 3))
    (f : S → BranchGerm) :
    (∃ φ : RestrictedAnalyticGerm S, restrictionToBranches S φ = f) ↔
      ∀ k (hk : sourcePair s k ⊆ S),
        axisRestriction (plusAxisIndex s k) (f (selectedPlusBranch s S ⟨k, hk⟩)) -
          axisRestriction (minusAxisIndex s k) (f (selectedMinusBranch s S ⟨k, hk⟩)) = 0 :=
  (orientedDifference_exact s S f).symm.trans (orientedDifference_eq_zero_iff s S f)

theorem orientedDifference_ker (s : Triangle) (S : Finset (Fin 3)) :
    (orientedDifference s S).ker = (restrictionToBranches S).toAddMonoidHom.range :=
  AddMonoidHom.exact_iff.mp (orientedDifference_exact s S)

/-- The first two local sheaf arrows in the actual active branch labels. -/
def orientedBranchComplex (s : Triangle) (S : Finset (Fin 3)) : ShortComplex AddCommGrpCat where
  X₁ := AddCommGrpCat.of (RestrictedAnalyticGerm S)
  X₂ := AddCommGrpCat.of (S → BranchGerm)
  X₃ := AddCommGrpCat.of (IncidentCurve s S → AxisGerm)
  f := AddCommGrpCat.ofHom (restrictionToBranches S).toAddMonoidHom
  g := AddCommGrpCat.ofHom (orientedDifference s S)
  zero := AddCommGrpCat.ext (orientedDifference_restriction s S)

theorem orientedBranchComplex_exact (s : Triangle) (S : Finset (Fin 3)) :
    (orientedBranchComplex s S).Exact :=
  (ShortComplex.ab_exact_iff_function_exact (orientedBranchComplex s S)).mpr
    (orientedDifference_exact s S)

instance orientedBranchComplex_mono (s : Triangle) (S : Finset (Fin 3)) :
    Mono (orientedBranchComplex s S).f :=
  (AddCommGrpCat.mono_iff_injective _).mpr (restrictionToBranches_injective S)

/-- Smooth and double local models form a short exact sequence uniformly
in their active coordinate branches and actual incident curve labels. -/
theorem orientedBranchComplex_shortExact (s : Triangle) (S : Finset (Fin 3))
    (hS : S.card ≤ 2) : (orientedBranchComplex s S).ShortExact where
  exact := orientedBranchComplex_exact s S
  mono_f := orientedBranchComplex_mono s S
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr
    (orientedDifference_surjective_of_card_le_two s S hS)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
