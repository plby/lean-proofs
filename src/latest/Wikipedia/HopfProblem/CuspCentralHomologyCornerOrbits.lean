import Wikipedia.HopfProblem.CuspCollapseCentralProjection
import Wikipedia.HopfProblem.CuspStrata
import Wikipedia.HopfProblem.ToricHexagon

/-!
# The two actual quotient orbits of the six honeycomb corners

The six toric origins alternate between lower and upper integral triangles.
The existing exact quotient relation identifies origins precisely when their
triangle orientations agree. Their actual central-fibre images therefore form
exactly two distinct points, represented by corner zero and corner one.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricFan ToricComponent CuspRetraction CuspCollapse

/-- The literal central toric origin at a numbered honeycomb corner. -/
def cornerOrigin (k : Fin 6) : CentralFibre :=
  ⟨inclusion (zeroTriangle k) 0, by simp [Triangle.time]⟩

@[simp] theorem cornerOrigin_coe (k : Fin 6) :
    (cornerOrigin k : Space) = inclusion (zeroTriangle k) 0 := rfl

theorem zeroTriangle_upper_eq_iff_parity (k l : Fin 6) :
    (zeroTriangle k).upper = (zeroTriangle l).upper ↔ k.val % 2 = l.val % 2 := by
  have h : ∀ k l : Fin 6,
      (zeroTriangle k).upper = (zeroTriangle l).upper ↔ k.val % 2 = l.val % 2 := by decide
  exact h k l

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original central quotient projection of the actual toric corner. -/
def cornerPoint (k : Fin 6) : QuotientCentralFibre C ε :=
  centralProject C ε hε (cornerOrigin k)

@[simp] theorem cornerPoint_coe (k : Fin 6) :
    (cornerPoint C ε hε k : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.centralChartMap C ε hε (zeroTriangle k) CuspQuotient.centralOrigin := rfl

/-- This is equality in the actual cusp quotient, not in an imposed corner relation. -/
theorem cornerPoint_eq_iff_parity (k l : Fin 6) :
    cornerPoint C ε hε k = cornerPoint C ε hε l ↔ k.val % 2 = l.val % 2 := by
  rw [Subtype.ext_iff, cornerPoint_coe, cornerPoint_coe,
    CuspQuotient.centralChartMap_origin_eq_iff, zeroTriangle_upper_eq_iff_parity]

/-- The canonical image of every even-indexed toric corner. -/
def evenPole : QuotientCentralFibre C ε := cornerPoint C ε hε 0

/-- The canonical image of every odd-indexed toric corner. -/
def oddPole : QuotientCentralFibre C ε := cornerPoint C ε hε 1

theorem cornerPoint_eq_evenPole_iff (k : Fin 6) :
    cornerPoint C ε hε k = evenPole C ε hε ↔ k.val % 2 = 0 := by
  simpa only [evenPole, Fin.val_zero, Nat.zero_mod] using
    cornerPoint_eq_iff_parity C ε hε k 0

theorem cornerPoint_eq_oddPole_iff (k : Fin 6) :
    cornerPoint C ε hε k = oddPole C ε hε ↔ k.val % 2 = 1 := by
  simpa [oddPole] using
    cornerPoint_eq_iff_parity C ε hε k 1

theorem pole_ne : evenPole C ε hε ≠ oddPole C ε hε := by
  intro h
  have hp := (cornerPoint_eq_iff_parity C ε hε 0 1).mp h
  norm_num at hp

theorem cornerPoint_eq_pole (k : Fin 6) :
    cornerPoint C ε hε k =
      if k.val % 2 = 0 then evenPole C ε hε else oddPole C ε hε := by
  by_cases hk : k.val % 2 = 0
  · rw [if_pos hk]
    exact (cornerPoint_eq_evenPole_iff C ε hε k).mpr hk
  · rw [if_neg hk]
    apply (cornerPoint_eq_oddPole_iff C ε hε k).mpr
    have hlt := Nat.mod_lt k.val (by decide : 0 < 2)
    omega

/-- All six actual corner images form precisely these two distinct quotient points. -/
theorem range_cornerPoint :
    Set.range (cornerPoint C ε hε) = {evenPole C ε hε, oddPole C ε hε} := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one k.val with hk | hk
    · exact Or.inl ((cornerPoint_eq_evenPole_iff C ε hε k).mpr hk)
    · exact Or.inr ((cornerPoint_eq_oddPole_iff C ε hε k).mpr hk)
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem cornerPoint_range_ncard : (Set.range (cornerPoint C ε hε)).ncard = 2 := by
  rw [range_cornerPoint]
  exact Set.ncard_pair (pole_ne C ε hε)

end Wikipedia.HopfProblem.CuspCentralHomology
