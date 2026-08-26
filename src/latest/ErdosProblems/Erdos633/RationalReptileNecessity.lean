import ErdosProblems.Erdos633.RationalReptileAngles
import ErdosProblems.Erdos633.IrrationalReptileNecessity

/-!
# Complete necessity for nonsquare reptilings

The new rational-angle branch combines the actual boundary-matrix cosine
degree bound with the finite cyclotomic angle list. Together with the
irrational branch, every nonsquare reptiling now has one of the eight listed
shapes. Rational-angle nonreptile tilings are handled by the subsequent
`Classification` module using geometric conjugation and finite corner data.
-/

namespace Erdos633

theorem Triangle.hasListedNonsquareShape_of_permuted_thirty (P : Triangle)
    (h : PermutedTriple P.cornerAngle ![Real.pi / 6, Real.pi / 2, Real.pi / 3]) :
    HasListedNonsquareShape P := by
  obtain ⟨Q, hQP, hA, hB, hC⟩ :=
    P.exists_relabel_of_permuted_angles (Real.pi / 6) (Real.pi / 2) (Real.pi / 3) h
  exact ⟨Q, hQP, Or.inr (Or.inr (Or.inl ⟨hA, hB, hC⟩))⟩

theorem Triangle.hasListedNonsquareShape_of_rational_quadratic_cosines (P : Triangle)
    (hrat : P.CommensurableAngles)
    (hcos : ∀ k : Fin 3, IsIntegral ℚ (Real.cos (P.cornerAngle k)) ∧
      (minpoly ℚ (Real.cos (P.cornerAngle k))).natDegree ≤ 2) :
    HasListedNonsquareShape P := by
  by_cases hinj : Function.Injective P.cornerAngle
  · exact P.hasListedNonsquareShape_of_permuted_thirty
      (P.permuted_thirty_of_rational_quadratic_cosines hrat hinj hcos)
  · exact P.hasListedNonsquareShape_of_equal_angles
      (P.equal_angles_of_not_injective_cornerAngle hinj)

theorem CongruentTiling.nonsquare_reptile_outer_cosines_degree_le_two
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hperm : PermutedTriple P.cornerAngle R.cornerAngle) :
    ∀ k : Fin 3, IsIntegral ℚ (Real.cos (P.cornerAngle k)) ∧
      (minpoly ℚ (Real.cos (P.cornerAngle k))).natDegree ≤ 2 := by
  have h := T.nonsquare_reptile_cosines_degree_le_two hN hperm
  obtain ⟨e, he⟩ := hperm
  intro k
  have hk := h (e.symm k)
  rw [← he (e.symm k), e.apply_symm_apply] at hk
  exact hk

theorem CongruentTiling.hasListedNonsquareShape_of_rational_reptile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : R.CommensurableAngles)
    (hperm : PermutedTriple P.cornerAngle R.cornerAngle) : HasListedNonsquareShape P := by
  exact P.hasListedNonsquareShape_of_rational_quadratic_cosines
    (T.commensurableAngles_of_tile hR)
    (T.nonsquare_reptile_outer_cosines_degree_le_two hN hperm)

theorem CongruentTiling.hasListedNonsquareShape_of_reptile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hperm : PermutedTriple P.cornerAngle R.cornerAngle) :
    HasListedNonsquareShape P := by
  by_cases hR : R.CommensurableAngles
  · exact T.hasListedNonsquareShape_of_rational_reptile hN hR hperm
  · exact T.hasListedNonsquareShape_of_irrational_tile hN hR

theorem CongruentTiling.rational_nonreptile_of_nonsquare_not_listed
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hP : ¬ HasListedNonsquareShape P) :
    R.CommensurableAngles ∧ ¬ PermutedTriple P.cornerAngle R.cornerAngle := by
  exact ⟨T.commensurableAngles_of_nonsquare_not_listed hN hP,
    fun h => hP (T.hasListedNonsquareShape_of_reptile hN h)⟩

end Erdos633
