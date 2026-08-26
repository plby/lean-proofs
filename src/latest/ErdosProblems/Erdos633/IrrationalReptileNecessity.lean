import ErdosProblems.Erdos633.UnsplitReptile
import ErdosProblems.Erdos633.MissingCornerReptile
import ErdosProblems.Erdos633.ActualRightReptileNecessity

/-!
# Complete necessity for tilings with irrational reference angles

Three unsplit corners contradict the negative boundary-matrix eigenvalue.
Otherwise a missing corner label can be moved to the third position, with
the actual counts transported through the chosen labelled isometries.
The angle ledger and signed-boundary parity then make that angle right.
Together with the right-reptile and exceptional-family results, this proves
the listed condition for every nonsquare tiling whose tile angles are not
all rational multiples of pi. Rational-angle tiles remain a separate case.
-/

namespace Erdos633

theorem CongruentTiling.irrational_scalene_aligned_reptile_has_right_angle
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hinj : Function.Injective R.cornerAngle)
    (hangle : ∀ j : Fin 3, P.cornerAngle j = R.cornerAngle j) :
    ∃ k : Fin 3, R.cornerAngle k = Real.pi / 2 := by
  by_cases hpos : ∀ k : Fin 3, 0 < T.outerCornerCount k
  · exact False.elim (hN (T.all_outer_types_aligned_reptile_isSquare hinj hangle hpos))
  push Not at hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : T.outerCornerCount k = 0 := by omega
  let e : Equiv.Perm (Fin 3) := Equiv.swap k 2
  let S := R.relabel e
  let Q := P.relabel e
  let U : CongruentTiling P S N := T.of_reference_carrier_eq (R.relabel_carrier e)
  let V : CongruentTiling Q S N := U.of_carrier_eq (P.relabel_carrier e).symm
  have hS : ¬ S.CommensurableAngles := fun h =>
    hR ((R.commensurableAngles_relabel_iff e).mp h)
  have hU : U.outerCornerCount 2 = 0 := by
    calc
      U.outerCornerCount 2 = T.outerCornerCount (e 2) :=
        T.outerCornerCount_of_reference_relabel e 2
      _ = 0 := by simpa only [e, Equiv.swap_apply_right] using hk0
  have hV : V.outerCornerCount 2 = 0 :=
    (U.outerCornerCount_of_outer_relabel e 2).trans hU
  have hA : Q.angleA = S.angleA :=
    (P.cornerAngle_relabel e 0).trans
      ((hangle (e 0)).trans (R.cornerAngle_relabel e 0).symm)
  have hB : Q.angleB = S.angleB :=
    (P.cornerAngle_relabel e 1).trans
      ((hangle (e 1)).trans (R.cornerAngle_relabel e 1).symm)
  have hright := V.missing_angle_right_of_nonsquare_aligned_reptile hN hS hV hA hB
  exact ⟨e 2, (R.cornerAngle_relabel e 2).symm.trans hright⟩

theorem CongruentTiling.irrational_scalene_reptile_has_right_angle
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hinj : Function.Injective R.cornerAngle)
    (hperm : PermutedTriple P.cornerAngle R.cornerAngle) :
    ∃ k : Fin 3, R.cornerAngle k = Real.pi / 2 := by
  obtain ⟨e, he⟩ := hperm
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hangle (j : Fin 3) : Q.cornerAngle j = R.cornerAngle j :=
    (P.cornerAngle_relabel e j).trans (he j)
  exact U.irrational_scalene_aligned_reptile_has_right_angle hN hR hinj hangle

theorem CongruentTiling.hasListedNonsquareShape_of_irrational_tile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles) : HasListedNonsquareShape P := by
  rcases T.permuted_angles_or_listed_of_irrational hN hR with hperm | hlisted
  · by_cases hinj : Function.Injective R.cornerAngle
    · have hright := T.irrational_scalene_reptile_has_right_angle hN hR hinj hperm
      exact T.hasListedNonsquareShape_of_irrational_right_reptile hN hR hright hperm
    · obtain ⟨e, he⟩ := hperm
      have hP : ¬ Function.Injective P.cornerAngle := by
        intro hPinj
        apply hinj
        intro i j hij
        apply e.injective
        apply hPinj
        rw [he i, he j]
        exact hij
      exact P.hasListedNonsquareShape_of_equal_angles
        (P.equal_angles_of_not_injective_cornerAngle hP)
  · exact hlisted

theorem CongruentTiling.commensurableAngles_of_nonsquare_not_listed
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hP : ¬ HasListedNonsquareShape P) : R.CommensurableAngles := by
  by_contra hR
  exact hP (T.hasListedNonsquareShape_of_irrational_tile hN hR)

theorem CongruentTiling.hasListedNonsquareShape_of_irrational_outer
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hP : ¬ P.CommensurableAngles) : HasListedNonsquareShape P := by
  exact T.hasListedNonsquareShape_of_irrational_tile hN
    (fun hR => hP (T.commensurableAngles_of_tile hR))

theorem Triangle.admitsNonsquareTiling_iff_listed_of_irrational_angles (P : Triangle)
    (hP : ¬ P.CommensurableAngles) :
    AdmitsNonsquareTiling P ↔ HasListedNonsquareShape P := by
  constructor
  · rintro ⟨N, R, hN, ⟨T⟩⟩
    exact T.hasListedNonsquareShape_of_irrational_outer hN hP
  · exact P.admitsNonsquareTiling_of_listed_shape

end Erdos633
