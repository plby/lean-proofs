import ErdosProblems.Erdos633.ActualGroupOneNecessity
import ErdosProblems.Erdos633.ActualOneTwentyRationality
import ErdosProblems.Erdos633.ReferenceRelabelling
import ErdosProblems.Erdos633.Sufficiency

/-!
# Necessity for all six exceptional patterns

Every irrational-angle nonreptile nonsquare tiling satisfies one of the eight
published conditions. All reference and outer label permutations are allowed.
This does not assert the remaining rational-angle or reptile necessity cases.
-/

namespace Erdos633

theorem CongruentTiling.commensurableSides_of_exceptional_pattern
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (h : ExceptionalAnglePattern R.angleA R.angleB P.cornerAngle) : R.CommensurableSides := by
  rcases h with ⟨hrel, hU | hV⟩ | ⟨hrel, hW | hY | hZ | hU⟩
  · exact T.groupOne_U_commensurableSides hR hrel hU
  · exact T.groupOne_V_commensurableSides hR hrel hV
  · exact T.oneTwenty_W_commensurableSides hR hrel hW
  · exact T.oneTwenty_Y_commensurableSides hR hrel hY
  · exact T.oneTwenty_Z_commensurableSides hR hrel hZ
  · exact T.oneTwenty_U_two_commensurableSides hR hrel hU

theorem CongruentTiling.irrational_nonisosceles_nonreptile_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles) (hP : ¬ P.Isosceles) (hsim : ¬ P.Similar R) :
    R.CommensurableSides ∧ P.CommensurableSides := by
  rcases T.irrational_geometric_shape_alternatives hR with h | h | ⟨e, he⟩
  · exact False.elim (hP h)
  · exact False.elim (hsim h)
  · let S := R.relabel e
    let U : CongruentTiling P S N := T.of_reference_carrier_eq (R.relabel_carrier e)
    have hS : ¬ S.CommensurableAngles := fun h => hR ((R.commensurableAngles_relabel_iff e).mp h)
    have hA : S.angleA = R.cornerAngle (e 0) := R.cornerAngle_relabel e 0
    have hB : S.angleB = R.cornerAngle (e 1) := R.cornerAngle_relabel e 1
    rw [← hA, ← hB] at he
    have hrat := U.commensurableSides_of_exceptional_pattern hS he
    have hr := (R.commensurableSides_relabel_iff e).mp hrat
    exact ⟨hr, T.commensurableSides_of_reference hr⟩

theorem CongruentTiling.groupOne_U_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle ![R.angleA, 2 * R.angleA, 2 * R.angleB]) :
    HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  obtain ⟨hdouble, hrat⟩ := U.groupOne_U_necessary_angle_condition hR hrel hA hB hC
  refine ⟨Q, hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; right; right; left
  exact ⟨hdouble, (mem_rationalReals_iff _).mp hrat⟩

theorem CongruentTiling.groupOne_V_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle ![2 * R.angleA, R.angleB, R.angleA + R.angleB]) :
    HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  have hc := U.groupOne_V_necessary_integer_condition hN hR hrel hA hB hC
  refine ⟨Q, hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; right; right; right; left
  exact hc

theorem CongruentTiling.oneTwenty_W_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB]) :
    HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  obtain ⟨hsixty, hrat⟩ := U.oneTwenty_W_necessary_angle_condition hR hrel hA hB hC
  let S := Q.relabel (Equiv.swap 1 2)
  have hSA : S.angleA = Q.angleA := by
    have he : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    simpa [Triangle.cornerAngle, he] using Q.cornerAngle_relabel (Equiv.swap 1 2) 0
  have hSC : S.angleC = Q.angleB := by
    simpa [Triangle.cornerAngle] using Q.cornerAngle_relabel (Equiv.swap 1 2) 2
  refine ⟨S, (Q.relabel_carrier _).trans hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; left
  refine ⟨hSC.trans hsixty, ?_⟩
  rw [hSA]
  exact (mem_rationalReals_iff _).mp hrat

theorem CongruentTiling.oneTwenty_Y_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle
      ![R.angleA, 2 * R.angleB, 2 * R.angleA + R.angleB]) : HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  obtain ⟨hangle, hrat⟩ := U.oneTwenty_Y_necessary_angle_condition hR hrel hA hB hC
  refine ⟨Q, hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; right; right; right; right
  exact ⟨hangle, (mem_rationalReals_iff _).mp hrat⟩

theorem CongruentTiling.oneTwenty_Z_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle
      ![2 * R.angleA, 2 * R.angleB, R.angleA + R.angleB]) : HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  obtain ⟨hsixty, hrat⟩ := U.oneTwenty_Z_necessary_angle_condition hR hrel hA hB hC
  refine ⟨Q, hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; left
  exact ⟨hsixty, (mem_rationalReals_iff _).mp hrat⟩

theorem CongruentTiling.oneTwenty_U_two_hasListedNonsquareShape
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (h : PermutedTriple P.cornerAngle ![R.angleA, 2 * R.angleA, 3 * R.angleB]) :
    HasListedNonsquareShape P := by
  obtain ⟨Q, hQ, hA, hB, hC⟩ := P.exists_relabel_of_permuted_angles _ _ _ h
  let U : CongruentTiling Q R N := T.of_carrier_eq hQ.symm
  obtain ⟨hdouble, hrat⟩ := U.oneTwenty_U_two_necessary_angle_condition hR hrel hA hB hC
  refine ⟨Q, hQ, ?_⟩
  unfold ListedNonsquareAngles
  right; right; right; right; left
  exact ⟨hdouble, (mem_rationalReals_iff _).mp hrat⟩

theorem CongruentTiling.hasListedNonsquareShape_of_exceptional_pattern
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles)
    (h : ExceptionalAnglePattern R.angleA R.angleB P.cornerAngle) : HasListedNonsquareShape P := by
  rcases h with ⟨hrel, hU | hV⟩ | ⟨hrel, hW | hY | hZ | hU⟩
  · exact T.groupOne_U_hasListedNonsquareShape hR hrel hU
  · exact T.groupOne_V_hasListedNonsquareShape hN hR hrel hV
  · exact T.oneTwenty_W_hasListedNonsquareShape hR hrel hW
  · exact T.oneTwenty_Y_hasListedNonsquareShape hR hrel hY
  · exact T.oneTwenty_Z_hasListedNonsquareShape hR hrel hZ
  · exact T.oneTwenty_U_two_hasListedNonsquareShape hR hrel hU

theorem Triangle.hasListedNonsquareShape_of_equal_angles (P : Triangle)
    (h : P.angleA = P.angleB ∨ P.angleB = P.angleC ∨ P.angleC = P.angleA) :
    HasListedNonsquareShape P := by
  rcases h with h | h | h
  · exact ⟨P, rfl, Or.inl h⟩
  · refine ⟨P.rotate, P.rotate_carrier, Or.inl ?_⟩
    simpa only [Triangle.angleA_rotate, Triangle.angleB_rotate] using h
  · refine ⟨P.rotate.rotate, P.rotate.rotate_carrier.trans P.rotate_carrier, Or.inl ?_⟩
    simpa only [Triangle.angleA_rotate, Triangle.angleB_rotate, Triangle.angleC_rotate] using h

theorem CongruentTiling.permuted_angles_or_listed_of_irrational
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles) :
    PermutedTriple P.cornerAngle R.cornerAngle ∨ HasListedNonsquareShape P := by
  rcases T.irrational_angle_classification hR with h | h | ⟨e, he⟩
  · exact Or.inr (P.hasListedNonsquareShape_of_equal_angles h)
  · exact Or.inl h
  · let S := R.relabel e
    let U : CongruentTiling P S N := T.of_reference_carrier_eq (R.relabel_carrier e)
    have hS : ¬ S.CommensurableAngles := fun h => hR ((R.commensurableAngles_relabel_iff e).mp h)
    have hA : S.angleA = R.cornerAngle (e 0) := R.cornerAngle_relabel e 0
    have hB : S.angleB = R.cornerAngle (e 1) := R.cornerAngle_relabel e 1
    rw [← hA, ← hB] at he
    exact Or.inr (U.hasListedNonsquareShape_of_exceptional_pattern hN hS he)

theorem CongruentTiling.similar_or_listed_of_irrational
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles) :
    P.Similar R ∨ HasListedNonsquareShape P := by
  exact (T.permuted_angles_or_listed_of_irrational hN hR).imp
    (P.similar_of_permuted_angles R) id

theorem CongruentTiling.hasListedNonsquareShape_of_irrational_nonreptile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (hR : ¬ R.CommensurableAngles) (hsim : ¬ P.Similar R) :
    HasListedNonsquareShape P :=
  (T.similar_or_listed_of_irrational hN hR).resolve_left hsim

end Erdos633
