/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterCenterHitting
import ErdosProblems.Erdos984.HunterRotation

/-!
# Simultaneous selection of separated, progression-hitting centers
-/

open Set Function MeasureTheory Metric
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

/-- The union of all group-miss events, over bounded progressions and groups. -/
def hunterAllGroupMissSet (D : ℕ) (theta : UnitAddTorus (Fin D)) :
    Set ((Fin (hunterY D) × Fin (hunterGroupSize D)) →
      UnitAddTorus (Fin D)) :=
  ⋃ i : BoundedAP (hunterN D) (hunterX D) × Fin (hunterY D),
    hunterGroupMissSet D theta i.1 i.2

lemma measurableSet_hunterAllGroupMissSet
    (D : ℕ) (theta : UnitAddTorus (Fin D)) :
    MeasurableSet (hunterAllGroupMissSet D theta) := by
  unfold hunterAllGroupMissSet
  exact MeasurableSet.iUnion fun i ↦
    measurableSet_hunterGroupMissSet D theta i.1 i.2

lemma volume_hunterAllGroupMissSet_lt_quarter
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta) :
    volume (hunterAllGroupMissSet D theta) <
      ENNReal.ofReal ((1 : ℝ) / 4) := by
  let I := BoundedAP (hunterN D) (hunterX D) × Fin (hunterY D)
  let q : ENNReal := ENNReal.ofReal (Real.exp (-((D : ℝ) ^ (9 * D))))
  calc
    volume (hunterAllGroupMissSet D theta) ≤
        ∑ i : I, volume (hunterGroupMissSet D theta i.1 i.2) := by
      exact MeasureTheory.measure_iUnion_fintype_le volume
        (fun i : I ↦ hunterGroupMissSet D theta i.1 i.2)
    _ ≤ ∑ _i : I, q := by
      gcongr with i
      exact volume_hunterGroupMissSet_le D hD htheta i.1 i.2
    _ = (Fintype.card I : ℕ) • q := by simp
    _ = (Fintype.card I : ENNReal) * q := by rw [nsmul_eq_mul]
    _ ≤ (hunterN D ^ 2 * hunterY D : ENNReal) * q := by
      gcongr
      have hcard := Nat.mul_le_mul_right (hunterY D)
        (card_boundedAP_le_sq (hunterN D) (hunterX D))
      simp only [I, Fintype.card_prod, Fintype.card_fin]
      exact_mod_cast hcard
    _ = ENNReal.ofReal
        (((hunterN D ^ 2 * hunterY D : ℕ) : ℝ) *
          Real.exp (-((D : ℝ) ^ (9 * D)))) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul]
      simpa only [q, ENNReal.ofReal_natCast] using
        (ENNReal.ofReal_mul (Nat.cast_nonneg
          (hunterN D ^ 2 * hunterY D))
          (q := Real.exp (-((D : ℝ) ^ (9 * D))))).symm
    _ < ENNReal.ofReal ((1 : ℝ) / 4) := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2
        (hunter_hit_union_real_cost_lt_quarter D hD)

/-- One center tuple simultaneously has separated second differences and a
hit in every one of the `hunterY D` independent groups for every bounded
progression. -/
lemma exists_hunter_center_groups
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta) :
    ∃ center : (Fin (hunterY D) × Fin (hunterGroupSize D)) →
        UnitAddTorus (Fin D),
      TorusCenterThreeSeparated center (hunterRho D) ∧
      ∀ (P : BoundedAP (hunterN D) (hunterX D)) (y : Fin (hunterY D)),
        ∃ l : Fin (hunterGroupSize D),
          center (y, l) ∈ hunterOrbitPositiveSet D theta P.start P.step := by
  let : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  let I := Fin (hunterY D) × Fin (hunterGroupSize D)
  let U : Set (I → UnitAddTorus (Fin D)) :=
    torusCenterSeparationBadSet (D := Fin D) (ι := I) (hunterRho D)
  let V : Set (I → UnitAddTorus (Fin D)) := hunterAllGroupMissSet D theta
  have hU : volume U < ENNReal.ofReal ((1 : ℝ) / 4) := by
    apply (volume_torusCenterSeparationBadSet_le
      (D := Fin D) (ι := I) (hunterRho_pos (D := D) (by omega)).le
      (hunter_four_mul_rho_le_half (D := D) (by omega))).trans_lt
    have hcard : Fintype.card I = hunterM D := by
      simp only [I, Fintype.card_prod, Fintype.card_fin]
      exact hunterY_mul_groupSize D
    rw [hcard]
    simpa only [Fintype.card_fin] using hunter_center_cost_lt_quarter D hD
  have hV : volume V < ENNReal.ofReal ((1 : ℝ) / 4) := by
    simpa only [V] using volume_hunterAllGroupMissSet_lt_quarter D hD htheta
  have hUV : volume (U ∪ V) < 1 := by
    apply (measure_union_le U V).trans_lt
    calc
      volume U + volume V < ENNReal.ofReal ((1 : ℝ) / 4) +
          ENNReal.ofReal ((1 : ℝ) / 4) := ENNReal.add_lt_add hU hV
      _ = ENNReal.ofReal ((1 : ℝ) / 2) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      _ < 1 := by norm_num
  have hne : U ∪ V ≠ Set.univ := by
    intro hEq
    rw [hEq, volume_centerSpace_univ] at hUV
    exact (lt_self_iff_false 1).mp hUV
  obtain ⟨center, hcenter⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hcenterU : center ∉ U := fun h ↦ hcenter (Or.inl h)
  have hcenterV : center ∉ V := fun h ↦ hcenter (Or.inr h)
  refine ⟨center, ?_, ?_⟩
  · apply torusCenterThreeSeparated_of_not_mem_badSet
    simpa only [U, I] using hcenterU
  · intro P y
    by_contra hmiss
    push Not at hmiss
    apply hcenterV
    apply Set.mem_iUnion_of_mem (P, y)
    exact hmiss

end

end Erdos984
