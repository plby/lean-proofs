import Wikipedia.NoExoticSixSphere.StableSixSphereStages

/-!
# Stable classes of actual sixth-stem sphere maps have finite witnesses

This is the directed limit of the actual homotopy classes and actual
suspension maps. Equality with the constant class is equivalent to an
ordinary nullhomotopy after some finite number of suspensions. It is not
defined to be a group of order two, and no such computation is proved here.
-/

noncomputable section

namespace NoExoticSixSphere.StableSixSphereMaps

abbrev Class := DirectLimit Stage transitionHom

def ofMap {k : ℕ} (f : StageMap k) : Class := Quotient.mk _ ⟨k, classOf f⟩

def nullClass : Class := Quotient.mk _ ⟨0, stageZero 0⟩

theorem nullClass_eq_stage (k : ℕ) :
    nullClass = (Quotient.mk _ ⟨k, stageZero k⟩ : Class) := by
  apply Quotient.sound
  refine ⟨k, Nat.zero_le k, le_rfl, ?_⟩
  change transition 0 k (Nat.zero_le k) (stageZero 0) = transition k k le_rfl (stageZero k)
  rw [transition_stageZero, transition_self]

theorem ofMap_suspend {k : ℕ} (f : StageMap k) :
    ofMap (SphereMapSuspension.map f) = ofMap f := by
  have h := DirectLimit.eq_of_le (f := transitionHom) ⟨k, classOf f⟩ (k + 1) (Nat.le_succ k)
  have ht : transition k (k + 1) (Nat.le_succ k) (classOf f) =
      classOf (SphereMapSuspension.map f) := Nat.leRecOn_succ' (classOf f)
  change ofMap f = (Quotient.mk _ ⟨k + 1,
    transition k (k + 1) (Nat.le_succ k) (classOf f)⟩ : Class) at h
  rw [ht] at h
  exact h.symm

theorem ofMap_eq_nullClass_iff_lift {k : ℕ} (f : StageMap k) :
    ofMap f = nullClass ↔ ∃ (l : ℕ) (h : k ≤ l), (liftMap h f).Nullhomotopic := by
  rw [nullClass_eq_stage k]
  constructor
  · intro h
    obtain ⟨l, hl, _, he⟩ := Quotient.exact h
    change transition k l hl (classOf f) = transition k l hl (stageZero k) at he
    rw [transition_classOf, transition_stageZero] at he
    exact ⟨l, hl, (classOf_eq_stageZero_iff _).mp he⟩
  · rintro ⟨l, hl, hnull⟩
    apply Quotient.sound
    refine ⟨l, hl, hl, ?_⟩
    change transition k l hl (classOf f) = transition k l hl (stageZero k)
    rw [transition_classOf, transition_stageZero]
    exact (classOf_eq_stageZero_iff _).mpr hnull

/-- Zero in the constructed direct limit supplies a genuine finite nullhomotopy witness. -/
theorem ofMap_eq_nullClass_iff {k : ℕ} (f : StageMap k) :
    ofMap f = nullClass ↔ ∃ r : ℕ, (SphereMapSuspension.iterate f r).Nullhomotopic := by
  rw [ofMap_eq_nullClass_iff_lift]
  constructor
  · rintro ⟨l, hl, hnull⟩
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hl
    exact ⟨r, (liftMap_add_nullhomotopic_iff k r f).mp hnull⟩
  · rintro ⟨r, hr⟩
    exact ⟨k + r, Nat.le_add_right k r, (liftMap_add_nullhomotopic_iff k r f).mpr hr⟩

end NoExoticSixSphere.StableSixSphereMaps
