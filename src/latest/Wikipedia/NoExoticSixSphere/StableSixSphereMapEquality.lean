import Wikipedia.NoExoticSixSphere.StableSixSphereMaps

/-!
# Stable equality supplies an actual finite homotopy between both original maps

Unpack equality in the genuine directed limit, not just equality with
the constant class. Different stages have a common later stage. At equal
initial stages, the witness is a homotopy after the same finite number
of literal sphere suspensions. Dimension casts transport only equal
natural numbers and do not introduce arbitrary sphere identifications.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

theorem homotopic_iff_of_heq {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    {f g : C(Sphere m, Sphere n)} {f' g' : C(Sphere m', Sphere n')}
    (hf : HEq f f') (hg : HEq g g') : f.Homotopic g ↔ f'.Homotopic g' := by
  subst m'
  subst n'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

end NoExoticSixSphere.SphereMapSuspension

namespace NoExoticSixSphere.StableSixSphereMaps

theorem liftMap_add_homotopic_iff (k r : ℕ) (f g : StageMap k) :
    (liftMap (Nat.le_add_right k r) f).Homotopic (liftMap (Nat.le_add_right k r) g) ↔
      (SphereMapSuspension.iterate f r).Homotopic (SphereMapSuspension.iterate g r) :=
  SphereMapSuspension.homotopic_iff_of_heq
    (Nat.add_right_comm k r 8) (Nat.add_right_comm k r 2)
    (liftMap_add_heq k r f) (liftMap_add_heq k r g)

theorem ofMap_eq_iff_lift {k l : ℕ} (f : StageMap k) (g : StageMap l) :
    ofMap f = ofMap g ↔
      ∃ (r : ℕ) (hk : k ≤ r) (hl : l ≤ r), (liftMap hk f).Homotopic (liftMap hl g) := by
  constructor
  · intro h
    obtain ⟨r, hk, hl, he⟩ := Quotient.exact h
    change transition k r hk (classOf f) = transition l r hl (classOf g) at he
    rw [transition_classOf, transition_classOf] at he
    exact ⟨r, hk, hl, (classOf_eq_iff _ _).mp he⟩
  · rintro ⟨r, hk, hl, he⟩
    apply Quotient.sound
    refine ⟨r, hk, hl, ?_⟩
    change transition k r hk (classOf f) = transition l r hl (classOf g)
    rw [transition_classOf, transition_classOf]
    exact (classOf_eq_iff _ _).mpr he

theorem ofMap_eq_iff_finite_homotopic {k : ℕ} (f g : StageMap k) :
    ofMap f = ofMap g ↔
      ∃ r : ℕ, (SphereMapSuspension.iterate f r).Homotopic
        (SphereMapSuspension.iterate g r) := by
  rw [ofMap_eq_iff_lift]
  constructor
  · rintro ⟨l, hl, _, he⟩
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hl
    exact ⟨r, (liftMap_add_homotopic_iff k r f g).mp he⟩
  · rintro ⟨r, hr⟩
    exact ⟨k + r, Nat.le_add_right k r, Nat.le_add_right k r,
      (liftMap_add_homotopic_iff k r f g).mpr hr⟩

end NoExoticSixSphere.StableSixSphereMaps
