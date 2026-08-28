import Wikipedia.NoExoticSixSphere.StableSixSphereMapEquality

/-!
# Actual finite lifts and homotopies retain the original stable class

These identities refer to the directed limit of actual sphere maps.
They do not replace the original maps by formal generators.
-/

noncomputable section

namespace NoExoticSixSphere.StableSixSphereMaps

theorem ofMap_liftMap {k l : ℕ} (h : k ≤ l) (f : StageMap k) :
    ofMap (liftMap h f) = ofMap f := by
  have he := DirectLimit.eq_of_le (f := transitionHom) ⟨k, classOf f⟩ l h
  change ofMap f = (Quotient.mk _ ⟨l, transition k l h (classOf f)⟩ : Class) at he
  rw [transition_classOf] at he
  exact he.symm

theorem ofMap_homotopic {k : ℕ} {f g : StageMap k} (h : f.Homotopic g) :
    ofMap f = ofMap g := (ofMap_eq_iff_finite_homotopic f g).mpr ⟨0, h⟩

end NoExoticSixSphere.StableSixSphereMaps
