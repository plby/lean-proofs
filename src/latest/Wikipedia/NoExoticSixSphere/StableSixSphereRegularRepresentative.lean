import Wikipedia.NoExoticSixSphere.StableSixSphereMaps
import Wikipedia.NoExoticSixSphere.SphereConnectivity
import Wikipedia.NoExoticSixSphere.SardRegularValues

/-!
# Smooth regular representatives of the actual stable sphere-map classes

Each actual direct-limit class has a smooth representative and a regular
value. A nonconstant stable class has a surjective representative, so its
regular fiber is nonempty. These statements do not yet identify the collapse
of the induced framed fiber with the original stable class.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StableSixSphereMaps

theorem ofMap_eq_of_homotopic {k : ℕ} {f g : StageMap k} (h : f.Homotopic g) :
    ofMap f = ofMap g := by
  apply Quotient.sound
  refine ⟨k, le_rfl, le_rfl, ?_⟩
  change transition k k le_rfl (classOf f) = transition k k le_rfl (classOf g)
  rw [transition_self, transition_self]
  exact (classOf_eq_iff f g).mpr h

theorem exists_smooth_regular_representative (c : Class) :
    ∃ (k : ℕ) (g : StageMap k),
      ∃ _hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g,
        ∃ b : Sphere (k + 2),
          (∀ x, g x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x)) ∧
          ofMap g = c := by
  induction c using DirectLimit.induction transitionHom with
  | ih k x =>
    induction x using Quotient.inductionOn with
    | h f =>
      obtain ⟨g, hg, H⟩ := exists_smoothSphereRepresentative (I := 𝓡 (k + 8)) (k + 2) f
      obtain ⟨b, hb⟩ := (Sard.dense_regularValues hg).nonempty
      exact ⟨k, g, hg, b, hb, ofMap_eq_of_homotopic H.symm⟩

theorem surjective_of_stable_class_ne_null {k : ℕ} (f : StageMap k)
    (h : ofMap f ≠ nullClass) : Surjective f := by
  intro b
  by_contra! hmiss
  obtain ⟨z, hz⟩ := sphereMap_nullhomotopic_of_omitted_point (k + 2) f b hmiss
  exact h ((ofMap_eq_nullClass_iff f).mpr ⟨0, z, hz⟩)

theorem exists_nonempty_smooth_regular_representative (c : Class) (hc : c ≠ nullClass) :
    ∃ (k : ℕ) (g : StageMap k),
      ∃ _hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g,
        ∃ b : Sphere (k + 2),
          (∀ x, g x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x)) ∧
          ofMap g = c ∧ Nonempty {x : Sphere (k + 8) // g x = b} := by
  obtain ⟨k, g, hg, b, hreg, he⟩ := exists_smooth_regular_representative c
  have hs : Surjective g := surjective_of_stable_class_ne_null g (fun h ↦ hc (he.symm.trans h))
  obtain ⟨x, hx⟩ := hs b
  exact ⟨k, g, hg, b, hreg, he, ⟨⟨x, hx⟩⟩⟩

end NoExoticSixSphere.StableSixSphereMaps
