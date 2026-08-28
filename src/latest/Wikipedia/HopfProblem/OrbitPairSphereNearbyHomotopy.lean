import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Relative normalization homotopies between nearby actual sphere maps
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SpherePathHomotopy

open NoExoticSixSphere

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

def nearbyHomotopyRel (f g : C(X, Sphere n))
    (h : ∀ x, dist (g x).val (f x).val < 1) (S : Set X)
    (hS : ∀ x ∈ S, g x = f x) : f.HomotopyRel g S := by
  let gv : C(X, EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨fun x => (g x).val, continuous_subtype_val.comp g.continuous⟩
  have hn : ∀ x, gv x ≠ 0 := fun x => nearby_unit_ne_zero (f x) (gv x) (h x)
  have he : normalizedSphereMap gv hn = g := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (g x))
  let H : f.Homotopy g := (nearbyNormalizationHomotopy f gv h).cast rfl he
  refine { toHomotopy := H, prop' := ?_ }
  intro t x hx
  apply Subtype.ext
  change NormedSpace.normalize ((f x).val + (t : ℝ) • ((g x).val - (f x).val)) = (f x).val
  rw [hS x hx, sub_self, smul_zero, add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (f x))

end Wikipedia.HopfProblem.OrbitPair.SpherePathHomotopy
