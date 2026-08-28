import Wikipedia.NoExoticSixSphere.WhitneySphereDerivative

/-!
# The Whitney sphere's unique crossing is transverse

At the poles the two derivative images are the graphs of minus and plus
the identity on the actual three-dimensional tail. Their sum is the whole
six-dimensional product, with explicit preimages.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization SphereCylinder SphereThreeTangentFrame

def modelDerivative (x : Sphere 3) : Vector 3 →L[ℝ] (Vector 3 × Vector 3) :=
  mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) map x

theorem modelDerivative_endPole (b : Bool) (v : Vector 3) :
    modelDerivative (endPole 2 b) v =
      (tail 2 (inclusionDerivative (endPole 2 b) v),
        (if b then (1 : ℝ) else -1) • tail 2 (inclusionDerivative (endPole 2 b) v)) :=
  mfderiv_map_endPole_apply b v

theorem transverse_poles :
    Surjective ((modelDerivative (endPole 2 false)).coprod
      (modelDerivative (endPole 2 true))) := by
  intro w
  obtain ⟨u, hu⟩ := tail_inclusion_surjective_endPole false ((1 / 2 : ℝ) • (w.1 - w.2))
  obtain ⟨v, hv⟩ := tail_inclusion_surjective_endPole true ((1 / 2 : ℝ) • (w.1 + w.2))
  change tail 2 (inclusionDerivative (endPole 2 false) u) = _ at hu
  change tail 2 (inclusionDerivative (endPole 2 true) v) = _ at hv
  refine ⟨(u, v), ?_⟩
  change modelDerivative (endPole 2 false) u + modelDerivative (endPole 2 true) v = w
  rw [modelDerivative_endPole, modelDerivative_endPole, hu, hv]
  apply Prod.ext <;> simp only [Bool.false_eq_true, ↓reduceIte, one_smul, neg_one_smul,
    Prod.fst_add, Prod.snd_add] <;> module

theorem selfTransverse_map (x y : Sphere 3) (hne : x ≠ y) (he : map x = map y) :
    Surjective ((modelDerivative x).coprod (modelDerivative y)) := by
  rcases (distinct_coincidence_iff x y).mp ⟨hne, he⟩ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact transverse_poles
  · intro w
    obtain ⟨p, hp⟩ := transverse_poles w
    refine ⟨(p.2, p.1), ?_⟩
    change modelDerivative (endPole 2 true) p.2 + modelDerivative (endPole 2 false) p.1 = w
    rw [add_comm]
    exact hp

end NoExoticSixSphere.WhitneySphere
