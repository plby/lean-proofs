import Wikipedia.HopfProblem.OrbitPairMappingCylinder
import Mathlib.Topology.CompactOpen

/-!
# Gluing continuous families through an actual topological pushout

Currying a locally compact parameter turns compatible families into a
pushout cocone with values in the compact-open function space. Evaluation
then gives the jointly continuous descended family.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace NoExoticSixSphere.CompactParameterPushout

variable {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {i : A ⟶ P} {j : B ⟶ P}
  {K Z : Type u} [TopologicalSpace K] [TopologicalSpace Z] [LocallyCompactSpace K]

def transpose {T : Type u} [TopologicalSpace T] (F : C(K × T, Z)) : C(T, C(K, Z)) :=
  ContinuousMap.curry ⟨fun p : T × K ↦ F (p.2, p.1), F.continuous.comp continuous_swap⟩

omit [LocallyCompactSpace K] in
theorem curried_compatible (F : C(K × A, Z)) (G : C(K × B, Z))
    (h : ∀ k s, F (k, f s) = G (k, g s)) :
    f ≫ TopCat.ofHom (transpose F) = g ≫ TopCat.ofHom (transpose G) := by
  ext s k
  exact h k s

def curried (hP : IsPushout f g i j) (F : C(K × A, Z)) (G : C(K × B, Z))
    (h : ∀ k s, F (k, f s) = G (k, g s)) : P ⟶ TopCat.of C(K, Z) :=
  hP.desc (TopCat.ofHom (transpose F)) (TopCat.ofHom (transpose G)) (curried_compatible F G h)

def glue (hP : IsPushout f g i j) (F : C(K × A, Z)) (G : C(K × B, Z))
    (h : ∀ k s, F (k, f s) = G (k, g s)) : C(K × P, Z) :=
  ⟨fun p ↦ curried hP F G h p.2 p.1,
    continuous_eval.comp (((curried hP F G h).hom.continuous.comp continuous_snd).prodMk
      continuous_fst)⟩

theorem glue_inl (hP : IsPushout f g i j) (F : C(K × A, Z)) (G : C(K × B, Z))
    (h : ∀ k s, F (k, f s) = G (k, g s)) (k : K) (a : A) :
    glue hP F G h (k, i a) = F (k, a) := by
  have he := hP.inl_desc (TopCat.ofHom (transpose F)) (TopCat.ofHom (transpose G))
    (curried_compatible F G h)
  exact congrArg (fun m : A ⟶ TopCat.of C(K, Z) ↦ m a k) he

theorem glue_inr (hP : IsPushout f g i j) (F : C(K × A, Z)) (G : C(K × B, Z))
    (h : ∀ k s, F (k, f s) = G (k, g s)) (k : K) (b : B) :
    glue hP F G h (k, j b) = G (k, b) := by
  have he := hP.inr_desc (TopCat.ofHom (transpose F)) (TopCat.ofHom (transpose G))
    (curried_compatible F G h)
  exact congrArg (fun m : B ⟶ TopCat.of C(K, Z) ↦ m b k) he

end NoExoticSixSphere.CompactParameterPushout
