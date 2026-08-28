import Wikipedia.HopfProblem.OrbitPairStandardSimplexDeformation

/-!
# Transporting a relative deformation across a pushout

If the attached space deforms onto its attaching subspace, the checked
homotopy-gluing operation transports that deformation to the pushout.
The resulting homotopy fixes the entire image of the base space.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy

variable {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B} {i : A ⟶ P} {j : B ⟶ P}

def baseDeformation (R : P ⟶ A) (hi : i ≫ R = 𝟙 _) :
    (i ≫ 𝟙 P).hom.Homotopy (i ≫ (R ≫ i)).hom where
  toFun p := i p.2
  continuous_toFun := i.hom.continuous.comp continuous_snd
  map_zero_left _ := rfl
  map_one_left a := by
    have h : i ≫ (R ≫ i) = i := by rw [← Category.assoc, hi, Category.id_comp]
    exact (congrArg (fun k ↦ k a) h).symm

theorem cell_deformation_endpoint (hP : IsPushout f g i j) (R : P ⟶ A)
    (r : B ⟶ S) (hj : j ≫ R = r ≫ f) : (r ≫ g) ≫ j = j ≫ (R ≫ i) := by
  calc
    _ = r ≫ (g ≫ j) := Category.assoc _ _ _
    _ = r ≫ (f ≫ i) := congrArg (fun k ↦ r ≫ k) hP.w.symm
    _ = (r ≫ f) ≫ i := (Category.assoc _ _ _).symm
    _ = (j ≫ R) ≫ i := congrArg (fun k ↦ k ≫ i) hj.symm
    _ = _ := Category.assoc _ _ _

def cellDeformation (hP : IsPushout f g i j) (R : P ⟶ A) (r : B ⟶ S)
    (hj : j ≫ R = r ≫ f)
    (H : (ContinuousMap.id B).HomotopyRel (r ≫ g).hom (Set.range g)) :
    (j ≫ 𝟙 P).hom.Homotopy (j ≫ (R ≫ i)).hom where
  toContinuousMap := j.hom.comp H.toHomotopy.toContinuousMap
  map_zero_left b := congrArg j (H.map_zero_left b)
  map_one_left b := (congrArg j (H.map_one_left b)).trans
    (congrArg (fun k ↦ k b) (cell_deformation_endpoint hP R r hj))

theorem deformations_compatible (hP : IsPushout f g i j) (R : P ⟶ A) (r : B ⟶ S)
    (hi : i ≫ R = 𝟙 _) (hj : j ≫ R = r ≫ f)
    (H : (ContinuousMap.id B).HomotopyRel (r ≫ g).hom (Set.range g)) (t : I) (s : S) :
    baseDeformation R hi (t, f s) = cellDeformation hP R r hj H (t, g s) := by
  change i (f s) = j (H (t, g s))
  rw [H.eq_fst t ⟨s, rfl⟩]
  exact congrArg (fun k ↦ k s) hP.w

def deformation (hP : IsPushout f g i j) (R : P ⟶ A) (r : B ⟶ S)
    (hi : i ≫ R = 𝟙 _) (hj : j ≫ R = r ≫ f)
    (H : (ContinuousMap.id B).HomotopyRel (r ≫ g).hom (Set.range g)) :
    (ContinuousMap.id P).HomotopyRel (R ≫ i).hom (Set.range i) where
  toHomotopy := glue hP (baseDeformation R hi) (cellDeformation hP R r hj H)
    (deformations_compatible hP R r hi hj H)
  prop' t p hp := by
    obtain ⟨a, rfl⟩ := hp
    exact glue_inl hP (baseDeformation R hi) (cellDeformation hP R r hj H)
      (deformations_compatible hP R r hi hj H) t a

end Wikipedia.HopfProblem.OrbitPair.PushoutHomotopy
