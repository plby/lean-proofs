import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Composition and based homotopy for the original native homotopy maps

The representative identities use the original continuous maps and
relative homotopies. Factoring these operations before specialization
avoids unfolding large geometric constructions during quotient induction.
-/

open Set

namespace NoExoticSixSphere.HigherHomotopy

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

theorem map_comp (f : C(X, Y)) (hf : f x = y) (g : C(Y, Z)) (hg : g y = z)
    (c : HomotopyGroup N X x) :
    map g hg (map f hf c) = map (g.comp f) ((congrArg g hf).trans hg) c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

theorem genLoopMap_homotopic_of_based_homotopy (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y) (H : f.HomotopyRel g {x}) (p : GenLoop N X x) :
    GenLoop.Homotopic (genLoopMap f hf p) (genLoopMap g hg p) := by
  refine ⟨{
    toFun := fun q ↦ H (q.1, p.val q.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
    map_zero_left := fun u ↦ H.apply_zero (p.val u)
    map_one_left := fun u ↦ H.apply_one (p.val u)
    prop' := ?_ }⟩
  intro t u hu
  exact H.eq_fst t (by rw [p.property u hu]; exact mem_singleton x)

theorem map_eq_of_based_homotopy (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y) (H : f.HomotopyRel g {x}) (c : HomotopyGroup N X x) :
    map f hf c = map g hg c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  exact Quotient.sound (genLoopMap_homotopic_of_based_homotopy f g hf hg H p)

theorem map_const (x : X) (y : Y) (c : HomotopyGroup N X x) :
    map (ContinuousMap.const X y) rfl c =
      (Quotient.mk _ GenLoop.const : HomotopyGroup N Y y) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

end NoExoticSixSphere.HigherHomotopy
