import Wikipedia.HopfProblem.OrbitPairHomotopyFiberMappedLoopContraction
import Wikipedia.HopfProblem.OrbitPairHomotopyCornerPaths

/-!
# Exactness at the loop-space term of the homotopy-fibre sequence

A nullhomotopy of an included target loop projects to a source loop. Its path
coordinate fills a square; the explicit corner sweep proves that the image of
the projected source loop is homotopic to the original target loop, relative
to every prescribed constant parameter. The converse uses tail contraction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

open NoExoticSixSphere

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def projectionLoopFamily (f : C(X, Y)) (x : X) (p : C(Z, Path (f x) (f x)))
    (H : ((loopInclusion f x).comp p).Homotopy (ContinuousMap.const _ (basepoint f x))) :
    C(Z, Path x x) :=
  PathFamilies.curry ((projection f (f x)).comp H.toContinuousMap) (by
    intro z
    change projection f (f x) (H (0, z)) = x
    rw [H.apply_zero]
    rfl) (by
    intro z
    change projection f (f x) (H (1, z)) = x
    rw [H.apply_one]
    rfl)

theorem projectionLoopFamily_fixed (f : C(X, Y)) (x : X)
    (p : C(Z, Path (f x) (f x))) (S : Set Z)
    (H : ((loopInclusion f x).comp p).HomotopyRel
      (ContinuousMap.const _ (basepoint f x)) S) (z : Z) (hz : z ∈ S) :
    projectionLoopFamily f x p H.toHomotopy z = Path.refl x := by
  apply Path.ext
  funext t
  change projection f (f x) (H (t, z)) = x
  rw [H.eq_fst t hz]
  rfl

def projectionLoopFamilyHomotopy (f : C(X, Y)) (x : X)
    (p : C(Z, Path (f x) (f x))) (S : Set Z) (hp : ∀ z ∈ S, p z = Path.refl (f x))
    (H : ((loopInclusion f x).comp p).HomotopyRel
      (ContinuousMap.const _ (basepoint f x)) S) :
    ((loopMap f x).comp (projectionLoopFamily f x p H.toHomotopy)).HomotopyRel p S := by
  let Q : C(unitInterval × (unitInterval × Z), Y) := (evaluation f (f x)).comp {
    toFun z := (z.2.1, H (z.1, z.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (H.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))) }
  apply HomotopyCorner.pathFamilyHomotopy (f x) _ p S Q
  · intro t z
    exact (H (t, z)).property.1
  · intro t z
    change (H (0, z)).val.2 t = p z t
    rw [H.apply_zero]
    rfl
  · intro t z
    change (H (1, z)).val.2 t = f x
    rw [H.apply_one]
    rfl
  · intro t z
    exact (H (t, z)).property.2
  · intro s t z hz
    change (H (s, z)).val.2 t = f x
    rw [H.eq_fst s hz]
    change p z t = f x
    rw [hp z hz]
    rfl

theorem exists_sourceLoopGenLoop_of_nullhomotopy (f : C(X, Y)) (x : X)
    (p : GenLoop N (Path (f x) (f x)) (Path.refl (f x)))
    (H : ((loopInclusion f x).comp p.val).HomotopyRel
      (ContinuousMap.const _ (basepoint f x)) (Cube.boundary N)) :
    ∃ q : GenLoop N (Path x x) (Path.refl x),
      GenLoop.Homotopic (HigherHomotopy.genLoopMap (loopMap f x) (loopMap_base f x) q) p := by
  let q : GenLoop N (Path x x) (Path.refl x) :=
    ⟨projectionLoopFamily f x p.val H.toHomotopy,
      projectionLoopFamily_fixed f x p.val (Cube.boundary N) H⟩
  exact ⟨q, ⟨projectionLoopFamilyHomotopy f x p.val (Cube.boundary N) p.property H⟩⟩

theorem loopInclusion_eq_const_iff_exists_sourceLoop_class (f : C(X, Y)) (x : X)
    (c : HomotopyGroup N (Path (f x) (f x)) (Path.refl (f x))) :
    HigherHomotopy.map (loopInclusion f x) (loopInclusion_base f x) c =
      (Quotient.mk' GenLoop.const : HomotopyGroup N (Space f (f x)) (basepoint f x)) ↔
        ∃ q : HomotopyGroup N (Path x x) (Path.refl x),
          HigherHomotopy.map (loopMap f x) (loopMap_base f x) q = c := by
  constructor
  · refine Quotient.inductionOn c ?_
    intro p hp
    obtain ⟨H⟩ := Quotient.exact hp
    obtain ⟨q, hq⟩ := exists_sourceLoopGenLoop_of_nullhomotopy f x p H
    exact ⟨Quotient.mk' q, Quotient.sound hq⟩
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro q
    exact Quotient.sound ⟨mappedLoopNullhomotopy f x q.val (Cube.boundary N) q.property⟩

theorem loopMap_range_eq_loopInclusion_ker [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (x : X) :
    (HigherHomotopy.mapMonoidHom (N := N) (loopMap f x) (loopMap_base f x)).range =
      (HigherHomotopy.mapMonoidHom (N := N) (loopInclusion f x) (loopInclusion_base f x)).ker := by
  ext c
  exact (loopInclusion_eq_const_iff_exists_sourceLoop_class f x c).symm

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
