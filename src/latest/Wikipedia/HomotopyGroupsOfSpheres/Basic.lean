import Wikipedia.HopfProblem.SphereHomologyBasic
import Wikipedia.HopfProblem.SecondHurewiczNativeMapsLoops

/-!
# Standard spheres and maps on native homotopy groups

`Sphere n` is the unit sphere in real Euclidean `(n+1)`-space with its
subspace topology. All homotopy groups below are Mathlib's cubical groups.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

open Wikipedia.HopfProblem.SecondHurewicz

variable {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [DecidableEq N] [Nonempty N]

/-- Continuous postcomposition on the original homotopy group. -/
def map (f : C(X, Y)) (x : X) : HomotopyGroup N X x →* HomotopyGroup N Y (f x) where
  toFun := Quotient.map (mapGenLoop f x) (fun _ _ h => mapGenLoop_homotopic f x h)
  map_one' := by
    change (⟦mapGenLoop f x GenLoop.const⟧ : HomotopyGroup N Y (f x)) = ⟦GenLoop.const⟧
    rw [mapGenLoop_const]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact (congrArg (Quotient.map (mapGenLoop f x)
      (fun _ _ h => mapGenLoop_homotopic f x h))
      (HomotopyGroup.mul_spec (i := Classical.arbitrary N) (p := p) (q := q))).trans
      ((congrArg (fun r : GenLoop N Y (f x) => (⟦r⟧ : HomotopyGroup N Y (f x)))
        (mapGenLoop_transAt f x (Classical.arbitrary N) q p)).trans
        (HomotopyGroup.mul_spec (i := Classical.arbitrary N)
          (p := mapGenLoop f x p) (q := mapGenLoop f x q)).symm)

/-- Homeomorphisms induce isomorphisms on the native homotopy groups. -/
def homeomorphMulEquiv (e : X ≃ₜ Y) (x : X) :
    HomotopyGroup N X x ≃* HomotopyGroup N Y (e x) :=
  MulEquiv.ofBijective (map (e : C(X, Y)) x) (by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with
      | h p =>
        induction b using Quotient.inductionOn with
        | h q =>
          have h : GenLoop.Homotopic
              (mapGenLoop (e : C(X, Y)) x p) (mapGenLoop (e : C(X, Y)) x q) :=
            Quotient.exact hab
          have hi := h.comp_continuousMap (e.symm : C(Y, X))
          apply Quotient.sound
          change p.val.HomotopicRel q.val (Cube.boundary N)
          convert hi using 1 <;> ext u <;> exact (e.symm_apply_apply _).symm
    · intro a
      induction a using Quotient.inductionOn with
      | h p =>
        let q : GenLoop N X x :=
          ⟨(e.symm : C(Y, X)).comp p.val, fun t ht => by
            change e.symm (p.val t) = x
            rw [p.property t ht, e.symm_apply_apply]⟩
        refine ⟨⟦q⟧, ?_⟩
        change (⟦mapGenLoop (e : C(X, Y)) x q⟧ : HomotopyGroup N Y (e x)) = ⟦p⟧
        have hq : mapGenLoop (e : C(X, Y)) x q = p := by
          apply GenLoop.ext
          intro t
          exact e.apply_symm_apply (p t)
        rw [hq])

end Wikipedia.HomotopyGroupsOfSpheres
