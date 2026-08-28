import Wikipedia.HopfProblem.SixSphereCubeCollapseFactorization
import Wikipedia.HopfProblem.SixSphereCubeQuotient

/-!
# Every original native based six-loop factors through the literal unit six-sphere

The genuine quotient-map lift descends the original continuous cube map.
It gives an actual continuous sphere map, takes the collapsed boundary
point to the given base point, and recovers the original cube map exactly.
The target is arbitrary; no separation or connectivity condition is used.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual continuous sphere map descended from an original native based six-cube. -/
def factorMap (p : GenLoop (Fin 6) X x) : C(StandardSphere, X) :=
  (collapseLift (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty
    p.val x (fun u hu => p.property u hu)).comp
      (cubeInteriorSphereHomeomorph.symm : C(StandardSphere, OnePoint CubeInterior))

@[simp] theorem factorMap_basePoint (p : GenLoop (Fin 6) X x) :
    factorMap p sphereBasePoint = x := by
  change collapseLift (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty
    p.val x (fun u hu => p.property u hu)
    (cubeInteriorSphereHomeomorph.symm sphereBasePoint) = x
  rw [cubeInteriorSphereHomeomorph_symm_basePoint]
  exact collapseLift_infty (Cube.boundary (Fin 6)) isClosed_cubeBoundary
    cubeBoundary_nonempty p.val x (fun u hu => p.property u hu)

/-- The descended sphere map recovers the literal original cube map pointwise. -/
@[simp] theorem factorMap_cubeSphereMap (p : GenLoop (Fin 6) X x) (u : Fin 6 → I) :
    factorMap p (cubeSphereMap u) = p u := by
  change collapseLift (Cube.boundary (Fin 6)) isClosed_cubeBoundary cubeBoundary_nonempty
    p.val x (fun v hv => p.property v hv)
    (cubeInteriorSphereHomeomorph.symm
      (cubeInteriorSphereHomeomorph (collapse (Cube.boundary (Fin 6)) u))) = p u
  rw [cubeInteriorSphereHomeomorph.symm_apply_apply]
  exact collapseLift_apply (Cube.boundary (Fin 6)) isClosed_cubeBoundary
    cubeBoundary_nonempty p.val x (fun v hv => p.property v hv) u

/-- Exact factorization in the original continuous-map space. -/
@[simp] theorem factorMap_comp_cubeSphereMap (p : GenLoop (Fin 6) X x) :
    (factorMap p).comp cubeSphereMap = p.val := by
  ext u
  exact factorMap_cubeSphereMap p u

/-- The actual quotient determines the sphere map uniquely, without a separation hypothesis. -/
theorem factorMap_unique (p : GenLoop (Fin 6) X x) (f : C(StandardSphere, X))
    (hf : f.comp cubeSphereMap = p.val) : f = factorMap p := by
  ext z
  obtain ⟨u, rfl⟩ := cubeSphereMap_surjective z
  exact (ContinuousMap.congr_fun hf u).trans (factorMap_cubeSphereMap p u).symm

@[simp] theorem factorMap_const :
    factorMap (GenLoop.const : GenLoop (Fin 6) X x) =
      ContinuousMap.const StandardSphere x := by
  symm
  apply factorMap_unique
  rfl

/-- An explicit actual sphere map realizes every native based six-loop. -/
theorem exists_factorMap (p : GenLoop (Fin 6) X x) :
    ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1, X),
      f sphereBasePoint = x ∧ f.comp cubeSphereMap = p.val :=
  ⟨factorMap p, factorMap_basePoint p, factorMap_comp_cubeSphereMap p⟩

end Wikipedia.HopfProblem.SixSphereCube
