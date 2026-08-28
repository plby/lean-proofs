import Wikipedia.NoExoticSixSphere.CubeFirstCoordinate
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying
import Wikipedia.NoExoticSixSphere.RetractionHomotopyTransfer

/-!
# Generalized loops in a loop space are one-higher-dimensional generalized loops

The first cube coordinate is path time. The remaining coordinates parameterize
the loop. All boundary faces are retained by the exact inverse constructions.
-/

open Set

namespace NoExoticSixSphere.GeneralizedLoopCurrying

variable {X : Type*} [TopologicalSpace X] {x : X} {d : ℕ}

noncomputable def uncurry (p : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    GenLoop (Fin (d + 1)) X x :=
  ⟨(PathFamilies.uncurry p.1).comp (CubeFirstCoordinate.split d), by
    intro t ht
    change p.1 (Fin.tail t) (t 0) = x
    rcases (CubeFirstCoordinate.boundary_split_iff d t).mp ht with h | h | h
    · change t 0 = 0 at h
      rw [h, Path.source]
    · change t 0 = 1 at h
      rw [h, Path.target]
    · rw [p.2 (Fin.tail t) h]
      rfl⟩

theorem curry_source (p : GenLoop (Fin (d + 1)) X x) (t : Fin d → unitInterval) :
    (p.1.comp (CubeFirstCoordinate.join d)) (0, t) = x :=
  p.2 _ ((CubeFirstCoordinate.boundary_join_iff d (0, t)).mpr (Or.inl rfl))

theorem curry_target (p : GenLoop (Fin (d + 1)) X x) (t : Fin d → unitInterval) :
    (p.1.comp (CubeFirstCoordinate.join d)) (1, t) = x :=
  p.2 _ ((CubeFirstCoordinate.boundary_join_iff d (1, t)).mpr (Or.inr (Or.inl rfl)))

noncomputable def curry (p : GenLoop (Fin (d + 1)) X x) :
    GenLoop (Fin d) (Path x x) (Path.refl x) :=
  ⟨PathFamilies.curry (p.1.comp (CubeFirstCoordinate.join d)) (curry_source p) (curry_target p), by
    intro t ht
    apply Path.ext
    funext s
    exact p.2 _ ((CubeFirstCoordinate.boundary_join_iff d (s, t)).mpr (Or.inr (Or.inr ht)))⟩

theorem uncurry_curry (p : GenLoop (Fin (d + 1)) X x) : uncurry (curry p) = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact congrArg p.1 (CubeFirstCoordinate.join_split d t)

theorem curry_uncurry (p : GenLoop (Fin d) (Path x x) (Path.refl x)) : curry (uncurry p) = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply Path.ext
  funext s
  rfl

noncomputable def equiv (d : ℕ) (x : X) :
    GenLoop (Fin d) (Path x x) (Path.refl x) ≃ GenLoop (Fin (d + 1)) X x where
  toFun := uncurry
  invFun := curry
  left_inv := curry_uncurry
  right_inv := uncurry_curry

theorem homotopic_uncurry {p q : GenLoop (Fin d) (Path x x) (Path.refl x)}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (uncurry p) (uncurry q) := by
  obtain ⟨F⟩ := h
  have H := RetractionHomotopyTransfer.precompose
    (PathFamilies.uncurryHomotopy F) (CubeFirstCoordinate.split d)
  have hs : (CubeFirstCoordinate.split d) ⁻¹'
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ Cube.boundary (Fin d)} = Cube.boundary (Fin (d + 1)) := by
    ext t
    exact (CubeFirstCoordinate.boundary_split_iff d t).symm
  rw [hs] at H
  exact ⟨H⟩

theorem homotopic_curry {p q : GenLoop (Fin (d + 1)) X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (curry p) (curry q) := by
  obtain ⟨F⟩ := h
  have H := RetractionHomotopyTransfer.precompose F (CubeFirstCoordinate.join d)
  have hs : (CubeFirstCoordinate.join d) ⁻¹' Cube.boundary (Fin (d + 1)) =
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ Cube.boundary (Fin d)} := by
    ext t
    exact CubeFirstCoordinate.boundary_join_iff d t
  rw [hs] at H
  exact ⟨PathFamilies.curryHomotopy H⟩

theorem homotopic_iff_uncurry (p q : GenLoop (Fin d) (Path x x) (Path.refl x)) :
    GenLoop.Homotopic p q ↔ GenLoop.Homotopic (uncurry p) (uncurry q) := by
  constructor
  · exact homotopic_uncurry
  · intro h
    have h' := homotopic_curry h
    rwa [curry_uncurry, curry_uncurry] at h'

end NoExoticSixSphere.GeneralizedLoopCurrying
