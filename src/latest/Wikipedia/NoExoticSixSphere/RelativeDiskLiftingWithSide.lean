import Wikipedia.NoExoticSixSphere.RelativeDiskLifting

/-!
# Native disk lifting retains a prescribed boundary homotopy exactly

Transport the original target disk backwards along the given side path.
The existing relative lift applies with the source filling's boundary.
Its comparison path is then joined to the transport path. Full-cylinder
homotopy extension removes the initial constant pause on the side,
without changing either endpoint or any prescribed boundary value.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.RelativeDiskLifting

open DegreeCollapse DegreeCollapse.DiskCylinder DegreeCollapse.MappingPaths

variable {n : ℕ} {A B V : Type} [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_lift_with_side (F : C(A, B))
    (hF : ∀ x : A, Function.Surjective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    (L : V ≃L[ℝ] (Fin n → ℝ)) (a : C(Disk (E := V), A)) (u : C(Disk (E := V), B))
    (H : C(I × Sphere (E := V), B))
    (h0 : ∀ s, H (0, s) = F (a (boundaryToDisk s)))
    (h1 : ∀ s, H (1, s) = u (boundaryToDisk s)) :
    ∃ (v : C(Disk (E := V), A)) (G : C(I × Disk (E := V), B)),
      (∀ s, v (boundaryToDisk s) = a (boundaryToDisk s)) ∧
      (∀ z, G (0, z) = F (v z)) ∧ (∀ z, G (1, z) = u z) ∧
      ∀ t s, G (t, boundaryToDisk s) = H (t, s) := by
  let b : C(Sphere (E := V), B) := (F.comp a).comp boundaryToDisk
  let HP : Path b (u.comp boundaryToDisk) := {
    toContinuousMap := H.curry
    source' := ContinuousMap.ext h0
    target' := ContinuousMap.ext h1 }
  obtain ⟨u₀, E, hE, hu₀⟩ := BoundaryPathTransport.exists_transport u HP.symm rfl
  have hu₀' (s : Sphere (E := V)) : u₀ (boundaryToDisk s) = F (a (boundaryToDisk s)) :=
    ContinuousMap.congr_fun hu₀ s
  obtain ⟨v, hv, ⟨K⟩⟩ := exists_relative_lift F hF L a u₀ hu₀'
  let KP := ofHomotopy K.toHomotopy
  have hKP : Over (fun w : C(Disk (E := V), B) ↦ w.comp boundaryToDisk) KP
      (Path.refl b) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(boundaryToDisk s : V)‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
    exact (K.eq_fst t hs).trans (congrArg F (hv s))
  have hEs : Over (fun w : C(Disk (E := V), B) ↦ w.comp boundaryToDisk) E.symm HP := by
    simpa only [Path.symm_symm] using hE.symm
  obtain ⟨G, hG0, hG1, hGside⟩ := SideRectification.exists_rectification
    (KP.trans E.symm) ((Path.refl b).trans HP) HP (hKP.trans hEs)
      (Path.Homotopic.refl_trans HP)
  exact ⟨v, G, hv, hG0, hG1, hGside⟩

end NoExoticSixSphere.RelativeDiskLifting
