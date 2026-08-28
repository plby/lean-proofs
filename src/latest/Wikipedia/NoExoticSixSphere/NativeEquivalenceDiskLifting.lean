import Wikipedia.NoExoticSixSphere.NativeBoundaryMapReflection
import Wikipedia.HopfProblem.DegreeCollapseCellLifting

/-!
# Exact disk lifting from the original native homotopy isomorphisms

Native injectivity first supplies the prescribed source boundary filling.
Native surjectivity then lifts the target disk and its entire specified
side homotopy. Zero- and one-dimensional boundaries are handled using
actual path connectedness, not a positive-dimensional cube quotient.
The existing finite-cell assembly therefore applies to the original map.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.RelativeDiskLifting

open DegreeCollapse DegreeCollapse.DiskCylinder DegreeCollapse.MappingPaths

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [PathConnectedSpace A]

theorem exists_boundary_extension_of_native_maps (F : C(A, B))
    (hF : ∀ n, 0 < n → ∀ x : A,
      Function.Injective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a : C(DiskCylinder.Sphere (E := V), A)) (u : C(Disk (E := V), B))
    (hu : ∀ s, u (boundaryToDisk s) = F (a s)) :
    ∃ v : C(Disk (E := V), A), ∀ s, v (boundaryToDisk s) = a s := by
  by_cases hlow : Module.finrank ℝ V ≤ 1
  · let x : A := Classical.choice (inferInstance : Nonempty A)
    obtain ⟨v, hv, _⟩ := DegreeCollapse.Sphere.exists_boundary_extension_of_pi
      (d := 1) (fun k hk hk1 _ ↦ by omega) hlow a x
    exact ⟨v, hv⟩
  · let n := Module.finrank ℝ V - 1
    have hn : 0 < n := by dsimp [n]; omega
    obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      (show Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) by
        simp only [finrank_euclideanSpace, Fintype.card_fin]
        dsimp [n]
        omega)
    exact boundary_extension_of_native_injective hn F (hF n hn)
      (UnitSphereEquiv.homeomorph L) a u hu

theorem relativeDiskLifting_of_native_bijective (F : C(A, B))
    (hF : ∀ n (x : A),
      Function.Bijective (HigherHomotopy.map (N := Fin n) F (y := x) rfl)) (d : ℕ) :
    FiniteCells.RelativeDiskLifting F d := by
  intro V _ _ _ _ a u H h0 h1
  let HP : Path (F.comp a) (u.comp boundaryToDisk) := {
    toContinuousMap := H.curry
    source' := ContinuousMap.ext h0
    target' := ContinuousMap.ext h1 }
  obtain ⟨u₀, _, _, hu₀⟩ := BoundaryPathTransport.exists_transport u HP.symm rfl
  obtain ⟨aD, haD⟩ := exists_boundary_extension_of_native_maps F
    (fun n _ x ↦ (hF n x).injective) a u₀ (fun s ↦ ContinuousMap.congr_fun hu₀ s)
  obtain ⟨L⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ V = Module.finrank ℝ (Fin (Module.finrank ℝ V) → ℝ) by simp)
  obtain ⟨v, G, hv, hG0, hG1, hGside⟩ := exists_lift_with_side F
    (fun x ↦ (hF (Module.finrank ℝ V) x).surjective) L aD u H
      (fun s ↦ (h0 s).trans (congrArg F (haD s).symm)) h1
  exact ⟨v, G, fun s ↦ (hv s).trans (haD s), hG0, hG1, hGside⟩

theorem finiteCell_mapsLift_of_native_bijective (F : C(A, B))
    (hF : ∀ n (x : A),
      Function.Bijective (HigherHomotopy.map (N := Fin n) F (y := x) rfl))
    {Z : Type} [TopologicalSpace Z] {d : ℕ} (hZ : FiniteCells.Built d Z) :
    FiniteCells.MapsLift F Z :=
  FiniteCells.mapsLift_of_built F (relativeDiskLifting_of_native_bijective F hF d) hZ

end NoExoticSixSphere.RelativeDiskLifting
