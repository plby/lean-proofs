import Wikipedia.HopfProblem.OrbitPairNeighborhoodDeformation
import Wikipedia.HopfProblem.OrbitPairNativeSkeletalHomotopyExtension

/-!
# Uniform control at the fixed subspace and native realization applications

Compactness of the time interval makes stationarity uniform in time
near a fixed point. Consequently an arbitrary change of the time
parameter remains continuous there. These facts are needed when product
deformations use ratios of their neighborhood functions.
-/

noncomputable section

universe u v

open CategoryTheory unitInterval Set Filter Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation

variable {A B : TopCat.{u}} {i : A ⟶ B} (D : Data i)

theorem height_image (a : A) : D.height (i a) = 0 := (D.zero_iff _).mpr ⟨a, rfl⟩

theorem fixed_of_height_zero (t : I) (b : B) (hb : D.height b = 0) :
    D.deformation (t, b) = b := by
  obtain ⟨a, rfl⟩ := (D.zero_iff b).mp hb
  exact D.fixed t a

include D in
theorem range_isClosed : IsClosed (Set.range i) := by
  have he : Set.range i = {b | D.height b = 0} := Set.ext (fun b ↦ (D.zero_iff b).symm)
  rw [he]
  exact isClosed_eq D.height.continuous continuous_const

theorem exists_uniform_neighborhood (b : B) (hb : D.height b = 0)
    (U : Set B) (hU : IsOpen U) (hbU : b ∈ U) :
    ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ ∀ t x, x ∈ V → D.deformation (t, x) ∈ U := by
  let paths : C(B, C(I, B)) := (D.deformation.comp ⟨Prod.swap, continuous_swap⟩).curry
  let O : Set C(I, B) := {p | Set.MapsTo p univ U}
  have hO : IsOpen O := ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hU
  refine ⟨paths ⁻¹' O, hO.preimage paths.continuous, ?_, ?_⟩
  · intro t _
    change D.deformation (t, b) ∈ U
    rw [fixed_of_height_zero D t b hb]
    exact hbU
  · intro t x hx
    exact hx (Set.mem_univ t)

theorem continuousAt_retime_at_zero {X : Type v} [TopologicalSpace X]
    (F : X → B) (τ : X → I) (x₀ : X) (hF : ContinuousAt F x₀)
    (h0 : D.height (F x₀) = 0) : ContinuousAt (fun x ↦ D.deformation (τ x, F x)) x₀ := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  have hFV : F x₀ ∈ V := (fixed_of_height_zero D (τ x₀) (F x₀) h0) ▸ hxV
  obtain ⟨W, hW, hxW, hWV⟩ := exists_uniform_neighborhood D (F x₀) h0 V hV hFV
  exact Filter.mem_of_superset (hF (hW.mem_nhds hxW))
    (fun x hx ↦ hVU (hWV (τ x) (F x) hx))

theorem realized_mono_of_dimension {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (d : ℕ) [Y.HasDimensionLT d] : Nonempty (Data (SSet.toTop.map i)) :=
  exists_data (SSet.toTop.map i) (HomotopyExtension.realized_mono_of_dimension i d)
    (RealizationSimplex.realizedMono_isClosedEmbedding i)

theorem realized_mono_of_finite {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] [Y.Finite] :
    Nonempty (Data (SSet.toTop.map i)) :=
  exists_data (SSet.toTop.map i) (HomotopyExtension.realized_mono_of_finite i)
    (RealizationSimplex.realizedMono_isClosedEmbedding i)

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodDeformation
