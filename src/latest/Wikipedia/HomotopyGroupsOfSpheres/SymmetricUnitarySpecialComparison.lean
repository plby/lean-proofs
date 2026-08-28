import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryDeterminant
import Wikipedia.HomotopyGroupsOfSpheres.CircleRelativeArguments
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# Relative comparison with the symmetric special-unitary locus

Real determinant arguments normalize higher based cubes into the actual
determinant-one fiber. Relative homotopies are reflected by lifting their
determinants with zero initial, final, and fixed-parameter values.
-/

noncomputable section

open scoped Topology unitInterval ContinuousMap

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

def specialInclusion (N : Type*) [Fintype N] [DecidableEq N] : C(SpecialSpace N, Space N) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem specialInclusion_identity (N : Type*) [Fintype N] [DecidableEq N] :
    specialInclusion N specialIdentity = identity := rfl

section Homotopies

variable {X : Type*} [TopologicalSpace X] {S : Set X}

def determinantHomotopy (n : ℕ)
    (f g : C(X, SpecialSpace (Fin (n + 1))))
    (H : ((specialInclusion _).comp f).HomotopyRel ((specialInclusion _).comp g) S) :
    (ContinuousMap.const X (1 : Circle)).HomotopyRel (.const X 1) S where
  toContinuousMap := determinant.comp H.toContinuousMap
  map_zero_left x := by
    change determinant (H (0, x)) = 1
    rw [H.apply_zero]
    exact (f x).property
  map_one_left x := by
    change determinant (H (1, x)) = 1
    rw [H.apply_one]
    exact (g x).property
  prop' t x hx := by
    change determinant (H (t, x)) = 1
    have he : H (t, x) = (f x).val := H.prop t x hx
    rw [he]
    exact (f x).property

def specialHomotopyOfInclusion [PreconnectedSpace X] (n : ℕ) (hS : S.Nonempty)
    (f g : C(X, SpecialSpace (Fin (n + 1))))
    (H : ((specialInclusion _).comp f).HomotopyRel ((specialInclusion _).comp g) S) :
    f.HomotopyRel g S := by
  let θ := relativeCircleArgument hS (determinantHomotopy n f g H)
  let G := normalizedSpecialFamily n H.toContinuousMap θ.toContinuousMap
    (fun z ↦ (relativeCircleArgument_lifts hS (determinantHomotopy n f g H) z).symm)
  refine {
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro x
    apply Subtype.ext
    change normalize n (θ (0, x)) (H (0, x)) = (f x).val
    have hθ : θ (0, x) = 0 := θ.apply_zero x
    rw [hθ, normalize_zero, H.apply_zero]
    rfl
  · intro x
    apply Subtype.ext
    change normalize n (θ (1, x)) (H (1, x)) = (g x).val
    have hθ : θ (1, x) = 0 := θ.apply_one x
    rw [hθ, normalize_zero, H.apply_one]
    rfl
  · intro t x hx
    apply Subtype.ext
    change normalize n (θ (t, x)) (H (t, x)) = (f x).val
    have hθ : θ (t, x) = 0 := θ.prop t x hx
    rw [hθ, normalize_zero]
    exact H.prop t x hx

theorem special_homotopicRel_iff [PreconnectedSpace X] (n : ℕ) (hS : S.Nonempty)
    (f g : C(X, SpecialSpace (Fin (n + 1)))) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((specialInclusion _).comp f).HomotopyRel ((specialInclusion _).comp g) S) :=
  ⟨fun ⟨H⟩ ↦ ⟨H.compContinuousMap (specialInclusion _)⟩,
    fun ⟨H⟩ ↦ ⟨specialHomotopyOfInclusion n hS f g H⟩⟩

end Homotopies

theorem exists_special_cube_representative (n d : ℕ)
    (p : GenLoop (Fin (d + 2)) (Space (Fin (n + 1))) identity) :
    ∃ q : GenLoop (Fin (d + 2)) (SpecialSpace (Fin (n + 1))) specialIdentity,
      GenLoop.Homotopic p
        (pointedMapGenLoop (specialInclusion _) specialIdentity identity rfl q) := by
  let δ : GenLoop (Fin (d + 2)) Circle 1 :=
    ⟨determinant.comp p.val, fun u hu ↦ by
      change determinant (p u) = 1
      have hp : p u = identity := p.property u hu
      rw [hp, determinant_identity]⟩
  obtain ⟨θ, hθ, hθboundary⟩ := exists_circle_cube_argument d δ
  let Q := normalizedSpecialFamily n p.val θ (fun u ↦ (hθ u).symm)
  have hQ (u : Fin (d + 2) → I) (hu : u ∈ Cube.boundary (Fin (d + 2))) :
      Q u = specialIdentity := by
    apply Subtype.ext
    change normalize n (θ u) (p u) = identity
    rw [hθboundary u hu, normalize_zero]
    exact p.property u hu
  let q : GenLoop (Fin (d + 2)) (SpecialSpace (Fin (n + 1))) specialIdentity := ⟨Q, hQ⟩
  refine ⟨q, ⟨?_⟩⟩
  let H := normalizationHomotopy n p.val θ
  exact {
    toContinuousMap := H.toContinuousMap
    map_zero_left := H.apply_zero
    map_one_left := H.apply_one
    prop' := fun t u hu ↦ H.prop t u (hθboundary u hu) }

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
