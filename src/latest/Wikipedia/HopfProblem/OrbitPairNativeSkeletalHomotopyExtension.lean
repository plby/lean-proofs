import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionCoproduct
import Wikipedia.HopfProblem.OrbitPairSubdivisionRealizedAttachments

/-!
# Homotopy extension for native realized skeletal attachments

The coproducts and pushouts below are the actual native simplicial
coproducts and skeletal squares, mapped through geometric realization.
No replacement of the attaching maps or their topological spaces is used.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem realized_coproduct {J : Type u} {A B : J → SSet.{u}}
    (e : ∀ j, A j ⟶ B j)
    (he : ∀ j, HasHomotopyExtension (SSet.toTop.map (e j))) :
    HasHomotopyExtension (SSet.toTop.map (Limits.Sigma.map e)) := by
  apply of_coproduct
    (fun j ↦ SSet.toTop.map (Sigma.ι A j))
    (fun j ↦ SSet.toTop.map (Sigma.ι B j))
    (isColimitCofanMkObjOfIsColimit SSet.toTop A (Sigma.ι A) (coproductIsCoproduct A))
    (isColimitCofanMkObjOfIsColimit SSet.toTop B (Sigma.ι B) (coproductIsCoproduct B))
    (fun j ↦ SSet.toTop.map (e j)) _ _ he
  intro j
  rw [← SSet.toTop.map_comp, Sigma.ι_map, SSet.toTop.map_comp]

theorem realized_skeletal_attaching {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) :
    HasHomotopyExtension (SSet.toTop.map (SSet.relativeCellComplexOfMono.l i d)) :=
  realized_coproduct (fun _ ↦ (SSet.boundary d).ι)
    (fun _ ↦ realized_boundary_hasHomotopyExtension d)

theorem realized_skeletal_successor {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) :
    HasHomotopyExtension (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i d)) :=
  of_pushout ((SSet.relativeCellComplexOfMono.isPushout i d).map SSet.toTop)
    (realized_skeletal_attaching i d)

theorem realized_skeletal_initial {X Y : SSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    HasHomotopyExtension (SSet.toTop.map (SSet.Subcomplex.homOfLE
      ((SSet.skeletonOfMono i).monotone (Nat.zero_le n)))) := by
  induction n with
  | zero =>
    simpa using of_isIso (𝟙 (SSet.toTop.obj (SSet.skeletonOfMono i 0)))
  | succ n ih =>
    simpa only [← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_comp] using
      comp _ _ ih (realized_skeletal_successor i n)

theorem skeleton_eq_top_of_dimension (Y : SSet.{u}) (d : ℕ) [Y.HasDimensionLT d] :
    Y.skeleton d = ⊤ := by
  apply top_unique
  rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
  intro n x _
  exact Y.mem_skeleton x.1 (Y.dim_lt_of_nonDegenerate x d)

theorem skeletonOfMono_eq_top_of_dimension {X Y : SSet.{u}} (i : X ⟶ Y)
    (d : ℕ) [Y.HasDimensionLT d] : SSet.skeletonOfMono i d = ⊤ := by
  change SSet.Subcomplex.range i ⊔ Y.skeleton d = ⊤
  rw [skeleton_eq_top_of_dimension Y d, sup_top_eq]

theorem realized_mono_of_dimension {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (d : ℕ) [Y.HasDimensionLT d] : HasHomotopyExtension (SSet.toTop.map i) := by
  let e₀ : X ≅ (SSet.skeletonOfMono i 0 : SSet.{u}) :=
    asIso (SSet.Subcomplex.toRange i) ≪≫
      SSet.Subcomplex.eqToIso (SSet.skeletonOfMono_zero i).symm
  let e₁ : (SSet.skeletonOfMono i d : SSet.{u}) ≅ Y :=
    SSet.Subcomplex.eqToIso (skeletonOfMono_eq_top_of_dimension i d) ≪≫
      SSet.Subcomplex.topIso Y
  let j := SSet.Subcomplex.homOfLE ((SSet.skeletonOfMono i).monotone (Nat.zero_le d))
  have hj : e₀.hom ≫ j ≫ e₁.hom = i := by
    rfl
  have h := comp (SSet.toTop.map e₀.hom)
    (SSet.toTop.map j ≫ SSet.toTop.map e₁.hom)
    (of_isIso _)
    (comp _ _ (realized_skeletal_initial i d) (of_isIso _))
  simpa only [← SSet.toTop.map_comp, hj] using h

theorem realized_mono_of_finite {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] [Y.Finite] :
    HasHomotopyExtension (SSet.toTop.map i) := by
  obtain ⟨d, hd⟩ := Y.hasDimensionLT_of_finite
  let : Y.HasDimensionLT d := hd
  exact realized_mono_of_dimension i d

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
