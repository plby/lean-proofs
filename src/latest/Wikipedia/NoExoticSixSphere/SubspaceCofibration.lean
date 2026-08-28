import Wikipedia.HopfProblem.OrbitPairNeighborhoodProductData

/-!+# Transport of neighborhood-deformation data for actual subspaces

Conjugation by a homeomorphism transports the height and deformation,
including exact stationarity and the terminal subspace condition.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.SubspaceCofibration

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def inclusion (A : Set X) : TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem mem_range (A : Set X) (x : X) : x ∈ Set.range (inclusion A) ↔ x ∈ A := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def emptyData : NeighborhoodDeformation.Data (inclusion (∅ : Set X)) where
  height := ContinuousMap.const _ 1
  deformation := ContinuousMap.snd
  zero_iff x := by simp
  bottom _ := rfl
  fixed _ a := a.property.elim
  terminal _ h := (lt_irrefl (1 : I) h).elim

variable {A : Set X} {B : Set Y} (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ A ↔ e x ∈ B)
    (D : NeighborhoodDeformation.Data (inclusion A))

def transportedDeformation : C(I × Y, Y) :=
  (⟨e, e.continuous⟩ : C(X, Y)).comp (D.deformation.comp
    ((ContinuousMap.id I).prodMap ⟨e.symm, e.symm.continuous⟩))

def transport : NeighborhoodDeformation.Data (inclusion B) where
  height := D.height.comp ⟨e.symm, e.symm.continuous⟩
  deformation := transportedDeformation e D
  zero_iff y := by
    change D.height (e.symm y) = 0 ↔ _
    rw [D.zero_iff, mem_range, mem_range, he, e.apply_symm_apply]
  bottom y := by
    change e (D.deformation (0, e.symm y)) = y
    rw [D.bottom, e.apply_symm_apply]
  fixed t y := by
    have hy : e.symm y.val ∈ A := (he _).mpr (by simp only [e.apply_symm_apply]; exact y.property)
    change e (D.deformation (t, e.symm y.val)) = y.val
    exact (congrArg e (D.fixed t ⟨e.symm y.val, hy⟩)).trans (e.apply_symm_apply y.val)
  terminal y hy := by
    have h := D.terminal (e.symm y) hy
    rw [mem_range] at h ⊢
    exact (he _).mp h

include D in
theorem hasHomotopyExtension : HomotopyExtension.HasHomotopyExtension (inclusion A) :=
  NeighborhoodDeformation.hasHomotopyExtension D IsEmbedding.subtypeVal

end NoExoticSixSphere.SubspaceCofibration
