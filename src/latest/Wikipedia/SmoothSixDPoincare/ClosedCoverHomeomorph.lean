import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn

/-!
# Gluing actual homeomorphisms on two closed pieces

The piece homeomorphisms must preserve precisely the cross-piece
identifications. Their maps and inverses then glue continuously over the two
closed covers. No compactness of the total spaces is needed, so the result
applies to the open complements obtained by deleting handle cores or belts.
-/

noncomputable section

open Set Function

namespace Wikipedia.SmoothSixDPoincare.ClosedCover

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {A B : Set X} {C D : Set Y}

def glue (hcover : A ∪ B = univ) (f : A → Y) (g : B → Y) : X → Y := by
  classical
  exact fun x => if hx : x ∈ A then f ⟨x, hx⟩ else
    g ⟨x, (show x ∈ A ∪ B by rw [hcover]; trivial).resolve_left hx⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem glue_left (hcover : A ∪ B = univ) (f : A → Y) (g : B → Y) (x : A) :
    glue hcover f g x = f x := by
  classical
  simp only [glue, dif_pos x.property]

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem glue_right (hcover : A ∪ B = univ) (f : A → Y) (g : B → Y)
    (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) (x : B) :
    glue hcover f g x = g x := by
  classical
  by_cases hx : (x : X) ∈ A
  · rw [glue, dif_pos hx]
    exact hagree ⟨x, hx⟩ x rfl
  · rw [glue, dif_neg hx]

theorem continuous_glue (hcover : A ∪ B = univ) (hA : IsClosed A) (hB : IsClosed B)
    (f : A → Y) (g : B → Y) (hf : Continuous f) (hg : Continuous g)
    (hagree : ∀ a : A, ∀ b : B, (a : X) = b → f a = g b) :
    Continuous (glue hcover f g) := by
  have hleft : ContinuousOn (glue hcover f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (glue hcover f g) = f :=
      funext (fun x => glue_left hcover f g x)
    rw [heq]
    exact hf
  have hright : ContinuousOn (glue hcover f g) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : B.domRestrict (glue hcover f g) = g :=
      funext (fun x => glue_right hcover f g hagree x)
    rw [heq]
    exact hg
  apply continuousOn_univ.mp
  rw [← hcover]
  exact hleft.union_of_isClosed hright hA hB

/-- Preserve the exact overlap identifications and glue both actual inverse maps. -/
def homeomorph (hcover : A ∪ B = univ) (hcover' : C ∪ D = univ)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) (hD : IsClosed D)
    (e : A ≃ₜ C) (f : B ≃ₜ D)
    (hcross : ∀ a : A, ∀ b : B, ((e a : C) : Y) = f b ↔ (a : X) = b) : X ≃ₜ Y := by
  let e₀ : A → Y := fun x => e x
  let f₀ : B → Y := fun x => f x
  let e₁ : C → X := fun y => e.symm y
  let f₁ : D → X := fun y => f.symm y
  have hagree : ∀ a : A, ∀ b : B, (a : X) = b → e₀ a = f₀ b :=
    fun a b h => (hcross a b).mpr h
  have hagreeInv : ∀ c : C, ∀ d : D, (c : Y) = d → e₁ c = f₁ d := by
    intro c d h
    apply (hcross (e.symm c) (f.symm d)).mp
    simpa only [e.apply_symm_apply, f.apply_symm_apply] using h
  let F := glue hcover e₀ f₀
  let G := glue hcover' e₁ f₁
  have hleft : LeftInverse G F := by
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · calc
        G (F x) = G (e₀ ⟨x, hx⟩) := congrArg G (glue_left hcover e₀ f₀ ⟨x, hx⟩)
        _ = e₁ (e ⟨x, hx⟩) := glue_left hcover' e₁ f₁ (e ⟨x, hx⟩)
        _ = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    · calc
        G (F x) = G (f₀ ⟨x, hx⟩) :=
          congrArg G (glue_right hcover e₀ f₀ hagree ⟨x, hx⟩)
        _ = f₁ (f ⟨x, hx⟩) := glue_right hcover' e₁ f₁ hagreeInv (f ⟨x, hx⟩)
        _ = x := congrArg Subtype.val (f.symm_apply_apply ⟨x, hx⟩)
  have hright : RightInverse G F := by
    intro y
    have hy : y ∈ C ∪ D := by rw [hcover']; trivial
    rcases hy with hy | hy
    · calc
        F (G y) = F (e₁ ⟨y, hy⟩) := congrArg F (glue_left hcover' e₁ f₁ ⟨y, hy⟩)
        _ = e₀ (e.symm ⟨y, hy⟩) := glue_left hcover e₀ f₀ (e.symm ⟨y, hy⟩)
        _ = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    · calc
        F (G y) = F (f₁ ⟨y, hy⟩) :=
          congrArg F (glue_right hcover' e₁ f₁ hagreeInv ⟨y, hy⟩)
        _ = f₀ (f.symm ⟨y, hy⟩) := glue_right hcover e₀ f₀ hagree (f.symm ⟨y, hy⟩)
        _ = y := congrArg Subtype.val (f.apply_symm_apply ⟨y, hy⟩)
  exact {
    toEquiv := { toFun := F, invFun := G, left_inv := hleft, right_inv := hright }
    continuous_toFun := continuous_glue hcover hA hB e₀ f₀
      (continuous_subtype_val.comp e.continuous) (continuous_subtype_val.comp f.continuous) hagree
    continuous_invFun := continuous_glue hcover' hC hD e₁ f₁
      (continuous_subtype_val.comp e.symm.continuous)
      (continuous_subtype_val.comp f.symm.continuous) hagreeInv }

theorem homeomorph_left (hcover : A ∪ B = univ) (hcover' : C ∪ D = univ)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) (hD : IsClosed D)
    (e : A ≃ₜ C) (f : B ≃ₜ D)
    (hcross : ∀ a : A, ∀ b : B, ((e a : C) : Y) = f b ↔ (a : X) = b) (a : A) :
    homeomorph hcover hcover' hA hB hC hD e f hcross a = (e a : Y) :=
  glue_left hcover (fun x => (e x : Y)) (fun x => (f x : Y)) a

theorem homeomorph_right (hcover : A ∪ B = univ) (hcover' : C ∪ D = univ)
    (hA : IsClosed A) (hB : IsClosed B) (hC : IsClosed C) (hD : IsClosed D)
    (e : A ≃ₜ C) (f : B ≃ₜ D)
    (hcross : ∀ a : A, ∀ b : B, ((e a : C) : Y) = f b ↔ (a : X) = b) (b : B) :
    homeomorph hcover hcover' hA hB hC hD e f hcross b = (f b : Y) :=
  glue_right hcover (fun x => (e x : Y)) (fun x => (f x : Y))
    (fun a b h => (hcross a b).mpr h) b

end Wikipedia.SmoothSixDPoincare.ClosedCover
