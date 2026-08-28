import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Glue two actual open patches by a partial homeomorphism

The equivalence relation identifies exactly the prescribed overlap. Both
patch maps are open embeddings and jointly cover the quotient. These exact
overlap formulas will carry the smooth transition data to its atlas.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e : OpenPartialHomeomorph X Y)

def Rel : X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl y => x = y
  | .inl x, .inr y => x ∈ e.source ∧ e x = y
  | .inr y, .inl x => y ∈ e.target ∧ e.symm y = x
  | .inr x, .inr y => x = y

theorem rel_equivalence : Equivalence (Rel e) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (x | y) <;> rfl
  · rintro (x | x) (y | y) h
    · exact h.symm
    · rcases h with ⟨hx, rfl⟩
      exact ⟨e.map_source hx, e.left_inv hx⟩
    · rcases h with ⟨hx, rfl⟩
      exact ⟨e.map_target hx, e.right_inv hx⟩
    · exact h.symm
  · rintro (x | x) (y | y) (z | z) hxy hyz
    · exact hxy.trans hyz
    · rcases hxy with rfl
      exact hyz
    · rcases hxy with ⟨hx, rfl⟩
      exact (e.left_inv hx).symm.trans hyz.2
    · rcases hyz with rfl
      exact hxy
    · rcases hyz with rfl
      exact hxy
    · rcases hxy with ⟨hx, rfl⟩
      exact (e.right_inv hx).symm.trans hyz.2
    · rcases hxy with rfl
      exact hyz
    · exact hxy.trans hyz

def setoid : Setoid (X ⊕ Y) := ⟨Rel e, rel_equivalence e⟩

abbrev Space := Quotient (setoid e)

def left : C(X, Space e) :=
  ⟨fun x => Quotient.mk (setoid e) (Sum.inl x),
    (continuous_quotient_mk' (s := setoid e)).comp continuous_inl⟩

def right : C(Y, Space e) :=
  ⟨fun y => Quotient.mk (setoid e) (Sum.inr y),
    (continuous_quotient_mk' (s := setoid e)).comp continuous_inr⟩

theorem left_eq_left (x x' : X) : left e x = left e x' ↔ x = x' := Quotient.eq

theorem right_eq_right (y y' : Y) : right e y = right e y' ↔ y = y' := Quotient.eq

theorem left_eq_right (x : X) (y : Y) : left e x = right e y ↔ x ∈ e.source ∧ e x = y :=
  Quotient.eq

theorem right_eq_left (y : Y) (x : X) : right e y = left e x ↔ y ∈ e.target ∧ e.symm y = x :=
  Quotient.eq

theorem cover (z : Space e) : z ∈ range (left e) ∪ range (right e) := by
  induction z using Quotient.inductionOn with
  | h a =>
      cases a with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr ⟨y, rfl⟩

theorem isOpen_iff (U : Set (Space e)) :
    IsOpen U ↔ IsOpen (left e ⁻¹' U) ∧ IsOpen (right e ⁻¹' U) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_sum_iff]
  rfl

theorem left_preimage_left_image (U : Set X) : left e ⁻¹' (left e '' U) = U :=
  preimage_image_eq U (fun _ _ h => (left_eq_left e _ _).mp h)

theorem right_preimage_right_image (V : Set Y) : right e ⁻¹' (right e '' V) = V :=
  preimage_image_eq V (fun _ _ h => (right_eq_right e _ _).mp h)

theorem right_preimage_left_image (U : Set X) :
    right e ⁻¹' (left e '' U) = e.target ∩ e.symm ⁻¹' U := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨hy, hyx⟩ := (right_eq_left e y x).mp hxy.symm
    exact ⟨hy, show e.symm y ∈ U from hyx.symm ▸ hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨e.symm y, hx, ((right_eq_left e y (e.symm y)).mpr ⟨hy, rfl⟩).symm⟩

theorem left_preimage_right_image (V : Set Y) :
    left e ⁻¹' (right e '' V) = e.source ∩ e ⁻¹' V := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨hx, hxy⟩ := (left_eq_right e x y).mp hyx.symm
    exact ⟨hx, show e x ∈ V from hxy.symm ▸ hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨e x, hy, ((left_eq_right e x (e x)).mpr ⟨hx, rfl⟩).symm⟩

theorem left_isOpenEmbedding : IsOpenEmbedding (left e) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (left e).continuous
    (fun _ _ h => (left_eq_left e _ _).mp h)
  intro U hU
  rw [isOpen_iff, left_preimage_left_image, right_preimage_left_image]
  exact ⟨hU, e.continuousOn_invFun.isOpen_inter_preimage e.open_target hU⟩

theorem right_isOpenEmbedding : IsOpenEmbedding (right e) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (right e).continuous
    (fun _ _ h => (right_eq_right e _ _).mp h)
  intro V hV
  rw [isOpen_iff, left_preimage_right_image, right_preimage_right_image]
  exact ⟨e.continuousOn_toFun.isOpen_inter_preimage e.open_source hV, hV⟩

end Wikipedia.SmoothSixDPoincare.OpenGluing
