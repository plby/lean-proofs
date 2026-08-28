import Wikipedia.SmoothSixDPoincare.CompactClosedQuotient
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Glue two bodies along their actual boundary maps

The quotient identifies exactly the two images of each common-boundary
point. Its two whole-piece maps and universal continuous map are explicit.
For injective boundary maps the full fibers are computed, and the compact
Hausdorff case retains the actual quotient topology and embedded bodies.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.BoundaryGluing

variable {B X Y Z : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace Z] (i : C(B, X)) (j : C(B, Y))

def Rel : X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inr y => ∃ b, i b = x ∧ j b = y
  | _, _ => False

abbrev Space := Quot (Rel i j)

def left : C(X, Space i j) :=
  ⟨fun x => Quot.mk _ (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩

def right : C(Y, Space i j) :=
  ⟨fun y => Quot.mk _ (Sum.inr y), continuous_quot_mk.comp continuous_inr⟩

theorem identification (b : B) : left i j (i b) = right i j (j b) :=
  Quot.sound ⟨b, rfl, rfl⟩

theorem induction_on (q : Space i j) {P : Space i j → Prop}
    (hleft : ∀ x, P (left i j x)) (hright : ∀ y, P (right i j y)) : P q := by
  induction q using Quot.inductionOn with
  | _ q => cases q with
    | inl x => exact hleft x
    | inr y => exact hright y

def desc (f : C(X, Z)) (g : C(Y, Z)) (h : ∀ b, f (i b) = g (j b)) : C(Space i j, Z) := by
  have hr : ∀ p q, Rel i j p q → Sum.elim f g p = Sum.elim f g q := by
    rintro (x | y) (x' | y') hp
    · exact hp.elim
    · obtain ⟨b, rfl, rfl⟩ := hp
      exact h b
    · exact hp.elim
    · exact hp.elim
  exact ⟨Quot.lift (Sum.elim f g) hr,
    continuous_quot_lift hr (f.continuous.sumElim g.continuous)⟩

theorem desc_left (f : C(X, Z)) (g : C(Y, Z)) (h : ∀ b, f (i b) = g (j b)) (x : X) :
    desc i j f g h (left i j x) = f x := rfl

theorem desc_right (f : C(X, Z)) (g : C(Y, Z)) (h : ∀ b, f (i b) = g (j b)) (y : Y) :
    desc i j f g h (right i j y) = g y := rfl

def ExactRel : X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl x' => x = x'
  | .inl x, .inr y => ∃ b, i b = x ∧ j b = y
  | .inr y, .inl x => ∃ b, i b = x ∧ j b = y
  | .inr y, .inr y' => y = y'

theorem exactRel_equivalence (hi : Injective i) (hj : Injective j) :
    Equivalence (ExactRel i j) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (x | y) <;> rfl
  · rintro (x | y) (x' | y') h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  · rintro (x | y) (x' | y') (x'' | y'') h₁ h₂
    · exact h₁.trans h₂
    · rcases h₁ with rfl
      exact h₂
    · obtain ⟨a, ha, hay⟩ := h₁
      obtain ⟨b, hb, hby⟩ := h₂
      exact ha.symm.trans ((congrArg i (hj (hay.trans hby.symm))).trans hb)
    · rcases h₂ with rfl
      exact h₁
    · rcases h₂ with rfl
      exact h₁
    · obtain ⟨a, ha, hay⟩ := h₁
      obtain ⟨b, hb, hby⟩ := h₂
      exact hay.symm.trans ((congrArg j (hi (ha.trans hb.symm))).trans hby)
    · rcases h₁ with rfl
      exact h₂
    · exact h₁.trans h₂

def exactSetoid (hi : Injective i) (hj : Injective j) : Setoid (X ⊕ Y) :=
  ⟨ExactRel i j, exactRel_equivalence i j hi hj⟩

private def exactDetector (hi : Injective i) (hj : Injective j) :
    Space i j → Quotient (exactSetoid i j hi hj) :=
  Quot.lift (Quotient.mk (exactSetoid i j hi hj)) (by
    rintro (x | y) (x' | y') h
    · exact h.elim
    · exact Quotient.sound h
    · exact h.elim
    · exact h.elim)

theorem quotient_eq_iff (hi : Injective i) (hj : Injective j) (p q : X ⊕ Y) :
    Quot.mk (Rel i j) p = Quot.mk (Rel i j) q ↔ ExactRel i j p q := by
  constructor
  · intro h
    exact Quotient.exact (congrArg (exactDetector i j hi hj) h)
  · cases p with
    | inl x => cases q with
      | inl x' => intro h; exact congrArg (fun z => Quot.mk _ (Sum.inl z)) h
      | inr y => intro h; exact Quot.sound h
    | inr y => cases q with
      | inl x =>
          intro h
          exact (Quot.sound (r := Rel i j) (a := Sum.inl x) (b := Sum.inr y) h).symm
      | inr y' => intro h; exact congrArg (fun z => Quot.mk _ (Sum.inr z)) h

theorem left_eq_left (hi : Injective i) (hj : Injective j) (x x' : X) :
    left i j x = left i j x' ↔ x = x' := quotient_eq_iff i j hi hj _ _

theorem right_eq_right (hi : Injective i) (hj : Injective j) (y y' : Y) :
    right i j y = right i j y' ↔ y = y' := quotient_eq_iff i j hi hj _ _

theorem left_eq_right (hi : Injective i) (hj : Injective j) (x : X) (y : Y) :
    left i j x = right i j y ↔ ∃ b, i b = x ∧ j b = y := quotient_eq_iff i j hi hj _ _

theorem cover (q : Space i j) : q ∈ range (left i j) ∪ range (right i j) :=
  induction_on i j q (fun x => Or.inl ⟨x, rfl⟩) (fun y => Or.inr ⟨y, rfl⟩)

def commute : Space i j ≃ₜ Space j i where
  toFun := desc i j (right j i) (left j i) (fun b => (identification j i b).symm)
  invFun := desc j i (right i j) (left i j) (fun b => (identification i j b).symm)
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ z => cases z <;> rfl
  right_inv q := by
    induction q using Quot.inductionOn with
    | _ z => cases z <;> rfl
  continuous_toFun := (desc i j _ _ _).continuous
  continuous_invFun := (desc j i _ _ _).continuous

theorem commute_left (x : X) : commute i j (left i j x) = right j i x := rfl

theorem commute_right (y : Y) : commute i j (right i j y) = left j i y := rfl

variable [CompactSpace B] [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

theorem isClosed_exactRel : IsClosed {p : (X ⊕ Y) × (X ⊕ Y) | ExactRel i j p.1 p.2} := by
  let dX : X → (X ⊕ Y) × (X ⊕ Y) := fun x => (.inl x, .inl x)
  let dY : Y → (X ⊕ Y) × (X ⊕ Y) := fun y => (.inr y, .inr y)
  let f : B → (X ⊕ Y) × (X ⊕ Y) := fun b => (.inl (i b), .inr (j b))
  let g : B → (X ⊕ Y) × (X ⊕ Y) := fun b => (.inr (j b), .inl (i b))
  have hdX : Continuous dX := continuous_inl.prodMk continuous_inl
  have hdY : Continuous dY := continuous_inr.prodMk continuous_inr
  have hf : Continuous f := (continuous_inl.comp i.continuous).prodMk
    (continuous_inr.comp j.continuous)
  have hg : Continuous g := (continuous_inr.comp j.continuous).prodMk
    (continuous_inl.comp i.continuous)
  have heq : {p : (X ⊕ Y) × (X ⊕ Y) | ExactRel i j p.1 p.2} =
      (range dX ∪ range dY) ∪ (range f ∪ range g) := by
    ext p
    rcases p with ⟨x | y, x' | y'⟩
    · simp [ExactRel, dX, dY, f, g, eq_comm]
    · simp [ExactRel, dX, dY, f, g]
    · simp [ExactRel, dX, dY, f, g, and_comm]
    · simp [ExactRel, dX, dY, f, g, eq_comm]
  rw [heq]
  exact (((isCompact_range hdX).union (isCompact_range hdY)).union
    ((isCompact_range hf).union (isCompact_range hg))).isClosed

theorem t2Space (hi : Injective i) (hj : Injective j) : T2Space (Space i j) := by
  apply CompactClosedQuotient.t2Space isQuotientMap_quot_mk
  convert isClosed_exactRel i j using 1
  ext p
  exact quotient_eq_iff i j hi hj p.1 p.2

theorem left_isClosedEmbedding (hi : Injective i) (hj : Injective j) :
    IsClosedEmbedding (left i j) := by
  let _ : T2Space (Space i j) := t2Space i j hi hj
  exact (left i j).continuous.isClosedEmbedding (fun x y h => (left_eq_left i j hi hj x y).mp h)

theorem right_isClosedEmbedding (hi : Injective i) (hj : Injective j) :
    IsClosedEmbedding (right i j) := by
  let _ : T2Space (Space i j) := t2Space i j hi hj
  exact (right i j).continuous.isClosedEmbedding (fun x y h => (right_eq_right i j hi hj x y).mp h)

end Wikipedia.SmoothSixDPoincare.BoundaryGluing
