import Wikipedia.SmoothSixDPoincare.ClosedAttachment
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.CompactOpen

/-!
# Maps and whole homotopies on actual cell attachment quotients

Compatible maps descend through the defining quotient. For homotopies,
joint continuity follows from the quotient theorem for products with the
locally compact time interval; no separation or compactness of the attached
space or target is needed.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachmentMaps

open Wikipedia.SmoothSixDPoincare

variable {K M X : Type*} [TopologicalSpace K] [TopologicalSpace M] [TopologicalSpace X]
  (A : Set M) (B : Set K) (h : C(K, M))

def oldInclusion : C(A, ClosedAttachment.Space A B h) :=
  ⟨fun a => Quot.mk _ (.inl a), continuous_quot_mk.comp continuous_inl⟩

def cellInclusion : C(K, ClosedAttachment.Space A B h) :=
  ⟨fun k => Quot.mk _ (.inr k), continuous_quot_mk.comp continuous_inr⟩

theorem boundary_eq (a : A) (k : K) (hk : k ∈ B) (ha : a.val = h k) :
    oldInclusion A B h a = cellInclusion A B h k := Quot.sound ⟨hk, ha⟩

variable (f : C(A, X)) (g : C(K, X))
  (hc : ∀ a k, k ∈ B → a.val = h k → f a = g k)

include hc in
theorem sum_respects (a b : A ⊕ K) (hab : ClosedAttachment.Rel A B h a b) :
    Sum.elim f g a = Sum.elim f g b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hab.elim
    | inr k => exact hc a k hab.1 hab.2
  | inr k => cases b <;> exact hab.elim

/-- A genuine continuous map on the original attachment quotient. -/
def glue : C(ClosedAttachment.Space A B h, X) where
  toFun := Quot.lift (Sum.elim f g) (sum_respects A B h f g hc)
  continuous_toFun := continuous_quot_lift _ (continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩)

@[simp] theorem glue_old (a : A) : glue A B h f g hc (oldInclusion A B h a) = f a := rfl

@[simp] theorem glue_cell (k : K) : glue A B h f g hc (cellInclusion A B h k) = g k := rfl

variable (F : C(I × A, X)) (G : C(I × K, X))
  (hFG : ∀ t a k, k ∈ B → a.val = h k → F (t, a) = G (t, k))

def familyOld (t : I) : C(A, X) :=
  F.comp ⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩

def familyCell (t : I) : C(K, X) :=
  G.comp ⟨fun k => (t, k), continuous_const.prodMk continuous_id⟩

/-- The descended family is jointly continuous, including at all attachment points. -/
def glueFamily : C(I × ClosedAttachment.Space A B h, X) where
  toFun p := glue A B h (familyOld A F p.1) (familyCell G p.1) (hFG p.1) p.2
  continuous_toFun := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    have hc : Continuous (fun p : (I × A) ⊕ (I × K) => Sum.elim F G p) :=
      continuous_sum_dom.mpr ⟨F.continuous, G.continuous⟩
    convert hc.comp (Homeomorph.prodSumDistrib : I × (A ⊕ K) ≃ₜ _).continuous using 1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

@[simp] theorem glueFamily_old (t : I) (a : A) :
    glueFamily A B h F G hFG (t, oldInclusion A B h a) = F (t, a) := rfl

@[simp] theorem glueFamily_cell (t : I) (k : K) :
    glueFamily A B h F G hFG (t, cellInclusion A B h k) = G (t, k) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.AttachmentMaps
