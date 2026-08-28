import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.SmoothSixDPoincare.FiniteTransverseIntersections
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic

/-!
# Actual intersection pairs of transverse embedded three-spheres

The count is taken on the original source pairs, not on an assigned algebraic
model. For embeddings, these pairs are in bijection with the intersection of
the two images. Native transversality and compactness prove finiteness.
Swapping the sheets or changing their parametrizations preserves the count.
Homotopy invariance and identification with a homological pairing are not
asserted here.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.MapIntersections

variable {X Y Z X' Y' : Type*}

/-- The actual ordered source pairs whose images coincide. -/
def pairs (f : X → Z) (g : Y → Z) : Set (X × Y) := {p | f p.1 = g p.2}

def imagePoint (f : X → Z) (g : Y → Z) (p : pairs f g) : ↥(range f ∩ range g) :=
  ⟨f p.val.1, ⟨⟨p.val.1, rfl⟩, ⟨p.val.2, p.property.symm⟩⟩⟩

theorem imagePoint_bijective (f : X → Z) (g : Y → Z)
    (hf : Injective f) (hg : Injective g) : Bijective (imagePoint f g) := by
  constructor
  · intro p q h
    have hx : f p.val.1 = f q.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    exact Prod.ext (hf hx) (hg (p.property.symm.trans (hx.trans q.property)))
  · rintro ⟨z, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    exact ⟨⟨(x, y), hx.trans hy.symm⟩, Subtype.ext hx⟩

def imageEquiv (f : X → Z) (g : Y → Z) (hf : Injective f) (hg : Injective g) :
    pairs f g ≃ ↥(range f ∩ range g) :=
  Equiv.ofBijective (imagePoint f g) (imagePoint_bijective f g hf hg)

theorem finite_pairs (f : X → Z) (g : Y → Z) (hf : Injective f) (hg : Injective g)
    (hfin : (range f ∩ range g).Finite) : (pairs f g).Finite := by
  let := hfin.to_subtype
  exact finite_coe_iff.mp (Finite.of_equiv ↥(range f ∩ range g) (imageEquiv f g hf hg).symm)

theorem pairs_ncard_eq_image (f : X → Z) (g : Y → Z)
    (hf : Injective f) (hg : Injective g) :
    (pairs f g).ncard = (range f ∩ range g).ncard :=
  Nat.card_congr (imageEquiv f g hf hg)

def swapEquiv (f : X → Z) (g : Y → Z) : pairs f g ≃ pairs g f where
  toFun p := ⟨p.val.swap, p.property.symm⟩
  invFun p := ⟨p.val.swap, p.property.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem pairs_ncard_comm (f : X → Z) (g : Y → Z) :
    (pairs f g).ncard = (pairs g f).ncard := Nat.card_congr (swapEquiv f g)

def reparametrizeEquiv (f : X → Z) (g : Y → Z) (u : X' ≃ X) (v : Y' ≃ Y) :
    pairs (f ∘ u) (g ∘ v) ≃ pairs f g where
  toFun p := ⟨(u p.val.1, v p.val.2), p.property⟩
  invFun p := ⟨(u.symm p.val.1, v.symm p.val.2), by
    simpa only [pairs, mem_ofPred_eq, Function.comp_apply, Equiv.apply_symm_apply]
      using p.property⟩
  left_inv p := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv p := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

theorem pairs_ncard_reparametrize (f : X → Z) (g : Y → Z) (u : X' ≃ X) (v : Y' ≃ Y) :
    (pairs (f ∘ u) (g ∘ v)).ncard = (pairs f g).ncard :=
  Nat.card_congr (reparametrizeEquiv f g u v)

/-- The mod-two count of actual intersection pairs; finiteness is proved below
for transverse embedded three-spheres. -/
def parity (f : X → Z) (g : Y → Z) : ZMod 2 := (pairs f g).ncard

theorem parity_comm (f : X → Z) (g : Y → Z) : parity f g = parity g f := by
  unfold parity
  rw [pairs_ncard_comm]

theorem parity_reparametrize (f : X → Z) (g : Y → Z) (u : X' ≃ X) (v : Y' ≃ Y) :
    parity (f ∘ u) (g ∘ v) = parity f g := by
  unfold parity
  rw [pairs_ncard_reparametrize]

theorem parity_eq_image_count (f : X → Z) (g : Y → Z)
    (hf : Injective f) (hg : Injective g) :
    parity f g = ((range f ∩ range g).ncard : ZMod 2) := by
  unfold parity
  rw [pairs_ncard_eq_image f g hf hg]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Finiteness follows from the actual native tangent maps, not a count hypothesis. -/
theorem finite_transverse_sphere_pairs {f g : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hi : Injective f) (hj : Injective g)
    (ht : ∀ x y, f x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) :
    (pairs f g).Finite := by
  apply finite_pairs f g hi hj
  exact Wikipedia.SmoothSixDPoincare.finite_transverse_intersections hf hg hi hj
    (by simp) (fun x y h ↦ ht x y h.symm)

end NoExoticSixSphere.MapIntersections
