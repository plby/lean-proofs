import Mathlib.Topology.Homeomorph.Defs

/-!
# Comparing actual quotient topologies with the same fibres

Two surjective quotient maps with exactly the same fibres determine a
homeomorphism, with its value fixed on every representative.  The inverse
is continuous by the original quotient topology, not by a transported one.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The comparison function determined by two quotient projections. -/
def quotientComparison (q : X → Y) (p : X → Z) (hq : Function.Surjective q) : Y → Z :=
  fun y => p (hq y).choose

omit [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] in
theorem quotientComparison_apply (q : X → Y) (p : X → Z) (hq : Function.Surjective q)
    (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    quotientComparison q p hq (q x) = p x :=
  (h _ _).mp (hq (q x)).choose_spec

theorem quotientComparison_continuous (q : X → Y) (p : X → Z)
    (hq : IsQuotientMap q) (hp : Continuous p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') :
    Continuous (quotientComparison q p hq.surjective) := by
  apply hq.continuous_iff.mpr
  have he : quotientComparison q p hq.surjective ∘ q = p :=
    funext (quotientComparison_apply q p hq.surjective h)
  rw [he]
  exact hp

/-- The homeomorphism forced by two actual quotient maps with identical fibres. -/
def quotientHomeomorph (q : X → Y) (p : X → Z)
    (hq : IsQuotientMap q) (hp : IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') : Y ≃ₜ Z where
  toFun := quotientComparison q p hq.surjective
  invFun := quotientComparison p q hp.surjective
  left_inv y := by
    obtain ⟨x, rfl⟩ := hq.surjective y
    rw [quotientComparison_apply q p hq.surjective h,
      quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm)]
  right_inv z := by
    obtain ⟨x, rfl⟩ := hp.surjective z
    rw [quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm),
      quotientComparison_apply q p hq.surjective h]
  continuous_toFun := quotientComparison_continuous q p hq hp.continuous h
  continuous_invFun := quotientComparison_continuous p q hp hq.continuous
    (fun x x' => (h x x').symm)

@[simp] theorem quotientHomeomorph_apply (q : X → Y) (p : X → Z)
    (hq : IsQuotientMap q) (hp : IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    quotientHomeomorph q p hq hp h (q x) = p x :=
  quotientComparison_apply q p hq.surjective h x

@[simp] theorem quotientHomeomorph_symm_apply (q : X → Y) (p : X → Z)
    (hq : IsQuotientMap q) (hp : IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    (quotientHomeomorph q p hq hp h).symm (p x) = q x :=
  quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm) x

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
