import Wikipedia.NoExoticSixSphere.UnorderedFamilyTime
import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints
import Wikipedia.NoExoticSixSphere.FamilyDoublePointOpenLocus

/-!
# A regular-time fiber is the original unordered sphere double-point set

The comparison preserves the actual source pairs. Immersion excludes any
diagonal point of the family closure at that time, while continuity gives
equality of the two image limits. Quotienting by the original sheet swap
therefore yields a genuine bijection, not an assigned fiber cardinality.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization FamilyEmbedding

variable {M : Type*} (f : ℝ → Sphere 3 → M) (t : ℝ)

def pairInFamilyClosure (p : SphereSelfIntersections.pairs (f t)) :
    closure (doublePoints f) := ⟨(t, p.val), subset_closure p.property⟩

def unorderedPairToTimeFiber : SphereSelfIntersections.Unordered (f t) →
    {q : UnorderedClosedDoublePoints f // unorderedTime f q = t} :=
  Quotient.lift
    (fun p : SphereSelfIntersections.pairs (f t) ↦
      ⟨unorderedProj f (pairInFamilyClosure f t p), rfl⟩) (by
      intro p q hpq
      change p = q ∨ SphereSelfIntersections.swap (f t) p = q at hpq
      rcases hpq with rfl | hpq
      · rfl
      · apply Subtype.ext
        apply (unorderedProj_eq_iff f _ _).mpr
        exact Or.inr (congrArg (fun p : SphereSelfIntersections.pairs (f t) ↦ (t, p.val)) hpq))

theorem unorderedPairToTimeFiber_proj (p : SphereSelfIntersections.pairs (f t)) :
    (unorderedPairToTimeFiber f t (SphereSelfIntersections.unorderedProj (f t) p)).val =
      unorderedProj f (pairInFamilyClosure f t p) := rfl

theorem unorderedPairToTimeFiber_injective : Injective (unorderedPairToTimeFiber f t) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro x y he
  have he' := congrArg Subtype.val he
  change unorderedProj f (pairInFamilyClosure f t x) =
    unorderedProj f (pairInFamilyClosure f t y) at he'
  apply Quotient.sound
  change x = y ∨ SphereSelfIntersections.swap (f t) x = y
  rcases (unorderedProj_eq_iff f _ _).mp he' with h | h
  · exact Or.inl (Subtype.ext (congrArg Prod.snd h))
  · exact Or.inr (Subtype.ext (congrArg Prod.snd h))

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (f t) s))

include hf hi in
theorem unorderedPairToTimeFiber_surjective : Surjective (unorderedPairToTimeFiber f t) := by
  intro q
  obtain ⟨a, ha⟩ := (isOpenQuotientMap_unorderedProj f).surjective q.val
  have hat : a.val.1 = t := (congrArg (unorderedTime f) ha).trans q.property
  have hne : a.val.2.1 ≠ a.val.2.2 := by
    intro he
    have hp : (t, (a.val.2.1, a.val.2.1)) ∈ closure (doublePoints f) := by
      have ha' : (a.val.1, (a.val.2.1, a.val.2.2)) ∈ closure (doublePoints f) := a.property
      rwa [hat, ← he] at ha'
    exact diagonal_not_mem_closure f hf (t, a.val.2.1) (hi _) hp
  have heq : f t a.val.2.1 = f t a.val.2.2 := by
    have he' := closure_doublePoints_equal_image_of_continuous f hf.continuous a.property
    rwa [hat] at he'
  let p : SphereSelfIntersections.pairs (f t) := ⟨a.val.2, hne, heq⟩
  refine ⟨SphereSelfIntersections.unorderedProj (f t) p, ?_⟩
  apply Subtype.ext
  rw [unorderedPairToTimeFiber_proj]
  have hp : pairInFamilyClosure f t p = a := Subtype.ext (Prod.ext hat.symm rfl)
  rw [hp]
  exact ha

def unorderedTimeFiberEquiv : SphereSelfIntersections.Unordered (f t) ≃
    {q : UnorderedClosedDoublePoints f // unorderedTime f q = t} :=
  Equiv.ofBijective (unorderedPairToTimeFiber f t)
    ⟨unorderedPairToTimeFiber_injective f t, unorderedPairToTimeFiber_surjective f t hf hi⟩

include hf hi in
theorem unorderedTimeFiber_card :
    Nat.card {q : UnorderedClosedDoublePoints f // unorderedTime f q = t} =
      Nat.card (SphereSelfIntersections.Unordered (f t)) :=
  (Nat.card_congr (unorderedTimeFiberEquiv f t hf hi)).symm

end NoExoticSixSphere.SphereFamily
