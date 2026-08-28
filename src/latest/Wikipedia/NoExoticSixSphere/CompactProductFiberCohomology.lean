import Wikipedia.NoExoticSixSphere.CompactSupportProperPullback

/-!
# Compact-support pullback from a product fiber

Projection from a product with a compact base is proper. Each fiber
inclusion is proper when the base is T1. The original composite is the
identity, so restricting the pulled-back compact-supported class to
any fiber recovers its original class. No product or Thom isomorphism
is assumed here.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactProductFiberCohomology

open CompactSupportCohomology

variable {B F : Type} [TopologicalSpace B] [TopologicalSpace F]

/-- The actual inclusion of a fiber, with its original product topology. -/
def fiberInclusion (b : B) : C(F, B × F) :=
  ⟨fun v => (b, v), continuous_const.prodMk continuous_id⟩

/-- A fiber over a closed point is closed and hence properly embedded. -/
theorem fiberInclusion_proper [T1Space B] (b : B) : IsProperMap (fiberInclusion (F := F) b) := by
  apply Topology.IsClosedEmbedding.isProperMap
  refine ⟨isEmbedding_prodMkRight b, ?_⟩
  have he : Set.range (fiberInclusion (F := F) b) = ({b} : Set B) ×ˢ Set.univ := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨rfl, Set.mem_univ _⟩
    · rintro ⟨hx, _⟩
      exact ⟨x.2, Prod.ext hx.symm rfl⟩
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

/-- Original compact-support restriction to this actual fiber. -/
def fiberPullback [T1Space B] (b : B) (p : ℕ) :
    Cohomology (B × F) p →ₗ[ℤ] Cohomology F p :=
  properPullback (fiberInclusion b) (fiberInclusion_proper b) p

/-- Pullback along the actual proper projection, for a compact base. -/
def projectionPullback [CompactSpace B] (p : ℕ) :
    Cohomology F p →ₗ[ℤ] Cohomology (B × F) p :=
  properPullback (ContinuousMap.snd : C(B × F, F)) isProperMap_snd_of_compactSpace p

/-- Each actual fiber restriction recovers the original compact-supported class. -/
theorem fiberPullback_projectionPullback [CompactSpace B] [T1Space B] (b : B) (p : ℕ)
    (a : Cohomology F p) :
    fiberPullback b p (projectionPullback (B := B) p a) = a :=
  (properPullback_comp (fiberInclusion b) (fiberInclusion_proper b)
    (ContinuousMap.snd : C(B × F, F)) isProperMap_snd_of_compactSpace p a).symm.trans
      (properPullback_id p a)

/-- A nonempty compact T1 base makes projection pullback injective. -/
theorem projectionPullback_injective [CompactSpace B] [T1Space B] (b : B) (p : ℕ) :
    Function.Injective (projectionPullback (B := B) (F := F) p) :=
  Function.LeftInverse.injective (fiberPullback_projectionPullback b p)

/-- A nonzero fiber class remains nonzero after the original projection pullback. -/
theorem projectionPullback_ne_zero [CompactSpace B] [T1Space B] (b : B) (p : ℕ)
    {a : Cohomology F p} (ha : a ≠ 0) : projectionPullback (B := B) p a ≠ 0 := by
  intro he
  apply ha
  apply projectionPullback_injective b p
  exact he.trans (projectionPullback (B := B) p).map_zero.symm

end NoExoticSixSphere.CompactProductFiberCohomology
