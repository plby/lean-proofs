import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections
import Wikipedia.NoExoticSixSphere.CompactFiberCardinality

/-!
# The actual coincidence trace in a compact source-pair region

The trace keeps real time in the closed interval `[-1,1]` and the original
sphere pair in a specified compact region. Its actual time fibers are in
bijection with the corresponding coincidence pairs in that region.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CompactPairTrace

variable {M : Type*} (f g : ℝ → Sphere 3 → M) (K : Set (Sphere 3 × Sphere 3))

def space : Set (ℝ × (Sphere 3 × Sphere 3)) :=
  (Icc (-1 : ℝ) 1 ×ˢ K) ∩ {p | f p.1 p.2.1 = g p.1 p.2.2}

def time : C(space f g K, ℝ) :=
  ⟨fun p ↦ p.val.1, continuous_subtype_val.fst⟩

def fiberPairEquiv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ↥((time f g K) ⁻¹' {t}) ≃ ↥(K ∩ MapIntersections.pairs (f t) (g t)) where
  toFun p := ⟨p.val.val.2, p.val.property.1.2, by
    have htime : p.val.val.1 = t := p.property
    change f t p.val.val.2.1 = g t p.val.val.2.2
    have he : f p.val.val.1 p.val.val.2.1 = g p.val.val.1 p.val.val.2.2 := p.val.property.2
    rwa [htime] at he⟩
  invFun p := ⟨⟨(t, p.val), ⟨ht, p.property.1⟩, p.property.2⟩, rfl⟩
  left_inv p := Subtype.ext (Subtype.ext (Prod.ext p.property.symm rfl))
  right_inv _ := Subtype.ext rfl

theorem fiber_ncard (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
    ((time f g K) ⁻¹' {t}).ncard = (K ∩ MapIntersections.pairs (f t) (g t)).ncard :=
  Nat.card_congr (fiberPairEquiv f g K t ht)

variable [TopologicalSpace M] [T2Space M]

theorem isCompact_space (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hK : IsCompact K) : IsCompact (space f g K) :=
  (isCompact_Icc.prod hK).inter_right
    (isClosed_eq (hf.comp (continuous_fst.prodMk continuous_snd.fst))
      (hg.comp (continuous_fst.prodMk continuous_snd.snd)))

end NoExoticSixSphere.CompactPairTrace
