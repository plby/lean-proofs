import Wikipedia.NoExoticSixSphere.IntersectionTraceEndpointChart

/-!
# Reversing the actual intersection trace

Time reversal is a homeomorphism of the original coincidence loci. It
interchanges the actual endpoint sets and transports the constructed initial
half-line charts to terminal half-line charts, with coordinate `1 - t`.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.IntersectionTrace

open MapIntersections InvolutionQuotient

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : ℝ → X → Z) (g : ℝ → Y → Z)

def reverseAmbient : (ℝ × (X × Y)) ≃ₜ (ℝ × (X × Y)) where
  toFun q := (1 - q.1, q.2)
  invFun q := (1 - q.1, q.2)
  left_inv q := Prod.ext (by dsimp; ring) rfl
  right_inv q := Prod.ext (by dsimp; ring) rfl
  continuous_toFun := (continuous_const.sub continuous_fst).prodMk continuous_snd
  continuous_invFun := (continuous_const.sub continuous_fst).prodMk continuous_snd

theorem reverseAmbient_mem_space_iff (q : ℝ × (X × Y)) :
    reverseAmbient q ∈ space (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) ↔ q ∈ space f g := by
  change ((0 ≤ 1 - q.1 ∧ 1 - q.1 ≤ 1) ∧
    f (1 - (1 - q.1)) q.2.1 = g (1 - (1 - q.1)) q.2.2) ↔ _
  have ht : 1 - (1 - q.1) = q.1 := by ring
  rw [ht]
  constructor
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨⟨by linarith, by linarith⟩, heq⟩
  · rintro ⟨⟨ha, hb⟩, heq⟩
    exact ⟨⟨by linarith, by linarith⟩, heq⟩

def reverseHomeomorph : space f g ≃ₜ space (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) :=
  reverseAmbient.subtype (fun q ↦ (reverseAmbient_mem_space_iff f g q).symm)

theorem reverseHomeomorph_val (q : space f g) :
    (reverseHomeomorph f g q).val = (1 - q.val.1, q.val.2) := rfl

theorem reverseHomeomorph_mem_ends_iff (q : space f g) :
    reverseHomeomorph f g q ∈ ends (fun t ↦ f (1 - t)) (fun t ↦ g (1 - t)) ↔
      q ∈ ends f g := by
  change (1 - q.val.1 = 0 ∨ 1 - q.val.1 = 1) ↔ (q.val.1 = 0 ∨ q.val.1 = 1)
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

theorem exists_one_halfLine_chart [T2Space X] [T2Space Y]
    (p : pairs (f 1) (g 1)) (c : ℝ) (hc : c ≤ 1) (hcpos : 0 < c)
    (hcoll : ∀ t ∈ Icc 0 c, pairs (f (1 - t)) (g (1 - t)) = pairs (f 1) (g 1))
    (hfin : (pairs (f 1) (g 1)).Finite) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      endpoint f g 1 p ∈ d.source ∧ (∀ q, (d q).val = 1 - q.val.1) ∧
      ∀ q ∈ d.source, (d q).val = 0 ↔ q ∈ ends f g := by
  let f' : ℝ → X → Z := fun t ↦ f (1 - t)
  let g' : ℝ → Y → Z := fun t ↦ g (1 - t)
  have heq : pairs (f' 0) (g' 0) = pairs (f 1) (g 1) := by simp only [f', g', sub_zero]
  let p' : pairs (f' 0) (g' 0) := ⟨p.val, heq.symm ▸ p.property⟩
  have hc' : ∀ t ∈ Icc 0 c, pairs (f' t) (g' t) = pairs (f' 0) (g' 0) :=
    fun t ht ↦ (hcoll t ht).trans heq.symm
  obtain ⟨d, hdp, hdtime, hdB⟩ := exists_zero_halfLine_chart f' g' p' c hc hc' hcpos
    (heq.symm ▸ hfin)
  let e := reverseHomeomorph f g
  have hep : e (endpoint f g 1 p) = endpoint f' g' 0 p' := by
    apply Subtype.ext
    exact Prod.ext (by change (1 : ℝ) - 1 = 0; ring) rfl
  refine ⟨e.toOpenPartialHomeomorph.trans d, ⟨mem_univ _, ?_⟩, ?_, ?_⟩
  · change d.source (e (endpoint f g 1 p))
    rw [hep]
    exact hdp
  · intro q
    exact hdtime (e q)
  · intro q hq
    exact (hdB (e q) hq.2).trans (reverseHomeomorph_mem_ends_iff f g q)

end NoExoticSixSphere.IntersectionTrace
