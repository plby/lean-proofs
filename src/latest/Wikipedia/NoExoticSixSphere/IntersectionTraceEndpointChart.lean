import Wikipedia.NoExoticSixSphere.SphereIntersectionTrace

/-!
# Actual half-line coordinates at collared intersection endpoints

Finitely many endpoint intersections are isolated in the original source
product. When the coincidence equation is constant in a time collar, the
time coordinate is a genuine half-line chart near each endpoint. Its zero
locus is exactly the time-end set. No endpoint chart is postulated.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.IntersectionTrace

open MapIntersections InvolutionQuotient

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : ℝ → X → Z) (g : ℝ → Y → Z) (p : pairs (f 0) (g 0))
  (c : ℝ) (hc : c ≤ 1)
  (hcoll : ∀ t ∈ Icc 0 c, pairs (f t) (g t) = pairs (f 0) (g 0))

def zeroChartInverse (v : HalfLine) : space f g := by
  classical
  exact if hv : v.val < c then
    ⟨(v.val, p.val), ⟨v.property, (hv.trans_le hc).le⟩, by
      change p.val ∈ pairs (f v.val) (g v.val)
      rw [hcoll v.val ⟨v.property, hv.le⟩]
      exact p.property⟩
  else endpoint f g 0 p

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem zeroChartInverse_val (v : HalfLine) (hv : v.val < c) :
    (zeroChartInverse f g p c hc hcoll v).val = (v.val, p.val) := by
  simp only [zeroChartInverse, dif_pos hv]

variable (O : Set (X × Y)) (hO : IsOpen O) (hp : p.val ∈ O)
  (hiso : ∀ q ∈ O, q ∈ pairs (f 0) (g 0) → q = p.val)

def zeroChart : OpenPartialHomeomorph (space f g) HalfLine where
  toFun q := ⟨q.val.1, q.property.1.1⟩
  invFun := zeroChartInverse f g p c hc hcoll
  source := {q | q.val.1 < c ∧ q.val.2 ∈ O}
  target := {v | v.val < c}
  map_source' _ hq := hq.1
  map_target' v hv := by
    change (zeroChartInverse f g p c hc hcoll v).val.1 < c ∧
      (zeroChartInverse f g p c hc hcoll v).val.2 ∈ O
    rw [zeroChartInverse_val f g p c hc hcoll v hv]
    exact ⟨hv, hp⟩
  left_inv' q hq := by
    apply Subtype.ext
    rw [zeroChartInverse_val f g p c hc hcoll _ hq.1]
    refine Prod.ext rfl (hiso q.val.2 hq.2 ?_).symm
    rw [← hcoll q.val.1 ⟨q.property.1.1, hq.1.le⟩]
    exact q.property.2
  right_inv' v hv := by
    apply Subtype.ext
    exact congrArg Prod.fst (zeroChartInverse_val f g p c hc hcoll v hv)
  open_source := (isOpen_lt continuous_subtype_val.fst continuous_const).inter
    (hO.preimage continuous_subtype_val.snd)
  open_target := isOpen_lt continuous_subtype_val continuous_const
  continuousOn_toFun := (continuous_subtype_val.fst.subtype_mk _).continuousOn
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (continuous_subtype_val.prodMk continuous_const).continuousOn.congr
      (fun v hv ↦ zeroChartInverse_val f g p c hc hcoll v hv)

theorem zeroChart_apply (q : space f g) :
    (zeroChart f g p c hc hcoll O hO hp hiso q).val = q.val.1 := rfl

theorem zeroChart_mem_source (hcpos : 0 < c) :
    endpoint f g 0 p ∈ (zeroChart f g p c hc hcoll O hO hp hiso).source := ⟨hcpos, hp⟩

theorem zeroChart_zero_iff (q : space f g)
    (hq : q ∈ (zeroChart f g p c hc hcoll O hO hp hiso).source) :
    (zeroChart f g p c hc hcoll O hO hp hiso q).val = 0 ↔ q ∈ ends f g := by
  change q.val.1 = 0 ↔ q.val.1 = 0 ∨ q.val.1 = 1
  constructor
  · exact Or.inl
  · rintro (h | h)
    · exact h
    · have hlt : q.val.1 < 1 := hq.1.trans_le hc
      exact False.elim (lt_irrefl 1 (h ▸ hlt))

include hc hcoll in
/-- The chart is constructed from finite endpoint intersections and an actual
constant coincidence collar. Its coordinate is the original time. -/
theorem exists_zero_halfLine_chart [T2Space X] [T2Space Y] (hcpos : 0 < c)
    (hfin : (pairs (f 0) (g 0)).Finite) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      endpoint f g 0 p ∈ d.source ∧ (∀ q, (d q).val = q.val.1) ∧
      ∀ q ∈ d.source, (d q).val = 0 ↔ q ∈ ends f g := by
  let O : Set (X × Y) := (pairs (f 0) (g 0) \ {p.val})ᶜ
  have hO : IsOpen O := hfin.sdiff.isClosed.isOpen_compl
  have hpO : p.val ∈ O := by simp only [O, mem_compl_iff, mem_sdiff, mem_singleton_iff]; tauto
  have hiso : ∀ q ∈ O, q ∈ pairs (f 0) (g 0) → q = p.val := by
    intro q hq hpair
    by_contra hne
    exact hq ⟨hpair, hne⟩
  exact ⟨zeroChart f g p c hc hcoll O hO hpO hiso,
    zeroChart_mem_source f g p c hc hcoll O hO hpO hiso hcpos,
    zeroChart_apply f g p c hc hcoll O hO hpO hiso,
    zeroChart_zero_iff f g p c hc hcoll O hO hpO hiso⟩

end NoExoticSixSphere.IntersectionTrace
