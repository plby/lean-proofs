import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending a compactly supported chart homotopy

A continuous family of self-maps of the source of an open partial
homeomorphism extends by the identity when its support is compact in the
source. The construction retains pointwise fixed-set, height, and endpoint
properties without any collar or triangulation hypothesis.
-/

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction.Supported

variable {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]

/-- Conjugate a chart map in its target, and use the identity elsewhere. -/
noncomputable def extend (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (p : S × Y) : Y := by
  classical
  exact if hy : p.2 ∈ e.target then
    e (H (p.1, ⟨e.symm p.2, e.map_target hy⟩))
  else p.2

theorem extend_target (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∈ e.target) :
    extend e H (s, y) = e (H (s, ⟨e.symm y, e.map_target hy⟩)) := by
  exact dif_pos hy

theorem extend_not_mem_target (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (y : Y) (hy : y ∉ e.target) :
    extend e H (s, y) = y := by
  exact dif_neg hy

/-- The extension agrees exactly with chart conjugation. -/
theorem extend_chart (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (x : e.source) :
    extend e H (s, e x) = e (H (s, x)) := by
  rw [extend_target e H s (e x) (e.map_source x.2)]
  exact congrArg (fun z : e.source => e (H (s, z))) (Subtype.ext (e.left_inv x.2))

/-- Outside the image of the support, all stages are the identity. -/
theorem extend_not_mem_image (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x)
    (s : S) (y : Y) (hyK : y ∉ e '' K) : extend e H (s, y) = y := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy]
    have hxK : e.symm y ∉ K := fun hx => hyK ⟨e.symm y, hx, e.right_inv hy⟩
    rw [hfix s ⟨e.symm y, e.map_target hy⟩ hxK]
    exact e.right_inv hy
  · exact extend_not_mem_target e H s y hy

theorem extend_continuousOn_target (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) :
    ContinuousOn (extend e H) (Prod.snd ⁻¹' e.target) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let g : (Prod.snd ⁻¹' e.target : Set (S × Y)) → S × e.source :=
    fun p => (p.1.1, e.toHomeomorphSourceTarget.symm ⟨p.1.2, p.2⟩)
  have hg : Continuous g :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (e.toHomeomorphSourceTarget.symm.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hc := continuous_subtype_val.comp
    (e.toHomeomorphSourceTarget.continuous.comp (H.continuous.comp hg))
  apply hc.congr
  intro p
  exact (extend_target e H p.1.1 p.1.2 p.2).symm

/-- Compact support permits open pasting across the chart boundary. -/
theorem extend_continuous [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X) (hK : IsCompact K)
    (hKs : K ⊆ e.source)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) :
    Continuous (extend e H) := by
  have hclosed : IsClosed (e '' K) :=
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)).isClosed
  have hout : ContinuousOn (extend e H) (Prod.snd ⁻¹' (e '' K)ᶜ) :=
    continuous_snd.continuousOn.congr fun p hp =>
      extend_not_mem_image e H K hfix p.1 p.2 hp
  have hcover : (Prod.snd ⁻¹' e.target : Set (S × Y)) ∪
      (Prod.snd ⁻¹' (e '' K)ᶜ) = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p.2 ∈ e.target
    · exact Or.inl hp
    · right
      rintro ⟨x, hx, hxy⟩
      exact hp (hxy ▸ e.map_source (hKs hx))
  rw [← continuousOn_univ, ← hcover]
  exact (extend_continuousOn_target e H).union_of_isOpen hout
    (e.open_target.preimage continuous_snd)
    (hclosed.isOpen_compl.preimage continuous_snd)

/-- The bundled, jointly continuous extension. -/
noncomputable def map [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (K : Set X) (hK : IsCompact K)
    (hKs : K ⊆ e.source)
    (hfix : ∀ (s : S) (x : e.source), (x : X) ∉ K → H (s, x) = x) :
    C(S × Y, Y) :=
  ⟨extend e H, extend_continuous e H K hK hKs hfix⟩

theorem extend_id (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S)
    (hs : ∀ x : e.source, H (s, x) = x) (y : Y) :
    extend e H (s, y) = y := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy, hs]
    exact e.right_inv hy
  · exact extend_not_mem_target e H s y hy

/-- Fixed sets need not themselves be closed. -/
theorem extend_fixed (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (A : Set Y)
    (hfix : ∀ (s : S) (x : e.source), e x ∈ A → H (s, x) = x)
    (s : S) (y : Y) (hyA : y ∈ A) : extend e H (s, y) = y := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy]
    rw [hfix s ⟨e.symm y, e.map_target hy⟩ (by simpa only [e.right_inv hy] using hyA)]
    exact e.right_inv hy
  · exact extend_not_mem_target e H s y hy

/-- Any reflexive pointwise property transfers from chart conjugation. -/
theorem extend_rel (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (R : Y → Y → Prop)
    (hrefl : ∀ y, R y y)
    (hlocal : ∀ (s : S) (x : e.source), R (e x) (e (H (s, x))))
    (s : S) (y : Y) : R y (extend e H (s, y)) := by
  by_cases hy : y ∈ e.target
  · rw [extend_target e H s y hy]
    simpa only [e.right_inv hy] using hlocal s ⟨e.symm y, e.map_target hy⟩
  · rw [extend_not_mem_target e H s y hy]
    exact hrefl y

theorem extend_height_nonincrease (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : e.source), f (e (H (s, x))) ≤ f (e x))
    (s : S) (y : Y) : f (extend e H (s, y)) ≤ f y :=
  extend_rel e H (fun y z => f z ≤ f y) (fun _ => le_rfl) hlocal s y

theorem extend_height_zero (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : e.source), f (e x) = 0 → f (e (H (s, x))) = 0)
    (s : S) (y : Y) (hy : f y = 0) : f (extend e H (s, y)) = 0 :=
  extend_rel e H (fun y z => f y = 0 → f z = 0) (fun _ h => h) hlocal s y hy

/-- The endpoint carries the image of every local collapse region into the
specified global set. -/
theorem extend_endpoint (e : OpenPartialHomeomorph X Y)
    (H : C(S × e.source, e.source)) (s : S) (L : Set X) (hLs : L ⊆ e.source)
    (A : Set Y) (hlocal : ∀ x : e.source, (x : X) ∈ L → e (H (s, x)) ∈ A) :
    MapsTo (fun y => extend e H (s, y)) (e '' L) A := by
  rintro y ⟨x, hx, rfl⟩
  change extend e H (s, e x) ∈ A
  rw [extend_chart e H s ⟨x, hLs hx⟩]
  exact hlocal ⟨x, hLs hx⟩ hx

/-- A supported family starting at the identity gives an actual homotopy
to its continuous endpoint. -/
noncomputable def homotopy [T2Space Y] (e : OpenPartialHomeomorph X Y)
    (H : C(unitInterval × e.source, e.source)) (K : Set X) (hK : IsCompact K)
    (hKs : K ⊆ e.source)
    (hfix : ∀ (s : unitInterval) (x : e.source), (x : X) ∉ K → H (s, x) = x)
    (hzero : ∀ x : e.source, H (0, x) = x) :
    (ContinuousMap.id Y).Homotopy
      ⟨fun y => extend e H (1, y),
        (extend_continuous e H K hK hKs hfix).comp
          (continuous_const.prodMk continuous_id)⟩ where
  toFun := extend e H
  continuous_toFun := extend_continuous e H K hK hKs hfix
  map_zero_left := extend_id e H 0 hzero
  map_one_left _ := rfl

section OpenEmbedding

variable [Nonempty X]

private noncomputable def embeddingLocalMap (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) :
    C(S × (he.toOpenPartialHomeomorph e).source, (he.toOpenPartialHomeomorph e).source) where
  toFun p := ⟨H (p.1, p.2.1), mem_univ _⟩
  continuous_toFun :=
    (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Extend a continuous family through an open embedding. -/
noncomputable def embeddingExtend (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) : S × Y → Y :=
  extend (he.toOpenPartialHomeomorph e) (embeddingLocalMap e he H)

theorem embeddingExtend_chart (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (s : S) (x : X) :
    embeddingExtend e he H (s, e x) = e (H (s, x)) := by
  let x' : (he.toOpenPartialHomeomorph e).source :=
    ⟨x, mem_univ _⟩
  simpa only [embeddingExtend, embeddingLocalMap, ContinuousMap.coe_mk,
    he.toOpenPartialHomeomorph_apply e] using
    extend_chart (he.toOpenPartialHomeomorph e) (embeddingLocalMap e he H) s x'

theorem embeddingExtend_not_mem_range (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (s : S) (y : Y) (hy : y ∉ range e) :
    embeddingExtend e he H (s, y) = y := by
  exact extend_not_mem_target (he.toOpenPartialHomeomorph e) (embeddingLocalMap e he H)
    s y (by simpa only [he.toOpenPartialHomeomorph_target e] using hy)

theorem embeddingExtend_not_mem_image (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (K : Set X)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x)
    (s : S) (y : Y) (hyK : y ∉ e '' K) : embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H]
    rw [hfix s x (fun hx => hyK ⟨x, hx, rfl⟩)]
  · exact embeddingExtend_not_mem_range e he H s y hy

theorem embeddingExtend_continuous [T2Space Y] (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) :
    Continuous (embeddingExtend e he H) := by
  apply extend_continuous (he.toOpenPartialHomeomorph e) (embeddingLocalMap e he H)
    K hK
  · rw [he.toOpenPartialHomeomorph_source e]
    exact subset_univ K
  · intro s x hx
    exact Subtype.ext (hfix s x hx)

/-- The compactly supported open-embedding extension as a continuous map. -/
noncomputable def embeddingMap [T2Space Y] (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : S) (x : X), x ∉ K → H (s, x) = x) : C(S × Y, Y) :=
  ⟨embeddingExtend e he H, embeddingExtend_continuous e he H K hK hfix⟩

theorem embeddingExtend_id (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (s : S) (hs : ∀ x : X, H (s, x) = x) (y : Y) :
    embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hs]
  · exact embeddingExtend_not_mem_range e he H s y hy

theorem embeddingExtend_fixed (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (A : Set Y)
    (hfix : ∀ (s : S) (x : X), e x ∈ A → H (s, x) = x)
    (s : S) (y : Y) (hyA : y ∈ A) : embeddingExtend e he H (s, y) = y := by
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H, hfix s x hyA]
  · exact embeddingExtend_not_mem_range e he H s y hy

theorem embeddingExtend_rel (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (R : Y → Y → Prop) (hrefl : ∀ y, R y y)
    (hlocal : ∀ (s : S) (x : X), R (e x) (e (H (s, x))))
    (s : S) (y : Y) : R y (embeddingExtend e he H (s, y)) := by
  by_cases hy : y ∈ range e
  · obtain ⟨x, rfl⟩ := hy
    rw [embeddingExtend_chart e he H]
    exact hlocal s x
  · rw [embeddingExtend_not_mem_range e he H s y hy]
    exact hrefl y

theorem embeddingExtend_height_nonincrease (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : X), f (e (H (s, x))) ≤ f (e x))
    (s : S) (y : Y) : f (embeddingExtend e he H (s, y)) ≤ f y :=
  embeddingExtend_rel e he H (fun y z => f z ≤ f y) (fun _ => le_rfl) hlocal s y

theorem embeddingExtend_height_zero (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (f : Y → ℝ)
    (hlocal : ∀ (s : S) (x : X), f (e x) = 0 → f (e (H (s, x))) = 0)
    (s : S) (y : Y) (hy : f y = 0) : f (embeddingExtend e he H (s, y)) = 0 :=
  embeddingExtend_rel e he H (fun y z => f y = 0 → f z = 0)
    (fun _ h => h) hlocal s y hy

theorem embeddingExtend_endpoint (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(S × X, X)) (s : S) (L : Set X) (A : Set Y)
    (hlocal : ∀ x ∈ L, e (H (s, x)) ∈ A) :
    MapsTo (fun y => embeddingExtend e he H (s, y)) (e '' L) A := by
  rintro y ⟨x, hx, rfl⟩
  change embeddingExtend e he H (s, e x) ∈ A
  rw [embeddingExtend_chart e he H]
  exact hlocal x hx

/-- An explicit supported homotopy through an open embedding. -/
noncomputable def embeddingHomotopy [T2Space Y] (e : X → Y) (he : IsOpenEmbedding e)
    (H : C(unitInterval × X, X)) (K : Set X) (hK : IsCompact K)
    (hfix : ∀ (s : unitInterval) (x : X), x ∉ K → H (s, x) = x)
    (hzero : ∀ x : X, H (0, x) = x) :
    (ContinuousMap.id Y).Homotopy
      ⟨fun y => embeddingExtend e he H (1, y),
        (embeddingExtend_continuous e he H K hK hfix).comp
          (continuous_const.prodMk continuous_id)⟩ where
  toFun := embeddingExtend e he H
  continuous_toFun := embeddingExtend_continuous e he H K hK hfix
  map_zero_left := embeddingExtend_id e he H 0 hzero
  map_one_left _ := rfl

end OpenEmbedding

end Wikipedia.HopfProblem.CuspPositiveRetraction.Supported
