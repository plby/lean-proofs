import ErdosProblems.Erdos633.FieldTilingRealization
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Original tiling vertices lie in the coefficient field

A coordinate outside the base field can be assigned any prescribed field
value by a linear retraction. But every such retraction produces an actual
tiling of the same bounded outer triangle. Its vertex coordinates therefore
remain bounded. These facts force the original coordinates into the field.
No additional geometric rigidity or positivity theorem is assumed.
-/

namespace Erdos633

theorem exists_field_retraction_prescribed (F : Subfield ℝ) (x : ℝ) (hx : x ∉ F)
    (y : F) : ∃ f : ℝ →ₗ[F] F, (∀ a : F, f (a : ℝ) = a) ∧ f x = y := by
  classical
  let S := Submodule.span F ({1} : Set ℝ)
  have hxS : x ∉ S := by
    intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have heq : (a : ℝ) = x := by
      change (a : ℝ) * 1 = x at ha
      simpa only [mul_one] using ha
    exact hx (heq ▸ a.property)
  obtain ⟨l, hlx, hlS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxS inferInstance
  have hl1 : l 1 = 0 := by
    have hmem : l 1 ∈ S.map l :=
      Submodule.mem_map.mpr ⟨1, Submodule.mem_span_singleton_self 1, rfl⟩
    simpa only [hlS, Submodule.mem_bot] using hmem
  have hla (a : F) : l (a : ℝ) = 0 := by
    rw [show (a : ℝ) = a • (1 : ℝ) by change (a : ℝ) = (a : ℝ) * 1; ring,
      l.map_smul, hl1, smul_zero]
  obtain ⟨g, hg, _⟩ := exists_field_retraction_injective_on (F := F) (E := ℝ) ∅
  let f : ℝ →ₗ[F] F := g + ((y - g x) / l x) • l
  refine ⟨f, ?_, ?_⟩
  · intro a
    change g (a : ℝ) + ((y - g x) / l x) • l (a : ℝ) = a
    rw [hla, smul_zero, add_zero]
    exact hg a
  · change g x + ((y - g x) / l x) • l x = y
    rw [smul_eq_mul, div_mul_cancel₀ _ hlx]
    ring

theorem mem_subfield_of_bounded_retractions (F : Subfield ℝ) (x C : ℝ)
    (h : ∀ f : ℝ →ₗ[F] F, (∀ a : F, f (a : ℝ) = a) → (f x : ℝ) ≤ C) : x ∈ F := by
  by_contra hx
  obtain ⟨n, hn⟩ := exists_nat_gt C
  obtain ⟨f, hf, hfx⟩ := exists_field_retraction_prescribed F x hx (n : F)
  have hb := h f hf
  rw [hfx] at hb
  exact (not_le_of_gt hn) (by simpa using hb)

theorem TriangleDissection.fieldCoordinateMap_vertex_mem
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (F : Subfield ℝ) (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a)
    (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F)
    (i : Fin N) (k : Fin 3) :
    fieldCoordinateMap F f ((T.tile i).vertex k) ∈ P.carrier := by
  let U := T.fieldRetract F f hf hP he
  have h := U.tile_subset i ((U.tile i).vertex_mem_carrier k)
  change ((T.tile i).fieldRetract F f).vertex k ∈ P.carrier at h
  rwa [(T.tile i).fieldRetract_vertexImage F f hf (he i) k] at h

/-- The conclusion concerns the original vertices, not merely a replacement
tiling with the same tile shapes. -/
theorem TriangleDissection.coordinatesIn_of_edgeVectors
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (F : Subfield ℝ) (hP : P.CoordinatesIn F)
    (he : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).edgeVector k ∈ complexCoordinateSubfield F) :
    ∀ i : Fin N, (T.tile i).CoordinatesIn F := by
  obtain ⟨C, hC⟩ := P.isCompact_carrier.isBounded.exists_norm_le
  intro i k
  have hbound (f : ℝ →ₗ[F] F) (hf : ∀ a : F, f (a : ℝ) = a) :
      ‖fieldCoordinateMap F f ((T.tile i).vertex k)‖ ≤ C :=
    hC _ (T.fieldCoordinateMap_vertex_mem F f hf hP he i k)
  constructor
  · apply mem_subfield_of_bounded_retractions F _ C
    intro f hf
    exact (Complex.re_le_norm _).trans (hbound f hf)
  · apply mem_subfield_of_bounded_retractions F _ C
    intro f hf
    exact (Complex.im_le_norm _).trans (hbound f hf)

theorem CongruentTiling.coefficient_field_vertices
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (F : Subfield ℝ)
    (ha : P.a ∈ complexCoordinateSubfield F)
    (hbase : P.unitEdgeVector 2 ∈ complexCoordinateSubfield F)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hc : R.sideLength 2 ∈ F) :
    P.CoordinatesIn F ∧ ∀ i : Fin N, (T.labelledTile i).CoordinatesIn F := by
  obtain ⟨hP, he⟩ := T.coefficient_field_edges F ha hbase hA hB hc
  exact ⟨hP, T.labelledDissection.coordinatesIn_of_edgeVectors F hP he⟩

end Erdos633
