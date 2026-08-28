import Wikipedia.HopfProblem.CuspTopology

/-!
# The central fibre of the cusp quotient

The central affine charts are connected. Lattice translations identify
their origins with the origins of the two reference triangles, whose
central charts overlap. Consequently the actual central quotient fibre
is connected, in addition to the compactness established by properness.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

def centralAffine : Set (CoordinateSpace 3) := {z | Triangle.time z = 0}

def centralOrigin : centralAffine := ⟨0, by simp [centralAffine, Triangle.time]⟩

theorem centralAffine_starConvex : StarConvex ℝ 0 centralAffine := by
  intro z hz a b _ _ _
  simp only [smul_zero, zero_add]
  change Triangle.time (b • z) = 0
  obtain h | h | h := (Triangle.central_fibre z).mp hz
  all_goals simp [Triangle.time, Pi.smul_apply, h]

instance centralAffine_connected : ConnectedSpace centralAffine :=
  isConnected_iff_connectedSpace.mp
    ((centralAffine_starConvex.isPathConnected centralOrigin.2).isConnected)

def centralLift (ε : ℝ) (hε : 0 < ε) (s : Triangle) (z : centralAffine) : Tube (disc ε) :=
  ⟨inclusion s z, by
    change time (inclusion s z) ∈ Metric.ball 0 ε
    rw [time_inclusion, z.2]
    simpa using hε⟩

theorem centralLift_continuous (ε : ℝ) (hε : 0 < ε) (s : Triangle) :
    Continuous (centralLift ε hε s) :=
  ((inclusion_openEmbedding s).continuous.comp continuous_subtype_val).subtype_mk _

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

def centralChartMap (s : Triangle) : centralAffine → QuotientSpace C ε :=
  quotientMap C ε ∘ centralLift ε hε s

theorem centralChartMap_continuous (s : Triangle) : Continuous (centralChartMap C ε hε s) :=
  (quotientMap_continuous C ε).comp (centralLift_continuous ε hε s)

theorem centralChartMap_range_connected (s : Triangle) :
    IsConnected (range (centralChartMap C ε hε s)) :=
  isConnected_range (centralChartMap_continuous C ε hε s)

@[simp] theorem projection_centralChartMap (s : Triangle) (z : centralAffine) :
    projection C ε (centralChartMap C ε hε s z) = 0 := by
  change time (inclusion s z) = 0
  rw [time_inclusion, z.2]

theorem centralChartMap_origin_shift (s : Triangle) (v : Fin 2 → ℤ) :
    centralChartMap C ε hε (s.shift (cuspVector v)) centralOrigin =
      centralChartMap C ε hε s centralOrigin := by
  have he : tubeTranslate C (disc ε) v (centralLift ε hε s centralOrigin) =
      centralLift ε hε (s.shift (cuspVector v)) centralOrigin := by
    apply Subtype.ext
    simp [tubeTranslate, centralLift, centralOrigin, twistedTranslate,
      variableMultiplier, translate_inclusion, torusAction_inclusion, scale]
  exact (congrArg (quotientMap C ε) he).symm.trans
    (quotientMap_translate C ε v (centralLift ε hε s centralOrigin))

theorem centralChartMap_origin_reference (s : Triangle) :
    centralChartMap C ε hε s centralOrigin =
      centralChartMap C ε hε ⟨0, 0, s.upper⟩ centralOrigin := by
  let v : Fin 2 → ℤ := ![-s.b, s.a]
  have he : (⟨0, 0, s.upper⟩ : Triangle).shift (cuspVector v) = s := by
    ext <;> simp [Triangle.shift, cuspVector, v]
  simpa only [he] using centralChartMap_origin_shift C ε hε ⟨0, 0, s.upper⟩ v

theorem reference_central_overlap :
    inclusion (⟨0, 0, false⟩ : Triangle) ![1, 0, 0] =
      inclusion (⟨0, 0, true⟩ : Triangle) ![0, 0, 1] := by
  have hA : Triangle.transition ⟨0, 0, false⟩ ⟨0, 0, true⟩ =
      !![1, 1, 0; 1, 0, 1; -1, 0, 0] := by decide
  apply (inclusion_eq_iff _ _ _ _).mpr
  constructor
  · rw [Triangle.chartChange_source]
    intro i j hij
    rw [hA] at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    norm_num
  · change monomial (Triangle.transition _ _) _ = _
    rw [hA]
    ext i
    fin_cases i <;> norm_num [monomial, Fin.prod_univ_succ]

theorem reference_centralChartMap_overlap :
    (range (centralChartMap C ε hε ⟨0, 0, false⟩) ∩
      range (centralChartMap C ε hε ⟨0, 0, true⟩)).Nonempty := by
  let z : centralAffine := ⟨![1, 0, 0], by simp [centralAffine, Triangle.time]⟩
  let w : centralAffine := ⟨![0, 0, 1], by simp [centralAffine, Triangle.time]⟩
  refine ⟨centralChartMap C ε hε ⟨0, 0, false⟩ z, mem_range_self z, w, ?_⟩
  apply congrArg (quotientMap C ε)
  exact Subtype.ext reference_central_overlap.symm

theorem central_fibre_eq_union : projection C ε ⁻¹' {0} =
    ⋃ s : Triangle, range (centralChartMap C ε hε s) := by
  ext q
  constructor
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have hx0 : time (x : Space) = 0 := hx
      obtain ⟨s, z, he⟩ := inclusion_jointly_surjective (x : Space)
      have hz : z ∈ centralAffine := by
        change Triangle.time z = 0
        rw [← time_inclusion s z, he, hx0]
      refine mem_iUnion.mpr ⟨s, ⟨z, hz⟩, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext he
  · intro hq
    obtain ⟨s, z, rfl⟩ := mem_iUnion.mp hq
    exact projection_centralChartMap C ε hε s z

include hε in
theorem central_fibre_connected : IsConnected (projection C ε ⁻¹' {0}) := by
  let U := fun s : Triangle => range (centralChartMap C ε hε s)
  let R := U ⟨0, 0, false⟩ ∪ U ⟨0, 0, true⟩
  have hU (s : Triangle) : IsPreconnected (U s) :=
    (centralChartMap_range_connected C ε hε s).isPreconnected
  have hR : IsPreconnected R := IsPreconnected.union'
    (reference_centralChartMap_overlap C ε hε) (hU _) (hU _)
  have horigin (s : Triangle) : centralChartMap C ε hε s centralOrigin ∈ R := by
    rw [centralChartMap_origin_reference]
    cases hs : s.upper
    · exact Or.inl (mem_range_self _)
    · exact Or.inr (mem_range_self _)
  have hcommon : (⋂ s : Triangle, R ∪ U s).Nonempty := by
    refine ⟨centralChartMap C ε hε ⟨0, 0, false⟩ centralOrigin, mem_iInter.mpr fun s => ?_⟩
    exact Or.inl (Or.inl (mem_range_self _))
  have hpre : IsPreconnected (⋃ s : Triangle, R ∪ U s) :=
    isPreconnected_iUnion hcommon (fun s => IsPreconnected.union'
      ⟨centralChartMap C ε hε s centralOrigin, horigin s, mem_range_self _⟩ hR (hU s))
  have he : (⋃ s : Triangle, R ∪ U s) = ⋃ s : Triangle, U s := by
    apply subset_antisymm
    · intro q hq
      obtain ⟨s, hq⟩ := mem_iUnion.mp hq
      rcases hq with (hq | hq) | hq
      · exact mem_iUnion.mpr ⟨⟨0, 0, false⟩, hq⟩
      · exact mem_iUnion.mpr ⟨⟨0, 0, true⟩, hq⟩
      · exact mem_iUnion.mpr ⟨s, hq⟩
    · intro q hq
      obtain ⟨s, hq⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨s, Or.inr hq⟩
  rw [he] at hpre
  rw [central_fibre_eq_union C ε hε]
  exact ⟨⟨centralChartMap C ε hε ⟨0, 0, false⟩ centralOrigin,
    mem_iUnion.mpr ⟨⟨0, 0, false⟩, mem_range_self _⟩⟩, hpre⟩

include hε in
theorem central_fibre_compact (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : IsCompact (projection C ε ⁻¹' {0}) := by
  have he : projection C ε ⁻¹' {0} = baseMap C ε ⁻¹' {⟨0, by simpa [disc] using hε⟩} := by
    ext q
    simp [baseMap, Subtype.ext_iff]
  rw [he]
  exact fibre_compact C ε hε hε1 hC hR _

end Wikipedia.HopfProblem.CuspQuotient
