import Wikipedia.HopfProblem.CuspBoundaryIdentifications
import Wikipedia.HopfProblem.ToricDoubleLocus

/-!
# The three double-curve loci

The images of the three positive boundary curves of `E₀` are precisely the
locus of branch count at least two. Their pairwise intersections are exactly
the two triple points. These are actual closed subsets of the cusp quotient;
their analytic identification with projective lines is not assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def edgeDirectionLocus (i : Fin 3) : Set Space :=
  {x | ∃ v ∈ branchVertices x, v + edgeDirection i ∈ branchVertices x}

theorem edgeDirectionLocus_preimage (s : Triangle) (i : Fin 3) :
    inclusion s ⁻¹' edgeDirectionLocus i =
      ⋂ j : Fin 3, {z | j ≠ s.axisIndex i → z j = 0} := by
  ext z
  change (∃ v ∈ branchVertices (inclusion s z),
    v + edgeDirection i ∈ branchVertices (inclusion s z)) ↔ _
  rw [branchVertices_inclusion, chartBranches_edge_axis]
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]

theorem edgeDirectionLocus_isClosed (i : Fin 3) : IsClosed (edgeDirectionLocus i) := by
  rw [← isOpen_compl_iff, gluing.isOpen_iff]
  change ∀ s : Triangle, IsOpen (inclusion s ⁻¹' (edgeDirectionLocus i)ᶜ)
  intro s
  rw [Set.preimage_compl, isOpen_compl_iff, edgeDirectionLocus_preimage]
  apply isClosed_iInter
  intro j
  by_cases hj : j = s.axisIndex i
  · simp [hj]
  · simpa [hj] using
      (isClosed_eq (continuous_apply j) continuous_const :
        IsClosed {z : CoordinateSpace 3 | z j = 0})

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

def doubleCurve (i : Fin 3) : Set (QuotientSpace C ε) :=
  componentProjection C ε hε '' componentBoundary (edgeDirection i)

theorem doubleCurve_subset_central (i : Fin 3) : doubleCurve C ε hε i ⊆ projection C ε ⁻¹' {0} := by
  rintro _ ⟨y, _, rfl⟩
  exact projection_componentProjection C ε hε y

@[simp] theorem branchCount_componentProjection (x : rayDivisor 0) :
    branchCount C ε (componentProjection C ε hε x) = ToricSpace.branchCount (x : Space) := rfl

theorem mem_doubleCurve_quotientMap (a : Tube (disc ε)) (i : Fin 3) :
    quotientMap C ε a ∈ doubleCurve C ε hε i ↔
      ∃ v ∈ branchVertices (a : Space), v + edgeDirection i ∈ branchVertices (a : Space) := by
  let := tubeAction C (disc ε)
  constructor
  · rintro ⟨y, hy, he⟩
    have horb := Quotient.exact he
    change componentLift ε hε y ∈ MulAction.orbit LatticeGroup a at horb
    obtain ⟨g, hg⟩ := horb
    have hg' : twistedTranslate C g.toAdd (a : Space) = (y : Space) := congrArg Subtype.val hg
    let v : Fin 2 → ℤ := -cuspVector g.toAdd
    have hzero : (a : Space) ∈ rayDivisor v := by
      have h := (twistedTranslate_mem_rayDivisor C g.toAdd 0 a).mp (by rw [hg']; exact y.2)
      simpa only [zero_sub] using h
    have hedge : (a : Space) ∈ rayDivisor (edgeDirection i - cuspVector g.toAdd) :=
      (twistedTranslate_mem_rayDivisor C g.toAdd (edgeDirection i) a).mp (by rw [hg']; exact hy)
    refine ⟨v, hzero, ?_⟩
    have hv : v + edgeDirection i = edgeDirection i - cuspVector g.toAdd := by
      dsimp [v]
      abel
    rw [hv]
    exact hedge
  · rintro ⟨v, hv, hw⟩
    let y := branchRepresentative C ε a ⟨v, hv⟩
    have hy : (y : Space) ∈ rayDivisor (edgeDirection i) := by
      change twistedTranslate C (cuspVector v) (a : Space) ∈ rayDivisor (edgeDirection i)
      rw [twistedTranslate_mem_rayDivisor, cuspVector_cuspVector, sub_neg_eq_add, add_comm]
      exact hw
    exact ⟨y, hy, componentProjection_branchRepresentative C ε hε a ⟨v, hv⟩⟩

theorem mem_doubleCurve_centralChartMap (s : Triangle) (z : centralAffine) (i : Fin 3) :
    centralChartMap C ε hε s z ∈ doubleCurve C ε hε i ↔
      ∀ j : Fin 3, j ≠ s.axisIndex i → (z : CoordinateSpace 3) j = 0 := by
  change quotientMap C ε (centralLift ε hε s z) ∈ doubleCurve C ε hε i ↔ _
  rw [mem_doubleCurve_quotientMap]
  change (∃ v ∈ branchVertices (inclusion s z),
    v + edgeDirection i ∈ branchVertices (inclusion s z)) ↔ _
  rw [branchVertices_inclusion]
  exact chartBranches_edge_axis s z i

theorem doubleCurve_isClosed (i : Fin 3) : IsClosed (doubleCurve C ε hε i) := by
  have hq : IsQuotientMap (quotientMap C ε) := isQuotientMap_quotient_mk'
  apply hq.isClosed_preimage.mp
  have he : quotientMap C ε ⁻¹' doubleCurve C ε hε i =
      (Subtype.val : Tube (disc ε) → Space) ⁻¹' edgeDirectionLocus i := by
    ext a
    exact mem_doubleCurve_quotientMap C ε hε a i
  rw [he]
  exact (edgeDirectionLocus_isClosed i).preimage continuous_subtype_val

theorem branchCount_ge_two_of_mem_doubleCurve (i : Fin 3) {x : QuotientSpace C ε}
    (hx : x ∈ doubleCurve C ε hε i) : 2 ≤ branchCount C ε x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [branchCount_componentProjection]
  exact (ToricSpace.branchCount_ge_two_iff (y : Space)).mpr
    ⟨0, edgeDirection i, (edgeDirection_ne_zero i).symm, y.2, hy⟩

theorem double_locus_eq_union : {x : QuotientSpace C ε | 2 ≤ branchCount C ε x} =
    ⋃ i : Fin 3, doubleCurve C ε hε i := by
  ext x
  constructor
  · induction x using Quotient.inductionOn with
    | h a =>
      intro ha
      obtain ⟨v, w, hne, hv, hw⟩ := (ToricSpace.branchCount_ge_two_iff (a : Space)).mp ha
      have hadj := (rayDivisor_inter_nonempty_iff v w hne).mp ⟨(a : Space), hv, hw⟩
      obtain ⟨i, hi | hi⟩ := hadj
      · apply Set.mem_iUnion.mpr
        refine ⟨i, (mem_doubleCurve_quotientMap C ε hε a i).mpr ⟨v, hv, ?_⟩⟩
        have he : w = v + edgeDirection i := (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
        rw [← he]
        exact hw
      · apply Set.mem_iUnion.mpr
        refine ⟨i, (mem_doubleCurve_quotientMap C ε hε a i).mpr ⟨w, hw, ?_⟩⟩
        have he : v = w + edgeDirection i := by
          ext j
          have h := congrFun hi j
          change w j - v j = -edgeDirection i j at h
          change v j = w j + edgeDirection i j
          omega
        rw [← he]
        exact hv
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact branchCount_ge_two_of_mem_doubleCurve C ε hε i hi

theorem doubleCurve_inter_eq_triple (i j : Fin 3) (hij : i ≠ j) :
    doubleCurve C ε hε i ∩ doubleCurve C ε hε j =
      {x : QuotientSpace C ε | branchCount C ε x = 3} := by
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    constructor
    · rintro ⟨hi, hj⟩
      have hi' := (mem_doubleCurve_quotientMap C ε hε a i).mp hi
      have hj' := (mem_doubleCurve_quotientMap C ε hε a j).mp hj
      obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (a : Space)
      rw [← hz, branchVertices_inclusion] at hi' hj'
      have hz0 := two_edge_directions_force_origin s z i j hij hi' hj'
      change ToricSpace.branchCount (a : Space) = 3
      rw [← hz, ToricSpace.branchCount_inclusion, hz0, zeroCount_zero]
    · intro hx
      have hx' : ToricSpace.branchCount (a : Space) = 3 := hx
      obtain ⟨s, hs⟩ := (ToricSpace.branchCount_eq_three (a : Space)).mp hx'
      constructor
      · change quotientMap C ε a ∈ doubleCurve C ε hε i
        rw [mem_doubleCurve_quotientMap, ← hs, branchVertices_inclusion]
        exact origin_has_edge_direction s i
      · change quotientMap C ε a ∈ doubleCurve C ε hε j
        rw [mem_doubleCurve_quotientMap, ← hs, branchVertices_inclusion]
        exact origin_has_edge_direction s j

theorem doubleCurve_inter_eq_pair (i j : Fin 3) (hij : i ≠ j) :
    doubleCurve C ε hε i ∩ doubleCurve C ε hε j =
      {lowerTriplePoint C ε hε, upperTriplePoint C ε hε} := by
  rw [doubleCurve_inter_eq_triple C ε hε i j hij, tripleStratum_eq C ε hε]

theorem lowerTriplePoint_mem_doubleCurve (i : Fin 3) :
    lowerTriplePoint C ε hε ∈ doubleCurve C ε hε i :=
  (mem_doubleCurve_centralChartMap C ε hε ⟨0, 0, false⟩ centralOrigin i).mpr (fun _ _ => rfl)

theorem upperTriplePoint_mem_doubleCurve (i : Fin 3) :
    upperTriplePoint C ε hε ∈ doubleCurve C ε hε i :=
  (mem_doubleCurve_centralChartMap C ε hε ⟨0, 0, true⟩ centralOrigin i).mpr (fun _ _ => rfl)

def doubleCurveSample (i : Fin 3) : centralAffine :=
  ⟨Pi.single (referenceTriangle.axisIndex i) 1, by
    fin_cases i <;> simp [centralAffine, Triangle.time, referenceTriangle, axisIndex]⟩

theorem doubleCurveSample_mem (i : Fin 3) :
    centralChartMap C ε hε referenceTriangle (doubleCurveSample i) ∈ doubleCurve C ε hε i := by
  apply (mem_doubleCurve_centralChartMap C ε hε referenceTriangle (doubleCurveSample i) i).mpr
  intro j hj
  simp [doubleCurveSample, hj]

theorem doubleCurveSample_not_triple (i : Fin 3) :
    branchCount C ε (centralChartMap C ε hε referenceTriangle (doubleCurveSample i)) ≠ 3 := by
  intro h
  rw [branchCount_centralChartMap] at h
  have hz := (zeroCount_eq_three (doubleCurveSample i : CoordinateSpace 3)).mp h
  have he := congrFun hz (referenceTriangle.axisIndex i)
  simp [doubleCurveSample] at he

theorem doubleCurves_injective : Function.Injective (doubleCurve C ε hε) := by
  intro i j he
  by_contra hij
  have hm : centralChartMap C ε hε referenceTriangle (doubleCurveSample i) ∈
      doubleCurve C ε hε i ∩ doubleCurve C ε hε j :=
    ⟨doubleCurveSample_mem C ε hε i, by rw [← he]; exact doubleCurveSample_mem C ε hε i⟩
  rw [doubleCurve_inter_eq_triple C ε hε i j hij] at hm
  exact doubleCurveSample_not_triple C ε hε i hm

theorem doubleCurve_compact (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (i : Fin 3) : IsCompact (doubleCurve C ε hε i) :=
  (central_fibre_compact C ε hε hε1 hC hR).of_isClosed_subset
    (doubleCurve_isClosed C ε hε i) (doubleCurve_subset_central C ε hε i)

end Wikipedia.HopfProblem.CuspQuotient
