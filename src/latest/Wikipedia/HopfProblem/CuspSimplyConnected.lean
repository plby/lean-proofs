import Wikipedia.HopfProblem.ToricSimplyConnected
import Wikipedia.HopfProblem.CuspTopology

/-!
# Simple connectivity of the cusp tube

Corollary 4.8 of `tex/s6.tex` asserts that the actual small tube in the toric
space is simply connected. Its affine pieces are star-shaped. Their
intersections are path-connected: each contains the dense punctured tube,
which is the exponential image of a convex half-space. Thus the assertion
can be proved directly on the open chart cover, without assuming the
fundamental group of a toric variety or a deformation-retraction theorem.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricFan.Triangle ToricSpace

theorem affineTube_isOpen (ε : ℝ) : IsOpen (affineTube ε) :=
  isOpen_lt Triangle.time_holomorphic.continuous.norm continuous_const

theorem affineTube_isSimplyConnected {ε : ℝ} (hε : 0 < ε) :
    IsSimplyConnected (affineTube ε) := by
  let := (affineTube_starConvex ε).contractibleSpace
    (show (affineTube ε).Nonempty from
      ⟨0, by simpa [affineTube, Triangle.time] using hε⟩)
  exact SimplyConnectedSpace.ofContractible _

/-- The inverse image of the punctured tube under componentwise exponential. -/
def logarithmicTube (ε : ℝ) : Set (CoordinateSpace 3) :=
  {z | (z 0 + z 1 + z 2).re < Real.log ε}

theorem logarithmicTube_convex (ε : ℝ) : Convex ℝ (logarithmicTube ε) := by
  apply convex_halfSpace_lt
  constructor
  · intro z w
    simp only [Pi.add_apply, Complex.add_re]
    ring
  · intro r z
    simp only [Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring

theorem logarithmicTube_nonempty (ε : ℝ) : (logarithmicTube ε).Nonempty := by
  refine ⟨![((Real.log ε - 1 : ℝ) : ℂ), 0, 0], ?_⟩
  simp [logarithmicTube]

theorem norm_time_coordinateExp (z : CoordinateSpace 3) :
    ‖Triangle.time (coordinateExp z)‖ = Real.exp (z 0 + z 1 + z 2).re := by
  simp only [Triangle.time, coordinateExp, ← Complex.exp_add, Complex.norm_exp]

theorem coordinateExp_mem_affineTube_iff {ε : ℝ} (hε : 0 < ε)
    (z : CoordinateSpace 3) :
    coordinateExp z ∈ affineTube ε ↔ z ∈ logarithmicTube ε := by
  change ‖Triangle.time (coordinateExp z)‖ < ε ↔
    (z 0 + z 1 + z 2).re < Real.log ε
  rw [norm_time_coordinateExp]
  exact (Real.lt_log_iff_exp_lt hε).symm

theorem coordinateExp_image_logarithmicTube {ε : ℝ} (hε : 0 < ε) :
    coordinateExp '' logarithmicTube ε = torus ∩ affineTube ε := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun j => Complex.exp_ne_zero _,
      (coordinateExp_mem_affineTube_iff hε w).mpr hw⟩
  · rintro ⟨hzT, hz⟩
    obtain ⟨w, rfl⟩ := range_coordinateExp.symm ▸ hzT
    exact ⟨w, (coordinateExp_mem_affineTube_iff hε w).mp hz, rfl⟩

theorem torus_inter_affineTube_isPathConnected {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected (torus ∩ affineTube ε) := by
  rw [← coordinateExp_image_logarithmicTube hε]
  exact ((logarithmicTube_convex ε).isPathConnected (logarithmicTube_nonempty ε)).image
    coordinateExp_continuous

theorem domain_inter_affineTube_isPathConnected (A : Matrix (Fin 3) (Fin 3) ℤ)
    {ε : ℝ} (hε : 0 < ε) : IsPathConnected (domain A ∩ affineTube ε) := by
  apply ((domain_open A).inter (affineTube_isOpen ε)).isConnected_iff_isPathConnected.mp
  apply (torus_inter_affineTube_isPathConnected hε).isConnected.subset_closure
  · exact fun _ hz => ⟨torus_subset_domain A hz.1, hz.2⟩
  · intro z hz
    simpa only [inter_comm] using
      (torus_dense.open_subset_closure_inter (affineTube_isOpen ε) hz.2)

/-- An affine tube chart stays inside the actual global tube. -/
theorem inclusion_affineTube_subset (s : Triangle) (ε : ℝ) :
    inclusion s '' affineTube ε ⊆ (tubeOpen (disc ε) : Set Space) := by
  rw [tube_eq_union]
  exact subset_iUnion (fun t => ToricSpace.inclusion t '' affineTube ε) s

theorem inclusion_affineTube_isOpen (s : Triangle) (ε : ℝ) :
    IsOpen (inclusion s '' affineTube ε) :=
  (inclusion_openEmbedding s).isOpenMap _ (affineTube_isOpen ε)

theorem inclusion_affineTube_isSimplyConnected (s : Triangle) {ε : ℝ} (hε : 0 < ε) :
    IsSimplyConnected (inclusion s '' affineTube ε) :=
  (inclusion_openEmbedding s).isEmbedding.isSimplyConnected_image.mpr
    (affineTube_isSimplyConnected hε)

theorem inclusion_affineTubes_inter (s t : Triangle) (ε : ℝ) :
    (inclusion s '' affineTube ε) ∩ (inclusion t '' affineTube ε) =
      inclusion s '' (domain (transition s t) ∩ affineTube ε) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, _, hw⟩⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    simpa only [chartChange_source] using ((inclusion_eq_iff s t z w).mp hw.symm).1
  · rintro ⟨z, ⟨hzD, hz⟩, rfl⟩
    have hzS : z ∈ (chartChange s t).source := by
      simpa only [chartChange_source] using hzD
    refine ⟨⟨z, hz, rfl⟩, chartChange s t z, ?_, ?_⟩
    · change ‖Triangle.time (chartChange s t z)‖ < ε
      have he : Triangle.time (chartChange s t z) = Triangle.time z :=
        chartChange_preserves_time s t hzS
      rw [he]
      exact hz
    · exact ((inclusion_eq_iff s t z _).mpr ⟨hzS, rfl⟩).symm

theorem inclusion_affineTubes_inter_isPathConnected (s t : Triangle)
    {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected ((inclusion s '' affineTube ε) ∩ (inclusion t '' affineTube ε)) := by
  rw [inclusion_affineTubes_inter]
  exact (domain_inter_affineTube_isPathConnected (transition s t) hε).image
    (inclusion_openEmbedding s).continuous

/-- The affine tube chart as an open subset of the global tube. -/
def affineTubeChart (ε : ℝ) (s : Triangle) : Set (Tube (disc ε)) :=
  Subtype.val ⁻¹' (inclusion s '' affineTube ε)

theorem affineTubeChart_isOpen (ε : ℝ) (s : Triangle) :
    IsOpen (affineTubeChart ε s) :=
  (inclusion_affineTube_isOpen s ε).preimage continuous_subtype_val

theorem affineTubeChart_isSimplyConnected {ε : ℝ} (hε : 0 < ε) (s : Triangle) :
    IsSimplyConnected (affineTubeChart ε s) := by
  apply IsEmbedding.subtypeVal.isSimplyConnected_image.mp
  have he : (Subtype.val : Tube (disc ε) → Space) '' affineTubeChart ε s =
      inclusion s '' affineTube ε := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, inclusion_affineTube_subset s ε hx⟩, hx, rfl⟩
  rw [he]
  exact inclusion_affineTube_isSimplyConnected s hε

theorem affineTubeCharts_inter_isPathConnected {ε : ℝ} (hε : 0 < ε)
    (s t : Triangle) :
    IsPathConnected (affineTubeChart ε s ∩ affineTubeChart ε t) := by
  change IsPathConnected ((Subtype.val : Tube (disc ε) → Space) ⁻¹'
    ((inclusion s '' affineTube ε) ∩ (inclusion t '' affineTube ε)))
  exact (inclusion_affineTubes_inter_isPathConnected s t hε).preimage_coe
    (inter_subset_left.trans (inclusion_affineTube_subset s ε))

theorem affineTubeCharts_cover (ε : ℝ) :
    ⋃ s : Triangle, affineTubeChart ε s = univ := by
  unfold affineTubeChart
  rw [← preimage_iUnion, ← tube_eq_union]
  ext x
  simp

/-- The main assertion of Corollary 4.8: the actual cusp tube, not merely its lattice presentation,
is simply connected. No upper bound on the positive tube radius is needed. -/
theorem tube_simplyConnected {ε : ℝ} (hε : 0 < ε) :
    SimplyConnectedSpace (Tube (disc ε)) := by
  obtain ⟨x, hx⟩ := tube_charts_common_point hε
  have hxTube : x ∈ (tubeOpen (disc ε) : Set Space) :=
    inclusion_affineTube_subset referenceTriangle ε (mem_iInter.mp hx referenceTriangle)
  exact simplyConnectedSpace_of_open_cover (affineTubeChart ε)
    (affineTubeChart_isOpen ε) (affineTubeCharts_cover ε)
    (affineTubeChart_isSimplyConnected hε) ⟨x, hxTube⟩
    (fun s => mem_iInter.mp hx s) (affineTubeCharts_inter_isPathConnected hε)

end Wikipedia.HopfProblem.CuspQuotient
