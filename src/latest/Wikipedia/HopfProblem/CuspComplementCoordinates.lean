import Wikipedia.HopfProblem.CuspProper
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCoordinates

/-!
# The finite native coordinate domain for the actual cusp cap

The compact representatives from `CuspProper` are parametrized by the original
98 toric charts with both lattice coordinates between minus three and three.
Every chart uses its literal closed unit polydisc and the original cubic time
bound. The map to the native cusp tube has exactly the previously constructed
representative set as its range.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspComplement.Coordinates

open ToricCharts ToricFan
open SpecialPeriods SpecialPeriods.Threefold VerticalAction

local notation "CD" => CuspGeometry.data
local notation "E₃" => CoordinateSpace 3

/-- The two triangles in each of the 49 original integral squares. -/
abbrev Index := Fin 7 × Fin 7 × Bool

/-- The exact original toric triangle indexed by its shifted lattice coordinates. -/
def triangle (i : Index) : Triangle :=
  ⟨(i.1 : ℤ) - 3, (i.2.1 : ℤ) - 3, i.2.2⟩

@[simp] theorem triangle_a (i : Index) : (triangle i).a = (i.1 : ℤ) - 3 := rfl

@[simp] theorem triangle_b (i : Index) : (triangle i).b = (i.2.1 : ℤ) - 3 := rfl

@[simp] theorem triangle_upper (i : Index) : (triangle i).upper = i.2.2 := rfl

theorem triangle_mem_boundedTriangles (i : Index) :
    triangle i ∈ ToricSpace.boundedTriangles := by
  have ha := i.1.isLt
  have hb := i.2.1.isLt
  change (-3 ≤ (i.1 : ℤ) - 3 ∧ (i.1 : ℤ) - 3 ≤ 3) ∧
    (-3 ≤ (i.2.1 : ℤ) - 3 ∧ (i.2.1 : ℤ) - 3 ≤ 3)
  omega

theorem exists_index_of_mem_boundedTriangles (s : Triangle)
    (hs : s ∈ ToricSpace.boundedTriangles) : ∃ i : Index, triangle i = s := by
  rcases hs with ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
  have ha7 : (s.a + 3).toNat < 7 := by omega
  have hb7 : (s.b + 3).toNat < 7 := by omega
  refine ⟨(⟨(s.a + 3).toNat, ha7⟩, ⟨(s.b + 3).toNat, hb7⟩, s.upper), ?_⟩
  apply Triangle.ext
  · change ((s.a + 3).toNat : ℤ) - 3 = s.a
    omega
  · change ((s.b + 3).toNat : ℤ) - 3 = s.b
    omega
  · rfl

/-- This finite index has exactly the triangle range used by the original properness proof. -/
theorem triangle_range : Set.range triangle = ToricSpace.boundedTriangles := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact triangle_mem_boundedTriangles i
  · exact exists_index_of_mem_boundedTriangles s

theorem triangle_injective : Function.Injective triangle := by
  intro i j h
  have ha := congrArg Triangle.a h
  have hb := congrArg Triangle.b h
  have hu := congrArg Triangle.upper h
  apply Prod.ext
  · apply Fin.ext
    simp only [triangle_a] at ha
    omega
  · apply Prod.ext
    · apply Fin.ext
      simp only [triangle_b] at hb
      omega
    · exact hu

theorem index_card : Fintype.card Index = 98 := by norm_num [Index]

/-- The literal native closed coordinate polydisc cut off by the original time. -/
abbrev CoordinateCap (η : ℝ) :=
  {z : E₃ // ‖z‖ ≤ 1 ∧ ‖Triangle.time z‖ ≤ η}

theorem coordinateCap_set_eq (η : ℝ) :
    {z : E₃ | ‖z‖ ≤ 1 ∧ ‖Triangle.time z‖ ≤ η} =
      Metric.closedBall (0 : E₃) 1 ∩
        Triangle.time ⁻¹' Metric.closedBall 0 η := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    Metric.mem_closedBall, dist_zero_right]

theorem coordinateCap_isCompact (η : ℝ) :
    IsCompact {z : E₃ | ‖z‖ ≤ 1 ∧ ‖Triangle.time z‖ ≤ η} := by
  rw [coordinateCap_set_eq]
  exact (isCompact_closedBall _ _).inter_right
    (Metric.isClosed_closedBall.preimage Triangle.time_holomorphic.continuous)

instance coordinateCap_compactSpace (η : ℝ) : CompactSpace (CoordinateCap η) :=
  isCompact_iff_compactSpace.mp (coordinateCap_isCompact η)

/-- Inclusion into the original open cusp coordinate domain, with no coordinate change. -/
def coordinateIntoDomain (η : ℝ) (hη : η < (CD).radius) (z : CoordinateCap η) :
    FixedCoordinates.Domain :=
  ⟨z, z.property.2.trans_lt hη⟩

@[simp] theorem coordinateIntoDomain_coe (η : ℝ) (hη : η < (CD).radius)
    (z : CoordinateCap η) :
    (coordinateIntoDomain η hη z : E₃) = z := rfl

theorem coordinateIntoDomain_continuous (η : ℝ) (hη : η < (CD).radius) :
    Continuous (coordinateIntoDomain η hη) :=
  continuous_subtype_val.subtype_mk (fun z => z.property.2.trans_lt hη)

/-- The original affine inclusions into the actual cusp tube, on a finite compact domain. -/
def toTube (η : ℝ) (hη : η < (CD).radius) (p : Index × CoordinateCap η) :
    ToricSpace.Tube (CuspQuotient.disc (CD).radius) :=
  FixedCoordinates.tubeMap (triangle p.1) (coordinateIntoDomain η hη p.2)

@[simp] theorem toTube_coe (η : ℝ) (hη : η < (CD).radius)
    (p : Index × CoordinateCap η) :
    (toTube η hη p : ToricSpace.Space) = ToricSpace.inclusion (triangle p.1) p.2 := rfl

theorem toTube_continuous (η : ℝ) (hη : η < (CD).radius) :
    Continuous (toTube η hη) := by
  apply continuous_prod_of_discrete_left.mpr
  intro i
  exact ((ToricSpace.inclusion_openEmbedding (triangle i)).continuous.comp
    continuous_subtype_val).subtype_mk (fun z => (toTube η hη (i, z)).property)

/-- The finite coordinate domain covers exactly the native compact tube representatives. -/
theorem range_toTube (η : ℝ) (hη : η < (CD).radius) :
    Set.range (toTube η hη) = CuspQuotient.tubeRepresentatives (CD).radius η := by
  ext x
  constructor
  · rintro ⟨⟨i, z⟩, rfl⟩
    change ToricSpace.inclusion (triangle i) (z : E₃) ∈
      CuspQuotient.compactRepresentatives η
    apply Set.mem_iUnion₂.mpr
    refine ⟨triangle i, triangle_mem_boundedTriangles i, (z : E₃), ?_, rfl⟩
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1
    · simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using z.property.2
  · intro hx
    change (x : ToricSpace.Space) ∈ CuspQuotient.compactRepresentatives η at hx
    obtain ⟨s, hs, z, hz, hzx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, rfl⟩ := exists_index_of_mem_boundedTriangles s hs
    have hcap : ‖z‖ ≤ 1 ∧ ‖Triangle.time z‖ ≤ η := by
      simpa only [Set.mem_inter_iff, Metric.mem_closedBall, Set.mem_preimage,
        dist_zero_right] using hz
    refine ⟨(i, ⟨z, hcap⟩), ?_⟩
    apply Subtype.ext
    exact hzx

theorem range_toTube_isCompact (η : ℝ) (hη : η < (CD).radius) :
    IsCompact (Set.range (toTube η hη)) :=
  isCompact_range (toTube_continuous η hη)

/-- The finite coordinate map into the unchanged glued threefold. -/
def toGlobal (η : ℝ) (hη : η < (CD).radius) (p : Index × CoordinateCap η) :
    Threefold.Space :=
  FixedCoordinates.globalMap (triangle p.1) (coordinateIntoDomain η hη p.2)

@[simp] theorem toGlobal_eq_native (η : ℝ) (hη : η < (CD).radius)
    (p : Index × CoordinateCap η) :
    toGlobal η hη p = CuspGeometry.inclusion
      (CuspQuotient.quotientMap (CD).correction (CD).radius (toTube η hη p)) := rfl

theorem toGlobal_continuous (η : ℝ) (hη : η < (CD).radius) :
    Continuous (toGlobal η hη) :=
  CuspGeometry.inclusion_continuous.comp
    ((CuspQuotient.quotientMap_continuous (CD).correction (CD).radius).comp
      (toTube_continuous η hη))

end Wikipedia.HopfProblem.CuspComplement.Coordinates
