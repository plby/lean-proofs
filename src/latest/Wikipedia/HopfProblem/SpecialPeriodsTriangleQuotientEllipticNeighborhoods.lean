import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientStabilizers
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientCayleyBalls
import Wikipedia.HopfProblem.EllipticFamilies

/-!
# Precisely invariant elliptic neighbourhoods

Proper discontinuity and separation of the two actual elliptic orbits
produce round Cayley balls with no returning translate outside their
stabilizers.  These chosen neighbourhoods avoid the other elliptic orbit.
Their actual stabilizers are cyclic of orders three and four, and their
normalized complex coordinates intertwine the generators with the exact
rotations used in the elliptic fillings.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous triangleGeometricAction_continuous

/-- Exchange the two elliptic kinds. -/
def ellipticOtherKind : Elliptic.Kind → Elliptic.Kind
  | .three => .four
  | .four => .three

@[simp] theorem ellipticOtherKind_other (j : Elliptic.Kind) :
    ellipticOtherKind (ellipticOtherKind j) = j := by cases j <;> rfl

/-- The actual fixed point of the indicated elliptic generator. -/
def ellipticCenter : Elliptic.Kind → ℍ
  | .three => centerOne
  | .four => centerTwo

/-- The indicated generator in the actual abstract triangle group. -/
def ellipticGenerator : Elliptic.Kind → TriangleGroup
  | .three => triangleGenerator₁
  | .four => triangleGenerator₂

/-- The corresponding real determinant-one matrix. -/
def ellipticGeneratorSL : Elliptic.Kind → SL(2, ℝ)
  | .three => generatorOneSL
  | .four => generatorTwoSL

theorem ellipticGenerator_smul (j : Elliptic.Kind) (z : ℍ) :
    ellipticGenerator j • z = ellipticGeneratorSL j • z := by
  cases j
  · exact triangleGeometricRepresentation_generator₁_apply z
  · exact triangleGeometricRepresentation_generator₂_apply z

theorem ellipticGeneratorSL_fixed (j : Elliptic.Kind) :
    ellipticGeneratorSL j • ellipticCenter j = ellipticCenter j := by
  cases j
  · exact generatorOne_fix
  · exact generatorTwo_fix

/-- The distinguished point of the full, actual orbit quotient. -/
def ellipticOrbitCenter (j : Elliptic.Kind) : TriangleOrbitSpace :=
  triangleOrbitProjection (ellipticCenter j)

@[simp] theorem ellipticOrbitCenter_three :
    ellipticOrbitCenter .three = triangleOrbitCenterOne := rfl

@[simp] theorem ellipticOrbitCenter_four :
    ellipticOrbitCenter .four = triangleOrbitCenterTwo := rfl

theorem ellipticOrbitCenter_ne_other (j : Elliptic.Kind) :
    ellipticOrbitCenter j ≠ ellipticOrbitCenter (ellipticOtherKind j) := by
  cases j
  · exact triangleOrbitCenterOne_ne_centerTwo
  · exact triangleOrbitCenterOne_ne_centerTwo.symm

/-- The stabilizer for the named actual triangle action. -/
def ellipticStabilizer (j : Elliptic.Kind) : Subgroup TriangleGroup :=
  MulAction.stabilizer TriangleGroup (ellipticCenter j)

theorem mem_ellipticStabilizer_iff (j : Elliptic.Kind) (g : TriangleGroup) :
    g ∈ ellipticStabilizer j ↔
      ∃ n : ℕ, n < j.order ∧ g = ellipticGenerator j ^ n := by
  cases j
  · exact triangle_fixed_centerOne_iff g
  · exact triangle_fixed_centerTwo_iff g

theorem ellipticStabilizer_eq_zpowers (j : Elliptic.Kind) :
    ellipticStabilizer j = Subgroup.zpowers (ellipticGenerator j) := by
  cases j
  · exact triangle_stabilizer_centerOne
  · exact triangle_stabilizer_centerTwo

theorem ellipticGenerator_order (j : Elliptic.Kind) :
    orderOf (ellipticGenerator j) = j.order := by
  cases j
  · exact triangleGenerator₁_order
  · exact triangleGenerator₂_order

theorem ellipticGenerator_mem_stabilizer (j : Elliptic.Kind) :
    ellipticGenerator j ∈ ellipticStabilizer j := by
  change ellipticGenerator j • ellipticCenter j = ellipticCenter j
  rw [ellipticGenerator_smul, ellipticGeneratorSL_fixed]

/-- The actual stabilizer generator, not merely an abstract cyclic symbol. -/
def ellipticStabilizerGenerator (j : Elliptic.Kind) : ellipticStabilizer j :=
  ⟨ellipticGenerator j, ellipticGenerator_mem_stabilizer j⟩

@[simp] theorem ellipticStabilizerGenerator_val (j : Elliptic.Kind) :
    (ellipticStabilizerGenerator j : TriangleGroup) = ellipticGenerator j := rfl

theorem ellipticStabilizerGenerator_order (j : Elliptic.Kind) :
    orderOf (ellipticStabilizerGenerator j) = j.order := by
  rw [← orderOf_injective (ellipticStabilizer j).subtype Subtype.val_injective]
  exact ellipticGenerator_order j

theorem ellipticStabilizerGenerator_pow_order (j : Elliptic.Kind) :
    ellipticStabilizerGenerator j ^ j.order = 1 := by
  rw [← ellipticStabilizerGenerator_order]
  exact pow_orderOf_eq_one _

/-- Every element of the actual stabilizer is one of the indicated
bounded nonnegative powers of its distinguished generator. -/
theorem ellipticStabilizer_eq_generator_pow (j : Elliptic.Kind) (g : ellipticStabilizer j) :
    ∃ n : ℕ, n < j.order ∧ g = ellipticStabilizerGenerator j ^ n := by
  obtain ⟨n, hn, hg⟩ := (mem_ellipticStabilizer_iff j g).mp g.property
  exact ⟨n, hn, Subtype.ext hg⟩

instance ellipticStabilizer_finite (j : Elliptic.Kind) : Finite (ellipticStabilizer j) := by
  apply Finite.of_surjective (fun n : Fin j.order => ellipticStabilizerGenerator j ^ n.val)
  intro g
  obtain ⟨n, hn, rfl⟩ := ellipticStabilizer_eq_generator_pow j g
  exact ⟨⟨n, hn⟩, rfl⟩

/-- The open complement of the other actual elliptic orbit upstairs. -/
def ellipticOtherOrbitComplement (j : Elliptic.Kind) : Opens ℍ :=
  ⟨{z | triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j)},
    isOpen_ne_fun triangleOrbitProjection_continuous continuous_const⟩

theorem ellipticCenter_mem_otherOrbitComplement (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticOtherOrbitComplement j := ellipticOrbitCenter_ne_other j

/-- Actual proper discontinuity produces a round precisely invariant
neighbourhood which avoids the other elliptic orbit. -/
theorem exists_ellipticNeighborhoodRadius (j : Elliptic.Kind) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      (∀ g : TriangleGroup,
        (((g • ·) '' (cayleyBall (ellipticCenter j) r : Set ℍ)) ∩
          cayleyBall (ellipticCenter j) r).Nonempty → g ∈ ellipticStabilizer j) ∧
      (cayleyBall (ellipticCenter j) r : Set ℍ) ⊆ ellipticOtherOrbitComplement j := by
  obtain ⟨U, hU, hret⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self TriangleGroup (ellipticCenter j)
  have hV := (ellipticOtherOrbitComplement j).isOpen.mem_nhds
    (ellipticCenter_mem_otherOrbitComplement j)
  obtain ⟨r, hr, hr1, hball⟩ := exists_cayleyBall_subset (ellipticCenter j)
    (Filter.inter_mem hU hV)
  refine ⟨r, hr, hr1, ?_, fun z hz => (hball hz).2⟩
  intro g hg
  obtain ⟨z, ⟨w, hw, hgw⟩, hz⟩ := hg
  exact hret g ⟨z, ⟨w, (hball hw).1, hgw⟩, (hball hz).1⟩

/-- A radius chosen from the proved actual no-return neighbourhood. -/
def ellipticNeighborhoodRadius (j : Elliptic.Kind) : ℝ :=
  (exists_ellipticNeighborhoodRadius j).choose

theorem ellipticNeighborhoodRadius_pos (j : Elliptic.Kind) :
    0 < ellipticNeighborhoodRadius j := (exists_ellipticNeighborhoodRadius j).choose_spec.1

theorem ellipticNeighborhoodRadius_le_one (j : Elliptic.Kind) :
    ellipticNeighborhoodRadius j ≤ 1 := (exists_ellipticNeighborhoodRadius j).choose_spec.2.1

/-- The chosen actual round neighbourhood of the indicated centre. -/
def ellipticNeighborhood (j : Elliptic.Kind) : Opens ℍ :=
  cayleyBall (ellipticCenter j) (ellipticNeighborhoodRadius j)

theorem ellipticCenter_mem_neighborhood (j : Elliptic.Kind) :
    ellipticCenter j ∈ ellipticNeighborhood j :=
  (center_mem_cayleyBall _ _).mpr (ellipticNeighborhoodRadius_pos j)

theorem ellipticNeighborhood_mem_nhds (j : Elliptic.Kind) :
    (ellipticNeighborhood j : Set ℍ) ∈ 𝓝 (ellipticCenter j) :=
  (ellipticNeighborhood j).isOpen.mem_nhds (ellipticCenter_mem_neighborhood j)

/-- Every returning triangle element belongs to the actual stabilizer. -/
theorem ellipticNeighborhood_return (j : Elliptic.Kind) (g : TriangleGroup)
    (hret : (((g • ·) '' (ellipticNeighborhood j : Set ℍ)) ∩
      ellipticNeighborhood j).Nonempty) : g ∈ ellipticStabilizer j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.1 g hret

theorem ellipticNeighborhood_subset_otherOrbitComplement (j : Elliptic.Kind) :
    (ellipticNeighborhood j : Set ℍ) ⊆ ellipticOtherOrbitComplement j :=
  (exists_ellipticNeighborhoodRadius j).choose_spec.2.2.2

/-- The chosen neighbourhood has no point in the other elliptic orbit. -/
theorem ellipticNeighborhood_avoids_other (j : Elliptic.Kind) (z : ℍ)
    (hz : z ∈ ellipticNeighborhood j) :
    triangleOrbitProjection z ≠ ellipticOrbitCenter (ellipticOtherKind j) :=
  ellipticNeighborhood_subset_otherOrbitComplement j hz

/-- Any actual stabilizer element preserves every centred Cayley ball. -/
theorem ellipticStabilizer_cayleyBall_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (r : ℝ) (z : ℍ) :
    (g : TriangleGroup) • z ∈ cayleyBall (ellipticCenter j) r ↔
      z ∈ cayleyBall (ellipticCenter j) r := by
  have hfix : (triangleMatrixLift g : SL(2, ℝ)) • ellipticCenter j = ellipticCenter j :=
    (triangleMatrixLift_smul g _).trans g.property
  rw [← triangleMatrixLift_smul]
  exact smul_mem_cayleyBall_iff (triangleMatrixLift g) (ellipticCenter j) z r hfix

theorem ellipticNeighborhood_invariant (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ℍ) :
    (g : TriangleGroup) • z ∈ ellipticNeighborhood j ↔ z ∈ ellipticNeighborhood j :=
  ellipticStabilizer_cayleyBall_invariant j g _ z

theorem ellipticNeighborhood_mapsTo (j : Elliptic.Kind) (g : ellipticStabilizer j) :
    MapsTo (fun z : ℍ => (g : TriangleGroup) • z)
      (ellipticNeighborhood j) (ellipticNeighborhood j) :=
  fun z hz => (ellipticNeighborhood_invariant j g z).mpr hz

/-- The literal restricted stabilizer action on the chosen neighbourhood. -/
@[instance_reducible] def ellipticNeighborhoodAction (j : Elliptic.Kind) :
    MulAction (ellipticStabilizer j) (ellipticNeighborhood j) :=
  LocalOrbitQuotient.restrictedAction (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

@[simp] theorem ellipticNeighborhood_smul_val (j : Elliptic.Kind)
    (g : ellipticStabilizer j) (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ((g • z : ellipticNeighborhood j) : ℍ) = (g : TriangleGroup) • (z : ℍ) := rfl

theorem ellipticNeighborhood_continuousConstSMul (j : Elliptic.Kind) :
    letI := ellipticNeighborhoodAction j
    ContinuousConstSMul (ellipticStabilizer j) (ellipticNeighborhood j) :=
  LocalOrbitQuotient.restricted_continuousConstSMul (ellipticStabilizer j)
    (ellipticNeighborhood j) (ellipticNeighborhood_mapsTo j)

/-- Every element of the actual restricted stabilizer action is holomorphic. -/
theorem ellipticNeighborhood_action_holomorphic (j : Elliptic.Kind)
    (g : ellipticStabilizer j) :
    letI := ellipticNeighborhoodAction j
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ellipticNeighborhood j => g • z) := by
  let := ellipticNeighborhoodAction j
  have hc := (triangleGeometricRepresentation_holomorphic (g : TriangleGroup)).comp
    (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω) (U := ellipticNeighborhood j))
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

/-- The actual centre as a point of its chosen open neighbourhood. -/
def ellipticNeighborhoodCenter (j : Elliptic.Kind) : ellipticNeighborhood j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j⟩

/-- The normalized actual Cayley chart on the precisely invariant
neighbourhood, with values in the unit disc. -/
def ellipticNeighborhoodChart (j : Elliptic.Kind) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (ellipticNeighborhood j) Disc ω :=
  cayleyBallBiholomorph (ellipticCenter j) (ellipticNeighborhoodRadius j)
    (ellipticNeighborhoodRadius_pos j) (ellipticNeighborhoodRadius_le_one j)

@[simp] theorem ellipticNeighborhoodChart_val (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    (ellipticNeighborhoodChart j z : ℂ) =
      cayleyCoordinate (ellipticCenter j) z / (ellipticNeighborhoodRadius j : ℂ) := rfl

@[simp] theorem ellipticNeighborhoodChart_symm_val (j : Elliptic.Kind) (z : Disc) :
    ((ellipticNeighborhoodChart j).symm z : ℍ) = fromDisc (ellipticCenter j)
      (cayleyBallDiscScale (ellipticNeighborhoodRadius j)
        (ellipticNeighborhoodRadius_pos j) (ellipticNeighborhoodRadius_le_one j) z) := rfl

@[simp] theorem ellipticNeighborhoodChart_center (j : Elliptic.Kind) :
    ellipticNeighborhoodChart j (ellipticNeighborhoodCenter j) = discZero :=
  cayleyBallBiholomorph_center _ _ _ _

/-- The actual stabilizer generator becomes exactly the base rotation
used by the corresponding elliptic family. -/
theorem ellipticNeighborhoodChart_generator (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ellipticNeighborhoodChart j (ellipticStabilizerGenerator j • z) =
      Elliptic.familyRotation j (ellipticNeighborhoodChart j z) := by
  let := ellipticNeighborhoodAction j
  apply Subtype.ext
  change cayleyCoordinate (ellipticCenter j) (ellipticGenerator j • (z : ℍ)) /
      (ellipticNeighborhoodRadius j : ℂ) = _
  rw [ellipticGenerator_smul]
  cases j
  · change cayleyCoordinate centerOne (generatorOneSL • (z : ℍ)) /
      (ellipticNeighborhoodRadius .three : ℂ) =
      -rho * (cayleyCoordinate centerOne z / (ellipticNeighborhoodRadius .three : ℂ))
    rw [generatorOne_cayley, mul_div_assoc]
  · change cayleyCoordinate centerTwo (generatorTwoSL • (z : ℍ)) /
      (ellipticNeighborhoodRadius .four : ℂ) =
      -Complex.I * (cayleyCoordinate centerTwo z / (ellipticNeighborhoodRadius .four : ℂ))
    rw [generatorTwo_cayley, mul_div_assoc]

/-- The full bounded-power stabilizer action is conjugate to the
corresponding iterated disc rotation. -/
theorem ellipticNeighborhoodChart_generator_pow (j : Elliptic.Kind) (n : ℕ)
    (z : ellipticNeighborhood j) :
    letI := ellipticNeighborhoodAction j
    ellipticNeighborhoodChart j (ellipticStabilizerGenerator j ^ n • z) =
      (Elliptic.familyRotation j)^[n] (ellipticNeighborhoodChart j z) := by
  let := ellipticNeighborhoodAction j
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ellipticNeighborhoodChart_generator,
      ih, Function.iterate_succ_apply']

/-- In the chosen neighbourhood the central global orbit has exactly
one representative: the actual elliptic centre. -/
theorem ellipticNeighborhood_projection_eq_center_iff (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    triangleOrbitProjection z = ellipticOrbitCenter j ↔ z = ellipticNeighborhoodCenter j := by
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff z (ellipticCenter j)).mp hz
    have hgH : g ∈ ellipticStabilizer j :=
      ellipticNeighborhood_return j g ⟨z, ⟨ellipticCenter j,
        ellipticCenter_mem_neighborhood j, hg⟩, z.property⟩
    apply Subtype.ext
    exact hg.symm.trans hgH
  · rintro rfl
    rfl

/-- The literal subgroup orbit space on the chosen open neighbourhood. -/
abbrev EllipticNeighborhoodQuotient (j : Elliptic.Kind) :=
  LocalOrbitQuotient.LocalQuotient (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j)

/-- The actual image of the elliptic neighbourhood in the full triangle quotient. -/
def ellipticNeighborhoodImage (j : Elliptic.Kind) : Opens TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := TriangleGroup) (ellipticNeighborhood j)

/-- The local-to-global quotient homeomorphism has all its inputs
discharged for the chosen actual elliptic neighbourhood. -/
def ellipticNeighborhoodQuotientHomeomorph (j : Elliptic.Kind) :
    EllipticNeighborhoodQuotient j ≃ₜ ellipticNeighborhoodImage j :=
  LocalOrbitQuotient.localHomeomorph (ellipticStabilizer j) (ellipticNeighborhood j)
    (ellipticNeighborhood_mapsTo j) (ellipticNeighborhood_return j)

@[simp] theorem ellipticNeighborhoodQuotientHomeomorph_mk_val (j : Elliptic.Kind)
    (z : ellipticNeighborhood j) :
    (ellipticNeighborhoodQuotientHomeomorph j
      (LocalOrbitQuotient.localProjection (ellipticStabilizer j) (ellipticNeighborhood j)
        (ellipticNeighborhood_mapsTo j) z) : TriangleOrbitSpace) =
      triangleOrbitProjection z := rfl

theorem ellipticOrbitCenter_mem_neighborhoodImage (j : Elliptic.Kind) :
    ellipticOrbitCenter j ∈ ellipticNeighborhoodImage j :=
  ⟨ellipticCenter j, ellipticCenter_mem_neighborhood j, rfl⟩

theorem ellipticOtherOrbitCenter_not_mem_neighborhoodImage (j : Elliptic.Kind) :
    ellipticOrbitCenter (ellipticOtherKind j) ∉ ellipticNeighborhoodImage j := by
  rintro ⟨z, hz, he⟩
  exact ellipticNeighborhood_avoids_other j z hz he

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
