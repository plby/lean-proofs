import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingMaps

/-!
# The full actual overlap of an elliptic filling and the regular family

The image of the punctured local family is exactly the inverse image of
the chosen elliptic base neighborhood.  The genuine triangle orbit
relation restricts to precisely the untwisted finite cyclic relation.
Consequently its actual quotient maps bijectively to the whole literal
regular-family overlap, not just to an unspecified germ or fibre.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.LogGauge TrianglePeriodFamily

variable (P : HolomorphicPeriodMap ℂ ℍ) (j : Kind)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The literal full preimage of the actual punctured elliptic base patch. -/
def regularOverlap : Opens (regularData P h₁ h₂).Space :=
  ⟨(regularData P h₁ h₂).projection ⁻¹'
      (regularBasePatch j : Set TriangleRegularQuotient),
    (regularBasePatch j).isOpen.preimage (regularData P h₁ h₂).projection_continuous⟩

@[simp] theorem regularOverlap_mem (y : (regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      (regularData P h₁ h₂).projection y ∈ regularBasePatch j := Iff.rfl

theorem regularMap_mem_overlap (x : FamilyStar (localPeriods P j)) :
    regularMap P j h₁ h₂ x ∈ regularOverlap P j h₁ h₂ := by
  rw [regularOverlap_mem, regularMap_base]
  exact baseQuotient_mem_regularBasePatch j ⟨x.1.1, x.2⟩

/-- Every torus point over every point of the entire chosen base patch
is represented by the punctured local family. -/
theorem regularMap_range :
    range (regularMap P j h₁ h₂) =
      (regularOverlap P j h₁ h₂ : Set (regularData P h₁ h₂).Space) := by
  let D := regularData P h₁ h₂
  let := D.totalAction
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact regularMap_mem_overlap P j h₁ h₂ x
  · intro hy
    obtain ⟨u, rfl⟩ := D.quotient_surjective y
    have hb : D.baseQuotient u.1 ∈ regularBasePatch j := hy
    have hz' : D.baseQuotient u.1 ∈ range (baseQuotient j) := by
      rw [baseQuotient_range]
      exact hb
    obtain ⟨z, hz⟩ := hz'
    have hbase : D.baseQuotient (localBase j z) = D.baseQuotient u.1 := hz
    obtain ⟨g, hg⟩ := (regularCovering P h₁ h₂).apply_eq_iff_mem_orbit.mp hbase
    let x : FamilyStar (localPeriods P j) :=
      ⟨(z.val, triangleTorusHomeomorph g u.2), z.property⟩
    refine ⟨x, ?_⟩
    change D.quotient (localTotalMap P j x) = D.quotient u
    apply (D.quotient_eq_iff _ _).mpr
    exact ⟨g, Prod.ext hg rfl⟩

/-- The no-return property of the actual elliptic neighborhood reduces
all global orbit identifications to bounded powers of its stabilizer
generator, hence to the exact zero-twist cyclic action. -/
theorem regularMap_eq_iff (x y : FamilyStar (localPeriods P j)) :
    letI := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
    regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y ↔
      ∃ g : CyclicGroup j, g • y = x := by
  let L := localData P h₁ h₂ j
  let D := regularData P h₁ h₂
  let := starAction L 0 (Matrix.mulVec_zero j.matrix)
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff (localTotalMap P j x)
      (localTotalMap P j y)).mp h
    have hb : g • localBase j ⟨y.1.1, y.2⟩ = localBase j ⟨x.1.1, x.2⟩ :=
      congrArg Prod.fst hg
    obtain ⟨n, hn, hgn, _⟩ := localBase_orbit_classification j g
      ⟨y.1.1, y.2⟩ ⟨x.1.1, x.2⟩ hb
    let c : CyclicGroup j := Multiplicative.ofAdd (n : ZMod j.order)
    refine ⟨c, localTotalMap_injective P j ?_⟩
    calc
      localTotalMap P j (c • y) =
          Triangle.ellipticGenerator j ^ n • localTotalMap P j y := by
        rw [localTotalMap_smul]
        simp only [c, toAdd_ofAdd, ZMod.val_natCast_of_lt hn]
      _ = localTotalMap P j x := hgn ▸ hg
  · rintro ⟨g, rfl⟩
    exact regularMap_smul P j h₁ h₂ g y

/-- The actual map corestricted to the full literal regular-family overlap. -/
def regularMapToOverlap (x : FamilyStar (localPeriods P j)) : regularOverlap P j h₁ h₂ :=
  ⟨regularMap P j h₁ h₂ x, regularMap_mem_overlap P j h₁ h₂ x⟩

@[simp] theorem regularMapToOverlap_val (x : FamilyStar (localPeriods P j)) :
    (regularMapToOverlap P j h₁ h₂ x : (regularData P h₁ h₂).Space) =
      regularMap P j h₁ h₂ x := rfl

theorem regularMapToOverlap_surjective : Function.Surjective (regularMapToOverlap P j h₁ h₂) := by
  intro y
  have hy : y.val ∈ range (regularMap P j h₁ h₂) := by
    rw [regularMap_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem regularMapToOverlap_continuous : Continuous (regularMapToOverlap P j h₁ h₂) :=
  ((regularData P h₁ h₂).quotient_continuous.comp
    (localTotalMap_continuous P j)).subtype_mk _

/-- The map induced on the actual finite orbit quotient, with values in
the entire literal overlap. -/
def tautologicalToOverlap : TautologicalStar (localData P h₁ h₂ j) → regularOverlap P j h₁ h₂ := by
  let := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  exact Quotient.lift (regularMapToOverlap P j h₁ h₂) (by
    rintro x y ⟨g, hg⟩
    apply Subtype.ext
    exact (regularMap_eq_iff P j h₁ h₂ x y).mpr ⟨g, hg⟩)

@[simp] theorem tautologicalToOverlap_project (x : FamilyStar (localPeriods P j)) :
    tautologicalToOverlap P j h₁ h₂
        (starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x) =
      regularMapToOverlap P j h₁ h₂ x := rfl

theorem tautologicalToOverlap_injective : Function.Injective (tautologicalToOverlap P j h₁ h₂) := by
  let L := localData P h₁ h₂ j
  let := starAction L 0 (Matrix.mulVec_zero j.matrix)
  intro a b h
  obtain ⟨x, rfl⟩ := starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) a
  obtain ⟨y, rfl⟩ := starProject_surjective L 0 (Matrix.mulVec_zero j.matrix) b
  have hxy : regularMap P j h₁ h₂ x = regularMap P j h₁ h₂ y := congrArg Subtype.val h
  exact Quotient.sound ((regularMap_eq_iff P j h₁ h₂ x y).mp hxy)

theorem tautologicalToOverlap_surjective :
    Function.Surjective (tautologicalToOverlap P j h₁ h₂) := by
  intro y
  obtain ⟨x, rfl⟩ := regularMapToOverlap_surjective P j h₁ h₂ y
  exact ⟨starProject (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix) x, rfl⟩

theorem tautologicalToOverlap_bijective : Function.Bijective (tautologicalToOverlap P j h₁ h₂) :=
  ⟨tautologicalToOverlap_injective P j h₁ h₂, tautologicalToOverlap_surjective P j h₁ h₂⟩

theorem tautologicalToOverlap_continuous : Continuous (tautologicalToOverlap P j h₁ h₂) := by
  let := starAction (localData P h₁ h₂ j) 0 (Matrix.mulVec_zero j.matrix)
  apply (starCoveringMap (localData P h₁ h₂ j) 0
    (Matrix.mulVec_zero j.matrix)).toIsQuotientMap.continuous_iff.mpr
  exact regularMapToOverlap_continuous P j h₁ h₂

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
