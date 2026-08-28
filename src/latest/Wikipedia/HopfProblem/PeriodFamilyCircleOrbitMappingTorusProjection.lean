import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLattice
import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitMappingTorusElliptic
import Wikipedia.HopfProblem.MappingTorusTopology

/-!
# The literal cylinder projection and its integer deck transformations

The native mapping-torus convention is `(t, x) ↦ (t + n, f^(-n) x)`.
The return map translating by `-6μ` therefore gives precisely the deck
translation `(z, r) ↦ (z + 6μ, r + 1)` of the projected period lattice.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- The actual mapping torus of the elliptic return translation. -/
abbrev MappingTorusModel (p : PeriodDomain) := MappingTorus.Torus (returnTranslation p)

/-- Quotient the complex coordinate by its genuine elliptic period lattice. -/
def ellipticCylinderProjection (p : PeriodDomain) : C(ℂ × ℝ, ℝ × EllipticModel p) where
  toFun z := (z.2, ellipticClass p z.1)
  continuous_toFun := continuous_snd.prodMk
    ((ellipticClass_continuous p).comp continuous_fst)

@[simp] theorem ellipticCylinderProjection_apply (p : PeriodDomain) (z : ℂ × ℝ) :
    ellipticCylinderProjection p z = (z.2, ellipticClass p z.1) := rfl

theorem ellipticCylinderProjection_isOpenMap (p : PeriodDomain) :
    IsOpenMap (ellipticCylinderProjection p) :=
  (IsOpenMap.id.prodMap (ellipticClass_isOpenMap p)).comp
    (Homeomorph.prodComm ℂ ℝ).isOpenMap

theorem ellipticCylinderProjection_surjective (p : PeriodDomain) :
    Function.Surjective (ellipticCylinderProjection p) := by
  rintro ⟨r, e⟩
  obtain ⟨z, rfl⟩ := ellipticClass_surjective p e
  exact ⟨(z, r), rfl⟩

/-- The unmodified representative map `(z,r) ↦ [r,[z]]`. -/
def mappingTorusProjection (p : PeriodDomain) : C(ℂ × ℝ, MappingTorusModel p) where
  toFun z := MappingTorus.mk (returnTranslation p) (ellipticCylinderProjection p z)
  continuous_toFun := (MappingTorus.mk_continuous (returnTranslation p)).comp
    (ellipticCylinderProjection p).continuous

@[simp] theorem mappingTorusProjection_apply (p : PeriodDomain) (z : ℂ × ℝ) :
    mappingTorusProjection p z =
      MappingTorus.mk (returnTranslation p) (z.2, ellipticClass p z.1) := rfl

theorem mappingTorusProjection_isOpenMap (p : PeriodDomain) :
    IsOpenMap (mappingTorusProjection p) :=
  (MappingTorus.mk_open (returnTranslation p)).comp
    (ellipticCylinderProjection_isOpenMap p)

theorem mappingTorusProjection_surjective (p : PeriodDomain) :
    Function.Surjective (mappingTorusProjection p) :=
  (MappingTorus.mk_surjective (returnTranslation p)).comp
    (ellipticCylinderProjection_surjective p)

theorem mappingTorusProjection_isQuotientMap (p : PeriodDomain) :
    IsQuotientMap (mappingTorusProjection p) :=
  (mappingTorusProjection_isOpenMap p).isQuotientMap
    (mappingTorusProjection p).continuous (mappingTorusProjection_surjective p)

/-- The three-period lattice is exactly an integer time shift together with
the corresponding elliptic translation. -/
theorem mem_orbitLattice_iff_ellipticSlice (p : PeriodDomain) (z : ℂ × ℝ) :
    z ∈ orbitLattice p ↔ ∃ n : ℤ,
      z.2 = (n : ℝ) ∧ z.1 - n • (6 * p.val.μ) ∈ ellipticLattice p := by
  rw [mem_orbitLattice_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, rfl, (ellipticLattice_mem_iff p _).mpr ⟨n 1, n 2, ?_⟩⟩
    simp only [zsmul_eq_mul]
    ring
  · rintro ⟨n, hn, hz⟩
    obtain ⟨m, k, hmk⟩ := (ellipticLattice_mem_iff p _).mp hz
    refine ⟨![n, m, k], Prod.ext ?_ hn⟩
    change z.1 = 6 * p.val.μ * (n : ℂ) + p.val.τ * (m : ℂ) + (k : ℂ)
    simp only [zsmul_eq_mul] at hmk
    linear_combination hmk

/-- Positive integer deck time adds the positive projected first period. -/
theorem returnTranslation_deck_class (p : PeriodDomain) (n : ℤ) (z : ℂ) :
    (returnTranslation p ^ (-n)) (ellipticClass p z) =
      ellipticClass p (z + n • (6 * p.val.μ)) := by
  rw [returnTranslation_zpow_apply, neg_zsmul, sub_neg_eq_add, ← map_zsmul, ← map_add]

/-- Equality of the literal mapping-torus representatives is exactly the
original projected lattice relation. -/
theorem mappingTorusProjection_eq_iff (p : PeriodDomain) (z w : ℂ × ℝ) :
    mappingTorusProjection p z = mappingTorusProjection p w ↔ w - z ∈ orbitLattice p := by
  rw [mappingTorusProjection_apply, mappingTorusProjection_apply,
    MappingTorus.mk_eq_mk_iff, mem_orbitLattice_iff_ellipticSlice]
  simp only [returnTranslation_deck_class, ellipticClass_eq_iff, Prod.fst_sub, Prod.snd_sub,
    sub_add_eq_sub_sub, sub_eq_iff_eq_add']

theorem mappingTorusProjection_eq_iff_orbitClass (p : PeriodDomain) (z w : ℂ × ℝ) :
    mappingTorusProjection p z = mappingTorusProjection p w ↔
      orbitClass p z = orbitClass p w := by
  rw [mappingTorusProjection_eq_iff, ← orbitClass_eq_iff p w z]
  exact eq_comm

@[simp] theorem mappingTorusProjection_deck (p : PeriodDomain) (n : ℤ) (z : ℂ × ℝ) :
    mappingTorusProjection p (z.1 + n • (6 * p.val.μ), z.2 + (n : ℝ)) =
      mappingTorusProjection p z := by
  change MappingTorus.mk (returnTranslation p)
      (z.2 + (n : ℝ), ellipticClass p (z.1 + n • (6 * p.val.μ))) = _
  rw [← returnTranslation_deck_class]
  exact MappingTorus.mk_deck (returnTranslation p) n (z.2, ellipticClass p z.1)

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
