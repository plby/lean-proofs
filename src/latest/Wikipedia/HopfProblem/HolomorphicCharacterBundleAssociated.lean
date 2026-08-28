import Wikipedia.HopfProblem.CoveringManifold

/-!
# The associated quotient of a character

For a covering action on `A`, the character `χ` acts diagonally on `A × ℂ`.
The total space below is the actual orbit quotient, with its quotient
topology.  Its projection has one-dimensional complex fibres; the coordinate
on a fibre after choosing a lift in `A` is proved to be unique.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle

variable {G A B : Type*} [Group G] [MulAction G A]

/-- The diagonal action defining the associated line bundle. -/
@[instance_reducible] def diagonalAction (χ : G →* ℂˣ) : MulAction G (A × ℂ) where
  smul g p := (g • p.1, (χ g : ℂ) * p.2)
  one_smul p := by
    change ((1 : G) • p.1, (χ 1 : ℂ) * p.2) = p
    simp
  mul_smul g h p := by
    change ((g * h) • p.1, (χ (g * h) : ℂ) * p.2) =
      (g • (h • p.1), (χ g : ℂ) * ((χ h : ℂ) * p.2))
    simp [mul_smul, mul_assoc]

def associatedRelation (χ : G →* ℂˣ) : Setoid (A × ℂ) :=
  letI := diagonalAction (A := A) χ
  MulAction.orbitRel G (A × ℂ)

/-- The actual quotient `(A × ℂ)/G`, not a product with a transported topology. -/
def AssociatedSpace (χ : G →* ℂˣ) := Quotient (associatedRelation (A := A) χ)

def associatedMap (χ : G →* ℂˣ) : A × ℂ → AssociatedSpace (A := A) χ :=
  Quotient.mk (associatedRelation χ)

theorem associatedMap_surjective (χ : G →* ℂˣ) :
    Function.Surjective (associatedMap (A := A) χ) := Quotient.mk_surjective

theorem associatedMap_eq_iff (χ : G →* ℂˣ) (p r : A × ℂ) :
    associatedMap χ p = associatedMap χ r ↔
      ∃ g : G, g • r.1 = p.1 ∧ (χ g : ℂ) * r.2 = p.2 := by
  change (Quotient.mk (associatedRelation χ) p : Quotient (associatedRelation χ)) =
    Quotient.mk (associatedRelation χ) r ↔ _
  rw [Quotient.eq]
  change (∃ g : G, (g • r.1, (χ g : ℂ) * r.2) = p) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  · rintro ⟨g, ha, hz⟩
    exact ⟨g, Prod.ext ha hz⟩

@[simp] theorem associatedMap_diagonal (χ : G →* ℂˣ) (g : G) (p : A × ℂ) :
    associatedMap χ (g • p.1, (χ g : ℂ) * p.2) = associatedMap χ p :=
  (associatedMap_eq_iff χ _ _).mpr ⟨g, rfl, rfl⟩

variable [TopologicalSpace A] [TopologicalSpace B]

instance associatedSpaceTopologicalSpace (χ : G →* ℂˣ) :
    TopologicalSpace (AssociatedSpace (A := A) χ) :=
  inferInstanceAs (TopologicalSpace (Quotient (associatedRelation χ)))

theorem associatedMap_isQuotientMap (χ : G →* ℂˣ) :
    IsQuotientMap (associatedMap (A := A) χ) := isQuotientMap_quotient_mk'

theorem associatedMap_continuous (χ : G →* ℂˣ) :
    Continuous (associatedMap (A := A) χ) :=
  (associatedMap_isQuotientMap χ).continuous

variable {q : A → B} (hq : IsQuotientCoveringMap q G) (χ : G →* ℂˣ)

include hq

/-- A covering action on the first factor gives a covering action on the
diagonal product, even though the action on the second factor fixes zero. -/
theorem associatedMap_isQuotientCoveringMap :
    letI := diagonalAction (A := A) χ
    IsQuotientCoveringMap (associatedMap (A := A) χ) G := by
  letI := diagonalAction (A := A) χ
  refine
    { toIsQuotientMap := associatedMap_isQuotientMap χ
      continuous_const_smul := ?_
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro g
    exact ((hq.continuous_const_smul g).comp continuous_fst).prodMk
      (continuous_const.mul continuous_snd)
  · intro p r
    exact Quotient.eq
  · intro p
    obtain ⟨U, hU, hd⟩ := hq.disjoint p.1
    refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
    rintro g ⟨r, ⟨s, hs, rfl⟩, hgs⟩
    exact hd g ⟨g • s.1, ⟨s.1, hs, rfl⟩, hgs⟩

/-- The quotient projection to the specified base quotient. -/
def projection : AssociatedSpace (A := A) χ → B :=
  Quotient.lift (fun p : A × ℂ => q p.1) fun p r h => by
    obtain ⟨g, hg⟩ := h
    exact congrArg q (congrArg Prod.fst hg).symm |>.trans (hq.map_smul g)

@[simp] theorem projection_associatedMap (p : A × ℂ) :
    projection hq χ (associatedMap χ p) = q p.1 := rfl

theorem projection_continuous : Continuous (projection hq χ) :=
  (associatedMap_isQuotientMap χ).continuous_iff.mpr
    (hq.continuous.comp continuous_fst)

theorem associatedMap_fibre_injective (a : A) :
    Function.Injective (fun z : ℂ => associatedMap χ (a, z)) := by
  letI := hq.isCancelSMul
  intro z w he
  obtain ⟨g, hg, hw⟩ := (associatedMap_eq_iff χ _ _).mp he
  have hg1 : g = 1 := IsCancelSMul.right_cancel g 1 a (hg.trans (one_smul G a).symm)
  simpa [hg1] using hw.symm

/-- A lift of the base point gives an honest bijective scalar coordinate
on its fibre. -/
theorem existsUnique_fibreCoordinate (a : A) (p : AssociatedSpace (A := A) χ)
    (hp : projection hq χ p = q a) :
    ∃! z : ℂ, associatedMap χ (a, z) = p := by
  obtain ⟨⟨b, w⟩, rfl⟩ := associatedMap_surjective χ p
  obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hp
  refine ⟨(χ g : ℂ)⁻¹ * w, ?_, ?_⟩
  · apply (associatedMap_eq_iff χ _ _).mpr
    refine ⟨g⁻¹, ?_, ?_⟩
    · exact (eq_inv_smul_iff.mpr hg).symm
    · simp
  · intro z hz
    apply associatedMap_fibre_injective hq χ a
    exact hz.trans ((associatedMap_eq_iff χ _ _).mpr
      ⟨g⁻¹, (eq_inv_smul_iff.mpr hg).symm, by simp⟩).symm

def fibreCoordinate (a : A) (p : AssociatedSpace (A := A) χ)
    (hp : projection hq χ p = q a) : ℂ :=
  (existsUnique_fibreCoordinate hq χ a p hp).choose

@[simp] theorem associatedMap_fibreCoordinate (a : A)
    (p : AssociatedSpace (A := A) χ) (hp : projection hq χ p = q a) :
    associatedMap χ (a, fibreCoordinate hq χ a p hp) = p :=
  (existsUnique_fibreCoordinate hq χ a p hp).choose_spec.1

@[simp] theorem fibreCoordinate_associatedMap (a : A) (z : ℂ) :
    fibreCoordinate hq χ a (associatedMap χ (a, z)) rfl = z :=
  associatedMap_fibre_injective hq χ a
    (associatedMap_fibreCoordinate hq χ a (associatedMap χ (a, z)) rfl)

end Wikipedia.HopfProblem.HolomorphicCharacterBundle
