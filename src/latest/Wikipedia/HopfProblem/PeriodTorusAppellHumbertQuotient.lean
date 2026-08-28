import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData
import Wikipedia.HopfProblem.CoveringManifold

/-!
# The actual quotient associated to a factor of automorphy

The total space is the orbit quotient of `ℂ² × ℂ` under
`(z,c) ↦ (z+l, F(l,z)c)`, with its quotient topology.  The projection
lands in the existing period torus.  A chosen lift of a base point gives
a unique scalar coordinate in its genuine quotient fibre.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The cocycle law is exactly the law for this point-dependent diagonal action. -/
@[instance_reducible] def diagonalAction :
    MulAction (Multiplicative p.lattice) (ComplexPlane₂ × ℂ) where
  smul g u := (u.1 + (g.toAdd : ComplexPlane₂), (F.factor g.toAdd u.1 : ℂ) * u.2)
  one_smul u := by
    change (u.1 + ((0 : p.lattice) : ComplexPlane₂), (F.factor 0 u.1 : ℂ) * u.2) = u
    simp
  mul_smul g h u := by
    change (u.1 + ((g.toAdd + h.toAdd : p.lattice) : ComplexPlane₂),
      (F.factor (g.toAdd + h.toAdd) u.1 : ℂ) * u.2) =
      ((u.1 + (h.toAdd : ComplexPlane₂)) + (g.toAdd : ComplexPlane₂),
        (F.factor g.toAdd (u.1 + h.toAdd) : ℂ) * ((F.factor h.toAdd u.1 : ℂ) * u.2))
    apply Prod.ext
    · simp only [Submodule.coe_add]
      abel
    · rw [F.factor_add_coe, mul_assoc]

def associatedRelation : Setoid (ComplexPlane₂ × ℂ) :=
  letI := diagonalAction F
  MulAction.orbitRel (Multiplicative p.lattice) (ComplexPlane₂ × ℂ)

/-- The genuine orbit quotient, not a product with a transported topology. -/
def AssociatedSpace := Quotient (associatedRelation F)

def associatedMap : ComplexPlane₂ × ℂ → AssociatedSpace F :=
  Quotient.mk (associatedRelation F)

theorem associatedMap_surjective : Function.Surjective (associatedMap F) :=
  Quotient.mk_surjective

theorem associatedMap_eq_iff (u v : ComplexPlane₂ × ℂ) :
    associatedMap F u = associatedMap F v ↔
      ∃ l : p.lattice, v.1 + (l : ComplexPlane₂) = u.1 ∧
        (F.factor l v.1 : ℂ) * v.2 = u.2 := by
  change (Quotient.mk (associatedRelation F) u : Quotient (associatedRelation F)) =
    Quotient.mk (associatedRelation F) v ↔ _
  rw [Quotient.eq]
  change (∃ g : Multiplicative p.lattice,
    (v.1 + (g.toAdd : ComplexPlane₂), (F.factor g.toAdd v.1 : ℂ) * v.2) = u) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.toAdd, congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  · rintro ⟨l, hz, hc⟩
    exact ⟨Multiplicative.ofAdd l, Prod.ext hz hc⟩

@[simp] theorem associatedMap_diagonal (l : p.lattice) (u : ComplexPlane₂ × ℂ) :
    associatedMap F (u.1 + l, (F.factor l u.1 : ℂ) * u.2) = associatedMap F u :=
  (associatedMap_eq_iff F _ _).mpr ⟨l, rfl, rfl⟩

instance associatedSpaceTopologicalSpace : TopologicalSpace (AssociatedSpace F) :=
  inferInstanceAs (TopologicalSpace (Quotient (associatedRelation F)))

theorem associatedMap_isQuotientMap : IsQuotientMap (associatedMap F) :=
  isQuotientMap_quotient_mk'

theorem associatedMap_continuous : Continuous (associatedMap F) :=
  (associatedMap_isQuotientMap F).continuous

/-- The actual lattice covering on the first factor supplies disjoint
neighborhoods for the diagonal action, including along the zero section. -/
theorem associatedMap_isQuotientCoveringMap :
    letI := diagonalAction F
    IsQuotientCoveringMap (associatedMap F) (Multiplicative p.lattice) := by
  let := diagonalAction F
  refine {
    toIsQuotientMap := associatedMap_isQuotientMap F
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro g
    exact (continuous_fst.add continuous_const).prodMk
      (((F.continuous_factor g.toAdd).comp continuous_fst).mul continuous_snd)
  · intro u v
    exact Quotient.eq
  · intro u
    obtain ⟨U, hU, hd⟩ := p.quotientCovering.disjoint u.1
    refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
    rintro g ⟨r, ⟨s, hs, rfl⟩, hgs⟩
    change g.toAdd = 0
    apply hd g.toAdd
    refine ⟨s.1 + (g.toAdd : ComplexPlane₂), ⟨s.1, hs, ?_⟩, hgs⟩
    exact add_comm _ _

theorem associatedMap_isOpenMap : IsOpenMap (associatedMap F) := by
  let := diagonalAction F
  exact (associatedMap_isQuotientCoveringMap F).isCoveringMap.isLocalHomeomorph.isOpenMap

/-- The quotient projection to the actual, already constructed period torus. -/
def projection : AssociatedSpace F → p.Torus :=
  Quotient.lift (fun u : ComplexPlane₂ × ℂ => p.lattice.mkQ u.1) (by
    intro u v h
    change (∃ g : Multiplicative p.lattice,
      (v.1 + (g.toAdd : ComplexPlane₂), (F.factor g.toAdd v.1 : ℂ) * v.2) = u) at h
    obtain ⟨g, hg⟩ := h
    have hz : v.1 + (g.toAdd : ComplexPlane₂) = u.1 := congrArg Prod.fst hg
    have hl : p.lattice.mkQ (g.toAdd : ComplexPlane₂) = 0 :=
      (Submodule.Quotient.mk_eq_zero p.lattice).mpr g.toAdd.property
    rw [← hz, map_add, hl, add_zero])

@[simp] theorem projection_associatedMap (u : ComplexPlane₂ × ℂ) :
    projection F (associatedMap F u) = p.lattice.mkQ u.1 := rfl

theorem projection_continuous : Continuous (projection F) :=
  (associatedMap_isQuotientMap F).continuous_iff.mpr
    (p.lattice.continuous_mkQ.comp continuous_fst)

theorem projection_surjective : Function.Surjective (projection F) := by
  intro b
  obtain ⟨a, rfl⟩ := p.lattice.mkQ_surjective b
  exact ⟨associatedMap F (a, 0), rfl⟩

theorem associatedMap_fibre_injective (a : ComplexPlane₂) :
    Function.Injective (fun c : ℂ => associatedMap F (a, c)) := by
  intro c d he
  obtain ⟨l, hl, hd⟩ := (associatedMap_eq_iff F _ _).mp he
  have hl0 : (l : ComplexPlane₂) = 0 := add_left_cancel (hl.trans (add_zero a).symm)
  have hl' : l = 0 := Subtype.ext hl0
  simpa [hl'] using hd.symm

/-- A lift of the base point gives a genuine unique scalar in its quotient fibre. -/
theorem existsUnique_fibreCoordinate (a : ComplexPlane₂) (u : AssociatedSpace F)
    (hu : projection F u = p.lattice.mkQ a) :
    ∃! c : ℂ, associatedMap F (a, c) = u := by
  obtain ⟨⟨b, c⟩, rfl⟩ := associatedMap_surjective F u
  have hab : a - b ∈ p.lattice := (Submodule.Quotient.eq p.lattice).mp hu.symm
  let l : p.lattice := ⟨a - b, hab⟩
  have hbase : b + (l : ComplexPlane₂) = a := by
    change b + (a - b) = a
    abel
  have he : associatedMap F (a, (F.factor l b : ℂ) * c) = associatedMap F (b, c) :=
    (associatedMap_eq_iff F _ _).mpr ⟨l, hbase, rfl⟩
  refine ⟨(F.factor l b : ℂ) * c, he, ?_⟩
  intro d hd
  exact associatedMap_fibre_injective F a (hd.trans he.symm)

def fibreCoordinate (a : ComplexPlane₂) (u : AssociatedSpace F)
    (hu : projection F u = p.lattice.mkQ a) : ℂ :=
  (existsUnique_fibreCoordinate F a u hu).choose

@[simp] theorem associatedMap_fibreCoordinate (a : ComplexPlane₂) (u : AssociatedSpace F)
    (hu : projection F u = p.lattice.mkQ a) :
    associatedMap F (a, fibreCoordinate F a u hu) = u :=
  (existsUnique_fibreCoordinate F a u hu).choose_spec.1

@[simp] theorem fibreCoordinate_associatedMap (a : ComplexPlane₂) (c : ℂ) :
    fibreCoordinate F a (associatedMap F (a, c)) rfl = c :=
  associatedMap_fibre_injective F a
    (associatedMap_fibreCoordinate F a (associatedMap F (a, c)) rfl)

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
