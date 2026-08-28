import Wikipedia.HopfProblem.PeriodTorusAppellHumbertQuotient

/-!
# Actual sections of the Appell--Humbert quotient

A section is a genuine right inverse to the projection of the orbit
quotient. Its scalar pullback is recovered from the unique coordinate
in each actual quotient fibre. The automorphy law and the inverse
descent construction are theorems, not the definition of a section.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- Automorphy with respect to the specified genuine factor of automorphy. -/
def IsAutomorphic (f : ComplexPlane₂ → ℂ) : Prop :=
  ∀ (l : p.lattice) z, f (z + l) = (F.factor l z : ℂ) * f z

/-- An actual right inverse to the independently constructed quotient projection. -/
structure Section where
  toFun : p.Torus → AssociatedSpace F
  projection_toFun : ∀ b, projection F (toFun b) = b

instance : CoeFun (Section F) (fun _ => p.Torus → AssociatedSpace F) := ⟨Section.toFun⟩

@[simp] theorem Section.projection_apply (s : Section F) (b : p.Torus) :
    projection F (s b) = b := s.projection_toFun b

@[ext] theorem Section.ext {s t : Section F} (h : ∀ b, s b = t b) : s = t := by
  cases s with
  | mk f hf =>
    cases t with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

/-- Scalar pullback in the actual quotient fibre over the given covering point. -/
def Section.pullback (s : Section F) (z : ComplexPlane₂) : ℂ :=
  fibreCoordinate F z (s (p.lattice.mkQ z)) (s.projection_apply F (p.lattice.mkQ z))

@[simp] theorem Section.associatedMap_pullback (s : Section F) (z : ComplexPlane₂) :
    associatedMap F (z, s.pullback F z) = s (p.lattice.mkQ z) :=
  associatedMap_fibreCoordinate F z (s (p.lattice.mkQ z)) _

/-- The transformation law is forced by equality of the same actual section fibre. -/
theorem Section.pullback_automorphic (s : Section F) : IsAutomorphic F (s.pullback F) := by
  intro l z
  apply associatedMap_fibre_injective F (z + l)
  dsimp only
  rw [s.associatedMap_pullback, map_add]
  have hl : p.lattice.mkQ (l : ComplexPlane₂) = 0 :=
    (Submodule.Quotient.mk_eq_zero p.lattice).mpr l.property
  rw [hl, add_zero, associatedMap_diagonal F l (z, s.pullback F z),
    s.associatedMap_pullback]

/-- Descent of an automorphic function to a genuine section. -/
def sectionOfAutomorphic (f : ComplexPlane₂ → ℂ) (_hf : IsAutomorphic F f) : Section F where
  toFun b := associatedMap F (DiscreteQuotient.representative p.lattice b,
    f (DiscreteQuotient.representative p.lattice b))
  projection_toFun b := DiscreteQuotient.mkQ_representative p.lattice b

theorem sectionOfAutomorphic_apply_project (f : ComplexPlane₂ → ℂ)
    (hf : IsAutomorphic F f) (z : ComplexPlane₂) :
    sectionOfAutomorphic F f hf (p.lattice.mkQ z) = associatedMap F (z, f z) := by
  let r := DiscreteQuotient.representative p.lattice (p.lattice.mkQ z)
  have hr : p.lattice.mkQ r = p.lattice.mkQ z :=
    DiscreteQuotient.mkQ_representative p.lattice (p.lattice.mkQ z)
  let l : p.lattice := ⟨r - z, (Submodule.Quotient.eq p.lattice).mp hr⟩
  have hl : z + (l : ComplexPlane₂) = r := by
    change z + (r - z) = r
    rw [add_comm z (r - z), sub_add_cancel]
  apply (associatedMap_eq_iff F _ _).mpr
  refine ⟨l, hl, ?_⟩
  exact (hf l z).symm.trans (congrArg f hl)

@[simp] theorem sectionOfAutomorphic_pullback (f : ComplexPlane₂ → ℂ)
    (hf : IsAutomorphic F f) : (sectionOfAutomorphic F f hf).pullback F = f := by
  funext z
  apply associatedMap_fibre_injective F z
  dsimp only
  rw [Section.associatedMap_pullback, sectionOfAutomorphic_apply_project]

@[simp] theorem sectionOfAutomorphic_section_pullback (s : Section F) :
    sectionOfAutomorphic F (s.pullback F) (s.pullback_automorphic F) = s := by
  apply Section.ext
  intro b
  obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective b
  rw [sectionOfAutomorphic_apply_project, Section.associatedMap_pullback]

/-- The explicit bijection is proved between actual sections and scalar automorphy. -/
def sectionEquivAutomorphic : Section F ≃ {f : ComplexPlane₂ → ℂ // IsAutomorphic F f} where
  toFun s := ⟨s.pullback F, s.pullback_automorphic F⟩
  invFun f := sectionOfAutomorphic F f.val f.property
  left_inv := sectionOfAutomorphic_section_pullback F
  right_inv f := Subtype.ext (sectionOfAutomorphic_pullback F f.val f.property)

def zeroSection : Section F :=
  sectionOfAutomorphic F (fun _ => 0) (fun _ _ => by simp)

@[simp] theorem zeroSection_apply_project (z : ComplexPlane₂) :
    zeroSection F (p.lattice.mkQ z) = associatedMap F (z, 0) :=
  sectionOfAutomorphic_apply_project F _ _ z

@[simp] theorem zeroSection_pullback : (zeroSection F).pullback F = 0 :=
  sectionOfAutomorphic_pullback F _ _

theorem Section.eq_zero_iff_pullback (s : Section F) :
    s = zeroSection F ↔ s.pullback F = 0 := by
  constructor
  · rintro rfl
    exact zeroSection_pullback F
  · intro hs
    apply Section.ext
    intro b
    obtain ⟨z, rfl⟩ := p.lattice.mkQ_surjective b
    rw [← s.associatedMap_pullback, zeroSection_apply_project]
    exact congrArg (fun c => associatedMap F (z, c)) (congrFun hs z)

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
