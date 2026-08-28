import Wikipedia.HopfProblem.MappingTorusTopology

/-!
# Mapping tori of conjugate homeomorphisms

A conjugacy of the actual fibre homeomorphisms induces a homeomorphism of
their actual mapping tori.  The map preserves the real cylinder coordinate
and applies the given conjugacy to the fibre coordinate.  Both directions
descend through the original integer-deck quotients with their quotient
topologies.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open MappingTorus

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Conjugation by a homeomorphism is a homomorphism of the homeomorphism groups. -/
def homeomorphConjugation (e : X ≃ₜ Y) : (X ≃ₜ X) →* (Y ≃ₜ Y) where
  toFun f := e.symm.trans (f.trans e)
  map_one' := by ext y; simp
  map_mul' f h := by ext y; simp

@[simp] theorem homeomorphConjugation_apply (e : X ≃ₜ Y) (f : X ≃ₜ X) (y : Y) :
    homeomorphConjugation e f y = e (f (e.symm y)) := rfl

/-- An intertwining of the generators intertwines every positive and negative
integer power; the negative powers use the actual inverse homeomorphisms. -/
theorem mappingTorusConjugacy_zpow (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (n : ℤ) (x : X) :
    e ((f ^ n) x) = (g ^ n) (e x) := by
  have hfg : homeomorphConjugation e f = g := by
    ext y
    change e (f (e.symm y)) = g y
    rw [he, e.apply_symm_apply]
  have hpow := congrArg (fun h : Y ≃ₜ Y ↦ h (e x))
    ((homeomorphConjugation e).map_zpow f n)
  simpa only [homeomorphConjugation_apply, e.symm_apply_apply, hfg] using hpow

/-- The inverse fibre homeomorphism gives the conjugacy in the opposite direction. -/
theorem mappingTorusConjugacy_symm_generator (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (e : X ≃ₜ Y) (he : ∀ x, e (f x) = g (e x)) (y : Y) :
    e.symm (g y) = f (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- The literal cylinder map intertwines every integer deck transformation. -/
theorem mappingTorusConjugacy_deck (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (n : ℤ) (p : ℝ × X) :
    ((deck f n p).1, e (deck f n p).2) = deck g n (p.1, e p.2) := by
  apply Prod.ext
  · rfl
  · exact mappingTorusConjugacy_zpow f g e he (-n) p.2

/-- The induced continuous map on the original mapping-torus quotient. -/
def mappingTorusConjugacyMap (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) : C(Torus f, Torus g) where
  toFun := Quotient.lift (fun p : ℝ × X ↦ mk g (p.1, e p.2)) (by
    rintro p q ⟨n, rfl⟩
    rw [mappingTorusConjugacy_deck f g e he, mk_deck])
  continuous_toFun := ((mk_continuous g).comp
    (continuous_fst.prodMk (e.continuous.comp continuous_snd))).quotient_lift _

@[simp] theorem mappingTorusConjugacyMap_mk (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (e : X ≃ₜ Y) (he : ∀ x, e (f x) = g (e x)) (t : ℝ) (x : X) :
    mappingTorusConjugacyMap f g e he (mk f (t, x)) = mk g (t, e x) := rfl

/-- Conjugate fibre homeomorphisms have homeomorphic actual mapping tori. -/
def mappingTorusConjugacy (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) : Torus f ≃ₜ Torus g where
  toFun := mappingTorusConjugacyMap f g e he
  invFun := mappingTorusConjugacyMap g f e.symm
    (mappingTorusConjugacy_symm_generator f g e he)
  left_inv q := by
    obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective f q
    simp only [mappingTorusConjugacyMap_mk, e.symm_apply_apply]
  right_inv q := by
    obtain ⟨⟨t, y⟩, rfl⟩ := mk_surjective g q
    simp only [mappingTorusConjugacyMap_mk, e.apply_symm_apply]
  continuous_toFun := (mappingTorusConjugacyMap f g e he).continuous
  continuous_invFun := (mappingTorusConjugacyMap g f e.symm
    (mappingTorusConjugacy_symm_generator f g e he)).continuous

/-- The homeomorphism retains the real time and applies the specified fibre map. -/
@[simp] theorem mappingTorusConjugacy_mk (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (e : X ≃ₜ Y) (he : ∀ x, e (f x) = g (e x)) (t : ℝ) (x : X) :
    mappingTorusConjugacy f g e he (mk f (t, x)) = mk g (t, e x) := rfl

/-- The inverse is the corresponding literal map with the inverse fibre homeomorphism. -/
@[simp] theorem mappingTorusConjugacy_symm_mk (f : X ≃ₜ X) (g : Y ≃ₜ Y)
    (e : X ≃ₜ Y) (he : ∀ x, e (f x) = g (e x)) (t : ℝ) (y : Y) :
    (mappingTorusConjugacy f g e he).symm (mk g (t, y)) =
      mk f (t, e.symm y) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
