import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspCoordinates
import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing

/-!
# The entire cusp-family quotient is a height times a mapping torus

Both quotient maps below have their existing quotient topologies. Their
fibres agree by the actual logarithmic deck action. Descending in both
directions gives a homeomorphism of the whole cusp-family quotient with
the height half-line times the mapping torus of the actual `M₀` action.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp

open SpecialPeriods.CuspFamily CuspUniformization

private def commonQuotientHomeomorph
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : A → X) (g : A → Y) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  let e : X ≃ Y := Equiv.ofBijective
    (CuspHoneycombHexagon.CommonFibres.descend f g hf.surjective)
    ⟨CuspHoneycombHexagon.CommonFibres.descend_injective f g hf.surjective
        (fun a b => (he a b).mpr),
      CuspHoneycombHexagon.CommonFibres.descend_surjective f g hf.surjective
        (fun a b => (he a b).mp) hg.surjective⟩
  refine { toEquiv := e
           continuous_toFun := CuspHoneycombHexagon.CommonFibres.descend_continuous
             f g hf.surjective hf hg.continuous (fun a b => (he a b).mp)
           continuous_invFun := ?_ }
  apply hg.continuous_iff.mpr
  change Continuous (e.symm ∘ g)
  have hcomp : e.symm ∘ g = f := by
    funext a
    apply e.injective
    change e (e.symm (g a)) = e (f a)
    rw [e.apply_symm_apply]
    exact (CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective
      (fun a b => (he a b).mp) a).symm
  rw [hcomp]
  exact hf.continuous

private theorem commonQuotientHomeomorph_apply
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : A → X) (g : A → Y) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    commonQuotientHomeomorph f g hf hg he (f a) = g a :=
  CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective
    (fun a b => (he a b).mp) a

/-- The genuine mapping-torus quotient, with the logarithmic height unchanged. -/
def cylinderProjection (r : ℝ) :
    C(Height r × (ℝ × RealTorus₄), Height r × Boundary) :=
  ⟨Prod.map id (MappingTorus.mk monodromy),
    continuous_id.prodMap (MappingTorus.mk_continuous monodromy)⟩

theorem cylinderProjection_isOpenQuotientMap (r : ℝ) :
    IsOpenQuotientMap (cylinderProjection r) :=
  IsOpenQuotientMap.id.prodMap
    ⟨MappingTorus.mk_surjective monodromy, MappingTorus.mk_continuous monodromy,
      MappingTorus.mk_open monodromy⟩

/-- The actual logarithmic family mapped to its height and mapping-torus coordinates. -/
def familyProductMap (D : Data) : C(D.TotalSpace, Height D.radius × Boundary) :=
  (cylinderProjection D.radius).comp
    ⟨familyCylinderHomeomorph D, (familyCylinderHomeomorph D).continuous⟩

theorem familyProductMap_isOpenQuotientMap (D : Data) :
    IsOpenQuotientMap (familyProductMap D) :=
  (cylinderProjection_isOpenQuotientMap D.radius).comp
    (familyCylinderHomeomorph D).isOpenQuotientMap

theorem familyProductMap_smul (D : Data) (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    familyProductMap D (k • x) = familyProductMap D x := by
  let := D.totalAction
  change Prod.map id (MappingTorus.mk monodromy) (familyCylinderHomeomorph D (k • x)) = _
  rw [familyCylinderHomeomorph_smul]
  exact Prod.ext rfl (MappingTorus.mk_deck monodromy (-k.toAdd) _)

/-- The two entire-space quotient projections have exactly the same fibres. -/
theorem familyProductMap_eq_iff (D : Data) (x y : D.TotalSpace) :
    familyProductMap D x = familyProductMap D y ↔ D.quotient x = D.quotient y := by
  let := D.totalAction
  constructor
  · intro h
    have hheight : (x.1 : ℂ).im = (y.1 : ℂ).im :=
      congrArg (fun p : Height D.radius × Boundary => (p.1 : ℝ)) h
    have htime := congrArg Prod.snd h
    change MappingTorus.mk monodromy ((x.1 : ℂ).re, x.2) =
      MappingTorus.mk monodromy ((y.1 : ℂ).re, y.2) at htime
    obtain ⟨n, ht, hx⟩ := (MappingTorus.mk_eq_mk_iff monodromy _ _).mp htime
    apply (D.quotient_eq_iff x y).mpr
    refine ⟨Multiplicative.ofAdd n, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Complex.ext
      · change ((y.1 : ℂ) - (n : ℂ)).re = (x.1 : ℂ).re
        change (y.1 : ℂ).re = (x.1 : ℂ).re + (n : ℝ) at ht
        simp only [Complex.sub_re, Complex.intCast_re]
        linarith
      · change ((y.1 : ℂ) - (n : ℂ)).im = (x.1 : ℂ).im
        simpa only [Complex.sub_im, Complex.intCast_im, sub_zero] using hheight.symm
    · change cuspTorusHomeomorph n y.2 = x.2
      change y.2 = (monodromy ^ (-n)) x.2 at hx
      rw [monodromy_zpow] at hx
      rw [hx, ← cuspTorusHomeomorph_add_apply, add_neg_cancel,
        cuspTorusHomeomorph_zero_apply]
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff x y).mp h
    rw [← hk, familyProductMap_smul]

theorem familyQuotient_isQuotientMap (D : Data) : IsQuotientMap D.quotient := by
  let := D.totalAction
  exact D.quotientCoveringMap.toIsQuotientMap

/-- The whole actual integer-monodromy quotient is a height half-line
times the genuine mapping torus of the actual integral monodromy. -/
def familyProductHomeomorph (D : Data) : D.Space ≃ₜ Height D.radius × Boundary :=
  commonQuotientHomeomorph D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D)
    (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm)

@[simp] theorem familyProductHomeomorph_quotient (D : Data) (x : D.TotalSpace) :
    familyProductHomeomorph D (D.quotient x) = familyProductMap D x :=
  commonQuotientHomeomorph_apply D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D)
    (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm) x

theorem familyProductMap_logPoint (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    familyProductMap D (logPoint D.radius D.radius_pos t h, x) =
      (h, MappingTorus.mk monodromy (t, x)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact logPoint_im D.radius D.radius_pos t h
  · change MappingTorus.mk monodromy ((logPoint D.radius D.radius_pos t h : ℂ).re, x) = _
    rw [logPoint_re]

/-- The inverse homeomorphism on every literal mapping-torus cylinder representative. -/
theorem familyProductHomeomorph_symm_mk (D : Data) (h : Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    (familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x)) =
      D.quotient (logPoint D.radius D.radius_pos t h, x) := by
  simpa only [familyProductHomeomorph_quotient, familyProductMap_logPoint] using
    (familyProductHomeomorph D).symm_apply_apply
      (D.quotient (logPoint D.radius D.radius_pos t h, x))

/-- The base-circle map in these actual whole-family coordinates. -/
def familyBaseCircle (D : Data) : C(D.Space, MappingTorus.Circle) :=
  (MappingTorus.base monodromy).comp
    ⟨fun q => (familyProductHomeomorph D q).2,
      continuous_snd.comp (familyProductHomeomorph D).continuous⟩

@[simp] theorem familyBaseCircle_quotient (D : Data) (x : D.TotalSpace) :
    familyBaseCircle D (D.quotient x) = ((x.1 : ℂ).re : MappingTorus.Circle) := by
  change MappingTorus.base monodromy (familyProductHomeomorph D (D.quotient x)).2 = _
  rw [familyProductHomeomorph_quotient]
  rfl

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Cusp
