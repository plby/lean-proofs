import Wikipedia.HopfProblem.AnalyticRootCoverPresheaf
import Wikipedia.HopfProblem.SpecialPeriodsModular

/-!
# The sheaf of actual local analytic lifts of the modular j-function

The target of each local section is the upper half-plane itself, not a
complex-valued function equipped with a germwise choice of target.  Its complex
coordinate extension is used only to express local analyticity.  The equation
`modularJ ∘ s = F` holds on the actual section domain.

Restriction and locality are proved using agreement on open neighborhoods.
No global lift or continuation theorem is assumed by this presheaf.
-/

noncomputable section

open CategoryTheory Function Filter Opposite Set TopologicalSpace UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

open AnalyticRootCover

/-- The complex coordinate extension of an actual upper-half-plane-valued section. -/
def extendLiftSection (S : Opens ℂ) (V : Opens S) (s : V → ℍ) : ℂ → ℂ :=
  extendSection S V (fun x => (s x : ℂ))

@[simp] theorem extendLiftSection_apply (S : Opens ℂ) (V : Opens S)
    (s : V → ℍ) (x : V) :
    extendLiftSection S V s (ambientVal S V x) = (s x : ℂ) :=
  extendSection_apply S V (fun y => (s y : ℂ)) x

theorem extendLiftSection_injective (S : Opens ℂ) (V : Opens S) :
    Injective (extendLiftSection S V) := by
  intro s t he
  funext x
  apply UpperHalfPlane.coe_injective
  simpa only [extendLiftSection_apply] using congr_fun he (ambientVal S V x)

theorem extendLiftSection_restrict_eventuallyEq (S : Opens ℂ) {U V : Opens S}
    (i : U ⟶ V) (s : V → ℍ) (x : U) :
    extendLiftSection S U (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (ambientVal S U x)]
      extendLiftSection S V s :=
  extendSection_restrict_eventuallyEq S i (fun y => (s y : ℂ)) x

/-- The predicate of being an actual local analytic lift of the fixed ambient function. -/
def IsLiftSection (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S} (s : V → ℍ) : Prop :=
  ∀ x : V, AnalyticAt ℂ (extendLiftSection S V s) (ambientVal S V x) ∧
    modularJ (s x) = F (ambientVal S V x)

/-- Locally analytic modular lifts form a local predicate with constant target `ℍ`. -/
def liftLocalPredicate (S : Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℍ) where
  pred {_} s := IsLiftSection S F s
  res {_ _} i s hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact (hs (Set.inclusion i.le x)).1.congr
      (extendLiftSection_restrict_eventuallyEq S i s x).symm
  locality {U} s hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendLiftSection_restrict_eventuallyEq S i s y)
    · have he : modularJ (s (Set.inclusion i.le y)) = F (ambientVal S U x) := (hV y).2
      rwa [hix] at he

/-- The type-valued presheaf of actual analytic modular lifts. -/
def liftPresheaf (S : Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (liftLocalPredicate S F).toPrelocalPredicate

theorem liftPresheaf_isSheaf (S : Opens ℂ) (F : ℂ → ℂ) :
    (liftPresheaf S F).IsSheaf :=
  TopCat.subpresheafToTypes.isSheaf (liftLocalPredicate S F)

/-- An actual upper-half-plane-valued section, with analytic lift property. -/
abbrev LiftSection (S : Opens ℂ) (F : ℂ → ℂ) (V : Opens S) :=
  (liftPresheaf S F).obj (op V)

theorem liftSection_analytic (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (s : LiftSection S F V) (x : V) :
    AnalyticAt ℂ (extendLiftSection S V s.1) (ambientVal S V x) := (s.2 x).1

theorem liftSection_modular (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (s : LiftSection S F V) (x : V) :
    modularJ (s.1 x) = F (ambientVal S V x) := (s.2 x).2

@[simp] theorem liftPresheaf_map_apply (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens S} (i : U ⟶ V) (s : LiftSection S F V) (x : U) :
    ((liftPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) := rfl

theorem liftSection_ext (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    {s t : LiftSection S F V}
    (he : extendLiftSection S V s.1 = extendLiftSection S V t.1) : s = t :=
  Subtype.ext ((extendLiftSection_injective S V) he)

namespace LiftSection

variable {S : Opens ℂ} {F : ℂ → ℂ} {V : Opens S}

/-- The actual complex coordinate extension is analytic throughout the ambient domain. -/
theorem analyticOnNhd_extend (s : LiftSection S F V) :
    AnalyticOnNhd ℂ (extendLiftSection S V s.1) (ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  exact liftSection_analytic S F s x

/-- The complex extension takes values in the upper half-plane on its true domain. -/
theorem mapsTo_extend (s : LiftSection S F V) :
    MapsTo (extendLiftSection S V s.1) (ambientOpen S V) upperHalfPlaneSet := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendLiftSection_apply]
  exact (s.1 x).im_pos

theorem mapsTo_upperHalfPlane (s : LiftSection S F V) :
    MapsTo (extendLiftSection S V s.1) (ambientOpen S V) upperHalfPlaneSet :=
  s.mapsTo_extend

/-- The modular lift equation for the complex coordinate extension, on its
actual ambient open domain. -/
theorem modular_eq (s : LiftSection S F V) {z : ℂ} (hz : z ∈ ambientOpen S V) :
    modularJ (UpperHalfPlane.ofComplex (extendLiftSection S V s.1 z)) = F z := by
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendLiftSection_apply, UpperHalfPlane.ofComplex_apply]
  exact liftSection_modular S F s x

theorem modular_eq_apply (s : LiftSection S F V) (x : V) :
    modularJ (s.1 x) = F (ambientVal S V x) := liftSection_modular S F s x

@[ext] theorem ext {s t : LiftSection S F V} (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

end LiftSection

/-- Package an actual ambient upper-half-plane-valued analytic map into the
modular lift presheaf. -/
def liftSectionOfAnalytic (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℍ) (hr : AnalyticOnNhd ℂ (fun z => (r z : ℂ)) (ambientOpen S V))
    (hJ : ∀ x : V, modularJ (r (ambientVal S V x)) = F (ambientVal S V x)) :
    LiftSection S F V := by
  refine ⟨fun x => r (ambientVal S V x), fun x => ⟨?_, hJ x⟩⟩
  apply (hr _ (ambientVal_mem S V x)).congr
  filter_upwards [(ambientOpen S V).isOpen.mem_nhds (ambientVal_mem S V x)] with z hz
  exact (extension_agreement S V (fun w => (r w : ℂ)) hz).symm

@[simp] theorem liftSectionOfAnalytic_apply (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℍ) (hr : AnalyticOnNhd ℂ (fun z => (r z : ℂ)) (ambientOpen S V))
    (hJ : ∀ x : V, modularJ (r (ambientVal S V x)) = F (ambientVal S V x)) (x : V) :
    (liftSectionOfAnalytic S F r hr hJ).1 x = r (ambientVal S V x) := rfl

theorem extend_liftSectionOfAnalytic_eqOn (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℍ) (hr : AnalyticOnNhd ℂ (fun z => (r z : ℂ)) (ambientOpen S V))
    (hJ : ∀ x : V, modularJ (r (ambientVal S V x)) = F (ambientVal S V x)) :
    EqOn (extendLiftSection S V (liftSectionOfAnalytic S F r hr hJ).1)
      (fun z => (r z : ℂ)) (ambientOpen S V) :=
  extension_agreement S V (fun z => (r z : ℂ))

/-- Package a complex analytic local lift which is proved to take values in
the upper half-plane on its domain.  No target membership is assumed elsewhere. -/
def liftSectionOfComplex (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℂ) (hr : AnalyticOnNhd ℂ r (ambientOpen S V))
    (hpos : MapsTo r (ambientOpen S V) upperHalfPlaneSet)
    (hJ : EqOn (fun z => modularJ (UpperHalfPlane.ofComplex (r z))) F (ambientOpen S V)) :
    LiftSection S F V := by
  refine ⟨fun x => ⟨r (ambientVal S V x), hpos (ambientVal_mem S V x)⟩,
    fun x => ⟨?_, ?_⟩⟩
  · apply (hr _ (ambientVal_mem S V x)).congr
    filter_upwards [(ambientOpen S V).isOpen.mem_nhds (ambientVal_mem S V x)] with z hz
    exact (extension_agreement S V r hz).symm
  · simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos (hpos (ambientVal_mem S V x))]
      using hJ (ambientVal_mem S V x)

@[simp] theorem liftSectionOfComplex_apply (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℂ) (hr : AnalyticOnNhd ℂ r (ambientOpen S V))
    (hpos : MapsTo r (ambientOpen S V) upperHalfPlaneSet)
    (hJ : EqOn (fun z => modularJ (UpperHalfPlane.ofComplex (r z))) F (ambientOpen S V))
    (x : V) :
    ((liftSectionOfComplex S F r hr hpos hJ).1 x : ℂ) = r (ambientVal S V x) := rfl

theorem extend_liftSectionOfComplex_eqOn (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (r : ℂ → ℂ) (hr : AnalyticOnNhd ℂ r (ambientOpen S V))
    (hpos : MapsTo r (ambientOpen S V) upperHalfPlaneSet)
    (hJ : EqOn (fun z => modularJ (UpperHalfPlane.ofComplex (r z))) F (ambientOpen S V)) :
    EqOn (extendLiftSection S V (liftSectionOfComplex S F r hr hpos hJ).1) r
      (ambientOpen S V) := extension_agreement S V r

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
