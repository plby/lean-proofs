import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardReconstructionLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsGluing

/-!
# Global native reconstruction on each original base open

The actual finite and cusp canonical sections glue in the sheaf of
holomorphic maps to the original canonical total space. The resulting
section is defined over the entire inverse image of the original open,
and retains the literal finite and cusp formulas.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Reconstruction

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The genuine two-open cover of the full preimage. -/
def covering (U : Opens RiemannSphere) : Bool → Opens Threefold.Space
  | false => Threefold.basePreimage (finiteBase U)
  | true => Threefold.basePreimage (Cusp.localBase U)

theorem covering_le (U : Opens RiemannSphere) (b : Bool) :
    covering U b ≤ Threefold.basePreimage U := by
  cases b <;> exact Threefold.basePreimage_mono inf_le_left

theorem covering_cover (U : Opens RiemannSphere) :
    Threefold.basePreimage U ≤ iSup (covering U) := by
  intro x hx
  have hp : Threefold.projectionSphere x ∈ finiteBase U ⊔ Cusp.localBase U := by
    rw [finiteBase_sup_cuspBase]
    exact hx
  rcases hp with hfin | hcusp
  · exact Opens.mem_iSup.mpr ⟨false, hfin⟩
  · exact Opens.mem_iSup.mpr ⟨true, hcusp⟩

/-- The already proved native local canonical sections on this cover. -/
def coveringSection (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    ∀ b : Bool, Section (covering U b)
  | false => finiteSection U h
  | true => cuspSection U h

theorem coveringSection_compatible (U : Opens RiemannSphere) (h : NegativeOneSection U)
    (a b : Bool) :
    restrictSection inf_le_left (coveringSection U h a) =
      restrictSection inf_le_right (coveringSection U h b) := by
  cases a <;> cases b
  · apply section_ext
    intro x
    rfl
  · apply section_ext
    intro x
    exact finiteSection_eq_cuspSection U h ⟨x.val, ⟨x.property.1, x.property.2⟩⟩
  · apply section_ext
    intro x
    exact (finiteSection_eq_cuspSection U h ⟨x.val, ⟨x.property.2, x.property.1⟩⟩).symm
  · apply section_ext
    intro x
    rfl

/-- Every actual ideal section reconstructs an actual native canonical
section on the full preimage, with both exact local formulas. -/
theorem exists_section (U : Opens RiemannSphere) (h : NegativeOneSection U) :
    ∃ s : PreimageSection U,
      (∀ x : Threefold.basePreimage (finiteBase U),
        s ⟨x.val, x.property.1⟩ = finiteSection U h x) ∧
      (∀ x : Threefold.basePreimage (Cusp.localBase U),
        s ⟨x.val, x.property.1⟩ = cuspSection U h x) := by
  obtain ⟨s, hs, _⟩ := NativeBundleSections.Section.existsUnique_gluing
    Threefold.Canonical.bundle IF (covering U) (coveringSection U h)
      (coveringSection_compatible U h)
  let t : PreimageSection U := restrictSection (covering_cover U) s
  refine ⟨t, ?_, ?_⟩
  · intro x
    exact congrArg (fun q : Section (covering U false) => q x) (hs false)
  · intro x
    exact congrArg (fun q : Section (covering U true) => q x) (hs true)

/-- Reconstruction of an actual ideal section into the original native
canonical fibres. Holomorphicity is part of the codomain section type. -/
def sectionOfIdeal (U : Opens RiemannSphere) (h : NegativeOneSection U) : PreimageSection U :=
  (exists_section U h).choose

theorem sectionOfIdeal_finite (U : Opens RiemannSphere) (h : NegativeOneSection U)
    (x : Threefold.basePreimage (finiteBase U)) :
    sectionOfIdeal U h ⟨x.val, x.property.1⟩ = finiteSection U h x :=
  (exists_section U h).choose_spec.1 x

theorem sectionOfIdeal_cusp (U : Opens RiemannSphere) (h : NegativeOneSection U)
    (x : Threefold.basePreimage (Cusp.localBase U)) :
    sectionOfIdeal U h ⟨x.val, x.property.1⟩ = cuspSection U h x :=
  (exists_section U h).choose_spec.2 x

/-- At every finite base value the reconstructed native section is
literally `h(f(x)) Ω(x)`, also at the zero divisor of Ω. -/
theorem sectionOfIdeal_apply_of_ne_infty (U : Opens RiemannSphere)
    (h : NegativeOneSection U) (x : Threefold.basePreimage U)
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    sectionOfIdeal U h x = h.val (Threefold.baseProjection U x) •
      GlobalMeromorphicSection.rawSection x.val := by
  exact (sectionOfIdeal_finite U h
    ⟨x.val, ⟨x.property, (NegativeOneFrames.mem_finiteChart _).mpr hx⟩⟩).trans
      (finiteSection_apply U h _)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Reconstruction
