import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverCompatibility

/-!
# The actual radial cover with the compact phase torus retained

The outer and inner regions below are the literal inverse images of the
proved open cover of the marked base torus. Their subtype product
homeomorphisms preserve both coordinates. Taking products of the actual
base homotopies therefore keeps the compact phase coordinate unchanged.
The two overlap inclusions become, respectively, the phase projection and
the product of the phase identity with the original circle-to-theta map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open ToricSpace

/-- The actual product of the compact fibre phases and the marked base torus. -/
abbrev PhaseBase := CompactFibreTorus × BaseTorus

/-- The outer region is the literal preimage under the second projection. -/
def phaseOuterRegion (a : ℝ) : Set PhaseBase := Prod.snd ⁻¹' outerRegion a

/-- The inner region is the literal product with the open base cell. -/
def phaseInnerRegion : Set PhaseBase := Prod.snd ⁻¹' innerRegion

/-- The actual intersection of the two phase-product regions. -/
def phaseOverlapRegion (a : ℝ) : Set PhaseBase :=
  phaseOuterRegion a ∩ phaseInnerRegion

@[simp] theorem mem_phaseOuterRegion (a : ℝ) (p : PhaseBase) :
    p ∈ phaseOuterRegion a ↔ p.2 ∈ outerRegion a := Iff.rfl

@[simp] theorem mem_phaseInnerRegion (p : PhaseBase) :
    p ∈ phaseInnerRegion ↔ p.2 ∈ innerRegion := Iff.rfl

@[simp] theorem mem_phaseOverlapRegion (a : ℝ) (p : PhaseBase) :
    p ∈ phaseOverlapRegion a ↔ p.2 ∈ overlapRegion a := Iff.rfl

theorem phaseOuterRegion_isOpen (a : ℝ) : IsOpen (phaseOuterRegion a) :=
  (outerRegion_isOpen a).preimage continuous_snd

theorem phaseInnerRegion_isOpen : IsOpen phaseInnerRegion :=
  innerRegion_isOpen.preimage continuous_snd

theorem phaseOverlapRegion_isOpen (a : ℝ) : IsOpen (phaseOverlapRegion a) :=
  (phaseOuterRegion_isOpen a).inter phaseInnerRegion_isOpen

/-- This is a genuine open cover of the original product space. -/
theorem phaseOuterRegion_union_phaseInnerRegion (a : ℝ) (ha1 : a < 1) :
    phaseOuterRegion a ∪ phaseInnerRegion = univ := by
  change Prod.snd ⁻¹' outerRegion a ∪ Prod.snd ⁻¹' innerRegion = univ
  rw [← preimage_union, outerRegion_union_innerRegion a ha1, preimage_univ]

private def phaseRegionProductHomeomorph (s : Set BaseTorus) :
    (Prod.snd ⁻¹' s : Set PhaseBase) ≃ₜ CompactFibreTorus × s where
  toFun p := (p.1.1, ⟨p.1.2, p.2⟩)
  invFun p := ⟨(p.1, (p.2 : BaseTorus)), p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The outer subspace has its inherited product topology. -/
def phaseOuterRegionHomeomorph (a : ℝ) :
    phaseOuterRegion a ≃ₜ CompactFibreTorus × outerRegion a :=
  phaseRegionProductHomeomorph (outerRegion a)

/-- The inner subspace has its inherited product topology. -/
def phaseInnerRegionHomeomorph :
    phaseInnerRegion ≃ₜ CompactFibreTorus × innerRegion :=
  phaseRegionProductHomeomorph innerRegion

/-- The overlap has its inherited product topology, with unchanged phases. -/
def phaseOverlapRegionHomeomorph (a : ℝ) :
    phaseOverlapRegion a ≃ₜ CompactFibreTorus × overlapRegion a :=
  phaseRegionProductHomeomorph (overlapRegion a)

@[simp] theorem phaseOuterRegionHomeomorph_apply (a : ℝ) (p : phaseOuterRegion a) :
    phaseOuterRegionHomeomorph a p = (p.1.1, ⟨p.1.2, p.2⟩) := rfl

@[simp] theorem phaseInnerRegionHomeomorph_apply (p : phaseInnerRegion) :
    phaseInnerRegionHomeomorph p = (p.1.1, ⟨p.1.2, p.2⟩) := rfl

@[simp] theorem phaseOverlapRegionHomeomorph_apply (a : ℝ) (p : phaseOverlapRegion a) :
    phaseOverlapRegionHomeomorph a p = (p.1.1, ⟨p.1.2, p.2⟩) := rfl

@[simp] theorem phaseOuterRegionHomeomorph_symm_coe (a : ℝ)
    (p : CompactFibreTorus × outerRegion a) :
    ((phaseOuterRegionHomeomorph a).symm p : PhaseBase) = (p.1, (p.2 : BaseTorus)) := rfl

@[simp] theorem phaseInnerRegionHomeomorph_symm_coe
    (p : CompactFibreTorus × innerRegion) :
    (phaseInnerRegionHomeomorph.symm p : PhaseBase) = (p.1, (p.2 : BaseTorus)) := rfl

@[simp] theorem phaseOverlapRegionHomeomorph_symm_coe (a : ℝ)
    (p : CompactFibreTorus × overlapRegion a) :
    ((phaseOverlapRegionHomeomorph a).symm p : PhaseBase) = (p.1, (p.2 : BaseTorus)) := rfl

/-- The original overlap inclusion into the inner phase-product region. -/
def phaseOverlapIntoInner (a : ℝ) : C(phaseOverlapRegion a, phaseInnerRegion) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The original overlap inclusion into the outer phase-product region. -/
def phaseOverlapIntoOuter (a : ℝ) : C(phaseOverlapRegion a, phaseOuterRegion a) :=
  ⟨fun p => ⟨(p : PhaseBase), p.property.1⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem phaseOverlapIntoInner_coe (a : ℝ) (p : phaseOverlapRegion a) :
    (phaseOverlapIntoInner a p : PhaseBase) = (p : PhaseBase) := rfl

@[simp] theorem phaseOverlapIntoOuter_coe (a : ℝ) (p : phaseOverlapRegion a) :
    (phaseOverlapIntoOuter a p : PhaseBase) = (p : PhaseBase) := rfl

theorem phaseOverlapIntoInner_product (a : ℝ) (p : phaseOverlapRegion a) :
    phaseInnerRegionHomeomorph (phaseOverlapIntoInner a p) =
      (p.1.1, overlapIntoInner a (phaseOverlapRegionHomeomorph a p).2) := rfl

theorem phaseOverlapIntoOuter_product (a : ℝ) (p : phaseOverlapRegion a) :
    phaseOuterRegionHomeomorph a (phaseOverlapIntoOuter a p) =
      (p.1.1, overlapIntoOuter a (phaseOverlapRegionHomeomorph a p).2) := rfl

/-- The actual outer homotopy equivalence acts only on the base coordinate. -/
def phaseOuterThetaHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    phaseOuterRegion a ≃ₕ CompactFibreTorus × Theta :=
  (phaseOuterRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl CompactFibreTorus).prodCongr
      (outerRegionThetaHomotopyEquiv a ha ha1))

@[simp] theorem phaseOuterThetaHomotopyEquiv_apply
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : phaseOuterRegion a) :
    phaseOuterThetaHomotopyEquiv a ha ha1 p =
      (p.1.1, outerRegionThetaHomotopyEquiv a ha ha1
        (phaseOuterRegionHomeomorph a p).2) := rfl

@[simp] theorem phaseOuterThetaHomotopyEquiv_symm_coe
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : CompactFibreTorus × Theta) :
    ((phaseOuterThetaHomotopyEquiv a ha ha1).symm p : PhaseBase) =
      (p.1, ((outerRegionThetaHomotopyEquiv a ha ha1).symm p.2 : BaseTorus)) := rfl

/-- Contract the actual inner base cell while keeping the phase unchanged. -/
def phaseInnerHomotopyEquiv : phaseInnerRegion ≃ₕ CompactFibreTorus :=
  phaseInnerRegionHomeomorph.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl CompactFibreTorus).prodCongr
      innerRegionPointHomotopyEquiv).trans
        (Homeomorph.prodUnique CompactFibreTorus Unit).toHomotopyEquiv)

@[simp] theorem phaseInnerHomotopyEquiv_apply (p : phaseInnerRegion) :
    phaseInnerHomotopyEquiv p = p.1.1 := rfl

@[simp] theorem phaseInnerHomotopyEquiv_symm_coe (u : CompactFibreTorus) :
    (phaseInnerHomotopyEquiv.symm u : PhaseBase) = (u, (innerRegionCenter : BaseTorus)) := rfl

/-- The actual overlap homotopy equivalence retains the phase and the
original radial circle coordinate. -/
def phaseOverlapCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    phaseOverlapRegion a ≃ₕ CompactFibreTorus × Circle :=
  (phaseOverlapRegionHomeomorph a).toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl CompactFibreTorus).prodCongr
      (overlapCircleHomotopyEquiv a ha ha1))

@[simp] theorem phaseOverlapCircleHomotopyEquiv_apply
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : phaseOverlapRegion a) :
    phaseOverlapCircleHomotopyEquiv a ha ha1 p =
      (p.1.1, overlapCircleHomotopyEquiv a ha ha1
        (phaseOverlapRegionHomeomorph a p).2) := rfl

@[simp] theorem phaseOverlapCircleHomotopyEquiv_symm_coe
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : CompactFibreTorus × Circle) :
    ((phaseOverlapCircleHomotopyEquiv a ha ha1).symm p : PhaseBase) =
      (p.1, ((overlapCircleHomotopyEquiv a ha ha1).symm p.2 : BaseTorus)) := rfl

/-- The actual inner overlap map is precisely the phase projection under
the displayed homotopy equivalences. -/
theorem phaseOverlapIntoInner_phase_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    phaseInnerHomotopyEquiv.toFun.comp (phaseOverlapIntoInner a) =
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The actual outer overlap map is the product of the unchanged phase
with the literal circle-to-theta boundary map. -/
theorem phaseOverlapIntoOuter_theta_map (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (phaseOuterThetaHomotopyEquiv a ha ha1).toFun.comp (phaseOverlapIntoOuter a) =
      ((ContinuousMap.id CompactFibreTorus).prodMap circleThetaMap).comp
        (phaseOverlapCircleHomotopyEquiv a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · exact congrArg (fun f : C(overlapRegion a, Theta) =>
      f (phaseOverlapRegionHomeomorph a p).2) (overlapIntoOuter_theta_map a ha ha1)

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
