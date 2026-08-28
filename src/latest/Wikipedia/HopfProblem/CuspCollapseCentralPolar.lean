import Wikipedia.HopfProblem.CuspCollapseFibreTorus
import Wikipedia.HopfProblem.CuspCollapseStabilizersBasic
import Wikipedia.HopfProblem.CuspPositiveRetractionStrong
import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy

/-!
# The actual central fibre as a phase-collapse quotient

The compact fibre torus, rather than the full three-dimensional compact
torus, suffices over the central positive part.  The height-one ray circle
absorbs the remaining phase. Multiplication is a proper quotient map onto
the literal central fibre; its exact fibres are the actual fibre-torus
stabilizers. This gives a topological quotient presentation of the genuine
central space without assuming honeycomb coordinates.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCollapse

open ToricSpace CuspRetraction CuspPositiveRetraction

/-- Every central point is a compact fibre phase of its actual modulus. -/
theorem exists_compactFibreAction_modulus {x : Space} (hx : time x = 0) :
    ∃ u : CompactFibreTorus, compactFibreAction u (modulus x) = x := by
  obtain ⟨u, hu⟩ := exists_compactTorusAction_modulus x
  have hzero : time (modulus x) = 0 := by
    simp only [time_modulus, hx, norm_zero, Complex.ofReal_zero]
  obtain ⟨v, hv⟩ := (branchVertices_nonempty (modulus x)).mpr hzero
  let w : CompactTorus := u * rayCompactPhase v (u 2)⁻¹
  have hw : w 2 = 1 := by simp only [w, Pi.mul_apply, rayCompactPhase_two, mul_inv_cancel]
  let uf : CompactFibreTorus := ![w 0, w 1]
  have hf : compactFibrePhase uf = w := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hw.symm
  refine ⟨uf, ?_⟩
  rw [compactFibreAction_eq_compact, hf]
  change compactTorusAction (u * rayCompactPhase v (u 2)⁻¹) (modulus x) = x
  rw [← compactTorusAction_mul, rayCompactPhase_fixes_of_mem_rayDivisor v (u 2)⁻¹ hv]
  exact hu

/-- The positive central locus has its literal closed-subspace topology. -/
theorem positiveCentral_isClosed :
    IsClosed {q : PositivePart | time (q : Space) = 0} :=
  isClosed_eq (time_holomorphic.continuous.comp continuous_subtype_val) continuous_const

theorem positiveCentralVal_isClosedEmbedding :
    IsClosedEmbedding (fun q : PositiveCentralFibre => (q.1 : Space)) :=
  positivePart_isClosed.isClosedEmbedding_subtypeVal.comp
    positiveCentral_isClosed.isClosedEmbedding_subtypeVal

/-- Phase multiplication into the actual central fibre. -/
def centralPolarMap (p : CompactFibreTorus × PositiveCentralFibre) : CentralFibre :=
  ⟨compactFibreAction p.1 (p.2.1 : Space), by rw [time_compactFibreAction, p.2.2]⟩

@[simp] theorem centralPolarMap_coe (p : CompactFibreTorus × PositiveCentralFibre) :
    (centralPolarMap p : Space) = compactFibreAction p.1 (p.2.1 : Space) := rfl

theorem centralPolarMap_continuous : Continuous centralPolarMap :=
  (compactFibreAction_continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_subtype_val).comp
      continuous_snd))).subtype_mk _

@[simp] theorem modulus_centralPolarMap (p : CompactFibreTorus × PositiveCentralFibre) :
    modulus (centralPolarMap p : Space) = (p.2.1 : Space) := by
  rw [centralPolarMap_coe, modulus_compactFibreAction]
  exact p.2.1.2

def centralModulus (x : CentralFibre) : PositiveCentralFibre :=
  ⟨modulusRetraction x, by simp only [modulusRetraction_coe, time_modulus, x.2,
    norm_zero, Complex.ofReal_zero]⟩

theorem centralModulus_continuous : Continuous centralModulus :=
  (modulusRetraction_continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem centralModulus_centralPolarMap (p : CompactFibreTorus × PositiveCentralFibre) :
    centralModulus (centralPolarMap p) = p.2 :=
  Subtype.ext (Subtype.ext (modulus_centralPolarMap p))

theorem centralPolarMap_surjective : Function.Surjective centralPolarMap := by
  intro x
  obtain ⟨u, hu⟩ := exists_compactFibreAction_modulus x.2
  exact ⟨(u, centralModulus x), Subtype.ext hu⟩

theorem centralPolarMap_isProperMap : IsProperMap centralPolarMap := by
  have hinc : IsProperMap
      (fun p : CompactFibreTorus × PositiveCentralFibre => (p.1, (p.2.1 : Space))) :=
    ((Homeomorph.refl CompactFibreTorus).isClosedEmbedding.prodMap
      positiveCentralVal_isClosedEmbedding).isProperMap
  have hcomp : IsProperMap ((Subtype.val : CentralFibre → Space) ∘ centralPolarMap) :=
    compactFibreAction_isProperMap.comp hinc
  exact isProperMap_of_comp_of_inj centralPolarMap_continuous continuous_subtype_val
    hcomp Subtype.val_injective

theorem centralPolarMap_isClosedMap : IsClosedMap centralPolarMap :=
  centralPolarMap_isProperMap.isClosedMap

/-- This quotient map describes the inherited topology of the genuine
central fibre, not a topology assigned to a model after the fact. -/
theorem centralPolarMap_isQuotientMap : IsQuotientMap centralPolarMap :=
  centralPolarMap_isClosedMap.isQuotientMap centralPolarMap_continuous centralPolarMap_surjective

/-- The positive coordinate is unique, and the phase ambiguity is exactly
the stabilizer in the two-dimensional fibre torus. -/
theorem centralPolarMap_eq_iff (p q : CompactFibreTorus × PositiveCentralFibre) :
    centralPolarMap p = centralPolarMap q ↔ p.2 = q.2 ∧
      p.1⁻¹ * q.1 ∈ MulAction.stabilizer CompactFibreTorus (p.2.1 : Space) := by
  rcases p with ⟨u, x⟩
  rcases q with ⟨v, y⟩
  constructor
  · intro h
    have hxy : x = y := by
      simpa only [centralModulus_centralPolarMap] using congrArg centralModulus h
    subst y
    refine ⟨rfl, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    have he : u • (x.1 : Space) = v • (x.1 : Space) := congrArg Subtype.val h
    rw [mul_smul, ← he, inv_smul_smul]
  · rintro ⟨hxy, h⟩
    change x = y at hxy
    subst y
    have hs := congrArg (fun z : Space => u • z) (MulAction.mem_stabilizer_iff.mp h)
    apply Subtype.ext
    change u • (x.1 : Space) = v • (x.1 : Space)
    simpa only [smul_smul, mul_inv_cancel_left] using hs.symm

/-- The explicit phase-collapse equivalence relation. -/
def centralPhaseSetoid : Setoid (CompactFibreTorus × PositiveCentralFibre) where
  r p q := p.2 = q.2 ∧
    p.1⁻¹ * q.1 ∈ MulAction.stabilizer CompactFibreTorus (p.2.1 : Space)
  iseqv :=
    { refl := fun p => (centralPolarMap_eq_iff p p).mp rfl
      symm := fun {p q} h => (centralPolarMap_eq_iff q p).mp
        ((centralPolarMap_eq_iff p q).mpr h).symm
      trans := fun {p q r} hpq hqr => (centralPolarMap_eq_iff p r).mp
        (((centralPolarMap_eq_iff p q).mpr hpq).trans ((centralPolarMap_eq_iff q r).mpr hqr)) }

abbrev CentralPhaseQuotient := Quotient centralPhaseSetoid

def centralPhaseMap : CentralPhaseQuotient → CentralFibre :=
  Quotient.lift centralPolarMap (fun p q h => (centralPolarMap_eq_iff p q).mpr h)

@[simp] theorem centralPhaseMap_mk (p : CompactFibreTorus × PositiveCentralFibre) :
    centralPhaseMap (Quotient.mk centralPhaseSetoid p) = centralPolarMap p := rfl

theorem centralPhaseMap_continuous : Continuous centralPhaseMap :=
  centralPolarMap_continuous.quotient_lift _

theorem centralPhaseMap_bijective : Function.Bijective centralPhaseMap := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        intro h
        exact Quotient.sound ((centralPolarMap_eq_iff p q).mp h)
  · intro x
    obtain ⟨p, hp⟩ := centralPolarMap_surjective x
    exact ⟨Quotient.mk centralPhaseSetoid p, hp⟩

def centralPhaseEquiv : CentralPhaseQuotient ≃ CentralFibre :=
  Equiv.ofBijective centralPhaseMap centralPhaseMap_bijective

@[simp] theorem centralPhaseEquiv_symm_centralPolarMap
    (p : CompactFibreTorus × PositiveCentralFibre) :
    centralPhaseEquiv.symm (centralPolarMap p) = Quotient.mk centralPhaseSetoid p := by
  apply centralPhaseEquiv.injective
  rw [centralPhaseEquiv.apply_symm_apply]
  rfl

/-- The actual central fibre is homeomorphic to its explicit phase-collapse
quotient. The stabilizers in this relation are calculated stratum by stratum. -/
def centralPhaseHomeomorph : CentralPhaseQuotient ≃ₜ CentralFibre where
  toEquiv := centralPhaseEquiv
  continuous_toFun := centralPhaseMap_continuous
  continuous_invFun := by
    apply centralPolarMap_isQuotientMap.continuous_iff.mpr
    change Continuous (centralPhaseEquiv.symm ∘ centralPolarMap)
    have he : centralPhaseEquiv.symm ∘ centralPolarMap = Quotient.mk centralPhaseSetoid :=
      funext centralPhaseEquiv_symm_centralPolarMap
    rw [he]
    exact continuous_quotient_mk'

@[simp] theorem centralPhaseHomeomorph_mk (p : CompactFibreTorus × PositiveCentralFibre) :
    centralPhaseHomeomorph (Quotient.mk centralPhaseSetoid p) = centralPolarMap p := rfl

end Wikipedia.HopfProblem.CuspCollapse
