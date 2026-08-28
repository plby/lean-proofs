import Wikipedia.HopfProblem.CuspCollapseCentralPolar
import Wikipedia.HopfProblem.CuspCollapseStabilizers

/-!
# The exact central phase-collapse fibres in the three chart strata

Over an open component stratum the actual central phase map is injective.
Over an open double curve its ambiguity is precisely the vertex-difference
circle, and over a chart origin all fibre phases agree.  The open-component
phase orbit has the topology of the actual compact two-torus.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCollapse

open ToricCharts ToricFan ToricSpace CuspRetraction CuspPositiveRetraction

/-- Chart coordinates retain exactly the phases attached to nonzero coordinates. -/
theorem centralPolarMap_eq_iff_coordinatePhase (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (u v : CompactFibreTorus) :
    centralPolarMap (u, q) = centralPolarMap (v, q) ↔
      ∀ i, z i ≠ 0 → fibreCoordinatePhase s u i = fibreCoordinatePhase s v i := by
  rw [Subtype.ext_iff]
  change compactFibreAction u (q.1 : Space) = compactFibreAction v (q.1 : Space) ↔ _
  rw [compactFibreAction_eq_compact, compactFibreAction_eq_compact, hq]
  change torusAction (compactTorusUnits (compactFibrePhase u)) (inclusion s z) =
    torusAction (compactTorusUnits (compactFibrePhase v)) (inclusion s z) ↔ _
  rw [torusAction_inclusion, torusAction_inclusion, (inclusion_openEmbedding s).injective.eq_iff]
  constructor
  · intro h i hi
    apply Circle.ext
    apply mul_right_cancel₀ hi
    exact congrFun h i
  · intro h
    funext i
    change factors s (compactTorusUnits (compactFibrePhase u)) i * z i =
      factors s (compactTorusUnits (compactFibrePhase v)) i * z i
    by_cases hi : z i = 0
    · simp only [hi, mul_zero]
    · exact congrArg (fun a : Circle => (a : ℂ) * z i) (h i hi)

theorem centralPolarMap_same_base_eq_iff (q : PositiveCentralFibre)
    (u v : CompactFibreTorus) :
    centralPolarMap (u, q) = centralPolarMap (v, q) ↔
      compactFibreAction (u⁻¹ * v) (q.1 : Space) = (q.1 : Space) := by
  rw [centralPolarMap_eq_iff]
  simp only [true_and, MulAction.mem_stabilizer_iff]
  rfl

/-- No phase is collapsed on an open component stratum. -/
theorem centralPolarMap_eq_iff_of_at_most_one_zero (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) (u v : CompactFibreTorus) :
    centralPolarMap (u, q) = centralPolarMap (v, q) ↔ u = v := by
  rw [centralPolarMap_same_base_eq_iff, hq,
    compactFibreAction_inclusion_eq_self_iff_of_at_most_one_zero _ s z j hz,
    inv_mul_eq_one]

/-- On an open double curve, exactly its integral edge-direction circle
is collapsed, in the original two-dimensional fibre torus. -/
theorem centralPolarMap_eq_iff_of_two_zero (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j k : Fin 3) (hjk : j ≠ k) (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) (u v : CompactFibreTorus) :
    centralPolarMap (u, q) = centralPolarMap (v, q) ↔
      ∃ a : Circle, ∀ i : Fin 2, (u i)⁻¹ * v i = a ^ (s.vertex k i - s.vertex j i) := by
  rw [centralPolarMap_same_base_eq_iff, hq,
    compactFibreAction_inclusion_eq_self_iff_of_two_zero _ s z j k hjk hzj hzk hz]
  rfl

/-- The phase orbit over an actual triple point consists of one point. -/
theorem centralPolarMap_eq_of_chart_origin (q : PositiveCentralFibre)
    (s : Triangle) (hq : (q.1 : Space) = inclusion s 0) (u v : CompactFibreTorus) :
    centralPolarMap (u, q) = centralPolarMap (v, q) := by
  apply (centralPolarMap_same_base_eq_iff q u v).mpr
  rw [hq]
  exact compactFibreAction_inclusion_zero _ s

/-- The phase orbit as a map into the literal central toric fibre. -/
def centralPhaseOrbit (q : PositiveCentralFibre) (u : CompactFibreTorus) : CentralFibre :=
  centralPolarMap (u, q)

@[simp] theorem centralPhaseOrbit_apply (q : PositiveCentralFibre) (u : CompactFibreTorus) :
    centralPhaseOrbit q u = centralPolarMap (u, q) := rfl

theorem centralPhaseOrbit_continuous (q : PositiveCentralFibre) :
    Continuous (centralPhaseOrbit q) :=
  centralPolarMap_continuous.comp (continuous_id.prodMk continuous_const)

/-- The literal fibre of the modulus projection, with its inherited topology. -/
abbrev CentralModulusFibre (q : PositiveCentralFibre) := {x : CentralFibre // centralModulus x = q}

def centralPhaseOrbitToFibre (q : PositiveCentralFibre) (u : CompactFibreTorus) :
    CentralModulusFibre q := ⟨centralPhaseOrbit q u, centralModulus_centralPolarMap (u, q)⟩

@[simp] theorem centralPhaseOrbitToFibre_coe (q : PositiveCentralFibre)
    (u : CompactFibreTorus) :
    (centralPhaseOrbitToFibre q u : CentralFibre) = centralPhaseOrbit q u := rfl

theorem centralPhaseOrbitToFibre_continuous (q : PositiveCentralFibre) :
    Continuous (centralPhaseOrbitToFibre q) := (centralPhaseOrbit_continuous q).subtype_mk _

theorem centralPhaseOrbitToFibre_surjective (q : PositiveCentralFibre) :
    Function.Surjective (centralPhaseOrbitToFibre q) := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨u, r⟩, rfl⟩ := centralPolarMap_surjective x
  rw [centralModulus_centralPolarMap] at hx
  change r = q at hx
  subst r
  exact ⟨u, rfl⟩

/-- The full two-torus is embedded, with the actual ambient topology,
over an open component stratum. -/
theorem centralPhaseOrbit_isClosedEmbedding_of_at_most_one_zero (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) : IsClosedEmbedding (centralPhaseOrbit q) :=
  (centralPhaseOrbit_continuous q).isClosedEmbedding fun u v h =>
    (centralPolarMap_eq_iff_of_at_most_one_zero q s z hq j hz u v).mp h

/-- The phase orbit over an open central component is the genuine
compact two-torus, as a homeomorphism onto the literal modulus fibre. -/
def centralModulusFibreTorusHomeomorph (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) :
    CompactFibreTorus ≃ₜ CentralModulusFibre q :=
  ((centralPhaseOrbitToFibre_continuous q).isClosedEmbedding
    (fun u v h => (centralPolarMap_eq_iff_of_at_most_one_zero q s z hq j hz u v).mp
      (congrArg Subtype.val h))).toIsEmbedding.toHomeomorphOfSurjective
    (centralPhaseOrbitToFibre_surjective q)

@[simp] theorem centralModulusFibreTorusHomeomorph_coe (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j : Fin 3) (hz : ∀ i, i ≠ j → z i ≠ 0) (u : CompactFibreTorus) :
    (centralModulusFibreTorusHomeomorph q s z hq j hz u : CentralFibre) =
      centralPolarMap (u, q) := rfl

theorem centralModulusFibre_subsingleton_of_chart_origin (q : PositiveCentralFibre)
    (s : Triangle) (hq : (q.1 : Space) = inclusion s 0) : Subsingleton (CentralModulusFibre q) := by
  constructor
  intro x y
  obtain ⟨u, rfl⟩ := centralPhaseOrbitToFibre_surjective q x
  obtain ⟨v, rfl⟩ := centralPhaseOrbitToFibre_surjective q y
  exact Subtype.ext (centralPolarMap_eq_of_chart_origin q s hq u v)

/-- A fibre phase whose chart phase at `l` is the specified circle element,
compensated at a different coordinate `j`. -/
def centralCoordinateCirclePhase (s : Triangle) (j l : Fin 3) (a : Circle) : CompactFibreTorus :=
  fun i => a ^ (s.vertex l i - s.vertex j i)

theorem centralCoordinateCirclePhase_continuous (s : Triangle) (j l : Fin 3) :
    Continuous (centralCoordinateCirclePhase s j l) := by
  apply continuous_pi
  intro i
  exact continuous_id.zpow (s.vertex l i - s.vertex j i)

theorem fibreCoordinatePhase_centralCoordinateCirclePhase (s : Triangle)
    (j l : Fin 3) (hjl : j ≠ l) (a : Circle) :
    fibreCoordinatePhase s (centralCoordinateCirclePhase s j l a) l = a := by
  apply Circle.ext
  rw [fibreCoordinatePhase_coe, compactTorusUnits_compactFibrePhase]
  change factors s (fibreMultiplier
    (compactFibreUnits (fun i => a ^ (s.vertex l i - s.vertex j i)))) l = (a : ℂ)
  rw [factors_vertexDifferencePhase]
  simp [hjl.symm]

/-- The circle parametrization inside the literal central modulus fibre. -/
def centralCircleOrbit (q : PositiveCentralFibre) (s : Triangle) (j l : Fin 3) (a : Circle) :
    CentralModulusFibre q := centralPhaseOrbitToFibre q (centralCoordinateCirclePhase s j l a)

theorem centralCircleOrbit_continuous (q : PositiveCentralFibre) (s : Triangle) (j l : Fin 3) :
    Continuous (centralCircleOrbit q s j l) :=
  (centralPhaseOrbitToFibre_continuous q).comp (centralCoordinateCirclePhase_continuous s j l)

theorem centralCircleOrbit_injective (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j l : Fin 3) (hjl : j ≠ l) (hzl : z l ≠ 0) :
    Function.Injective (centralCircleOrbit q s j l) := by
  intro a b hab
  have he : centralPolarMap (centralCoordinateCirclePhase s j l a, q) =
      centralPolarMap (centralCoordinateCirclePhase s j l b, q) :=
    congrArg (fun x : CentralModulusFibre q => x.1) hab
  have hh := (centralPolarMap_eq_iff_coordinatePhase q s z hq _ _).mp he l hzl
  rwa [fibreCoordinatePhase_centralCoordinateCirclePhase s j l hjl,
    fibreCoordinatePhase_centralCoordinateCirclePhase s j l hjl] at hh

theorem centralCircleOrbit_surjective (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j l : Fin 3) (hjl : j ≠ l) (hz : ∀ i, i ≠ l → z i = 0) :
    Function.Surjective (centralCircleOrbit q s j l) := by
  intro x
  obtain ⟨u, rfl⟩ := centralPhaseOrbitToFibre_surjective q x
  refine ⟨fibreCoordinatePhase s u l, ?_⟩
  apply Subtype.ext
  apply (centralPolarMap_eq_iff_coordinatePhase q s z hq _ _).mpr
  intro i hi
  have hil : i = l := by
    by_contra h
    exact hi (hz i h)
  subst i
  exact fibreCoordinatePhase_centralCoordinateCirclePhase s j l hjl _

/-- With just one nonzero chart coordinate, the actual modulus fibre is
an ordinary circle, not just an abstract orbit with circle stabilizer. -/
def centralModulusFibreCircleHomeomorph (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j l : Fin 3) (hjl : j ≠ l) (hzl : z l ≠ 0) (hz : ∀ i, i ≠ l → z i = 0) :
    Circle ≃ₜ CentralModulusFibre q :=
  ((centralCircleOrbit_continuous q s j l).isClosedEmbedding
    (centralCircleOrbit_injective q s z hq j l hjl hzl)).toIsEmbedding.toHomeomorphOfSurjective
    (centralCircleOrbit_surjective q s z hq j l hjl hz)

@[simp] theorem centralModulusFibreCircleHomeomorph_coe (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j l : Fin 3) (hjl : j ≠ l) (hzl : z l ≠ 0) (hz : ∀ i, i ≠ l → z i = 0) (a : Circle) :
    (centralModulusFibreCircleHomeomorph q s z hq j l hjl hzl hz a : CentralFibre) =
      centralPolarMap (centralCoordinateCirclePhase s j l a, q) := rfl

private theorem exists_remainingIndex (j k : Fin 3) (hjk : j ≠ k) :
    ∃ l : Fin 3, l ≠ j ∧ l ≠ k ∧ ∀ i : Fin 3, i ≠ l → i = j ∨ i = k := by
  fin_cases j <;> fin_cases k <;> first | exact (hjk rfl).elim | decide

/-- The two-zero-coordinate formulation of the actual circle fibre. -/
def centralModulusFibreCircleHomeomorph_of_two_zero (q : PositiveCentralFibre)
    (s : Triangle) (z : CoordinateSpace 3) (hq : (q.1 : Space) = inclusion s z)
    (j k : Fin 3) (hjk : j ≠ k) (hzj : z j = 0) (hzk : z k = 0)
    (hz : ∀ i, i ≠ j → i ≠ k → z i ≠ 0) : Circle ≃ₜ CentralModulusFibre q := by
  let l := (exists_remainingIndex j k hjk).choose
  have hl : l ≠ j ∧ l ≠ k ∧ ∀ i : Fin 3, i ≠ l → i = j ∨ i = k :=
    (exists_remainingIndex j k hjk).choose_spec
  apply centralModulusFibreCircleHomeomorph q s z hq j l hl.1.symm (hz l hl.1 hl.2.1)
  intro i hi
  rcases hl.2.2 i hi with rfl | rfl
  · exact hzj
  · exact hzk

end Wikipedia.HopfProblem.CuspCollapse
