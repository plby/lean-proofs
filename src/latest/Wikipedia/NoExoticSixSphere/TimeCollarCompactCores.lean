import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sets.Compacts

/-!
# Actual boundary collars and cofinal compact cores of a collared half

The strict interior is the original positive-time open submanifold. Its
inclusion into the half factors through the literal interior subset by
a homeomorphism fixing ambient points. Positive time thresholds give
compact cores, cofinal among all compact supports, and their complements
are the actual collar regions used for relative excision.
-/

noncomputable section

open Set Function TopologicalSpace ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def boundary (t : M → ℝ) : Set (NonnegativeHalf t) := {p | t p.val = 0}

def interiorDomain : Opens (NonnegativeHalf t) :=
  ⟨{p | 0 < t p.val}, isOpen_lt continuous_const
    (C.continuous_time.comp continuous_subtype_val)⟩

def collarRegion (δ : ℝ) : Opens (NonnegativeHalf t) :=
  ⟨{p | t p.val < δ}, isOpen_lt (C.continuous_time.comp continuous_subtype_val) continuous_const⟩

theorem boundary_subset_collar (δ : ℝ) (hδ : 0 < δ) :
    boundary t ⊆ collarRegion C δ := by
  intro p hp
  change t p.val < δ
  change t p.val = 0 at hp
  rwa [hp]

theorem interior_collar_cover (δ : ℝ) (hδ : 0 < δ) :
    (interiorDomain C : Set (NonnegativeHalf t)) ∪ collarRegion C δ = univ := by
  apply eq_univ_of_forall
  intro p
  by_cases hp : t p.val = 0
  · exact Or.inr (by change t p.val < δ; rwa [hp])
  · exact Or.inl (lt_of_le_of_ne p.property (Ne.symm hp))

def interiorHomeomorph : C.positiveInterior ≃ₜ interiorDomain C where
  toFun p := ⟨⟨p.val, p.property.le⟩, p.property⟩
  invFun p := ⟨p.val.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem interiorHomeomorph_inclusion :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(interiorDomain C, NonnegativeHalf t)).comp
      ⟨interiorHomeomorph C, (interiorHomeomorph C).continuous⟩ = C.interiorToHalf := rfl

def interiorTime : C(C.positiveInterior, ℝ) :=
  ⟨fun p ↦ t p.val, C.continuous_time.comp continuous_subtype_val⟩

theorem exists_inner_time_below_compact (K : Compacts C.positiveInterior) :
    ∃ δ : ℝ, 0 < δ ∧ δ < C.width ∧ ∀ p ∈ K, δ < interiorTime C p := by
  by_cases hne : (K : Set C.positiveInterior).Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ :=
      K.isCompact.exists_isMinOn hne (interiorTime C).continuous.continuousOn
    let δ := min (C.width / 2) (interiorTime C p₀ / 2)
    have hp : 0 < interiorTime C p₀ := p₀.property
    refine ⟨δ, lt_min (half_pos C.width_pos) (half_pos hp),
      (min_le_left _ _).trans_lt (half_lt_self C.width_pos), ?_⟩
    intro p hpK
    exact ((min_le_right _ _).trans_lt (half_lt_self hp)).trans_le (hmin hpK)
  · exact ⟨C.width / 2, half_pos C.width_pos, half_lt_self C.width_pos,
      fun p hp ↦ (hne ⟨p, hp⟩).elim⟩

def coreInclusion (δ : ℝ) (hδ : 0 < δ) : C({p : M // δ ≤ t p}, C.positiveInterior) :=
  ⟨fun p ↦ ⟨p.val, hδ.trans_le p.property⟩, continuous_subtype_val.subtype_mk _⟩

variable [CompactSpace M]

def compactCore (δ : ℝ) (hδ : 0 < δ) : Compacts C.positiveInterior := by
  let : CompactSpace {p : M // δ ≤ t p} :=
    (isClosed_le continuous_const C.continuous_time).isClosedEmbedding_subtypeVal.compactSpace
  exact ⟨range (coreInclusion C δ hδ), isCompact_range (coreInclusion C δ hδ).continuous⟩

theorem mem_compactCore_iff (δ : ℝ) (hδ : 0 < δ) (p : C.positiveInterior) :
    p ∈ compactCore C δ hδ ↔ δ ≤ t p.val := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val, hp⟩, rfl⟩

theorem compactCore_cofinal (K : Compacts C.positiveInterior) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ < C.width ∧ K ≤ compactCore C δ hδ := by
  obtain ⟨δ, hδ, hδw, hK⟩ := exists_inner_time_below_compact C K
  refine ⟨δ, hδ, hδw, ?_⟩
  intro p hp
  exact (mem_compactCore_iff C δ hδ p).mpr (hK p hp).le

theorem compactCore_mono (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    compactCore C δ hδ ≤ compactCore C ε hε := by
  intro p hp
  exact (mem_compactCore_iff C ε hε p).mpr (hεδ.trans ((mem_compactCore_iff C δ hδ p).mp hp))

theorem coreComplement_mapsTo_collar (δ : ℝ) (hδ : 0 < δ) :
    MapsTo C.interiorToHalf (compactCore C δ hδ : Set C.positiveInterior)ᶜ (collarRegion C δ) := by
  intro p hp
  change t p.val < δ
  exact lt_of_not_ge (fun h ↦ hp ((mem_compactCore_iff C δ hδ p).mpr h))

end NoExoticSixSphere.TimeCollarDuality
