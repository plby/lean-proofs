import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartierTensor

/-!
# Genuine sections and local-fraction identities for Cartier lines

The local fractions give a holomorphic section of the actual bundle on
the actual dense open submanifold.  The denominator germs are nonzero at
every point of every defining chart.  Continuous cross-multiplication
identities can be checked on a dense generic open and then extended to
the entire chart overlap.
-/

noncomputable section

open Set Filter Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobal

theorem eqOn_of_dense_open {M : Type*} [TopologicalSpace M] {G U : Set M}
    (hG : Dense G) (hU : IsOpen U) {f g : M → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (he : EqOn f g (U ∩ G)) :
    EqOn f g U :=
  he.of_subset_closure hf hg inter_subset_left (hG.open_subset_closure_inter hU)

namespace CartierData

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℂ E H} (D : CartierData I M ι)

/-- The section has values in the original bundle's actual fibres. -/
def meromorphicSection (x : D.genericSet) : D.associatedBundle.Fiber x.val := D.rawSection x.val

def meromorphicSectionMap (x : D.genericSet) : D.associatedBundle.TotalSpace :=
  ⟨x.val, D.meromorphicSection x⟩

@[simp] theorem meromorphicSectionMap_proj (x : D.genericSet) :
    (D.meromorphicSectionMap x).proj = x.val := rfl

theorem meromorphicSection_ne_zero (x : D.genericSet) : D.meromorphicSection x ≠ 0 :=
  D.rawSection_ne_zero x.property

/-- Holomorphicity uses the original bundle atlas and the actual open
submanifold structure, not a transported topology. -/
theorem meromorphicSectionMap_holomorphic :
    ContMDiff I (I.prod (modelWithCornersSelf ℂ ℂ)) ω D.meromorphicSectionMap := by
  intro x
  exact (D.rawSectionMap_holomorphicAt x.property).comp x (contMDiff_subtype_val x)

theorem meromorphicSectionMap_localTriv (i : ι) (x : D.genericSet)
    (hx : x.val ∈ D.transitions.baseSet i) :
    D.associatedBundle.localTriv i (D.meromorphicSectionMap x) =
      (x.val, D.localFraction i x.val) := by
  apply Prod.ext
  · rfl
  · exact D.rawSection_localCoefficient i hx x.property

/-- The denominators define nonzero holomorphic germs at every point
of their charts; density is used here, rather than merely recorded. -/
theorem denominator_not_eventually_zero (i : ι) {x : M}
    (hx : x ∈ D.transitions.baseSet i) :
    ¬ (D.denominator i =ᶠ[𝓝 x] fun _ => (0 : ℂ)) := by
  intro he
  have hU := (D.transitions.isOpen_baseSet i).mem_nhds hx
  have h : {y | y ∈ D.transitions.baseSet i ∧ D.denominator i y = 0} ∈ 𝓝 x := by
    filter_upwards [hU, he] with y hy hz
    exact ⟨hy, hz⟩
  obtain ⟨y, hyG, hy⟩ := D.genericSet_dense.inter_nhds_nonempty h
  exact D.denominator_ne_zero i y hy.1 hyG hy.2

theorem numerator_not_eventually_zero (i : ι) {x : M}
    (hx : x ∈ D.transitions.baseSet i) :
    ¬ (D.numerator i =ᶠ[𝓝 x] fun _ => (0 : ℂ)) := by
  intro he
  have hU := (D.transitions.isOpen_baseSet i).mem_nhds hx
  have h : {y | y ∈ D.transitions.baseSet i ∧ D.numerator i y = 0} ∈ 𝓝 x := by
    filter_upwards [hU, he] with y hy hz
    exact ⟨hy, hz⟩
  obtain ⟨y, hyG, hy⟩ := D.genericSet_dense.inter_nhds_nonempty h
  exact D.numerator_ne_zero i y hy.1 hyG hy.2

variable {κ : Type*} (B : CartierData I M κ)

/-- The native coefficient of the tensor section is the product of the
native coefficients of the original actual sections. -/
theorem tensor_rawSection_localCoefficient (i : ι × κ) (x : M) :
    (D.tensor B).transitions.localCoefficient (D.tensor B).rawSection i x =
      D.transitions.localCoefficient D.rawSection i.1 x *
        B.transitions.localCoefficient B.rawSection i.2 x := by
  change ((D.transitions.transition (D.transitions.indexAt x) i.1 x : ℂ) *
      (B.transitions.transition (B.transitions.indexAt x) i.2 x : ℂ)) *
      id (α := ℂ) ((D.tensor B).rawSection x) =
    ((D.transitions.transition (D.transitions.indexAt x) i.1 x : ℂ) *
      id (α := ℂ) (D.rawSection x)) *
    ((B.transitions.transition (B.transitions.indexAt x) i.2 x : ℂ) *
      id (α := ℂ) (B.rawSection x))
  have h : id (α := ℂ) ((D.tensor B).rawSection x) =
      id (α := ℂ) (D.rawSection x) * id (α := ℂ) (B.rawSection x) :=
    D.tensor_localFraction B (D.transitions.indexAt x, B.transitions.indexAt x) x
  rw [h]
  ac_rfl

end CartierData

end Wikipedia.HopfProblem.CanonicalGlobal
