import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Wikipedia.HopfProblem.CoveringManifold

/-!
# The character cocycle of an actual quotient covering

Local sections of the quotient covering determine unique deck
transformations on overlaps. These transformations satisfy the cocycle
law and are locally constant by uniqueness of local lifts. Applying a
character gives general multiplicative transition data for an actual
analytic line bundle. No coboundary or triviality is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore

variable {G A B : Type*} [Group G] [MulAction G A]
  [TopologicalSpace A] [TopologicalSpace B]
  {q : A → B} (hq : IsQuotientCoveringMap q G)

def lift (i : B) : OpenPartialHomeomorph B A :=
  CoveringQuotient.localInverse hq (CoveringQuotient.representative hq i)

def baseSet (i : B) : Set B := (lift hq i).source

theorem isOpen_baseSet (i : B) : IsOpen (baseSet hq i) := (lift hq i).open_source

theorem mem_baseSet (i : B) : i ∈ baseSet hq i := by
  have h := hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := CoveringQuotient.representative hq i)
  simpa only [baseSet, lift, CoveringQuotient.localInverse,
    CoveringQuotient.project_representative] using h

theorem lift_project (i : B) {x : B} (hx : x ∈ baseSet hq i) : q (lift hq i x) = x :=
  CoveringQuotient.project_localInverse hq _ hx

theorem lift_apply_self (i : B) : lift hq i i = CoveringQuotient.representative hq i := by
  have h := hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
    (x := CoveringQuotient.representative hq i)
  simpa only [lift, CoveringQuotient.localInverse,
    CoveringQuotient.project_representative] using h

theorem exists_deck (i j : B) {x : B} (hx : x ∈ baseSet hq i ∩ baseSet hq j) :
    ∃ g : G, g • lift hq i x = lift hq j x :=
  hq.apply_eq_iff_mem_orbit.mp ((lift_project hq j hx.2).trans (lift_project hq i hx.1).symm)

/-- The unique deck transformation from the first local lift to the second;
its irrelevant extension off the overlap is the identity. -/
def deck (i j x : B) : G := by
  classical
  exact if hx : x ∈ baseSet hq i ∩ baseSet hq j then (exists_deck hq i j hx).choose else 1

theorem deck_spec (i j : B) {x : B} (hx : x ∈ baseSet hq i ∩ baseSet hq j) :
    deck hq i j x • lift hq i x = lift hq j x := by
  classical
  rw [deck, dif_pos hx]
  exact (exists_deck hq i j hx).choose_spec

theorem deck_eq_of_smul (i j : B) {x : B} (hx : x ∈ baseSet hq i ∩ baseSet hq j)
    (g : G) (hg : g • lift hq i x = lift hq j x) : deck hq i j x = g := by
  let := hq.isCancelSMul
  exact IsCancelSMul.right_cancel _ _ (lift hq i x) ((deck_spec hq i j hx).trans hg.symm)

theorem deck_self (i : B) {x : B} (hx : x ∈ baseSet hq i) : deck hq i i x = 1 :=
  deck_eq_of_smul hq i i ⟨hx, hx⟩ 1 (one_smul G _)

theorem deck_comp (i j k : B) {x : B}
    (hx : x ∈ baseSet hq i ∩ baseSet hq j ∩ baseSet hq k) :
    deck hq j k x * deck hq i j x = deck hq i k x := by
  symm
  apply deck_eq_of_smul hq i k ⟨hx.1.1, hx.2⟩
  rw [mul_smul, deck_spec hq i j hx.1, deck_spec hq j k ⟨hx.1.2, hx.2⟩]

/-- Changes of local covering sections are locally a fixed deck transformation. -/
theorem deck_locally_constant (i j : B) {x : B}
    (hx : x ∈ baseSet hq i ∩ baseSet hq j) :
    deck hq i j =ᶠ[𝓝 x] fun _ => deck hq i j x := by
  have hU : ∀ᶠ y in 𝓝 x, y ∈ baseSet hq i ∩ baseSet hq j :=
    ((isOpen_baseSet hq i).inter (isOpen_baseSet hq j)).mem_nhds hx
  have he : (lift hq j : B → A) =ᶠ[𝓝 x] fun y => deck hq i j x • lift hq i y := by
    apply eventuallyEq_of_localHomeomorph_comp_eq hq.isCoveringMap.isLocalHomeomorph
      ((lift hq j).continuousAt hx.2)
      ((hq.continuous_const_smul (deck hq i j x)).continuousAt.comp
        ((lift hq i).continuousAt hx.1)) (deck_spec hq i j hx).symm
    filter_upwards [hU] with y hy
    change q (lift hq j y) = q (deck hq i j x • lift hq i y)
    rw [hq.map_smul, lift_project hq i hy.1, lift_project hq j hy.2]
  filter_upwards [hU, he] with y hy hey
  exact deck_eq_of_smul hq i j hy (deck hq i j x) hey.symm

variable (χ : G →* ℂˣ)

theorem transition_locally_constant (i j : B) {x : B}
    (hx : x ∈ baseSet hq i ∩ baseSet hq j) :
    (fun y => (χ (deck hq i j y) : ℂ)) =ᶠ[𝓝 x] fun _ => (χ (deck hq i j x) : ℂ) :=
  (deck_locally_constant hq i j hx).fun_comp (fun g => (χ g : ℂ))

/-- The actual character cocycle of the chosen local covering sections. -/
def data : TransitionData B B where
  baseSet := baseSet hq
  isOpen_baseSet := isOpen_baseSet hq
  indexAt := id
  mem_baseSet_at := mem_baseSet hq
  transition i j x := χ (deck hq i j x)
  transition_self i x hx := by rw [deck_self hq i hx, map_one]
  transition_comp i j k x hx := by rw [← map_mul, deck_comp hq i j k hx]
  continuousOn_transition i j x hx :=
    (transition_locally_constant hq χ i j hx).continuousAt.continuousWithinAt

@[simp] theorem data_baseSet (i : B) : (data hq χ).baseSet i = baseSet hq i := rfl

@[simp] theorem data_indexAt (x : B) : (data hq χ).indexAt x = x := rfl

@[simp] theorem data_transition (i j x : B) :
    (data hq χ).transition i j x = χ (deck hq i j x) := rfl

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]

instance data_isHolomorphic [ChartedSpace H B] (I : ModelWithCorners ℂ E H) :
    (data hq χ).IsHolomorphic I :=
  (data hq χ).isHolomorphic_of_locally_constant I fun i j _ hx =>
    transition_locally_constant hq χ i j hx

omit H [TopologicalSpace H] in
theorem lift_holomorphic [ChartedSpace E A] [IsManifold (modelWithCornersSelf ℂ E) ω A]
    (hG : ∀ g : G, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (fun a : A => g • a)) (i : B) :
    letI := CoveringQuotient.chartedSpace (E := E) hq
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (lift hq i) (baseSet hq i) :=
  CoveringQuotient.localInverse_holomorphic hq ω hG (CoveringQuotient.representative hq i)

end Wikipedia.HopfProblem.HolomorphicCharacterBundle.AssociatedCore
