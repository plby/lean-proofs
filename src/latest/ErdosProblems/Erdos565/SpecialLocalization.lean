import ErdosProblems.Erdos565.SpecialContainerBridge
import Mathlib.Tactic

/-!
# Fixed-container localisation for the specialised container theorem

This file proves the Section 7 localisation step of
Aragão--Campos--Dahia--Filipe--Marciano.  The statement is deliberately
separated from the fingerprint assembly: it starts with one non-Janson
container for the uniformised conditional cover and produces the large
subcontainer on which the projected copy hypergraph is non-Janson.

The proof uses only finite sums.  In particular, the bounded-one-degree
witness is the infimum/near-minimiser construction in `BoundedDegree`, and
all conditional expectations are the explicit weighted `Finset` sums from
`FiniteExpectation`.
-/

open scoped BigOperators NNReal

namespace Erdos565
namespace SpecialLocalization

open Hypergraph

variable {V U : Type*}

section WeightRestriction

variable [Fintype V] [DecidableEq V]

/-- Restrict a weight to the edges of a subhypergraph. -/
noncomputable def restrictWeight (K : Hypergraph V) {H : Hypergraph V}
    (nu : EdgeWeight H) : EdgeWeight K :=
  fun E => if E ∈ K then nu E else 0

@[simp] theorem restrictWeight_apply_of_mem {K H : Hypergraph V}
    (nu : EdgeWeight H) {E : Finset V} (hE : E ∈ K) :
    restrictWeight K nu E = nu E := by
  simp [restrictWeight, hE]

@[simp] theorem restrictWeight_apply_of_not_mem {K H : Hypergraph V}
    (nu : EdgeWeight H) {E : Finset V} (hE : E ∉ K) :
    restrictWeight K nu E = 0 := by
  simp [restrictWeight, hE]

theorem mass_restrictWeight (K : Hypergraph V) {H : Hypergraph V}
    (nu : EdgeWeight H) :
    mass K (restrictWeight K nu) = ∑ E ∈ K, (nu E : ℝ) := by
  apply Finset.sum_congr rfl
  intro E hE
  simp [mass, restrictWeight, hE]

theorem weightedDegree_restrictWeight (K : Hypergraph V) {H : Hypergraph V}
    (nu : EdgeWeight H) (L : Finset V) :
    weightedDegree K (restrictWeight K nu) L =
      ∑ E ∈ K with L ⊆ E, (nu E : ℝ) := by
  apply Finset.sum_congr rfl
  intro E hE
  simp [weightedDegree, restrictWeight, (Finset.mem_filter.mp hE).1]

/-- Passing to a subhypergraph and restricting the weight cannot increase
the Janson energy. -/
theorem Lambda_restrictWeight_le {K H : Hypergraph V} (hKH : K ⊆ H)
    {p : ℝ} (hp : 0 < p) (nu : EdgeWeight H) :
    Lambda K p (restrictWeight K nu) ≤ Lambda H p nu := by
  rw [Lambda, Lambda]
  apply Finset.sum_le_sum
  intro L hL
  have hdeg : weightedDegree K (restrictWeight K nu) L ≤
      weightedDegree H nu L := by
    rw [weightedDegree_restrictWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro E hE
        obtain ⟨hEK, hLE⟩ := Finset.mem_filter.mp hE
        exact Finset.mem_filter.mpr ⟨hKH hEK, hLE⟩)
      (fun E _ _ => NNReal.coe_nonneg (nu E))
  have hK0 := weightedDegree_nonneg K (restrictWeight K nu) L
  have hH0 := weightedDegree_nonneg H nu L
  have hsquare : weightedDegree K (restrictWeight K nu) L ^ 2 ≤
      weightedDegree H nu L ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right hsquare (pow_pos hp _).le

/-- The mass of a weight splits over a hypergraph and its complement inside
a larger hypergraph. -/
theorem mass_inter_add_sdiff (H C : Hypergraph V) (nu : EdgeWeight H) :
    mass (H ∩ C) (restrictWeight (H ∩ C) nu) +
        mass (H \ C) (restrictWeight (H \ C) nu) = mass H nu := by
  rw [mass_restrictWeight, mass_restrictWeight, mass]
  have hi : H.filter (fun E => E ∈ C) = H ∩ C := by
    ext E
    simp
  have hd : H.filter (fun E => E ∉ C) = H \ C := by
    ext E
    simp
  rw [← hi, ← hd]
  exact Finset.sum_filter_add_sum_filter_not H (fun E => E ∈ C)
    (fun E => (nu E : ℝ))

/-- Restricting a weight to more edges can only increase its mass. -/
theorem mass_restrictWeight_mono {K L H : Hypergraph V} (hKL : K ⊆ L)
    (nu : EdgeWeight H) :
    mass K (restrictWeight K nu) ≤ mass L (restrictWeight L nu) := by
  rw [mass_restrictWeight, mass_restrictWeight]
  exact Finset.sum_le_sum_of_subset_of_nonneg hKL
    (fun E _ _ => NNReal.coe_nonneg (nu E))

theorem singletonEnergy_restrictWeight_le {K H : Hypergraph V}
    (hKH : K ⊆ H) (nu : EdgeWeight H) :
    singletonEnergy K (restrictWeight K nu) ≤ singletonEnergy H nu := by
  unfold singletonEnergy
  apply Finset.sum_le_sum
  intro u hu
  have hdeg : weightedDegree K (restrictWeight K nu) {u} ≤
      weightedDegree H nu {u} := by
    rw [weightedDegree_restrictWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro E hE
        obtain ⟨hEK, huE⟩ := Finset.mem_filter.mp hE
        exact Finset.mem_filter.mpr ⟨hKH hEK, huE⟩)
      (fun E _ _ => NNReal.coe_nonneg (nu E))
  have hK0 := weightedDegree_nonneg K (restrictWeight K nu) {u}
  have hH0 := weightedDegree_nonneg H nu {u}
  nlinarith

end WeightRestriction

section MixedEnergy

variable [Fintype U] [DecidableEq U]

/-- The mixed Janson bilinear form for weights living on two different
hypergraphs on the same vertex type. -/
noncomputable def mixedCross (A B : Hypergraph U) (p : ℝ)
    (rho : EdgeWeight A) (mu : EdgeWeight B) : ℝ :=
  ∑ L ∈ jansonSets, (p ^ L.card)⁻¹ *
    weightedDegree A rho L * weightedDegree B mu L

theorem mixedCross_nonneg (A B : Hypergraph U) {p : ℝ} (hp : 0 ≤ p)
    (rho : EdgeWeight A) (mu : EdgeWeight B) :
    0 ≤ mixedCross A B p rho mu := by
  apply Finset.sum_nonneg
  intro L hL
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg hp _))
      (weightedDegree_nonneg A rho L))
    (weightedDegree_nonneg B mu L)

theorem mixedCross_sq_le (A B : Hypergraph U) {p : ℝ} (hp : 0 < p)
    (rho : EdgeWeight A) (mu : EdgeWeight B) :
    mixedCross A B p rho mu ^ 2 ≤ Lambda A p rho * Lambda B p mu := by
  have h := FiniteAnalysis.weighted_cauchy_schwarz jansonSets
    (fun L => (p ^ L.card)⁻¹)
    (fun L => weightedDegree A rho L)
    (fun L => weightedDegree B mu L)
    (fun L _ => inv_nonneg.mpr (pow_nonneg hp.le _))
  simpa only [mixedCross, Lambda, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using h

theorem mixedCross_lt_one (A B : Hypergraph U) {p : ℝ} (hp : 0 < p)
    (rho : EdgeWeight A) (mu : EdgeWeight B)
    (hrho : Lambda A p rho < 1) (hmu : Lambda B p mu < 1) :
    mixedCross A B p rho mu < 1 := by
  have hA0 := Lambda_nonneg A hp.le rho
  have hB0 := Lambda_nonneg B hp.le mu
  have hcross0 := mixedCross_nonneg A B hp.le rho mu
  have hsquare := mixedCross_sq_le A B hp rho mu
  have hprod : Lambda A p rho * Lambda B p mu < 1 := by nlinarith
  nlinarith

end MixedEnergy

section FixedContainer

variable [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

private theorem projected_vertices_subset (pi : V → U) (H : Hypergraph V)
    (X : Finset V) :
    (((H.restrict X).map pi).vertices) ⊆ X.image pi := by
  intro u hu
  obtain ⟨K, hK, huK⟩ := mem_vertices.mp hu
  obtain ⟨E, hEX, rfl⟩ := mem_map.mp hK
  obtain ⟨x, hxE, rfl⟩ := Finset.mem_image.mp huK
  exact Finset.mem_image.mpr ⟨x, (mem_restrict.mp hEX).2 hxE, rfl⟩

private theorem fresh_projected_restrict
    (pi : V → U) (v : U) (H : Hypergraph V)
    (hv : ∀ x, pi x ≠ v) (X : Finset V) :
    FreshFor v ((H.restrict X).map pi) :=
  SpecialContainerTheorem.freshFor_projected_restrict pi v H hv X

/-- A large fixed container cannot remain locally Janson after every small
deletion.  This is the deterministic first half of the Section 7 argument:
it produces the bounded-one-degree projected witness under the contrary
assumption. -/
private theorem boundedWitness_of_no_localization
    (pi : V → U) (H : Hypergraph V)
    {q p R R' eta : ℝ} {r s : ℕ} (X : Finset V)
    (hpar : SpecialContainer.ParameterConditions (Fintype.card V)
      s r q p R R' eta)
    (hs : 0 < s) (hH : H.IsUniform s)
    (hpi : SpecialContainer.ProjectionConditions pi H)
    (hXlarge : Fintype.card V ≤ 8 * r * X.card)
    (hno : ∀ Y : Finset V, Y ⊆ X →
      256 * r * (X.card - Y.card) ≤ Fintype.card V →
        ((H.restrict Y).map pi).IsJanson p R) :
    ∃ mu : EdgeWeight ((H.restrict X).map pi),
      mass ((H.restrict X).map pi) mu = Real.sqrt R ∧
      Lambda ((H.restrict X).map pi) p mu < 1 ∧
      oneDegreeEnergy ((H.restrict X).map pi) mu ≤
        2 * (s : ℝ) ^ 2 * mass ((H.restrict X).map pi) mu ^ 2 /
          (SpecialContainerTheorem.deletionBeta r *
            ((X.image pi).card : ℝ)) := by
  let K : Hypergraph U := (H.restrict X).map pi
  let carrier : Finset U := X.image pi
  let beta : ℝ := SpecialContainerTheorem.deletionBeta r
  have hr : 2 ≤ r := hpar.2.1
  have hp : 0 < p := hpar.2.2.2.2.1
  have hR : 0 < R :=
    SpecialContainerTheorem.parameter_R_pos hs hpar
  have hbeta : 0 < beta := by
    exact SpecialContainerTheorem.deletionBeta_pos hr
  have hn : 0 < Fintype.card V :=
    SpecialContainerTheorem.parameter_n_pos hs hpar
  have hX : 0 < X.card := by
    by_contra hX0
    have : X.card = 0 := Nat.eq_zero_of_not_pos hX0
    rw [this] at hXlarge
    simp at hXlarge
    omega
  have hcarrier : 0 < carrier.card := by
    have hhalf := hpi.1 X
    dsimp [carrier]
    omega
  have hKuniform : K.IsUniform s := by
    exact SpecialContainerTheorem.projected_restrict_isUniform pi H hH hpi X
  have hKvertices : K.vertices ⊆ carrier := by
    exact projected_vertices_subset pi H X
  have hlocal : ∀ W : Finset U, W ⊆ carrier →
      (1 - beta) * (carrier.card : ℝ) ≤ (W.card : ℝ) →
        (K.restrict W).IsJanson p R := by
    intro W hW hWlarge
    let Y := SpecialContainerTheorem.retainedByProjectedSet pi X W
    have hYX : Y ⊆ X :=
      SpecialContainerTheorem.retainedByProjectedSet_subset pi X W
    have hcardW : W.card ≤ carrier.card := Finset.card_le_card hW
    have hdiffcard : (carrier \ W).card = carrier.card - W.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hW]
    have hdiffR : ((carrier \ W).card : ℝ) ≤
        beta * (carrier.card : ℝ) := by
      rw [hdiffcard, Nat.cast_sub hcardW]
      linarith
    have hlossNat : X.card - Y.card ≤ 2 * (carrier \ W).card := by
      simpa [carrier, Y] using
        (SpecialContainerTheorem.retained_card_loss_le_twice pi H hpi X W)
    have hlossR : ((X.card - Y.card : ℕ) : ℝ) ≤
        2 * beta * (carrier.card : ℝ) := by
      have hcast : ((X.card - Y.card : ℕ) : ℝ) ≤
          (2 * (carrier \ W).card : ℕ) := by
        exact_mod_cast hlossNat
      norm_num at hcast ⊢
      nlinarith
    have hcarrierN : carrier.card ≤ Fintype.card V := by
      calc
        carrier.card ≤ X.card := Finset.card_image_le
        _ ≤ Fintype.card V := Finset.card_le_univ X
    have hloss : 256 * r * (X.card - Y.card) ≤ Fintype.card V := by
      have hcarrierR : (carrier.card : ℝ) ≤ Fintype.card V := by
        exact_mod_cast hcarrierN
      have hrR : 0 < (r : ℝ) := by positivity
      have hlossR' : (256 : ℝ) * r * ((X.card - Y.card : ℕ) : ℝ) ≤
          Fintype.card V := by
        have hbetaEq : beta = 1 / (512 * (r : ℝ)) := rfl
        rw [hbetaEq] at hlossR
        field_simp at hlossR
        calc
          (256 : ℝ) * r * ((X.card - Y.card : ℕ) : ℝ) =
              (((X.card - Y.card : ℕ) : ℝ) * 512 * r) / 2 := by ring
          _ ≤ (carrier.card : ℝ) := by linarith
          _ ≤ Fintype.card V := hcarrierR
      have hlossR'' : ((256 * r * (X.card - Y.card) : ℕ) : ℝ) ≤
          (Fintype.card V : ℝ) := by
        norm_num at hlossR' ⊢
        exact hlossR'
      exact_mod_cast hlossR''
    have hJ := hno Y hYX hloss
    rw [show K.restrict W = (H.restrict Y).map pi by
      exact SpecialContainerTheorem.map_restrict_retained pi H X W]
    exact hJ
  obtain ⟨mu, hmass, hLambda, henergy⟩ :=
    exists_bounded_oneDegree_onCarrier carrier hKuniform hKvertices hs hp hR
      hbeta hcarrier hlocal
  exact ⟨mu, hmass, hLambda, by simpa [K, carrier, beta] using henergy⟩

/-- The non-Janson conclusion supplied by the ordinary container theorem
forces less than half of the normalized mass to lie on cover edges. -/
private theorem cover_mass_lt_half
    (pi : V → U) (H : Hypergraph V) (C : Hypergraph V)
    {q p R R' eta : ℝ} {r s : ℕ} (X : Finset V)
    (hpar : SpecialContainer.ParameterConditions (Fintype.card V)
      s r q p R R' eta)
    (hs : 0 < s)
    (hpi : SpecialContainer.ProjectionConditions pi H)
    (mu : EdgeWeight ((H.restrict X).map pi))
    (hmass : mass ((H.restrict X).map pi) mu = Real.sqrt R)
    (hLambda : Lambda ((H.restrict X).map pi) p mu < 1)
    (hX : X.Nonempty)
    (hcontainer : ¬ (C.restrict X).IsJanson p
      (SpecialContainerTheorem.containerZeta r * p * X.card)) :
    let G := H.restrict X
    let nu := averagePullback G pi mu
    mass (G ∩ C) (restrictWeight (G ∩ C) nu) < Real.sqrt R / 2 := by
  classical
  dsimp only
  let G : Hypergraph V := H.restrict X
  let K : Hypergraph U := G.map pi
  let nu : EdgeWeight G := averagePullback G pi mu
  let D : ℝ := SpecialContainerTheorem.containerZeta r * p * X.card
  have hr : 2 ≤ r := hpar.2.1
  have hp : 0 < p := hpar.2.2.2.2.1
  have hR : 0 < R := SpecialContainerTheorem.parameter_R_pos hs hpar
  have hD : 0 < D := by
    dsimp [D, SpecialContainerTheorem.containerZeta]
    have hXcard : 0 < X.card := Finset.card_pos.mpr hX
    positivity
  have hGinj : EdgewiseInjective G pi := by
    exact SpecialContainerTheorem.projected_restrict_edgewiseInjective pi H hpi X
  have hmassnu : mass G nu = Real.sqrt R := by
    simpa [G, K, nu] using (mass_averagePullback (H := G) (π := pi) mu).trans hmass
  have hLambdanu : Lambda G p nu < 1 := by
    exact (Lambda_averagePullback_le hGinj mu hp).trans_lt hLambda
  let GC : Hypergraph V := G ∩ C
  have hGCsub : GC ⊆ C.restrict X := by
    intro E hE
    have hparts := Finset.mem_inter.mp hE
    exact mem_restrict.mpr ⟨hparts.2, (mem_restrict.mp hparts.1).2⟩
  by_contra hnot
  have hhalf : Real.sqrt R / 2 ≤
      mass GC (restrictWeight GC nu) := le_of_not_gt hnot
  have hDle : D ≤ R / 4 := by
    have hXn : X.card ≤ Fintype.card V := Finset.card_le_univ X
    have hXnR : (X.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hXn
    have hrR : 0 < (r : ℝ) := by positivity
    have hRdef := hpar.2.2.2.2.2.2.1
    dsimp [D, SpecialContainerTheorem.containerZeta]
    rw [hRdef]
    field_simp
    nlinarith
  have hmasssq : R / 4 ≤ mass GC (restrictWeight GC nu) ^ 2 := by
    have hsqrt : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
    have hmass0 := mass_nonneg GC (restrictWeight GC nu)
    have hsqrt0 : 0 ≤ Real.sqrt R / 2 := by positivity
    have hsquare : (Real.sqrt R / 2) ^ 2 ≤
        mass GC (restrictWeight GC nu) ^ 2 :=
      (sq_le_sq₀ hsqrt0 hmass0).2 hhalf
    nlinarith
  have hone : 1 ≤ mass GC (restrictWeight GC nu) ^ 2 / D := by
    apply (le_div_iff₀ hD).2
    simpa only [one_mul] using hDle.trans hmasssq
  apply hcontainer
  right
  let omega : EdgeWeight (C.restrict X) :=
    zeroExtend hGCsub (restrictWeight GC nu)
  refine ⟨omega, ?_⟩
  have hLE : Lambda (C.restrict X) p omega ≤ Lambda G p nu := by
    rw [show Lambda (C.restrict X) p omega =
      Lambda GC p (restrictWeight GC nu) by
        exact Lambda_zeroExtend hGCsub p (restrictWeight GC nu)]
    exact Lambda_restrictWeight_le (Finset.inter_subset_left) hp nu
  have hmE : mass (C.restrict X) omega = mass GC (restrictWeight GC nu) :=
    mass_zeroExtend hGCsub (restrictWeight GC nu)
  rw [hmE]
  exact (hLE.trans_lt hLambdanu).trans_le hone

/-! ### Canonical residual lifts and their conditional probabilities -/

/-- Choose one source lift of a projected edge.  Outside the mapped
hypergraph the chosen lift is empty; this makes the associated event the
whole outcome space and hence gives a nonzero probability everywhere. -/
noncomputable def chosenLift (G : Hypergraph V) (pi : V → U)
    (K : Finset U) : Finset V := by
  classical
  exact if h : K ∈ G.map pi then Classical.choose (mem_map.mp h) else ∅

theorem chosenLift_mem {G : Hypergraph V} {pi : V → U} {K : Finset U}
    (hK : K ∈ G.map pi) : chosenLift G pi K ∈ G := by
  classical
  simp only [chosenLift, dif_pos hK]
  exact (Classical.choose_spec (mem_map.mp hK)).1

theorem image_chosenLift {G : Hypergraph V} {pi : V → U}
    {K : Finset U} (hK : K ∈ G.map pi) :
    (chosenLift G pi K).image pi = K := by
  classical
  simp only [chosenLift, dif_pos hK]
  exact (Classical.choose_spec (mem_map.mp hK)).2

theorem chosenLift_eq_empty_of_not_mem {G : Hypergraph V} {pi : V → U}
    {K : Finset U} (hK : K ∉ G.map pi) : chosenLift G pi K = ∅ := by
  classical
  simp [chosenLift, hK]

/-- Conditioning on a nonempty event assigns probability one to the whole
outcome space. -/
theorem conditionalProbability_univ
    {Omega : Type*} [DecidableEq Omega]
    (outcomes given : Finset Omega) (weight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given weight ≠ 0) :
    FiniteExpectation.conditionalProbability outcomes given outcomes weight = 1 := by
  unfold FiniteExpectation.conditionalProbability
    FiniteExpectation.conditionalExpectation FiniteExpectation.expectation
    FiniteExpectation.conditioningMass
  have hsub := FiniteExpectation.conditioningSet_subset_left outcomes given
  have hsum : (∑ omega ∈ FiniteExpectation.conditioningSet outcomes given,
      weight omega * (if omega ∈ outcomes then (1 : ℝ) else 0)) =
      ∑ omega ∈ FiniteExpectation.conditioningSet outcomes given, weight omega := by
    apply Finset.sum_congr rfl
    intro omega homega
    rw [if_pos (hsub homega), mul_one]
  rw [hsum]
  exact div_self hmass

/-- Conditional probability viewed as a nonnegative real. -/
noncomputable def conditionalProbabilityNNReal
    {Omega : Type*} [DecidableEq Omega]
    (outcomes given event : Finset Omega) (weight : Omega → ℝ) : NNReal :=
  Real.toNNReal
    (FiniteExpectation.conditionalProbability outcomes given event weight)

theorem coe_conditionalProbabilityNNReal
    {Omega : Type*} [DecidableEq Omega]
    (outcomes given event : Finset Omega) (weight : Omega → ℝ)
    (hweight : ∀ omega ∈ outcomes, 0 ≤ weight omega)
    (hmass : 0 < FiniteExpectation.conditioningMass outcomes given weight) :
    (conditionalProbabilityNNReal outcomes given event weight : ℝ) =
      FiniteExpectation.conditionalProbability outcomes given event weight := by
  rw [conditionalProbabilityNNReal, Real.coe_toNNReal]
  apply FiniteExpectation.conditionalExpectation_nonneg
    outcomes given weight _ hweight hmass
  intro omega homega
  split <;> norm_num

/-- The conditional decomposition gives the uniform lower bound needed for
inverse-probability reweighting, including the case where the residual lift
is empty. -/
private theorem residual_probability_lower
    (pi : V → U) (H : Hypergraph V) (J : Hypergraph V)
    (q : ℝ) (s : ℕ) (T X : Finset V)
    (hH : H.IsUniform s) (hq : 0 < q) (hq8 : q < 1 / 8)
    (hTind : J.IsIndependent T)
    (K : Finset U)
    (hK : K ∈ ((H.restrict X \
      SpecialContainerTheorem.uniformizedCover q J s T).map pi)) :
    let outcomes := (Finset.univ : Finset V).powerset
    let given := ConditionalDecomposition.independentContainingEvent
      (Finset.univ : Finset V) J T
    let weight := ConditionalDecomposition.subsetWeight q (Finset.univ : Finset V)
    let L := chosenLift (H.restrict X \
      SpecialContainerTheorem.uniformizedCover q J s T) pi K \ T
    let event := SpecialContainerTheorem.containmentEvent (Finset.univ : Finset V) L
    ((q / 2) ^ s : ℝ) ≤
      FiniteExpectation.conditionalProbability outcomes given event weight := by
  classical
  dsimp only
  let C := SpecialContainerTheorem.uniformizedCover q J s T
  let Gout := H.restrict X \ C
  let E := chosenLift Gout pi K
  let L := E \ T
  have hEout : E ∈ Gout := chosenLift_mem hK
  have hEH : E ∈ H := (mem_restrict.mp (Finset.mem_sdiff.mp hEout).1).1
  have hEcard : E.card = s := hH E hEH
  have hq1 : q < 1 := hq8.trans (by norm_num)
  have hbase0 : 0 ≤ q / 2 := by positivity
  have hbase1 : q / 2 ≤ 1 := by linarith
  have hmass : 0 < FiniteExpectation.conditioningMass
      (Finset.univ : Finset V).powerset
      (ConditionalDecomposition.independentContainingEvent Finset.univ J T)
      (ConditionalDecomposition.subsetWeight q Finset.univ) :=
    SpecialContainerTheorem.conditioningMass_independentContaining_pos
      hq hq1 (Finset.subset_univ T) hTind
  by_cases hL : L.Nonempty
  · have hLC : L ∉ SpecialContainerTheorem.conditionalCover q J T := by
      intro hmem
      have hLE : L ⊆ E := Finset.sdiff_subset
      have hEup : E ∈
          (SpecialContainerTheorem.conditionalCover q J T).upClosure :=
        mem_upClosure.mpr ⟨L, hmem, hLE⟩
      have hEC : E ∈ C := by
        exact mem_layer.mpr ⟨hEup, hEcard⟩
      exact (Finset.mem_sdiff.mp hEout).2 hEC
    have hLsub : L ⊆ (Finset.univ : Finset V) \ T := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hstrict := SpecialContainerTheorem.conditional_large_of_not_mem_cover
      hLsub hL hLC
    rw [← SpecialContainerTheorem.conditionalProbability_containmentEvent]
      at hstrict
    have hcard : L.card ≤ s := by
      calc
        L.card ≤ E.card := Finset.card_le_card Finset.sdiff_subset
        _ = s := hEcard
    have hpow : (q / 2) ^ s ≤ (q / 2) ^ L.card :=
      pow_le_pow_of_le_one hbase0 hbase1 hcard
    have hthreshold : ConditionalDecomposition.threshold q (1 / 2) L =
        (q / 2) ^ L.card := by
      unfold ConditionalDecomposition.threshold
      congr 1
      ring
    rw [hthreshold] at hstrict
    exact hpow.trans hstrict.le
  · have hLEmpty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    have hevent : SpecialContainerTheorem.containmentEvent
        (Finset.univ : Finset V) L = (Finset.univ : Finset V).powerset := by
      ext Y
      simp [SpecialContainerTheorem.containmentEvent, hLEmpty]
    rw [hevent, conditionalProbability_univ _ _ _ hmass.ne']
    exact pow_le_one₀ hbase0 hbase1

/-- Removing the cover edges in the source and then projecting leaves more
than half of the normalized mass.  Projection collisions can only add mass,
which is why an inequality rather than an equality is used here. -/
private theorem projected_out_mass_gt_half
    (pi : V → U) (H C : Hypergraph V) {p R : ℝ} (X : Finset V)
    (hpi : SpecialContainer.ProjectionConditions pi H)
    (mu : EdgeWeight ((H.restrict X).map pi))
    (hmass : mass ((H.restrict X).map pi) mu = Real.sqrt R)
    (hcover :
      let G := H.restrict X
      let nu := averagePullback G pi mu
      mass (G ∩ C) (restrictWeight (G ∩ C) nu) < Real.sqrt R / 2) :
    let Gout := H.restrict X \ C
    let Kout := Gout.map pi
    Real.sqrt R / 2 < mass Kout (restrictWeight Kout mu) := by
  classical
  dsimp only at hcover ⊢
  let G : Hypergraph V := H.restrict X
  let Gout : Hypergraph V := G \ C
  let Kout : Hypergraph U := Gout.map pi
  let nu : EdgeWeight G := averagePullback G pi mu
  have hGinj : EdgewiseInjective G pi :=
    SpecialContainerTheorem.projected_restrict_edgewiseInjective pi H hpi X
  have hmassnu : mass G nu = Real.sqrt R := by
    simpa [G, nu] using
      (mass_averagePullback (H := G) (π := pi) mu).trans hmass
  have hsplit := mass_inter_add_sdiff G C nu
  have hout : Real.sqrt R / 2 < mass Gout (restrictWeight Gout nu) := by
    dsimp [Gout]
    rw [hmassnu] at hsplit
    nlinarith
  have hsubset : Gout ⊆ G.filter (fun E => E.image pi ∈ Kout) := by
    intro E hE
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hE).1,
      mem_map.mpr ⟨E, hE, rfl⟩⟩
  have hsumle : mass Gout (restrictWeight Gout nu) ≤
      ∑ E ∈ G with E.image pi ∈ Kout, (nu E : ℝ) := by
    rw [mass_restrictWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun E _ _ => NNReal.coe_nonneg (nu E))
  have hsum : (∑ E ∈ G with E.image pi ∈ Kout, (nu E : ℝ)) =
      mass Kout (restrictWeight Kout mu) := by
    rw [show (∑ E ∈ G with E.image pi ∈ Kout, (nu E : ℝ)) =
      ∑ F ∈ G.map pi with F ∈ Kout, (mu F : ℝ) by
        exact sum_averagePullback_image_filter mu (fun F => F ∈ Kout)]
    rw [mass_restrictWeight]
    apply Finset.sum_congr
    · ext F
      simp only [Finset.mem_filter]
      constructor
      · exact fun hF => hF.2
      · intro hF
        exact ⟨map_mono (Finset.sdiff_subset) hF, hF⟩
    · intro F hF
      rfl
  rw [hsum] at hsumle
  exact hout.trans_le hsumle

/-! ### Adjoined measures and support transport -/

/-- The sum of an available-edge weight and a freshly adjoined weight,
both extended by zero to their disjoint union. -/
noncomputable def joinedWeight (v : U) (A B : Hypergraph U)
    (rho : EdgeWeight A) (mu : EdgeWeight B) : EdgeWeight (A ∪ adjoinVertex v B) :=
  zeroExtend Finset.subset_union_left rho +
    zeroExtend Finset.subset_union_right (adjoinWeight v mu)

theorem mass_joinedWeight {v : U} {A B : Hypergraph U}
    (hBfresh : FreshFor v B) (rho : EdgeWeight A) (mu : EdgeWeight B) :
    mass (A ∪ adjoinVertex v B) (joinedWeight v A B rho mu) =
      mass A rho + mass B mu := by
  rw [joinedWeight, mass_add, mass_zeroExtend, mass_zeroExtend,
    mass_adjoinWeight hBfresh]

theorem lambdaCross_joined_eq_mixed {v : U} {A B : Hypergraph U}
    (hAfresh : FreshFor v A) (hBfresh : FreshFor v B) {p : ℝ}
    (rho : EdgeWeight A) (mu : EdgeWeight B) :
    lambdaCross (A ∪ adjoinVertex v B) p
        (zeroExtend Finset.subset_union_left rho)
        (zeroExtend Finset.subset_union_right (adjoinWeight v mu)) =
      mixedCross A B p rho mu := by
  unfold lambdaCross mixedCross
  apply Finset.sum_congr rfl
  intro L hL
  rw [weightedDegree_zeroExtend, weightedDegree_zeroExtend,
    weightedDegree_adjoinWeight hBfresh]
  by_cases hvL : v ∈ L
  · rw [weightedDegree_eq_zero_of_fresh_mem hAfresh rho hvL]
    ring
  · rw [Finset.erase_eq_self.mpr hvL]

theorem Lambda_joinedWeight {v : U} {A B : Hypergraph U}
    (hAfresh : FreshFor v A) (hBfresh : FreshFor v B) {p : ℝ}
    (rho : EdgeWeight A) (mu : EdgeWeight B) :
    Lambda (A ∪ adjoinVertex v B) p (joinedWeight v A B rho mu) =
      Lambda A p rho + 2 * mixedCross A B p rho mu +
        Lambda (adjoinVertex v B) p (adjoinWeight v mu) := by
  rw [joinedWeight, Lambda_add_eq, Lambda_zeroExtend, Lambda_zeroExtend,
    lambdaCross_joined_eq_mixed hAfresh hBfresh]

/-- Two finite sums agree if the summand vanishes on both sides of their
symmetric difference. -/
private theorem sum_eq_of_zero_off
    {alpha : Type*} [DecidableEq alpha] (S T : Finset alpha) (f : alpha → ℝ)
    (hST : ∀ x ∈ S, x ∉ T → f x = 0)
    (hTS : ∀ x ∈ T, x ∉ S → f x = 0) :
    ∑ x ∈ S, f x = ∑ x ∈ T, f x := by
  rw [← S.sum_inter_add_sum_sdiff T f,
    ← T.sum_inter_add_sum_sdiff S f]
  have hSzero : ∑ x ∈ S \ T, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hST x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
  have hTzero : ∑ x ∈ T \ S, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hTS x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
  rw [hSzero, hTzero, add_zero, add_zero]
  apply Finset.sum_congr
  · ext x
    simp [and_comm]
  · intro x hx
    rfl

/-- Mass and all degrees depend only on the edge support of the weight. -/
private theorem mass_eq_of_zero_off (S T : Hypergraph U)
    (nu : Finset U → NNReal)
    (hST : ∀ E ∈ S, E ∉ T → nu E = 0)
    (hTS : ∀ E ∈ T, E ∉ S → nu E = 0) :
    mass S nu = mass T nu := by
  unfold mass
  apply sum_eq_of_zero_off
  · intro E hES hET
    simp [hST E hES hET]
  · intro E hET hES
    simp [hTS E hET hES]

private theorem weightedDegree_eq_of_zero_off (S T : Hypergraph U)
    (nu : Finset U → NNReal)
    (hST : ∀ E ∈ S, E ∉ T → nu E = 0)
    (hTS : ∀ E ∈ T, E ∉ S → nu E = 0)
    (L : Finset U) :
    weightedDegree S nu L = weightedDegree T nu L := by
  unfold weightedDegree
  apply sum_eq_of_zero_off
  · intro E hE hnot
    have hparts := Finset.mem_filter.mp hE
    have hnotT : E ∉ T := by
      intro hET
      exact hnot (Finset.mem_filter.mpr ⟨hET, hparts.2⟩)
    simp [hST E hparts.1 hnotT]
  · intro E hE hnot
    have hparts := Finset.mem_filter.mp hE
    have hnotS : E ∉ S := by
      intro hES
      exact hnot (Finset.mem_filter.mpr ⟨hES, hparts.2⟩)
    simp [hTS E hparts.1 hnotS]

private theorem Lambda_eq_of_zero_off (S T : Hypergraph U) {p : ℝ}
    (nu : Finset U → NNReal)
    (hST : ∀ E ∈ S, E ∉ T → nu E = 0)
    (hTS : ∀ E ∈ T, E ∉ S → nu E = 0) :
    Lambda S p nu = Lambda T p nu := by
  unfold Lambda
  apply Finset.sum_congr rfl
  intro L hL
  rw [weightedDegree_eq_of_zero_off S T nu hST hTS L]

private theorem conditionalExpectation_const_eq
    {Omega : Type*} [DecidableEq Omega]
    (outcomes given : Finset Omega) (weight : Omega → ℝ) (c : ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given weight ≠ 0) :
    FiniteExpectation.conditionalExpectation outcomes given weight
      (fun _ => c) = c := by
  unfold FiniteExpectation.conditionalExpectation FiniteExpectation.expectation
    FiniteExpectation.conditioningMass
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c hmass

private theorem conditionalExpectation_mixedCross
    {Omega : Type*} [DecidableEq Omega]
    (A B : Hypergraph U) {p : ℝ} (rho : EdgeWeight A)
    (gamma : NNReal) (mu : EdgeWeight B)
    (probability : Finset U → NNReal)
    (edgeEvent : Finset U → Finset Omega)
    (outcomes given : Finset Omega) (sampleWeight : Omega → ℝ)
    (hmass : FiniteExpectation.conditioningMass outcomes given sampleWeight ≠ 0)
    (hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E)
        sampleWeight = (probability E : ℝ))
    (hprob0 : ∀ E, probability E ≠ 0) :
    FiniteExpectation.conditionalExpectation outcomes given sampleWeight
      (fun omega => mixedCross A B p rho
        (inverseProbabilityWeight gamma mu probability edgeEvent omega)) =
      (gamma : ℝ) * mixedCross A B p rho mu := by
  unfold mixedCross
  apply FiniteExpectation.conditionalExpectation_crossDegree_sum_of_unbiased
    outcomes given sampleWeight jansonSets
      (fun L => (p ^ L.card)⁻¹)
      (fun L => weightedDegree A rho L)
      (fun L => weightedDegree B mu L)
      (fun omega L => weightedDegree B
        (inverseProbabilityWeight gamma mu probability edgeEvent omega) L)
      (gamma : ℝ)
  intro L hL
  exact conditionalExpectation_weightedDegree_inverseProbabilityWeight
    gamma mu probability edgeEvent outcomes given sampleWeight
      hmass hprob hprob0 L

private theorem finish_localization_contradiction
    (pi : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (J Gout : Hypergraph V) (Kout : Hypergraph U)
    (q p R R' eta : ℝ) (r s : ℕ) (T : Finset V) (gamma : NNReal)
    (outcomes given : Finset (Finset V)) (sampleWeight : Finset V → ℝ)
    (residual : Finset U → Finset V)
    (edgeEvent : Finset U → Finset (Finset V))
    (probability : Finset U → NNReal)
    (muout : EdgeWeight Kout) (rho : EdgeWeight F)
    (randomWeight : Finset V → EdgeWeight Kout)
    (fixedUnion : Hypergraph U)
    (totalWeight : Finset V → EdgeWeight fixedUnion)
    (hpar : SpecialContainer.ParameterConditions (Fintype.card V)
      s r q p R R' eta)
    (hs : 0 < s) (hr : 2 ≤ r) (hq : 0 < q) (hq8 : q < 1 / 8)
    (hp : 0 < p)
    (hpq : p ≤ q / ((2 ^ 11 : ℝ) * r * (s : ℝ) ^ 2))
    (hR : 0 < R) (hR'0 : 0 ≤ R')
    (heta : eta = p ^ 4 * (q / 2) ^ (4 * s)) (heta0 : 0 < eta)
    (hgamma : 0 < gamma) (hgammaSq : (gamma : ℝ) ^ 2 = 8 * eta)
    (hKoutFresh : FreshFor v Kout)
    (hJdef : J = SpecialContainer.jansonGeneratingFamily pi v H F p
      (R' + eta * R))
    (hKoutDef : Kout = Gout.map pi) (hGoutH : Gout ⊆ H)
    (hgivenDef : given =
      ConditionalDecomposition.independentContainingEvent Finset.univ J T)
    (hresidualDef : residual = fun E => chosenLift Gout pi E \ T)
    (hedgeEventDef : edgeEvent = fun E =>
      SpecialContainerTheorem.containmentEvent Finset.univ (residual E))
    (hrandomDef : randomWeight = fun omega =>
      inverseProbabilityWeight gamma muout probability edgeEvent omega)
    (hfixedDef : fixedUnion = F ∪ adjoinVertex v Kout)
    (htotalDef : totalWeight = fun omega =>
      joinedWeight v F Kout rho (randomWeight omega))
    (hsampleWeight : ∀ omega ∈ outcomes, 0 ≤ sampleWeight omega)
    (hconditioning : 0 < FiniteExpectation.conditioningMass
      outcomes given sampleWeight)
    (htotalMassLower : Real.sqrt R' +
      (gamma : ℝ) * Real.sqrt R / 2 <
      FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega)))
    (htotalEnergyUpper :
      FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => Lambda fixedUnion p (totalWeight omega)) <
      1 + 4 * (gamma : ℝ)) : False := by
  classical
  have hp_lt_q : p < q := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hsSq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ 2 := by norm_num
        _ ≤ (s : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hsR 2
    have hden : 1 < (2 ^ 11 : ℝ) * r * (s : ℝ) ^ 2 := by
      have hrs0 := mul_le_mul hrR hsSq (by norm_num) (by positivity)
      have hrs : (2 : ℝ) ≤ (r : ℝ) * (s : ℝ) ^ 2 := by
        simpa only [mul_one] using hrs0
      calc
        (1 : ℝ) < 2048 * 2 := by norm_num
        _ ≤ 2048 * ((r : ℝ) * (s : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hrs (by norm_num)
        _ = (2 ^ 11 : ℝ) * r * (s : ℝ) ^ 2 := by norm_num <;> ring
    exact hpq.trans_lt (div_lt_self hq hden)
  have hp8 : p < 1 / 8 := hp_lt_q.trans hq8
  have hfactor : 0 ≤ (q / 2) ^ (4 * s) ∧
      (q / 2) ^ (4 * s) ≤ 1 :=
    ⟨pow_nonneg (by positivity) _, pow_le_one₀ (by positivity) (by linarith)⟩
  have hp4 : p ^ 4 < (1 / 8 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hp8 hp.le (by norm_num)
  have hetaSmall : eta < 1 / 128 := by
    rw [heta]
    have hetaLe : p ^ 4 * (q / 2) ^ (4 * s) ≤ p ^ 4 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hfactor.2 (pow_nonneg hp.le 4)
    norm_num at hp4 ⊢
    linarith
  have hgammaLt : (gamma : ℝ) < 1 / 4 := by
    have hgammaR := NNReal.coe_nonneg gamma
    nlinarith
  have hmassNumerical := JensenContradiction.sqrt_mass_square_gt
    hR hR'0 (SpecialContainerTheorem.parameter_sixteen_R'_le_R hpar)
    (NNReal.coe_pos.mpr hgamma) hgammaLt hgammaSq
  have hden : 0 < R' + eta * R := by positivity
  have hpointwise : ∀ omega ∈ FiniteExpectation.conditioningSet outcomes given,
      mass fixedUnion (totalWeight omega) ^ 2 / (R' + eta * R) ≤
        Lambda fixedUnion p (totalWeight omega) := by
    intro omega homega
    have homegaGiven :=
      FiniteExpectation.conditioningSet_subset_right outcomes given homega
    have homegaGiven' : omega ∈
        ConditionalDecomposition.independentContainingEvent Finset.univ J T := by
      rw [← hgivenDef]
      exact homegaGiven
    have hind : J.IsIndependent omega := by
      exact (ConditionalDecomposition.mem_independentContainingEvent.mp
        homegaGiven').2.1
    have hnon : ¬ (SpecialContainer.extensionUnion pi v H F omega).IsJanson
        p (R' + eta * R) := by
      intro hJomega
      have hmem : omega ∈ J := by
        rw [hJdef]
        exact SpecialContainer.mem_jansonGeneratingFamily.mpr hJomega
      exact hind omega hmem Finset.Subset.rfl
    have hnotWitness : ¬ ∃ nu : EdgeWeight
        (SpecialContainer.extensionUnion pi v H F omega),
        Lambda (SpecialContainer.extensionUnion pi v H F omega) p nu <
          mass (SpecialContainer.extensionUnion pi v H F omega) nu ^ 2 /
            (R' + eta * R) := by
      intro hex
      exact hnon (Or.inr hex)
    let Womega := SpecialContainer.extensionUnion pi v H F omega
    have hST : ∀ E ∈ fixedUnion, E ∉ Womega → totalWeight omega E = 0 := by
      intro E hEfix hEnot
      have hparts : E ∈ F ∪ adjoinVertex v Kout := by
        simpa [hfixedDef] using hEfix
      have hEF : E ∉ F := by
        intro hEinF
        exact hEnot (Finset.mem_union_right _ hEinF)
      rcases Finset.mem_union.mp hparts with hEinF | hEadj
      · exact (hEF hEinF).elim
      · obtain ⟨B, hBK, hBE⟩ := mem_adjoinVertex.mp hEadj
        have hnotEvent : omega ∉ edgeEvent B := by
          intro hevent
          have hBout : chosenLift Gout pi B ∈ Gout := by
            apply chosenLift_mem
            rw [← hKoutDef]
            exact hBK
          have hresSub : residual B ⊆ omega :=
            by
              rw [hedgeEventDef] at hevent
              exact (SpecialContainerTheorem.mem_containmentEvent.mp hevent).2
          have hTsub : T ⊆ omega :=
            (ConditionalDecomposition.mem_independentContainingEvent.mp
              homegaGiven').2.2
          have hliftSub : chosenLift Gout pi B ⊆ omega := by
            intro x hx
            by_cases hxT : x ∈ T
            · exact hTsub hxT
            · have hxres : x ∈ residual B := by
                rw [hresidualDef]
                exact Finset.mem_sdiff.mpr ⟨hx, hxT⟩
              exact hresSub hxres
          have hBmap : B ∈ (H.restrict omega).map pi := by
            refine mem_map.mpr ⟨chosenLift Gout pi B, ?_, image_chosenLift ?_⟩
            · exact mem_restrict.mpr ⟨hGoutH hBout, hliftSub⟩
            · rw [← hKoutDef]
              exact hBK
          apply hEnot
          apply Finset.mem_union_left F
          exact SpecialContainer.mem_coneAt.mpr ⟨B, hBmap, hBE⟩
        have hfirst : zeroExtend (Finset.subset_union_left : F ⊆
            F ∪ adjoinVertex v Kout) rho E = 0 := by
          simp [hEF]
        have hsecond : zeroExtend
            (Finset.subset_union_right : adjoinVertex v Kout ⊆
              F ∪ adjoinVertex v Kout)
            (adjoinWeight v (randomWeight omega)) E = 0 := by
          rw [zeroExtend_apply_of_mem _ _ hEadj]
          subst E
          rw [adjoinWeight_insert hKoutFresh (randomWeight omega) hBK]
          simp [hrandomDef, inverseProbabilityWeight, hnotEvent]
        rw [htotalDef]
        simp [joinedWeight, hfirst, hsecond]
    have hTS : ∀ E ∈ Womega, E ∉ fixedUnion → totalWeight omega E = 0 := by
      intro E hEW hEnot
      have hEF : E ∉ F := fun h => hEnot (by
        rw [hfixedDef]
        exact Finset.mem_union_left _ h)
      have hEadj : E ∉ adjoinVertex v Kout := fun h => hEnot (by
        rw [hfixedDef]
        exact Finset.mem_union_right _ h)
      rw [htotalDef]
      simp [joinedWeight, zeroExtend, hEF, hEadj]
    have hmassEq := mass_eq_of_zero_off fixedUnion Womega
      (totalWeight omega) hST hTS
    have hLambdaEq := Lambda_eq_of_zero_off (p := p) fixedUnion Womega
      (totalWeight omega) hST hTS
    rw [hmassEq, hLambdaEq]
    exact le_of_not_gt (fun hlt => hnotWitness ⟨totalWeight omega, hlt⟩)
  have hjensen := FiniteExpectation.sq_conditionalExpectation_le
    outcomes given sampleWeight
      (fun omega => mass fixedUnion (totalWeight omega))
      hsampleWeight hconditioning
  have hpointMul : ∀ omega ∈ FiniteExpectation.conditioningSet outcomes given,
      mass fixedUnion (totalWeight omega) ^ 2 ≤
        (R' + eta * R) * Lambda fixedUnion p (totalWeight omega) := by
    intro omega homega
    simpa [mul_comm] using (div_le_iff₀ hden).mp (hpointwise omega homega)
  have hexpectPoint := FiniteExpectation.conditionalExpectation_mono
    outcomes given sampleWeight
      (fun omega => mass fixedUnion (totalWeight omega) ^ 2)
      (fun omega => (R' + eta * R) * Lambda fixedUnion p (totalWeight omega))
      hsampleWeight hconditioning hpointMul
  rw [FiniteExpectation.conditionalExpectation_const_mul] at hexpectPoint
  have hupper :
      (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 <
      (R' + eta * R) * (1 + 4 * (gamma : ℝ)) := by
    calc
      _ ≤ FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun omega => mass fixedUnion (totalWeight omega) ^ 2) := hjensen
      _ ≤ (R' + eta * R) *
          FiniteExpectation.conditionalExpectation outcomes given sampleWeight
            (fun omega => Lambda fixedUnion p (totalWeight omega)) := hexpectPoint
      _ < (R' + eta * R) * (1 + 4 * (gamma : ℝ)) :=
        mul_lt_mul_of_pos_left htotalEnergyUpper hden
  have hmassStrict : (1 + 4 * (gamma : ℝ)) * (R' + eta * R) <
      (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 := by
    have htarget0 : 0 ≤ Real.sqrt R' +
        (gamma : ℝ) * Real.sqrt R / 2 := by positivity
    have htotal0 : 0 ≤ FiniteExpectation.conditionalExpectation outcomes given
        sampleWeight (fun omega => mass fixedUnion (totalWeight omega)) := by
      apply FiniteExpectation.conditionalExpectation_nonneg outcomes given
        sampleWeight _ hsampleWeight hconditioning
      intro omega homega
      exact mass_nonneg fixedUnion (totalWeight omega)
    have hsquares : (Real.sqrt R' + (gamma : ℝ) * Real.sqrt R / 2) ^ 2 <
        (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 := by
      nlinarith
    exact hmassNumerical.trans hsquares
  rw [mul_comm] at hupper
  exact (not_lt_of_ge hupper.le) hmassStrict

/-! ### The fixed-container localisation theorem -/

/-- ACDFM Section 7, conclusion (ii) of the specialised container theorem,
for one valid pair of fingerprints. -/
theorem fixedContainer_localize
    (pi : V → U) (v : U) (H : Hypergraph V) (F : Hypergraph U)
    (q p R R' eta : ℝ) (r s : ℕ) (T X : Finset V)
    (hpar : SpecialContainer.ParameterConditions (Fintype.card V)
      s r q p R R' eta)
    (hs : 0 < s)
    (hH : H.IsUniform s)
    (hF : F.IsUniform (s + 1))
    (hFJ : F.IsJanson p R')
    (hpi : SpecialContainer.ProjectionConditions pi H)
    (hv : ∀ x, pi x ≠ v)
    (hFfresh : FreshFor v F)
    (hTind : (SpecialContainer.jansonGeneratingFamily pi v H F p
      (R' + eta * R)).IsIndependent T)
    (hcontainer : ¬ ((SpecialContainerTheorem.uniformizedCover q
      (SpecialContainer.jansonGeneratingFamily pi v H F p (R' + eta * R))
      s T).restrict X).IsJanson p
        (SpecialContainerTheorem.containerZeta r * p * X.card))
    (hXlarge : Fintype.card V ≤ 8 * r * X.card) :
    ∃ Y : Finset V, Y ⊆ X ∧
      256 * r * (X.card - Y.card) ≤ Fintype.card V ∧
      ¬ ((H.restrict Y).map pi).IsJanson p R := by
  classical
  let J : Hypergraph V := SpecialContainer.jansonGeneratingFamily pi v H F p
    (R' + eta * R)
  let C : Hypergraph V := SpecialContainerTheorem.uniformizedCover q J s T
  let G : Hypergraph V := H.restrict X
  let Gout : Hypergraph V := G \ C
  let K : Hypergraph U := G.map pi
  let Kout : Hypergraph U := Gout.map pi
  have hpar0 := hpar
  rcases hpar with
    ⟨hsn, hr, hq, hq8, hp, hpq, hRdef, hR'0, hR'le, heta⟩
  have hn : 0 < Fintype.card V := lt_of_lt_of_le hs hsn
  have hR : 0 < R := by
    rw [hRdef]
    positivity
  have hq1 : q < 1 := hq8.trans (by norm_num)
  have hX : X.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hXe
    subst X
    simp at hXlarge
    omega
  by_contra hgoal
  have hno : ∀ Y : Finset V, Y ⊆ X →
      256 * r * (X.card - Y.card) ≤ Fintype.card V →
        ((H.restrict Y).map pi).IsJanson p R := by
    intro Y hYX hloss
    by_contra hnot
    exact hgoal ⟨Y, hYX, hloss, hnot⟩
  obtain ⟨mu, hmumass, hmuLambda, hmuDegree⟩ :=
    boundedWitness_of_no_localization pi H X hpar0 hs hH hpi hXlarge hno
  have hcover := cover_mass_lt_half pi H C X hpar0 hs hpi mu hmumass
    hmuLambda hX (by simpa [C, J] using hcontainer)
  have hmuoutMass : Real.sqrt R / 2 <
      mass Kout (restrictWeight Kout mu) := by
    simpa [G, Gout, Kout] using
      projected_out_mass_gt_half (p := p) pi H C X hpi mu hmumass hcover
  let muout : EdgeWeight Kout := restrictWeight Kout mu
  have hKoutK : Kout ⊆ K := by
    exact map_mono Finset.sdiff_subset
  have hmuoutLambda : Lambda Kout p muout < 1 := by
    exact (Lambda_restrictWeight_le hKoutK hp mu).trans_lt hmuLambda
  have hcarrier : 0 < (X.image pi).card := by
    by_contra hnot
    have hz : (X.image pi).card = 0 := Nat.eq_zero_of_not_pos hnot
    have hproj := hpi.1 X
    rw [hz] at hproj
    simp at hproj
    rw [hproj] at hX
    exact Finset.not_nonempty_empty hX
  have hncarrier : Fintype.card V ≤ 16 * r * (X.image pi).card := by
    have hproj := hpi.1 X
    calc
      Fintype.card V ≤ 8 * r * X.card := hXlarge
      _ ≤ 8 * r * (2 * (X.image pi).card) :=
        Nat.mul_le_mul_left (8 * r) hproj
      _ = 16 * r * (X.image pi).card := by ring
  have hncarrierR : (Fintype.card V : ℝ) ≤
      16 * (r : ℝ) * ((X.image pi).card : ℝ) := by
    exact_mod_cast hncarrier
  have hmuDegree' : oneDegreeEnergy K mu ≤
      256 * (r : ℝ) * (s : ℝ) ^ 2 * p := by
    rw [hmumass, Real.sq_sqrt hR.le] at hmuDegree
    change oneDegreeEnergy K mu ≤
      2 * (s : ℝ) ^ 2 * R /
        (SpecialContainerTheorem.deletionBeta r *
          ((X.image pi).card : ℝ)) at hmuDegree
    rw [hRdef] at hmuDegree
    unfold SpecialContainerTheorem.deletionBeta at hmuDegree
    have hrR : 0 < (r : ℝ) := by positivity
    have hcarrierR : 0 < ((X.image pi).card : ℝ) := by exact_mod_cast hcarrier
    field_simp at hmuDegree
    nlinarith [mul_nonneg (sq_nonneg (s : ℝ)) hp.le]
  have hmuoutDegree : singletonEnergy Kout muout ≤
      256 * ((r : ℝ) * (s : ℝ) ^ 2) * p := by
    have hmono := singletonEnergy_restrictWeight_le hKoutK mu
    have heq : singletonEnergy K mu = oneDegreeEnergy K mu := rfl
    rw [heq] at hmono
    nlinarith
  let a : NNReal := ⟨(q / 2) ^ s, pow_nonneg (by positivity) _⟩
  let gamma : NNReal := ⟨Real.sqrt (8 * eta), Real.sqrt_nonneg _⟩
  let sqrtEta : ℝ := p ^ 2 * (a : ℝ) ^ 2
  have ha : 0 < a := by
    exact NNReal.coe_pos.mp (by
      change 0 < (q / 2 : ℝ) ^ s
      positivity)
  have hsqrtEta : 0 < sqrtEta := by
    dsimp [sqrtEta]
    positivity
  have hetaEq : eta = sqrtEta ^ 2 := by
    rw [heta]
    change p ^ 4 * (q / 2) ^ (4 * s) =
      (p ^ 2 * ((q / 2) ^ s) ^ 2) ^ 2
    rw [show 4 * s = s * 4 by omega, pow_mul]
    ring
  have heta0 : 0 < eta := by rw [hetaEq]; positivity
  have hgamma : 0 < gamma := by
    apply NNReal.coe_pos.mp
    change 0 < Real.sqrt (8 * eta)
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) heta0)
  have hgammaSq : (gamma : ℝ) ^ 2 = 8 * eta := by
    dsimp [gamma]
    exact Real.sq_sqrt (mul_nonneg (by norm_num) heta0.le)
  have hsqrt : sqrtEta = p ^ 2 * (a : ℝ) ^ 2 := rfl
  have ht : (1 : ℝ) ≤ (r : ℝ) * (s : ℝ) ^ 2 := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((s : ℝ) - 1)]
  have hsmall : 2048 * ((r : ℝ) * (s : ℝ) ^ 2) * p ≤ 1 := by
    apply acdfm_smallness_of_p_le hp (by linarith : q ≤ 1) ht
    convert hpq using 1 <;> norm_num <;> ring
  let outcomes : Finset (Finset V) := (Finset.univ : Finset V).powerset
  let given : Finset (Finset V) :=
    ConditionalDecomposition.independentContainingEvent Finset.univ J T
  let sampleWeight : Finset V → ℝ :=
    ConditionalDecomposition.subsetWeight q Finset.univ
  let residual : Finset U → Finset V := fun E => chosenLift Gout pi E \ T
  let edgeEvent : Finset U → Finset (Finset V) := fun E =>
    SpecialContainerTheorem.containmentEvent Finset.univ (residual E)
  let probability : Finset U → NNReal := fun E =>
    conditionalProbabilityNNReal outcomes given (edgeEvent E) sampleWeight
  have hsampleWeight : ∀ omega ∈ outcomes, 0 ≤ sampleWeight omega := by
    intro omega homega
    exact ConditionalDecomposition.subsetWeight_nonneg hq.le hq1.le _ _
  have hconditioning : 0 < FiniteExpectation.conditioningMass
      outcomes given sampleWeight := by
    simpa [outcomes, given, sampleWeight, J] using
      (SpecialContainerTheorem.conditioningMass_independentContaining_pos
        hq hq1 (Finset.subset_univ T) hTind)
  have hprob : ∀ E,
      FiniteExpectation.conditionalProbability outcomes given (edgeEvent E)
        sampleWeight = (probability E : ℝ) := by
    intro E
    symm
    exact coe_conditionalProbabilityNNReal outcomes given (edgeEvent E)
      sampleWeight hsampleWeight hconditioning
  have hprobLower : ∀ E ∈ Kout, a ≤ probability E := by
    intro E hE
    have hE' : E ∈ ((H.restrict X \
        SpecialContainerTheorem.uniformizedCover q J s T).map pi) := by
      simpa [Kout, Gout, G, C] using hE
    apply NNReal.coe_le_coe.mp
    change (q / 2) ^ s ≤ (probability E : ℝ)
    rw [← hprob E]
    simpa [outcomes, given, sampleWeight, edgeEvent, residual, Gout, G, C, J]
      using residual_probability_lower pi H J q s T X hH hq hq8
        (by simpa [J] using hTind) E hE'
  have hprob0 : ∀ E, probability E ≠ 0 := by
    intro E
    by_cases hE : E ∈ Kout
    · exact ne_of_gt (ha.trans_le (hprobLower E hE))
    · have hlift : chosenLift Gout pi E = ∅ := by
        apply chosenLift_eq_empty_of_not_mem
        simpa [Kout] using hE
      have hevent : edgeEvent E = outcomes := by
        ext omega
        simp [edgeEvent, residual, hlift, outcomes,
          SpecialContainerTheorem.containmentEvent]
      have hcoe : (probability E : ℝ) = 1 := by
        rw [← hprob E, hevent]
        exact conditionalProbability_univ outcomes given sampleWeight hconditioning.ne'
      exact NNReal.coe_ne_zero.mp (by rw [hcoe]; norm_num)
  have hKoutFresh : FreshFor v Kout := by
    have hKfresh := fresh_projected_restrict pi v H hv X
    intro E hE
    exact hKfresh E (hKoutK hE)
  have hpointRandom : ∀ omega,
      Lambda (adjoinVertex v Kout) p
          (adjoinWeight v (inverseProbabilityWeight gamma muout
            probability edgeEvent omega)) <
        (gamma : ℝ) ^ 2 / (2 * sqrtEta) := by
    intro omega
    exact Lambda_adjoin_inverseProbabilityWeight_lt hKoutFresh hp ht hsmall
      hgamma ha hsqrtEta hsqrt hmuoutLambda hmuoutDegree hprobLower
  obtain ⟨rho, hrhoMass, hrhoLambda⟩ : ∃ rho : EdgeWeight F,
      mass F rho = Real.sqrt R' ∧ Lambda F p rho < 1 := by
    rcases eq_or_lt_of_le hR'0 with hR'eq | hR'pos
    · subst R'
      exact ⟨0, by simp, by simp⟩
    · obtain ⟨rho, hmassrho, hLrho⟩ :=
        hFJ.exists_normalized hp hR'pos (Real.sqrt_pos.2 hR'pos)
      refine ⟨rho, hmassrho, ?_⟩
      calc
        Lambda F p rho < Real.sqrt R' ^ 2 / R' := hLrho
        _ = 1 := by rw [Real.sq_sqrt hR'pos.le]; exact div_self hR'pos.ne'
  have hcross : mixedCross F Kout p rho muout < 1 :=
    mixedCross_lt_one F Kout hp rho muout hrhoLambda hmuoutLambda
  have hrandomSmall : (gamma : ℝ) ^ 2 / (2 * sqrtEta) <
      2 * (gamma : ℝ) := by
    have hgammaR : 0 < (gamma : ℝ) := NNReal.coe_pos.mpr hgamma
    have h2sqrt : 2 * sqrtEta < (gamma : ℝ) := by
      rw [hetaEq] at hgammaSq
      nlinarith [sq_nonneg ((gamma : ℝ) - 2 * sqrtEta)]
    calc
      (gamma : ℝ) ^ 2 / (2 * sqrtEta) = 4 * sqrtEta := by
        rw [hgammaSq, hetaEq]
        field_simp <;> ring
      _ < 2 * (gamma : ℝ) := by linarith
  let randomWeight : Finset V → EdgeWeight Kout := fun omega =>
    inverseProbabilityWeight gamma muout probability edgeEvent omega
  let fixedUnion : Hypergraph U := F ∪ adjoinVertex v Kout
  let totalWeight : Finset V → EdgeWeight fixedUnion := fun omega =>
    joinedWeight v F Kout rho (randomWeight omega)
  have hmassRandom : FiniteExpectation.conditionalExpectation outcomes given
      sampleWeight (fun omega => mass Kout (randomWeight omega)) =
      (gamma : ℝ) * mass Kout muout := by
    exact conditionalExpectation_mass_inverseProbabilityWeight gamma muout
      probability edgeEvent outcomes given sampleWeight hconditioning.ne'
      hprob hprob0
  have hcrossExpected : FiniteExpectation.conditionalExpectation outcomes given
      sampleWeight (fun omega => mixedCross F Kout p rho (randomWeight omega)) =
      (gamma : ℝ) * mixedCross F Kout p rho muout := by
    exact conditionalExpectation_mixedCross F Kout rho gamma muout probability
      edgeEvent outcomes given sampleWeight hconditioning.ne' hprob hprob0
  have hrandomExpected : FiniteExpectation.conditionalExpectation outcomes given
      sampleWeight (fun omega => Lambda (adjoinVertex v Kout) p
        (adjoinWeight v (randomWeight omega))) ≤
      (gamma : ℝ) ^ 2 / (2 * sqrtEta) := by
    calc
      _ ≤ FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun _ => (gamma : ℝ) ^ 2 / (2 * sqrtEta)) := by
        apply FiniteExpectation.conditionalExpectation_mono outcomes given
          sampleWeight _ _ hsampleWeight hconditioning
        intro omega homega
        exact (hpointRandom omega).le
      _ = _ := conditionalExpectation_const_eq outcomes given sampleWeight _
        hconditioning.ne'
  have htotalMass : FiniteExpectation.conditionalExpectation outcomes given
      sampleWeight (fun omega => mass fixedUnion (totalWeight omega)) =
      Real.sqrt R' + (gamma : ℝ) * mass Kout muout := by
    have hfun : (fun omega => mass fixedUnion (totalWeight omega)) =
        (fun omega => mass F rho + mass Kout (randomWeight omega)) := by
      funext omega
      exact mass_joinedWeight hKoutFresh rho (randomWeight omega)
    rw [hfun, FiniteExpectation.conditionalExpectation_add,
      conditionalExpectation_const_eq outcomes given sampleWeight _
        hconditioning.ne', hmassRandom, hrhoMass]
  have htotalMassLower : Real.sqrt R' +
      (gamma : ℝ) * Real.sqrt R / 2 <
      FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega)) := by
    rw [htotalMass]
    have hm := mul_lt_mul_of_pos_left hmuoutMass (NNReal.coe_pos.mpr hgamma)
    simpa only [muout, mul_div_assoc, add_comm] using
      add_lt_add_left hm (Real.sqrt R')
  have htotalEnergy : FiniteExpectation.conditionalExpectation outcomes given
      sampleWeight (fun omega => Lambda fixedUnion p (totalWeight omega)) =
      Lambda F p rho +
        2 * ((gamma : ℝ) * mixedCross F Kout p rho muout) +
        FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun omega => Lambda (adjoinVertex v Kout) p
            (adjoinWeight v (randomWeight omega))) := by
    have hfun : (fun omega => Lambda fixedUnion p (totalWeight omega)) =
        (fun omega => Lambda F p rho +
          2 * mixedCross F Kout p rho (randomWeight omega) +
          Lambda (adjoinVertex v Kout) p
            (adjoinWeight v (randomWeight omega))) := by
      funext omega
      exact Lambda_joinedWeight hFfresh hKoutFresh rho (randomWeight omega)
    rw [hfun, FiniteExpectation.conditionalExpectation_add,
      FiniteExpectation.conditionalExpectation_add,
      conditionalExpectation_const_eq outcomes given sampleWeight _
        hconditioning.ne',
      FiniteExpectation.conditionalExpectation_const_mul,
      hcrossExpected]
  have htotalEnergyUpper :
      FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => Lambda fixedUnion p (totalWeight omega)) <
      1 + 4 * (gamma : ℝ) := by
    rw [htotalEnergy]
    calc
      _ ≤ Lambda F p rho +
          2 * ((gamma : ℝ) * mixedCross F Kout p rho muout) +
          ((gamma : ℝ) ^ 2 / (2 * sqrtEta)) := by
        gcongr
      _ < 1 + 2 * (gamma : ℝ) +
          ((gamma : ℝ) ^ 2 / (2 * sqrtEta)) := by
        have hgammaR : 0 < (gamma : ℝ) := NNReal.coe_pos.mpr hgamma
        have hgc : (gamma : ℝ) * mixedCross F Kout p rho muout <
            (gamma : ℝ) := by
          simpa using mul_lt_mul_of_pos_left hcross hgammaR
        linarith
      _ < 1 + 4 * (gamma : ℝ) := by linarith
  have hGoutH : Gout ⊆ H := by
    intro E hE
    exact (mem_restrict.mp (Finset.mem_sdiff.mp hE).1).1
  exact finish_localization_contradiction
    (pi := pi) (v := v) (H := H) (F := F) (J := J) (Gout := Gout)
    (Kout := Kout) (q := q) (p := p) (R := R) (R' := R') (eta := eta)
    (r := r) (s := s) (T := T) (gamma := gamma) (outcomes := outcomes)
    (given := given) (sampleWeight := sampleWeight) (residual := residual)
    (edgeEvent := edgeEvent) (probability := probability) (muout := muout)
    (rho := rho) (randomWeight := randomWeight) (fixedUnion := fixedUnion)
    (totalWeight := totalWeight) hpar0 hs hr hq hq8 hp hpq hR hR'0 heta
    heta0 hgamma hgammaSq hKoutFresh rfl rfl hGoutH rfl rfl rfl rfl rfl rfl
    hsampleWeight hconditioning htotalMassLower htotalEnergyUpper
  /-
  have hp_lt_q : p < q := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hsSq : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((s : ℝ) - 1)]
    have hden : 1 < (2 ^ 11 : ℝ) * r * (s : ℝ) ^ 2 := by
      have hrs : (2 : ℝ) ≤ (r : ℝ) * (s : ℝ) ^ 2 :=
        mul_le_mul hrR hsSq (by norm_num) (by positivity)
      norm_num
      linarith
    have hdiv : q / ((2 ^ 11 : ℝ) * r * (s : ℝ) ^ 2) < q :=
      div_lt_self hq hden
    exact hpq.trans_lt hdiv
  have hp8 : p < 1 / 8 := hp_lt_q.trans hq8
  have hfactor : 0 ≤ (q / 2) ^ (4 * s) ∧
      (q / 2) ^ (4 * s) ≤ 1 :=
    ⟨pow_nonneg (by positivity) _, pow_le_one₀ (by positivity) (by linarith)⟩
  have hp4 : p ^ 4 < (1 / 8 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hp8 hp.le (by norm_num)
  have hetaSmall : eta < 1 / 128 := by
    rw [heta]
    have hetaLe : p ^ 4 * (q / 2) ^ (4 * s) ≤ p ^ 4 := by
      nlinarith [pow_nonneg p 4]
    norm_num at hp4 ⊢
    linarith
  have hgammaLt : (gamma : ℝ) < 1 / 4 := by
    have hgammaR := NNReal.coe_nonneg gamma
    nlinarith
  have hmassNumerical := JensenContradiction.sqrt_mass_square_gt
    hR hR'0 (SpecialContainerTheorem.parameter_sixteen_R'_le_R hpar0)
    (NNReal.coe_pos.mpr hgamma) hgammaLt hgammaSq
  have hden : 0 < R' + eta * R := by positivity
  have hpointwise : ∀ omega ∈ FiniteExpectation.conditioningSet outcomes given,
      mass fixedUnion (totalWeight omega) ^ 2 / (R' + eta * R) ≤
        Lambda fixedUnion p (totalWeight omega) := by
    intro omega homega
    have homegaGiven := FiniteExpectation.conditioningSet_subset_right outcomes given homega
    have hind : J.IsIndependent omega := by
      exact (ConditionalDecomposition.mem_independentContainingEvent.mp
        (by simpa [given] using homegaGiven)).2.1
    have hnon : ¬ (SpecialContainer.extensionUnion pi v H F omega).IsJanson
        p (R' + eta * R) := by
      intro hJomega
      have hmem : omega ∈ J := by
        simpa [J] using
          (SpecialContainer.mem_jansonGeneratingFamily.mpr hJomega)
      exact hind omega hmem Finset.Subset.rfl
    have hnotWitness : ¬ ∃ nu : EdgeWeight
        (SpecialContainer.extensionUnion pi v H F omega),
        Lambda (SpecialContainer.extensionUnion pi v H F omega) p nu <
          mass (SpecialContainer.extensionUnion pi v H F omega) nu ^ 2 /
            (R' + eta * R) := by
      intro hex
      exact hnon (Or.inr hex)
    let Womega := SpecialContainer.extensionUnion pi v H F omega
    have hST : ∀ E ∈ fixedUnion, E ∉ Womega → totalWeight omega E = 0 := by
      intro E hEfix hEnot
      have hparts := Finset.mem_union.mp hEfix
      have hEF : E ∉ F := by
        intro hEF
        exact hEnot (Finset.mem_union_right _ hEF)
      rcases hparts with hEinF | hEadj
      · exact (hEF hEinF).elim
      · obtain ⟨B, hBK, hBE⟩ := mem_adjoinVertex.mp hEadj
        have hnotEvent : omega ∉ edgeEvent B := by
          intro hevent
          have hBout := chosenLift_mem hBK
          have hresSub : residual B ⊆ omega :=
            (SpecialContainerTheorem.mem_containmentEvent.mp hevent).2
          have hTsub : T ⊆ omega :=
            (ConditionalDecomposition.mem_independentContainingEvent.mp
              (by simpa [given] using homegaGiven)).2.2
          have hliftSub : chosenLift Gout pi B ⊆ omega := by
            intro x hx
            by_cases hxT : x ∈ T
            · exact hTsub hxT
            · exact hresSub (Finset.mem_sdiff.mpr ⟨hx, hxT⟩)
          have hBmap : B ∈ (H.restrict omega).map pi := by
            refine mem_map.mpr ⟨chosenLift Gout pi B, ?_, image_chosenLift hBK⟩
            exact mem_restrict.mpr
              ⟨(mem_restrict.mp (Finset.mem_sdiff.mp hBout).1).1, hliftSub⟩
          apply hEnot
          apply Finset.mem_union_left F
          exact SpecialContainer.mem_coneAt.mpr ⟨B, hBmap, hBE⟩
        have hfirst : zeroExtend (Finset.subset_union_left : F ⊆ fixedUnion) rho E = 0 := by
          simp [hEF]
        have hsecond : zeroExtend
            (Finset.subset_union_right : adjoinVertex v Kout ⊆ fixedUnion)
            (adjoinWeight v (randomWeight omega)) E = 0 := by
          rw [zeroExtend_apply_of_mem _ _ hEadj]
          subst E
          rw [adjoinWeight_insert hKoutFresh (randomWeight omega) hBK]
          simp [randomWeight, inverseProbabilityWeight, hnotEvent]
        simp [totalWeight, joinedWeight, hfirst, hsecond]
    have hTS : ∀ E ∈ Womega, E ∉ fixedUnion → totalWeight omega E = 0 := by
      intro E hEW hEnot
      have hEF : E ∉ F := fun h => hEnot (Finset.mem_union_left _ h)
      have hEadj : E ∉ adjoinVertex v Kout :=
        fun h => hEnot (Finset.mem_union_right _ h)
      simp [totalWeight, joinedWeight, zeroExtend, hEF, hEadj]
    have hmassEq := mass_eq_of_zero_off fixedUnion Womega
      (totalWeight omega) hST hTS
    have hLambdaEq := Lambda_eq_of_zero_off fixedUnion Womega
      (totalWeight omega) hST hTS
    rw [hmassEq, hLambdaEq]
    exact le_of_not_gt (fun hlt => hnotWitness ⟨totalWeight omega, hlt⟩)
  have hjensen := FiniteExpectation.sq_conditionalExpectation_le
    outcomes given sampleWeight
      (fun omega => mass fixedUnion (totalWeight omega))
      hsampleWeight hconditioning
  have hpointMul : ∀ omega ∈ FiniteExpectation.conditioningSet outcomes given,
      mass fixedUnion (totalWeight omega) ^ 2 ≤
        (R' + eta * R) * Lambda fixedUnion p (totalWeight omega) := by
    intro omega homega
    simpa [mul_comm] using (div_le_iff₀ hden).mp (hpointwise omega homega)
  have hexpectPoint := FiniteExpectation.conditionalExpectation_mono
    outcomes given sampleWeight
      (fun omega => mass fixedUnion (totalWeight omega) ^ 2)
      (fun omega => (R' + eta * R) * Lambda fixedUnion p (totalWeight omega))
      hsampleWeight hconditioning hpointMul
  rw [FiniteExpectation.conditionalExpectation_const_mul] at hexpectPoint
  have hupper :
      (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 <
      (R' + eta * R) * (1 + 4 * (gamma : ℝ)) := by
    calc
      _ ≤ FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun omega => mass fixedUnion (totalWeight omega) ^ 2) := hjensen
      _ ≤ (R' + eta * R) *
          FiniteExpectation.conditionalExpectation outcomes given sampleWeight
            (fun omega => Lambda fixedUnion p (totalWeight omega)) := hexpectPoint
      _ < (R' + eta * R) * (1 + 4 * (gamma : ℝ)) :=
        mul_lt_mul_of_pos_left htotalEnergyUpper hden
  have hmassStrict : (1 + 4 * (gamma : ℝ)) * (R' + eta * R) <
      (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
        (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 := by
    have htarget0 : 0 ≤ Real.sqrt R' +
        (gamma : ℝ) * Real.sqrt R / 2 := by positivity
    have htotal0 : 0 ≤ FiniteExpectation.conditionalExpectation outcomes given
        sampleWeight (fun omega => mass fixedUnion (totalWeight omega)) := by
      apply FiniteExpectation.conditionalExpectation_nonneg outcomes given
        sampleWeight _ hsampleWeight hconditioning
      intro omega homega
      exact mass_nonneg fixedUnion (totalWeight omega)
    have hsquares : (Real.sqrt R' + (gamma : ℝ) * Real.sqrt R / 2) ^ 2 <
        (FiniteExpectation.conditionalExpectation outcomes given sampleWeight
          (fun omega => mass fixedUnion (totalWeight omega))) ^ 2 := by
      nlinarith
    exact hmassNumerical.trans hsquares
  rw [mul_comm] at hupper
  exact (not_lt_of_ge hupper.le) hmassStrict
  -/

end FixedContainer

end SpecialLocalization
end Erdos565
