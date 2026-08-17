import ErdosProblems.Erdos581.StableNumerics
import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Prod

/-!
# The stable/active recoloring lemma

The proof is expressed as finite averaging.  There is no measure-theoretic or
asymptotic input in this file.
-/

open Finset Set
open scoped BigOperators

namespace Erdos581

section LocalProbabilities

variable {α : Type*} [Fintype α] [DecidableEq α]

private def stableSame (A : Finset α) : Prop :=
  Fintype.card α + 1 < 2 * A.card

private def stableDifferent (A : Finset α) : Prop :=
  Fintype.card α + 1 < 2 * (A.card + 1)

private instance (A : Finset α) : Decidable (stableSame A) := by
  unfold stableSame
  infer_instance

private instance (A : Finset α) : Decidable (stableDifferent A) := by
  unfold stableDifferent
  infer_instance

private noncomputable def sameStableProb : ℝ :=
  𝔼 A : Finset α, if stableSame A then 1 else 0

private noncomputable def differentStableProb : ℝ :=
  𝔼 A : Finset α, if stableDifferent A then 1 else 0

private lemma expect_indicator (P : Finset α → Prop) [DecidablePred P] :
    (𝔼 A : Finset α, if P A then (1 : ℝ) else 0) =
      ((univ.filter P).card : ℝ) / Fintype.card (Finset α) := by
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  simp

private lemma expect_card_eq (r : ℕ) :
    (𝔼 A : Finset α, if A.card = r then (1 : ℝ) else 0) =
      ((Fintype.card α).choose r : ℝ) / (2 : ℝ) ^ Fintype.card α := by
  rw [expect_indicator]
  rw [univ_filter_card_eq, card_powersetCard, card_univ, Fintype.card_finset]
  norm_cast

private lemma stable_indicator_sub (A : Finset α) :
    (if stableDifferent A then (1 : ℝ) else 0) -
        (if stableSame A then 1 else 0) =
      if A.card = (Fintype.card α + 1) / 2 then 1 else 0 := by
  have hcard := A.card_le_univ
  by_cases hd : stableDifferent A <;> by_cases hs : stableSame A
    <;> simp [hd, hs]
    <;> unfold stableDifferent at hd
    <;> unfold stableSame at hs
    <;> omega

private lemma choose_odd_middle (r : ℕ) :
    2 * (2 * r + 1).choose (r + 1) = Nat.centralBinom (r + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hsym : (2 * r + 1).choose r = (2 * r + 1).choose (r + 1) := by
    exact (Nat.choose_symm_half r).symm
  calc
    2 * (2 * r + 1).choose (r + 1) =
        (2 * r + 1).choose r + (2 * r + 1).choose (r + 1) := by omega
    _ = ((2 * r + 1) + 1).choose (r + 1) :=
      (Nat.choose_succ_succ' (2 * r + 1) r).symm
    _ = (2 * (r + 1)).choose (r + 1) := by
      congr 1

private lemma pivotal_probability :
    differentStableProb (α := α) - sameStableProb (α := α) =
      degreeInfluence (Fintype.card α + 1) := by
  rw [differentStableProb, sameStableProb, ← Finset.expect_sub_distrib]
  simp_rw [stable_indicator_sub]
  rw [expect_card_eq]
  obtain ⟨r, hn | hn⟩ := Nat.even_or_odd' (Fintype.card α)
  · rw [hn]
    rw [show (2 * r + 1) / 2 = r by omega]
    rw [degreeInfluence, show (2 * r + 1) / 2 = r by omega,
      centralProb, Nat.centralBinom_eq_two_mul_choose]
    congr 1
    norm_num [pow_mul]
  · rw [hn]
    rw [show (2 * r + 1 + 1) / 2 = r + 1 by omega]
    rw [degreeInfluence, show (2 * r + 1 + 1) / 2 = r + 1 by omega,
      centralProb]
    have hchoose := choose_odd_middle r
    have hchooseR : (Nat.centralBinom (r + 1) : ℝ) =
        2 * ((2 * r + 1).choose (r + 1) : ℝ) := by
      exact_mod_cast hchoose.symm
    rw [hchooseR]
    norm_num [pow_succ, pow_mul]
    ring

private lemma differentStableProb_nonneg :
    0 ≤ differentStableProb (α := α) := by
  unfold differentStableProb
  rw [Fintype.expect_eq_sum_div_card]
  apply div_nonneg
  · exact sum_nonneg fun A _ ↦ by split_ifs <;> norm_num
  · positivity

private lemma sameStableProb_nonneg :
    0 ≤ sameStableProb (α := α) := by
  unfold sameStableProb
  rw [Fintype.expect_eq_sum_div_card]
  apply div_nonneg
  · exact sum_nonneg fun A _ ↦ by split_ifs <;> norm_num
  · positivity

private lemma differentStableProb_le_one :
    differentStableProb (α := α) ≤ 1 := by
  unfold differentStableProb
  rw [Fintype.expect_eq_sum_div_card]
  rw [div_le_one (by positivity : (0 : ℝ) < Fintype.card (Finset α))]
  have hle : (∑ A : Finset α, if stableDifferent A then (1 : ℝ) else 0) ≤
      ∑ _A : Finset α, (1 : ℝ) := by
    gcongr with A
    split_ifs <;> norm_num
  simpa using hle

private lemma differentStableProb_ge_half :
    (1 : ℝ) / 2 ≤ differentStableProb (α := α) := by
  let e : Finset α ≃ Finset α :=
    { toFun := (·ᶜ)
      invFun := (·ᶜ)
      left_inv := compl_compl
      right_inv := compl_compl }
  let I : Finset α → ℝ := fun A ↦ if stableDifferent A then 1 else 0
  have hcomp : (𝔼 A : Finset α, I (Aᶜ)) = 𝔼 A : Finset α, I A := by
    exact Fintype.expect_equiv e (fun A ↦ I (Aᶜ)) I (fun _ ↦ rfl)
  have hpoint : ∀ A : Finset α, (1 : ℝ) ≤ I A + I (Aᶜ) := by
    intro A
    have hcard := A.card_le_univ
    have hc : (Aᶜ).card = Fintype.card α - A.card := Finset.card_compl A
    have hstable : stableDifferent A ∨ stableDifferent (Aᶜ) := by
      unfold stableDifferent
      rw [hc]
      omega
    change (1 : ℝ) ≤
      (if stableDifferent A then 1 else 0) +
        (if stableDifferent (Aᶜ) then 1 else 0)
    rcases hstable with h | h
    · simp only [h, if_true]
      split_ifs <;> norm_num
    · simp only [h, if_true]
      split_ifs <;> norm_num
  have havg : Finset.expect univ (fun _A : Finset α ↦ (1 : ℝ)) ≤
      Finset.expect univ (fun A : Finset α ↦ I A + I (Aᶜ)) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
    apply div_le_div_of_nonneg_right
    · exact sum_le_sum fun A _ ↦ hpoint A
    · positivity
  rw [Fintype.expect_const, Finset.expect_add_distrib, hcomp] at havg
  simpa [differentStableProb, I] using (show (1 : ℝ) / 2 ≤
      𝔼 A : Finset α, I A by linarith)

/-- The local product gain used at the two ends of an edge. -/
private lemma local_product_gain {β : Type*} [Fintype β] [DecidableEq β] :
    (1 : ℝ) / 4 *
        (differentStableProb (α := α) * differentStableProb (α := β) -
          sameStableProb (α := α) * sameStableProb (α := β)) ≥
      (degreeInfluence (Fintype.card α + 1) +
          degreeInfluence (Fintype.card β + 1)) / 16 := by
  let ca := degreeInfluence (Fintype.card α + 1)
  let cb := degreeInfluence (Fintype.card β + 1)
  have ha := pivotal_probability (α := α)
  have hb := pivotal_probability (α := β)
  have hpa := differentStableProb_ge_half (α := α)
  have hpb := differentStableProb_ge_half (α := β)
  by_cases hα : IsEmpty α
  · letI : IsEmpty α := hα
    have hcardα : Fintype.card α = 0 := Fintype.card_eq_zero
    have hca_one : ca = 1 := by
      simp [ca, hcardα, degreeInfluence, centralProb]
    have hsameα := sameStableProb_nonneg (α := α)
    have hdiffα := differentStableProb_le_one (α := α)
    have hsameβ := sameStableProb_nonneg (α := β)
    have hdiffβ := differentStableProb_le_one (α := β)
    have hcb_le : cb ≤ 1 := by
      dsimp [cb] at *
      linarith
    dsimp [ca, cb] at *
    nlinarith
  · have hcardα : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp hα)
    by_cases hβ : IsEmpty β
    · letI : IsEmpty β := hβ
      have hcardβ : Fintype.card β = 0 := Fintype.card_eq_zero
      have hcb_one : cb = 1 := by
        simp [cb, hcardβ, degreeInfluence, centralProb]
      have hsameα := sameStableProb_nonneg (α := α)
      have hdiffα := differentStableProb_le_one (α := α)
      have hsameβ := sameStableProb_nonneg (α := β)
      have hdiffβ := differentStableProb_le_one (α := β)
      have hca_le : ca ≤ 1 := by
        dsimp [ca]
        linarith
      dsimp [ca, cb] at *
      nlinarith
    · have hcardβ : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp hβ)
      have hca : ca ≤ 1 / 2 := by
        apply degreeInfluence_le_half
        omega
      have hcb : cb ≤ 1 / 2 := by
        apply degreeInfluence_le_half
        omega
      have hprod : ca * cb ≤ (ca + cb) / 4 := by
        have hcap := degreeInfluence_pos (d := Fintype.card α + 1) (by omega)
        have hcbp := degreeInfluence_pos (d := Fintype.card β + 1) (by omega)
        nlinarith
      have hca0 := degreeInfluence_pos (d := Fintype.card α + 1) (by omega)
      have hcb0 := degreeInfluence_pos (d := Fintype.card β + 1) (by omega)
      have hleft : (1 : ℝ) / 2 * cb ≤ differentStableProb (α := α) * cb := by
        exact mul_le_mul_of_nonneg_right hpa hcb0.le
      have hright : (1 : ℝ) / 2 * ca ≤ differentStableProb (α := β) * ca := by
        exact mul_le_mul_of_nonneg_right hpb hca0.le
      dsimp [ca, cb] at *
      nlinarith

section IndependentRestrictions

variable {V : Type*} [Fintype V] [DecidableEq V]

private def coloringSplitEquiv (s t : Finset V) (hst : Disjoint s t) :
    (V → Bool) ≃
      (s → Bool) × (t → Bool) × ({x : V // x ∉ s ∧ x ∉ t} → Bool) where
  toFun σ := (fun x ↦ σ x, fun x ↦ σ x, fun x ↦ σ x)
  invFun p x := if hs : x ∈ s then p.1 ⟨x, hs⟩
    else if ht : x ∈ t then p.2.1 ⟨x, ht⟩ else p.2.2 ⟨x, hs, ht⟩
  left_inv σ := by
    funext x
    by_cases hs : x ∈ s <;> simp [hs]
  right_inv p := by
    apply Prod.ext
    · funext x
      simp [x.property]
    · apply Prod.ext
      · funext x
        have hns : (x : V) ∉ s := by
          intro hs
          exact Finset.disjoint_left.mp hst hs x.property
        simp [hns, x.property]
      · funext x
        simp [x.property.1, x.property.2]

/-- Uniform Boolean colorings have independent restrictions to disjoint
finite vertex sets. -/
private lemma expect_restrictions_mul (s t : Finset V) (hst : Disjoint s t)
    (f : (s → Bool) → ℝ) (g : (t → Bool) → ℝ) :
    (𝔼 σ : V → Bool, f (fun x ↦ σ x) * g (fun x ↦ σ x)) =
      (𝔼 a : s → Bool, f a) * (𝔼 b : t → Bool, g b) := by
  let R := {x : V // x ∉ s ∧ x ∉ t}
  let e := coloringSplitEquiv s t hst
  rw [Fintype.expect_equiv e
    (fun σ : V → Bool ↦ f (fun x ↦ σ x) * g (fun x ↦ σ x))
    (fun p : (s → Bool) × (t → Bool) × (R → Bool) ↦ f p.1 * g p.2.1)
    (fun _ ↦ rfl)]
  calc
    (𝔼 p : (s → Bool) × (t → Bool) × (R → Bool), f p.1 * g p.2.1) =
        𝔼 a : s → Bool, 𝔼 q : (t → Bool) × (R → Bool), f a * g q.1 := by
          simpa only [univ_product_univ] using
            (Finset.expect_product (univ : Finset (s → Bool))
              (univ : Finset ((t → Bool) × (R → Bool)))
              (fun p ↦ f p.1 * g p.2.1))
    _ = 𝔼 a : s → Bool, 𝔼 b : t → Bool, f a * g b := by
      congr 1
      funext a
      calc
        (𝔼 q : (t → Bool) × (R → Bool), f a * g q.1) =
            𝔼 b : t → Bool, 𝔼 _r : R → Bool, f a * g b := by
              simpa only [univ_product_univ] using
                (Finset.expect_product (univ : Finset (t → Bool))
                  (univ : Finset (R → Bool)) (fun q ↦ f a * g q.1))
        _ = 𝔼 b : t → Bool, f a * g b := by simp
    _ = (𝔼 a : s → Bool, f a) * (𝔼 b : t → Bool, g b) :=
      (Fintype.expect_mul_expect f g).symm

end IndependentRestrictions

section PointedColorings

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A coloring of a pointed finite type is its color at the point together
with the set of all other points having the opposite color. -/
private def relativeColoringEquiv (u : U) :
    (U → Bool) ≃ Bool × Finset {x : U // x ≠ u} where
  toFun σ := (σ u,
    (univ : Finset {x : U // x ≠ u}).filter
      (fun x : {x : U // x ≠ u} ↦ σ x.1 ≠ σ u))
  invFun p x := if h : x = u then p.1
    else if (⟨x, h⟩ : {x : U // x ≠ u}) ∈ p.2 then !p.1 else p.1
  left_inv σ := by
    funext x
    by_cases hxu : x = u
    · simp [hxu]
    · by_cases hx : σ x = σ u
      · simp [hxu, hx]
      · simp only [hxu, ↓reduceDIte]
        have hmem : (⟨x, hxu⟩ : {x : U // x ≠ u}) ∈
            (univ : Finset {x : U // x ≠ u}).filter
              (fun y : {x : U // x ≠ u} ↦ σ y.1 ≠ σ u) := by
          simp [hx]
        rw [if_pos hmem]
        cases h1 : σ x <;> cases h2 : σ u <;> simp_all
  right_inv p := by
    apply Prod.ext
    · simp
    · ext x
      by_cases hx : x ∈ p.2
      · have hne : (x : U) ≠ u := x.property
        simp [hne, hx]
      · have hne : (x : U) ≠ u := x.property
        simp [hne, hx]

/-- Fixing the color at the distinguished point costs exactly a factor of
two and is independent of any predicate of the relative-color finset. -/
private lemma relative_fixed_expect (u : U) (c : Bool)
    (P : Finset {x : U // x ≠ u} → Prop) [DecidablePred P] :
    (𝔼 σ : U → Bool,
        if σ u = c ∧ P (relativeColoringEquiv u σ).2 then (1 : ℝ) else 0) =
      (1 : ℝ) / 2 * (𝔼 A : Finset {x : U // x ≠ u}, if P A then 1 else 0) := by
  let e := relativeColoringEquiv u
  rw [Fintype.expect_equiv e
    (fun σ : U → Bool ↦
      if σ u = c ∧ P (relativeColoringEquiv u σ).2 then (1 : ℝ) else 0)
    (fun p : Bool × Finset {x : U // x ≠ u} ↦
      if p.1 = c ∧ P p.2 then (1 : ℝ) else 0)
    (fun _ ↦ rfl)]
  rw [show (𝔼 p : Bool × Finset {x : U // x ≠ u},
      if p.1 = c ∧ P p.2 then (1 : ℝ) else 0) =
        𝔼 b : Bool, 𝔼 A : Finset {x : U // x ≠ u},
          if b = c ∧ P A then (1 : ℝ) else 0 by
    simpa only [univ_product_univ] using
      (Finset.expect_product (univ : Finset Bool)
        (univ : Finset (Finset {x : U // x ≠ u}))
        (fun p ↦ if p.1 = c ∧ P p.2 then (1 : ℝ) else 0))]
  rw [Fintype.expect_eq_sum_div_card]
  cases c <;> simp [Fintype.expect_eq_sum_div_card]
    <;> ring

end PointedColorings

section GraphBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The endpoint block for the oriented edge `u-v`: the endpoint `u` and all
its neighbors except `v`. -/
private def edgeBlock (u v : V) : Finset V :=
  insert u (G.neighborFinset u \ {v})

private def edgePoint (u v : V) : edgeBlock G u v :=
  ⟨u, mem_insert_self _ _⟩

private lemma card_edgeBlock {u v : V} (huv : G.Adj u v) :
    #(edgeBlock G u v) = G.degree u := by
  rw [edgeBlock, card_insert_of_notMem]
  · rw [card_sdiff_of_subset]
    · have hdeg : 0 < G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact card_pos.mpr ⟨v, (G.mem_neighborFinset u v).mpr huv⟩
      rw [Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]
      omega
    · simpa [SimpleGraph.mem_neighborFinset] using huv
  · simp [SimpleGraph.mem_neighborFinset, G.loopless]

private lemma card_other_edgeBlock {u v : V} (huv : G.Adj u v) :
    Fintype.card {x : edgeBlock G u v // x ≠ edgePoint G u v} + 1 =
      G.degree u := by
  have hcompl := Fintype.card_subtype_compl
    (fun x : edgeBlock G u v ↦ x = edgePoint G u v)
  have hpos : 0 < Fintype.card (edgeBlock G u v) :=
    Fintype.card_pos_iff.mpr ⟨edgePoint G u v⟩
  have hpoint : Fintype.card
      {x : edgeBlock G u v // x = edgePoint G u v} = 1 := by simp
  rw [hpoint] at hcompl
  change Fintype.card
      {x : edgeBlock G u v // ¬x = edgePoint G u v} + 1 = G.degree u
  rw [hcompl, Fintype.card_coe, card_edgeBlock G huv]
  have hdeg : 0 < G.degree u := by
    rw [← card_edgeBlock G huv]
    exact card_pos.mpr ⟨u, mem_insert_self _ _⟩
  omega

private lemma edgeBlock_disjoint {u v : V} (huv : G.Adj u v)
    (htri : G.CliqueFree 3) :
    Disjoint (edgeBlock G u v) (edgeBlock G v u) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  simp only [edgeBlock, Finset.mem_insert, Finset.mem_sdiff,
    SimpleGraph.mem_neighborFinset, Finset.mem_singleton] at hxu hxv
  rcases hxu with rfl | ⟨hux, hne_v⟩
  · rcases hxv with huv' | ⟨hvu, hne_u⟩
    · exact huv.ne huv'
    · exact hne_u rfl
  · rcases hxv with rfl | ⟨hvx, hne_u⟩
    · exact hne_v rfl
    · exact htri {u, v, x} (SimpleGraph.is3Clique_triple_iff.mpr
        ⟨huv, hux, hvx⟩)

private lemma card_relative_edgeBlock {u v : V} (huv : G.Adj u v)
    (σ : V → Bool) :
    #((relativeColoringEquiv (edgePoint G u v)
        (fun x : edgeBlock G u v ↦ σ x)).2) =
      #((G.neighborFinset u \ {v}).filter fun x ↦ σ x ≠ σ u) := by
  let A := (relativeColoringEquiv (edgePoint G u v)
    (fun x : edgeBlock G u v ↦ σ x)).2
  let B := (G.neighborFinset u \ {v}).filter fun x ↦ σ x ≠ σ u
  apply Finset.card_bij (fun x _ ↦ (x.1.1 : V))
  · intro x hx
    have hxcolor : σ x.1.1 ≠ σ u := by
      simpa [A, relativeColoringEquiv, edgePoint] using
        (Finset.mem_filter.mp hx).2
    have hxbase : x.1.1 ∈ G.neighborFinset u \ {v} := by
      rcases Finset.mem_insert.mp x.1.2 with hxu | hxu
      · exfalso
        apply x.2
        apply Subtype.ext
        exact hxu
      · exact hxu
    exact Finset.mem_filter.mpr ⟨hxbase, hxcolor⟩
  · intro x₁ _ x₂ _ h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro b hb
    have hbbase := (Finset.mem_filter.mp hb).1
    have hbcolor := (Finset.mem_filter.mp hb).2
    have hbparts := Finset.mem_sdiff.mp hbbase
    have hbAdj : G.Adj u b := (G.mem_neighborFinset u b).mp hbparts.1
    let xb : edgeBlock G u v := ⟨b, Finset.mem_insert_of_mem hbbase⟩
    have hxb : xb ≠ edgePoint G u v := by
      intro h
      have hbu : b = u := by simpa [xb, edgePoint] using congrArg Subtype.val h
      exact hbAdj.ne hbu.symm
    refine ⟨⟨xb, hxb⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [A, relativeColoringEquiv, xb, edgePoint] using hbcolor⟩

/-- A vertex is stable when strictly more than half of its incident edges
cross the initial coloring. -/
private def vertexStable (σ : V → Bool) (u : V) : Prop :=
  G.degree u < 2 * #((G.neighborFinset u).filter fun x ↦ σ x ≠ σ u)

private def blockStableSame (u v : V) (a : edgeBlock G u v → Bool) : Prop :=
  stableSame ((relativeColoringEquiv (edgePoint G u v) a).2)

private def blockStableDifferent (u v : V) (a : edgeBlock G u v → Bool) : Prop :=
  stableDifferent ((relativeColoringEquiv (edgePoint G u v) a).2)

private instance (σ : V → Bool) (u : V) : Decidable (vertexStable G σ u) := by
  unfold vertexStable
  infer_instance

private instance (u v : V) (a : edgeBlock G u v → Bool) :
    Decidable (blockStableSame G u v a) := by
  unfold blockStableSame
  infer_instance

private instance (u v : V) (a : edgeBlock G u v → Bool) :
    Decidable (blockStableDifferent G u v a) := by
  unfold blockStableDifferent
  infer_instance

private lemma vertexStable_iff_block_same {u v : V} (huv : G.Adj u v)
    (σ : V → Bool) (hsame : σ u = σ v) :
    vertexStable G σ u ↔
      blockStableSame G u v (fun x : edgeBlock G u v ↦ σ x) := by
  have hv : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
  have hcount :
      #((G.neighborFinset u).filter fun x ↦ σ x ≠ σ u) =
        #((G.neighborFinset u \ {v}).filter fun x ↦ σ x ≠ σ u) := by
    rw [Finset.sdiff_singleton_eq_erase]
    conv_lhs => rw [← Finset.insert_erase hv]
    rw [Finset.filter_insert]
    have hvnot : ¬σ v ≠ σ u := by simpa using hsame.symm
    rw [if_neg hvnot]
  unfold vertexStable blockStableSame stableSame
  rw [hcount, ← card_relative_edgeBlock G huv, card_other_edgeBlock G huv]

private lemma vertexStable_iff_block_different {u v : V} (huv : G.Adj u v)
    (σ : V → Bool) (hdiff : σ u ≠ σ v) :
    vertexStable G σ u ↔
      blockStableDifferent G u v (fun x : edgeBlock G u v ↦ σ x) := by
  have hv : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
  have hcount :
      #((G.neighborFinset u).filter fun x ↦ σ x ≠ σ u) =
        #((G.neighborFinset u \ {v}).filter fun x ↦ σ x ≠ σ u) + 1 := by
    rw [Finset.sdiff_singleton_eq_erase]
    conv_lhs => rw [← Finset.insert_erase hv]
    have hvcolor : σ v ≠ σ u := fun h ↦ hdiff h.symm
    rw [Finset.filter_insert, if_pos hvcolor]
    rw [Finset.card_insert_of_notMem (by
      intro hm
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hm).1).1 rfl)]
  unfold vertexStable blockStableDifferent stableDifferent
  rw [hcount, ← card_relative_edgeBlock G huv, card_other_edgeBlock G huv]

private lemma block_fixed_same_expect {u v : V} (c : Bool) :
    (𝔼 a : edgeBlock G u v → Bool,
      if a (edgePoint G u v) = c ∧ blockStableSame G u v a
        then (1 : ℝ) else 0) =
      (1 : ℝ) / 2 *
        sameStableProb
          (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}) := by
  unfold blockStableSame sameStableProb
  exact relative_fixed_expect (edgePoint G u v) c
    (stableSame (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}))

private lemma block_fixed_different_expect {u v : V} (c : Bool) :
    (𝔼 a : edgeBlock G u v → Bool,
      if a (edgePoint G u v) = c ∧ blockStableDifferent G u v a
        then (1 : ℝ) else 0) =
      (1 : ℝ) / 2 *
        differentStableProb
          (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}) := by
  unfold blockStableDifferent differentStableProb
  exact relative_fixed_expect (edgePoint G u v) c
    (stableDifferent (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}))

private lemma expect_both_stable_same {u v : V} (huv : G.Adj u v)
    (htri : G.CliqueFree 3) :
    (𝔼 σ : V → Bool,
      if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u = σ v
        then (1 : ℝ) else 0) =
      sameStableProb
          (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}) *
        sameStableProb
          (α := {x : edgeBlock G v u // x ≠ edgePoint G v u}) / 2 := by
  let U := edgeBlock G u v
  let W := edgeBlock G v u
  have hdisj : Disjoint U W := edgeBlock_disjoint G huv htri
  have hpoint : ∀ σ : V → Bool,
      (if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u = σ v
        then (1 : ℝ) else 0) =
      ∑ c : Bool,
        (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) := by
    intro σ
    by_cases hs : σ u = σ v
    · have hu := vertexStable_iff_block_same G huv σ hs
      have hv := vertexStable_iff_block_same G huv.symm σ hs.symm
      by_cases hu' : blockStableSame G u v (fun x : U ↦ σ x) <;>
      by_cases hv' : blockStableSame G v u (fun x : W ↦ σ x) <;>
      cases hcu : σ u <;> cases hcv : σ v <;> simp_all <;> aesop
    · cases hcu : σ u <;> cases hcv : σ v <;> simp_all <;> aesop
  rw [show (𝔼 σ : V → Bool,
      if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u = σ v
        then (1 : ℝ) else 0) =
      𝔼 σ : V → Bool, ∑ c : Bool,
        (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) by congr 1; funext σ; exact hpoint σ]
  rw [show (𝔼 σ : V → Bool, ∑ c : Bool,
      (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
        then (1 : ℝ) else 0) *
      (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
        then (1 : ℝ) else 0)) =
      ∑ c : Bool, 𝔼 σ : V → Bool,
        (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) by
    simpa using (Finset.expect_sum_comm (univ : Finset (V → Bool))
      (univ : Finset Bool) (fun σ c ↦
        (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0)))]
  have hind (c : Bool) :
      (𝔼 σ : V → Bool,
        (if σ u = c ∧ blockStableSame G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = c ∧ blockStableSame G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0)) =
      (𝔼 a : U → Bool,
        if a (edgePoint G u v) = c ∧ blockStableSame G u v a
          then (1 : ℝ) else 0) *
      (𝔼 b : W → Bool,
        if b (edgePoint G v u) = c ∧ blockStableSame G v u b
          then (1 : ℝ) else 0) := by
    convert (expect_restrictions_mul U W hdisj
        (fun a : U → Bool ↦
          if a (edgePoint G u v) = c ∧ blockStableSame G u v a
            then (1 : ℝ) else 0)
        (fun b : W → Bool ↦
          if b (edgePoint G v u) = c ∧ blockStableSame G v u b
            then (1 : ℝ) else 0)) using 1 <;> rfl
  simp_rw [hind]
  dsimp only [U, W]
  simp_rw [block_fixed_same_expect]
  simp
  ring

private lemma expect_both_stable_different {u v : V} (huv : G.Adj u v)
    (htri : G.CliqueFree 3) :
    (𝔼 σ : V → Bool,
      if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u ≠ σ v
        then (1 : ℝ) else 0) =
      differentStableProb
          (α := {x : edgeBlock G u v // x ≠ edgePoint G u v}) *
        differentStableProb
          (α := {x : edgeBlock G v u // x ≠ edgePoint G v u}) / 2 := by
  let U := edgeBlock G u v
  let W := edgeBlock G v u
  have hdisj : Disjoint U W := edgeBlock_disjoint G huv htri
  have hpoint : ∀ σ : V → Bool,
      (if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u ≠ σ v
        then (1 : ℝ) else 0) =
      ∑ c : Bool,
        (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) := by
    intro σ
    by_cases hd : σ u ≠ σ v
    · have hu := vertexStable_iff_block_different G huv σ hd
      have hv := vertexStable_iff_block_different G huv.symm σ
        (fun h ↦ hd h.symm)
      by_cases hu' : blockStableDifferent G u v (fun x : U ↦ σ x) <;>
      by_cases hv' : blockStableDifferent G v u (fun x : W ↦ σ x) <;>
      cases hcu : σ u <;> cases hcv : σ v <;> simp_all <;> aesop
    · cases hcu : σ u <;> cases hcv : σ v <;> simp_all <;> aesop
  rw [show (𝔼 σ : V → Bool,
      if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u ≠ σ v
        then (1 : ℝ) else 0) =
      𝔼 σ : V → Bool, ∑ c : Bool,
        (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) by congr 1; funext σ; exact hpoint σ]
  rw [show (𝔼 σ : V → Bool, ∑ c : Bool,
      (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
        then (1 : ℝ) else 0) *
      (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
        then (1 : ℝ) else 0)) =
      ∑ c : Bool, 𝔼 σ : V → Bool,
        (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0) by
    simpa using (Finset.expect_sum_comm (univ : Finset (V → Bool))
      (univ : Finset Bool) (fun σ c ↦
        (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0)))]
  have hind (c : Bool) :
      (𝔼 σ : V → Bool,
        (if σ u = c ∧ blockStableDifferent G u v (fun x : U ↦ σ x)
          then (1 : ℝ) else 0) *
        (if σ v = !c ∧ blockStableDifferent G v u (fun x : W ↦ σ x)
          then (1 : ℝ) else 0)) =
      (𝔼 a : U → Bool,
        if a (edgePoint G u v) = c ∧ blockStableDifferent G u v a
          then (1 : ℝ) else 0) *
      (𝔼 b : W → Bool,
        if b (edgePoint G v u) = !c ∧ blockStableDifferent G v u b
          then (1 : ℝ) else 0) := by
    convert (expect_restrictions_mul U W hdisj
        (fun a : U → Bool ↦
          if a (edgePoint G u v) = c ∧ blockStableDifferent G u v a
            then (1 : ℝ) else 0)
        (fun b : W → Bool ↦
          if b (edgePoint G v u) = !c ∧ blockStableDifferent G v u b
            then (1 : ℝ) else 0)) using 1 <;> rfl
  simp_rw [hind]
  dsimp only [U, W]
  simp_rw [block_fixed_different_expect]
  simp
  ring

private lemma expect_coloring_coord_eq (u : V) (c : Bool) :
    (𝔼 σ : V → Bool, if σ u = c then (1 : ℝ) else 0) = 1 / 2 := by
  have h := relative_fixed_expect u c (fun _ : Finset {x : V // x ≠ u} ↦ True)
  simpa using h

private lemma expect_coloring_coord_ne (u : V) (c : Bool) :
    (𝔼 σ : V → Bool, if σ u ≠ c then (1 : ℝ) else 0) = 1 / 2 := by
  cases c
  · simpa using expect_coloring_coord_eq (V := V) u true
  · simpa using expect_coloring_coord_eq (V := V) u false

private lemma expect_coloring_pair_ne {u v : V} (hne : u ≠ v) :
    (𝔼 σ : V → Bool, if σ u ≠ σ v then (1 : ℝ) else 0) = 1 / 2 := by
  let U : Finset V := {u}
  let W : Finset V := {v}
  have hdisj : Disjoint U W := by
    simp [U, W, hne]
  have hpoint : ∀ σ : V → Bool,
      (if σ u ≠ σ v then (1 : ℝ) else 0) =
        ∑ c : Bool, (if σ u = c then (1 : ℝ) else 0) *
          (if σ v = !c then (1 : ℝ) else 0) := by
    intro σ
    cases hu : σ u <;> cases hv : σ v <;> simp_all
  rw [show (𝔼 σ : V → Bool, if σ u ≠ σ v then (1 : ℝ) else 0) =
      𝔼 σ : V → Bool,
        ∑ c : Bool, (if σ u = c then (1 : ℝ) else 0) *
          (if σ v = !c then (1 : ℝ) else 0) by
    congr 1
    funext σ
    exact hpoint σ]
  rw [show (𝔼 σ : V → Bool,
      ∑ c : Bool, (if σ u = c then (1 : ℝ) else 0) *
        (if σ v = !c then (1 : ℝ) else 0)) =
      ∑ c : Bool, 𝔼 σ : V → Bool,
        (if σ u = c then (1 : ℝ) else 0) *
          (if σ v = !c then (1 : ℝ) else 0) by
    simpa using (Finset.expect_sum_comm (univ : Finset (V → Bool))
      (univ : Finset Bool) (fun σ c ↦
        (if σ u = c then (1 : ℝ) else 0) *
          (if σ v = !c then (1 : ℝ) else 0)))]
  have hind (c : Bool) :
      (𝔼 σ : V → Bool, (if σ u = c then (1 : ℝ) else 0) *
        (if σ v = !c then (1 : ℝ) else 0)) =
      (𝔼 a : U → Bool, if a ⟨u, by simp [U]⟩ = c then (1 : ℝ) else 0) *
      (𝔼 b : W → Bool, if b ⟨v, by simp [W]⟩ = !c then (1 : ℝ) else 0) := by
    convert (expect_restrictions_mul U W hdisj
      (fun a : U → Bool ↦ if a ⟨u, by simp [U]⟩ = c then (1 : ℝ) else 0)
      (fun b : W → Bool ↦ if b ⟨v, by simp [W]⟩ = !c then (1 : ℝ) else 0)) using 1 <;> rfl
  simp_rw [hind]
  have hU (c : Bool) :
      (𝔼 a : U → Bool, if a ⟨u, by simp [U]⟩ = c then (1 : ℝ) else 0) =
        1 / 2 := expect_coloring_coord_eq (V := U) ⟨u, by simp [U]⟩ c
  have hW (c : Bool) :
      (𝔼 b : W → Bool, if b ⟨v, by simp [W]⟩ = c then (1 : ℝ) else 0) =
        1 / 2 := expect_coloring_coord_eq (V := W) ⟨v, by simp [W]⟩ c
  simp_rw [hU, hW]
  simp

private def recolor (σ τ : V → Bool) (u : V) : Bool :=
  if vertexStable G σ u then σ u else τ u

private lemma expect_recolored_edge {u v : V} (hne : u ≠ v) (σ : V → Bool) :
    (𝔼 τ : V → Bool,
      if recolor G σ τ u ≠ recolor G σ τ v then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 *
        ((if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u ≠ σ v
            then (1 : ℝ) else 0) -
          (if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u = σ v
            then (1 : ℝ) else 0)) := by
  by_cases hu : vertexStable G σ u <;> by_cases hv : vertexStable G σ v
  · by_cases hc : σ u = σ v
    · norm_num [recolor, hu, hv, hc]
    · norm_num [recolor, hu, hv, hc]
  · simpa [recolor, hu, hv, ne_comm] using
      expect_coloring_coord_ne (V := V) v (σ u)
  · simpa [recolor, hu, hv] using expect_coloring_coord_ne (V := V) u (σ v)
  · simpa [recolor, hu, hv] using expect_coloring_pair_ne (V := V) hne

private lemma expect_recolored_edge_gain {u v : V} (huv : G.Adj u v)
    (htri : G.CliqueFree 3) :
    (1 : ℝ) / 2 +
        (degreeInfluence (G.degree u) + degreeInfluence (G.degree v)) / 16 ≤
      𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
        if recolor G σ τ u ≠ recolor G σ τ v then (1 : ℝ) else 0 := by
  let α := {x : edgeBlock G u v // x ≠ edgePoint G u v}
  let β := {x : edgeBlock G v u // x ≠ edgePoint G v u}
  let D : (V → Bool) → ℝ := fun σ ↦
    if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u ≠ σ v then 1 else 0
  let S : (V → Bool) → ℝ := fun σ ↦
    if vertexStable G σ u ∧ vertexStable G σ v ∧ σ u = σ v then 1 else 0
  have hinner : (𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
      if recolor G σ τ u ≠ recolor G σ τ v then (1 : ℝ) else 0) =
      Finset.expect univ
        (fun σ : V → Bool ↦ (1 : ℝ) / 2 + 1 / 2 * (D σ - S σ)) := by
    congr 1
    funext σ
    simpa [D, S] using expect_recolored_edge G huv.ne σ
  have havg : Finset.expect univ
      (fun σ : V → Bool ↦ (1 : ℝ) / 2 + 1 / 2 * (D σ - S σ)) =
      1 / 2 + 1 / 2 *
        ((𝔼 σ : V → Bool, D σ) - (𝔼 σ : V → Bool, S σ)) := by
    calc
      Finset.expect univ
          (fun σ : V → Bool ↦ (1 : ℝ) / 2 + 1 / 2 * (D σ - S σ)) =
          (𝔼 _σ : V → Bool, (1 : ℝ) / 2) +
            Finset.expect univ (fun σ : V → Bool ↦ 1 / 2 * (D σ - S σ)) :=
        Finset.expect_add_distrib univ _ _
      _ = 1 / 2 + 1 / 2 *
          Finset.expect univ (fun σ : V → Bool ↦ D σ - S σ) := by
        rw [Fintype.expect_const]
        congr 1
        exact (Finset.mul_expect univ (fun σ ↦ D σ - S σ) (1 / 2)).symm
      _ = 1 / 2 + 1 / 2 *
          ((𝔼 σ : V → Bool, D σ) - (𝔼 σ : V → Bool, S σ)) := by
        rw [Finset.expect_sub_distrib]
  have hD : (𝔼 σ : V → Bool, D σ) =
      differentStableProb (α := α) * differentStableProb (α := β) / 2 := by
    simpa [D, α, β] using expect_both_stable_different G huv htri
  have hS : (𝔼 σ : V → Bool, S σ) =
      sameStableProb (α := α) * sameStableProb (α := β) / 2 := by
    simpa [S, α, β] using expect_both_stable_same G huv htri
  rw [hinner, havg, hD, hS]
  have hlocal := local_product_gain (α := α) (β := β)
  have hα := card_other_edgeBlock G huv
  have hβ := card_other_edgeBlock G huv.symm
  dsimp only [α, β] at hα hβ hlocal
  rw [hα, hβ] at hlocal
  calc
    (1 : ℝ) / 2 +
        (degreeInfluence (G.degree u) + degreeInfluence (G.degree v)) / 16 ≤
      1 / 2 + 1 / 4 *
        (differentStableProb (α := α) * differentStableProb (α := β) -
          sameStableProb (α := α) * sameStableProb (α := β)) :=
      by simpa [add_comm] using add_le_add_left hlocal (1 / 2)
    _ = 1 / 2 + 1 / 2 *
        (differentStableProb (α := α) * differentStableProb (α := β) / 2 -
          sameStableProb (α := α) * sameStableProb (α := β) / 2) := by ring

private def colorSet (c : V → Bool) : Set V :=
  {v | c v = true}

private def crosses (c : V → Bool) : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v ↦ c u ≠ c v, fun u v ↦ propext ne_comm⟩

private noncomputable instance (c : V → Bool) (e : Sym2 V) :
    Decidable (crosses c e) := Classical.propDecidable _

private noncomputable def cutSize (c : V → Bool) : ℝ :=
  ((cutGraph G (colorSet c)).edgeSet.ncard : ℝ)

private lemma cutGraph_adj_color (c : V → Bool) (u v : V) :
    (cutGraph G (colorSet c)).Adj u v ↔ G.Adj u v ∧ c u ≠ c v := by
  rw [cutGraph_adj]
  unfold colorSet
  cases hu : c u <;> cases hv : c v <;> simp_all

private lemma cutSize_eq_sum (c : V → Bool) :
    cutSize G c =
      ∑ e ∈ G.edgeFinset, if crosses c e then (1 : ℝ) else 0 := by
  classical
  have hedge : (cutGraph G (colorSet c)).edgeFinset =
      G.edgeFinset.filter (crosses c) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      rw [Finset.mem_filter]
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        crosses, Sym2.lift_mk] using
        cutGraph_adj_color G c u v
  unfold cutSize
  rw [Set.ncard_eq_toFinset_card']
  change (((cutGraph G (colorSet c)).edgeFinset.card : ℕ) : ℝ) = _
  rw [hedge, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e _he
  by_cases h : crosses c e <;> simp [h]

private noncomputable def edgeWeight (a : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v ↦ a u + a v, fun u v ↦ by simp [add_comm]⟩

private lemma sum_dart_fst_fiber (a : V → ℝ) (v : V) :
    (∑ d : {d : G.Dart // d.fst = v}, a d.val.fst) =
      (G.degree v : ℝ) * a v := by
  calc
    (∑ d : {d : G.Dart // d.fst = v}, a d.val.fst) =
        ∑ _d : {d : G.Dart // d.fst = v}, a v := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [d.property]
    _ = (Fintype.card {d : G.Dart // d.fst = v} : ℝ) * a v := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = (G.degree v : ℝ) * a v := by
      congr 1
      norm_cast
      rw [Fintype.card_subtype]
      change #{d : G.Dart | d.fst = v} = G.degree v
      exact G.dart_fst_fiber_card_eq_degree v

private lemma sum_darts_eq_vertex (a : V → ℝ) :
    (∑ d : G.Dart, a d.fst) = ∑ v, (G.degree v : ℝ) * a v := by
  rw [← Fintype.sum_fiberwise (fun d : G.Dart ↦ d.fst) (fun d ↦ a d.fst)]
  apply Finset.sum_congr rfl
  intro v _hv
  exact sum_dart_fst_fiber G a v

private lemma sum_dart_edge_fiber (a : V → ℝ) (e : Sym2 V)
    (he : e ∈ G.edgeFinset) :
    (∑ d ∈ (Finset.univ : Finset G.Dart) with d.edge = e, a d.fst) =
      edgeWeight a e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : G.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    let d : G.Dart := ⟨(u, v), huv⟩
    change (∑ d' ∈ (Finset.univ : Finset G.Dart) with d'.edge = d.edge,
      a d'.fst) = _
    rw [show (Finset.univ.filter fun d' : G.Dart ↦ d'.edge = d.edge) =
        {d, d.symm} by exact d.edge_fiber]
    rw [Finset.sum_insert (by simpa using d.symm_ne.symm), Finset.sum_singleton]
    simp [d, edgeWeight]

private lemma weighted_handshake (a : V → ℝ) :
    (∑ e ∈ G.edgeFinset, edgeWeight a e) =
      ∑ v, (G.degree v : ℝ) * a v := by
  calc
    (∑ e ∈ G.edgeFinset, edgeWeight a e) =
        ∑ e ∈ G.edgeFinset,
          ∑ d ∈ (Finset.univ : Finset G.Dart) with d.edge = e, a d.fst := by
      apply Finset.sum_congr rfl
      intro e he
      exact (sum_dart_edge_fiber G a e he).symm
    _ = ∑ d : G.Dart, a d.fst := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
        (g := SimpleGraph.Dart.edge)
        (fun d _hd ↦ by
          rw [SimpleGraph.mem_edgeFinset]
          exact d.edge_mem)
        (fun d ↦ a d.fst)
    _ = ∑ v, (G.degree v : ℝ) * a v := sum_darts_eq_vertex G a

private lemma exists_ge_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) : ∃ ω, (𝔼 x : Ω, f x) ≤ f ω := by
  by_contra h
  push_neg at h
  have hsum : (∑ ω : Ω, f ω) < ∑ _ω : Ω, (𝔼 x : Ω, f x) := by
    apply Finset.sum_lt_sum
    · intro ω _hω
      exact (h ω).le
    · exact ⟨Classical.choice (inferInstance : Nonempty Ω), Finset.mem_univ _, h _⟩
  rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_mul_expect f] at hsum
  exact (lt_irrefl _ hsum)

private lemma expected_cut_ge (htri : G.CliqueFree 3) :
    (∑ e ∈ G.edgeFinset,
        ((1 : ℝ) / 2 + edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e / 16)) ≤
      (𝔼 σ : V → Bool, 𝔼 τ : V → Bool, cutSize G (recolor G σ τ)) := by
  simp_rw [cutSize_eq_sum]
  calc
    (∑ e ∈ G.edgeFinset,
        ((1 : ℝ) / 2 + edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e / 16)) ≤
        ∑ e ∈ G.edgeFinset, 𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
          if crosses (recolor G σ τ) e then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
        have huv : G.Adj u v := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
        have hrhs :
            (𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
              if crosses (recolor G σ τ) s(u, v) then (1 : ℝ) else 0) =
            (𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
              if recolor G σ τ u ≠ recolor G σ τ v then (1 : ℝ) else 0) := by
          apply Finset.expect_congr rfl
          intro σ _hσ
          apply Finset.expect_congr rfl
          intro τ _hτ
          by_cases h : recolor G σ τ u ≠ recolor G σ τ v <;>
            simp [crosses, h]
        rw [hrhs]
        simpa only [edgeWeight, Sym2.lift_mk] using
          expect_recolored_edge_gain G huv htri
    _ = 𝔼 σ : V → Bool, ∑ e ∈ G.edgeFinset, 𝔼 τ : V → Bool,
          if crosses (recolor G σ τ) e then (1 : ℝ) else 0 := by
      exact (Finset.expect_sum_comm (univ : Finset (V → Bool)) G.edgeFinset
        (fun σ e ↦ 𝔼 τ : V → Bool,
          if crosses (recolor G σ τ) e then (1 : ℝ) else 0)).symm
    _ = 𝔼 σ : V → Bool, 𝔼 τ : V → Bool,
          ∑ e ∈ G.edgeFinset,
            if crosses (recolor G σ τ) e then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro σ _hσ
      exact (Finset.expect_sum_comm (univ : Finset (V → Bool)) G.edgeFinset
        (fun τ e ↦ if crosses (recolor G σ τ) e then (1 : ℝ) else 0)).symm

private lemma sum_edge_gain_eq :
    (∑ e ∈ G.edgeFinset,
        ((1 : ℝ) / 2 + edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e / 16)) =
      (G.edgeFinset.card : ℝ) / 2 +
        (∑ v, (G.degree v : ℝ) * degreeInfluence (G.degree v)) / 16 := by
  have hw := weighted_handshake G (fun v ↦ degreeInfluence (G.degree v))
  calc
    (∑ e ∈ G.edgeFinset,
        ((1 : ℝ) / 2 + edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e / 16)) =
        (∑ _e ∈ G.edgeFinset, (1 : ℝ) / 2) +
          (∑ e ∈ G.edgeFinset,
            edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e) / 16 := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = (G.edgeFinset.card : ℝ) / 2 +
        (∑ v, (G.degree v : ℝ) * degreeInfluence (G.degree v)) / 16 := by
      rw [hw]
      simp [nsmul_eq_mul]
      ring

private lemma exists_recolored_cut_ge (htri : G.CliqueFree 3) :
    ∃ σ τ : V → Bool,
      (∑ e ∈ G.edgeFinset,
          ((1 : ℝ) / 2 + edgeWeight (fun v ↦ degreeInfluence (G.degree v)) e / 16)) ≤
        cutSize G (recolor G σ τ) := by
  have havg := expected_cut_ge G htri
  obtain ⟨σ, hσ⟩ := exists_ge_expect
    (fun σ : V → Bool ↦ 𝔼 τ : V → Bool, cutSize G (recolor G σ τ))
  obtain ⟨τ, hτ⟩ := exists_ge_expect
    (fun τ : V → Bool ↦ cutSize G (recolor G σ τ))
  exact ⟨σ, τ, havg.trans (hσ.trans hτ)⟩

/-- A triangle-free graph has a cut whose surplus is bounded below by the
sum of the stable-vertex influences. -/
theorem exists_cut_degreeInfluence (htri : G.CliqueFree 3) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 +
          (∑ v, (G.degree v : ℝ) * degreeInfluence (G.degree v)) / 16 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  obtain ⟨σ, τ, hcut⟩ := exists_recolored_cut_ge G htri
  refine ⟨colorSet (recolor G σ τ), ?_⟩
  rw [← sum_edge_gain_eq G]
  simpa only [cutSize] using hcut

/-- The degree-sum form of Alon's stable-vertex cut lemma. -/
theorem exists_cut_sqrtDegree (htri : G.CliqueFree 3) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 +
          (∑ v, Real.sqrt (G.degree v : ℝ)) / 32 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  obtain ⟨s, hs⟩ := exists_cut_degreeInfluence G htri
  refine ⟨s, ?_⟩
  apply le_trans ?_ hs
  have hpoint : ∀ v : V,
      Real.sqrt (G.degree v : ℝ) ≤
        2 * (G.degree v : ℝ) * degreeInfluence (G.degree v) := by
    intro v
    by_cases hd : G.degree v = 0
    · simp [hd]
    · exact sqrt_degree_le_two_mul_degreeInfluence (Nat.one_le_iff_ne_zero.mpr hd)
  have hsum : (∑ v, Real.sqrt (G.degree v : ℝ)) ≤
      ∑ v, 2 * (G.degree v : ℝ) * degreeInfluence (G.degree v) :=
    Finset.sum_le_sum fun v _hv ↦ hpoint v
  have hsum' : (∑ v, Real.sqrt (G.degree v : ℝ)) ≤
      2 * ∑ v, (G.degree v : ℝ) * degreeInfluence (G.degree v) := by
    apply hsum.trans_eq
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    ring
  have hnonneg : 0 ≤
      ∑ v, (G.degree v : ℝ) * degreeInfluence (G.degree v) := by
    apply Finset.sum_nonneg
    intro v _hv
    exact mul_nonneg (by positivity) (le_of_lt (centralProb_pos _))
  nlinarith

/-! ## Extending a cut from an induced vertex set -/

/-- The ambient edges which lie inside `T` and cross the partial cut `A`. -/
noncomputable def partialCutEdges (T A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦
    e.toFinset ⊆ T ∧ crosses (fun v ↦ decide (v ∈ A)) e

private def extendColor (T A : Finset V) (tau : V → Bool) (v : V) : Bool :=
  if v ∈ T then decide (v ∈ A) else tau v

private lemma expect_extendColor_edge {T A : Finset V} {u v : V}
    (hne : u ≠ v) :
    (𝔼 tau : V → Bool,
      if extendColor T A tau u ≠ extendColor T A tau v then (1 : ℝ) else 0) =
      if u ∈ T ∧ v ∈ T then
        (if (u ∈ A) ≠ (v ∈ A) then (1 : ℝ) else 0)
      else 1 / 2 := by
  by_cases huT : u ∈ T <;> by_cases hvT : v ∈ T
  · simp [extendColor, huT, hvT]
  · simpa [extendColor, huT, hvT, ne_comm] using
      (expect_coloring_coord_ne (V := V) v (decide (u ∈ A)))
  · simpa [extendColor, huT, hvT, ne_comm] using
      (expect_coloring_coord_ne (V := V) u (decide (v ∈ A)))
  · simpa [extendColor, huT, hvT] using
      (expect_coloring_pair_ne (V := V) hne)

private lemma expect_extended_cut (T A : Finset V) :
    (𝔼 tau : V → Bool, cutSize G (extendColor T A tau)) =
      (partialCutEdges G T A).card +
        ((G.edgeFinset.card : ℝ) -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ)) / 2 := by
  classical
  simp_rw [cutSize_eq_sum]
  rw [show
      (𝔼 tau : V → Bool,
        ∑ e ∈ G.edgeFinset,
          if crosses (extendColor T A tau) e then (1 : ℝ) else 0) =
        ∑ e ∈ G.edgeFinset, 𝔼 tau : V → Bool,
          if crosses (extendColor T A tau) e then (1 : ℝ) else 0 by
    exact Finset.expect_sum_comm (univ : Finset (V → Bool)) G.edgeFinset
      (fun tau e ↦ if crosses (extendColor T A tau) e then (1 : ℝ) else 0)]
  have hedge (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (𝔼 tau : V → Bool,
        if crosses (extendColor T A tau) e then (1 : ℝ) else 0) =
      (if e.toFinset ⊆ T then
        (if crosses (fun v ↦ decide (v ∈ A)) e then (1 : ℝ) else 0)
      else 1 / 2) := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have h := expect_extendColor_edge (V := V) (T := T) (A := A) huv.ne
      have hlhs :
          (𝔼 tau : V → Bool,
            if crosses (extendColor T A tau) s(u, v) then (1 : ℝ) else 0) =
          (𝔼 tau : V → Bool,
            if extendColor T A tau u ≠ extendColor T A tau v then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro tau _htau
        by_cases heq : extendColor T A tau u = extendColor T A tau v <;>
          simp [crosses, heq]
      rw [hlhs]
      by_cases huT : u ∈ T <;> by_cases hvT : v ∈ T
      · have hsub : (s(u, v)).toFinset ⊆ T := by
          rw [Sym2.toFinset_mk_eq]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact huT
          · exact hvT
        simpa [crosses, hsub, huT, hvT] using h
      · have hsub : ¬(s(u, v)).toFinset ⊆ T := by
          intro hs
          apply hvT
          apply hs
          rw [Sym2.toFinset_mk_eq]
          simp
        simpa [crosses, hsub, huT, hvT] using h
      · have hsub : ¬(s(u, v)).toFinset ⊆ T := by
          intro hs
          apply huT
          apply hs
          rw [Sym2.toFinset_mk_eq]
          simp
        simpa [crosses, hsub, huT, hvT] using h
      · have hsub : ¬(s(u, v)).toFinset ⊆ T := by
          intro hs
          apply huT
          apply hs
          rw [Sym2.toFinset_mk_eq]
          simp
        simpa [crosses, hsub, huT, hvT] using h
  rw [show
      (∑ e ∈ G.edgeFinset, 𝔼 tau : V → Bool,
        if crosses (extendColor T A tau) e then (1 : ℝ) else 0) =
      ∑ e ∈ G.edgeFinset,
        if e.toFinset ⊆ T then
          (if crosses (fun v ↦ decide (v ∈ A)) e then (1 : ℝ) else 0)
        else 1 / 2 by
    apply Finset.sum_congr rfl
    intro e he
    exact hedge e he]
  have hpoint (e : Sym2 V) :
      (if e.toFinset ⊆ T then
          (if crosses (fun v ↦ decide (v ∈ A)) e then (1 : ℝ) else 0)
        else 1 / 2) =
      (if e.toFinset ⊆ T ∧ crosses (fun v ↦ decide (v ∈ A)) e
        then (1 : ℝ) else 0) +
      (if e.toFinset ⊆ T then 0 else (1 : ℝ) / 2) := by
    by_cases hi : e.toFinset ⊆ T <;>
      by_cases hc : crosses (fun v ↦ decide (v ∈ A)) e <;> simp [hi, hc]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  have hpartial :
      (∑ e ∈ G.edgeFinset,
        if e.toFinset ⊆ T ∧ crosses (fun v ↦ decide (v ∈ A)) e
          then (1 : ℝ) else 0) = (partialCutEdges G T A).card := by
    simpa [partialCutEdges] using
      (Finset.sum_boole
        (R := ℝ) (fun e ↦ e.toFinset ⊆ T ∧
          crosses (fun v ↦ decide (v ∈ A)) e) G.edgeFinset)
  rw [hpartial]
  have hinternal :
      #{e ∈ G.edgeFinset | e.toFinset ⊆ T} =
        #(G.induce (T : Set V)).edgeFinset :=
    G.card_filter_edgeFinset_toFinset_subset T
  have houtside :
      (∑ e ∈ G.edgeFinset, if e.toFinset ⊆ T then (0 : ℝ) else 1 / 2) =
        ((G.edgeFinset.card : ℝ) -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ)) / 2 := by
    have hfilterNot :
        (∑ e ∈ G.edgeFinset, if ¬e.toFinset ⊆ T then (1 : ℝ) else 0) =
          ((G.edgeFinset.filter fun e ↦ ¬e.toFinset ⊆ T).card : ℝ) := by
      simpa using
        (Finset.sum_boole (R := ℝ)
          (fun e ↦ ¬e.toFinset ⊆ T) G.edgeFinset)
    calc
      (∑ e ∈ G.edgeFinset, if e.toFinset ⊆ T then (0 : ℝ) else 1 / 2) =
          (∑ e ∈ G.edgeFinset, if ¬e.toFinset ⊆ T then (1 : ℝ) else 0) / 2 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro e _he
            by_cases hi : e.toFinset ⊆ T <;> simp [hi]
      _ = ((G.edgeFinset.filter fun e ↦ ¬e.toFinset ⊆ T).card : ℝ) / 2 := by
            rw [hfilterNot]
      _ = ((G.edgeFinset.card : ℝ) -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ)) / 2 := by
            rw [Finset.filter_not,
              Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
              Nat.cast_sub (Finset.card_filter_le _ _), hinternal]
  rw [houtside]

/-- A cut of the graph induced by `T` extends to the whole graph without
losing any of its surplus over one half.  `A` records the chosen side of the
partial cut. -/
theorem exists_cut_extending_finset (T A : Finset V) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 + (partialCutEdges G T A).card -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ) / 2 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  obtain ⟨tau, htau⟩ := exists_ge_expect
    (fun tau : V → Bool ↦ cutSize G (extendColor T A tau))
  refine ⟨colorSet (extendColor T A tau), ?_⟩
  rw [expect_extended_cut G T A] at htau
  simpa only [cutSize] using (show
    (G.edgeFinset.card : ℝ) / 2 + (partialCutEdges G T A).card -
        ((G.induce (T : Set V)).edgeFinset.card : ℝ) / 2 ≤
      cutSize G (extendColor T A tau) by
    nlinarith [htau])

/-- The image in the ambient vertex type of a finset of vertices of an
induced graph. -/
noncomputable def liftInducedFinset (T : Finset V) (A : Finset T) : Finset V :=
  A.map (Function.Embedding.subtype (fun v ↦ v ∈ (T : Set V)))

/-- The edge finset of a cut inside an induced graph, with classical
decidability made explicit. -/
noncomputable def inducedCutEdges (T : Finset V) (A : Finset T) :
    Finset (Sym2 T) :=
  open scoped Classical in
  (cutGraph (G.induce (T : Set V)) (A : Set T)).edgeSet.toFinset

private lemma card_inducedCutEdges_eq_partial (T : Finset V) (A : Finset T) :
    (inducedCutEdges G T A).card =
      (partialCutEdges G T (liftInducedFinset T A)).card := by
  classical
  let emb := (Function.Embedding.subtype
    (fun v ↦ v ∈ (T : Set V))).sym2Map
  apply Finset.card_bij (fun w _hw ↦ emb w)
  · intro w hw
    induction w using Sym2.inductionOn with
    | _ a b =>
      have hw' : (G.induce (T : Set V)).Adj a b ∧
          ((a ∈ (A : Set T)) ≠ (b ∈ (A : Set T))) := by
        simpa [inducedCutEdges, cutGraph_adj, SimpleGraph.mem_edgeSet] using hw
      have hsub : ({(a : V), (b : V)} : Finset V) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact a.property
        · exact b.property
      have hne : ((a : V) ∈ liftInducedFinset T A) ≠
          ((b : V) ∈ liftInducedFinset T A) := by
        simpa [liftInducedFinset] using hw'.2
      simpa [emb, partialCutEdges, crosses, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, hsub] using
        (show G.Adj (a : V) (b : V) ∧
          (((a : V) ∈ liftInducedFinset T A) ≠
            ((b : V) ∈ liftInducedFinset T A)) from ⟨hw'.1, hne⟩)
  · intro w₁ _hw₁ w₂ _hw₂ heq
    exact emb.injective heq
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have h' : G.Adj u v ∧ (s(u, v)).toFinset ⊆ T ∧
        ((u ∈ liftInducedFinset T A) ≠ (v ∈ liftInducedFinset T A)) := by
        simpa [partialCutEdges, crosses, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he
      have huT : u ∈ T := h'.2.1 (by
        rw [Sym2.toFinset_mk_eq]
        simp)
      have hvT : v ∈ T := h'.2.1 (by
        rw [Sym2.toFinset_mk_eq]
        simp)
      let a : T := ⟨u, huT⟩
      let b : T := ⟨v, hvT⟩
      have hneAB : (a ∈ A) ≠ (b ∈ A) := by
        intro hab
        apply h'.2.2
        have hua : (∃ x : u ∈ T, (⟨u, x⟩ : T) ∈ A) ↔ a ∈ A := by
          constructor
          · rintro ⟨x, hx⟩
            simpa [a] using hx
          · intro hx
            exact ⟨huT, by simpa [a] using hx⟩
        have hvb : (∃ x : v ∈ T, (⟨v, x⟩ : T) ∈ A) ↔ b ∈ A := by
          constructor
          · rintro ⟨x, hx⟩
            simpa [b] using hx
          · intro hx
            exact ⟨hvT, by simpa [b] using hx⟩
        apply propext
        simpa [liftInducedFinset] using
          (hua.trans ((Iff.of_eq hab).trans hvb.symm))
      refine ⟨s(a, b), ?_, ?_⟩
      · simpa [inducedCutEdges, cutGraph_adj, SimpleGraph.mem_edgeSet,
          a, b, h'.1, hneAB]
      · simp [emb, a, b]

/-- Graph-valued form of `exists_cut_extending_finset`: a cut of the graph
induced by `T` extends to the ambient graph with the same surplus over half
of the induced edge count. -/
theorem exists_cut_extending_induced (T : Finset V) (A : Finset T) :
    ∃ s : Set V,
      (G.edgeFinset.card : ℝ) / 2 +
          ((inducedCutEdges G T A).card : ℝ) -
          ((G.induce (T : Set V)).edgeFinset.card : ℝ) / 2 ≤
        ((cutGraph G s).edgeSet.ncard : ℝ) := by
  obtain ⟨s, hs⟩ := exists_cut_extending_finset G T (liftInducedFinset T A)
  refine ⟨s, ?_⟩
  rw [card_inducedCutEdges_eq_partial G T A]
  exact hs


end GraphBlocks

end LocalProbabilities

end Erdos581
