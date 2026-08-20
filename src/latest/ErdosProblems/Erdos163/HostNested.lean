/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostTools
import Mathlib.Data.List.Chain

/-!
# Same-colour nested dependent random choice

The all-direction host lemma starts from a nested chain in one of the two
colours.  This file proves the one-step density and DRC facts with explicit
finite cardinalities.  A fixed lower cardinality reserve is carried through
the iteration, avoiding floors and asymptotic notation.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace HostNested

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

def colorGraph (G : SimpleGraph α) : Bool → SimpleGraph α
  | false => G
  | true => Gᶜ

instance colorGraph_decidableAdj (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) : DecidableRel (colorGraph G c).Adj := by
  cases c <;> simp only [colorGraph] <;> infer_instance

@[simp] theorem colorGraph_false (G : SimpleGraph α) : colorGraph G false = G := rfl

@[simp] theorem colorGraph_true (G : SimpleGraph α) : colorGraph G true = Gᶜ := rfl

theorem neighborFilters_card_add
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) {y : α} (hy : y ∈ S) :
    (S.filter fun z => G.Adj z y).card +
        (S.filter fun z => Gᶜ.Adj z y).card = S.card - 1 := by
  classical
  let R := S.filter fun z => G.Adj z y
  let B := S.filter fun z => Gᶜ.Adj z y
  have hdis : Disjoint R B := by
    rw [Finset.disjoint_left]
    intro z hzR hzB
    have hr : G.Adj z y := (Finset.mem_filter.mp hzR).2
    have hb : Gᶜ.Adj z y := (Finset.mem_filter.mp hzB).2
    simpa [SimpleGraph.compl_adj, hr] using hb
  have hunion : R ∪ B = S.erase y := by
    ext z
    simp only [R, B, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hzS, hz⟩ | ⟨hzS, hz⟩)
      · exact ⟨G.ne_of_adj hz, hzS⟩
      · exact ⟨by
          simpa [SimpleGraph.compl_adj] using Gᶜ.ne_of_adj hz, hzS⟩
    · rintro ⟨hzy, hzS⟩
      by_cases hz : G.Adj z y
      · exact Or.inl ⟨hzS, hz⟩
      · exact Or.inr ⟨hzS, by simpa [SimpleGraph.compl_adj, hzy, hz]⟩
  calc
    (S.filter fun z => G.Adj z y).card +
          (S.filter fun z => Gᶜ.Adj z y).card = (R ∪ B).card := by
      simpa [R, B] using (Finset.card_union_of_disjoint hdis).symm
    _ = (S.erase y).card := congrArg Finset.card hunion
    _ = S.card - 1 := Finset.card_erase_of_mem hy

theorem edgeMass_add_compl
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) :
    DRC.edgeMass G S S + DRC.edgeMass Gᶜ S S = S.card * (S.card - 1) := by
  classical
  unfold DRC.edgeMass
  calc
    (∑ y ∈ S, (S.filter fun z => G.Adj z y).card) +
          ∑ y ∈ S, (S.filter fun z => Gᶜ.Adj z y).card =
        ∑ y ∈ S, ((S.filter fun z => G.Adj z y).card +
          (S.filter fun z => Gᶜ.Adj z y).card) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ _y ∈ S, (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact neighborFilters_card_add G S hy
    _ = S.card * (S.card - 1) := by simp

/-- On a set of at least two vertices, one colour has oriented edge density
at least `1/4`.  The slack from `1/2` absorbs the missing diagonal. -/
theorem exists_color_density_quarter
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : 2 ≤ S.card) :
    ∃ c : Bool,
      (1 / 4 : ℝ) * S.card * S.card ≤
        DRC.edgeMass (colorGraph G c) S S := by
  classical
  have htotal := edgeMass_add_compl G S
  have hquad : S.card * S.card ≤ 2 * (S.card * (S.card - 1)) := by
    calc
      S.card * S.card ≤ S.card * (2 * (S.card - 1)) := by
        gcongr
        omega
      _ = 2 * (S.card * (S.card - 1)) := by ring
  by_cases hred : S.card * (S.card - 1) ≤ 2 * DRC.edgeMass G S S
  · refine ⟨false, ?_⟩
    simp only [colorGraph_false]
    have hnat : S.card * S.card ≤ 4 * DRC.edgeMass G S S :=
      hquad.trans (by omega)
    rw [show (1 / 4 : ℝ) * S.card * S.card =
      (S.card : ℝ) * S.card / 4 by ring]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
      have : ((S.card * S.card : ℕ) : ℝ) ≤
          ((4 * DRC.edgeMass G S S : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa [Nat.cast_mul, mul_comm] using this)
  · refine ⟨true, ?_⟩
    simp only [colorGraph_true]
    have hblue : S.card * (S.card - 1) ≤ 2 * DRC.edgeMass Gᶜ S S := by
      omega
    have hnat : S.card * S.card ≤ 4 * DRC.edgeMass Gᶜ S S :=
      hquad.trans (by omega)
    rw [show (1 / 4 : ℝ) * S.card * S.card =
      (S.card : ℝ) * S.card / 4 by ring]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
      have : ((S.card * S.card : ℕ) : ℝ) ≤
          ((4 * DRC.edgeMass Gᶜ S S : ℕ) : ℝ) := by exact_mod_cast hnat
      simpa [Nat.cast_mul, mul_comm] using this)

def reserveFactor (t : ℕ) : ℕ := 2 * 4 ^ t

theorem reserveFactor_pos (t : ℕ) : 0 < reserveFactor t := by
  simp [reserveFactor]

/-- One same-colour DRC step, with a caller-supplied integral reserve `τ`.
The factor `2*4^t` is intentionally wasteful but makes the `D`-th-power size
selection immediate for every positive `D`. -/
theorem exists_color_drc_step
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} (hS : S.Nonempty)
    {θ s D t τ : ℕ} (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t)
    (hτ : 0 < τ)
    (hcard : reserveFactor t * τ ≤ S.card)
    {η : ℝ} (hη : 0 < η)
    (hθ : (θ : ℝ) ≤ η * (1 / 4 : ℝ) ^ D * τ) :
    ∃ c : Bool, ∃ U : Finset α,
      U ⊆ S ∧ τ ≤ U.card ∧
      FiniteDefect.moment (colorGraph G c) θ s
        (fun _ : Fin D => U) S ≤ 2 * η ^ t := by
  classical
  have hScard : 2 ≤ S.card := by
    have hfactor : 2 ≤ reserveFactor t := by
      unfold reserveFactor
      have hp : 1 ≤ 4 ^ t := by simpa using Nat.one_le_pow' t 3
      omega
    have : 2 * τ ≤ reserveFactor t * τ := Nat.mul_le_mul_right τ hfactor
    omega
  obtain ⟨c, hdensity⟩ := exists_color_density_quarter G hScard
  have hθS : (θ : ℝ) ≤ η * (1 / 4 : ℝ) ^ D * S.card := by
    have hτS : τ ≤ S.card := by
      exact (Nat.le_mul_of_pos_left τ (reserveFactor_pos t)).trans hcard
    exact hθ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hτS) (by positivity))
  have hτpow : (τ : ℝ) ^ D ≤
      ((((1 / 4 : ℝ) ^ t) * S.card) ^ D) / 2 := by
    have hbase : (2 : ℝ) * τ ≤ (1 / 4 : ℝ) ^ t * S.card := by
      have hc : reserveFactor t * τ ≤ S.card := hcard
      rw [reserveFactor] at hc
      have hcR : ((2 * 4 ^ t * τ : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hc
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at hcR
      have hinv : (1 / 4 : ℝ) ^ t * (4 : ℝ) ^ t = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) * τ = (1 / 4 : ℝ) ^ t * (2 * 4 ^ t * τ) := by
          calc
            (2 : ℝ) * τ = 2 * 1 * τ := by ring
            _ = 2 * ((1 / 4 : ℝ) ^ t * (4 : ℝ) ^ t) * τ := by rw [hinv]
            _ = (1 / 4 : ℝ) ^ t * (2 * 4 ^ t * τ) := by ring
        _ ≤ (1 / 4 : ℝ) ^ t * S.card :=
          mul_le_mul_of_nonneg_left hcR (by positivity)
    have hnonneg : (0 : ℝ) ≤ 2 * τ := by positivity
    have hpow := pow_le_pow_left₀ hnonneg hbase D
    have htwo : (2 : ℝ) ≤ 2 ^ D := by
      exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hD)
    calc
      (τ : ℝ) ^ D ≤ (2 ^ D * (τ : ℝ) ^ D) / 2 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        simpa [mul_comm] using mul_le_mul_of_nonneg_right htwo
          (pow_nonneg (by positivity : (0 : ℝ) ≤ τ) D)
      _ = ((2 : ℝ) * τ) ^ D / 2 := by rw [mul_pow]
      _ ≤ ((((1 / 4 : ℝ) ^ t) * S.card) ^ D) / 2 := by
        exact div_le_div_of_nonneg_right hpow (by norm_num)
  obtain ⟨x, hx, hUcard, hmom⟩ :=
    DRC.exists_drc (colorGraph G c) hS hS hD ht hst hη
      (by norm_num : (0 : ℝ) < 1 / 4) hdensity hθS hτpow
  let U := FiniteDefect.commonNeighbors (colorGraph G c) x S
  refine ⟨c, U, ?_, hUcard, hmom⟩
  exact Defect.commonNeighbors_subset_target _ _ _

/-! ## Iterating the step and retaining both colour chains -/

def chainRel (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D : ℕ) (μ : ℝ) (U T : Finset α) : Prop :=
  U ⊆ T ∧
    FiniteDefect.moment (colorGraph G c) θ s
      (fun _ : Fin D => U) T ≤ μ

structure DrcChain (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D τ : ℕ) (μ : ℝ) (current : Finset α) where
  sets : List (Finset α)
  nonempty : sets ≠ []
  current_subset : current ⊆ sets.head nonempty
  linked : sets.IsChain (chainRel G c θ s D μ)
  reserve : ∀ U ∈ sets, τ ≤ U.card

def DrcChain.singleton
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D τ : ℕ) (μ : ℝ) (S : Finset α)
    (hS : τ ≤ S.card) : DrcChain G c θ s D τ μ S where
  sets := [S]
  nonempty := by simp
  current_subset := subset_rfl
  linked := List.isChain_singleton S
  reserve := by
    intro U hU
    simp only [List.mem_singleton] at hU
    subst U
    exact hS

def DrcChain.restrictCurrent
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D τ : ℕ) (μ : ℝ)
    {S U : Finset α} (C : DrcChain G c θ s D τ μ S)
    (hUS : U ⊆ S) : DrcChain G c θ s D τ μ U where
  sets := C.sets
  nonempty := C.nonempty
  current_subset := hUS.trans C.current_subset
  linked := C.linked
  reserve := C.reserve

def DrcChain.extend
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D τ : ℕ) (μ : ℝ)
    {S U : Finset α} (C : DrcChain G c θ s D τ μ S)
    (hU : τ ≤ U.card) (hUS : U ⊆ S)
    (hmom : FiniteDefect.moment (colorGraph G c) θ s
      (fun _ : Fin D => U) S ≤ μ) :
    DrcChain G c θ s D τ μ U where
  sets := U :: C.sets
  nonempty := by simp
  current_subset := by simp
  linked := by
    apply C.linked.cons_of_ne_nil C.nonempty
    refine ⟨hUS.trans C.current_subset, ?_⟩
    rw [← FiniteDefect.familyMoment_fin] at hmom ⊢
    exact (HostTools.familyMoment_mono_target (colorGraph G c) θ s
      (fun _ : Fin D => U) C.current_subset).trans hmom
  reserve := by
    intro V hV
    simp only [List.mem_cons] at hV
    rcases hV with rfl | hV
    · exact hU
    · exact C.reserve V hV

theorem DrcChain.length_pos
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (c : Bool) (θ s D τ : ℕ) (μ : ℝ) (S : Finset α)
    (C : DrcChain G c θ s D τ μ S) : 0 < C.sets.length := by
  have : C.sets.length ≠ 0 := by
    simpa [List.length_eq_zero_iff] using C.nonempty
  omega

theorem iterate_from
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {S : Finset α} {m θ s D t τ : ℕ}
    (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t) (hτ : 0 < τ)
    {η : ℝ} (hη : 0 < η)
    (hθ : (θ : ℝ) ≤ η * (1 / 4 : ℝ) ^ D * τ)
    (hcard : reserveFactor t ^ m * τ ≤ S.card)
    (R : DrcChain G false θ s D τ (2 * η ^ t) S)
    (B : DrcChain G true θ s D τ (2 * η ^ t) S) :
    ∃ U : Finset α,
      ∃ R' : DrcChain G false θ s D τ (2 * η ^ t) U,
      ∃ B' : DrcChain G true θ s D τ (2 * η ^ t) U,
        R'.sets.length + B'.sets.length =
          R.sets.length + B.sets.length + m := by
  induction m generalizing S R B with
  | zero =>
      exact ⟨S, R, B, by simp⟩
  | succ m ih =>
      have hreservePos : 0 < reserveFactor t ^ m * τ :=
        Nat.mul_pos (pow_pos (reserveFactor_pos t) m) hτ
      have hstepCard : reserveFactor t * (reserveFactor t ^ m * τ) ≤ S.card := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcard
      have hθstep : (θ : ℝ) ≤
          η * (1 / 4 : ℝ) ^ D * ((reserveFactor t ^ m * τ : ℕ) : ℝ) := by
        have hbase : τ ≤ reserveFactor t ^ m * τ := by
          have hp : 1 ≤ reserveFactor t ^ m := by
            exact one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_of_gt (reserveFactor_pos t)))
          simpa using Nat.mul_le_mul_right τ hp
        exact hθ.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hbase)
          (by positivity))
      have hS : S.Nonempty := by
        apply Finset.card_pos.mp
        have : 0 < reserveFactor t * (reserveFactor t ^ m * τ) :=
          Nat.mul_pos (reserveFactor_pos t) hreservePos
        omega
      obtain ⟨c, U, hUS, hUcard, hmom⟩ := exists_color_drc_step G hS hD ht hst
        hreservePos hstepCard hη hθstep
      have hUbase : τ ≤ U.card := by
        exact (Nat.le_mul_of_pos_left τ
          (pow_pos (reserveFactor_pos t) m)).trans hUcard
      cases c with
      | false =>
          let R₁ := R.extend G false θ s D τ (2 * η ^ t) hUbase hUS hmom
          let B₁ := B.restrictCurrent G true θ s D τ (2 * η ^ t) hUS
          obtain ⟨V, R₂, B₂, hlen⟩ := ih hUcard R₁ B₁
          refine ⟨V, R₂, B₂, ?_⟩
          dsimp [R₁, B₁, DrcChain.extend, DrcChain.restrictCurrent] at hlen
          omega
      | true =>
          let R₁ := R.restrictCurrent G false θ s D τ (2 * η ^ t) hUS
          let B₁ := B.extend G true θ s D τ (2 * η ^ t) hUbase hUS hmom
          obtain ⟨V, R₂, B₂, hlen⟩ := ih hUcard R₁ B₁
          refine ⟨V, R₂, B₂, ?_⟩
          dsimp [R₁, B₁, DrcChain.extend, DrcChain.restrictCurrent] at hlen
          omega

theorem isChain_get_succ {X : Type*} {r : X → X → Prop}
    {L : List X} (hL : L.IsChain r) (i : ℕ) (hi : i + 1 < L.length) :
    r L[i] L[i + 1] := by
  rw [List.isChain_iff_getElem] at hL
  exact hL i hi

/-- Qualitative nested same-colour family.  The input reserve is explicit;
all selected sets retain at least `τ` vertices. -/
theorem exists_nested_same_color
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {r θ s D t τ : ℕ} (hr : 1 ≤ r)
    (hD : 0 < D) (ht : 0 < t) (hst : s ≤ t) (hτ : 0 < τ)
    {η : ℝ} (hη : 0 < η)
    (hθ : (θ : ℝ) ≤ η * (1 / 4 : ℝ) ^ D * τ)
    (hcard : reserveFactor t ^ (2 * (r - 1)) * τ ≤ Fintype.card α) :
    ∃ c : Bool, ∃ A : Fin r → Finset α,
      (∀ i, τ ≤ (A i).card) ∧
      (∀ i : ℕ, ∀ hi : i + 1 < r,
        A ⟨i, (Nat.lt_succ_self i).trans hi⟩ ⊆ A ⟨i + 1, hi⟩) ∧
      (∀ i : ℕ, ∀ hi : i + 1 < r,
        FiniteDefect.moment (colorGraph G c) θ s
          (fun _ : Fin D => A ⟨i, (Nat.lt_succ_self i).trans hi⟩)
          (A ⟨i + 1, hi⟩) ≤ 2 * η ^ t) := by
  classical
  let S : Finset α := Finset.univ
  have hS : τ ≤ S.card := by
    have hp : 1 ≤ reserveFactor t ^ (2 * (r - 1)) := by
      exact one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (reserveFactor_pos t)))
    change τ ≤ Fintype.card α
    nlinarith
  let R := DrcChain.singleton G false θ s D τ (2 * η ^ t) S hS
  let B := DrcChain.singleton G true θ s D τ (2 * η ^ t) S hS
  obtain ⟨U, R', B', hlen⟩ := iterate_from G hD ht hst hτ hη hθ hcard R B
  have hsum : R'.sets.length + B'.sets.length = 2 * r := by
    change R'.sets.length + B'.sets.length = 2 + 2 * (r - 1) at hlen
    omega
  have hlong : r ≤ R'.sets.length ∨ r ≤ B'.sets.length := by omega
  rcases hlong with hR | hB
  · let A : Fin r → Finset α := fun i =>
      R'.sets.get ⟨i.1, i.2.trans_le hR⟩
    refine ⟨false, A, ?_, ?_, ?_⟩
    · intro i
      exact R'.reserve _ (List.get_mem (l := R'.sets) ⟨i.1, i.2.trans_le hR⟩)
    · intro i hi
      exact (isChain_get_succ R'.linked i (by omega)).1
    · intro i hi
      exact (isChain_get_succ R'.linked i (by omega)).2
  · let A : Fin r → Finset α := fun i =>
      B'.sets.get ⟨i.1, i.2.trans_le hB⟩
    refine ⟨true, A, ?_, ?_, ?_⟩
    · intro i
      exact B'.reserve _ (List.get_mem (l := B'.sets) ⟨i.1, i.2.trans_le hB⟩)
    · intro i hi
      exact (isChain_get_succ B'.linked i (by omega)).1
    · intro i hi
      exact (isChain_get_succ B'.linked i (by omega)).2

end HostNested
end Erdos163
