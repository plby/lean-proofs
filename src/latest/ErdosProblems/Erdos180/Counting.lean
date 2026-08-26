/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Subgraphs

set_option linter.mathlibStandardSet false

namespace Erdos180

section Quadratic

section CommutativeRing

variable {K : Type*} [CommRing K]

def symmetricQuadratic (a b c x y : K) : K :=
  a * x ^ 2 + (2 : K) * b * x * y + c * y ^ 2

def symmetricDet (a b c : K) : K := a * c - b ^ 2

lemma symmetricQuadratic_eq_bilinear
    (a b c x y : K) :
    symmetricQuadratic a b c x y =
      x * (a * x + b * y) + y * (b * x + c * y) := by
  unfold symmetricQuadratic
  ring

lemma symmetricDet_zero_diagonal_sub (b b' : K) :
    symmetricDet (0 : K) (b - b') 0 = -((b - b') ^ 2) := by
  simp [symmetricDet]

end CommutativeRing

section CharacteristicTwo

variable {K : Type*} [Field K] [CharP K 2]

lemma symmetricQuadratic_char_two
    (a b c x y : K) :
    symmetricQuadratic a b c x y = a * x ^ 2 + c * y ^ 2 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [symmetricQuadratic, htwo]

lemma symmetricQuadratic_char_two_eq_square
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by
  rw [symmetricQuadratic_char_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 =
        (r * x) ^ 2 + (s * y) ^ 2 := by ring
    _ = (r * x + s * y) ^ 2 := by
      rw [add_sq]
      simp [htwo]

lemma square_surjective_char_two [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨r, hr⟩ := (isSquare_of_charTwo' a).exists_sq
  exact ⟨r, hr.symm⟩

lemma symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    [Finite K] {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : symmetricQuadratic a b c x y = 0)
    (hsecond : symmetricQuadratic a b c x' y' = 0) :
    a = 0 ∧ c = 0 := by
  obtain ⟨r, hr⟩ := square_surjective_char_two a
  obtain ⟨s, hs⟩ := square_surjective_char_two c
  change r ^ 2 = a at hr
  change s ^ 2 = c at hs
  have hlinfirst : r * x + s * y = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hfirst
  have hlinsecond : r * x' + s * y' = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hsecond
  have hrdet : (x * y' - x' * y) * r = 0 := by
    linear_combination y' * hlinfirst - y * hlinsecond
  have hsdet : (x * y' - x' * y) * s = 0 := by
    linear_combination x * hlinsecond - x' * hlinfirst
  have hrzero : r = 0 := (mul_eq_zero.mp hrdet).resolve_left hind
  have hszero : s = 0 := (mul_eq_zero.mp hsdet).resolve_left hind
  constructor
  · simpa [hrzero] using hr.symm
  · simpa [hszero] using hs.symm

end CharacteristicTwo

section Field

variable {K : Type*} [Field K]

def symmetricQuadraticEvaluationMatrix
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀ ^ 2, (2 : K) * x₀ * y₀, y₀ ^ 2;
     x₁ ^ 2, (2 : K) * x₁ * y₁, y₁ ^ 2;
     x₂ ^ 2, (2 : K) * x₂ * y₂, y₂ ^ 2]

lemma symmetricQuadraticEvaluationMatrix_det
    (x₀ y₀ x₁ y₁ x₂ y₂ : K) :
    (symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂).det =
      (2 : K) * (x₀ * y₁ - x₁ * y₀) *
        (x₀ * y₂ - x₂ * y₀) * (x₁ * y₂ - x₂ * y₁) := by
  rw [Matrix.det_fin_three]
  simp [symmetricQuadraticEvaluationMatrix]
  ring

lemma symmetricQuadratic_no_three_independent_roots
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hcoeff : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  let A := symmetricQuadraticEvaluationMatrix x₀ y₀ x₁ y₁ x₂ y₂
  have hdet : A.det ≠ 0 := by
    rw [symmetricQuadraticEvaluationMatrix_det]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo h01) h02) h12
  have hmul : A.mulVec ![a, b, c] = 0 := by
    funext i
    fin_cases i
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₀
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₁
    · simpa [A, symmetricQuadraticEvaluationMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ, symmetricQuadratic,
        mul_assoc, mul_comm, mul_left_comm, add_assoc] using hroot₂
  have hzero : ![a, b, c] = (0 : Fin 3 → K) :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have ha : a = 0 := congrFun hzero 0
  have hb : b = 0 := congrFun hzero 1
  have hc : c = 0 := congrFun hzero 2
  exact hcoeff.elim (fun h => h ha)
    (fun h => h.elim (fun h' => h' hb) (fun h' => h' hc))

lemma symmetricQuadratic_no_three_roots_of_det_ne_zero
    (htwo : (2 : K) ≠ 0)
    {a b c x₀ y₀ x₁ y₁ x₂ y₂ : K}
    (hdet : symmetricDet a b c ≠ 0)
    (h01 : x₀ * y₁ - x₁ * y₀ ≠ 0)
    (h02 : x₀ * y₂ - x₂ * y₀ ≠ 0)
    (h12 : x₁ * y₂ - x₂ * y₁ ≠ 0)
    (hroot₀ : symmetricQuadratic a b c x₀ y₀ = 0)
    (hroot₁ : symmetricQuadratic a b c x₁ y₁ = 0)
    (hroot₂ : symmetricQuadratic a b c x₂ y₂ = 0) : False := by
  apply symmetricQuadratic_no_three_independent_roots
    htwo (a := a) (b := b) (c := c) (x₀ := x₀) (y₀ := y₀)
    (x₁ := x₁) (y₁ := y₁) (x₂ := x₂) (y₂ := y₂)
    (h01 := h01) (h02 := h02) (h12 := h12)
    (hroot₀ := hroot₀) (hroot₁ := hroot₁) (hroot₂ := hroot₂)
  by_contra h
  push Not at h
  obtain ⟨ha, hb, hc⟩ := h
  apply hdet
  simp [symmetricDet, ha, hb, hc]

lemma symmetricDet_zero_diagonal_sub_ne_zero
    {b b' : K} (h : b ≠ b') :
    symmetricDet (0 : K) (b - b') 0 ≠ 0 := by
  rw [symmetricDet_zero_diagonal_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr h))

end Field

end Quadratic

section Separation

open Filter Finset SimpleGraph
open scoped Topology

noncomputable def extremalScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((4 : ℝ) / 3)

lemma extremalScale_pos {n : ℕ} (hn : 0 < n) :
    0 < extremalScale n := by
  unfold extremalScale
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma extremalScale_nonneg (n : ℕ) :
    0 ≤ extremalScale n := by
  unfold extremalScale
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

def FamilyLittleO (family : Finset FiniteGraph) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (familyExtremal family n : ℝ) ≤ ε * extremalScale n

def UniformMemberLower (family : Finset FiniteGraph) (c : ℝ) : Prop :=
  ∀ forbidden ∈ family,
    ∀ᶠ n : ℕ in atTop,
      c * extremalScale n ≤
        (SimpleGraph.extremalNumber n forbidden.graph : ℝ)

structure SeparationCertificate (family : Finset FiniteGraph) where

  lowerConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  family_littleO : FamilyLittleO family
  member_lower : UniformMemberLower family lowerConstant

noncomputable def manuscriptLowerConstant : ℝ :=
  (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
    (27 : ℝ) ^ (-((4 : ℝ) / 3))

theorem manuscriptLowerConstant_pos : 0 < manuscriptLowerConstant := by
  unfold manuscriptLowerConstant
  positivity

lemma not_compact_of_separation
    {family : Finset FiniteGraph}
    (certificate : SeparationCertificate family) :
    ¬ IsCompactFamily family := by
  rintro ⟨forbidden, hmem, C, hC, hcomparison⟩
  have hepsilon : 0 < certificate.lowerConstant / (2 * C) := by
    exact div_pos certificate.lowerConstant_pos
      (mul_pos (by norm_num) hC)
  have hupper := certificate.family_littleO
    (certificate.lowerConstant / (2 * C)) hepsilon
  have hlower := certificate.member_lower forbidden hmem
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_gt_atTop 0
  have himpossible : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hupper, hlower, hcomparison, hpositive]
      with n hnupper hnlower hncomparison hnpositive
    have hs := extremalScale_pos hnpositive
    have hscaled :
        C * (familyExtremal family n : ℝ) ≤
          C * ((certificate.lowerConstant / (2 * C)) *
            extremalScale n) :=
      mul_le_mul_of_nonneg_left hnupper hC.le
    have hidentity :
        C * ((certificate.lowerConstant / (2 * C)) *
          extremalScale n) =
            (certificate.lowerConstant / 2) * extremalScale n := by
      field_simp
    rw [hidentity] at hscaled
    nlinarith [mul_pos certificate.lowerConstant_pos hs]
  exact himpossible.exists.elim (fun _ h => h)

theorem proposedFamily_not_compact_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ IsCompactFamily proposedFamily := by
  apply not_compact_of_separation
  exact
    { lowerConstant := manuscriptLowerConstant
      lowerConstant_pos := manuscriptLowerConstant_pos
      family_littleO := hupper
      member_lower := hlower }

lemma not_compactnessConjecture_of_bounds
    (hupper : FamilyLittleO proposedFamily)
    (hlower : UniformMemberLower proposedFamily manuscriptLowerConstant) :
    ¬ CompactnessConjectureStatement := by
  intro hconjecture
  exact proposedFamily_not_compact_of_bounds hupper hlower
    (hconjecture proposedFamily proposedFamily_nonempty
      proposedFamily_isCyclic)

end Separation

section Supersaturation

open Finset SimpleGraph

section FiniteHeavyFibers

noncomputable def fourPathHeavyThreshold (N p : ℕ) : ℝ :=
  (p : ℝ) / (2 * (N : ℝ))

noncomputable def finiteHeavyFiberMass {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ) : ℝ :=
  ∑ x : α,
    if fourPathHeavyThreshold N p ≤ (weight x : ℝ)
    then (weight x : ℝ) else 0

theorem finite_heavy_fiber_mass_half
    {α : Type*} [Fintype α]
    (weight : α → ℕ) (N p : ℕ)
    (hN : 0 < N)
    (hcapacity : Fintype.card α ≤ N)
    (htotal : p ≤ ∑ x : α, weight x) :
    (p : ℝ) / 2 ≤ finiteHeavyFiberMass weight N p := by
  classical
  let R : ℝ := fourPathHeavyThreshold N p
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hsum :
      (∑ x : α, (weight x : ℝ)) ≤
        (∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) +
          (Fintype.card α : ℝ) * R := by
    calc
      (∑ x : α, (weight x : ℝ)) ≤
          ∑ x : α,
            ((if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0) + R) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · linarith
        · have : (weight x : ℝ) < R := lt_of_not_ge hx
          linarith
      _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hcapacityReal : (Fintype.card α : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcapacity
  have hthreshold : (N : ℝ) * R = (p : ℝ) / 2 := by
    dsimp [R, fourPathHeavyThreshold]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  have htotalReal :
      (p : ℝ) ≤ ∑ x : α, (weight x : ℝ) := by
    exact_mod_cast htotal
  change (p : ℝ) / 2 ≤
    ∑ x : α, if R ≤ (weight x : ℝ) then (weight x : ℝ) else 0
  nlinarith [mul_le_mul_of_nonneg_right hcapacityReal hR]

end FiniteHeavyFibers

section ActualFourPathFibers

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma unrelated_four_path_endpoint_card_le
    (G : SimpleGraph V) (u : V) :
    Fintype.card (UnrelatedFourPathEndpoint G u) ≤ Fintype.card V := by
  exact Fintype.card_le_of_injective
    (fun v : UnrelatedFourPathEndpoint G u => (v : V))
    Subtype.val_injective

omit [Fintype V] [DecidableEq V] in
lemma common_second_neighbor_pairwise_unrelated
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u v : V}
    (huv : u ≠ v)
    (hunrelated : ¬ CommonNeighborRelated G u v)
    (x y : CommonSecondNeighbor G u v) :
    ¬ CommonNeighborRelated G (x : V) (y : V) := by
  exact common_second_neighbors_pairwise_unrelated
    hbip hfour hsix huv hunrelated
    (commonNeighborRelated_symm x.property.1)
    (commonNeighborRelated_symm x.property.2)
    (commonNeighborRelated_symm y.property.1)
    (commonNeighborRelated_symm y.property.2)

lemma four_path_heavy_common_second_neighbor_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 2 ≤
      finiteHeavyFiberMass
        (fun v : UnrelatedFourPathEndpoint G u =>
          Fintype.card (CommonSecondNeighbor G u (v : V)))
        (Fintype.card V) (d * (d - 1) ^ 3) := by
  apply finite_heavy_fiber_mass_half
  · exact Fintype.card_pos_iff.mpr ⟨u⟩
  · exact unrelated_four_path_endpoint_card_le G u
  · exact four_path_common_second_neighbor_sum_lower
      G hbip hfour hsix d hdegree u

end ActualFourPathFibers

section ActualThetaExtensions

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def thetaBaseExtensions
    (G : SimpleGraph V) (y z : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    ∃ witness : SimpleGraph.Copy thetaGraph G,
      witness (.inl (.inl (0 : Fin 3))) = x ∧
      witness (.inl (.inl (1 : Fin 3))) = y ∧
      witness (.inl (.inl (2 : Fin 3))) = z

lemma mem_thetaBaseExtensions
    (G : SimpleGraph V) (x y z : V) :
    x ∈ thetaBaseExtensions G y z ↔
      ∃ witness : SimpleGraph.Copy thetaGraph G,
        witness (.inl (.inl (0 : Fin 3))) = x ∧
        witness (.inl (.inl (1 : Fin 3))) = y ∧
        witness (.inl (.inl (2 : Fin 3))) = z := by
  classical
  simp [thetaBaseExtensions]

def gluedJBase {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G) : Fin 4 → V :=
  ![copies 0 (.inl (.inl (0 : Fin 3))),
    copies 1 (.inl (.inl (0 : Fin 3))),
    copies 0 (.inl (.inl (1 : Fin 3))),
    copies 0 (.inl (.inl (2 : Fin 3)))]

def gluedJVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V) : JVertex → V
  | .inl (.inl base) => gluedJBase copies base
  | .inl (.inr (copy, center)) =>
      copies copy (.inl (.inr center))
  | .inr (.inl (copy, (base, center))) =>
      copies copy (.inr (base, center))
  | .inr (.inr _) => joining

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_jBase
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (base : Fin 3) :
    gluedJBase copies (jBase copy base) =
      copies copy (.inl (.inl base)) := by
  fin_cases copy <;> fin_cases base <;>
    simp [gluedJBase, jBase, hfirst, hsecond]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_jThetaVertex
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (copy : Fin 2) (vertex : SubdivisionVertex 2) :
    gluedJVertex copies joining (jThetaVertex copy vertex) =
      copies copy vertex := by
  rcases vertex with (base | center) | pair
  · exact gluedJBase_jBase copies hfirst hsecond copy base
  · simp [jThetaVertex, gluedJVertex]
  · simp [jThetaVertex, gluedJVertex]

lemma inJCopy_iff_exists_jThetaVertex
    (copy : Fin 2) (vertex : JVertex) :
    InJCopy copy vertex ↔
      ∃ source : SubdivisionVertex 2,
        jThetaVertex copy source = vertex := by
  constructor
  · intro h
    rcases vertex with (base | center) | (pair | joining)
    · obtain ⟨source, hsource⟩ := h
      refine ⟨.inl (.inl source), ?_⟩
      simpa [jThetaVertex] using congrArg
        (fun value : Fin 4 => (Sum.inl (Sum.inl value) : JVertex))
        hsource.symm
    · rcases center with ⟨index, center⟩
      change copy = index at h
      subst index
      exact ⟨.inl (.inr center), rfl⟩
    · rcases pair with ⟨index, base, center⟩
      change copy = index at h
      subst index
      exact ⟨.inr (base, center), rfl⟩
    · exact False.elim h
  · rintro ⟨source, rfl⟩
    exact jThetaVertex_mem copy source

lemma theta_base_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma theta_center_pair_adj (base : Fin 3) (center : Fin 2) :
    thetaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    {source target : JVertex}
    (hedge : jTemplateRelation source target) :
    G.Adj
      (gluedJVertex copies joining source)
      (gluedJVertex copies joining target) := by
  rcases source with (base | center) | (pair | star)
  · rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy, base', center'⟩
      change base = jBase copy base' at hedge
      subst base
      change G.Adj
        (gluedJBase copies (jBase copy base'))
        (copies copy (.inr (base', center')))
      rw [gluedJBase_jBase copies hfirst hsecond copy base']
      exact (copies copy).toHom.map_rel
        (theta_base_pair_adj base' center')
    · change base = 0 ∨ base = 1 at hedge
      rcases hedge with hbase | hbase
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinFirst
      · subst base
        simpa [gluedJVertex, gluedJBase] using hjoinSecond
  · rcases center with ⟨copy, center⟩
    rcases target with (targetBase | targetCenter) | (targetPair | targetStar)
    · exact False.elim hedge
    · exact False.elim hedge
    · rcases targetPair with ⟨copy', base, center'⟩
      change copy = copy' ∧ center = center' at hedge
      obtain ⟨hcopy, hcenter⟩ := hedge
      subst copy'
      subst center'
      exact (copies copy).toHom.map_rel
        (theta_center_pair_adj base center)
    · exact False.elim hedge
  · exact False.elim hedge
  · exact False.elim hedge

def gluedJHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    jTemplate →g G where
  toFun := gluedJVertex copies joining
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      jTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedJVertex_map_relation copies joining hfirst hsecond
        hjoinFirst hjoinSecond hforward
    · exact (gluedJVertex_map_relation copies joining
        hfirst hsecond hjoinFirst hjoinSecond hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by
  intro left hleft right hright heq
  change InJCopy copy left at hleft
  change InJCopy copy right at hright
  obtain ⟨source, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy left).mp hleft
  obtain ⟨target, rfl⟩ :=
    (inJCopy_iff_exists_jThetaVertex copy right).mp hright
  change
    gluedJVertex copies joining (jThetaVertex copy source) =
      gluedJVertex copies joining (jThetaVertex copy target) at heq
  rw [gluedJVertex_jThetaVertex copies joining hfirst hsecond copy,
    gluedJVertex_jThetaVertex copies joining hfirst hsecond copy] at heq
  have hequal := (copies copy).injective heq
  subst target
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_injective
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by
  have hcopy (index : Fin 2) {i j : Fin 3}
      (hij : i ≠ j) :
      copies index (.inl (.inl i)) ≠
        copies index (.inl (.inl j)) := by
    intro h
    apply hij
    simpa using (copies index).injective h
  have h02 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) :=
    hcopy 0 (by decide)
  have h03 :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h23 :
      copies 0 (.inl (.inl (1 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) :=
    hcopy 0 (by decide)
  have h12 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 1))
      (h.trans hfirst.symm)
  have h13 :
      copies 1 (.inl (.inl (0 : Fin 3))) ≠
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    intro h
    exact (hcopy 1 (by decide : (0 : Fin 3) ≠ 2))
      (h.trans hsecond.symm)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [gluedJBase]

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_center_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (base : Fin 3) (center : Fin 2) :
    color (copy (.inl (.inl base))) =
      color (copy (.inl (.inr center))) := by
  exact bipartite_coloring_eq_of_common_neighbor color
    (copy.toHom.map_rel (theta_base_pair_adj base center))
    (copy.toHom.map_rel (theta_center_pair_adj base center))

omit [Fintype V] [DecidableEq V] in
lemma thetaCopy_base_color_eq
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (copy : SimpleGraph.Copy thetaGraph G)
    (first second : Fin 3) :
    color (copy (.inl (.inl first))) =
      color (copy (.inl (.inl second))) := by
  calc
    color (copy (.inl (.inl first))) =
        color (copy (.inl (.inr (0 : Fin 2)))) :=
      thetaCopy_base_center_color_eq color copy first 0
    _ = color (copy (.inl (.inl second))) :=
      (thetaCopy_base_center_color_eq color copy second 0).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedThetaBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (copy : Fin 2) (base : Fin 3) :
    color (copies copy (.inl (.inl base))) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases copy
  · exact thetaCopy_base_color_eq color (copies 0) base 0
  · calc
      color (copies 1 (.inl (.inl base))) =
          color (copies 1 (.inl (.inl (1 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 1) base 1
      _ = color (copies 0 (.inl (.inl (1 : Fin 3)))) :=
        congrArg color hfirst
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        thetaCopy_base_color_eq color (copies 0) 1 0

omit [Fintype V] [DecidableEq V] in
lemma gluedJBase_color_eq
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (color : G.Coloring (Fin 2))
    (base : Fin 4) :
    color (gluedJBase copies base) =
      color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  fin_cases base
  · rfl
  · exact gluedThetaBase_color_eq copies hfirst color 1 0
  · exact gluedThetaBase_color_eq copies hfirst color 0 1
  · exact gluedThetaBase_color_eq copies hfirst color 0 2

omit [Fintype V] [DecidableEq V] in
lemma gluedJVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (color : G.Coloring (Fin 2))
    (vertex : JVertex) :
    jColor vertex = false ↔
      color (gluedJVertex copies joining vertex) =
        color (copies 0 (.inl (.inl (0 : Fin 3)))) := by
  rcases vertex with (base | center) | (pair | star)
  · simpa [jColor, gluedJVertex] using
      gluedJBase_color_eq copies hfirst color base
  · rcases center with ⟨copy, center⟩
    simp only [jColor, gluedJVertex, true_iff]
    calc
      color (copies copy (.inl (.inr center))) =
          color (copies copy (.inl (.inl (0 : Fin 3)))) :=
        (thetaCopy_base_center_color_eq
          color (copies copy) 0 center).symm
      _ = color (copies 0 (.inl (.inl (0 : Fin 3)))) :=
        gluedThetaBase_color_eq copies hfirst color copy 0
  · rcases pair with ⟨copy, base, center⟩
    simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    have hedge := (copies copy).toHom.map_rel
      (theta_base_pair_adj base center)
    have hvalid := color.valid hedge
    apply hvalid
    exact (gluedThetaBase_color_eq
      copies hfirst color copy base).trans heq.symm
  · simp only [jColor, Bool.true_eq_false, false_iff, gluedJVertex]
    intro heq
    exact (color.valid hjoinFirst) heq.symm

omit [Fintype V] [DecidableEq V] in
lemma gluedJHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining) :
    ∀ left right,
      gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond left =
          gluedJHom copies joining hfirst hsecond
            hjoinFirst hjoinSecond right →
        jColor left = jColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hcolor :
      color (gluedJVertex copies joining left) =
        color (gluedJVertex copies joining right) :=
    congrArg color heq
  cases hleft : jColor left <;> cases hright : jColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mp hleft
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mpr
        (hcolor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color right).mp hright
    have hfalse :=
      (gluedJVertex_color_false_iff copies joining
        hfirst hjoinFirst color left).mpr
        (hcolor.trans hbase)
    simp [hleft] at hfalse
  · rfl

lemma thetaBaseExtensions_commonNeighborIndependent
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (y z : Fin n) :
    CommonNeighborIndependent host (thetaBaseExtensions host y z) := by
  intro x x' hx hx' hdistinct
  rintro ⟨_, joining, hxjoin, hx'join⟩
  obtain ⟨first, hfirstX, hfirstY, hfirstZ⟩ :=
    (mem_thetaBaseExtensions host x y z).mp hx
  obtain ⟨second, hsecondX, hsecondY, hsecondZ⟩ :=
    (mem_thetaBaseExtensions host x' y z).mp hx'
  let copies : Fin 2 → SimpleGraph.Copy thetaGraph host :=
    ![first, second]
  have hsharedFirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))) := by
    change second (.inl (.inl (1 : Fin 3))) =
      first (.inl (.inl (1 : Fin 3)))
    exact hsecondY.trans hfirstY.symm
  have hsharedSecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))) := by
    change second (.inl (.inl (2 : Fin 3))) =
      first (.inl (.inl (2 : Fin 3)))
    exact hsecondZ.trans hfirstZ.symm
  have hjoinFirst :
      host.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (first (.inl (.inl (0 : Fin 3)))) joining
    rw [hfirstX]
    exact hxjoin
  have hjoinSecond :
      host.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining := by
    change host.Adj (second (.inl (.inl (0 : Fin 3)))) joining
    rw [hsecondX]
    exact hx'join
  have hbaseDistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3))) := by
    change first (.inl (.inl (0 : Fin 3))) ≠
      second (.inl (.inl (0 : Fin 3)))
    rw [hfirstX, hsecondX]
    exact hdistinct
  apply proposedFamilyFree_no_jTemplate hfree
    (gluedJHom copies joining hsharedFirst hsharedSecond
      hjoinFirst hjoinSecond)
  · exact gluedJHom_color_respecting hbip copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond
  · change Function.Injective (gluedJBase copies)
    exact gluedJBase_injective copies hsharedFirst
      hsharedSecond hbaseDistinct
  · intro copy
    exact gluedJHom_injOn_marked_copy copies joining
      hsharedFirst hsharedSecond hjoinFirst hjoinSecond copy

lemma thetaBaseExtensions_card_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (y z : Fin n) :
    (thetaBaseExtensions host y z).card * d ≤ n := by
  simpa using
    (commonNeighborIndependent_card_mul_degree_le
      host (thetaBaseExtensions host y z)
      (thetaBaseExtensions_commonNeighborIndependent
        host hfree hbip y z)
      d hdegree)

end ActualThetaExtensions

section ActualCommonCenterTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ i : Fin 3, CommonNeighborRelated G (base i) center

omit [DecidableEq V] in
lemma mem_tripleCommonCenters
    (G : SimpleGraph V) (base : Fin 3 → V) (center : V) :
    center ∈ tripleCommonCenters G base ↔
      ∀ i : Fin 3, CommonNeighborRelated G (base i) center := by
  classical
  simp [tripleCommonCenters]

lemma mem_thetaBaseExtensions_of_girthEightCenters
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V) (center : Fin 2 → V)
    (hbase : Function.Injective base)
    (hcenter : Function.Injective center)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j)) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  refine (mem_thetaBaseExtensions G _ _ _).mpr ?_
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_, ?_, ?_⟩
  all_goals rfl

lemma mem_thetaBaseExtensions_of_two_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    (hcenters : 2 ≤ (tripleCommonCenters G base).card) :
    base 0 ∈ thetaBaseExtensions G (base 1) (base 2) := by
  classical
  have hcard : 1 < (tripleCommonCenters G base).card := by omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp hcard
  let center : Fin 2 → V := ![first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base first).mp hfirst i
    · exact (mem_tripleCommonCenters G base second).mp hsecond i
  exact mem_thetaBaseExtensions_of_girthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated

end ActualCommonCenterTriples

section CubicBinomialSupersaturation

lemma choose_three_factorial_identity (t : ℕ) :
    6 * t.choose 3 = t * (t - 1) * (t - 2) := by
  simpa [Nat.descFactorial, Nat.factorial, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose t 3).symm

lemma choose_three_cubic_lower {t : ℕ} (ht : 3 ≤ t) :
    (t : ℝ) ^ 3 / 27 ≤ (t.choose 3 : ℝ) := by
  have hone : 1 ≤ t := by omega
  have htwo : 2 ≤ t := by omega
  have hidentity := congrArg (fun value : ℕ => (value : ℝ))
    (choose_three_factorial_identity t)
  norm_num [Nat.cast_sub hone, Nat.cast_sub htwo] at hidentity
  have htReal : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hfactor :
      0 ≤ (t : ℝ) * ((t : ℝ) - 3) *
        (7 * (t : ℝ) - 6) := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (by linarith)
  nlinarith

end CubicBinomialSupersaturation

section ActualTripleSupersaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborTripleMass
    (G : SimpleGraph V) (u : V) : ℕ :=
  ∑ v : UnrelatedFourPathEndpoint G u,
    (Fintype.card (CommonSecondNeighbor G u (v : V))).choose 3

lemma four_path_common_second_neighbor_triple_mass_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold (Fintype.card V) (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass G u : ℝ) := by
  classical
  let p : ℕ := d * (d - 1) ^ 3
  let R : ℝ := fourPathHeavyThreshold (Fintype.card V) p
  let weight : UnrelatedFourPathEndpoint G u → ℕ :=
    fun v => Fintype.card (CommonSecondNeighbor G u (v : V))
  have hR : 0 ≤ R := by
    dsimp [R, fourPathHeavyThreshold]
    positivity
  have hRthree : (3 : ℝ) ≤ R := by
    simpa [R, p] using hthreshold
  have hheavy :
      (p : ℝ) / 2 ≤
        finiteHeavyFiberMass weight (Fintype.card V) p := by
    simpa [weight, p] using
      (four_path_heavy_common_second_neighbor_mass_lower
        G hbip hfour hsix d hdegree u)
  have hpoint (v : UnrelatedFourPathEndpoint G u) :
      R ^ 2 *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) / 27 ≤
        ((weight v).choose 3 : ℝ) := by
    split_ifs with hv
    · have htReal : (3 : ℝ) ≤ (weight v : ℝ) := hRthree.trans hv
      have ht : 3 ≤ weight v := by exact_mod_cast htReal
      have hsquare : R ^ 2 ≤ (weight v : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hR
          (sub_nonneg.mpr hv),
          mul_nonneg (Nat.cast_nonneg (weight v))
            (sub_nonneg.mpr hv)]
      have hcubic :
          R ^ 2 * (weight v : ℝ) ≤ (weight v : ℝ) ^ 3 := by
        calc
          R ^ 2 * (weight v : ℝ) ≤
              (weight v : ℝ) ^ 2 * (weight v : ℝ) :=
            mul_le_mul_of_nonneg_right hsquare
              (Nat.cast_nonneg (weight v))
          _ = (weight v : ℝ) ^ 3 := by ring
      calc
        R ^ 2 * (weight v : ℝ) / 27 ≤
            (weight v : ℝ) ^ 3 / 27 := by linarith
        _ ≤ ((weight v).choose 3 : ℝ) :=
          choose_three_cubic_lower ht
    · simp
  change R ^ 2 * (p : ℝ) / 54 ≤
    (commonSecondNeighborTripleMass G u : ℝ)
  calc
    R ^ 2 * (p : ℝ) / 54 =
        (R ^ 2 / 27) * ((p : ℝ) / 2) := by ring
    _ ≤ (R ^ 2 / 27) *
        finiteHeavyFiberMass weight (Fintype.card V) p :=
      mul_le_mul_of_nonneg_left hheavy (by positivity)
    _ = ∑ v : UnrelatedFourPathEndpoint G u,
          R ^ 2 *
            (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) /
              27 := by
      simp only [finiteHeavyFiberMass, Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro v hv
        change (R ^ 2 / 27) *
          (if R ≤ (weight v : ℝ) then (weight v : ℝ) else 0) = _
        ring
    _ ≤ ∑ v : UnrelatedFourPathEndpoint G u,
          ((weight v).choose 3 : ℝ) :=
      Finset.sum_le_sum fun v _ => hpoint v
    _ = (commonSecondNeighborTripleMass G u : ℝ) := by
      simp [commonSecondNeighborTripleMass, weight]

theorem proposedFamilyFree_four_path_triple_mass_lower
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (u : Fin n)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass host u : ℝ) := by
  have hthreshold' : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card (Fin n))
        (d * (d - 1) ^ 3) := by
    simpa using hthreshold
  simpa using four_path_common_second_neighbor_triple_mass_lower
    host hbip (proposedFamilyFree_four_cycle hfree)
    (proposedFamilyFree_six_cycle hfree) d hdegree u hthreshold'

end ActualTripleSupersaturation

section OrderedThetaTripleCounting

noncomputable def orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n)) : ℕ :=
  ∑ y : Fin n, ∑ z : Fin n, (thetaBaseExtensions host y z).card

lemma orderedThetaTripleCount_mul_degree_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    orderedThetaTripleCount host * d ≤ n ^ 3 := by
  classical
  calc
    orderedThetaTripleCount host * d =
        ∑ y : Fin n, ∑ z : Fin n,
          (thetaBaseExtensions host y z).card * d := by
      simp [orderedThetaTripleCount, Finset.sum_mul]
    _ ≤ ∑ _y : Fin n, ∑ _z : Fin n, n := by
      gcongr with y _ z _
      exact thetaBaseExtensions_card_mul_degree_le
        host hfree hbip d hdegree y z
    _ = n ^ 3 := by simp [pow_succ, Nat.mul_assoc]

end OrderedThetaTripleCounting

section ActualGammaAndKForcing

variable {V : Type*} [Fintype V] [DecidableEq V]

def GammaGood (G : SimpleGraph V) (u : V) : Prop :=
  ∃ witness : SimpleGraph.Copy gammaGraph G,
    witness kSpecifiedCenter = u

lemma gammaGood_of_three_common_centers
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (base : Fin 3 → V)
    (hbase : Function.Injective base)
    (hbase_unrelated : ∀ ⦃i j : Fin 3⦄, i ≠ j →
      ¬ CommonNeighborRelated G (base i) (base j))
    {u : V}
    (hu : u ∈ tripleCommonCenters G base)
    (hcenters : 3 ≤ (tripleCommonCenters G base).card) :
    GammaGood G u := by
  classical
  have herase :
      1 < ((tripleCommonCenters G base).erase u).card := by
    rw [Finset.card_erase_of_mem hu]
    omega
  obtain ⟨first, hfirst, second, hsecond, hdistinct⟩ :=
    Finset.one_lt_card.mp herase
  have hfirstne : first ≠ u := (Finset.mem_erase.mp hfirst).1
  have hsecondne : second ≠ u := (Finset.mem_erase.mp hsecond).1
  have hfirstmem : first ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hfirst).2
  have hsecondmem : second ∈ tripleCommonCenters G base :=
    (Finset.mem_erase.mp hsecond).2
  let center : Fin 3 → V := ![u, first, second]
  have hcenter : Function.Injective center := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [center]
  have hrelated : ∀ i j,
      CommonNeighborRelated G (base i) (center j) := by
    intro i j
    fin_cases j
    · exact (mem_tripleCommonCenters G base u).mp hu i
    · exact (mem_tripleCommonCenters G base first).mp hfirstmem i
    · exact (mem_tripleCommonCenters G base second).mp hsecondmem i
  let witness := subdivisionCopyOfGirthEightCenters
    hbip hfour hsix base center hbase hcenter hbase_unrelated hrelated
  refine ⟨witness, ?_⟩
  rfl

lemma gamma_base_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma gamma_center_pair_adj (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gammaCopy_vertex_color_false_iff
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (witness : SimpleGraph.Copy gammaGraph G)
    (vertex : SubdivisionVertex 3) :
    subdivisionColor 3 vertex = false ↔
      color (witness vertex) = color (witness kSpecifiedCenter) := by
  rcases vertex with (base | center) | pair
  · simp only [subdivisionColor, true_iff]
    exact bipartite_coloring_eq_of_common_neighbor color
      (witness.toHom.map_rel (gamma_base_pair_adj base 0))
      (witness.toHom.map_rel (gamma_center_pair_adj base 0))
  · simp only [subdivisionColor, true_iff]
    calc
      color (witness (.inl (.inr center))) =
          color (witness (.inl (.inl (0 : Fin 3)))) :=
        (bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 center))
          (witness.toHom.map_rel
            (gamma_center_pair_adj 0 center))).symm
      _ = color (witness kSpecifiedCenter) :=
        bipartite_coloring_eq_of_common_neighbor color
          (witness.toHom.map_rel (gamma_base_pair_adj 0 0))
          (witness.toHom.map_rel (gamma_center_pair_adj 0 0))
  · rcases pair with ⟨base, center⟩
    simp only [subdivisionColor, Bool.true_eq_false, false_iff]
    intro heq
    have hbase :
        color (witness (.inl (.inl base))) =
          color (witness kSpecifiedCenter) :=
      bipartite_coloring_eq_of_common_neighbor color
        (witness.toHom.map_rel (gamma_base_pair_adj base 0))
        (witness.toHom.map_rel (gamma_center_pair_adj base 0))
    exact (color.valid
      (witness.toHom.map_rel (gamma_base_pair_adj base center)))
        (hbase.trans heq.symm)

def gluedKVertex {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (vertex : KVertex) : V :=
  copies vertex.1 vertex.2

lemma subdivisionRelation_adj
    {k : ℕ} {source target : SubdivisionVertex k}
    (hedge : subdivisionRelation k source target) :
    (SubdivisionGraph k).Adj source target := by
  rcases source with (base | center) | pair <;>
    rcases target with (targetBase | targetCenter) | targetPair <;>
    simp_all [SubdivisionGraph, SimpleGraph.fromRel_adj,
      subdivisionRelation]

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_map_relation
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    {source target : KVertex}
    (hedge : kTemplateRelation source target) :
    G.Adj (gluedKVertex copies source)
      (gluedKVertex copies target) := by
  rcases hedge with hcopy | hjoin
  · obtain ⟨hindex, hsubdivision⟩ := hcopy
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = index' at hindex
    subst index'
    exact (copies index).toHom.map_rel
      (subdivisionRelation_adj hsubdivision)
  · obtain ⟨hsource, htarget, hvertex, hvertex'⟩ := hjoin
    rcases source with ⟨index, vertex⟩
    rcases target with ⟨index', vertex'⟩
    change index = 0 at hsource
    change index' = 1 at htarget
    subst index
    subst index'
    change vertex = kSpecifiedCenter at hvertex
    change vertex' = kSpecifiedCenter at hvertex'
    subst vertex
    subst vertex'
    exact hjoining

def gluedKHom
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    kTemplate →g G where
  toFun := gluedKVertex copies
  map_rel' := by
    intro source target hedge
    rcases (SimpleGraph.fromRel_adj
      kTemplateRelation source target).mp hedge with
      ⟨_, hforward | hbackward⟩
    · exact gluedKVertex_map_relation copies hjoining hforward
    · exact (gluedKVertex_map_relation
        copies hjoining hbackward).symm

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (index : Fin 2) :
    Set.InjOn (gluedKHom copies hjoining)
      {vertex : KVertex | vertex.1 = index} := by
  rintro ⟨leftIndex, leftVertex⟩ hleft
    ⟨rightIndex, rightVertex⟩ hright heq
  change leftIndex = index at hleft
  change rightIndex = index at hright
  subst leftIndex
  subst rightIndex
  change copies index leftVertex = copies index rightVertex at heq
  have hvertices := (copies index).injective heq
  subst rightVertex
  rfl

omit [Fintype V] [DecidableEq V] in
lemma gluedKVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter))
    (color : G.Coloring (Fin 2))
    (vertex : KVertex) :
    kColor vertex = false ↔
      color (gluedKVertex copies vertex) =
        color (copies 0 kSpecifiedCenter) := by
  rcases vertex with ⟨index, vertex⟩
  fin_cases index
  · simpa [kColor, gluedKVertex] using
      (gammaCopy_vertex_color_false_iff color (copies 0) vertex)
  · have hvalid :
        color (copies 0 kSpecifiedCenter) ≠
          color (copies 1 kSpecifiedCenter) :=
        color.valid hjoining
    change
      (if (1 : Fin 2) = 0 then subdivisionColor 3 vertex
        else !(subdivisionColor 3 vertex)) = false ↔
        color (copies 1 vertex) = color (copies 0 kSpecifiedCenter)
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    cases hcolor : subdivisionColor 3 vertex
    · simp only [Bool.not_false, Bool.true_eq_false, false_iff]
      intro heq
      have hsame :
          color (copies 1 vertex) =
            color (copies 1 kSpecifiedCenter) :=
        (gammaCopy_vertex_color_false_iff
          color (copies 1) vertex).mp hcolor
      exact hvalid (heq.symm.trans hsame)
    · simp only [Bool.not_true, true_iff]
      have hdistinct :
          color (copies 1 vertex) ≠
            color (copies 1 kSpecifiedCenter) := by
        intro heq
        have hfalse :=
          (gammaCopy_vertex_color_false_iff
            color (copies 1) vertex).mpr heq
        simp [hcolor] at hfalse
      apply Fin.ext
      omega

omit [Fintype V] [DecidableEq V] in
lemma gluedKHom_color_respecting
    {G : SimpleGraph V}
    (hbip : G.IsBipartite)
    (copies : Fin 2 → SimpleGraph.Copy gammaGraph G)
    (hjoining :
      G.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter)) :
    ∀ left right,
      gluedKHom copies hjoining left =
        gluedKHom copies hjoining right →
      kColor left = kColor right := by
  obtain ⟨color⟩ := hbip
  intro left right heq
  have hhostColor :
      color (gluedKVertex copies left) =
        color (gluedKVertex copies right) :=
    congrArg color heq
  cases hleft : kColor left <;> cases hright : kColor right
  · rfl
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mp hleft
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mpr
        (hhostColor.symm.trans hbase)
    simp [hright] at hfalse
  · exfalso
    have hbase :=
      (gluedKVertex_color_false_iff
        copies hjoining color right).mp hright
    have hfalse :=
      (gluedKVertex_color_false_iff
        copies hjoining color left).mpr
        (hhostColor.trans hbase)
    simp [hleft] at hfalse
  · rfl

theorem proposedFamilyFree_not_adj_gammaGood
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hu : GammaGood host u) (hv : GammaGood host v) :
    ¬ host.Adj u v := by
  obtain ⟨first, hfirst⟩ := hu
  obtain ⟨second, hsecond⟩ := hv
  intro hedge
  let copies : Fin 2 → SimpleGraph.Copy gammaGraph host :=
    ![first, second]
  have hjoining :
      host.Adj (copies 0 kSpecifiedCenter)
        (copies 1 kSpecifiedCenter) := by
    change host.Adj (first kSpecifiedCenter)
      (second kSpecifiedCenter)
    rwa [hfirst, hsecond]
  exact proposedFamilyFree_no_kTemplate hfree
    (gluedKHom copies hjoining)
    (gluedKHom_color_respecting hbip copies hjoining)
    (gluedKHom_injOn_marked_copy copies hjoining)

end ActualGammaAndKForcing

section ActualBadVertexEdgeCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def gammaBadVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ¬ GammaGood G v

omit [DecidableEq V] in
lemma mem_gammaBadVertices (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by
  classical
  simp [gammaBadVertices]

theorem proposedFamilyFree_edge_has_gammaBad
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    {u v : Fin n}
    (hedge : host.Adj u v) :
    u ∈ gammaBadVertices host ∨ v ∈ gammaBadVertices host := by
  classical
  by_cases hu : GammaGood host u
  · right
    apply (mem_gammaBadVertices host v).mpr
    intro hv
    exact proposedFamilyFree_not_adj_gammaGood
      host hfree hbip hu hv hedge
  · left
    exact (mem_gammaBadVertices host u).mpr hu

lemma edgeFinset_card_le_sum_degree_of_vertex_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover : Finset V)
    (hcover : ∀ ⦃u v : V⦄, G.Adj u v →
      u ∈ cover ∨ v ∈ cover) :
    G.edgeFinset.card ≤ ∑ v ∈ cover, G.degree v := by
  classical
  have hsubset :
      G.edgeFinset ⊆ cover.biUnion (fun v => G.incidenceFinset v) := by
    intro edge hedge
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hedge
      rcases hcover hadj with hu | hv
      · exact Finset.mem_biUnion.mpr
          ⟨u, hu, (G.mem_incidenceFinset u _).mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
      · exact Finset.mem_biUnion.mpr
          ⟨v, hv, (G.mem_incidenceFinset v _).mpr
            (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
  calc
    G.edgeFinset.card ≤
        (cover.biUnion fun v => G.incidenceFinset v).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ v ∈ cover, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ cover, G.degree v := by
      simp

theorem proposedFamilyFree_edge_card_le_gammaBad_degree_sum
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite) :
    host.edgeFinset.card ≤
      ∑ v ∈ gammaBadVertices host, host.degree v :=
  edgeFinset_card_le_sum_degree_of_vertex_cover
    host (gammaBadVertices host)
    (fun _ _ hedge => proposedFamilyFree_edge_has_gammaBad
      host hfree hbip hedge)

end ActualBadVertexEdgeCounting

end Supersaturation

section BadVertexCounting

open Finset SimpleGraph

noncomputable def finiteBadFiberMass
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop) : ℕ := by
  classical
  exact ∑ index : α,
    ((fibers index).filter fun vertex => ¬ good vertex).card

lemma finite_bad_fiber_card_le_two
    {α β : Type*} [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    [DecidablePred good]
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex)
    (index : α) :
    ((fibers index).filter fun vertex => ¬ good vertex).card ≤ 2 := by
  classical
  by_cases hlarge : 3 ≤ (fibers index).card
  · have hempty :
        (fibers index).filter (fun vertex => ¬ good vertex) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro vertex hvertex hbad
      exact hbad (hgood index vertex hvertex hlarge)
    simp [hempty]
  · have hcard :=
      Finset.card_filter_le (fibers index)
        (fun vertex => ¬ good vertex)
    omega

lemma finite_bad_fiber_mass_le_two
    {α β : Type*} [Fintype α] [Fintype β]
    (fibers : α → Finset β) (good : β → Prop)
    (hgood : ∀ (index : α) (vertex : β),
      vertex ∈ fibers index →
      3 ≤ (fibers index).card → good vertex) :
    finiteBadFiberMass fibers good ≤ 2 * Fintype.card α := by
  classical
  simpa [finiteBadFiberMass, Nat.mul_comm] using
    Finset.sum_le_card_nsmul Finset.univ
      (fun index => ((fibers index).filter fun vertex => ¬ good vertex).card)
      2 (fun index _ => finite_bad_fiber_card_le_two fibers good hgood index)

section ActualIndependentTriples

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun center =>
    ∀ vertex ∈ base, CommonNeighborRelated G vertex center

lemma mem_commonCenterFinset
    (G : SimpleGraph V) (base : Finset V) (center : V) :
    center ∈ commonCenterFinset G base ↔
      ∀ vertex ∈ base, CommonNeighborRelated G vertex center := by
  classical
  simp [commonCenterFinset]

def IsIndependentThetaTriple
    (G : SimpleGraph V) (base : Finset V) : Prop :=
  base.card = 3 ∧
    (base : Set V).Pairwise
      (fun first second => ¬ CommonNeighborRelated G first second) ∧
    2 ≤ (commonCenterFinset G base).card

abbrev IndependentThetaTriple (G : SimpleGraph V) :=
  {base : Finset V // IsIndependentThetaTriple G base}

noncomputable instance independentThetaTripleFintype
    (G : SimpleGraph V) : Fintype (IndependentThetaTriple G) :=
  Fintype.ofFinite _

abbrev OrderedThetaWitness (G : SimpleGraph V) :=
  Σ first : V, Σ second : V,
    {third : V // third ∈ thetaBaseExtensions G first second}

noncomputable def independentThetaTripleBase
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Fin 3 → V :=
  fun index =>
    ((Finset.equivFinOfCardEq triple.property.1).symm index : triple.val)

lemma independentThetaTripleBase_injective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    Function.Injective (independentThetaTripleBase G triple) := by
  intro first second heq
  apply (Finset.equivFinOfCardEq triple.property.1).symm.injective
  exact Subtype.ext heq

lemma independentThetaTripleBase_mem
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    (index : Fin 3) :
    independentThetaTripleBase G triple index ∈ triple.val :=
  ((Finset.equivFinOfCardEq triple.property.1).symm index).property

lemma independentThetaTripleBase_surjective
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    {vertex : V} (hvertex : vertex ∈ triple.val) :
    ∃ index : Fin 3,
      independentThetaTripleBase G triple index = vertex := by
  let member : triple.val := ⟨vertex, hvertex⟩
  refine ⟨Finset.equivFinOfCardEq triple.property.1 member, ?_⟩
  change (((Finset.equivFinOfCardEq triple.property.1).symm
    (Finset.equivFinOfCardEq triple.property.1 member) : triple.val) : V) =
      vertex
  simp [member]

lemma commonCenterFinset_eq_tripleCommonCenters
    (G : SimpleGraph V) (triple : IndependentThetaTriple G) :
    commonCenterFinset G triple.val =
      tripleCommonCenters G (independentThetaTripleBase G triple) := by
  classical
  ext center
  rw [mem_commonCenterFinset, mem_tripleCommonCenters]
  constructor
  · intro hcenter index
    exact hcenter _ (independentThetaTripleBase_mem G triple index)
  · intro hcenter vertex hvertex
    obtain ⟨index, rfl⟩ :=
      independentThetaTripleBase_surjective G triple hvertex
    exact hcenter index

lemma independentThetaTripleBase_unrelated
    (G : SimpleGraph V) (triple : IndependentThetaTriple G)
    ⦃first second : Fin 3⦄ (hne : first ≠ second) :
    ¬ CommonNeighborRelated G
      (independentThetaTripleBase G triple first)
      (independentThetaTripleBase G triple second) := by
  apply triple.property.2.1
    (independentThetaTripleBase_mem G triple first)
    (independentThetaTripleBase_mem G triple second)
  exact fun heq =>
    hne (independentThetaTripleBase_injective G triple heq)

lemma gammaGood_of_independentThetaTriple_fiber
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) (vertex : V)
    (hvertex : vertex ∈ commonCenterFinset G triple.val)
    (hcard : 3 ≤ (commonCenterFinset G triple.val).card) :
    GammaGood G vertex := by
  apply gammaGood_of_three_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hvertex
  · rw [← commonCenterFinset_eq_tripleCommonCenters]
    exact hcard

noncomputable def independentThetaTripleOrderedWitness
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G) : OrderedThetaWitness G := by
  refine ⟨independentThetaTripleBase G triple 1,
    independentThetaTripleBase G triple 2,
    ⟨independentThetaTripleBase G triple 0, ?_⟩⟩
  apply mem_thetaBaseExtensions_of_two_common_centers
    hbip hfour hsix (independentThetaTripleBase G triple)
    (independentThetaTripleBase_injective G triple)
    (independentThetaTripleBase_unrelated G triple)
  rw [← commonCenterFinset_eq_tripleCommonCenters]
  exact triple.property.2.2

lemma independentThetaTripleOrderedWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by
  intro left right heq
  have hbase : independentThetaTripleBase G left =
      independentThetaTripleBase G right := by
    funext index
    fin_cases index
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.2.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.1) heq
    · exact congrArg (fun witness : OrderedThetaWitness G => witness.2.1) heq
  apply Subtype.ext
  ext vertex
  constructor
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G left hvertex
    rw [hbase]
    exact independentThetaTripleBase_mem G right index
  · intro hvertex
    obtain ⟨index, rfl⟩ := independentThetaTripleBase_surjective G right hvertex
    rw [← hbase]
    exact independentThetaTripleBase_mem G left index

lemma orderedThetaWitness_card
    {n : ℕ} (host : SimpleGraph (Fin n)) :
    Fintype.card (OrderedThetaWitness host) =
      orderedThetaTripleCount host := by
  classical
  simp [OrderedThetaWitness, orderedThetaTripleCount,
    Fintype.card_sigma, Fintype.card_coe]

lemma independentThetaTriple_card_le_orderedThetaTripleCount
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    Fintype.card (IndependentThetaTriple host) ≤
      orderedThetaTripleCount host := by
  calc
    Fintype.card (IndependentThetaTriple host) ≤
        Fintype.card (OrderedThetaWitness host) :=
      Fintype.card_le_of_injective
        (independentThetaTripleOrderedWitness host hbip hfour hsix)
        (independentThetaTripleOrderedWitness_injective
          host hbip hfour hsix)
    _ = orderedThetaTripleCount host := orderedThetaWitness_card host

theorem gamma_bad_triple_fiber_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by
  exact (finite_bad_fiber_mass_le_two _ _ (fun triple vertex hvertex hcard =>
    gammaGood_of_independentThetaTriple_fiber
      host hbip hfour hsix triple vertex hvertex hcard)).trans
    (Nat.mul_le_mul_left 2
      (independentThetaTriple_card_le_orderedThetaTripleCount
        host hbip hfour hsix))

end ActualIndependentTriples

end BadVertexCounting

section TripleMassIncidence

open Finset SimpleGraph

section TripleIncidence

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def commonSecondNeighborFinset
    (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x

omit [DecidableEq V] in
lemma mem_commonSecondNeighborFinset
    (G : SimpleGraph V) (u v x : V) :
    x ∈ commonSecondNeighborFinset G u v ↔
      CommonNeighborRelated G u x ∧ CommonNeighborRelated G v x := by
  classical
  simp [commonSecondNeighborFinset]

omit [DecidableEq V] in
lemma commonSecondNeighborFinset_card
    (G : SimpleGraph V) (u v : V) :
    (commonSecondNeighborFinset G u v).card =
      Fintype.card (CommonSecondNeighbor G u v) := by
  classical
  rw [Fintype.card_subtype]
  rfl

abbrev BadFourPathTripleWitness (G : SimpleGraph V) :=
  Σ center : {u : V // ¬ GammaGood G u},
    Σ endpoint : UnrelatedFourPathEndpoint G (center : V),
      {base : Finset V //
        base ∈ (commonSecondNeighborFinset G
          (center : V) (endpoint : V)).powersetCard 3}

abbrev BadIndependentTripleWitness (G : SimpleGraph V) :=
  Σ triple : IndependentThetaTriple G,
    {center : V // center ∈ commonCenterFinset G triple.val ∧
      ¬ GammaGood G center}

noncomputable instance badFourPathTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadFourPathTripleWitness G) := by
  classical
  infer_instance

noncomputable instance badIndependentTripleWitnessFintype
    (G : SimpleGraph V) : Fintype (BadIndependentTripleWitness G) := by
  classical
  infer_instance

noncomputable def fourPathTripleToIndependentThetaTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    IndependentThetaTriple G := by
  have hsubset :
      base.val ⊆ commonSecondNeighborFinset G u (endpoint : V) :=
    (Finset.mem_powersetCard.mp base.property).1
  refine ⟨base.val, ?_, ?_, ?_⟩
  · exact (Finset.mem_powersetCard.mp base.property).2
  · intro x hx y hy hne
    have hx' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)
    have hy' := (mem_commonSecondNeighborFinset
      G u (endpoint : V) y).mp (hsubset hy)
    exact common_second_neighbor_pairwise_unrelated
      G hbip hfour hsix endpoint.property.1 endpoint.property.2
      (⟨x, hx'⟩ : CommonSecondNeighbor G u (endpoint : V))
      (⟨y, hy'⟩ : CommonSecondNeighbor G u (endpoint : V))
  · have hu : u ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val u).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).1
    have hv : (endpoint : V) ∈ commonCenterFinset G base.val := by
      apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
      intro x hx
      exact commonNeighborRelated_symm
        ((mem_commonSecondNeighborFinset
          G u (endpoint : V) x).mp (hsubset hx)).2
    have hcard : 1 < (commonCenterFinset G base.val).card :=
      Finset.one_lt_card.mpr
        ⟨u, hu, (endpoint : V), hv, endpoint.property.1⟩
    omega

lemma fourPathTripleToIndependentThetaTriple_center_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    u ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change u ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val u).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).1

lemma fourPathTripleToIndependentThetaTriple_endpoint_mem
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    (endpoint : V) ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change (endpoint : V) ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).2

lemma badIndependentThetaTriple_other_center_unique
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (triple : IndependentThetaTriple G)
    (u : V)
    (hu : u ∈ commonCenterFinset G triple.val)
    (hbad : ¬ GammaGood G u)
    {v w : V}
    (hv : v ∈ commonCenterFinset G triple.val)
    (hw : w ∈ commonCenterFinset G triple.val)
    (huv : u ≠ v) (huw : u ≠ w) :
    v = w := by
  classical
  by_contra hvw
  have hsubset :
      ({u, v, w} : Finset V) ⊆ commonCenterFinset G triple.val := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hw
  have hcard : 3 ≤ (commonCenterFinset G triple.val).card := by
    calc
      3 = ({u, v, w} : Finset V).card := by
        simp [huv, huw, hvw]
      _ ≤ (commonCenterFinset G triple.val).card :=
        Finset.card_le_card hsubset
  exact hbad (gammaGood_of_independentThetaTriple_fiber
    G hbip hfour hsix triple u hu hcard)

noncomputable def badFourPathTripleToBadIndependentTriple
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    BadFourPathTripleWitness G → BadIndependentTripleWitness G := by
  rintro ⟨center, endpoint, base⟩
  refine ⟨fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix center endpoint base, ?_⟩
  refine ⟨center, ?_, center.property⟩
  exact fourPathTripleToIndependentThetaTriple_center_mem
    G hbip hfour hsix center endpoint base

lemma badFourPathTripleToBadIndependentTriple_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (badFourPathTripleToBadIndependentTriple
        G hbip hfour hsix) := by
  rintro ⟨u, v, base⟩ ⟨u', v', base'⟩ heq
  have hcenter := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      (witness.2 : V)) heq
  change (u : V) = (u' : V) at hcenter
  have husub : u = u' := Subtype.ext hcenter
  subst u'
  have hbase := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      witness.1.val) heq
  change base.val = base'.val at hbase
  let triple := fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix (u : V) v base
  have hu : (u : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_center_mem
      G hbip hfour hsix (u : V) v base
  have hv : (v : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v base
  have hv' : (v' : V) ∈ commonCenterFinset G triple.val := by
    change (v' : V) ∈ commonCenterFinset G base.val
    rw [hbase]
    exact fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v' base'
  have hendpoint : (v : V) = (v' : V) :=
    badIndependentThetaTriple_other_center_unique
      G hbip hfour hsix triple (u : V) hu u.property hv hv'
      v.property.1 v'.property.1
  have hvsub : v = v' := Subtype.ext hendpoint
  subst v'
  have hbasesub : base = base' := Subtype.ext hbase
  subst base'
  rfl

omit [DecidableEq V] in
lemma badFourPathTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadFourPathTripleWitness G) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_coe,
    Finset.card_powersetCard, commonSecondNeighborFinset_card]
  change
    (∑ u : {u : V // ¬ GammaGood G u},
      commonSecondNeighborTripleMass G u) =
      ∑ u ∈ gammaBadVertices G,
        commonSecondNeighborTripleMass G u
  symm
  apply Finset.sum_subtype
    (gammaBadVertices G)
    (fun u => (mem_gammaBadVertices G u))

lemma badIndependentTripleWitness_card
    (G : SimpleGraph V) :
    Fintype.card (BadIndependentTripleWitness G) =
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  classical
  rw [Fintype.card_sigma]
  unfold finiteBadFiberMass
  apply Finset.sum_congr
  · rfl
  · intro triple htriple
    rw [Fintype.card_subtype]
    congr 1
    ext center
    simp

lemma gammaBad_four_path_triple_mass_le_bad_fiber_mass
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    (∑ u ∈ gammaBadVertices G,
      commonSecondNeighborTripleMass G u) ≤
      finiteBadFiberMass
        (fun triple : IndependentThetaTriple G =>
          commonCenterFinset G triple.val)
        (GammaGood G) := by
  rw [← badFourPathTripleWitness_card,
    ← badIndependentTripleWitness_card]
  exact Fintype.card_le_of_injective
    (badFourPathTripleToBadIndependentTriple
      G hbip hfour hsix)
    (badFourPathTripleToBadIndependentTriple_injective
      G hbip hfour hsix)

theorem gammaBad_four_path_triple_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    (∑ u ∈ gammaBadVertices host,
      commonSecondNeighborTripleMass host u) ≤
      2 * orderedThetaTripleCount host := by
  exact (gammaBad_four_path_triple_mass_le_bad_fiber_mass
    host hbip hfour hsix).trans
      (gamma_bad_triple_fiber_mass_le_two_orderedTheta
        host hbip hfour hsix)

lemma gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        (fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54) ≤
      2 * (orderedThetaTripleCount host : ℝ) := by
  classical
  let lower : ℝ :=
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54
  have hpoint (u : Fin n) :
      lower ≤ (commonSecondNeighborTripleMass host u : ℝ) := by
    exact proposedFamilyFree_four_path_triple_mass_lower
      host hfree hbip d hdegree u hthreshold
  change ((gammaBadVertices host).card : ℝ) * lower ≤
    2 * (orderedThetaTripleCount host : ℝ)
  calc
    ((gammaBadVertices host).card : ℝ) * lower =
        ∑ u ∈ gammaBadVertices host, lower := by simp
    _ ≤ ∑ u ∈ gammaBadVertices host,
        (commonSecondNeighborTripleMass host u : ℝ) := by
      gcongr with u hu
      exact hpoint u
    _ = ((∑ u ∈ gammaBadVertices host,
          commonSecondNeighborTripleMass host u) : ℝ) := by
      simp
    _ ≤ ((2 * orderedThetaTripleCount host : ℕ) : ℝ) := by
      exact_mod_cast
        (gammaBad_four_path_triple_mass_le_two_orderedTheta
          host hbip (proposedFamilyFree_four_cycle hfree)
          (proposedFamilyFree_six_cycle hfree))
    _ = 2 * (orderedThetaTripleCount host : ℝ) := by
      norm_num

theorem gammaBad_card_mul_fourpath_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (gammaBadVertices host).card *
      (d * (d - 1) ^ 3) ^ 3 * d ≤ 432 * n ^ 5 := by
  have hn : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hzero
    subst n
    norm_num [fourPathHeavyThreshold] at hthreshold
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let p : ℕ := d * (d - 1) ^ 3
  let bad : ℕ := (gammaBadVertices host).card
  let theta : ℕ := orderedThetaTripleCount host
  have hmass :
      (bad : ℝ) *
        (fourPathHeavyThreshold n p ^ 2 *
          (p : ℝ) / 54) ≤ 2 * (theta : ℝ) := by
    exact gammaBad_card_mul_heavyTripleLower_le_two_orderedTheta
      host hfree hbip d hdegree hthreshold
  have hnormalized :
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) ≤ 2 * (theta : ℝ) := by
    calc
      ((bad : ℝ) * (p : ℝ) ^ 3) /
          (216 * (n : ℝ) ^ 2) =
        (bad : ℝ) *
          (fourPathHeavyThreshold n p ^ 2 * (p : ℝ) / 54) := by
            unfold fourPathHeavyThreshold
            field_simp [ne_of_gt hnReal]
            ring
      _ ≤ 2 * (theta : ℝ) := hmass
  have hden : 0 < (216 : ℝ) * (n : ℝ) ^ 2 := by
    positivity
  have hclear := (div_le_iff₀ hden).mp hnormalized
  have hbadpoly :
      (bad : ℝ) * (p : ℝ) ^ 3 ≤
        432 * (theta : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have htheta :
      (theta : ℝ) * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast
      (orderedThetaTripleCount_mul_degree_le
        host hfree hbip d hdegree)
  have hfinal :
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 5 := by
    calc
      (bad : ℝ) * (p : ℝ) ^ 3 * (d : ℝ) ≤
          (432 * (theta : ℝ) * (n : ℝ) ^ 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right hbadpoly (Nat.cast_nonneg d)
      _ = 432 * ((theta : ℝ) * (d : ℝ)) * (n : ℝ) ^ 2 := by ring
      _ ≤ 432 * (n : ℝ) ^ 3 * (n : ℝ) ^ 2 := by
        gcongr
      _ = 432 * (n : ℝ) ^ 5 := by ring
  exact_mod_cast hfinal

theorem proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n := by
  classical
  calc
    host.edgeFinset.card * (d - 1) ^ 2 ≤
        (∑ u ∈ gammaBadVertices host, host.degree u) *
          (d - 1) ^ 2 :=
      Nat.mul_le_mul_right ((d - 1) ^ 2)
        (proposedFamilyFree_edge_card_le_gammaBad_degree_sum
          host hfree hbip)
    _ = ∑ u ∈ gammaBadVertices host,
        host.degree u * (d - 1) ^ 2 := by
      simp [Finset.sum_mul]
    _ ≤ ∑ _u ∈ gammaBadVertices host, n := by
      gcongr with u hu
      simpa using girthEight_degree_mul_pred_sq_le_card
        host hbip (proposedFamilyFree_four_cycle hfree)
        (proposedFamilyFree_six_cycle hfree) d hdegree u
    _ = (gammaBadVertices host).card * n := by simp

lemma fourPathHeavyThreshold_low_degree_fourth_le
    (N d : ℕ)
    (hN : 0 < N)
    (hd : 2 ≤ d)
    (hlow : ¬ (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 4 ≤ 48 * (N : ℝ) := by
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hthreshold :
      fourPathHeavyThreshold N (d * (d - 1) ^ 3) < 3 :=
    lt_of_not_ge hlow
  have hp :
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) < 6 * (N : ℝ) := by
    unfold fourPathHeavyThreshold at hthreshold
    have hden : 0 < 2 * (N : ℝ) := by positivity
    have hclear := (div_lt_iff₀ hden).mp hthreshold
    nlinarith
  have hpredNat : d ≤ 2 * (d - 1) := by omega
  have hpredReal : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hpowers :
      (d : ℝ) ^ 3 ≤ (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 := by
    gcongr
  have hfourth :
      (d : ℝ) ^ 4 ≤
        8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
    calc
      (d : ℝ) ^ 4 = (d : ℝ) * (d : ℝ) ^ 3 := by ring
      _ ≤ (d : ℝ) *
          (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpowers (Nat.cast_nonneg d)
      _ = 8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
        push_cast
        ring
  nlinarith

end TripleIncidence

end TripleMassIncidence

section QuantitativeBadVertexBound

open Finset SimpleGraph

lemma quantitative_minimum_degree_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    n * d ≤ 2 * host.edgeFinset.card := by
  simpa [SimpleGraph.sum_degrees_eq_twice_card_edges] using
    Finset.card_nsmul_le_sum Finset.univ
      (fun vertex : Fin n => host.degree vertex) d
      (fun vertex _ => hdegree vertex)

lemma quantitative_bad_vertex_edge_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex) :
    host.edgeFinset.card * (d - 1) ^ 2 ≤
      (gammaBadVertices host).card * n :=
  proposedFamilyFree_edge_mul_pred_sq_le_bad_card_mul
    host hfree hbip d hdegree

lemma quantitative_bad_vertex_heavy_triple_bound
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    ((gammaBadVertices host).card : ℝ) *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
      432 * (n : ℝ) ^ 5 := by
  apply (mul_le_mul_iff_right₀
    (by exact_mod_cast hn : (0 : ℝ) < n)).mp
  exact_mod_cast Nat.mul_le_mul_left n
    (gammaBad_card_mul_fourpath_power_le
      host hfree hbip d hdegree hthreshold)

theorem proposedFamilyFree_minDegree_polynomial_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 ≤
      864 * (n : ℝ) ^ 5 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdegreeReal :
      (n : ℝ) * (d : ℝ) ≤ 2 * (host.edgeFinset.card : ℝ) := by
    exact_mod_cast quantitative_minimum_degree_edge_bound
      host d hdegree
  have hedgeReal :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 ≤
        ((gammaBadVertices host).card : ℝ) * (n : ℝ) := by
    exact_mod_cast quantitative_bad_vertex_edge_bound
      host hfree hbip d hdegree
  have hbadReal := quantitative_bad_vertex_heavy_triple_bound
    host hn hfree hbip d hdegree hthreshold
  have hedgePolynomial :
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
        432 * (n : ℝ) ^ 6 := by
    calc
      (host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) ≤
          (((gammaBadVertices host).card : ℝ) * (n : ℝ)) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ) := by
        gcongr
      _ = (((gammaBadVertices host).card : ℝ) *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) *
            (n : ℝ) := by ring
      _ ≤ (432 * (n : ℝ) ^ 5) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hbadReal (Nat.cast_nonneg n)
      _ = 432 * (n : ℝ) ^ 6 := by ring
  apply (mul_le_mul_iff_right₀ hnreal).mp
  calc
    (n : ℝ) *
        ((d : ℝ) ^ 2 * ((d - 1 : ℕ) : ℝ) ^ 2 *
          ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3) =
        ((n : ℝ) * (d : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ (2 * (host.edgeFinset.card : ℝ)) *
          (((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      gcongr
    _ = 2 *
          ((host.edgeFinset.card : ℝ) * ((d - 1 : ℕ) : ℝ) ^ 2 *
            ((d * (d - 1) ^ 3 : ℕ) : ℝ) ^ 3 * (d : ℝ)) := by
      ring
    _ ≤ 2 * (432 * (n : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left hedgePolynomial (by norm_num)
    _ = (n : ℝ) * (864 * (n : ℝ) ^ 5) := by ring

theorem proposedFamilyFree_minDegree_sixteenth_power_le
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hn : 0 < n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hd : 2 ≤ d)
    (hdegree : ∀ vertex : Fin n, d ≤ host.degree vertex)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 16 ≤ 1769472 * (n : ℝ) ^ 5 := by
  have hraw := proposedFamilyFree_minDegree_polynomial_le
    host hn hfree hbip d hdegree hthreshold
  have hshape :
      (d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11 ≤
        864 * (n : ℝ) ^ 5 := by
    convert hraw using 1
    push_cast
    ring
  have hdone : 1 ≤ d := by omega
  have hhalf : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdone, Nat.cast_one]
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    (d : ℝ) ^ 16 = (d : ℝ) ^ 5 * (d : ℝ) ^ 11 := by ring
    _ ≤ (d : ℝ) ^ 5 *
        (2 * ((d - 1 : ℕ) : ℝ)) ^ 11 := by
      gcongr
    _ = 2 ^ (11 : ℕ) *
        ((d : ℝ) ^ 5 * ((d - 1 : ℕ) : ℝ) ^ 11) := by ring
    _ ≤ 2 ^ (11 : ℕ) * (864 * (n : ℝ) ^ 5) := by
      gcongr
    _ = 1769472 * (n : ℝ) ^ 5 := by ring

end QuantitativeBadVertexBound

end Erdos180
