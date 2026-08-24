/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 574.
https://www.erdosproblems.com/forum/thread/574

Informal authors:
- Felix Lazebnik
- Vasiliy Ustimenko
- Andrew Woldar

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos574.md
-/
import ErdosProblems.Erdos59.CycleAdapters
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Erdős Problem 574

The proposed asymptotic formula for graphs avoiding two consecutive cycle
lengths is false.  We formalize the counterexample at `k = 3`: a two-copy
Lazebnik--Ustimenko--Woldar construction gives, at unbounded orders `3*q^3`,
a bipartite `C₆`-free graph with exactly `2*q^4` edges.  Its leading constant
`2 / 3^(4/3)` is strictly larger than the proposed `2^(-4/3)`.
-/

namespace Erdos574

open Filter Finset Fintype SimpleGraph
open scoped Asymptotics BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A graph is free of the two consecutive cycles occurring in Problem 574. -/
def FreeConsecutiveCycles {V : Type*} (k : ℕ) (G : SimpleGraph V) : Prop :=
  (SimpleGraph.cycleGraph (2 * k - 1)).Free G ∧
    (SimpleGraph.cycleGraph (2 * k)).Free G

/-- The exact extremal number for the forbidden family `{C_(2k-1), C_(2k)}`. -/
noncomputable def consecutiveCycleExtremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact Finset.sup {G : SimpleGraph (Fin n) | FreeConsecutiveCycles k G}
      (fun G ↦ G.edgeFinset.card)

/-- Every admissible labelled graph supplies a lower bound for the family extremal number. -/
theorem card_edgeFinset_le_consecutiveCycleExtremalNumber
    {k n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : FreeConsecutiveCycles k G) :
    G.edgeFinset.card ≤ consecutiveCycleExtremalNumber k n := by
  classical
  rw [consecutiveCycleExtremalNumber]
  convert! @Finset.le_sup _ _ _ _
    {H : SimpleGraph (Fin n) | FreeConsecutiveCycles k H}
    (fun H ↦ H.edgeFinset.card) G (by simpa using hG)

/-- The comparison function on the right-hand side of the conjecture. -/
noncomputable def erdos574Comparison (k n : ℕ) : ℝ :=
  ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ))

/-- The exact universal assertion asked in Erdős Problem 574. -/
def erdos_574 : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
      erdos574Comparison k

namespace LUW

open Erdos59
open Erdos59.AffinePolarity

/-- The finite-field order used by the affine incidence construction. -/
def q (a : ℕ) : ℕ := 2 ^ (2 * a + 1)

/-- Two labelled copies of the line side, together with the point side. -/
abbrev Vertex (a : ℕ) := Point a ⊕ (Bool × Line a)

/-- The `t = 2` LUW duplication of the affine incidence graph. -/
def graph (a : ℕ) : SimpleGraph (Vertex a) :=
  SimpleGraph.fromRel fun v w ↦
    match v, w with
    | Sum.inl p, Sum.inr (_, l) => Incident p l
    | _, _ => False

noncomputable instance graphDecidableRel (a : ℕ) : DecidableRel (graph a).Adj :=
  Classical.decRel _

@[simp] theorem graph_adj_inl_inl {a : ℕ} (p p' : Point a) :
    ¬(graph a).Adj (Sum.inl p) (Sum.inl p') := by
  simp [graph]

@[simp] theorem graph_adj_inr_inr {a : ℕ} (x y : Bool × Line a) :
    ¬(graph a).Adj (Sum.inr x) (Sum.inr y) := by
  simp [graph]

@[simp] theorem graph_adj_inl_inr {a : ℕ} (p : Point a) (b : Bool) (l : Line a) :
    (graph a).Adj (Sum.inl p) (Sum.inr (b, l)) ↔ Incident p l := by
  simp [graph]

@[simp] theorem graph_adj_inr_inl {a : ℕ} (b : Bool) (l : Line a) (p : Point a) :
    (graph a).Adj (Sum.inr (b, l)) (Sum.inl p) ↔ Incident p l := by
  simp [graph]

/-- The point side as a finset. -/
noncomputable def leftPart (a : ℕ) : Finset (Vertex a) := by
  classical
  exact Finset.univ.image (fun p : Point a ↦ Sum.inl p)

/-- The doubled line side as a finset. -/
noncomputable def rightPart (a : ℕ) : Finset (Vertex a) := by
  classical
  exact Finset.univ.image (fun x : Bool × Line a ↦ Sum.inr x)

theorem graph_isBipartiteWith (a : ℕ) :
    (graph a).IsBipartiteWith (leftPart a : Set (Vertex a))
      (rightPart a : Set (Vertex a)) := by
  classical
  constructor
  · simp [Set.disjoint_left, leftPart, rightPart]
  · rintro (p | x) (p' | y) h
    · simp at h
    · exact Or.inl ⟨by simp [leftPart], by simp [rightPart]⟩
    · exact Or.inr ⟨by simp [rightPart], by simp [leftPart]⟩
    · simp at h

theorem graph_isBipartite (a : ℕ) : (graph a).IsBipartite :=
  (graph_isBipartiteWith a).isBipartite

/-- The neighbors of a point are a Boolean label and an incident line. -/
noncomputable def pointNeighborEquiv {a : ℕ} (p : Point a) :
    (graph a).neighborSet (Sum.inl p) ≃
      Bool × {l : Line a // Incident p l} where
  toFun x := by
    rcases x with ⟨v, hv⟩
    rcases v with p' | ⟨b, l⟩
    · simp [SimpleGraph.mem_neighborSet] at hv
    · exact ⟨b, l, by simpa [SimpleGraph.mem_neighborSet] using hv⟩
  invFun x :=
    ⟨Sum.inr (x.1, x.2.1), by
      simpa [SimpleGraph.mem_neighborSet] using x.2.2⟩
  left_inv x := by
    rcases x with ⟨v, hv⟩
    rcases v with p' | ⟨b, l⟩
    · simp [SimpleGraph.mem_neighborSet] at hv
    · rfl
  right_inv x := by
    rcases x with ⟨b, l, hl⟩
    rfl

theorem degree_inl (a : ℕ) (p : Point a) :
    (graph a).degree (Sum.inl p) = 2 * q a := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [Fintype.card_congr (pointNeighborEquiv p)]
  simp [q, card_incident_lines]

theorem card_vertex (a : ℕ) :
    Fintype.card (Vertex a) = 3 * (q a) ^ 3 := by
  simp [q, coord_card]
  ring

theorem card_edgeFinset (a : ℕ) :
    (graph a).edgeFinset.card = 2 * (q a) ^ 4 := by
  classical
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (graph_isBipartiteWith a)]
  rw [leftPart, Finset.sum_image fun _ _ _ _ h ↦ Sum.inl.inj h]
  simp_rw [degree_inl]
  simp [q, coord_card]
  ring

private theorem no_alternating_hexagon {a : ℕ}
    (p₀ p₁ p₂ : Point a) (b₀ b₁ b₂ : Bool) (l₀ l₁ l₂ : Line a)
    (hp₀₁ : p₀ ≠ p₁) (hp₁₂ : p₁ ≠ p₂) (hp₂₀ : p₂ ≠ p₀)
    (hr₀₁ : (b₀, l₀) ≠ (b₁, l₁))
    (hr₁₂ : (b₁, l₁) ≠ (b₂, l₂))
    (hr₂₀ : (b₂, l₂) ≠ (b₀, l₀))
    (h₀₀ : Incident p₀ l₀) (h₁₀ : Incident p₁ l₀)
    (h₁₁ : Incident p₁ l₁) (h₂₁ : Incident p₂ l₁)
    (h₂₂ : Incident p₂ l₂) (h₀₂ : Incident p₀ l₂) : False := by
  by_cases hl₀₁ : l₀ = l₁
  · subst l₁
    by_cases hl₂₀ : l₂ = l₀
    · subst l₂
      cases b₀ <;> cases b₁ <;> cases b₂ <;> simp_all
    · apply no_incidence_C4
      exact ⟨p₀, p₂, l₀, l₂, hp₂₀.symm, fun h ↦ hl₂₀ h.symm,
        h₀₀, h₂₁, h₀₂, h₂₂⟩
  · by_cases hl₁₂ : l₁ = l₂
    · subst l₂
      apply no_incidence_C4
      exact ⟨p₀, p₁, l₀, l₁, hp₀₁, hl₀₁,
        h₀₀, h₁₀, h₀₂, h₁₁⟩
    · by_cases hl₂₀ : l₂ = l₀
      · subst l₂
        apply no_incidence_C4
        exact ⟨p₁, p₂, l₁, l₀, hp₁₂, fun h ↦ hl₀₁ h.symm,
          h₁₁, h₂₁, h₁₀, h₂₂⟩
      · apply no_incidence_C6
        exact ⟨p₀, p₁, p₂, l₀, l₁, l₂,
          hp₀₁, hp₁₂, hp₂₀, hl₀₁, hl₁₂, hl₂₀,
          h₀₀, h₁₀, h₁₁, h₂₁, h₂₂, h₀₂⟩

theorem no_explicit_C6 (a : ℕ) :
    ¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅,
      Erdos59.AffinePolarity.IsC6 (graph a) v₀ v₁ v₂ v₃ v₄ v₅ := by
  rintro ⟨v₀, v₁, v₂, v₃, v₄, v₅,
    h₀₁, h₀₂, h₀₃, h₀₄, h₀₅, h₁₂, h₁₃, h₁₄, h₁₅,
    h₂₃, h₂₄, h₂₅, h₃₄, h₃₅, h₄₅,
    ha₀₁, ha₁₂, ha₂₃, ha₃₄, ha₄₅, ha₅₀⟩
  rcases v₀ with p₀ | ⟨b₂, l₂⟩
  · rcases v₁ with p | ⟨b₀, l₀⟩
    · simp at ha₀₁
    · rcases v₂ with p₁ | x
      · rcases v₃ with p | ⟨b₁, l₁⟩
        · simp at ha₂₃
        · rcases v₄ with p₂ | x
          · rcases v₅ with p | ⟨b₂, l₂⟩
            · simp at ha₄₅
            · exact no_alternating_hexagon p₀ p₁ p₂ b₀ b₁ b₂ l₀ l₁ l₂
                (fun h ↦ h₀₂ (congrArg Sum.inl h))
                (fun h ↦ h₂₄ (congrArg Sum.inl h))
                (fun h ↦ h₀₄ (congrArg Sum.inl h.symm))
                (fun h ↦ h₁₃ (congrArg Sum.inr h))
                (fun h ↦ h₃₅ (congrArg Sum.inr h))
                (fun h ↦ h₁₅ (congrArg Sum.inr h.symm))
                (by simpa using ha₀₁) (by simpa using ha₁₂)
                (by simpa using ha₂₃) (by simpa using ha₃₄)
                (by simpa using ha₄₅) (by simpa using ha₅₀)
          · simp at ha₃₄
      · simp at ha₁₂
  · rcases v₁ with p₀ | x
    · rcases v₂ with p | ⟨b₀, l₀⟩
      · simp at ha₁₂
      · rcases v₃ with p₁ | x
        · rcases v₄ with p | ⟨b₁, l₁⟩
          · simp at ha₃₄
          · rcases v₅ with p₂ | x
            · exact no_alternating_hexagon p₀ p₁ p₂ b₀ b₁ b₂ l₀ l₁ l₂
                (fun h ↦ h₁₃ (congrArg Sum.inl h))
                (fun h ↦ h₃₅ (congrArg Sum.inl h))
                (fun h ↦ h₁₅ (congrArg Sum.inl h.symm))
                (fun h ↦ h₂₄ (congrArg Sum.inr h))
                (fun h ↦ h₀₄ (congrArg Sum.inr h.symm))
                (fun h ↦ h₀₂ (congrArg Sum.inr h))
                (by simpa using ha₁₂) (by simpa using ha₂₃)
                (by simpa using ha₃₄) (by simpa using ha₄₅)
                (by simpa using ha₅₀) (by simpa using ha₀₁)
            · simp at ha₄₅
        · simp at ha₂₃
    · simp at ha₀₁

theorem cycleGraph_six_free (a : ℕ) :
    (SimpleGraph.cycleGraph 6).Free (graph a) :=
  (Erdos59.CycleAdapters.affine_no_c6_iff_cycleGraph_six_free (graph a)).mp
    (no_explicit_C6 a)

theorem cycleGraph_five_free (a : ℕ) :
    (SimpleGraph.cycleGraph 5).Free (graph a) := by
  intro hcopy
  rcases hcopy with ⟨copy⟩
  have hmono := SimpleGraph.chromaticNumber_mono_of_hom copy.toHom
  have hfive : (SimpleGraph.cycleGraph 5).chromaticNumber = 3 :=
    SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by omega) (by decide)
  have htwo : (graph a).chromaticNumber ≤ 2 :=
    SimpleGraph.chromaticNumber_le_two_iff_isBipartite.mpr (graph_isBipartite a)
  rw [hfive] at hmono
  exact (by norm_num : ¬(3 : ℕ∞) ≤ 2) (hmono.trans htwo)

/-- A labelled version of the construction on its exact number of vertices. -/
noncomputable def finiteGraph (a : ℕ) :
    SimpleGraph (Fin (3 * (q a) ^ 3)) :=
  (graph a).overFin (card_vertex a)

noncomputable instance finiteGraphDecidableRel (a : ℕ) :
    DecidableRel (finiteGraph a).Adj := Classical.decRel _

/-- The coordinate and labelled versions are isomorphic. -/
noncomputable def finiteGraphIso (a : ℕ) :
    graph a ≃g finiteGraph a :=
  (graph a).overFinIso (card_vertex a)

theorem finiteGraph_edge_card (a : ℕ) :
    (finiteGraph a).edgeFinset.card = 2 * (q a) ^ 4 := by
  rw [← (finiteGraphIso a).card_edgeFinset_eq]
  exact card_edgeFinset a

theorem finiteGraph_free (a : ℕ) : FreeConsecutiveCycles 3 (finiteGraph a) := by
  change (SimpleGraph.cycleGraph 5).Free (finiteGraph a) ∧
    (SimpleGraph.cycleGraph 6).Free (finiteGraph a)
  constructor
  · exact (SimpleGraph.free_congr_right (finiteGraphIso a)).mp (cycleGraph_five_free a)
  · exact (SimpleGraph.free_congr_right (finiteGraphIso a)).mp (cycleGraph_six_free a)

theorem extremal_lower (a : ℕ) :
    2 * (q a) ^ 4 ≤ consecutiveCycleExtremalNumber 3 (3 * (q a) ^ 3) := by
  rw [← finiteGraph_edge_card]
  exact card_edgeFinset_le_consecutiveCycleExtremalNumber (finiteGraph_free a)

end LUW

private theorem three_halves_rpow_four_thirds_lt_twenty_elevenths :
    (3 / 2 : ℝ) ^ (4 / 3 : ℝ) < 20 / 11 := by
  apply lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 20 / 11)
  have hleft : ((3 / 2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 = (3 / 2 : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    norm_num [Real.rpow_natCast]
  rw [hleft]
  norm_num

private theorem conjectured_constant_strictly_too_small :
    (11 / 10 : ℝ) * (3 / 2 : ℝ) ^ (4 / 3 : ℝ) < 2 := by
  nlinarith [three_halves_rpow_four_thirds_lt_twenty_elevenths]

private theorem scaled_constant_gap (q₀ : ℕ) (hq₀ : 0 < q₀) :
    (11 / 10 : ℝ) * (((3 * q₀ ^ 3 : ℕ) : ℝ) / 2) ^ (4 / 3 : ℝ) <
      ((2 * q₀ ^ 4 : ℕ) : ℝ) := by
  have hqreal : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hbase : (((3 * q₀ ^ 3 : ℕ) : ℝ) / 2) =
      (3 / 2 : ℝ) * (q₀ : ℝ) ^ 3 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    ring
  have hscale : (((q₀ : ℝ) ^ 3) ^ (4 / 3 : ℝ)) = (q₀ : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqreal.le]
    norm_num [Real.rpow_natCast]
  rw [hbase, Real.mul_rpow (by norm_num) (by positivity), hscale]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  calc
    (11 / 10 : ℝ) * ((3 / 2 : ℝ) ^ (4 / 3 : ℝ) * (q₀ : ℝ) ^ 4) =
        ((11 / 10 : ℝ) * (3 / 2 : ℝ) ^ (4 / 3 : ℝ)) * (q₀ : ℝ) ^ 4 := by ring
    _ < 2 * (q₀ : ℝ) ^ 4 :=
      mul_lt_mul_of_pos_right conjectured_constant_strictly_too_small (pow_pos hqreal 4)

/-- Erdős Problem 574 has a negative answer.  The asserted asymptotic fails already at `k = 3`. -/
theorem not_erdos_574 :
    ¬ (∀ k : ℕ, 2 ≤ k →
      (fun n : ℕ ↦ (consecutiveCycleExtremalNumber k n : ℝ)) ~[atTop]
        erdos574Comparison k) := by
  intro h574
  have hequiv := h574 3 (by omega)
  have hsmall := hequiv.isLittleO.def (by norm_num : (0 : ℝ) < 1 / 10)
  have hupper : ∀ᶠ n : ℕ in atTop,
      (consecutiveCycleExtremalNumber 3 n : ℝ) ≤
        (11 / 10 : ℝ) * ((n : ℝ) / 2) ^ (4 / 3 : ℝ) := by
    filter_upwards [hsmall] with n hn
    have hcomparison_nonneg :
        0 ≤ ((n : ℝ) / 2) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hn
    rw [show erdos574Comparison 3 n = ((n : ℝ) / 2) ^ (4 / 3 : ℝ) by
      norm_num [erdos574Comparison], abs_of_nonneg hcomparison_nonneg] at hn
    have hdiff_le_abs :
        (consecutiveCycleExtremalNumber 3 n : ℝ) -
            ((n : ℝ) / 2) ^ (4 / 3 : ℝ) ≤
          |(consecutiveCycleExtremalNumber 3 n : ℝ) -
            ((n : ℝ) / 2) ^ (4 / 3 : ℝ)| := le_abs_self _
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hupper
  let a := N + 1
  have hqpos : 0 < LUW.q a := by simp [LUW.q]
  have hNq : N < LUW.q a := by
    calc
      N < 2 * a + 1 := by dsimp [a]; omega
      _ < 2 ^ (2 * a + 1) := Nat.lt_two_pow_self
      _ = LUW.q a := by rfl
  have hqone : 1 ≤ LUW.q a := Nat.one_le_iff_ne_zero.mpr hqpos.ne'
  have hqpow : LUW.q a ≤ (LUW.q a) ^ 3 :=
    le_self_pow₀ hqone (by norm_num)
  have hNorder : N ≤ 3 * (LUW.q a) ^ 3 := by omega
  have hupper_at := hN (3 * (LUW.q a) ^ 3) hNorder
  have hlower := LUW.extremal_lower a
  have hlower_real :
      ((2 * (LUW.q a) ^ 4 : ℕ) : ℝ) ≤
        (consecutiveCycleExtremalNumber 3 (3 * (LUW.q a) ^ 3) : ℝ) := by
    exact_mod_cast hlower
  have hgap := scaled_constant_gap (LUW.q a) hqpos
  exact (not_lt_of_ge (hlower_real.trans hupper_at)) hgap

end Erdos574

#print axioms Erdos574.not_erdos_574
