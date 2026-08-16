import ErdosProblems.Erdos920.TupleHistory
import ErdosProblems.Erdos920.MarkedChildrenBound
import ErdosProblems.Erdos920.StoppingPower
import ErdosProblems.Erdos920.NumericAbsorption

/-!
# The forward-independent tuple bound for the projective `D*`

This file assembles the projective container argument.  The geometric
input is the poor/popular marking and its shrink certificate; the two
numerical inputs are the stopping-power estimate and the final absorption
of the exceptional levels.
-/

open scoped LinearAlgebra.Projectivization

namespace Erdos920.ForwardBound

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveDStar
open Erdos920.RamseyPackaging

/-- Coefficient in the uniform marked-child bound. -/
def markedCoefficient (t : ℕ) : ℕ := 2112 * (t + 1)

/-- Coefficient which pays for the stopping depth at all `t+2` levels. -/
def totalStoppingCoefficient (t : ℕ) : ℕ :=
  (t + 2) * StoppingPower.stoppingCoefficient t

/-- A common coefficient for marked and unmarked exceptional steps. -/
def treeCoefficient (t : ℕ) : ℕ :=
  max (markedCoefficient t) (totalStoppingCoefficient t)

/-- The constant occurring both in the length hypothesis and in the final
exponential base. -/
def forwardConstantNat (t : ℕ) : ℕ :=
  NumericAbsorption.absorptionConstant t (treeCoefficient t)

/-- A threshold which ensures both `q ≥ 4` and `treeCoefficient t ≤ q`. -/
def forwardThreshold (t : ℕ) : ℕ := max 4 (treeCoefficient t)

theorem treeCoefficient_pos (t : ℕ) : 1 ≤ treeCoefficient t := by
  unfold treeCoefficient markedCoefficient
  omega

theorem forwardConstantNat_pos {t : ℕ} (ht : 2 ≤ t) :
    0 < forwardConstantNat t := by
  exact NumericAbsorption.absorptionConstant_pos (by omega)
    (treeCoefficient_pos t)

variable {q t m : ℕ} [Fact q.Prime]

abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)

local instance pointFintype : Fintype (PointT q t) := Fintype.ofFinite _
local instance pointDecidableEq : DecidableEq (PointT q t) := Classical.decEq _
local instance orthogonalDecidable :
    DecidableRel (@Projective.Orthogonal (ZMod q) _ (t + 1)) :=
  Classical.decRel _

/-- The two independently useful descriptions of the concrete child tree
(`TupleHistory` and `MarkedChildren`) agree. -/
theorem tupleChildren_eq_projectiveChildren :
    TupleBound.consistentChildren
        (TupleHistory.incidentPairs (q := q) (t := t))
        Projective.Orthogonal =
      MarkedChildren.projectiveChildren q t := by
  funext sigma
  ext p
  simp [TupleBound.consistentChildren, TupleHistory.incidentPairs,
    MarkedChildren.projectiveChildren, MarkedChildren.projectiveVertices,
    ProjectiveContainer.incidentPairs]

/-- At every node, the concrete child set is bounded by the size of the
projective `D*` vertex set, hence by `4*q^(2*t-1)`. -/
theorem projectiveChildren_card_le (ht : 1 ≤ t)
    (sigma : List (PointT q t × PointT q t)) :
    (MarkedChildren.projectiveChildren q t sigma).card ≤
      4 * q ^ (2 * t - 1) := by
  have hsub : MarkedChildren.projectiveChildren q t sigma ⊆
      MarkedChildren.projectiveVertices q t :=
    Finset.filter_subset _ _
  have hcard :
      (MarkedChildren.projectiveVertices q t).card =
        Fintype.card (ProjectiveDStar.Vertex q t) := by
    classical
    simpa [MarkedChildren.projectiveVertices,
      ProjectiveContainer.incidentPairs] using
      (Fintype.card_subtype
        (fun p : PointT q t × PointT q t ↦
          Projective.Orthogonal p.1 p.2)).symm
  calc
    (MarkedChildren.projectiveChildren q t sigma).card ≤
        (MarkedChildren.projectiveVertices q t).card :=
      Finset.card_le_card hsub
    _ = Fintype.card (ProjectiveDStar.Vertex q t) := hcard
    _ ≤ 4 * q ^ (2 * t - 1) :=
      ProjectiveDStar.card_vertex_le_four_mul_pow q t ht

/-- The contraction certificate and the stopping-power inequality bound all
unmarked steps on a path by the numerical absorption budget. -/
theorem projective_unmarkedCount_le (ht : 2 ≤ t) (hq : 4 ≤ q)
    (xs : List (PointT q t × PointT q t))
    (hpath : MarkedTree.IsPath
      (MarkedChildren.projectiveChildren q t) xs) :
    (MarkedTree.pathSignature (MarkedChildren.projectiveMarked q t) xs).count false ≤
      NumericAbsorption.unmarkedBudget (treeCoefficient t) q := by
  let K : ℕ := 32 * t * q
  let N : ℕ := Fintype.card (PointT q t)
  let w : ℕ := StoppingPower.stoppingDepth t q
  let cert := MarkedChildren.projectiveShrinkCertificate q t ht
  have hK : 1 ≤ K := by
    dsimp [K]
    have h32t : 1 ≤ 32 * t :=
      Nat.mul_le_mul (by norm_num : 1 ≤ 32) (by omega : 1 ≤ t)
    simpa using Nat.mul_le_mul h32t (show 1 ≤ q by omega)
  have hN : N ≤ 2 * q ^ t := by
    dsimp [N]
    simpa only [Nat.card_eq_fintype_card] using
      (Projective.point_zmod_bounds q t).2
  have hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
    intro c hc
    have hstop := StoppingPower.projective_stopping_power ht hq hc
    have hterminal : N + 1 ≤ StoppingPower.terminalBound t q + 1 :=
      Nat.add_le_add_right hN 1
    exact (Nat.mul_le_mul_left ((2 * K - 1) ^ c) hterminal).trans_lt (by
      simpa [K, StoppingPower.branchFactor] using hstop)
  have hcount := Container.unmarkedCount_le_of_certificate
    (L := Fin (t + 2)) cert hK hpow xs hpath
  calc
    (MarkedTree.pathSignature (MarkedChildren.projectiveMarked q t) xs).count false
        ≤ (t + 2) * StoppingPower.stoppingDepth t q := by
      simpa [cert, K, N, w] using hcount
    _ ≤ NumericAbsorption.unmarkedBudget (treeCoefficient t) q := by
      simp only [StoppingPower.stoppingDepth,
        NumericAbsorption.unmarkedBudget]
      simpa [treeCoefficient, totalStoppingCoefficient, Nat.mul_assoc] using
        Nat.mul_le_mul_right
          (q * ⌈Real.log (q : ℝ)⌉₊)
          (Nat.le_max_right (markedCoefficient t)
            (totalStoppingCoefficient t))

/-- The marked-tree estimate before casting and analytic absorption. -/
theorem forwardIndependentTupleCount_le_tree
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hAq : treeCoefficient t ≤ q)
    (hm : (forwardConstantNat t : ℝ) * (q : ℝ) *
      Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    @Digraph.forwardIndependentTupleCount
        (ProjectiveDStar.Vertex q t)
        (ProjectiveDStar.vertexFintype q t)
        (ProjectiveDStar.digraph q t) m ≤
      2 ^ m * (4 * q ^ (2 * t - 1)) ^
          NumericAbsorption.unmarkedBudget (treeCoefficient t) q *
        (treeCoefficient t * q ^ t) ^
          (m - NumericAbsorption.unmarkedBudget (treeCoefficient t) q) := by
  let children := MarkedChildren.projectiveChildren q t
  let marked := MarkedChildren.projectiveMarked q t
  let Delta := 4 * q ^ (2 * t - 1)
  let h := treeCoefficient t * q ^ t
  let w := NumericAbsorption.unmarkedBudget (treeCoefficient t) q
  have hchildren : ∀ sigma, (children sigma).card ≤ Delta := by
    intro sigma
    exact projectiveChildren_card_le (q := q) (t := t) (by omega) sigma
  have hmarked : ∀ sigma,
      ((children sigma).filter fun p ↦ marked sigma p = true).card ≤ h := by
    intro sigma
    calc
      ((children sigma).filter fun p ↦ marked sigma p = true).card =
          (MarkedChildrenBound.markedChildren q t sigma).card := by
        rfl
      _ ≤ 2112 * (t + 1) * q ^ t :=
        MarkedChildrenBound.markedChildren_card_le ht sigma
      _ ≤ treeCoefficient t * q ^ t :=
        Nat.mul_le_mul_right (q ^ t)
          (Nat.le_max_left (markedCoefficient t)
            (totalStoppingCoefficient t))
  have hunmarked : ∀ xs, MarkedTree.IsPath children xs → xs.length = m →
      (MarkedTree.pathSignature marked xs).count false ≤ w := by
    intro xs hpath _hlen
    exact projective_unmarkedCount_le ht hq xs hpath
  have hhDelta : h ≤ Delta := by
    have hq1 : 1 ≤ q := by omega
    calc
      treeCoefficient t * q ^ t ≤ q * q ^ t :=
        Nat.mul_le_mul_right (q ^ t) hAq
      _ = q ^ (t + 1) := by rw [pow_succ']
      _ ≤ q ^ (2 * t - 1) := by
        exact Nat.pow_le_pow_right hq1 (by omega)
      _ ≤ 4 * q ^ (2 * t - 1) := by omega
  have hwm : w ≤ m :=
    NumericAbsorption.unmarkedBudget_le (by omega)
      (treeCoefficient_pos t) hq hm
  have htree := Container.card_allPaths_le children marked
    hchildren hmarked hunmarked hhDelta hwm
  rw [TupleHistory.forwardIndependentTupleCount_eq_card_allPaths marked,
    tupleChildren_eq_projectiveChildren] 
  simpa [children, marked, Delta, h, w] using htree

/-- Real-valued form of the concrete projective forward-tuple estimate. -/
theorem forwardIndependentTupleCount_le
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hAq : treeCoefficient t ≤ q)
    (hm : (forwardConstantNat t : ℝ) * (q : ℝ) *
      Real.log (q : ℝ) ^ 2 ≤ (m : ℝ)) :
    ((@Digraph.forwardIndependentTupleCount
        (ProjectiveDStar.Vertex q t)
        (ProjectiveDStar.vertexFintype q t)
        (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
      ((forwardConstantNat t : ℝ) * (q : ℝ) ^ t) ^ m := by
  have hnat := forwardIndependentTupleCount_le_tree
    (q := q) (t := t) (m := m) ht hq hAq hm
  have hreal :
      ((@Digraph.forwardIndependentTupleCount
          (ProjectiveDStar.Vertex q t)
          (ProjectiveDStar.vertexFintype q t)
          (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
        (2 : ℝ) ^ m *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^
            NumericAbsorption.unmarkedBudget (treeCoefficient t) q *
          ((treeCoefficient t : ℝ) * (q : ℝ) ^ t) ^
            (m - NumericAbsorption.unmarkedBudget (treeCoefficient t) q) := by
    exact_mod_cast hnat
  exact hreal.trans
    (NumericAbsorption.markedTree_numeric_absorption
      (by omega) (treeCoefficient_pos t) hq hm)

/-- **Bradač's forward-independent tuple bound for projective `D*`.**

For every fixed `t ≥ 2`, all sufficiently large prime `q` and all
`m ≥ C q (log q)^2`, the number of forward-independent `m`-tuples is at
most `(C q^t)^m`. -/
theorem exists_forwardConstant (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ,
      ∀ (q m : ℕ), (hq : q.Prime) → Q ≤ q →
        C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) →
        letI : Fact q.Prime := ⟨hq⟩
        ((@Digraph.forwardIndependentTupleCount
            (ProjectiveDStar.Vertex q t)
            (ProjectiveDStar.vertexFintype q t)
            (ProjectiveDStar.digraph q t) m : ℕ) : ℝ) ≤
          (C * (q : ℝ) ^ t) ^ m := by
  refine ⟨(forwardConstantNat t : ℝ), ?_, forwardThreshold t, ?_⟩
  · exact_mod_cast forwardConstantNat_pos ht
  · intro q m hq hQ hm
    letI : Fact q.Prime := ⟨hq⟩
    have hq4 : 4 ≤ q :=
      (Nat.le_max_left 4 (treeCoefficient t)).trans hQ
    have hAq : treeCoefficient t ≤ q :=
      (Nat.le_max_right 4 (treeCoefficient t)).trans hQ
    exact forwardIndependentTupleCount_le ht hq4 hAq hm

end

end Erdos920.ForwardBound
