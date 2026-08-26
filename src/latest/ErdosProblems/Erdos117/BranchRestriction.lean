import ErdosProblems.Erdos117.CentralBranch
import ErdosProblems.Erdos117.NestedAnchor

/-!
# Restrictions at one branch stage

The interaction kernels have their exact index. Intersecting any selected
collection of these kernels and anchor centralizers gives the stage clique
with the required scalar credit and nonzero leading commutators.
-/

namespace Erdos117

open scoped commutatorElement BigOperators

variable {G : Type*} [Group G] {p : ℕ} {D : CentralChain G p}

namespace CentralBranch

variable (B : CentralBranch D)

def interactionHom (j k : Fin B.length) (hjk : j ≤ k) :
    B.group k →* Multiplicative (B.pairing j).rowSpace :=
  (B.pairing j).rowMonoidHom.comp (Subgroup.inclusion (B.antitone hjk))

def interactionKernel (j k : Fin B.length) (hjk : j ≤ k) : Subgroup (B.group k) :=
  (B.interactionHom j k hjk).ker

theorem interactionKernel_index [Finite G] [Fact p.Prime]
    (j k : Fin B.length) (hjk : j ≤ k) :
    (B.interactionKernel j k hjk).index = p ^ B.interactionRank j k := by
  classical
  let := Fintype.ofFinite (B.group j)
  let H := (B.group k).subgroupOf (B.group j)
  let f := (B.pairing j).rowMonoidHom
  let e : H ≃* B.group k := Subgroup.subgroupOfEquivOfLe (B.antitone hjk)
  let ψ := subgroupImageHom (p := p) f H
  have hker : ψ.ker.map e.toMonoidHom = B.interactionKernel j k hjk := by
    ext x
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [← hker]
  exact (Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective ψ.ker).trans
    (subgroupImageHom_ker_index f H)

theorem mem_interactionKernel_iff (j k : Fin B.length) (hjk : j ≤ k) (x : B.group k) :
    x ∈ B.interactionKernel j k hjk ↔
      ∀ y : B.group j, ⁅(y : G), (x : G)⁆ ∈ D.term (j + 1) := by
  let x' : B.group j := Subgroup.inclusion (B.antitone hjk) x
  constructor
  · intro hx y
    have hrow : (B.pairing j).row x' = 0 := hx
    have hz := congrArg (fun v : (B.pairing j).rowSpace => v.val y) hrow
    change (B.pairing j).toFun x' y = 0 at hz
    apply (B.pairing_zero_iff j y x').mp
    rw [← (B.pairing j).neg_swap x' y, hz, neg_zero]
  · intro hx
    change (B.pairing j).row x' = 0
    apply Subtype.ext
    funext y
    change (B.pairing j).toFun x' y = 0
    have hz := (B.pairing_zero_iff j y x').mpr (hx y)
    rw [← (B.pairing j).neg_swap y x', hz, neg_zero]

def stageRestriction (k : Fin B.length) {ι : Type*} (r : ι → Fin B.length)
    (hr : ∀ i, r i ≤ k) (a : ι → G) : Subgroup (B.group k) :=
  (⨅ i, B.interactionKernel (r i) k (hr i)) ⊓ simultaneousCentralizer (B.group k) a

theorem stageRestriction_index [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n) (k : Fin B.length)
    {ι : Type*} [Fintype ι] (r : ι → Fin B.length) (hr : ∀ i, r i ≤ k) (a : ι → G) :
    (B.stageRestriction k r hr a).index ≤ p ^
      ((∑ i, B.interactionRank (r i) k) + Fintype.card ι * Nat.clog p ((2 * n) ^ 2)) := by
  have hk : (⨅ i, B.interactionKernel (r i) k (hr i)).index ≤
      p ^ ∑ i, B.interactionRank (r i) k :=
    index_iInf_le_pow_sum _ p _ (fun i => (B.interactionKernel_index (r i) k (hr i)).le)
  have hc := simultaneousCentralizer_index_le_pow (p := p) (B.group k) a
    (centralizerIndex_le hn)
  calc
    (B.stageRestriction k r hr a).index ≤
        (⨅ i, B.interactionKernel (r i) k (hr i)).index *
          (simultaneousCentralizer (B.group k) a).index := Subgroup.index_inf_le
    _ ≤ (p ^ ∑ i, B.interactionRank (r i) k) *
        p ^ (Fintype.card ι * Nat.clog p ((2 * n) ^ 2)) := Nat.mul_le_mul hk hc
    _ = _ := (pow_add _ _ _).symm

structure StageClique (k : Fin B.length) where
  credit : ℕ
  point : Fin (credit + 1) → G
  mem_group : ∀ u, point u ∈ B.group k
  leading : ∀ u v, u ≠ v → ⁅point u, point v⁆ ∉ D.term (k + 1)

theorem exists_stage_clique [Finite G] [Fact p.Prime]
    {n : ℕ} (hn : NoncommutingBound G n) (k : Fin B.length)
    {ι : Type*} [Fintype ι] (r : ι → Fin B.length) (hr : ∀ i, r i ≤ k) (a : ι → G) :
    ∃ C : B.StageClique k,
      (∀ i u, Commute (a i) (C.point u)) ∧
      (∀ i (y : B.group (r i)) u, ⁅(y : G), C.point u⁆ ∈ D.term (r i + 1)) ∧
      scalarCreditRate p * B.halfRank k ≤ C.credit + scalarDefect p + scalarCreditRate p *
        ((∑ i, B.interactionRank (r i) k) + Fintype.card ι * Nat.clog p ((2 * n) ^ 2)) := by
  classical
  let := Fintype.ofFinite (B.group k)
  let β := B.pairing k
  let H := B.stageRestriction k r hr a
  obtain ⟨c, f, hf, hcredit⟩ := exists_restricted_scalar_family β.rowMonoidHom
    β.row_surjective β.form β.form_nondegenerate β.form_isAlt H
    (B.stageRestriction_index hn k r hr a)
  let C : B.StageClique k := {
    credit := c
    point := fun u => ((f u : B.group k) : G)
    mem_group := fun u => (f u).val.2
    leading := by
      intro u v huv hmem
      apply hf u v huv
      change β.form (β.row (f u)) (β.row (f v)) = 0
      rw [β.form_apply, β.pairing_row]
      exact (B.pairing_zero_iff k (f u) (f v)).mpr hmem }
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i u
    exact (mem_simultaneousCentralizer (B.group k) a (f u).val).mp (f u).2.2 i
  · intro i y u
    have hker := (Subgroup.mem_iInf.mp (f u).2.1) i
    exact (B.mem_interactionKernel_iff (r i) k (hr i) (f u).val).mp hker y
  · change scalarCreditRate p * B.halfRank k ≤ c + scalarDefect p + _
    rwa [B.pairing_half_dimension] at hcredit

end CentralBranch

end Erdos117
