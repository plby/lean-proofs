import ErdosProblems.Erdos117.CentralSeries
import ErdosProblems.Erdos117.CoverTree

/-!
# Central-factor recursion in a fixed ambient group

The central chain is fixed throughout the recursion. At each node only the
subgroup being covered changes, so different levels can subsequently be
compared inside the same ambient group.
-/

namespace Erdos117

open scoped commutatorElement

variable {G : Type*} [Group G] {p : ℕ}

def subgroupCommutatorValue (A N : Subgroup G) (hD : ⁅A, A⁆ ≤ N) (x y : A) : N :=
  ⟨⁅(x : G), (y : G)⁆, hD (Subgroup.commutator_mem_commutator x.2 y.2)⟩

theorem subgroupCommutatorValue_mul_left (A N : Subgroup G) (hD : ⁅A, A⁆ ≤ N)
    (hN : N ≤ Subgroup.center G) (x y z : A) :
    subgroupCommutatorValue A N hD (x * y) z =
      subgroupCommutatorValue A N hD x z * subgroupCommutatorValue A N hD y z := by
  have hc (a b : A) (c : G) : c * ⁅(a : G), (b : G)⁆ = ⁅(a : G), (b : G)⁆ * c :=
    Subgroup.mem_center_iff.mp (hN (subgroupCommutatorValue A N hD a b).2) c
  apply Subtype.ext
  change ⁅(x : G) * y, (z : G)⁆ = ⁅(x : G), (z : G)⁆ * ⁅(y : G), (z : G)⁆
  rw [commutatorElement_mul_left_eq_conj_mul, hc y z x, mul_inv_cancel_right]
  exact (hc y z ⁅(x : G), (z : G)⁆).symm

theorem subgroupCommutatorValue_mul_right (A N : Subgroup G) (hD : ⁅A, A⁆ ≤ N)
    (hN : N ≤ Subgroup.center G) (x y z : A) :
    subgroupCommutatorValue A N hD x (y * z) =
      subgroupCommutatorValue A N hD x y * subgroupCommutatorValue A N hD x z := by
  have hc : (y : G) * ⁅(x : G), (z : G)⁆ = ⁅(x : G), (z : G)⁆ * y :=
    Subgroup.mem_center_iff.mp (hN (subgroupCommutatorValue A N hD x z).2) y
  apply Subtype.ext
  change ⁅(x : G), (y : G) * z⁆ = ⁅(x : G), (y : G)⁆ * ⁅(x : G), (z : G)⁆
  calc
    ⁅(x : G), (y : G) * z⁆ = ⁅(x : G), (y : G)⁆ *
        ((y : G) * ⁅(x : G), (z : G)⁆ * (y : G)⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    _ = ⁅(x : G), (y : G)⁆ * ⁅(x : G), (z : G)⁆ := by
      rw [hc, mul_inv_cancel_right]

def subgroupCentralBicharacter (A N : Subgroup G) (hD : ⁅A, A⁆ ≤ N)
    (hN : N ≤ Subgroup.center G) (χ : N →* Multiplicative (ZMod p)) :
    AlternatingBicharacter A p where
  toFun x y := (χ (subgroupCommutatorValue A N hD x y)).toAdd
  mul_left x y z := by rw [subgroupCommutatorValue_mul_left A N hD hN, map_mul]; rfl
  mul_right x y z := by rw [subgroupCommutatorValue_mul_right A N hD hN, map_mul]; rfl
  self x := by
    have h : subgroupCommutatorValue A N hD x x = 1 :=
      Subtype.ext (commutatorElement_self (x : G))
    rw [h, map_one]
    rfl

theorem subgroupCentralBicharacter_zero_iff (A N K : Subgroup G) (hD : ⁅A, A⁆ ≤ N)
    (hN : N ≤ Subgroup.center G) (χ : N →* Multiplicative (ZMod p))
    (hχ : χ.ker = K.subgroupOf N) (x y : A) :
    (subgroupCentralBicharacter A N hD hN χ).toFun x y = 0 ↔
      ⁅(x : G), (y : G)⁆ ∈ K := by
  change subgroupCommutatorValue A N hD x y ∈ χ.ker ↔ _
  rw [hχ]
  rfl

/-- A node descends through one prescribed central factor, keeping both its
children and all commutators in the original ambient group. -/
theorem exists_central_descent [Finite G] [Fact p.Prime]
    (A N K : Subgroup G) (hD : ⁅A, A⁆ ≤ N) (hN : N ≤ Subgroup.center G)
    (χ : N →* Multiplicative (ZMod p)) (hχ : χ.ker = K.subgroupOf N) :
    let β := subgroupCentralBicharacter A N hD hN χ
    ∃ (m : ℕ) (C : Fin (p ^ m + 1) → Subgroup G),
      Module.finrank (ZMod p) β.rowSpace = 2 * m ∧
      (∀ i, C i ≤ A) ∧ (∀ x ∈ A, ∃ i, x ∈ C i) ∧ ∀ i, ⁅C i, C i⁆ ≤ K := by
  classical
  let β := subgroupCentralBicharacter A N hD hN χ
  let := Fintype.ofFinite A
  let m := Module.finrank (ZMod p) β.rowSpace / 2
  have hdim : Module.finrank (ZMod p) β.rowSpace = 2 * m := by
    obtain ⟨a, ha⟩ := even_finrank_of_nondegenerate_alt β.form β.form_isAlt β.form_nondegenerate
    dsimp [m]
    omega
  obtain ⟨B, hcover, hzero⟩ := β.exists_subgroup_cover
  refine ⟨m, fun i => (B i).map A.subtype, hdim, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  · intro x hx
    obtain ⟨i, hi⟩ := hcover ⟨x, hx⟩
    exact ⟨i, Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro i
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact (subgroupCentralBicharacter_zero_iff A N K hD hN χ hχ a b).mp (hzero i a ha b hb)

/-- A fixed descending central chain, with characters identifying each prime
factor. All data are constructed below for finite class-two `p`-groups. -/
structure CentralChain (G : Type*) [Group G] (p : ℕ) where
  length : ℕ
  term : ℕ → Subgroup G
  central : ∀ j, term j ≤ Subgroup.center G
  last : term length = ⊥
  step_le : ∀ j < length, term (j + 1) ≤ term j
  character : (j : Fin length) → term j →* Multiplicative (ZMod p)
  character_surjective : ∀ j, Function.Surjective (character j)
  character_ker : ∀ j, (character j).ker = (term (j + 1)).subgroupOf (term j)

theorem exists_derived_central_chain [Finite G] [Fact p.Prime]
    (hP : IsPGroup p G) (hcentral : commutator G ≤ Subgroup.center G) :
    ∃ D : CentralChain G p, D.term 0 = commutator G ∧
      Nat.card (commutator G) = p ^ D.length := by
  classical
  obtain ⟨L, S, hS0, hSL, hSN, hstep, hcard⟩ := exists_central_prime_series
    (commutator G) hcentral (hP.of_injective _ (commutator G).subtype_injective)
  have hc : ∀ j, S j ≤ Subgroup.center G := fun j => (hSN j).trans hcentral
  have hchar (j : Fin L) : ∃ χ : S j →* Multiplicative (ZMod p),
      Function.Surjective χ ∧ χ.ker = (S (j + 1)).subgroupOf (S j) := by
    let : CommGroup (S j) := { (inferInstance : Group (S j)) with
      mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hc j y.2) x) }
    exact exists_character_of_prime_index _ (hstep j j.2).2
  choose χ hχ hker using hchar
  let D : CentralChain G p := {
    length := L
    term := S
    central := hc
    last := hSL
    step_le := fun j hj => (hstep j hj).1
    character := χ
    character_surjective := hχ
    character_ker := hker }
  exact ⟨D, hS0, hcard⟩

namespace CentralChain

variable (D : CentralChain G p)

/-- The node label is half the rank of the form coming from the specified
central factor, not an arbitrary branching parameter. -/
def NodeRank (j : ℕ) (A : Subgroup G) (m : ℕ) : Prop :=
  ∃ (hj : j < D.length) (hA : ⁅A, A⁆ ≤ D.term j),
    Module.finrank (ZMod p)
      (subgroupCentralBicharacter A (D.term j) hA (D.central j)
        (D.character ⟨j, hj⟩)).rowSpace = 2 * m

/-- Build the entire finite cover tree by descending the fixed central chain.
Every node retains the scalar rank needed for subsequent interaction bounds. -/
theorem exists_cover_tree [Finite G] [Fact p.Prime]
    {j L : ℕ} (hjL : j + L = D.length) (A : Subgroup G) (hA : ⁅A, A⁆ ≤ D.term j) :
    ∃ t : ScalarCoverTree G p A L, t.Satisfies D.NodeRank j := by
  classical
  induction L generalizing j A with
  | zero =>
    have hj : j = D.length := by omega
    have hcomm : IsMulCommutative A := by
      apply IsMulCommutative.of_comm
      intro x y
      apply Subtype.ext
      apply commutatorElement_eq_one_iff_mul_comm.mp
      have h := hA (Subgroup.commutator_mem_commutator x.2 y.2)
      rw [hj, D.last] at h
      exact h
    exact ⟨.leaf A hcomm, trivial⟩
  | succ L ih =>
    have hj : j < D.length := by omega
    obtain ⟨m, C, hdim, hle, hcover, hnext⟩ := exists_central_descent
      A (D.term j) (D.term (j + 1)) hA (D.central j)
      (D.character ⟨j, hj⟩) (D.character_ker ⟨j, hj⟩)
    have hchild (i : Fin (p ^ m + 1)) :
        ∃ t : ScalarCoverTree G p (C i) L, t.Satisfies D.NodeRank (j + 1) :=
      ih (by omega) (C i) (hnext i)
    choose children hchildren using hchild
    refine ⟨.node A m C hle hcover children, ?_⟩
    exact ⟨⟨hj, hA, hdim⟩, hchildren⟩

end CentralChain

/-- The central recursion and branch-cover bound, with all group-theoretic
and linear-algebraic construction inputs proved. `RankSum` and
`RankOptimization` bound the actual node ranks along these branches. -/
theorem exists_class_two_branch_cover [Finite G] [Fact p.Prime]
    (hP : IsPGroup p G) (hcentral : commutator G ≤ Subgroup.center G) :
    ∃ (D : CentralChain G p) (b : List (Subgroup G × ℕ)),
      D.term 0 = commutator G ∧ Nat.card (commutator G) = p ^ D.length ∧
      b.length = D.length ∧ Antitone (fun i : Fin b.length => (b.get i).1) ∧
      (∀ i : Fin b.length, D.NodeRank i.val (b.get i).1 (b.get i).2) ∧
      HasAbelianCover G (2 ^ D.length * p ^ (b.map Prod.snd).sum) := by
  obtain ⟨D, hD0, hcard⟩ := exists_derived_central_chain hP hcentral
  have htop : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ D.term 0 := by
    change commutator G ≤ D.term 0
    rw [hD0]
  obtain ⟨t, ht⟩ := D.exists_cover_tree (j := 0) (L := D.length) (by omega) ⊤ htop
  obtain ⟨b, hb, hcover⟩ := t.exists_branch_exponential_cover
    (Nat.le_of_lt (Fact.out : p.Prime).one_lt)
  refine ⟨D, b, hD0, hcard, t.branch_length hb, t.branch_antitone hb, ?_, ?_⟩
  · intro i
    simpa only [Nat.zero_add] using t.satisfies_branch ht hb i
  · exact hasAbelianCover_mulEquiv Subgroup.topEquiv hcover

end Erdos117
