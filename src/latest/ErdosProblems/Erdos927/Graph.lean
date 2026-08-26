/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 927.
Informal proof: Joel H. Spencer, "On cliques in graphs" (1971).
Formal authors: John Jennings and Aristotle (Harmonic).
Jake Mallen replaced native evaluation with kernel-checked proofs in the selected copy.
Source: https://www.erdosproblems.com/927#post-6850
https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927
Original and selected toolchain: Lean 4.28.0.
Selected Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos927.Basic

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Spencer's Graph — Definition and Key Properties

This file defines the vertex type, edge relation, and key parameters
for Spencer's graph construction.

The graph has five types of vertices:
- `y i` : selector vertices (i < n)
- `yStar` : special selector
- `c i j` : elements of C_i (position sets)
- `cStar j` : elements of C* (recursive structure)
- `z` : root for small cliques
-/

/-! ## Key Parameters -/

/-- Auxiliary function computing the total size of C*.
  For parameter `m`, computes the total from the recursive sequence starting at `m`. -/
def spAux : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | (m + 3) =>
    let next := Nat.log 2 (m + 2) + 1
    if next ≤ 2 then 2 ^ next + next - 1 + 1
    else 2 ^ next + next - 1 + spAux next
termination_by m => m
decreasing_by
  simp_wf
  have : Nat.log 2 (m + 2) < m + 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    exact Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2)
  omega

/-- The size of C* for parameter `n`. -/
def spA (n : ℕ) : ℕ := spAux n

/-- Total vertex count. -/
def spN (n : ℕ) : ℕ := n + 1 + (2 ^ n + n - 1) + spA n + 1

/-- B = size of the largest clique. -/
def spB (n : ℕ) : ℕ := 2 ^ n + n - 1 + spA n

/-- spA n ≥ 1 for all n. -/
lemma spAux_pos : ∀ m, 1 ≤ spAux m := by
  classical
  intro m
  induction' m using Nat.strongRecOn with m ih
  match m with
  | 0 | 1 | 2 => simp [spAux]
  | m + 3 =>
    simp only [spAux]
    have hlog : Nat.log 2 (m + 2) + 1 < m + 3 := by
      have := Nat.log_lt_of_lt_pow (show m + 2 ≠ 0 by omega)
        (Nat.lt_pow_self (by norm_num : (1 : ℕ) < 2))
      omega
    split
    · have : 2 ^ (Nat.log 2 (m + 2) + 1) ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
      omega
    · have := ih _ hlog; omega

lemma spA_pos (n : ℕ) : 1 ≤ spA n := spAux_pos n

/-- Explicit evaluation of `spA 16 = 25`, used to discharge a small case in
`spencer_log`. -/
lemma spA_16_eq : spA 16 = 25 := by
  classical
  show spAux 16 = 25
  have h15 : Nat.log 2 15 = 3 := by
    rw [Nat.log_eq_iff] <;> norm_num
  have h3 : Nat.log 2 3 = 1 := by
    rw [Nat.log_eq_iff] <;> norm_num
  have h_spAux_4 : spAux 4 = 6 := by
    show spAux (1 + 3) = 6
    unfold spAux
    simp [h3]
  show spAux (13 + 3) = 25
  unfold spAux
  simp [h15, h_spAux_4]

/-- The vertex count satisfies N ≥ 2 for n ≥ 2. -/
lemma spN_ge_two (n : ℕ) (hn : n ≥ 2) : spN n ≥ 2 := by
  classical
  unfold spN; omega

/-- n ≤ spN n. -/
lemma le_spN (n : ℕ) : n ≤ spN n := by
  classical
  unfold spN; omega

/-- The waste equation: spN n = n + 4 + (spB n - 2) for n ≥ 2. -/
lemma spN_eq (n : ℕ) (hn : n ≥ 2) : spN n = n + 4 + (spB n - 2) := by
  classical
  unfold spN spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-- spB n ≥ 3 for n ≥ 2. -/
lemma spB_ge_three (n : ℕ) (hn : n ≥ 2) : spB n ≥ 3 := by
  classical
  unfold spB
  have h1 : 2 ^ n ≥ 4 := by
    calc 2 ^ n ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn
    _ = 4 := by norm_num
  have h2 := spA_pos n
  omega

/-! ## Vertex Type -/

/-- Size of C_i (0-indexed): |C_i| = 2^i + 1. -/
def cSize (i : ℕ) : ℕ := 2 ^ i + 1

/-- The vertex type for Spencer's graph. -/
inductive SpVtx (n A : ℕ) where
  | y (i : Fin n)
  | yStar
  | c (i : Fin n) (j : Fin (cSize i))
  | cStar (j : Fin A)
  | z
  deriving DecidableEq

instance SpVtx.instFintype {n A : ℕ} : Fintype (SpVtx n A) := by
  classical
  have equiv : SpVtx n A ≃
      (Fin n ⊕ Unit ⊕ (Σ i : Fin n, Fin (cSize i)) ⊕ Fin A ⊕ Unit) := {
    toFun := fun v => match v with
      | .y i => Sum.inl i
      | .yStar => Sum.inr (Sum.inl ())
      | .c i j => Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩))
      | .cStar j => Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
      | .z => Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))
    invFun := fun v => match v with
      | Sum.inl i => .y i
      | Sum.inr (Sum.inl ()) => .yStar
      | Sum.inr (Sum.inr (Sum.inl ⟨i, j⟩)) => .c i j
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) => .cStar j
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))) => .z
    left_inv := by intro v; cases v <;> simp
    right_inv := by intro v; rcases v with _ | _ | ⟨⟨_, _⟩⟩ | _ | _ <;> simp
  }
  exact Fintype.ofEquiv _ equiv.symm

/-! ## Edge Relation -/

/-- Whether y-vertex `i` is a "generic" selector (i < n/2). -/
def isGeneric (n : ℕ) (i : Fin n) : Bool := decide ((i : ℕ) < n / 2)

/-- The recursive sequence for the w/v structure.
  `recSeq n 0 = n`, subsequent values are roughly `log₂` of previous. -/
def recSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if recSeq n k ≤ 2 then 2 else Nat.log 2 (recSeq n k - 1) + 1

/-- Find (level, position) for a w-vertex given its offset from n/2. -/
def wLookup (n offset level fuel : ℕ) : Option (ℕ × ℕ) :=
  match fuel with
  | 0 => if offset = 0 then some (level, 0) else none
  | fuel + 1 =>
    let nℓ := recSeq n (level + 1)
    if offset < nℓ then some (level, offset)
    else wLookup n (offset - nℓ) (level + 1) fuel

/-- Find (position, sub-index) within a v-level. -/
def findVPos (offset pos fuel : ℕ) : ℕ × ℕ :=
  match fuel with
  | 0 => (pos, offset)
  | fuel + 1 =>
    let sz := 2 ^ pos + 1
    if offset < sz then (pos, offset)
    else findVPos (offset - sz) (pos + 1) fuel

/-- Size of v-vertices at a given level. -/
def levelVSize (n level : ℕ) : ℕ :=
  let nℓ := recSeq n (level + 1)
  2 ^ nℓ + nℓ - 1

/-- Find (level, position, sub-index) for a C*-vertex given its index. -/
def vLookup (n offset level fuel : ℕ) : ℕ × ℕ × ℕ :=
  match fuel with
  | 0 =>
    let nℓ := recSeq n (level + 1)
    let (p, q) := findVPos offset 0 nℓ
    (level, p, q)
  | fuel + 1 =>
    let lvlSz := levelVSize n level
    if offset < lvlSz then
      let nℓ := recSeq n (level + 1)
      let (p, q) := findVPos offset 0 nℓ
      (level, p, q)
    else
      vLookup n (offset - lvlSz) (level + 1) fuel

/-- Whether a non-generic y-vertex (w-vertex) `i` is adjacent to C* vertex `j`.
  This encodes the recursive w/v structure:
  w at (level, pos) is adjacent to v at (level', pos', _) iff level = level' and pos ≠ pos'. -/
def wvAdj (n : ℕ) (i : Fin n) (j : Fin (spA n)) : Bool :=
  let wOffset := (i : ℕ) - n / 2
  match wLookup n wOffset 0 n with
  | none => false
  | some (wl, wp) =>
    let (vl, vp, _) := vLookup n (j : ℕ) 0 n
    wl == vl && wp != vp

/-- Spencer's graph adjacency relation. -/
def spAdj (n : ℕ) : SpVtx n (spA n) → SpVtx n (spA n) → Prop := fun u v =>
  u ≠ v ∧ match u, v with
  -- y-y and y-yStar: all pairwise adjacent
  | .y _, .y _ | .y _, .yStar | .yStar, .y _ => True
  -- C-C, C-C*, C*-C*: all pairwise adjacent
  | .c _ _, .c _ _ | .c _ _, .cStar _ | .cStar _, .c _ _ | .cStar _, .cStar _ => True
  -- C_i ~ y_k iff k ≠ i
  | .c i _, .y k | .y k, .c i _ => k ≠ i
  -- C ~ yStar: adjacent
  | .c _ _, .yStar | .yStar, .c _ _ => True
  -- y_i ~ cStar_j: generic selectors always; w-vertices via wvAdj
  | .y i, .cStar j | .cStar j, .y i =>
    if isGeneric n i then True else wvAdj n i j = true
  -- yStar is NOT adjacent to C*
  | .yStar, .cStar _ | .cStar _, .yStar => False
  -- z ~ y_i: only if i is a w-vertex (not generic)
  | .z, .y i | .y i, .z => !(isGeneric n i)
  -- z is NOT adjacent to yStar or C
  | .z, .yStar | .yStar, .z | .z, .c _ _ | .c _ _, .z => False
  -- z IS adjacent to all C*
  | .z, .cStar _ | .cStar _, .z => True
  -- Self
  | .yStar, .yStar | .z, .z => False

/-- Spencer's adjacency is symmetric. -/
lemma spAdj_symm (n : ℕ) : Std.Symm (spAdj n) := by
  constructor
  intro u v ⟨hne, hadj⟩
  refine ⟨hne.symm, ?_⟩
  cases u <;> cases v <;> simp_all

/-- Spencer's graph as a SimpleGraph. -/
def spGraph (n : ℕ) : SimpleGraph (SpVtx n (spA n)) where
  Adj := spAdj n
  symm := spAdj_symm n
  loopless := ⟨fun v => by intro ⟨h, _⟩; exact h rfl⟩

/-! ## Key Properties -/

/-
The cardinality of the Spencer vertex type equals spN n.
-/
lemma spVtx_card (n : ℕ) :
    Fintype.card (SpVtx n (spA n)) = spN n := by
  classical
  unfold spN;
  rw [ show Fintype.card ( SpVtx n ( spA n ) ) =
      Fintype.card ( Fin n ⊕ Unit ⊕ ( Σ i : Fin n, Fin ( cSize i ) ) ⊕ Fin ( spA n ) ⊕ Unit ) by
        convert Fintype.card_congr ( Equiv.ofBijective _ ⟨ _, _ ⟩ );
        exact fun v => match v with
          | .y i => Sum.inl i | .yStar => Sum.inr ( Sum.inl () )
          | .c i j => Sum.inr ( Sum.inr ( Sum.inl ⟨ i, j ⟩ ) )
          | .cStar j => Sum.inr ( Sum.inr ( Sum.inr ( Sum.inl j ) ) )
          | .z => Sum.inr ( Sum.inr ( Sum.inr ( Sum.inr () ) ) );
        · intro v w; aesop;
        · intro x;
          rcases x with ( x | x | x | x | x ) <;> [ exact ⟨ SpVtx.y x, rfl ⟩ ;
            exact ⟨ SpVtx.yStar, rfl ⟩ ; exact ⟨ SpVtx.c x.1 x.2, rfl ⟩ ;
            exact ⟨ SpVtx.cStar x, rfl ⟩ ; exact ⟨ SpVtx.z, rfl ⟩ ] ];
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma, Fintype.card_unit]
  simp only [cSize, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hgeom : (∑ i : Fin n, 2 ^ (i : ℕ)) + 1 = 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [pow_succ]
      omega
  omega

/-
Nat.log 2 (spN n) = n for n ≥ 16.
-/
set_option maxHeartbeats 1600000 in
theorem spencer_log (n : ℕ) (hn : n ≥ 16) : Nat.log 2 (spN n) = n := by
  classical
  rw [ Nat.log_eq_iff ] <;> norm_num [ spN ];
  have h_upper : ∀ m ≥ 16, spAux m ≤ 4 * m := by
    intro m hm
    induction' m using Nat.strong_induction_on with m ih;
    rcases m with ( _ | _ | _ | m ) <;> simp +arith +decide [ * ] at hm ⊢;
    unfold spAux; simp +arith +decide [ * ];
    by_cases h₂ : Nat.log 2 (m + 2) + 1 ≥ 16;
    · have := ih ( Nat.log 2 ( m + 2 ) + 1 )
        ( by linarith [ Nat.log_lt_of_lt_pow ( by linarith ) ( show m + 2 < 2 ^ ( m + 2 ) by
                exact Nat.recOn m ( by norm_num ) fun n ihn => by
                  norm_num [ Nat.pow_succ' ] at * ;
                  linarith
              )
            ] ) h₂;
      have := Nat.pow_log_le_self 2 ( by linarith : m + 2 ≠ 0 );
      rcases k : Nat.log 2 ( m + 2 ) with
          ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;>
            simp_all +arith +decide [ Nat.pow_succ' ];
      · grind +splitImp;
      · rename_i k' hk';
        linarith [ Nat.one_le_pow k' 2 zero_lt_two, show k' ≤ 2 ^ k' by
            exact Nat.recOn k' ( by norm_num ) fun n ihn => by
              rw [ pow_succ' ] ;
              linarith [ Nat.one_le_pow n 2 zero_lt_two ]
          ];
    · interval_cases _ : Nat.log 2 ( m + 2 ) + 1 <;> simp_all +decide;
      all_goals rw [ Nat.log_eq_iff ] at * <;> norm_num at *;
      all_goals unfold spAux; simp +arith +decide at *;
      all_goals norm_num [ Nat.log_of_lt ] at *;
      any_goals omega;
      all_goals unfold spAux; simp +arith +decide at *;
      all_goals norm_num [ Nat.log_of_lt ] at * ; omega;
  rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;>
      simp +arith +decide [ Nat.pow_succ' ] at *;
  · rw [spA_16_eq]; decide;
  · linarith! [ h_upper ( n + 17 ) ( by linarith ), show 2 ^ n ≥ n + 1 from Nat.recOn n ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith ]

end Erdos927
