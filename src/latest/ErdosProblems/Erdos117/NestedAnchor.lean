import ErdosProblems.Erdos117.CliqueComposition

/-!
# Nested-anchor composition

Each stage replaces the current distinguished point by a translated clique.
Earlier vertices retain a commutator that is nontrivial in their birth layer.
The resulting clique has one point plus the sum of all stage credits.
-/

namespace Erdos117

open scoped commutatorElement BigOperators

variable {G : Type*} [Group G]

def anchorPrefix (a : ℕ → G) : ℕ → G
  | 0 => 1
  | k + 1 => anchorPrefix a k * a k

theorem commute_anchorPrefix (a : ℕ → G) (x : G) (k : ℕ)
    (h : ∀ i < k, Commute x (a i)) : Commute x (anchorPrefix a k) := by
  induction k with
  | zero => exact Commute.one_right x
  | succ k ih =>
    exact (ih (fun i hi => h i (by omega))).mul_right (h k (Nat.lt_succ_self k))

theorem mul_notMem_of_notMem_of_mem (K : Subgroup G) {x y : G}
    (hx : x ∉ K) (hy : y ∈ K) : x * y ∉ K := by
  intro h
  apply hx
  simpa only [mul_inv_cancel_right] using K.mul_mem h (K.inv_mem hy)

structure LayeredCliques (G : Type*) [Group G] (N : ℕ) where
  credit : ℕ → ℕ
  point : (k : ℕ) → Fin (credit k + 1) → G
  layer : ℕ → Subgroup G
  stage : ∀ k < N, ∀ u v, u ≠ v → ⁅point k u, point k v⁆ ∉ layer k
  centralizes_anchor : ∀ i j, i < j → j < N → ∀ v,
    Commute (point i 0) (point j v)
  later_layer : ∀ i j, i < j → j < N → ∀ u v,
    ⁅point i u, point j v⁆ ∈ layer i

namespace LayeredCliques

variable {N : ℕ} (C : LayeredCliques G N)

def anchor (k : ℕ) : G := C.point k 0

theorem anchors_commute {i j : ℕ} (hi : i < N) (hj : j < N) :
    Commute (C.anchor i) (C.anchor j) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact C.centralizes_anchor i j hij hj 0
  · exact Commute.refl _
  · exact (C.centralizes_anchor j i hji hi 0).symm

theorem prefixes_commute {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    Commute (anchorPrefix C.anchor i) (anchorPrefix C.anchor j) := by
  apply commute_anchorPrefix
  intro k hk
  apply Commute.symm
  apply commute_anchorPrefix
  intro l hl
  exact C.anchors_commute (by omega) (by omega)

theorem prefix_point_commute {i j : ℕ} (hij : i ≤ j) (hj : j < N)
    (v : Fin (C.credit j + 1)) : Commute (anchorPrefix C.anchor i) (C.point j v) := by
  apply Commute.symm
  apply commute_anchorPrefix
  intro k hk
  exact (C.centralizes_anchor k j (by omega) hj v).symm

theorem point_prefix_notMem (hG : commutator G ≤ Subgroup.center G)
    {i j : ℕ} (hij : i < j) (hj : j ≤ N) (u : Fin (C.credit i + 1)) (hu : u ≠ 0) :
    ⁅C.point i u, anchorPrefix C.anchor j⁆ ∉ C.layer i := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases heq : i = j
    · subst j
      rw [anchorPrefix, commutator_mul_right_of_class_two hG,
        (C.prefix_point_commute le_rfl (by omega) u).symm.commutator_eq, one_mul]
      exact C.stage i (by omega) u 0 hu
    · have hlt : i < j := by omega
      rw [anchorPrefix, commutator_mul_right_of_class_two hG]
      exact mul_notMem_of_notMem_of_mem (C.layer i) (ih hlt (by omega))
        (C.later_layer i j hlt (by omega) u 0)

theorem vertex_later_notMem (hG : commutator G ≤ Subgroup.center G)
    {i j : ℕ} (hij : i < j) (hj : j < N)
    (u : Fin (C.credit i + 1)) (hu : u ≠ 0) (v : Fin (C.credit j + 1)) :
    ⁅anchorPrefix C.anchor i * C.point i u, anchorPrefix C.anchor j * C.point j v⁆ ∉
      C.layer i := by
  rw [commutator_mul_left_of_class_two hG, commutator_mul_right_of_class_two hG,
    commutator_mul_right_of_class_two hG,
    (C.prefixes_commute (by omega) (by omega)).commutator_eq,
    (C.prefix_point_commute (by omega) hj v).commutator_eq, one_mul, one_mul]
  exact mul_notMem_of_notMem_of_mem (C.layer i)
    (C.point_prefix_notMem hG hij (by omega) u hu) (C.later_layer i j hij hj u v)

theorem vertex_final_notMem (hG : commutator G ≤ Subgroup.center G)
    {i : ℕ} (hi : i < N) (u : Fin (C.credit i + 1)) (hu : u ≠ 0) :
    ⁅anchorPrefix C.anchor i * C.point i u, anchorPrefix C.anchor N⁆ ∉ C.layer i := by
  rw [commutator_mul_left_of_class_two hG,
    (C.prefixes_commute (by omega) le_rfl).commutator_eq, one_mul]
  exact C.point_prefix_notMem hG hi le_rfl u hu

def family : Option ((k : Fin N) × Fin (C.credit k)) → G
  | none => anchorPrefix C.anchor N
  | some ⟨k, u⟩ => anchorPrefix C.anchor k * C.point k u.succ

theorem family_noncommuting (hG : commutator G ≤ Subgroup.center G) :
    ∀ i j, i ≠ j → ¬Commute (C.family i) (C.family j) := by
  intro i j hij hc
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      simp only [family] at hc
      apply C.vertex_final_notMem hG j.1.2 j.2.succ (Fin.succ_ne_zero _)
      rw [hc.symm.commutator_eq]
      exact Subgroup.one_mem _
  | some i =>
    cases j with
    | none =>
      simp only [family] at hc
      apply C.vertex_final_notMem hG i.1.2 i.2.succ (Fin.succ_ne_zero _)
      rw [hc.commutator_eq]
      exact Subgroup.one_mem _
    | some j =>
      rcases i with ⟨i, u⟩
      rcases j with ⟨j, v⟩
      simp only [family] at hc
      rcases lt_trichotomy i j with hlt | heq | hgt
      · apply C.vertex_later_notMem hG hlt j.2 u.succ (Fin.succ_ne_zero _) v.succ
        rw [hc.commutator_eq]
        exact Subgroup.one_mem _
      · subst j
        have huv : u ≠ v := by
          intro h
          subst v
          exact hij rfl
        have hpair := hc.commutator_eq
        change ⁅anchorPrefix C.anchor i * C.point i u.succ,
          anchorPrefix C.anchor i * C.point i v.succ⁆ = 1 at hpair
        rw [commutator_same_anchor hG (C.prefix_point_commute le_rfl i.2 u.succ)
          (C.prefix_point_commute le_rfl i.2 v.succ)] at hpair
        apply C.stage i i.2 u.succ v.succ (fun h => huv (Fin.succ_injective _ h))
        rw [hpair]
        exact Subgroup.one_mem _
      · apply C.vertex_later_notMem hG hgt i.2 v.succ (Fin.succ_ne_zero _) u.succ
        rw [hc.symm.commutator_eq]
        exact Subgroup.one_mem _

theorem total_credit_le (hG : commutator G ≤ Subgroup.center G)
    {n : ℕ} (hn : NoncommutingBound G n) :
    1 + ∑ k : Fin N, C.credit k ≤ n := by
  have h := hn.card_le (C.family_noncommuting hG)
  simpa [Fintype.card_sigma, Nat.add_comm] using h

end LayeredCliques

/-- A finite indexed version of nested-anchor composition. The extension
beyond the selected index set is trivial and has no mathematical role. -/
theorem layered_credit_le_of_fin (hG : commutator G ≤ Subgroup.center G)
    {n M : ℕ} (hn : NoncommutingBound G n) (credit : Fin M → ℕ)
    (point : (k : Fin M) → Fin (credit k + 1) → G) (layer : Fin M → Subgroup G)
    (hstage : ∀ k u v, u ≠ v → ⁅point k u, point k v⁆ ∉ layer k)
    (hanchor : ∀ i j, i < j → ∀ v, Commute (point i 0) (point j v))
    (hlayer : ∀ i j, i < j → ∀ u v, ⁅point i u, point j v⁆ ∈ layer i) :
    1 + ∑ k, credit k ≤ n := by
  classical
  let S : ℕ → (c : ℕ) × (Fin (c + 1) → G) := fun k =>
    if hk : k < M then ⟨credit ⟨k, hk⟩, point ⟨k, hk⟩⟩ else ⟨0, fun _ => 1⟩
  let K : ℕ → Subgroup G := fun k => if hk : k < M then layer ⟨k, hk⟩ else ⊥
  let C : LayeredCliques G M := {
    credit := fun k => (S k).1
    point := fun k => (S k).2
    layer := K
    stage := by
      intro k hk
      rw [show S k = ⟨credit ⟨k, hk⟩, point ⟨k, hk⟩⟩ from dif_pos hk]
      simpa only [K, dif_pos hk] using hstage ⟨k, hk⟩
    centralizes_anchor := by
      intro i j hij hj
      have hi : i < M := lt_trans hij hj
      rw [show S i = ⟨credit ⟨i, hi⟩, point ⟨i, hi⟩⟩ from dif_pos hi,
        show S j = ⟨credit ⟨j, hj⟩, point ⟨j, hj⟩⟩ from dif_pos hj]
      exact hanchor ⟨i, hi⟩ ⟨j, hj⟩ hij
    later_layer := by
      intro i j hij hj
      have hi : i < M := lt_trans hij hj
      rw [show S i = ⟨credit ⟨i, hi⟩, point ⟨i, hi⟩⟩ from dif_pos hi,
        show S j = ⟨credit ⟨j, hj⟩, point ⟨j, hj⟩⟩ from dif_pos hj]
      simpa only [K, dif_pos hi] using hlayer ⟨i, hi⟩ ⟨j, hj⟩ hij }
  have h := C.total_credit_le hG hn
  change 1 + ∑ k : Fin M, (S k).1 ≤ n at h
  have hsum : (∑ k : Fin M, (S k).1) = ∑ k, credit k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [S, dif_pos k.2]
  rwa [hsum] at h

end Erdos117
