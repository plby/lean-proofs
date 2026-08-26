import ErdosProblems.Erdos556.PathSegments

/-!
# Nearby vertices of the same path parity

Dividing positions into bounded intervals and two parity classes gives
two close positions whenever a subset of path vertices has linear size.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_close_same_parity_indices (S : Finset ℕ) (N Q : ℕ) (hQ : 0 < Q)
    (hS : ∀ i ∈ S, i < N) (hc : 2 * (N / Q + 1) < S.card) :
    ∃ i ∈ S, ∃ j ∈ S, i < j ∧ j < i + Q ∧ i % 2 = j % 2 := by
  let f (i : ℕ) := (i / Q, i % 2)
  let T := range (N / Q + 1) ×ˢ range 2
  have hT : T.card < S.card := by simpa only [T, card_product, card_range, Nat.mul_comm] using hc
  have hf : ∀ i ∈ S, f i ∈ T := by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_, mem_range.mpr (Nat.mod_lt _ (by decide))⟩
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS i hi).le)
  obtain ⟨i, hi, j, hj, hij, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hT hf
  have hdiv : i / Q = j / Q := congrArg Prod.fst heq
  have hpar : i % 2 = j % 2 := congrArg Prod.snd heq
  have hclose : j < i + Q ∧ i < j + Q := by
    have hiq := Nat.div_add_mod i Q
    have hjq := Nat.div_add_mod j Q
    have him := Nat.mod_lt i hQ
    have hjm := Nat.mod_lt j hQ
    rw [hdiv] at hiq
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i, hi, j, hj, hij, hclose.1, hpar⟩
  · exact ⟨j, hj, i, hi, hji, hclose.2, hpar.symm⟩

theorem two_block_count_le_div (N K : ℕ) (hK : 0 < K) (hN : 4 * K ≤ N) :
    2 * (N / (4 * K) + 1) ≤ N / K := by
  have hq : 1 ≤ N / (4 * K) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hmul := Nat.div_mul_le_self N (4 * K)
  have hdiv : 4 * (N / (4 * K)) ≤ N / K := by
    apply (Nat.le_div_iff_mul_le hK).mpr
    nlinarith only [hmul]
  omega

theorem exists_close_same_parity_path_vertices {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (W : Finset V) (hW : ∀ x ∈ W, x ∈ p.support)
    (N K : ℕ) (hK : 0 < K) (hN : 4 * K ≤ N) (hpN : p.length < N)
    (hcard : N / K < W.card) :
    ∃ i j : ℕ, i < j ∧ j ≤ p.length ∧ j < i + 4 * K ∧
      i % 2 = j % 2 ∧ p.getVert i ∈ W ∧ p.getVert j ∈ W := by
  let S := W.image (fun x => p.support.idxOf x)
  have hidx (x : V) (hx : x ∈ W) : p.support.idxOf x ≤ p.length := by
    have h := List.idxOf_lt_length_of_mem (hW x hx)
    rw [Walk.length_support] at h
    omega
  have hinj : Set.InjOn (fun x => p.support.idxOf x) (W : Set V) := by
    intro x hx y hy hxy
    have h := congrArg p.getVert hxy
    simpa only [p.getVert_support_idxOf (hW x hx), p.getVert_support_idxOf (hW y hy)] using h
  have hScard : S.card = W.card := card_image_of_injOn hinj
  have hS (i : ℕ) (hi : i ∈ S) : i < N := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
    exact (hidx x hx).trans_lt hpN
  have hc : 2 * (N / (4 * K) + 1) < S.card := by
    rw [hScard]
    exact (two_block_count_le_div N K hK hN).trans_lt hcard
  obtain ⟨i, hi, j, hj, hij, hclose, hpar⟩ :=
    exists_close_same_parity_indices S N (4 * K) (by omega) hS hc
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  obtain ⟨y, hy, hyj⟩ := mem_image.mp hj
  have hix : p.getVert i = x := by rw [← hxi]; exact p.getVert_support_idxOf (hW x hx)
  have hjy : p.getVert j = y := by rw [← hyj]; exact p.getVert_support_idxOf (hW y hy)
  refine ⟨i, j, hij, ?_, hclose, hpar, hix ▸ hx, hjy ▸ hy⟩
  rw [← hyj]
  exact hidx y hy

#print axioms exists_close_same_parity_path_vertices

end Erdos556
