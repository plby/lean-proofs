import ErdosProblems.Erdos4.TiltedBlocks

/-! Representatives and short offsets for all blocks, including short final blocks. -/

namespace Erdos4.Tilted

def fiberRepresentative (x p n : ℕ) : ℕ := x + 1 + (n - (x + 1)) % p

def fiberOffset (x p n : ℕ) : ℕ := (n - (x + 1)) / p

theorem fiberRepresentative_bounds (x p n : ℕ) (hp : 0 < p) :
    1 ≤ fiberRepresentative x p n ∧ fiberRepresentative x p n ≤ x + p := by
  have hh := Nat.mod_lt (n - (x + 1)) hp
  unfold fiberRepresentative
  omega

theorem fiber_reconstruct {x p n : ℕ} (hxn : x < n) :
    n = fiberRepresentative x p n + p * fiberOffset x p n := by
  have hh := Nat.mod_add_div (n - (x + 1)) p
  unfold fiberRepresentative fiberOffset
  omega

theorem fiberRepresentative_eq {x p n m : ℕ} (hxn : x < n) (hxm : x < m)
    (hmod : (n : ZMod p) = (m : ZMod p)) :
    fiberRepresentative x p n = fiberRepresentative x p m := by
  have hh : ((n - (x + 1) : ℕ) : ZMod p) = ((m - (x + 1) : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (show x + 1 ≤ n by omega), Nat.cast_sub (show x + 1 ≤ m by omega), hmod]
  have hrem := (ZMod.natCast_eq_natCast_iff' (n - (x + 1)) (m - (x + 1)) p).mp hh
  unfold fiberRepresentative
  rw [hrem]

theorem fiberOffset_lt {x p n Y U : ℕ} (hp : 0 < p) (hnY : n ≤ Y) (hYU : Y < p * U) :
    fiberOffset x p n < U := by
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  have hh : n - (x + 1) < p * U := (Nat.sub_le _ _).trans_lt (hnY.trans_lt hYU)
  simpa only [Nat.mul_comm] using hh

theorem exists_partition_offsets {C : Finset ℕ} (P : Finpartition C) (x p Y U : ℕ)
    (hp : 0 < p) (hC : ∀ n ∈ C, x < n ∧ n ≤ Y) (hYU : Y < p * U)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) :
    ∃ (representative : P.parts → ℕ) (offset : ∀ E : P.parts, E.val → Fin U),
      (∀ E, 1 ≤ representative E ∧ representative E ≤ x + p) ∧
      (∀ (E : P.parts) (n : E.val), n.val = representative E + p * (offset E n).val) := by
  classical
  choose anchor hanchor using fun E : P.parts => P.nonempty_of_mem_parts E.property
  let representative := fun E : P.parts => fiberRepresentative x p (anchor E)
  let offset := fun (E : P.parts) (n : E.val) =>
    (⟨fiberOffset x p n.val, fiberOffset_lt hp (hC n.val (P.subset E.property n.property)).2 hYU⟩ : Fin U)
  refine ⟨representative, offset, fun E => fiberRepresentative_bounds x p (anchor E) hp, ?_⟩
  intro E n
  have hnC := hC n.val (P.subset E.property n.property)
  have haC := hC (anchor E) (P.subset E.property (hanchor E))
  have heq := fiberRepresentative_eq hnC.1 haC.1 (hfiber E.val E.property n.val n.property (anchor E) (hanchor E))
  change n.val = fiberRepresentative x p (anchor E) + p * fiberOffset x p n.val
  rw [← heq]
  exact fiber_reconstruct hnC.1

end Erdos4.Tilted
