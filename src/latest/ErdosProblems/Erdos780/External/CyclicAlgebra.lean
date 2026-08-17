import Mathlib

open scoped BigOperators

namespace CyclicAlgebra

abbrev FreeCyclic (p : ℕ) (ι : Type*) := ι → ZMod p → ℤ

variable {p : ℕ} {ι κ : Type*}

def g [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι where
  toFun x i a := x i (a + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

def D [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι := g - AddMonoidHom.id _

def N [NeZero p] : FreeCyclic p ι →+ FreeCyclic p ι where
  toFun x i _ := ∑ a : ZMod p, x i a
  map_zero' := by ext i a; simp
  map_add' _ _ := by ext i a; simp [Finset.sum_add_distrib]

def op [NeZero p] (degree : ℕ) : FreeCyclic p ι →+ FreeCyclic p ι :=
  if Odd degree then D else N

def augmentation [NeZero p] [Fintype ι] : FreeCyclic p ι →+ ℤ where
  toFun x := ∑ i, ∑ a : ZMod p, x i a
  map_zero' := by simp
  map_add' _ _ := by simp [Finset.sum_add_distrib]

@[simp] theorem g_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    g x i a = x i (a + 1) := rfl

@[simp] theorem D_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    D x i a = x i (a + 1) - x i a := rfl

@[simp] theorem N_apply [NeZero p] (x : FreeCyclic p ι) (i : ι) (a : ZMod p) :
    N x i a = ∑ b : ZMod p, x i b := rfl

theorem D_comp_N [NeZero p] :
    (D : FreeCyclic p ι →+ FreeCyclic p ι).comp N = 0 := by
  ext x i a
  simp

theorem N_comp_D [NeZero p] :
    (N : FreeCyclic p ι →+ FreeCyclic p ι).comp D = 0 := by
  ext x i a
  simp only [AddMonoidHom.comp_apply, N_apply, D_apply, AddMonoidHom.zero_apply]
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ b : ZMod p, x i (b + 1)) = ∑ b : ZMod p, x i b := by
    exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [hshift, sub_self]
  rfl

@[simp] theorem augmentation_N [NeZero p] [Fintype ι] (x : FreeCyclic p ι) :
    augmentation (N x) = (p : ℤ) * augmentation x := by
  simp only [augmentation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, N_apply]
  simp [ZMod.card, ← Finset.mul_sum]

theorem D_eq_zero_iff [NeZero p] (x : FreeCyclic p ι) :
    D x = 0 ↔ ∀ i a, x i (a + 1) = x i a := by
  constructor
  · intro h i a
    have ha := congrFun (congrFun h i) a
    exact sub_eq_zero.mp (by simpa [D_apply] using ha)
  · intro h
    funext i a
    simp [D_apply, h]

theorem constant_of_D_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : D x = 0) :
    ∀ i a, x i a = x i 0 := by
  intro i a
  have hstep : ∀ z : ZMod p, x i (z + 1) = x i z := (D_eq_zero_iff x).mp hx i
  have hnat : ∀ n : ℕ, x i (n : ZMod p) = x i 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (hstep (n : ZMod p)).trans ih
  rw [← ZMod.natCast_zmod_val a]
  exact hnat a.val

theorem exists_N_of_D_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : D x = 0) :
    ∃ y, N y = x := by
  let y : FreeCyclic p ι := fun i a => if a = 0 then x i 0 else 0
  refine ⟨y, ?_⟩
  funext i a
  rw [N_apply, constant_of_D_eq_zero hx i a]
  simp [y]

/-- On every free cyclic orbit, a vector whose coordinate sum is zero is a cyclic
difference.  This is the second exactness direction of the two-periodic resolution. -/
theorem exists_D_of_N_eq_zero [NeZero p] {x : FreeCyclic p ι} (hx : N x = 0) :
    ∃ y, D y = x := by
  by_cases hp1 : p = 1
  · let _ : Unique (ZMod p) := hp1 ▸ inferInstance
    have hNx : N x = x := by
      funext i a
      rw [N_apply]
      calc
        (∑ b : ZMod p, x i b) = ∑ _b : ZMod p, x i a := by
          apply Finset.sum_congr rfl
          intro b _
          exact congrArg (x i) (Subsingleton.elim b a)
        _ = x i a := by simp
    have hx0 : x = 0 := by simpa [hNx] using hx
    exact ⟨0, by simp [hx0]⟩
  · have hp : 1 < p := (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne p, hp1⟩
    let _ : Fact (1 < p) := ⟨hp⟩
    let y : FreeCyclic p ι := fun i a => ∑ k ∈ Finset.range a.val, x i (k : ZMod p)
    refine ⟨y, ?_⟩
    funext i a
    rw [D_apply]
    change (∑ k ∈ Finset.range (a + 1).val, x i (k : ZMod p)) -
      (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) = x i a
    have hsum_univ : (∑ b : ZMod p, x i b) = 0 := by
      have h := congrFun (congrFun hx i) 0
      simpa [N_apply] using h
    have hsum_range : (∑ k ∈ Finset.range p, x i (k : ZMod p)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have hconvert :
          (∑ k : Fin p, x i (k.val : ZMod p)) = ∑ b : ZMod p, x i b := by
        apply Fintype.sum_equiv (ZMod.finEquiv p)
        intro k
        congr 2
        have hv : (ZMod.finEquiv p k).val = k.val := by
          cases p with
          | zero => exact (NeZero.ne 0 rfl).elim
          | succ p => rfl
        exact (congrArg (fun n : ℕ => (n : ZMod p)) hv.symm).trans
          (ZMod.natCast_zmod_val (ZMod.finEquiv p k))
      exact hconvert.trans hsum_univ
    by_cases ha : a.val + 1 < p
    · have hval : (a + 1).val = a.val + 1 := by
        have hlt : a.val + (1 : ZMod p).val < p := by
          simpa [ZMod.val_one p] using ha
        simpa [ZMod.val_one p] using ZMod.val_add_of_lt hlt
      rw [hval, Finset.sum_range_succ, ZMod.natCast_zmod_val, add_sub_cancel_left]
    · have hap : a.val + 1 = p := by
        have hva := a.val_lt
        omega
      have hval : (a + 1).val = 0 := by
        rw [ZMod.val_add, ZMod.val_one p, hap, Nat.mod_self]
      have hsum_last :
          (∑ k ∈ Finset.range a.val, x i (k : ZMod p)) + x i a = 0 := by
        rw [← ZMod.natCast_zmod_val a]
        simpa [← hap, Finset.sum_range_succ] using hsum_range
      rw [hval]
      simp only [Finset.sum_range_zero, zero_sub]
      omega

theorem op_period_two [NeZero p] (n : ℕ) :
    (op (n + 2) : FreeCyclic p ι →+ FreeCyclic p ι) = op n := by
  have hiff : Odd (n + 2) ↔ Odd n := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.odd_add_one, Nat.odd_add_one]
    simp
  by_cases hn : Odd n
  · have hn2 : Odd (n + 2) := hiff.mpr hn
    simp [op, hn, hn2]
  · have hn2 : ¬ Odd (n + 2) := fun h => hn (hiff.mp h)
    simp [op, hn, hn2]

theorem adjacent_ops_comp [NeZero p] (n : ℕ) :
    (op (n + 1) : FreeCyclic p ι →+ FreeCyclic p ι).comp (op n) = 0 := by
  rcases Nat.even_or_odd n with hn | hn
  · have hno : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
    have hs : Odd (n + 1) := hn.add_one
    simp [op, hno, hs, D_comp_N]
  · have hs : ¬ Odd (n + 1) := Nat.not_odd_iff_even.mpr hn.add_one
    simp [op, hn, hs, N_comp_D]

theorem augmentation_contradiction [NeZero p] [Fintype ι] (hp : 1 < p)
    (boundary : FreeCyclic p κ →+ FreeCyclic p ι)
    (hboundary : ∀ z, augmentation (boundary z) = 0)
    (c0 : FreeCyclic p ι) (hc0 : augmentation c0 = 1)
    (b1 : FreeCyclic p κ) (b0 : FreeCyclic p ι)
    (hdecomp : c0 = boundary b1 + N b0) : False := by
  have h : (1 : ℤ) = (p : ℤ) * augmentation b0 := by
    rw [← hc0, hdecomp, map_add, hboundary, augmentation_N, zero_add]
  have hp0 : (p : ℤ) ≠ 0 := by omega
  have hdivZ : (p : ℤ) ∣ 1 := ⟨augmentation b0, h⟩
  have hdivN : p ∣ 1 := by exact_mod_cast hdivZ
  have hle := Nat.le_of_dvd (by omega : 0 < 1) hdivN
  omega

end CyclicAlgebra
