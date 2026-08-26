import ErdosProblems.Erdos421.SimpleRootTuples
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm

/-! # Counting nonsingular power-sum tuples modulo a prime power -/

namespace Erdos421

def primePowerReduction (p d : ℕ) (hd : 0 < d) : ZMod (p ^ d) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hd.ne') (ZMod p)

theorem isUnit_of_primePowerReduction_ne_zero {p d : ℕ} (hp : p.Prime) (hd : 0 < d)
    (a : ZMod (p ^ d)) (ha : primePowerReduction p d hd a ≠ 0) : IsUnit a := by
  let : NeZero (p ^ d) := ⟨pow_ne_zero d hp.ne_zero⟩
  have hred : primePowerReduction p d hd a = (a.val : ZMod p) := by
    simpa only [map_natCast] using
      (congrArg (primePowerReduction p d hd) (ZMod.natCast_zmod_val a)).symm
  rw [hred] at ha
  have hnot : ¬p ∣ a.val := by
    exact fun h ↦ ha ((ZMod.natCast_eq_zero_iff a.val p).mpr h)
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (a := a.val) hp hd).mpr hnot
  simpa only [ZMod.natCast_zmod_val] using hu

theorem primePower_tuple_perm_of_power_sums {p d n : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hn : n < p) (x y : Fin n → ZMod (p ^ d))
    (hy : Function.Injective (fun i ↦ primePowerReduction p d hd (y i)))
    (hs : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) := by
  let : Fact p.Prime := ⟨hp⟩
  apply tuple_perm_of_power_sums (primePowerReduction p d hd)
    (isUnit_of_primePowerReduction_ne_zero hp hd) x y hy
  · intro k hk hkn
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd).mpr
    exact Nat.not_dvd_of_pos_of_lt hk (hkn.trans_lt hn)
  · exact hs

open scoped Classical in
/-- Fix a tuple whose entries are distinct modulo `p`. Over `ZMod (p^d)`,
at most `n!` tuples in any finite search set have the same first `n` power
sums. The prime-power and small-integer unit inputs are proved above. -/
theorem primePower_power_sum_fiber_card_le {p d n : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hn : n < p) (S : Finset (Fin n → ZMod (p ^ d))) (y : Fin n → ZMod (p ^ d))
    (hy : Function.Injective (fun i ↦ primePowerReduction p d hd (y i))) :
    (S.filter (fun x : Fin n → ZMod (p ^ d) ↦ ∀ k : ℕ, 0 < k → k ≤ n →
      (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k)).card ≤ n.factorial := by
  classical
  let P : Finset (Fin n → ZMod (p ^ d)) :=
    Finset.univ.image (fun e : Equiv.Perm (Fin n) ↦ fun i ↦ y (e i))
  have hsub : S.filter (fun x : Fin n → ZMod (p ^ d) ↦ ∀ k : ℕ, 0 < k → k ≤ n →
      (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) ⊆ P := by
    intro x hx
    obtain ⟨e, he⟩ := primePower_tuple_perm_of_power_sums hp hd hn x y hy
      (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, (funext he).symm⟩
  calc
    _ ≤ P.card := Finset.card_le_card hsub
    _ ≤ Fintype.card (Equiv.Perm (Fin n)) := Finset.card_image_le
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

end Erdos421
