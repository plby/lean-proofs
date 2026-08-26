import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Every interval of diameter `G` contains at least `G/P-2` disjoint full
copies of each good residue of a predicate with positive period `P`. -/
theorem periodic_interval_count_lower
    (f : ℕ → Prop) [DecidablePred f] (P L G : ℕ) (hP : 0 < P)
    (hf : Function.Periodic f P) :
    (G / P - 2) * ((Finset.range P).filter f).card ≤
      ((Finset.Icc L (L + G)).filter f).card := by
  let S := (Finset.range P).filter f
  let q := G / P - 2
  let D := S ×ˢ Finset.range q
  let F : (ℕ × ℕ) → ℕ := fun z => (L / P + 1 + z.2) * P + z.1
  have hmap : Set.MapsTo F (D : Set (ℕ × ℕ))
      (((Finset.Icc L (L + G)).filter f : Finset ℕ) : Set ℕ) := by
    intro z hz
    have hzD : z ∈ D := hz
    have hzS : z.1 ∈ S := (Finset.mem_product.mp hzD).1
    have hzq : z.2 < q := Finset.mem_range.mp (Finset.mem_product.mp hzD).2
    have hzr : z.1 < P := Finset.mem_range.mp (Finset.mem_filter.mp hzS).1
    have hzf : f z.1 := (Finset.mem_filter.mp hzS).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have hLlt : L < (L / P + 1) * P := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ L hP
      have hblock : (L / P + 1) * P ≤ (L / P + 1 + z.2) * P :=
        Nat.mul_le_mul_right P (Nat.le_add_right _ _)
      dsimp [F]
      omega
    · have hj : z.2 + 2 ≤ G / P := by omega
      have hmul : (z.2 + 2) * P ≤ G :=
        (Nat.mul_le_mul_right P hj).trans (Nat.div_mul_le_self G P)
      have hbase : (L / P) * P ≤ L := Nat.div_mul_le_self L P
      have hrlt : z.1 < P := hzr
      dsimp [F]
      nlinarith
    · have hper := hf.nat_mul (L / P + 1 + z.2) z.1
      simp only [Nat.cast_id] at hper
      dsimp [F]
      rw [Nat.add_comm]
      exact hper.mpr hzf
  have hinj : Set.InjOn F (D : Set (ℕ × ℕ)) := by
    intro z hz w hw hEq
    have hzD : z ∈ D := hz
    have hwD : w ∈ D := hw
    have hzr : z.1 < P := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hzD).1).1
    have hwr : w.1 < P := Finset.mem_range.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hwD).1).1
    have hrem := congrArg (fun n => n % P) hEq
    have hzrem : F z % P = z.1 := by
      dsimp [F]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hzr]
    have hwrem : F w % P = w.1 := by
      dsimp [F]
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hwr]
    rw [hzrem, hwrem] at hrem
    have hfirst : z.1 = w.1 := hrem
    have hmul : (L / P + 1 + z.2) * P =
        (L / P + 1 + w.2) * P := by
      dsimp [F] at hEq
      omega
    have hblock : L / P + 1 + z.2 = L / P + 1 + w.2 :=
      Nat.eq_of_mul_eq_mul_right hP hmul
    apply Prod.ext hfirst
    omega
  have hcard := Finset.card_le_card_of_injOn F hmap hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  simpa [S, q, D, Nat.mul_comm] using hcard

end Erdos489
