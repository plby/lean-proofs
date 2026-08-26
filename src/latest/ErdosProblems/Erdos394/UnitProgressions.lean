import ErdosProblems.Erdos394.CyclicGap
import ErdosProblems.Erdos394.ProgressionSum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Partitioning coprime integers by unit residue classes
-/

open Nat Finset

namespace Erdos394

/-- The unit attached to a coprime natural has residue `m mod q`. -/
theorem unitResidue_unitOfCoprime {m q : ℕ} (hcop : m.Coprime q) :
    unitResidue q (ZMod.unitOfCoprime m hcop) = m % q := by
  unfold unitResidue
  rw [show ((ZMod.unitOfCoprime m hcop : (ZMod q)ˣ) : ZMod q) = (m : ZMod q) by
    exact ZMod.coe_unitOfCoprime m hcop]
  exact ZMod.val_natCast q m

/-- A unit has the same least residue as a coprime natural exactly when it is
the unit attached to that natural. -/
theorem unitResidue_eq_mod_iff_eq_unitOfCoprime {m q : ℕ} (hq : 0 < q)
    (hcop : m.Coprime q) (a : (ZMod q)ˣ) :
    unitResidue q a = m % q ↔ a = ZMod.unitOfCoprime m hcop := by
  letI : NeZero q := ⟨hq.ne'⟩
  constructor
  · intro hres
    apply Units.ext
    apply ZMod.val_injective q
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact hres
  · rintro rfl
    exact unitResidue_unitOfCoprime hcop

/-- If an integer lies in a unit residue class modulo positive `q`, then it is
coprime to `q`. -/
theorem coprime_of_mod_eq_unitResidue {m q : ℕ} (hq : 0 < q)
    (a : (ZMod q)ˣ) (hres : m % q = unitResidue q a) :
    m.Coprime q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have heq : (m : ZMod q) = (a : ZMod q) := by
    apply ZMod.val_injective q
    rw [ZMod.val_natCast]
    exact hres
  apply (ZMod.isUnit_iff_coprime m q).mp
  rw [heq]
  exact Units.isUnit a

/-- Units with prescribed residue `m mod q` form a singleton when `m` is
coprime and are empty otherwise. -/
theorem filter_units_unitResidue_eq_mod {m q : ℕ} [NeZero q] (hq : 0 < q) :
    (Finset.univ.filter (fun a : (ZMod q)ˣ ↦ unitResidue q a = m % q)) =
      if hcop : m.Coprime q then {ZMod.unitOfCoprime m hcop} else ∅ := by
  split_ifs with hcop
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact unitResidue_eq_mod_iff_eq_unitOfCoprime hq hcop a
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hres
      exact (hcop (coprime_of_mod_eq_unitResidue hq a hres.symm)).elim
    · intro ha
      simp at ha

/-- Exact weighted partition of all coprime naturals up to `M` into their unit
residue classes. -/
theorem sum_unit_residueClasses_eq_sum_coprime
    {M q : ℕ} [NeZero q] (hq : 0 < q) (F : (ZMod q)ˣ → ℕ → ℝ) :
    (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
      ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
  calc
    (∑ a : (ZMod q)ˣ,
        ∑ m ∈ residueClassUpTo M q (unitResidue q a), F a m) =
      ∑ a : (ZMod q)ˣ, ∑ m ∈ Finset.range (M + 1),
        if unitResidue q a = m % q then F a m else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          unfold residueClassUpTo
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro m hm
          by_cases h : m % q = unitResidue q a
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (Ne.symm h)]
    _ = ∑ m ∈ Finset.range (M + 1), ∑ a : (ZMod q)ˣ,
        if unitResidue q a = m % q then F a m else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range (M + 1),
        if hcop : m.Coprime q then F (ZMod.unitOfCoprime m hcop) m else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_filter]
      rw [filter_units_unitResidue_eq_mod hq]
      split_ifs with hcop
      · simp
      · simp

end Erdos394
