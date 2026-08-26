import ErdosProblems.Erdos421.MixedConcentration
import ErdosProblems.Erdos421.VinogradovMoments

/-! # Mixed counts for the integer complete system and finite partitions -/

namespace Erdos421

theorem sum_comp_append {X G : Type*} [AddCommMonoid G] {r s : ℕ}
    (f : X → G) (x : Fin r → X) (y : Fin s → X) :
    (∑ i : Fin (r + s), f (Fin.append x y i)) =
      (∑ i : Fin r, f (x i)) + ∑ i : Fin s, f (y i) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

def mixedIntegerCount {r N : ℕ} (A : Finset (Fin r → Fin N)) (T : Finset (Fin N))
    (s k : ℕ) : ℕ :=
  let D := A ×ˢ Fintype.piFinset (fun _ : Fin s ↦ T)
  ((D ×ˢ D).filter (fun p ↦ vinogradovSums k (Fin.append p.1.1 p.1.2) =
    vinogradovSums k (Fin.append p.2.1 p.2.2))).card

theorem mixedCongruenceCount_eq_integer {r s k N q : ℕ} [NeZero q]
    (hq : (r + s) * (N + 1) ^ k < q) (A : Finset (Fin r → Fin N)) (T : Finset (Fin N)) :
    mixedCongruenceCount A T
      (fun x ↦ ∑ i : Fin r, vinogradovPhasePoint q k (x i))
      (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) s = mixedIntegerCount A T s k := by
  dsimp only [mixedCongruenceCount, mixedIntegerCount]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _
  rw [← sum_comp_append, ← sum_comp_append]
  exact vinogradov_residue_sums_eq_iff hq (Fin.append p.1.1 p.1.2) (Fin.append p.2.1 p.2.2)

theorem exists_mixedIntegerCount_fiber {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {r N s k : ℕ} (A : Finset (Fin r → Fin N)) (T : Finset (Fin N)) (ρ : Fin N → C)
    (hs : 0 < s) :
    ∃ c : C, mixedIntegerCount A T s k ≤
      (Fintype.card C) ^ (2 * s) * mixedIntegerCount A (T.filter (fun y ↦ ρ y = c)) s k := by
  let q := (r + s) * (N + 1) ^ k + 1
  have hqpos : 0 < q := Nat.succ_pos _
  let : NeZero q := ⟨hqpos.ne'⟩
  have hq : (r + s) * (N + 1) ^ k < q := Nat.lt_succ_self _
  obtain ⟨c, hc⟩ := exists_mixedCongruenceCount_fiber A T
    (fun x ↦ ∑ i : Fin r, vinogradovPhasePoint q k (x i))
    (vinogradovPhasePoint q k : Fin N → Fin k → ZMod q) ρ hs
  rw [mixedCongruenceCount_eq_integer hq, mixedCongruenceCount_eq_integer hq] at hc
  exact ⟨c, hc⟩

end Erdos421
