import ErdosProblems.Erdos157.GoodFibers
import ErdosProblems.Erdos157.ResidueLogs
import ErdosProblems.Erdos157.FiniteDensity

/-! The good-residue estimate in independent logarithmic coordinates. -/

namespace Erdos157.Elementary

open AuxiliaryModuli Polynomial FiniteFiberCounts

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

abbrev LogVector (k : ℕ) := ∀ i : Fin k, LogDigit K i

noncomputable def unitLogEquiv (k : ℕ) :
    (AdjoinRoot (product K k))ˣ ≃ LogVector K k :=
  (quotientUnitsEquiv K k).toEquiv.trans (Equiv.piCongrRight (fun _ => CyclicLog.equiv))

def logPrefix {h k : ℕ} (hhk : h ≤ k) (v : LogVector K k) : LogVector K h :=
  fun i => v ⟨i.1, lt_of_lt_of_le i.2 hhk⟩

theorem logPrefix_unitLogEquiv {h k : ℕ} (hhk : h ≤ k)
    (v : (AdjoinRoot (product K k))ˣ) :
    logPrefix K hhk (unitLogEquiv K k v) =
      unitLogEquiv K h (quotientProjection K hhk v) := by
  funext i
  change CyclicLog.log (quotientUnitsEquiv K k v ⟨i.1, lt_of_lt_of_le i.2 hhk⟩) =
    CyclicLog.log (quotientUnitsEquiv K h (quotientProjection K hhk v) i)
  rw [quotientProjection_coordinates]
  rfl

abbrev HighIndex (h k : ℕ) := {i : Fin k // ¬i.1 < h}
abbrev HighLogVector (h k : ℕ) := ∀ i : HighIndex h k, LogDigit K i.1

def joinLogVectors {h k : ℕ} (hhk : h ≤ k)
    (u : LogVector K h) (v : HighLogVector K h k) : LogVector K k :=
  fun i => if hi : i.1 < h then u ⟨i.1, hi⟩ else v ⟨i, hi⟩

theorem logPrefix_join {h k : ℕ} (hhk : h ≤ k)
    (u : LogVector K h) (v : HighLogVector K h k) :
    logPrefix K hhk (joinLogVectors K hhk u v) = u := by
  funext i
  simp only [logPrefix, joinLogVectors, dif_pos i.2]

noncomputable def logExtensionEquiv {h k : ℕ} (hhk : h ≤ k)
    (u : (AdjoinRoot (product K h))ˣ) :
    HighLogVector K h k ≃ {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = u} where
  toFun w := ⟨(unitLogEquiv K k).symm (joinLogVectors K hhk (unitLogEquiv K h u) w), by
    apply (unitLogEquiv K h).injective
    rw [← logPrefix_unitLogEquiv, Equiv.apply_symm_apply, logPrefix_join]⟩
  invFun v i := unitLogEquiv K k v.1 i.1
  left_inv w := by
    funext i
    simp only [Equiv.apply_symm_apply, joinLogVectors, dif_neg i.2]
  right_inv v := by
    apply Subtype.ext
    apply (unitLogEquiv K k).injective
    rw [Equiv.apply_symm_apply]
    funext i
    dsimp only [joinLogVectors]
    split_ifs with hi
    · have hp := congrFun (logPrefix_unitLogEquiv K hhk v.1) ⟨i.1, hi⟩
      rw [v.2] at hp
      exact hp.symm
    · rfl

noncomputable def GoodLogVector (k : ℕ) (v : LogVector K k) : Prop :=
  GoodResidue k ((unitLogEquiv K k).symm v)

theorem good_log_extensions_density {h k : ℕ} (hhk : h ≤ k)
    (hg : ∀ u : (AdjoinRoot (product K h))ˣ,
      (fiberCard (quotientProjection K hhk) u : ℝ) / (1024 * (levelDegree k : ℝ) ^ 3) ≤
        Nat.card {v : {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = u} //
          GoodResidue k v.1}) (u : LogVector K h) :
    1 / (1024 * (levelDegree k : ℝ) ^ 3) ≤
      finiteDensity (fun v => GoodLogVector K k (joinLogVectors K hhk u v)) := by
  let r := (unitLogEquiv K h).symm u
  let e := logExtensionEquiv K hhk r
  have hp : finiteDensity (fun v => GoodLogVector K k (joinLogVectors K hhk u v)) =
      finiteDensity (fun v : {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = r} =>
        GoodResidue k v.1) := by
    rw [← finiteDensity_equiv e]
    apply finiteDensity_congr
    intro v
    change GoodResidue k ((unitLogEquiv K k).symm (joinLogVectors K hhk u v)) ↔
      GoodResidue k ((unitLogEquiv K k).symm
        (joinLogVectors K hhk ((unitLogEquiv K h) ((unitLogEquiv K h).symm u)) v))
    rw [Equiv.apply_symm_apply]
  rw [hp]
  have hc : (0 : ℝ) < fiberCard (quotientProjection K hhk) r := by
    have hn : 0 < Nat.card {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = r} := by
      let ⟨v, hv⟩ := quotientProjection_surjective K hhk r
      letI : Nonempty {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = r} := ⟨⟨v, hv⟩⟩
      exact Nat.card_pos
    exact_mod_cast hn
  unfold finiteDensity
  change _ ≤ _ / (fiberCard (quotientProjection K hhk) r : ℝ)
  apply (le_div_iff₀ hc).mpr
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hg r

end Erdos157.Elementary
