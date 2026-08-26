import ErdosProblems.Erdos157b.PrimeTripleEnumeration
import ErdosProblems.Erdos157b.LevelRealization

/-! Every triple in the mask-selected fiber admits an exact target assignment. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open AuxiliaryModuli Polynomial PolynomialCharacters

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

theorem realize_primeTriple (τ : MaskChoice K) (k : ℕ)
    (d : ∀ i : Fin k, BlockTarget K i) (t : ∀ i : Fin k, TagField i × TagField i × TagField i)
    (hmom : ∀ i, Parabola.IsTriple ((targetMoments K d).firstMoment i)
      ((targetMoments K d).secondMoment i) (t i))
    (T : PrimeTriple K (levelDegree k))
    (hT : levelTripleResidue k k T = (unitLogEquiv K k).symm
      (fun i => (targetMoments K d).logarithm i - Masks.maskSum (t i) (τ i)))
    (z : ℕ) (hzlo : 3 ≤ z) (hzhi : z ≤ 3 * Fintype.card K ^ (3 * k)) :
    ∃ c : Fin 3 → LocalChoice K k,
      localValue K τ k (primeTripleEntry K T 0) (c 0) +
        localValue K τ k (primeTripleEntry K T 1) (c 1) +
        localValue K τ k (primeTripleEntry K T 2) (c 2) =
        levelTargetValue K d + blockPlace K 0 k * z := by
  have hlog (i : Fin k) :
      maskedLog K i (τ i) (t i).1 (primeAtLevelResidue K k (primeTripleEntry K T 0) i) +
        maskedLog K i (τ i) (t i).2.1 (primeAtLevelResidue K k (primeTripleEntry K T 1) i) +
        maskedLog K i (τ i) (t i).2.2 (primeAtLevelResidue K k (primeTripleEntry K T 2) i) =
        (d i).1.data.val := by
    have hr := levelTripleResidue_log K k T i
    rw [hT, Equiv.apply_symm_apply] at hr
    change (d i).1.data.val - Masks.maskSum (t i) (τ i) = _ at hr
    dsimp only [maskedLog, Masks.maskSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hr ⊢
    linear_combination -hr
  obtain ⟨c₁, c₂, c₃, hc⟩ := realize_levelTarget K τ k
    (primeTripleEntry K T 0) (primeTripleEntry K T 1) (primeTripleEntry K T 2)
    d t hmom hlog z hzlo hzhi
  exact ⟨![c₁, c₂, c₃], hc⟩

end Erdos157.Binary
