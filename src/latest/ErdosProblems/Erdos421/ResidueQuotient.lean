import ErdosProblems.Erdos421.ResidueCoupledBound

/-! # Parametrizing one residue class by a shorter integer interval

The quotient map lands in `Fin (N / p + 1)`. The extra endpoint is kept
explicit, so no rounding assumption is hidden in the count.
-/

namespace Erdos421

def residueQuotient (N p : ℕ) (x : Fin N) : Fin (N / p + 1) :=
  ⟨(x : ℕ) / p, Nat.lt_succ_of_le (Nat.div_le_div_right x.isLt.le)⟩

theorem integerResidueClass_mod_eq {N p : ℕ} (c : ZMod p) (x y : Fin N)
    (hx : x ∈ integerResidueClass N p c) (hy : y ∈ integerResidueClass N p c) :
    (x : ℕ) % p = (y : ℕ) % p := by
  have he : (x : ZMod p) = (y : ZMod p) := (Equiv.addRight (1 : ZMod p)).injective
    ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  exact (ZMod.natCast_eq_natCast_iff' x y p).mp he

theorem residueQuotient_injOn {N p : ℕ} (c : ZMod p) :
    Set.InjOn (residueQuotient N p) (integerResidueClass N p c) := by
  intro x hx y hy h
  have hmod := integerResidueClass_mod_eq c x y hx hy
  have hquot := congrArg Fin.val h
  change (x : ℕ) / p = (y : ℕ) / p at hquot
  apply Fin.ext
  calc
    (x : ℕ) = (x : ℕ) % p + p * ((x : ℕ) / p) := (Nat.mod_add_div _ _).symm
    _ = (y : ℕ) % p + p * ((y : ℕ) / p) := by rw [hmod, hquot]
    _ = (y : ℕ) := Nat.mod_add_div _ _

theorem residueQuotient_affine {N p : ℕ} (c : ZMod p) (b x : Fin N)
    (hb : b ∈ integerResidueClass N p c) (hx : x ∈ integerResidueClass N p c) :
    (x : ℤ) + 1 = (p : ℤ) * ((residueQuotient N p x : ℤ) + 1) +
      (((b : ℕ) % p : ℕ) : ℤ) + 1 - p := by
  have he : (x : ℤ) = (((x : ℕ) % p : ℕ) : ℤ) +
      (p : ℤ) * (((x : ℕ) / p : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div (x : ℕ) p).symm
  rw [integerResidueClass_mod_eq c x b hx hb] at he
  change (x : ℤ) + 1 = (p : ℤ) * ((((x : ℕ) / p : ℕ) : ℤ) + 1) +
    (((b : ℕ) % p : ℕ) : ℤ) + 1 - p
  linarith

theorem restrictedResidueCount_le (s k N p : ℕ) (hs : 0 < s) (hp : 0 < p) (c : ZMod p) :
    restrictedVinogradovCount (integerResidueClass N p c) s k ≤
      vinogradovCount s k (N / p + 1) := by
  classical
  by_cases hT : (integerResidueClass N p c).Nonempty
  · obtain ⟨b, hb⟩ := hT
    let a : ℤ := (((b : ℕ) % p : ℕ) : ℤ) + 1 - p
    have ha (x : Fin N) (hx : x ∈ integerResidueClass N p c) :
        (p : ℤ) * ((residueQuotient N p x : ℤ) + 1) + a = (x : ℤ) + 1 := by
      have he := residueQuotient_affine c b x hb hx
      dsimp only [a]
      linarith
    let F : (Fin s → Fin N) × (Fin s → Fin N) →
        (Fin s → Fin (N / p + 1)) × (Fin s → Fin (N / p + 1)) :=
      fun uv ↦ (fun i ↦ residueQuotient N p (uv.1 i), fun i ↦ residueQuotient N p (uv.2 i))
    unfold restrictedVinogradovCount vinogradovCount
    apply Finset.card_le_card_of_injOn F
    · intro uv huv
      obtain ⟨huvT, he⟩ := Finset.mem_filter.mp huv
      have hu := Fintype.mem_piFinset.mp (Finset.mem_product.mp huvT).1
      have hv := Fintype.mem_piFinset.mp (Finset.mem_product.mp huvT).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_eq_zero.mpr ?_⟩
      change powerSumVector k (fun i ↦ (residueQuotient N p (uv.1 i) : ℤ) + 1) =
        powerSumVector k (fun i ↦ (residueQuotient N p (uv.2 i) : ℤ) + 1)
      apply (powerSumVector_affine_eq_iff _ _ (p : ℤ) a (by exact_mod_cast hp.ne')).mp
      have huEq : (fun i ↦ (p : ℤ) * ((residueQuotient N p (uv.1 i) : ℤ) + 1) + a) =
          (fun i ↦ (uv.1 i : ℤ) + 1) := funext (fun i ↦ ha _ (hu i))
      have hvEq : (fun i ↦ (p : ℤ) * ((residueQuotient N p (uv.2 i) : ℤ) + 1) + a) =
          (fun i ↦ (uv.2 i : ℤ) + 1) := funext (fun i ↦ ha _ (hv i))
      rw [huEq, hvEq]
      exact he
    · intro uv huv xy hxy h
      have hu := Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).1
      have hv := Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).2
      have hx := Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).1
      have hy := Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).2
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      apply Prod.ext
      · funext i
        exact residueQuotient_injOn c (hu i) (hx i) (congrFun h1 i)
      · funext i
        exact residueQuotient_injOn c (hv i) (hy i) (congrFun h2 i)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hT
    let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    simp only [restrictedVinogradovCount, he, Fintype.piFinset_empty, Finset.empty_product,
      Finset.filter_empty, Finset.card_empty, Nat.zero_le]

end Erdos421
