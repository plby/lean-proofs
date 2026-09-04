import ErdosProblems.Erdos4.FGKMTTranslatedEdges

/-!
The full translated tuple is encoded by `n + h i * p`; targets are encoded by `q + Y`.
Initial random-sieve conditioning uses these full tuples, not the clipped target edges.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {k : ℕ}

noncomputable def translatedSites (h : Fin k → ℕ) (p n : ℕ) : Finset ℕ :=
  Finset.univ.image (fun i => n + h i * p)

theorem mem_translatedSites (h : Fin k → ℕ) (p n q : ℕ) :
    q ∈ translatedSites h p n ↔ ∃ i : Fin k, n + h i * p = q := by
  simp only [translatedSites, Finset.mem_image, Finset.mem_univ, true_and]

theorem translatedSites_card (h : Fin k → ℕ) (hinj : Function.Injective h)
    {p : ℕ} (hp : 0 < p) (n : ℕ) : (translatedSites h p n).card = k := by
  have hf : Function.Injective (fun i : Fin k => n + h i * p) := by
    intro i j hij
    exact hinj (mul_right_cancel₀ hp.ne' (Nat.add_left_cancel hij))
  rw [translatedSites, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem translatedSites_card_le (h : Fin k → ℕ) (p n : ℕ) :
    (translatedSites h p n).card ≤ k := by
  simpa only [translatedSites, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := fun i => n + h i * p)

theorem translatedSites_subset_window (h : Fin k → ℕ) {p Y n : ℕ}
    (hshift : ∀ i, h i * p ≤ Y) (hn : n ∈ Finset.Icc 1 (2 * Y)) :
    translatedSites h p n ⊆ Finset.Icc 1 (3 * Y) := by
  intro q hq
  obtain ⟨i, rfl⟩ := (mem_translatedSites h p n q).mp hq
  have hi := hshift i
  have hh := Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem mem_translatedEdge_iff_sites (h : Fin k → ℕ) (p Y n : ℕ)
    {q : ℕ} (hq0 : 1 ≤ q) (hqY : q ≤ Y) :
    q ∈ translatedEdge h p Y n ↔ q + Y ∈ translatedSites h p n := by
  rw [mem_translatedEdge, mem_translatedSites]
  simp only [hq0, hqY, true_and, eq_comm]

theorem translatedSites_same_source_residue (h : Fin k → ℕ) {p n q q' : ℕ}
    (hq : q ∈ translatedSites h p n) (hq' : q' ∈ translatedSites h p n) :
    (q : ZMod p) = (q' : ZMod p) := by
  obtain ⟨i, rfl⟩ := (mem_translatedSites h p n q).mp hq
  obtain ⟨j, rfl⟩ := (mem_translatedSites h p n q').mp hq'
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]

theorem translatedSites_common_point_unique (h : Fin k → ℕ)
    {p p' n n' q q' : ℕ} (hp : p.Prime) (hpp : p'.Prime) (hppne : p' ≠ p)
    (hinj : Function.Injective (fun i => (h i : ZMod p)))
    (hq : q ∈ translatedSites h p n) (hq' : q' ∈ translatedSites h p n)
    (hr : q ∈ translatedSites h p' n') (hr' : q' ∈ translatedSites h p' n') : q = q' := by
  let : Fact p.Prime := ⟨hp⟩
  have hres := translatedSites_same_source_residue h hq hq'
  obtain ⟨i, hi⟩ := (mem_translatedSites h p' n' q).mp hr
  obtain ⟨j, hj⟩ := (mem_translatedSites h p' n' q').mp hr'
  have hp'0 : (p' : ZMod p) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff p' p).mp hh
    exact hppne ((Nat.prime_dvd_prime_iff_eq hp hpp).mp hd).symm
  have hmul : (h i : ZMod p) * (p' : ZMod p) = (h j : ZMod p) * (p' : ZMod p) := by
    apply add_left_cancel (a := (n' : ZMod p))
    calc
      _ = (q : ZMod p) := by
        simpa only [Nat.cast_add, Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) hi
      _ = (q' : ZMod p) := hres
      _ = _ := by
        simpa only [Nat.cast_add, Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) hj.symm
  have hij : i = j := hinj (mul_right_cancel₀ hp'0 hmul)
  rw [hij] at hi
  exact hi.symm.trans hj

end Erdos4.FGKMT
