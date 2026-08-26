import ErdosProblems.Erdos941.AllRootCountingTransfer

/-! # Finite counts of quadratic-root data at coprime moduli -/

namespace Erdos941

@[ext] theorem RootDatum.ext {n : ℕ} {d e : RootDatum n}
    (ha : d.modulus = e.modulus) (hb : d.root = e.root) : d = e := by
  cases d
  cases e
  cases ha
  cases hb
  rfl

instance boundedAllRootDatum_finite (n X : ℕ) :
    Finite {d : RootDatum n // d.modulus ≤ X} := by
  let f : {d : RootDatum n // d.modulus ≤ X} → Fin (X + 1) × Fin (X + 1) :=
    fun d => (⟨d.val.modulus, by omega⟩, ⟨d.val.root, by have hh := d.val.root_lt; omega⟩)
  apply Finite.of_injective f
  intro d e h
  apply Subtype.ext
  apply RootDatum.ext
  · exact congrArg (fun z : Fin (X + 1) × Fin (X + 1) => z.1.val) h
  · exact congrArg (fun z : Fin (X + 1) × Fin (X + 1) => z.2.val) h

noncomputable def boundedAllRootData (n X : ℕ) : Finset (RootDatum n) := by
  classical
  letI := Fintype.ofFinite {d : RootDatum n // d.modulus ≤ X}
  exact (Finset.univ : Finset {d : RootDatum n // d.modulus ≤ X}).image Subtype.val

@[simp] theorem mem_boundedAllRootData {n X : ℕ} {d : RootDatum n} :
    d ∈ boundedAllRootData n X ↔ d.modulus ≤ X := by
  classical
  simp only [boundedAllRootData, Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists,
    exists_prop, exists_eq_right]

noncomputable def allRootCount (n X : ℕ) : ℕ := (boundedAllRootData n X).card

noncomputable def allRootResidues (n a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter fun b => a.Coprime (2 * n) ∧ a ∣ b ^ 2 + n

@[simp] theorem mem_allRootResidues {n a b : ℕ} :
    b ∈ allRootResidues n a ↔
      b < a ∧ a.Coprime (2 * n) ∧ a ∣ b ^ 2 + n := by
  classical
  simp only [allRootResidues, Finset.mem_filter, Finset.mem_range]

theorem allRootCount_eq_sum (n X : ℕ) :
    allRootCount n X = ∑ a ∈ Finset.range (X + 1), (allRootResidues n a).card := by
  classical
  have hfiber (a : ℕ) (ha : a ∈ Finset.range (X + 1)) :
      ((boundedAllRootData n X).filter fun d => d.modulus = a).card =
        (allRootResidues n a).card := by
    let t := (boundedAllRootData n X).filter fun d => d.modulus = a
    have himage : t.image RootDatum.root = allRootResidues n a := by
      ext b
      simp only [Finset.mem_image, mem_allRootResidues]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have hda := (Finset.mem_filter.mp hd).2
        exact ⟨hda ▸ d.root_lt, hda ▸ d.coprime, hda ▸ d.root_dvd⟩
      · rintro ⟨hb, hcop, hroot⟩
        let d : RootDatum n := ⟨a, b, by omega, hcop, hb, hroot⟩
        refine ⟨d, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨mem_boundedAllRootData.mpr ?_, rfl⟩
        have ha' := Finset.mem_range.mp ha
        change a ≤ X
        omega
    have hinj : Set.InjOn RootDatum.root (t : Set (RootDatum n)) := by
      intro d hd e he hroot
      apply RootDatum.ext _ hroot
      exact (Finset.mem_filter.mp hd).2.trans (Finset.mem_filter.mp he).2.symm
    rw [← himage, Finset.card_image_iff.mpr hinj]
  have hh : (boundedAllRootData n X).card =
      ∑ a ∈ Finset.range (X + 1), ((boundedAllRootData n X).filter fun d => d.modulus = a).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro d hd
      have hh := mem_boundedAllRootData.mp hd
      exact Finset.mem_range.mpr (by omega))
  exact hh.trans (Finset.sum_congr rfl hfiber)

theorem allRootCount_bound {v : Triple} {n : ℕ} (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ,
      (allRootCount n X : ℝ) ≤
        8 * (sphereCount n : ℝ) * X / Real.sqrt (n : ℝ) + K * Real.sqrt X + (sphereCount n : ℝ) := by
  obtain ⟨K, hK, hcount⟩ := allRoot_finite_count_bound hn hv hp
  refine ⟨K, hK, fun X => ?_⟩
  apply hcount X (Nat.cast_nonneg X) (boundedAllRootData n X)
  intro d hd
  exact_mod_cast mem_boundedAllRootData.mp hd

end Erdos941
