import ErdosProblems.Erdos941.RootCountingTransfer

/-! # Finite counts of squarefree quadratic-root data -/

namespace Erdos941

@[ext] theorem SquarefreeRootDatum.ext {n : ℕ} {d e : SquarefreeRootDatum n}
    (ha : d.modulus = e.modulus) (hb : d.root = e.root) : d = e := by
  cases d
  cases e
  cases ha
  cases hb
  rfl

instance boundedRootDatum_finite (n X : ℕ) :
    Finite {d : SquarefreeRootDatum n // d.modulus ≤ X} := by
  let f : {d : SquarefreeRootDatum n // d.modulus ≤ X} → Fin (X + 1) × Fin (X + 1) :=
    fun d => (⟨d.val.modulus, by omega⟩, ⟨d.val.root, by have hh := d.val.root_lt; omega⟩)
  apply Finite.of_injective f
  intro d e h
  apply Subtype.ext
  apply SquarefreeRootDatum.ext
  · exact congrArg (fun z : Fin (X + 1) × Fin (X + 1) => z.1.val) h
  · exact congrArg (fun z : Fin (X + 1) × Fin (X + 1) => z.2.val) h

noncomputable def boundedRootData (n X : ℕ) : Finset (SquarefreeRootDatum n) := by
  classical
  letI := Fintype.ofFinite {d : SquarefreeRootDatum n // d.modulus ≤ X}
  exact (Finset.univ : Finset {d : SquarefreeRootDatum n // d.modulus ≤ X}).image Subtype.val

@[simp] theorem mem_boundedRootData {n X : ℕ} {d : SquarefreeRootDatum n} :
    d ∈ boundedRootData n X ↔ d.modulus ≤ X := by
  classical
  simp only [boundedRootData, Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists,
    exists_prop, exists_eq_right]

noncomputable def squarefreeRootCount (n X : ℕ) : ℕ := (boundedRootData n X).card

noncomputable def squarefreeRootResidues (n a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range a).filter fun b => Squarefree a ∧ a.Coprime (2 * n) ∧ a ∣ b ^ 2 + n

@[simp] theorem mem_squarefreeRootResidues {n a b : ℕ} :
    b ∈ squarefreeRootResidues n a ↔
      b < a ∧ Squarefree a ∧ a.Coprime (2 * n) ∧ a ∣ b ^ 2 + n := by
  classical
  simp only [squarefreeRootResidues, Finset.mem_filter, Finset.mem_range]

theorem squarefreeRootCount_eq_sum (n X : ℕ) :
    squarefreeRootCount n X = ∑ a ∈ Finset.range (X + 1), (squarefreeRootResidues n a).card := by
  classical
  have hfiber (a : ℕ) (ha : a ∈ Finset.range (X + 1)) :
      ((boundedRootData n X).filter fun d => d.modulus = a).card =
        (squarefreeRootResidues n a).card := by
    let t := (boundedRootData n X).filter fun d => d.modulus = a
    have himage : t.image SquarefreeRootDatum.root = squarefreeRootResidues n a := by
      ext b
      simp only [Finset.mem_image, mem_squarefreeRootResidues]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have hda := (Finset.mem_filter.mp hd).2
        exact ⟨hda ▸ d.root_lt, hda ▸ d.squarefree, hda ▸ d.coprime, hda ▸ d.root_dvd⟩
      · rintro ⟨hb, hsq, hcop, hroot⟩
        let d : SquarefreeRootDatum n := ⟨a, b, by omega, hsq, hcop, hb, hroot⟩
        refine ⟨d, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨mem_boundedRootData.mpr ?_, rfl⟩
        have ha' := Finset.mem_range.mp ha
        change a ≤ X
        omega
    have hinj : Set.InjOn SquarefreeRootDatum.root (t : Set (SquarefreeRootDatum n)) := by
      intro d hd e he hroot
      apply SquarefreeRootDatum.ext _ hroot
      exact (Finset.mem_filter.mp hd).2.trans (Finset.mem_filter.mp he).2.symm
    rw [← himage, Finset.card_image_iff.mpr hinj]
  have hh : (boundedRootData n X).card =
      ∑ a ∈ Finset.range (X + 1), ((boundedRootData n X).filter fun d => d.modulus = a).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro d hd
      have hh := mem_boundedRootData.mp hd
      exact Finset.mem_range.mpr (by omega))
  exact hh.trans (Finset.sum_congr rfl hfiber)

theorem squarefreeRootCount_bound {v : Triple} {n : ℕ} (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ,
      (squarefreeRootCount n X : ℝ) ≤
        8 * (sphereCount n : ℝ) * X / Real.sqrt (n : ℝ) + K * Real.sqrt X + (sphereCount n : ℝ) := by
  obtain ⟨K, hK, hcount⟩ := squarefreeRoot_finite_count_bound hn hv hp
  refine ⟨K, hK, fun X => ?_⟩
  apply hcount X (Nat.cast_nonneg X) (boundedRootData n X)
  intro d hd
  exact_mod_cast mem_boundedRootData.mp hd

end Erdos941
