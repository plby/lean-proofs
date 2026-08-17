import ErdosProblems.Erdos780.External.SignedSphere

namespace SignedSphere

open SourceFlags ZpTuckerScratch

noncomputable section

variable {α β : Type*}

def BoundaryTerm (l q : List α) : Prop :=
  q.Sublist l ∧ q.length + 1 = l.length

theorem boundaryBasis_supported_terms (l : List α) :
    Supported (BoundaryTerm l) (boundaryBasis l) := by
  induction l with
  | nil => exact supported_zero _
  | cons x xs ih =>
      apply supported_sub
      · exact supported_basis
          ⟨List.Sublist.cons _ (List.Sublist.refl xs), by simp⟩
      · apply supported_linearOfBasis
          (P := BoundaryTerm xs) (Q := BoundaryTerm (x :: xs))
          (fun q => basis (x :: q))
        · intro q hq
          exact supported_basis
            ⟨hq.1.cons_cons x, by simp [hq.2]⟩
        · exact ih

def ExactStrictFlag {p n : ℕ} (k : ℕ) (l : List (Vertex p n)) : Prop :=
  IsStrictFlag l ∧ l.length = k

theorem boundary_supported_exact_flags {p n k : ℕ} {c : SChain p n}
    (hc : Supported (ExactStrictFlag k) c) :
    Supported (ExactStrictFlag (k - 1)) (boundary c) := by
  apply supported_linearOfBasis
    (P := ExactStrictFlag k) (Q := ExactStrictFlag (k - 1)) boundaryBasis
  · intro l hl q hq
    have ht := boundaryBasis_supported_terms l q hq
    constructor
    · exact hl.1.sublist ht.1
    · have hlen_l : l.length = k := hl.2
      have hlen_q : q.length + 1 = l.length := ht.2
      omega
  · exact hc

theorem prismBasis_supported_length (f : α → β) (g : α → β) (l : List α) :
    Supported (fun q : List β => q.length = l.length + 1)
      (prism f g (basis l)) := by
  induction l with
  | nil => simp [prismBasis, supported_zero]
  | cons x xs ih =>
      rw [prism_basis, prismBasis_cons]
      apply supported_sub
      · exact supported_basis (by simp)
      · rw [show prismBasis f g xs = prism f g (basis xs) by simp]
        apply supported_prepend
            (P := fun q : List β => q.length = xs.length + 1)
            (Q := fun q : List β => q.length = (x :: xs).length + 1) (f x)
        · intro q hq
          simp [hq]
        · exact ih

theorem freshFill_basis_supported_length (v : α) (J : α → α) (l : List α) :
    Supported (fun q : List α => q.length = l.length + 1)
      (freshFill v J (basis l)) := by
  rw [show freshFill v J (basis l) =
      cone v J (basis l) - prism id J (basis l) by rfl]
  apply supported_sub
  · simpa [cone] using
      (supported_basis (P := fun q : List α => q.length = l.length + 1) (by simp))
  · exact prismBasis_supported_length id J l

def FreshExactFlag {p n : ℕ} (q : Fin n) (k : ℕ)
    (l : List (Vertex p n)) : Prop :=
  ExactStrictFlag k l ∧ AllFresh q l

theorem freshFill_supported_exact {p n k : ℕ} (q : Fin n) (a : ZMod p)
    {c : SChain p n} (hc : Supported (FreshExactFlag q k) c) :
    Supported (ExactStrictFlag (k + 1))
      (freshFill (unit q a) (adjoin q a) c) := by
  apply supported_linearMap
    (P := FreshExactFlag q k) (Q := ExactStrictFlag (k + 1))
    (freshFill (unit q a) (adjoin q a)) _ hc
  intro l hl out hout
  have hfill := freshFill_basis_filled q a hl.1.1 hl.2 out hout
  have hlength := freshFill_basis_supported_length
    (unit q a) (adjoin q a) l out hout
  have hlk : l.length = k := hl.1.2
  exact ⟨hfill.1, by omega⟩

theorem alternatingOp_supported
    (A B : Chain α →ₗ[ℤ] Chain α) (P : List α → Prop)
    (hA : ∀ c, Supported P c → Supported P (A c))
    (hB : ∀ c, Supported P c → Supported P (B c))
    (i : ℕ) {c : Chain α} (hc : Supported P c) :
    Supported P (alternatingOp A B i c) := by
  simp only [alternatingOp]
  split
  · exact hB c hc
  · exact hA c hc

theorem sphereChain_supported_exact
    {p n : ℕ} (A B F : SChain p n →ₗ[ℤ] SChain p n) (x0 : SChain p n)
    (hx0 : Supported (ExactStrictFlag 1) x0)
    (hA : ∀ k c, Supported (ExactStrictFlag k) c →
      Supported (ExactStrictFlag k) (A c))
    (hB : ∀ k c, Supported (ExactStrictFlag k) c →
      Supported (ExactStrictFlag k) (B c))
    (hF : ∀ k c, Supported (ExactStrictFlag k) c →
      Supported (ExactStrictFlag (k + 1)) (F c)) :
    ∀ i, Supported (ExactStrictFlag (i + 1)) (sphereChain A B F x0 i) := by
  intro i
  induction i with
  | zero => simpa [sphereChain] using hx0
  | succ i ih =>
      rw [sphereChain]
      apply hF (i + 1)
      exact alternatingOp_supported A B (ExactStrictFlag (i + 1))
        (hA (i + 1)) (hB (i + 1)) (i + 1) ih

theorem supported_and {P Q : List α → Prop} {c : Chain α}
    (hP : Supported P c) (hQ : Supported Q c) :
    Supported (fun l => P l ∧ Q l) c := by
  intro l hl
  exact ⟨hP l hl, hQ l hl⟩

theorem shiftChain_supported_exact {p n k : ℕ} (a : ZMod p) {c : SChain p n}
    (hc : Supported (ExactStrictFlag k) c) :
    Supported (ExactStrictFlag k) (shiftChain a c) := by
  apply supported_mapVertices
    (P := ExactStrictFlag k) (Q := ExactStrictFlag k)
    (NonzeroSignedVector.shift a) _ hc
  intro l hl
  constructor
  · rw [IsStrictFlag, List.pairwise_map]
    exact hl.1.imp (vertex_shift_lt a)
  · simp [hl.2]

theorem tau_supported_exact {p n k : ℕ} {c : SChain p n}
    (hc : Supported (ExactStrictFlag k) c) :
    Supported (ExactStrictFlag k) (tau c) := by
  exact supported_sub (shiftChain_supported_exact 1 hc) hc

theorem norm_supported_exact {p n k : ℕ} [NeZero p] {c : SChain p n}
    (hc : Supported (ExactStrictFlag k) c) :
    Supported (ExactStrictFlag k) (norm c) := by
  rw [norm]
  simp only [LinearMap.sum_apply]
  exact supported_sum (s := Finset.univ) (c := fun a => shiftChain a c)
    (fun a _ => shiftChain_supported_exact a hc)

theorem periodicOp_supported_exact {p n k : ℕ} [NeZero p] (i : ℕ)
    {c : SChain p n} (hc : Supported (ExactStrictFlag k) c) :
    Supported (ExactStrictFlag k) (periodicOp i c) := by
  by_cases hi : i % 2 = 1
  · rw [periodicOp, if_pos hi]
    exact tau_supported_exact hc
  · rw [periodicOp, if_neg hi]
    exact norm_supported_exact hc

/-- The concrete recursive generalized-sphere chain in degree `i` consists
only of strict flags with exactly `i+1` vertices. -/
theorem y_supported_exact {p n : ℕ} [NeZero p] {i : ℕ} (hi : i < n) :
    Supported (ExactStrictFlag (i + 1)) (y p n i) := by
  induction i with
  | zero =>
      rw [y_zero hi]
      exact supported_basis ⟨by simp [IsStrictFlag], by simp⟩
  | succ i ih =>
      rw [y_succ hi]
      apply freshFill_supported_exact ⟨i + 1, hi⟩ 0
      have hexact := periodicOp_supported_exact (i + 1) (ih (by omega))
      have hbase : Supported (GoodFlag (i + 1)) (y p n i) :=
        y_supported_good (p := p) (n := n) (i := i) (by omega)
      have hgood := periodicOp_supported (p := p) (n := n) (d := i + 1)
        (i + 1) hbase
      intro l hl
      constructor
      · exact hexact l hl
      · intro x hx
        exact (hgood l hl).2 x hx ⟨i + 1, hi⟩ (by simp)

end

end SignedSphere
