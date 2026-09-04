import ErdosProblems.Erdos909.CubeSeparators

open Set Topology

namespace Erdos909.LebesguePartition

open CubeSeparators

variable {X : Type*} [MetricSpace X]

/-- A relative partition of a closed set can be enlarged to an ambient
partition.  This is the metric version of Engelking's Lemma 1.2.9(2). -/
theorem exists_separator_of_relative
    {A B P R U V : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hP : IsClosed P) (hU : IsOpen U) (hV : IsOpen V)
    (hUVP : Disjoint (P ∩ U) (P ∩ V))
    (hAPU : A ∩ P ⊆ U) (hBPV : B ∩ P ⊆ V)
    (hcover : P \ R ⊆ U ∪ V)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ∃ Q : Set X,
      (∃ G H : Set X, IsOpen G ∧ IsOpen H ∧ Disjoint G H ∧
        G ∪ H = Qᶜ ∧ A ⊆ G ∧ B ⊆ H) ∧
      P ∩ Q ⊆ R := by
  let S : Set X := A ∪ (P ∩ U)
  let T : Set X := B ∪ (P ∩ V)
  have hSne : S.Nonempty := hAne.mono (subset_union_left)
  have hTne : T.Nonempty := hBne.mono (subset_union_left)
  have hSclT : Disjoint S (closure T) := by
    rw [Set.disjoint_left]
    intro x hxS hxTc
    have hxTnot : x ∉ closure T := by
      rw [mem_closure_iff_nhds]
      push Not
      rcases hxS with hxA | hxPU
      · by_cases hxP : x ∈ P
        · have hxU : x ∈ U := hAPU ⟨hxA, hxP⟩
          have hxBc : x ∈ Bᶜ := fun hxB ↦ Set.disjoint_left.1 hAB hxA hxB
          refine ⟨U ∩ Bᶜ, (hU.inter hB.isOpen_compl).mem_nhds ⟨hxU, hxBc⟩, ?_⟩
          apply Set.not_nonempty_iff_eq_empty.mp
          rintro ⟨y, ⟨⟨hyU, hyB⟩, hyT⟩⟩
          rcases hyT with hyB' | hyPV
          · exact hyB hyB'
          · exact Set.disjoint_left.1 hUVP ⟨hyPV.1, hyU⟩ hyPV
        · refine ⟨Pᶜ ∩ Bᶜ, (hP.isOpen_compl.inter hB.isOpen_compl).mem_nhds
              ⟨hxP, fun hxB ↦ Set.disjoint_left.1 hAB hxA hxB⟩, ?_⟩
          apply Set.not_nonempty_iff_eq_empty.mp
          rintro ⟨y, ⟨⟨hyP, hyB⟩, hyT⟩⟩
          rcases hyT with hyB' | hyPV
          · exact hyB hyB'
          · exact hyP hyPV.1
      · have hxBc : x ∈ Bᶜ := by
          intro hxB
          exact Set.disjoint_left.1 hUVP hxPU ⟨hxPU.1, hBPV ⟨hxB, hxPU.1⟩⟩
        refine ⟨U ∩ Bᶜ, (hU.inter hB.isOpen_compl).mem_nhds ⟨hxPU.2, hxBc⟩, ?_⟩
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨y, ⟨⟨hyU, hyB⟩, hyT⟩⟩
        rcases hyT with hyB' | hyPV
        · exact hyB hyB'
        · exact Set.disjoint_left.1 hUVP ⟨hyPV.1, hyU⟩ hyPV
    exact hxTnot hxTc
  have hTclS : Disjoint T (closure S) := by
    rw [Set.disjoint_left]
    intro x hxT hxSc
    have hxSnot : x ∉ closure S := by
      rw [mem_closure_iff_nhds]
      push Not
      rcases hxT with hxB | hxPV
      · by_cases hxP : x ∈ P
        · have hxV : x ∈ V := hBPV ⟨hxB, hxP⟩
          refine ⟨V ∩ Aᶜ, (hV.inter hA.isOpen_compl).mem_nhds ⟨hxV, ?_⟩, ?_⟩
          · exact fun hxA ↦ Set.disjoint_left.1 hAB hxA hxB
          · apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨y, ⟨⟨hyV, hyA⟩, hyS⟩⟩
            rcases hyS with hyA' | hyPU
            · exact hyA hyA'
            · exact Set.disjoint_left.1 hUVP hyPU ⟨hyPU.1, hyV⟩
        · refine ⟨Pᶜ ∩ Aᶜ, (hP.isOpen_compl.inter hA.isOpen_compl).mem_nhds
              ⟨hxP, ?_⟩, ?_⟩
          · exact fun hxA ↦ Set.disjoint_left.1 hAB hxA hxB
          · apply Set.not_nonempty_iff_eq_empty.mp
            rintro ⟨y, ⟨⟨hyP, hyA⟩, hyS⟩⟩
            rcases hyS with hyA' | hyPU
            · exact hyA hyA'
            · exact hyP hyPU.1
      · have hxAc : x ∈ Aᶜ := by
          intro hxA
          exact Set.disjoint_left.1 hUVP ⟨hxPV.1, hAPU ⟨hxA, hxPV.1⟩⟩ hxPV
        refine ⟨V ∩ Aᶜ, (hV.inter hA.isOpen_compl).mem_nhds ⟨hxPV.2, hxAc⟩, ?_⟩
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨y, ⟨⟨hyV, hyA⟩, hyS⟩⟩
        rcases hyS with hyA' | hyPU
        · exact hyA hyA'
        · exact Set.disjoint_left.1 hUVP hyPU ⟨hyPU.1, hyV⟩
    exact hxSnot hxSc
  let G : Set X := {x | Metric.infDist x S < Metric.infDist x T}
  let H : Set X := {x | Metric.infDist x T < Metric.infDist x S}
  let Q : Set X := (G ∪ H)ᶜ
  have hGo : IsOpen G := isOpen_lt (Metric.continuous_infDist_pt S) (Metric.continuous_infDist_pt T)
  have hHo : IsOpen H := isOpen_lt (Metric.continuous_infDist_pt T) (Metric.continuous_infDist_pt S)
  have hGH : Disjoint G H := by
    rw [Set.disjoint_left]
    intro x hxG hxH
    change Metric.infDist x S < Metric.infDist x T at hxG
    change Metric.infDist x T < Metric.infDist x S at hxH
    exact (lt_asymm hxG hxH)
  have hSG : S ⊆ G := by
    intro x hxS
    have hzero : Metric.infDist x S = 0 := Metric.infDist_zero_of_mem hxS
    have hpos : 0 < Metric.infDist x T :=
      (Metric.infDist_pos_iff_notMem_closure hTne).1
        (fun hx ↦ Set.disjoint_left.1 hSclT hxS hx)
    simpa [G, hzero] using hpos
  have hTH : T ⊆ H := by
    intro x hxT
    have hzero : Metric.infDist x T = 0 := Metric.infDist_zero_of_mem hxT
    have hpos : 0 < Metric.infDist x S :=
      (Metric.infDist_pos_iff_notMem_closure hSne).1
        (fun hx ↦ Set.disjoint_left.1 hTclS hxT hx)
    simpa [H, hzero] using hpos
  refine ⟨Q, ⟨G, H, hGo, hHo, hGH, ?_, ?_, ?_⟩, ?_⟩
  · change G ∪ H = (G ∪ H)ᶜᶜ
    exact (compl_compl _).symm
  · exact fun x hx ↦ hSG (Or.inl hx)
  · exact fun x hx ↦ hTH (Or.inl hx)
  · intro x hx
    by_contra hxR
    rcases hcover ⟨hx.1, hxR⟩ with hxU | hxV
    · exact hx.2 (Or.inl (hSG (Or.inr ⟨hx.1, hxU⟩)))
    · exact hx.2 (Or.inr (hTH (Or.inr ⟨hx.1, hxV⟩)))

/-- `R` is a partition between the traces of the `i`th opposite faces in
the closed subspace `P`.  The witnesses are kept as ambient-open sets, which
is the form needed in the finite-cover argument. -/
def SeparatesFacesWithin {n : ℕ} (i : Fin n)
    (P R : Set (Cube n)) : Prop :=
  ∃ U V : Set (Cube n), IsOpen U ∧ IsOpen V ∧
    Disjoint (P ∩ U) (P ∩ V) ∧ P \ R ⊆ U ∪ V ∧
    lowerFace i ∩ P ⊆ U ∧ upperFace i ∩ P ⊆ V

private theorem lowerFace_closed {n : ℕ} (i : Fin n) :
    IsClosed (lowerFace i) := by
  exact isClosed_eq
    (((continuous_apply i).comp continuous_subtype_val)) continuous_const

private theorem upperFace_closed {n : ℕ} (i : Fin n) :
    IsClosed (upperFace i) := by
  exact isClosed_eq
    (((continuous_apply i).comp continuous_subtype_val)) continuous_const

private theorem faces_disjoint {n : ℕ} (i : Fin n) :
    Disjoint (lowerFace i) (upperFace i) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  have : (0 : ℝ) = 1 := hx0.symm.trans hx1
  norm_num at this

private theorem lowerFace_ne {n : ℕ} (i : Fin n) :
    (lowerFace i).Nonempty := by
  exact ⟨⟨0, by constructor <;> simp⟩, by simp [lowerFace]⟩

private theorem upperFace_ne {n : ℕ} (i : Fin n) :
    (upperFace i).Nonempty := by
  exact ⟨⟨1, by constructor <;> simp⟩, by simp [upperFace]⟩

/-- Metric relative partitions can be lifted to partitions of the full cube
without adding points to the old closed set outside the prescribed relative
partition. -/
theorem SeparatesFacesWithin.exists_ambient_separator {n : ℕ}
    {i : Fin n} {P R : Set (Cube n)} (hP : IsClosed P)
    (h : SeparatesFacesWithin i P R) :
    ∃ Q : Set (Cube n), SeparatesFaces i Q ∧ P ∩ Q ⊆ R := by
  rcases h with ⟨U, V, hU, hV, hUV, hcover, hlo, hhi⟩
  obtain ⟨Q, ⟨G, H, hG, hH, hGH, hGHQ, hlowG, huppH⟩, hsub⟩ :=
    exists_separator_of_relative (lowerFace_closed i) (upperFace_closed i)
      (faces_disjoint i) hP hU hV hUV hlo hhi hcover
      (lowerFace_ne i) (upperFace_ne i)
  exact ⟨Q, ⟨G, H, hG, hH, hGH, hGHQ, hlowG, huppH⟩, hsub⟩

/-- Engelking's nested-partition lemma (Lemma 1.8.14), in the exact form
needed for the generalized Lebesgue covering theorem. -/
theorem nested_relative_partitions_nonempty {n : ℕ}
    (P : Fin (n + 1) → Set (Cube (n + 1)))
    (hPclosed : ∀ j, IsClosed (P j))
    (hPzero : SeparatesFaces 0 (P 0))
    (hstep : ∀ i : Fin n,
      SeparatesFacesWithin i.succ (P i.castSucc) (P i.succ)) :
    (P (Fin.last n)).Nonempty := by
  choose Q hQsep hQsub using fun i : Fin n ↦
    (hstep i).exists_ambient_separator (hPclosed i.castSucc)
  let E : Fin (n + 1) → Set (Cube (n + 1)) := Fin.cases (P 0) Q
  have hEsep : ∀ j, SeparatesFaces j (E j) := by
    intro j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [E] using hPzero
    · simpa [E] using hQsep i
  obtain ⟨x, hx⟩ :=
    iInter_separators_nonempty (poincareMiranda (n + 1)) E hEsep
  have hxE : ∀ j, x ∈ E j := Set.mem_iInter.1 hx
  have hxPnat : ∀ (k : ℕ) (hk : k < n + 1), x ∈ P ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa [E] using hxE (0 : Fin (n + 1))
    | succ k ih =>
        intro hk
        have hklt : k < n := Nat.lt_of_succ_lt_succ hk
        let i : Fin n := ⟨k, hklt⟩
        have hxprev : x ∈ P i.castSucc := by
          simpa [i] using ih (Nat.lt_trans hklt (Nat.lt_succ_self n))
        have hxQi : x ∈ Q i := by
          simpa [E] using hxE i.succ
        exact hQsub i ⟨hxprev, hxQi⟩
  have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext rfl
  exact ⟨x, by rw [← hlast]; exact hxPnat n (Nat.lt_succ_self n)⟩

/-- Engelking's generalized Lebesgue covering theorem (Theorem 1.8.16).
If a finite closed cover covers a partition between one pair of opposite
faces of an `(n+1)`-cube, and no cover member meets any pair of opposite
faces, then some point is contained in at least `n+1` cover members. -/
theorem finite_closed_cover_separator_multiplicity
    {n : ℕ} {I : Type*} [Finite I]
    (C : I → Set (Cube (n + 1))) (hCclosed : ∀ a, IsClosed (C a))
    (L : Set (Cube (n + 1))) (hLsep : SeparatesFaces 0 L)
    (hcover : L ⊆ ⋃ a, C a)
    (havoid : ∀ a i,
      ¬ ((C a ∩ lowerFace i).Nonempty ∧
         (C a ∩ upperFace i).Nonempty)) :
    ∃ x, n + 1 ≤ Nat.card {a : I // x ∈ C a} := by
  classical
  let := Fintype.ofFinite I
  let hits : I → Fin n → Prop := fun a i ↦
    (C a ∩ lowerFace i.succ).Nonempty
  let H : I → Finset (Fin n) := fun a ↦ Finset.univ.filter (hits a)
  let owner : I → Fin (n + 1) := fun a ↦
    if h : (H a).Nonempty then (H a).min' h |>.castSucc else Fin.last n
  have owner_le_of_hits (a : I) (i : Fin n) (hai : hits a i) :
      (owner a).val ≤ i.val := by
    have hiH : i ∈ H a := by simp [H, hai]
    have hH : (H a).Nonempty := ⟨i, hiH⟩
    simp only [owner, dif_pos hH]
    exact Finset.min'_le _ _ hiH
  have hits_of_owner_castSucc (a : I) (i : Fin n)
      (hai : owner a = i.castSucc) : hits a i := by
    by_cases hH : (H a).Nonempty
    · simp only [owner, dif_pos hH] at hai
      have hmin : (H a).min' hH = i := by
        apply Fin.ext
        simpa using congrArg Fin.val hai
      have hm := Finset.min'_mem (H a) hH
      rw [hmin] at hm
      simpa [H] using hm
    · simp only [owner, dif_neg hH] at hai
      have hv := congrArg Fin.val hai
      simp at hv
      omega
  let K : Fin (n + 1) → Set (Cube (n + 1)) := fun q ↦
    ⋃ a : {a : I // owner a = q}, C a
  have hKclosed (q : Fin (n + 1)) : IsClosed (K q) := by
    exact isClosed_iUnion_of_finite fun a ↦ hCclosed a
  have hLK : L ⊆ ⋃ q, K q := by
    intro x hxL
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (hcover hxL)
    exact Set.mem_iUnion.mpr
      ⟨owner a, Set.mem_iUnion.mpr ⟨⟨a, rfl⟩, hxa⟩⟩
  have hLclosed : IsClosed L := by
    rcases hLsep with ⟨U, V, hU, hV, hUV, hUVL, hlo, hhi⟩
    rw [← isOpen_compl_iff, ← hUVL]
    exact hU.union hV
  let pref : Fin (n + 1) → Set (Cube (n + 1)) := fun j ↦
    ⋂ q : {q : Fin (n + 1) // q.val < j.val}, K q
  let tail : Fin (n + 1) → Set (Cube (n + 1)) := fun j ↦
    ⋃ q : {q : Fin (n + 1) // j.val ≤ q.val}, K q
  let P : Fin (n + 1) → Set (Cube (n + 1)) := fun j ↦
    L ∩ pref j ∩ tail j
  have hpref_closed (j : Fin (n + 1)) : IsClosed (pref j) :=
    isClosed_iInter fun q ↦ hKclosed q
  have htail_closed (j : Fin (n + 1)) : IsClosed (tail j) :=
    isClosed_iUnion_of_finite fun q ↦ hKclosed q
  have hPclosed (j : Fin (n + 1)) : IsClosed (P j) := by
    simpa [P] using (hLclosed.inter (hpref_closed j)).inter (htail_closed j)
  have hPzero_eq : P 0 = L := by
    apply Set.Subset.antisymm
    · intro x hx
      exact hx.1.1
    · intro x hxL
      refine ⟨⟨hxL, Set.mem_iInter.2 (fun q ↦ ?_)⟩, ?_⟩
      · exact (Nat.not_lt_zero q.val (by simpa using q.property)).elim
      · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp (hLK hxL)
        exact Set.mem_iUnion.mpr ⟨⟨q, Nat.zero_le _⟩, hxq⟩
  have hPzero : SeparatesFaces 0 (P 0) := by
    rw [hPzero_eq]
    exact hLsep
  have hstep : ∀ i : Fin n,
      SeparatesFacesWithin i.succ (P i.castSucc) (P i.succ) := by
    intro i
    let U : Set (Cube (n + 1)) := (tail i.succ)ᶜ
    let V : Set (Cube (n + 1)) := (K i.castSucc)ᶜ
    refine ⟨U, V, (htail_closed i.succ).isOpen_compl,
      (hKclosed i.castSucc).isOpen_compl, ?_, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hxU hxV
      have hxtail : x ∈ tail i.castSucc := hxU.1.2
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxtail
      by_cases hqi : q.val = i.val
      · apply hxV.2
        have hq : (q : Fin (n + 1)) = i.castSucc := Fin.ext hqi
        simpa [hq] using hxq
      · apply hxU.2
        apply Set.mem_iUnion.mpr
        refine ⟨⟨q, ?_⟩, hxq⟩
        have hge := q.property
        change i.val ≤ q.val at hge
        change i.val + 1 ≤ q.val
        omega
    · intro x hx
      by_cases hKi : x ∈ K i.castSucc
      · by_cases htail : x ∈ tail i.succ
        · exfalso
          apply hx.2
          refine ⟨⟨hx.1.1.1, Set.mem_iInter.2 (fun q ↦ ?_)⟩, htail⟩
          by_cases hq : q.val < i.val
          · exact Set.mem_iInter.1 hx.1.1.2 ⟨q, hq⟩
          · have hqeq : (q : Fin (n + 1)) = i.castSucc := by
              apply Fin.ext
              have hlt := q.property
              change q.val < i.val + 1 at hlt
              change q.val = i.val
              omega
            simpa [hqeq] using hKi
        · exact Or.inl htail
      · exact Or.inr hKi
    · intro x hx
      apply show x ∉ tail i.succ from ?_
      intro hxtail
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxtail
      obtain ⟨a, haC⟩ := Set.mem_iUnion.mp hxq
      have hhits : hits a i := ⟨x, haC, hx.1⟩
      have hle := owner_le_of_hits a i hhits
      have howner : owner a = q := a.2
      have hv := congrArg Fin.val howner
      have hge := q.property
      change i.val + 1 ≤ q.val at hge
      omega
    · intro x hx
      apply show x ∉ K i.castSucc from ?_
      intro hxK
      obtain ⟨a, haC⟩ := Set.mem_iUnion.mp hxK
      have hhits : hits a i := hits_of_owner_castSucc a i a.2
      exact havoid a i.succ ⟨hhits, ⟨x, haC, hx.1⟩⟩
  obtain ⟨x, hxlast⟩ :=
    nested_relative_partitions_nonempty P hPclosed hPzero hstep
  have hxK : ∀ q : Fin (n + 1), x ∈ K q := by
    intro q
    by_cases hq : q.val < n
    · exact Set.mem_iInter.1 hxlast.1.2 ⟨q, hq⟩
    · have hqeq : q = Fin.last n := Fin.ext (by simp; omega)
      have htail := hxlast.2
      obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp htail
      have hre : (r : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
      simpa [hqeq, hre] using hxr
  choose pick hpickC using fun q ↦ Set.mem_iUnion.mp (hxK q)
  have hpick_inj : Function.Injective (fun q ↦ (pick q : I)) := by
    intro q r hqr
    have hqo : owner (pick q : I) = q := (pick q).2
    have hro : owner (pick r : I) = r := (pick r).2
    exact hqo.symm.trans ((congrArg owner hqr).trans hro)
  refine ⟨x, ?_⟩
  let f : Fin (n + 1) → {a : I // x ∈ C a} := fun q ↦
    ⟨(pick q : I), hpickC q⟩
  have hf : Function.Injective f := by
    intro q r h
    apply hpick_inj
    exact congrArg Subtype.val h
  simpa using Nat.card_le_card_of_injective f hf

/-- The same theorem with the cube dimension named directly. -/
theorem finite_closed_cover_separator_multiplicity_of_pos
    {m : ℕ} (hm : 0 < m) {I : Type*} [Finite I]
    (C : I → Set (Cube m)) (hCclosed : ∀ a, IsClosed (C a))
    (L : Set (Cube m)) (hLsep : SeparatesFaces ⟨0, hm⟩ L)
    (hcover : L ⊆ ⋃ a, C a)
    (havoid : ∀ a i,
      ¬ ((C a ∩ lowerFace i).Nonempty ∧
         (C a ∩ upperFace i).Nonempty)) :
    ∃ x, m ≤ Nat.card {a : I // x ∈ C a} := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simpa [Nat.succ_eq_add_one] using
    finite_closed_cover_separator_multiplicity (n := n) C hCclosed L hLsep hcover havoid

end Erdos909.LebesguePartition
