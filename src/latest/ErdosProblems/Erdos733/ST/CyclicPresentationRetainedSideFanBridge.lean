import Mathlib.GroupTheory.Perm.List
import ErdosProblems.Erdos733.ST.CyclicPresentationRetainedSideSum

open Classical
noncomputable section

-- [TABLET NODE: CyclicPresentationRetainedSideFanBridge]
lemma CyclicPresentationRetainedSideFanBridge
    (γ : PolygonalPath) (hγ : γ.source = γ.target)
    {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K) :
    let retained : Finset ℕ :=
      ((Finset.range γ.vertices.length).filter fun i =>
        if hi : i + 1 < γ.vertices.length then
          γ.vertices[i] ≠ γ.vertices[i + 1]
        else
          False)
    let start : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
      γ.vertices[i.1]'(by
        have h := i.2
        simp [retained] at h
        exact h.1)
    let stop : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
      γ.vertices[i.1 + 1]'(by
        have h := i.2
        simp [retained] at h
        exact h.2.choose)
    ∃ σ : Equiv.Perm retained,
      (∀ i : retained, start (σ i) = stop i) ∧
        retained.sum (fun i =>
          if hi : i + 1 < γ.vertices.length then
            R.vertices.attach.sum fun p =>
              Set.ncard (openSegment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                openSegment ℝ p.1 (R.successor p).1)
          else
            0) =
          ∑ i : retained, R.vertices.attach.sum fun p =>
            Set.ncard (openSegment ℝ (start i) (start (σ i)) ∩
              openSegment ℝ p.1 (R.successor p).1) := by
-- BODY
  intro retained start stop
  have hretained :
      retained =
        ((Finset.range γ.vertices.length).filter fun i =>
          if hi : i + 1 < γ.vertices.length then
            γ.vertices[i] ≠ γ.vertices[i + 1]
          else
            False) := rfl
  have hfirst_last :
      γ.vertices[0]'(List.length_pos_iff.mpr γ.vertices_nonempty) =
        γ.vertices[γ.vertices.length - 1]'(Nat.sub_lt
          (List.length_pos_iff.mpr γ.vertices_nonempty) Nat.zero_lt_one) := by
    have hpos : 0 < γ.vertices.length :=
      List.length_pos_iff.mpr γ.vertices_nonempty
    have hlast_lt : γ.vertices.length - 1 < γ.vertices.length :=
      Nat.sub_lt hpos Nat.zero_lt_one
    have hhead? : γ.vertices.head? = some (γ.vertices[0]'hpos) := by
      rw [List.head?_eq_getElem?]
      simp [hpos]
    have hsource : γ.vertices[0]'hpos = γ.source := by
      have hs := γ.source_eq_head
      rw [hhead?] at hs
      exact Option.some.inj hs
    have htarget : γ.vertices[γ.vertices.length - 1]'hlast_lt = γ.target := by
      have ht := γ.target_eq_last
      rw [List.getLast?_eq_getLast_of_ne_nil γ.vertices_nonempty] at ht
      have hget :
          γ.vertices.get ⟨γ.vertices.length - 1, hlast_lt⟩ =
            γ.vertices.getLast γ.vertices_nonempty :=
        List.get_length_sub_one hlast_lt
      rw [← hget] at ht
      exact Option.some.inj ht
    rw [hsource, htarget, hγ]
  have vertices_eq_of_no_retained :
      ∀ {m n : ℕ} (hmn : m ≤ n) (hn : n < γ.vertices.length),
        (∀ j : ℕ, m ≤ j → j < n → j ∉ retained) →
        γ.vertices[m] = γ.vertices[n] := by
    intro m n hmn hn hnone
    induction hmn with
    | refl =>
        rfl
    | @step k hmk ih =>
        have hklen : k + 1 < γ.vertices.length := by
          exact Nat.succ_le_iff.mp (Nat.succ_le_of_lt hn)
        have hknot : k ∉ retained := hnone k hmk (Nat.lt_succ_self k)
        have hkeq : γ.vertices[k] = γ.vertices[k + 1] := by
          rw [hretained] at hknot
          have hklt : k < γ.vertices.length := Nat.lt_of_succ_lt hklen
          simp [hklt, hklen] at hknot
          exact hknot
        trans γ.vertices[k]
        · exact ih (Nat.lt_of_succ_lt hn)
            (fun j hmj hjk => hnone j hmj (Nat.lt_trans hjk (Nat.lt_succ_self k)))
        · exact hkeq
  let L := retained.sort (· ≤ ·)
  let σN : Equiv.Perm ℕ := L.formPerm
  have memL_iff (j : ℕ) : j ∈ L ↔ j ∈ retained := by
    simp [L]
  have hmem_iff : ∀ i : ℕ, σN i ∈ retained ↔ i ∈ retained := by
    intro i
    change L.formPerm i ∈ retained ↔ i ∈ retained
    rw [← memL_iff (L.formPerm i), ← memL_iff i]
    exact List.formPerm_mem_iff_mem
  let σ : Equiv.Perm retained := σN.subtypePerm hmem_iff
  have raw_endpoint :
      ∀ (i : ℕ) (hi : i ∈ retained),
        γ.vertices[L.formPerm i]'(by
          have hmemL : L.formPerm i ∈ L := by
            exact List.formPerm_apply_mem_of_mem (by simpa [L] using hi)
          have hmem : L.formPerm i ∈ retained := by
            change (retained.sort (· ≤ ·)).formPerm i ∈ retained
            have hmemL' :
                (retained.sort (· ≤ ·)).formPerm i ∈ retained.sort (· ≤ ·) := by
              simpa [L] using hmemL
            exact (Finset.mem_sort (s := retained) (r := (· ≤ ·))).1 hmemL'
          have h := hmem
          simp [retained] at h
          rcases h.2 with ⟨hsucc, _⟩
          exact Nat.lt_of_succ_lt hsucc)
          =
        γ.vertices[i + 1]'(by
          have h := hi
          simp [retained] at h
          exact h.2.choose) := by
    intro i hi
    have hiL : i ∈ L := by
      simpa [L] using hi
    obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hiL
    have hLnodup : L.Nodup := by
      simp [L]
    have hLsorted : L.SortedLT := by
      simpa [L] using retained.sortedLT_sort
    have hform :
        L.formPerm i =
          L[(k + 1) % L.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hk)) := by
      rw [← hki]
      exact List.formPerm_apply_getElem L hLnodup k hk
    have mem_retained_iff (j : ℕ) :
        j ∈ retained ↔
          j < γ.vertices.length ∧
            (if hj : j + 1 < γ.vertices.length then
              γ.vertices[j] ≠ γ.vertices[j + 1]
            else
              False) := by
      simp [retained]
    have retained_succ_lt {j : ℕ} (hj : j ∈ retained) :
        j + 1 < γ.vertices.length := by
      have h := (mem_retained_iff j).1 hj
      by_cases hsucc : j + 1 < γ.vertices.length
      · exact hsucc
      · simp [hsucc] at h
    have retained_lt {j : ℕ} (hj : j ∈ retained) :
        j < γ.vertices.length :=
      Nat.lt_of_succ_lt (retained_succ_lt hj)
    have no_between_consecutive
        {j : ℕ} (hj : j ∈ retained)
        (hk1 : k + 1 < L.length)
        (hij : i < j) (hjn : j < L[k + 1]'hk1) : False := by
      have hjL : j ∈ L := (memL_iff j).2 hj
      let r := L.idxOf j
      have hr : r < L.length := List.idxOf_lt_length_iff.2 hjL
      have hgetr : L[r] = j := List.getElem_idxOf hr
      have hkr : k < r := by
        have : L[k] < L[r] := by simpa [hki, hgetr] using hij
        simpa using (hLsorted.getElem_lt_getElem_iff (i := k) (j := r)).1 this
      have hrk : r < k + 1 := by
        have : L[r] < L[k + 1] := by simpa [hgetr] using hjn
        simpa using (hLsorted.getElem_lt_getElem_iff (i := r) (j := k + 1)).1 this
      omega
    have no_after_last
        {j : ℕ} (hj : j ∈ retained)
        (hnot : ¬ k + 1 < L.length) (hij : i < j) : False := by
      have hjL : j ∈ L := (memL_iff j).2 hj
      let r := L.idxOf j
      have hr : r < L.length := List.idxOf_lt_length_iff.2 hjL
      have hgetr : L[r] = j := List.getElem_idxOf hr
      have hkr : k < r := by
        have : L[k] < L[r] := by simpa [hki, hgetr] using hij
        simpa using (hLsorted.getElem_lt_getElem_iff (i := k) (j := r)).1 this
      omega
    have no_before_first
        {j : ℕ} (hj : j ∈ retained)
        (h0 : 0 < L.length) (hj0 : j < L[0]'h0) : False := by
      have hjL : j ∈ L := (memL_iff j).2 hj
      let r := L.idxOf j
      have hr : r < L.length := List.idxOf_lt_length_iff.2 hjL
      have hgetr : L[r] = j := List.getElem_idxOf hr
      have hr0 : r < 0 := by
        have : L[r] < L[0] := by simpa [hgetr] using hj0
        simpa using (hLsorted.getElem_lt_getElem_iff (i := r) (j := 0)).1 this
      omega
    by_cases hk1 : k + 1 < L.length
    · have hmod : (k + 1) % L.length = k + 1 := Nat.mod_eq_of_lt hk1
      have hnext :
          L.formPerm i = L[k + 1]'hk1 := by
        simpa [hmod] using hform
      have hle : i + 1 ≤ L[k + 1]'hk1 := by
        have hik : L[k] < L[k + 1] :=
          hLsorted.getElem_lt_getElem_of_lt (by exact Nat.lt_succ_self k)
        omega
      have hnext_mem : L[k + 1]'hk1 ∈ retained := by
        exact (memL_iff _).1 (List.get_mem L ⟨k + 1, hk1⟩)
      have heq :=
        vertices_eq_of_no_retained
          hle (retained_lt hnext_mem)
          (fun j hjlo hjhi hjmem =>
            no_between_consecutive hjmem hk1 (by omega) (by simpa using hjhi))
      simpa [hnext] using heq.symm
    · have h0 : 0 < L.length := Nat.zero_lt_of_lt hk
      have hmod : (k + 1) % L.length = 0 := by
        have hklen : k + 1 = L.length := by omega
        rw [hklen, Nat.mod_self]
      have hnext :
          L.formPerm i = L[0]'h0 := by
        simpa [hmod] using hform
      have hi_succ : i + 1 < γ.vertices.length := retained_succ_lt hi
      have hlast_lt : γ.vertices.length - 1 < γ.vertices.length :=
        Nat.sub_lt (List.length_pos_iff.mpr γ.vertices_nonempty) Nat.zero_lt_one
      have hi_last : i + 1 ≤ γ.vertices.length - 1 := by omega
      have heq_tail :
          γ.vertices[i + 1]'hi_succ =
            γ.vertices[γ.vertices.length - 1]'hlast_lt :=
        vertices_eq_of_no_retained
          hi_last hlast_lt
          (fun j hjlo hjhi hjmem =>
            no_after_last hjmem hk1 (by omega))
      have hnext_mem : L[0]'h0 ∈ retained := by
        exact (memL_iff _).1 (List.get_mem L ⟨0, h0⟩)
      have hnext_lt : L[0]'h0 < γ.vertices.length := retained_lt hnext_mem
      have hzero_next : 0 ≤ L[0]'h0 := Nat.zero_le _
      have heq_head :
          γ.vertices[0]'(List.length_pos_iff.mpr γ.vertices_nonempty) =
            γ.vertices[L[0]'h0]'hnext_lt :=
        vertices_eq_of_no_retained
          hzero_next hnext_lt
          (fun j _ hjhi hjmem =>
            no_before_first hjmem h0 (by simpa using hjhi))
      simpa [hnext] using (heq_head.symm.trans (hfirst_last.trans heq_tail.symm))
  have hcyclic : ∀ i : retained, start (σ i) = stop i := by
    intro i
    have hendpoint := raw_endpoint i.1 i.2
    simpa [start, stop, σ, σN, L, hretained] using hendpoint
  refine ⟨σ, hcyclic, ?_⟩
  rw [← Finset.sum_coe_sort retained]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_succ : i.1 + 1 < γ.vertices.length := by
    have h := i.2
    simp [retained] at h
    exact h.2.choose
  simp [hi_succ, start, stop, hcyclic i]
