import ErdosProblems.Erdos360.FiveLayerArithmetic

/-!
# The sharp five-layer finite-set inequality

This module enumerates the four possible numbers of non-endpoint fibres in
the distinguished coset.  The numerical leaves are supplied by
`FiveLayerArithmetic`; here they are assembled without imposing an order on
the three remaining support points.
-/
namespace Erdos360

open scoped BigOperators

attribute [local instance] Classical.propDecidable

lemma hybrid_five_filter_sum_one_good (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hbasew : w base = M) (htopw : w top = K) (hMK : M < K)
    (hwiM : w i ≤ M)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ a ∈ ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a),
      hybridA K (w a)) = K + (if M < w j then hybridA K (w j) else 0) +
        (if M < w k then hybridA K (w k) else 0) := by
  rw [Finset.sum_filter]
  simp [hbasew, htopw, hMK, not_lt_of_ge hwiM, hybridA,
    hbt, hbt.symm, hbi, hbi.symm, hbj, hbj.symm, hbk, hbk.symm,
    hti, hti.symm, htj, htj.symm, htk, htk.symm,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm, add_assoc]
  omega

lemma hybrid_five_arithmetic_explicit_three_good
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hA : A = {base, top, i, j, k})
    (hGood : Good = {base, i, j, k})
    (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hwiK : w i ≤ K) (hwjK : w j ≤ K) (hwkK : w k ≤ K)
    (hwiM : w i ≤ M) (hwjM : w j ≤ M) (hwkM : w k ≤ M)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let Bad := A \ Good
    let G := ∑ a ∈ Good, hybridG K (w a)
    let AH := ∑ a ∈ A.filter (fun a => M < w a), hybridA K (w a)
    let T := ∑ a ∈ A, hybridT K (w a)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    24 * (∑ a ∈ A, w a) ≤
      5 * (2 * ((∑ a ∈ A, w a) + (A.card - 1) * K) +
        max C (max AA T)) := by
  subst A
  subst Good
  have h := five_hybrid_three_good hMK hwiK hwjK hwkK hwiM hwjM hwkM
  have hBadSet : ({base, top, i, j, k} \ {base, i, j, k} : Finset ℕ) = {top} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hBad : ({base, top, i, j, k} \ {base, i, j, k} : Finset ℕ).card = 1 := by
    rw [hBadSet]
    simp
  have hBadTail : ({top, i, j, k} \ {base, i, j, k} : Finset ℕ).card = 1 := by
    have hset : ({top, i, j, k} \ {base, i, j, k} : Finset ℕ) = {top} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset]
    simp
  have hfilter : ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a) =
      {top} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, hwa⟩
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · omega
      · rfl
      · omega
      · omega
      · omega
    · rintro rfl
      simp [hMK, htopw]
  have hAH : (∑ a ∈ ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a),
      hybridA K (w a)) = K := by
    rw [hfilter]
    simp [htopw, hybridA]
    omega
  have htwice : 2 * K - K = K := by omega
  simpa [hBad, hBadTail, hAH, htwice, hbasew, htopw, hbt, hbt.symm, hbi, hbi.symm, hbj, hbj.symm,
    hbk, hbk.symm, hti, hti.symm, htj, htj.symm, htk, htk.symm,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm, add_assoc] using h

lemma hybrid_five_arithmetic_explicit_two_good
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hA : A = {base, top, i, j, k})
    (hGood : Good = {base, i, j})
    (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hwiK : w i ≤ K) (hwjK : w j ≤ K) (hwkK : w k ≤ K)
    (hwiM : w i ≤ M) (hwjM : w j ≤ M)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let Bad := A \ Good
    let G := ∑ a ∈ Good, hybridG K (w a)
    let AH := ∑ a ∈ A.filter (fun a => M < w a), hybridA K (w a)
    let T := ∑ a ∈ A, hybridT K (w a)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    24 * (∑ a ∈ A, w a) ≤
      5 * (2 * ((∑ a ∈ A, w a) + (A.card - 1) * K) +
        max C (max AA T)) := by
  subst A
  subst Good
  have hBadSet : ({base, top, i, j, k} \ {base, i, j} : Finset ℕ) = {top, k} := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hBad : ({base, top, i, j, k} \ {base, i, j} : Finset ℕ).card = 2 := by
    rw [hBadSet]
    simp [htk]
  have hBadTail : ({top, i, j, k} \ {base, i, j} : Finset ℕ).card = 2 := by
    have hs : ({top, i, j, k} \ {base, i, j} : Finset ℕ) = {top, k} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hs]
    simp [htk]
  have hAH : (∑ a ∈ ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a),
      hybridA K (w a)) = K + if M < w k then hybridA K (w k) else 0 := by
    by_cases hkAbove : M < w k
    · have hf : ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a) =
          {top, k} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, hwa⟩
          rcases ha with rfl | rfl | rfl | rfl | rfl
          · omega
          · simp
          · omega
          · omega
          · simp
        · intro ha
          rcases ha with rfl | rfl
          · exact ⟨by simp, by simpa [htopw] using hMK⟩
          · exact ⟨by simp, hkAbove⟩
      rw [hf]
      simp [htk, htopw, hybridA, hkAbove]
      omega
    · have hf : ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a) =
          {top} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨ha, hwa⟩
          rcases ha with rfl | rfl | rfl | rfl | rfl
          · omega
          · rfl
          · omega
          · omega
          · contradiction
        · rintro rfl
          simp [hMK, htopw]
      rw [hf]
      simp [htopw, hybridA, hkAbove]
      omega
  have h := five_hybrid_two_good hMK hwiK hwjK hwkK hwiM hwjM
  have htwice : 2 * K - K = K := by omega
  simp [hBad, hBadTail, hAH, htwice, hbasew, htopw, hbt, hbt.symm, hbi, hbi.symm,
    hbj, hbj.symm, hbk, hbk.symm, hti, hti.symm, htj, htj.symm,
    htk, htk.symm, hij, hij.symm, hik, hik.symm, hjk, hjk.symm,
    add_assoc] at h ⊢
  have hC := le_max_left
      (hybridG K M + hybridG K (w i) + hybridG K (w j) + hybridG K M)
      (max
        (hybridG K M + hybridG K (w i) + hybridG K (w j) +
          (hybridG K M - K) + (2 * (K + if M < w k then hybridA K (w k) else 0) - K))
        (hybridT K M + hybridT K K + hybridT K (w i) +
          hybridT K (w j) + hybridT K (w k)))
  have hAA := (le_max_left
      (hybridG K M + hybridG K (w i) + hybridG K (w j) +
        (hybridG K M - K) + (2 * (K + if M < w k then hybridA K (w k) else 0) - K))
      (hybridT K M + hybridT K K + hybridT K (w i) +
        hybridT K (w j) + hybridT K (w k))).trans
      (le_max_right
        (hybridG K M + hybridG K (w i) + hybridG K (w j) + hybridG K M)
        (max
          (hybridG K M + hybridG K (w i) + hybridG K (w j) +
            (hybridG K M - K) + (2 * (K + if M < w k then hybridA K (w k) else 0) - K))
          (hybridT K M + hybridT K K + hybridT K (w i) +
            hybridT K (w j) + hybridT K (w k))))
  omega

lemma hybrid_five_arithmetic_explicit_one_good
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hA : A = {base, top, i, j, k})
    (hGood : Good = {base, i})
    (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hwiK : w i ≤ K) (hwjK : w j ≤ K) (hwkK : w k ≤ K)
    (hwiM : w i ≤ M)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let Bad := A \ Good
    let G := ∑ a ∈ Good, hybridG K (w a)
    let AH := ∑ a ∈ A.filter (fun a => M < w a), hybridA K (w a)
    let T := ∑ a ∈ A, hybridT K (w a)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    24 * (∑ a ∈ A, w a) ≤
      5 * (2 * ((∑ a ∈ A, w a) + (A.card - 1) * K) +
        max C (max AA T)) := by
  subst A
  subst Good
  have hBad : ({base, top, i, j, k} \ {base, i} : Finset ℕ).card = 3 := by
    have hs : ({base, top, i, j, k} \ {base, i} : Finset ℕ) = {top, j, k} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hs]
    simp [htj, htk, hjk]
  have hBadTail : ({top, i, j, k} \ {base, i} : Finset ℕ).card = 3 := by
    have hs : ({top, i, j, k} \ {base, i} : Finset ℕ) = {top, j, k} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hs]
    simp [htj, htk, hjk]
  have hAH := hybrid_five_filter_sum_one_good w hbasew htopw hMK hwiM
    hbt hbi hbj hbk
    hti htj htk hij hik hjk
  have h := five_hybrid_one_good hMK hwiK hwjK hwkK hwiM
  have htwice : 2 * K - K = K := by omega
  simpa [hBad, hBadTail, hAH, htwice, hbasew, htopw, hbt, hbt.symm,
    hbi, hbi.symm, hbj, hbj.symm, hbk, hbk.symm,
    hti, hti.symm, htj, htj.symm, htk, htk.symm,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm, add_assoc] using h

lemma hybrid_five_filter_sum_only_base (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hbasew : w base = M) (htopw : w top = K) (hMK : M < K)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ a ∈ ({base, top, i, j, k} : Finset ℕ).filter (fun a => M < w a),
      hybridA K (w a)) = K + (if M < w i then hybridA K (w i) else 0) +
        (if M < w j then hybridA K (w j) else 0) +
        (if M < w k then hybridA K (w k) else 0) := by
  rw [Finset.sum_filter]
  simp [hbasew, htopw, hMK, hybridA,
    hbt, hbt.symm, hbi, hbi.symm, hbj, hbj.symm, hbk, hbk.symm,
    hti, hti.symm, htj, htj.symm, htk, htk.symm,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm, add_assoc]
  omega

lemma hybrid_five_arithmetic_explicit_only_base
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top i j k M K : ℕ}
    (hA : A = {base, top, i, j, k})
    (hGood : Good = {base})
    (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hwiK : w i ≤ K) (hwjK : w j ≤ K) (hwkK : w k ≤ K)
    (hbt : base ≠ top) (hbi : base ≠ i) (hbj : base ≠ j) (hbk : base ≠ k)
    (hti : top ≠ i) (htj : top ≠ j) (htk : top ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let Bad := A \ Good
    let G := ∑ a ∈ Good, hybridG K (w a)
    let AH := ∑ a ∈ A.filter (fun a => M < w a), hybridA K (w a)
    let T := ∑ a ∈ A, hybridT K (w a)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    24 * (∑ a ∈ A, w a) ≤
      5 * (2 * ((∑ a ∈ A, w a) + (A.card - 1) * K) +
        max C (max AA T)) := by
  subst A
  subst Good
  have hBad : ({base, top, i, j, k} \ {base} : Finset ℕ).card = 4 := by
    have hs : ({base, top, i, j, k} \ {base} : Finset ℕ) = {top, i, j, k} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hs]
    simp [hti, htj, htk, hij, hik, hjk]
  have hBadTail : ({top, i, j, k} \ {base} : Finset ℕ).card = 4 := by
    have hs : ({top, i, j, k} \ {base} : Finset ℕ) = {top, i, j, k} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hs]
    simp [hti, htj, htk, hij, hik, hjk]
  have hAH := hybrid_five_filter_sum_only_base w hbasew htopw hMK
    hbt hbi hbj hbk
    hti htj htk hij hik hjk
  have h := five_hybrid_only_base hMK hwiK hwjK hwkK
  dsimp [fiveHybridOnlyBaseGoal] at h
  have hTK : hybridT K K = K := ob_hybridT_eq_top le_rfl (by omega)
  have hg : hybridG K M + 3 * hybridG K M = 4 * hybridG K M := by omega
  simpa [hBad, hBadTail, hAH, hTK, hg, hbasew, htopw, hbt, hbt.symm,
    hbi, hbi.symm, hbj, hbj.symm, hbk, hbk.symm,
    hti, hti.symm, htj, htj.symm, htk, htk.symm,
    hij, hij.symm, hik, hik.symm, hjk, hjk.symm, add_assoc] using h

lemma hybrid_five_arithmetic
    (A Good : Finset ℕ) (w : ℕ → ℕ) {base top M K : ℕ}
    (hcard : A.card = 5) (hGoodSub : Good ⊆ A)
    (hbaseA : base ∈ A) (htopA : top ∈ A)
    (hbase : base ∈ Good) (hbasew : w base = M) (htopw : w top = K)
    (hMK : M < K) (hmax : ∀ i ∈ A, w i ≤ K)
    (hGoodMax : ∀ i ∈ Good, w i ≤ M) :
    let Bad := A \ Good
    let G := ∑ i ∈ Good, hybridG K (w i)
    let AH := ∑ i ∈ A.filter (fun i => M < w i), hybridA K (w i)
    let T := ∑ i ∈ A, hybridT K (w i)
    let C := G + (Bad.card - 1) * hybridG K M
    let AA := G + (Bad.card - 1) * (hybridG K M - K) + (2 * AH - K)
    24 * (∑ i ∈ A, w i) ≤
      5 * (2 * ((∑ i ∈ A, w i) + (A.card - 1) * K) +
        max C (max AA T)) := by
  classical
  have htopNotGood : top ∉ Good := by
    intro ht
    have := hGoodMax top ht
    omega
  have hne : top ≠ base := by
    intro heq
    subst top
    omega
  let R := (A.erase top).erase base
  have hbaseErase : base ∈ A.erase top := Finset.mem_erase.mpr ⟨hne.symm, hbaseA⟩
  have hRcard : R.card = 3 := by
    dsimp only [R]
    rw [Finset.card_erase_of_mem hbaseErase, Finset.card_erase_of_mem htopA]
    omega
  obtain ⟨i, j, k, hij, hik, hjk, hReq⟩ := Finset.card_eq_three.mp hRcard
  have hiR : i ∈ R := by simp [hReq]
  have hjR : j ∈ R := by simp [hReq]
  have hkR : k ∈ R := by simp [hReq]
  have hiA : i ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hiR)
  have hjA : j ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hjR)
  have hkA : k ∈ A := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hkR)
  have hib : i ≠ base := (Finset.mem_erase.mp hiR).1
  have hjb : j ≠ base := (Finset.mem_erase.mp hjR).1
  have hkb : k ≠ base := (Finset.mem_erase.mp hkR).1
  have hit : i ≠ top := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hiR)).1
  have hjt : j ≠ top := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hjR)).1
  have hkt : k ≠ top := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hkR)).1
  have hAeq : A = {base, top, i, j, k} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_cases xb : x = base
      · simp [xb]
      by_cases xt : x = top
      · simp [xt]
      have hxR : x ∈ R := Finset.mem_erase.mpr ⟨xb, Finset.mem_erase.mpr ⟨xt, hx⟩⟩
      rw [hReq] at hxR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxR ⊢
      tauto
    · have h1 := Finset.card_insert_le base ({top, i, j, k} : Finset ℕ)
      have h2 := Finset.card_insert_le top ({i, j, k} : Finset ℕ)
      have h3 := Finset.card_insert_le i ({j, k} : Finset ℕ)
      have h4 := Finset.card_insert_le j ({k} : Finset ℕ)
      simp only [Finset.card_singleton] at h1 h2 h3 h4 ⊢
      omega
  have hwi := hmax i hiA
  have hwj := hmax j hjA
  have hwk := hmax k hkA
  by_cases hiG : i ∈ Good <;>
    by_cases hjG : j ∈ Good <;>
      by_cases hkG : k ∈ Good
  all_goals
    have hiGM : i ∈ Good → w i ≤ M := fun hi => hGoodMax i hi
    have hjGM : j ∈ Good → w j ≤ M := fun hj => hGoodMax j hj
    have hkGM : k ∈ Good → w k ≤ M := fun hk => hGoodMax k hk
    let G0 : Finset ℕ := {base} ∪ (if i ∈ Good then {i} else ∅) ∪
      (if j ∈ Good then {j} else ∅) ∪ (if k ∈ Good then {k} else ∅)
    have hGoodConcrete : Good = G0 := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hxA := hGoodSub hx
        rw [hAeq] at hxA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxA
        rcases hxA with hxb | hxt | hxi | hxj | hxk
        · subst x; simp [G0]
        · subst x; exact (htopNotGood hx).elim
        · subst x; simp [G0, hx]
        · subst x; simp [G0, hx]
        · subst x; simp [G0, hx]
      · intro x hx
        simp only [G0, Finset.mem_union] at hx
        rcases hx with hx | hx
        · rcases hx with hx | hx
          · rcases hx with hx | hx
            · have : x = base := Finset.mem_singleton.mp hx
              subst x
              exact hbase
            · by_cases him : i ∈ Good
              · have : x = i := by simpa [him] using hx
                subst x
                exact him
              · simp [him] at hx
          · by_cases hjm : j ∈ Good
            · have : x = j := by simpa [hjm] using hx
              subst x
              exact hjm
            · simp [hjm] at hx
        · by_cases hkm : k ∈ Good
          · have : x = k := by simpa [hkm] using hx
            subst x
            exact hkm
          · simp [hkm] at hx
    simp [G0, hiG, hjG, hkG] at hGoodConcrete
  · exact hybrid_five_arithmetic_explicit_three_good A Good w hAeq
      (by rw [hGoodConcrete]; ext x; simp [or_comm, or_left_comm, or_assoc])
      hbasew htopw hMK
      hwi hwj hwk (hiGM hiG) (hjGM hjG) (hkGM hkG) hne.symm hib.symm
      hjb.symm hkb.symm hit.symm hjt.symm hkt.symm hij hik hjk
  · exact hybrid_five_arithmetic_explicit_two_good A Good w hAeq hGoodConcrete
      hbasew htopw hMK
      hwi hwj hwk (hiGM hiG) (hjGM hjG) hne.symm hib.symm
      hjb.symm hkb.symm hit.symm hjt.symm hkt.symm hij hik hjk
  · exact hybrid_five_arithmetic_explicit_two_good
      (i := i) (j := k) (k := j) A Good w
      (by rw [hAeq]; ext x; simp [or_comm, or_left_comm, or_assoc])
      (by rw [hGoodConcrete])
      hbasew htopw hMK
      hwi hwk hwj (hiGM hiG) (hkGM hkG) hne.symm hib.symm
      hkb.symm hjb.symm hit.symm hkt.symm hjt.symm hik hij hjk.symm
  · exact hybrid_five_arithmetic_explicit_one_good A Good w hAeq hGoodConcrete
      hbasew htopw hMK
      hwi hwj hwk (hiGM hiG) hne.symm hib.symm hjb.symm hkb.symm
      hit.symm hjt.symm hkt.symm hij hik hjk
  · exact hybrid_five_arithmetic_explicit_two_good
      (i := j) (j := k) (k := i) A Good w
      (by rw [hAeq]; ext x; simp [or_comm, or_left_comm, or_assoc])
      (by rw [hGoodConcrete]; ext x; simp [or_comm, or_left_comm, or_assoc])
      hbasew htopw hMK
      hwj hwk hwi (hjGM hjG) (hkGM hkG) hne.symm hjb.symm
      hkb.symm hib.symm hjt.symm hkt.symm hit.symm hjk hij.symm hik.symm
  · exact hybrid_five_arithmetic_explicit_one_good
      (i := j) (j := i) (k := k) A Good w
      (by rw [hAeq]; ext x; simp [or_comm, or_left_comm, or_assoc])
      (by rw [hGoodConcrete])
      hbasew htopw hMK
      hwj hwi hwk (hjGM hjG) hne.symm hjb.symm hib.symm hkb.symm
      hjt.symm hit.symm hkt.symm hij.symm hjk hik
  · exact hybrid_five_arithmetic_explicit_one_good
      (i := k) (j := i) (k := j) A Good w
      (by rw [hAeq]; ext x; simp [or_comm, or_left_comm, or_assoc])
      (by rw [hGoodConcrete])
      hbasew htopw hMK
      hwk hwi hwj (hkGM hkG) hne.symm hkb.symm hib.symm hjb.symm
      hkt.symm hit.symm hjt.symm hik.symm hjk.symm hij
  · exact hybrid_five_arithmetic_explicit_only_base A Good w hAeq hGoodConcrete
      hbasew htopw hMK
      hwi hwj hwk hne.symm hib.symm hjb.symm hkb.symm
      hit.symm hjt.symm hkt.symm hij hik hjk

end Erdos360
