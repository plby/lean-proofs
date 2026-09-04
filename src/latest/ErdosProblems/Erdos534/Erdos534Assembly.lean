import ErdosProblems.Erdos534.Erdos534Sieve

namespace Erdos534

def PrimitiveSupportedOn (P A : Finset ℕ) : Prop :=
  ∀ g ∈ primitive A, g.primeFactors ⊆ P

lemma primePowerReplace_dvd_primePowerReplace_of_dvd
    {p q a b : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ∣ b) :
    primePowerReplace p q a ∣ primePowerReplace p q b := by
  rw [← Nat.factorization_le_iff_dvd
    (primePowerReplace_ne_zero hp ha0) (primePowerReplace_ne_zero hp hb0),
    primePowerReplace_factorization hp ha0,
    primePowerReplace_factorization hp hb0]
  have hfac : a.factorization ≤ b.factorization :=
    (Nat.factorization_le_iff_dvd ha0 hb0).2 hab
  intro r
  by_cases hrq : r = q
  · subst r
    simp [hpq]
  · simp only [Finsupp.add_apply, Finsupp.erase_ne hrq,
      Finsupp.single_apply]
    by_cases hpr : p = r
    · subst r
      simp only [if_pos rfl]
      have hpFac := hfac p
      have hqFac := hfac q
      simp only [↓reduceIte, ge_iff_le]
      exact Nat.add_le_add hpFac hqFac
    · simp only [if_neg hpr]
      exact hfac r

lemma dvd_primePowerReplace_of_dvd_of_not_dvd
    {p q a g : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha0 : a ≠ 0) (hg0 : g ≠ 0) (hpa : ¬p ∣ a)
    (hqa : q ∣ a) (hga : g ∣ a) (hqg : ¬q ∣ g) :
    g ∣ primePowerReplace p q a := by
  rw [← Nat.factorization_le_iff_dvd hg0
    (primePowerReplace_ne_zero hp ha0),
    primePowerReplace_factorization hp ha0]
  have hfac : g.factorization ≤ a.factorization :=
    (Nat.factorization_le_iff_dvd hg0 ha0).2 hga
  have hgfq : g.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqg
  have hafp : a.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpa
  intro r
  by_cases hrq : r = q
  · subst r
    simp [hgfq, hpq]
  · simp only [Finsupp.add_apply, Finsupp.erase_ne hrq,
      Finsupp.single_apply]
    by_cases hpr : p = r
    · subst r
      simp only [if_pos rfl]
      have hgp : g.factorization p = 0 := by
        have := hfac p
        omega
      simp [hpq, hgp]
    · simp only [if_neg hpr]
      exact hfac r

lemma replaced_prime_not_dvd_primePowerReplace
    {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha0 : a ≠ 0) (hpa : ¬p ∣ a) (hqa : q ∣ a) :
    ¬q ∣ primePowerReplace p q a := by
  rw [prime_dvd_primePowerReplace_iff hp hq hq hpq ha0 hpa hqa]
  aesop

lemma inserted_prime_dvd_primePowerReplace
    {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha0 : a ≠ 0) (hpa : ¬p ∣ a) (hqa : q ∣ a) :
    p ∣ primePowerReplace p q a := by
  rw [prime_dvd_primePowerReplace_iff hp hq hp hpq ha0 hpa hqa]
  exact Or.inl rfl

lemma primeFactors_primePowerReplace_subset
    {p q a : ℕ} {P : Finset ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha0 : a ≠ 0) (hpa : ¬p ∣ a) (hqa : q ∣ a)
    (hpP : p ∈ P) (haP : a.primeFactors ⊆ P) :
    (primePowerReplace p q a).primeFactors ⊆ P := by
  intro t ht
  have htPrime := Nat.prime_of_mem_primeFactors ht
  have htDiv := Nat.dvd_of_mem_primeFactors ht
  rw [prime_dvd_primePowerReplace_iff hp hq htPrime hpq ha0 hpa hqa] at htDiv
  rcases htDiv with rfl | ⟨_htq, hta⟩
  · exact hpP
  · exact haP (Nat.mem_primeFactors.mpr ⟨htPrime, hta, ha0⟩)

lemma QOptimal.leftCompress_primitiveSupportedOn
    {N p q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hallow : AllowedShift N p q) {P : Finset ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P)
    (hSupport : PrimitiveSupportedOn P A) :
    PrimitiveSupportedOn P (leftCompress p q A) := by
  classical
  let C := leftCompress p q A
  have hCadm := leftCompress_qAdmissible hp hq hpq hallow hA.1
  have hC : QOptimal N C := by
    refine ⟨hCadm.1, ?_⟩
    intro D hD
    simpa [C, hCadm.2] using hA.2 D hD
  intro x hx t ht
  have hxC := (mem_primitive.mp hx).1
  have hx0 : x ≠ 0 := by
    have := (mem_interval.mp (hC.1.1 hxC)).1
    omega
  have hminimal := (mem_primitive.mp hx).2
  rcases mem_leftCompress_iff.mp hxC with hxOld | hxImage
  · rcases hxOld with ⟨hxA, hxNotMoving⟩
    obtain ⟨g, hgPrim, hgx⟩ := exists_primitive_dvd hA.1.1 hxA
    have hgA := (mem_primitive.mp hgPrim).1
    have hg0 : g ≠ 0 := by
      have := (mem_interval.mp (hA.1.1 hgA)).1
      omega
    by_cases hgMove : g ∈ movingPart p q A
    · have hgData := mem_movingPart.mp hgMove
      have hqx : q ∣ x := hgData.2.1.trans hgx
      by_cases hpx : p ∣ x
      · have hgSq := hA.squarefree_of_mem_primitive hgPrim
        have hrepEq : primePowerReplace p q g = ordCompl[q] g * p :=
          primePowerReplace_eq_ordCompl_mul_of_squarefree hq hgSq hgData.2.1
        have hcompl : ordCompl[q] g ∣ x :=
          (Nat.ordCompl_dvd g q).trans hgx
        have hcop : Nat.Coprime (ordCompl[q] g) p :=
          (hp.coprime_iff_not_dvd.mpr fun hdiv ↦
            hgData.2.2.1 (hdiv.trans (Nat.ordCompl_dvd g q))).symm
        have hrepDvd : primePowerReplace p q g ∣ x := by
          rw [hrepEq]
          exact hcop.mul_dvd_of_dvd_of_dvd hcompl hpx
        have hrepC : primePowerReplace p q g ∈ C :=
          mem_leftCompress_iff.mpr (Or.inr ⟨g, hgMove, rfl⟩)
        have hxrep : x ∣ primePowerReplace p q g :=
          hminimal _ hrepC hrepDvd
        have hEq : x = primePowerReplace p q g :=
          Nat.dvd_antisymm hxrep hrepDvd
        have hrepP := primeFactors_primePowerReplace_subset hp hq hpq.ne
          hg0 hgData.2.2.1 hgData.2.1 hpP (hSupport g hgPrim)
        exact hrepP (by simpa [hEq] using ht)
      ·
        have hxReplaceA : primePowerReplace p q x ∈ A := by
          by_contra hnot
          exact hxNotMoving (mem_movingPart.mpr ⟨hxA, hqx, hpx, hnot⟩)
        have hxReplace0 : primePowerReplace p q x ≠ 0 :=
          primePowerReplace_ne_zero hp hx0
        obtain ⟨h, hhPrim, hhReplace⟩ :=
          exists_primitive_dvd hA.1.1 hxReplaceA
        have hhA := (mem_primitive.mp hhPrim).1
        have hh0 : h ≠ 0 := by
          have := (mem_interval.mp (hA.1.1 hhA)).1
          omega
        have hqReplace : ¬q ∣ primePowerReplace p q x :=
          replaced_prime_not_dvd_primePowerReplace hp hq hpq.ne hx0 hpx hqx
        have hqh : ¬q ∣ h := fun hdiv ↦ hqReplace (hdiv.trans hhReplace)
        by_cases hph : p ∣ h
        · let e := primePowerReplace q p h
          have he0 : e ≠ 0 := primePowerReplace_ne_zero hq hh0
          have hex : e ∣ x := by
            have hmono := primePowerReplace_dvd_primePowerReplace_of_dvd
              hq hpq.ne.symm hh0 hxReplace0 hhReplace
            rw [primePowerReplace_inverse hp hq hpq.ne hx0 hpx] at hmono
            exact hmono
          let y := Nat.lcm g e
          have hyx : y ∣ x := Nat.lcm_dvd hgx hex
          have hypos : 0 < y := Nat.lcm_pos (Nat.pos_of_ne_zero hg0)
            (Nat.pos_of_ne_zero he0)
          have hyA : y ∈ A := by
            apply hA.upward_closed hgA (Nat.dvd_lcm_left g e) hypos
            exact (Nat.le_of_dvd (by
              have := (mem_interval.mp (hA.1.1 hxA)).1
              omega) hyx).trans (mem_interval.mp (hA.1.1 hxA)).2
          have hqe : q ∣ e := inserted_prime_dvd_primePowerReplace
            hq hp hpq.ne.symm hh0 hqh hph
          have hpe : ¬p ∣ e := replaced_prime_not_dvd_primePowerReplace
            hq hp hpq.ne.symm hh0 hqh hph
          have hqy : q ∣ y := hgData.2.1.trans (Nat.dvd_lcm_left g e)
          have hpy : ¬p ∣ y := by
            intro hdiv
            have hpProd : p ∣ g * e := hdiv.trans
              (Nat.lcm_dvd (dvd_mul_right g e) (dvd_mul_left e g))
            rcases hp.dvd_mul.mp hpProd with hpg | hpe'
            · exact hgData.2.2.1 hpg
            · exact hpe hpe'
          have heMono : primePowerReplace p q e ∣
              primePowerReplace p q y :=
            primePowerReplace_dvd_primePowerReplace_of_dvd hp hpq.ne
              he0 (ne_of_gt hypos) (Nat.dvd_lcm_right g e)
          have heInv : primePowerReplace p q e = h :=
            primePowerReplace_inverse hq hp hpq.ne.symm hh0 hqh
          have hyReplaceA : primePowerReplace p q y ∈ A := by
            apply hA.upward_closed hhA (heInv ▸ heMono)
            · exact primePowerReplace_ne_zero hp (ne_of_gt hypos) |>.bot_lt
            · have hlt := primePowerReplace_lt hpq hq (ne_of_gt hypos) hqy
              exact hlt.le.trans (mem_interval.mp (hA.1.1 hyA)).2
          have hyNotMove : y ∉ movingPart p q A := by
            intro hyMove
            exact (mem_movingPart.mp hyMove).2.2.2 hyReplaceA
          have hyC : y ∈ C := mem_leftCompress_iff.mpr (Or.inl ⟨hyA, hyNotMove⟩)
          have hxy : x ∣ y := hminimal y hyC hyx
          have hEq : x = y := Nat.dvd_antisymm hxy hyx
          have htY : t ∣ y := by simpa [hEq] using Nat.dvd_of_mem_primeFactors ht
          have htProd : t ∣ g * e := htY.trans
            (Nat.lcm_dvd (dvd_mul_right g e) (dvd_mul_left e g))
          have htPrime := Nat.prime_of_mem_primeFactors ht
          rcases htPrime.dvd_mul.mp htProd with htg | hte
          · exact hSupport g hgPrim
              (Nat.mem_primeFactors.mpr ⟨htPrime, htg, hg0⟩)
          · have heP := primeFactors_primePowerReplace_subset hq hp hpq.ne.symm
              hh0 hqh hph hqP (hSupport h hhPrim)
            exact heP (Nat.mem_primeFactors.mpr ⟨htPrime, hte, he0⟩)
        · have hhx : h ∣ x := by
            have hdiv := dvd_primePowerReplace_of_dvd_of_not_dvd
              hq hp hpq.ne.symm hxReplace0 hh0 hqReplace
              (inserted_prime_dvd_primePowerReplace hp hq hpq.ne hx0 hpx hqx)
              hhReplace hph
            rw [primePowerReplace_inverse hp hq hpq.ne hx0 hpx] at hdiv
            exact hdiv
          have hhNotMove : h ∉ movingPart p q A := by
            intro hm
            exact hqh (mem_movingPart.mp hm).2.1
          have hhC : h ∈ C := mem_leftCompress_iff.mpr (Or.inl ⟨hhA, hhNotMove⟩)
          have hxh : x ∣ h := hminimal h hhC hhx
          have hEq : x = h := Nat.dvd_antisymm hxh hhx
          exact hSupport h hhPrim (by simpa [hEq] using ht)
    · have hgC : g ∈ C := mem_leftCompress_iff.mpr (Or.inl ⟨hgA, hgMove⟩)
      have hxg : x ∣ g := hminimal g hgC hgx
      have hEq : x = g := Nat.dvd_antisymm hxg hgx
      exact hSupport g hgPrim (by simpa [hEq] using ht)

  · obtain ⟨a, haMove, rfl⟩ := hxImage
    have haData := mem_movingPart.mp haMove
    have ha0 : a ≠ 0 := by
      have := (mem_interval.mp (hA.1.1 haData.1)).1
      omega
    obtain ⟨g, hgPrim, hga⟩ := exists_primitive_dvd hA.1.1 haData.1
    have hgA := (mem_primitive.mp hgPrim).1
    have hg0 : g ≠ 0 := by
      have := (mem_interval.mp (hA.1.1 hgA)).1
      omega
    by_cases hqg : q ∣ g
    · have hpg : ¬p ∣ g := fun h ↦ haData.2.2.1 (h.trans hga)
      have hdiv : primePowerReplace p q g ∣ primePowerReplace p q a :=
        primePowerReplace_dvd_primePowerReplace_of_dvd hp hpq.ne
          hg0 ha0 hga
      have hrepC : primePowerReplace p q g ∈ C := by
        by_cases hrepA : primePowerReplace p q g ∈ A
        · apply mem_leftCompress_iff.mpr (Or.inl ⟨hrepA, ?_⟩)
          intro hm
          exact (mem_movingPart.mp hm).2.2.1
            (inserted_prime_dvd_primePowerReplace hp hq hpq.ne hg0 hpg hqg)
        · exact mem_leftCompress_iff.mpr (Or.inr
            ⟨g, mem_movingPart.mpr ⟨hgA, hqg, hpg, hrepA⟩, rfl⟩)
      have hxrep : primePowerReplace p q a ∣ primePowerReplace p q g :=
        (mem_primitive.mp hx).2 _ hrepC hdiv
      have hEq := Nat.dvd_antisymm hxrep hdiv
      have hrepP := primeFactors_primePowerReplace_subset hp hq hpq.ne
        hg0 hpg hqg hpP (hSupport g hgPrim)
      exact hrepP (by simpa [hEq] using ht)
    · have hgdiv : g ∣ primePowerReplace p q a :=
        dvd_primePowerReplace_of_dvd_of_not_dvd hp hq hpq.ne
          ha0 hg0 haData.2.2.1 haData.2.1 hga hqg
      have hgNotMove : g ∉ movingPart p q A := by
        intro hm
        exact hqg (mem_movingPart.mp hm).2.1
      have hgC : g ∈ C := mem_leftCompress_iff.mpr (Or.inl ⟨hgA, hgNotMove⟩)
      have hxg : primePowerReplace p q a ∣ g :=
        (mem_primitive.mp hx).2 _ hgC hgdiv
      have hEq := Nat.dvd_antisymm hxg hgdiv
      exact hSupport g hgPrim (by simpa [hEq] using ht)


lemma QOptimal.leftCompress_eq_of_not_mem_support
    {N p q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hqAbsent : ∀ g ∈ primitive A, q ∉ g.primeFactors) :
    leftCompress p q A = A := by
  have hMove : movingPart p q A = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    obtain ⟨a, ha⟩ := hnonempty
    have haData := mem_movingPart.mp ha
    have ha0 : a ≠ 0 := by
      have := (mem_interval.mp (hA.1.1 haData.1)).1
      omega
    obtain ⟨g, hgPrim, hga⟩ := exists_primitive_dvd hA.1.1 haData.1
    have hgA := (mem_primitive.mp hgPrim).1
    have hg0 : g ≠ 0 := by
      have := (mem_interval.mp (hA.1.1 hgA)).1
      omega
    have hqg : ¬q ∣ g := by
      intro hdiv
      exact hqAbsent g hgPrim
        (Nat.mem_primeFactors.mpr ⟨hq, hdiv, hg0⟩)
    have hgReplace : g ∣ primePowerReplace p q a :=
      dvd_primePowerReplace_of_dvd_of_not_dvd hp hq hpq.ne ha0 hg0
        haData.2.2.1 haData.2.1 hga hqg
    have hrepPos : 0 < primePowerReplace p q a :=
      (primePowerReplace_ne_zero hp ha0).bot_lt
    have hrepLe : primePowerReplace p q a ≤ N :=
      (primePowerReplace_lt hpq hq ha0 haData.2.1).le.trans
        (mem_interval.mp (hA.1.1 haData.1)).2
    exact haData.2.2.2
      (hA.upward_closed hgA hgReplace hrepPos hrepLe)
  simp [leftCompress, hMove]

lemma exists_supported_leftCompressed_qOptimal
    {N : ℕ} {P : Finset ℕ}
    (hex : ∃ A, QOptimal N A ∧ PrimitiveSupportedOn P A)
    (hshift : ∀ p q, p.Prime → q.Prime → p < q →
      AllowedShift N p q → q ∈ P → p ∈ P) :
    ∃ A, QOptimal N A ∧ PrimitiveSupportedOn P A ∧
      ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
        leftCompress p q A = A := by
  classical
  let F : Finset (Finset ℕ) :=
    (interval N).powerset.filter fun A ↦
      QOptimal N A ∧ PrimitiveSupportedOn P A
  obtain ⟨A₀, hA₀, hA₀P⟩ := hex
  have hF : F.Nonempty := by
    refine ⟨A₀, ?_⟩
    simpa only [F, Finset.mem_filter, Finset.mem_powerset] using
      ⟨hA₀.1.1, hA₀, hA₀P⟩
  have hWeights : (F.image familyWeight).Nonempty := hF.image _
  let w := (F.image familyWeight).min' hWeights
  have hwmem : w ∈ F.image familyWeight := Finset.min'_mem _ hWeights
  obtain ⟨A, hAF, hAw⟩ := Finset.mem_image.mp hwmem
  have hAData := Finset.mem_filter.mp (show A ∈
    (interval N).powerset.filter fun A ↦
      QOptimal N A ∧ PrimitiveSupportedOn P A by simpa only [F] using hAF)
  have hA : QOptimal N A := hAData.2.1
  have hAP : PrimitiveSupportedOn P A := hAData.2.2
  refine ⟨A, hA, hAP, ?_⟩
  intro p q hp hq hpq hallow
  by_cases hqP : q ∈ P
  · by_contra hne
    have hcompAdm := leftCompress_qAdmissible hp hq hpq hallow hA.1
    have hcompOpt : QOptimal N (leftCompress p q A) := by
      refine ⟨hcompAdm.1, ?_⟩
      intro D hD
      simpa [hcompAdm.2] using hA.2 D hD
    have hcompP := hA.leftCompress_primitiveSupportedOn hp hq hpq hallow
      (hshift p q hp hq hpq hallow hqP) hqP hAP
    have hcompF : leftCompress p q A ∈ F := by
      simpa only [F, Finset.mem_filter, Finset.mem_powerset] using
        ⟨hcompOpt.1.1, hcompOpt, hcompP⟩
    have hwle := Finset.min'_le (F.image familyWeight)
      (familyWeight (leftCompress p q A))
      (Finset.mem_image.mpr ⟨leftCompress p q A, hcompF, rfl⟩)
    have hlt := leftCompress_weight_lt hp hq hpq hA.1.1 hne
    rw [hAw] at hlt
    have hwle' : w ≤ familyWeight (leftCompress p q A) := by
      simpa only [w] using hwle
    exact (not_lt_of_ge hwle') hlt
  · apply hA.leftCompress_eq_of_not_mem_support hp hq hpq
    intro g hg hqg
    exact hqP (hAP g hg hqg)

lemma QOptimal.primitiveSupportedOn_multiplesBelow
    {N : ℕ} {G P : Finset ℕ}
    (hA : QOptimal N (multiplesBelow N G))
    (hGI : G ⊆ interval N)
    (hGP : ∀ g ∈ G, g.primeFactors ⊆ P) :
    PrimitiveSupportedOn P (multiplesBelow N G) := by
  intro x hx
  have hxA := (mem_primitive.mp hx).1
  obtain ⟨_hx1, _hxN, g, hgG, hgx⟩ := mem_multiplesBelow.mp hxA
  have hgI := mem_interval.mp (hGI hgG)
  have hgA : g ∈ multiplesBelow N G :=
    mem_multiplesBelow.mpr ⟨hgI.1, hgI.2, g, hgG, dvd_rfl⟩
  have hxg : x ∣ g := (mem_primitive.mp hx).2 g hgA hgx
  have hEq : x = g := Nat.dvd_antisymm hxg hgx
  simpa [hEq] using hGP g hgG

lemma generatedRemainder_pull_doubling_of_supported
    {N r : ℕ} {A L R : Finset ℕ}
    (hN : N ≠ 0) (hA : QOptimal N A) (hr : r.Prime) (hr3 : 3 ≤ r)
    (hL : L ⊆ primitive A) (hR : R ⊆ primitive A)
    (hrL : ∀ g ∈ L, ¬r ∣ g) (hrR : ∀ g ∈ R, r ∣ g)
    (hSupport : PrimitiveSupportedOn (coreScope N r) A) :
    2 * (generatedRemainder N L R).card ≤
      (generatedRemainder N L (pullGenerators r R)).card := by
  apply generatedRemainder_pull_doubling_of_fibers hr hrL hrR
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hA.squarefree_of_mem_primitive (hL hg)
    · exact hA.squarefree_of_mem_primitive (hR hg)
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hSupport g (hL hg)
    · exact hSupport g (hR hg)
  · intro S hS
    exact card_sifted_signature_doubling hN hr hr3
      (active_signature_contains_pull_prime hr hrR hS)
      (mem_activeRemainderSignatures.mp hS).1

lemma pull_displayed_support_pred
    {N r : ℕ} {A R : Finset ℕ}
    (hA : QOptimal N A) (hr : r.Prime)
    (hR : R ⊆ primitive A) (hrR : ∀ g ∈ R, r ∣ g)
    (hSupport : PrimitiveSupportedOn (coreScope N r) A) :
    ∀ g ∈ pullGenerators r R, g.primeFactors ⊆ coreScope N (r - 1) := by
  intro e he t ht
  obtain ⟨g, hgR, rfl⟩ := mem_pullGenerators.mp he
  have hgPrim := hR hgR
  have hgA := (mem_primitive.mp hgPrim).1
  have hg0 : g ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have htPrime := Nat.prime_of_mem_primeFactors ht
  have htDivG : t ∣ g := (Nat.dvd_of_mem_primeFactors ht).trans
    (Nat.ordCompl_dvd g r)
  have htG : t ∈ g.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨htPrime, htDivG, hg0⟩
  rcases mem_coreScope.mp (hSupport g hgPrim htG) with htSmall | htN
  · apply mem_coreScope.mpr (Or.inl ⟨htPrime, ?_⟩)
    have htr : t ≠ r := by
      intro h
      subst t
      exact Nat.not_dvd_ordCompl hr hg0 (Nat.dvd_of_mem_primeFactors ht)
    omega
  · exact mem_coreScope.mpr (Or.inr htN)

lemma QOptimal.primitiveSupportedOn_coreScope_self
    {N : ℕ} {A : Finset ℕ} (hA : QOptimal N A) :
    PrimitiveSupportedOn (coreScope N N) A := by
  intro g hg p hp
  have hgA := (mem_primitive.mp hg).1
  have hgI := mem_interval.mp (hA.1.1 hgA)
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpg := Nat.dvd_of_mem_primeFactors hp
  apply mem_coreScope.mpr
  left
  exact ⟨hpPrime, (Nat.le_of_dvd (by omega) hpg).trans hgI.2⟩

lemma coreScope_closed_under_allowed_shift
    {N r p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hallow : AllowedShift N p q) (hqScope : q ∈ coreScope N r) :
    p ∈ coreScope N r := by
  rcases mem_coreScope.mp hqScope with hqSmall | hqN
  · exact mem_coreScope.mpr (Or.inl ⟨hp, hpq.le.trans hqSmall.2⟩)
  · rcases hallow with hboth | hqNotN
    · exact mem_coreScope.mpr (Or.inr hboth.1)
    · exact (hqNotN hqN).elim

lemma primitiveSupportedOn_coreScope_pred_of_absent
    {N r : ℕ} {A : Finset ℕ}
    (hSupport : PrimitiveSupportedOn (coreScope N r) A)
    (hrAbsent : ∀ g ∈ primitive A, r ∉ g.primeFactors) :
    PrimitiveSupportedOn (coreScope N (r - 1)) A := by
  intro g hg p hp
  rcases mem_coreScope.mp (hSupport g hg hp) with hpSmall | hpN
  · apply mem_coreScope.mpr
    left
    refine ⟨hpSmall.1, ?_⟩
    have hpr : p ≠ r := by
      intro h
      subst p
      exact hrAbsent g hg hp
    omega
  · exact mem_coreScope.mpr (Or.inr hpN)

lemma primitiveSupportedOn_coreScope_pred_of_endpoint
    {N r : ℕ} {A : Finset ℕ}
    (hSupport : PrimitiveSupportedOn (coreScope N r) A)
    (hrN : r ∈ N.primeFactors) :
    PrimitiveSupportedOn (coreScope N (r - 1)) A := by
  intro g hg p hp
  rcases mem_coreScope.mp (hSupport g hg hp) with hpSmall | hpN
  · by_cases hpr : p = r
    · subst p
      exact mem_coreScope.mpr (Or.inr hrN)
    · exact mem_coreScope.mpr (Or.inl ⟨hpSmall.1, by omega⟩)
  · exact mem_coreScope.mpr (Or.inr hpN)

lemma lower_displayed_support_pred
    {N r : ℕ} {A : Finset ℕ}
    (hSupport : PrimitiveSupportedOn (coreScope N r) A) :
    ∀ g ∈ lowerGenerators r A,
      g.primeFactors ⊆ coreScope N (r - 1) := by
  intro g hg p hp
  have hgData := mem_lowerGenerators.mp hg
  rcases mem_coreScope.mp (hSupport g hgData.1 hp) with hpSmall | hpN
  · apply mem_coreScope.mpr
    left
    refine ⟨hpSmall.1, ?_⟩
    have hpr : p ≠ r := by
      intro h
      subst p
      exact hgData.2 (Nat.dvd_of_mem_primeFactors hp)
    omega
  · exact mem_coreScope.mpr (Or.inr hpN)

lemma pulled_optimal_supported_on_coreScope_pred
    {N r : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) (hr : r.Prime)
    (hSupport : PrimitiveSupportedOn (coreScope N r) A)
    {R : Finset ℕ} (hR : R ⊆ primitive A)
    (hrR : ∀ g ∈ R, r ∣ g)
    (hPull : QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r R))) :
    PrimitiveSupportedOn (coreScope N (r - 1))
      (multiplesBelow N (lowerGenerators r A ∪ pullGenerators r R)) := by
  apply hPull.primitiveSupportedOn_multiplesBelow
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hA.1.1 (mem_primitive.mp (mem_lowerGenerators.mp hg).1).1
    · apply pullGenerators_mem_interval
      · intro b hb
        exact hA.1.1 (mem_primitive.mp (hR hb)).1
      · exact hg
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact lower_displayed_support_pred hSupport g hg
    · exact pull_displayed_support_pred hA hr hR hrR hSupport g hg

/-- There is an auxiliary optimum whose primitive generators use no primes
other than endpoint primes and `2`.  This is the complete external-prime
elimination step of the Ahlswede--Khachatrian argument. -/
theorem exists_qOptimal_supported_on_coreScope_two (N : ℕ) (hN : N ≠ 0) :
    ∃ A, QOptimal N A ∧ PrimitiveSupportedOn (coreScope N 2) A := by
  classical
  let Good : ℕ → Prop := fun r ↦
    ∃ A, QOptimal N A ∧ PrimitiveSupportedOn (coreScope N r) A
  obtain ⟨A₀, hA₀⟩ := exists_qOptimal N
  have hGood : ∃ r, Good r := by
    refine ⟨N, A₀, hA₀, ?_⟩
    exact hA₀.primitiveSupportedOn_coreScope_self
  let r := Nat.find hGood
  have hrGood : Good r := Nat.find_spec hGood
  by_cases hr2 : r ≤ 2
  · obtain ⟨A, hA, hASupport⟩ := hrGood
    refine ⟨A, hA, ?_⟩
    intro g hg p hp
    rcases mem_coreScope.mp (hASupport g hg hp) with hpSmall | hpN
    · exact mem_coreScope.mpr (Or.inl ⟨hpSmall.1, hpSmall.2.trans hr2⟩)
    · exact mem_coreScope.mpr (Or.inr hpN)
  · have hr3 : 3 ≤ r := by omega
    have hrUsed : ∃ g ∈ primitive (Classical.choose hrGood),
        r ∈ g.primeFactors := by
      by_contra hnone
      push_neg at hnone
      have hPred : Good (r - 1) := by
        refine ⟨Classical.choose hrGood, (Classical.choose_spec hrGood).1, ?_⟩
        exact primitiveSupportedOn_coreScope_pred_of_absent
          (Classical.choose_spec hrGood).2 hnone
      have hmin := Nat.find_min' hGood hPred
      omega
    obtain ⟨g, hgPrim, hrg⟩ := hrUsed
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hrg
    have hrNotN : r ∉ N.primeFactors := by
      intro hrN
      have hPred : Good (r - 1) := by
        refine ⟨Classical.choose hrGood, (Classical.choose_spec hrGood).1, ?_⟩
        exact primitiveSupportedOn_coreScope_pred_of_endpoint
          (Classical.choose_spec hrGood).2 hrN
      have hmin := Nat.find_min' hGood hPred
      omega
    obtain ⟨A, hA, hASupport, hfix⟩ :=
      exists_supported_leftCompressed_qOptimal hrGood
        (fun p q hp hq hpq hallow hqScope ↦
          coreScope_closed_under_allowed_shift hp hq hpq hallow hqScope)
    have hDoubleWith := generatedRemainder_pull_doubling_of_supported
      (R := topGeneratorsWith r 2 A)
      hN hA hr hr3
      (fun g hg ↦ (mem_lowerGenerators.mp hg).1)
      (fun g hg ↦ (mem_topGeneratorsWith.mp hg).1)
      (fun g hg ↦ (mem_lowerGenerators.mp hg).2)
      (fun g hg ↦ (mem_topGeneratorsWith.mp hg).2.1) hASupport
    have hDoubleWithout := generatedRemainder_pull_doubling_of_supported
      (R := topGeneratorsWithout r 2 A)
      hN hA hr hr3
      (fun g hg ↦ (mem_lowerGenerators.mp hg).1)
      (fun g hg ↦ (mem_topGeneratorsWithout.mp hg).1)
      (fun g hg ↦ (mem_lowerGenerators.mp hg).2)
      (fun g hg ↦ (mem_topGeneratorsWithout.mp hg).2.1) hASupport
    have hPulled := hA.optimal_external_pull_of_doubling hN hfix
      Nat.prime_two hr (by omega) hrNotN hDoubleWith hDoubleWithout
    rcases hPulled with hPulled | hPulled
    · have hPred : Good (r - 1) := ⟨_, hPulled,
        pulled_optimal_supported_on_coreScope_pred hA hr hASupport
          (fun g hg ↦ (mem_topGeneratorsWith.mp hg).1)
          (fun g hg ↦ (mem_topGeneratorsWith.mp hg).2.1) hPulled⟩
      have hmin := Nat.find_min' hGood hPred
      omega
    · have hPred : Good (r - 1) := ⟨_, hPulled,
        pulled_optimal_supported_on_coreScope_pred hA hr hASupport
          (fun g hg ↦ (mem_topGeneratorsWithout.mp hg).1)
          (fun g hg ↦ (mem_topGeneratorsWithout.mp hg).2.1) hPulled⟩
      have hmin := Nat.find_min' hGood hPred
      omega

lemma primitiveSupportedOn_prefixSupport_self
    {N : ℕ} {A : Finset ℕ} (hN : N ≠ 0)
    (hSupport : PrimitiveSupportedOn (coreScope N 2) A) :
    PrimitiveSupportedOn (insert 2 (primePrefix N N)) A := by
  intro g hg p hp
  rcases mem_coreScope.mp (hSupport g hg hp) with hpSmall | hpN
  · have hpTwo : p = 2 := by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      exact Nat.le_antisymm hpSmall.2 hpPrime.two_le
    simpa [hpTwo]
  · apply Finset.mem_insert_of_mem
    exact mem_primePrefix.mpr ⟨hpN,
      Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.dvd_of_mem_primeFactors hpN)⟩

lemma prefixSupport_closed_under_allowed_shift
    {N s p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hallow : AllowedShift N p q)
    (hqSupport : q ∈ insert 2 (primePrefix N s)) :
    p ∈ insert 2 (primePrefix N s) := by
  rcases Finset.mem_insert.mp hqSupport with hqTwo | hqPrefix
  · subst q
    exact (not_lt_of_ge hp.two_le hpq).elim
  · have hqN := primePrefix_subset N s hqPrefix
    rcases hallow with hboth | hqNotN
    · apply Finset.mem_insert_of_mem
      exact mem_primePrefix.mpr
        ⟨hboth.1, hpq.le.trans (mem_primePrefix.mp hqPrefix).2⟩
    · exact (hqNotN hqN).elim

lemma primitiveSupportedOn_prefixSupport_pred_of_absent
    {N s : ℕ} {A : Finset ℕ}
    (hSupport : PrimitiveSupportedOn (insert 2 (primePrefix N s)) A)
    (hsAbsent : ∀ g ∈ primitive A, s ∉ g.primeFactors) :
    PrimitiveSupportedOn (insert 2 (primePrefix N (s - 1))) A := by
  intro g hg p hp
  rcases Finset.mem_insert.mp (hSupport g hg hp) with hpTwo | hpPrefix
  · exact Finset.mem_insert.mpr (Or.inl hpTwo)
  · apply Finset.mem_insert.mpr
    right
    apply mem_primePrefix.mpr
    refine ⟨(primePrefix_subset N s hpPrefix), ?_⟩
    have hps := (mem_primePrefix.mp hpPrefix).2
    have hpne : p ≠ s := by
      intro h
      subst p
      exact hsAbsent g hg hp
    omega

lemma prefixSupport_erase_subset_pred {N s : ℕ} (hsTwo : s ≠ 2) :
    (insert 2 (primePrefix N s)).erase s ⊆
      insert 2 (primePrefix N (s - 1)) := by
  intro p hp
  have hpData := Finset.mem_erase.mp hp
  rcases Finset.mem_insert.mp hpData.2 with hpTwo | hpPrefix
  · exact Finset.mem_insert.mpr (Or.inl hpTwo)
  · apply Finset.mem_insert.mpr
    right
    apply mem_primePrefix.mpr
    refine ⟨(primePrefix_subset N s hpPrefix), ?_⟩
    have hple := (mem_primePrefix.mp hpPrefix).2
    omega

lemma lower_displayed_support_erase
    {r : ℕ} {A P : Finset ℕ}
    (hSupport : PrimitiveSupportedOn P A) :
    ∀ g ∈ lowerGenerators r A, g.primeFactors ⊆ P.erase r := by
  intro g hg p hp
  have hgData := mem_lowerGenerators.mp hg
  apply Finset.mem_erase.mpr
  exact ⟨fun h ↦ hgData.2 (h ▸ Nat.dvd_of_mem_primeFactors hp),
    hSupport g hgData.1 hp⟩

lemma pull_displayed_support_erase
    {N r : ℕ} {A R P : Finset ℕ}
    (hA : QOptimal N A) (hr : r.Prime)
    (hR : R ⊆ primitive A) (hrR : ∀ g ∈ R, r ∣ g)
    (hSupport : PrimitiveSupportedOn P A) :
    ∀ g ∈ pullGenerators r R, g.primeFactors ⊆ P.erase r := by
  intro e he p hp
  obtain ⟨g, hgR, rfl⟩ := mem_pullGenerators.mp he
  have hgPrim := hR hgR
  have hgA := (mem_primitive.mp hgPrim).1
  have hg0 : g ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDivG : p ∣ g := (Nat.dvd_of_mem_primeFactors hp).trans
    (Nat.ordCompl_dvd g r)
  have hpG : p ∈ g.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpDivG, hg0⟩
  apply Finset.mem_erase.mpr
  refine ⟨?_, hSupport g hgPrim hpG⟩
  intro hpr
  subst p
  exact Nat.not_dvd_ordCompl hr hg0 (Nat.dvd_of_mem_primeFactors hp)

lemma pulled_optimal_supported_on_prefixSupport_pred
    {N r : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) (hr : r.Prime) (hrTwo : r ≠ 2)
    (hSupport : PrimitiveSupportedOn (insert 2 (primePrefix N r)) A)
    {R : Finset ℕ} (hR : R ⊆ primitive A)
    (hrR : ∀ g ∈ R, r ∣ g)
    (hPull : QOptimal N (multiplesBelow N
      (lowerGenerators r A ∪ pullGenerators r R))) :
    PrimitiveSupportedOn (insert 2 (primePrefix N (r - 1)))
      (multiplesBelow N (lowerGenerators r A ∪ pullGenerators r R)) := by
  apply hPull.primitiveSupportedOn_multiplesBelow
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hA.1.1 (mem_primitive.mp (mem_lowerGenerators.mp hg).1).1
    · apply pullGenerators_mem_interval
      · intro b hb
        exact hA.1.1 (mem_primitive.mp (hR hb)).1
      · exact hg
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact (lower_displayed_support_erase hSupport g hg).trans
        (prefixSupport_erase_subset_pred hrTwo)
    · exact (pull_displayed_support_erase hA hr hR hrR hSupport g hg).trans
        (prefixSupport_erase_subset_pred hrTwo)

lemma QOptimal.primitive_nonempty {N : ℕ} {A : Finset ℕ}
    (hA : QOptimal N A) (hN : 2 ≤ N) : (primitive A).Nonempty := by
  obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < N)
  have hCandQ : QAdmissible N (candidate N q) :=
    QAdmissible.of_admissible (by omega) (candidate_admissible hq)
  have hcard := hA.2 (candidate N q) hCandQ
  have hCandPos : 0 < (candidate N q).card :=
    Finset.card_pos.mpr ⟨N, candidate_contains_N hq⟩
  have hAPos : 0 < A.card := hCandPos.trans_le hcard
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hAPos
  obtain ⟨g, hg, _hga⟩ := exists_primitive_dvd hA.1.1 ha
  exact ⟨g, hg⟩

lemma no_qOptimal_supported_on_prefixSupport_zero
    {N : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hNodd : ¬2 ∣ N)
    (hA : QOptimal N A) :
    ¬PrimitiveSupportedOn (insert 2 (primePrefix N 0)) A := by
  intro hSupport
  have hPrefix0 : primePrefix N 0 = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hpPrime := Nat.prime_of_mem_primeFactors (primePrefix_subset N 0 hp)
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hple := (mem_primePrefix.mp hp).2
    omega
  obtain ⟨g, hg⟩ := hA.primitive_nonempty hN
  obtain ⟨p, hpPrime, hpg, hpN⟩ :=
    exists_prime_dvd_both_of_one_lt_gcd (hA.primitive_meets_N hg)
  have hg0 : g ≠ 0 := by
    have hgA := (mem_primitive.mp hg).1
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hpG : p ∈ g.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hg0⟩
  have hpTwo := hSupport g hg hpG
  simp only [hPrefix0, Finset.insert_empty, Finset.mem_singleton] at hpTwo
  exact hNodd (hpTwo ▸ hpN)

lemma candidate_eq_filter_dvd_of_primePrefix_eq_single {N q : ℕ}
    (hPrefix : primePrefix N q = {q}) :
    candidate N q = (interval N).filter (q ∣ ·) := by
  have hprod : prefixProduct N q = q := by simp [prefixProduct, hPrefix]
  ext m
  rw [mem_candidate]
  simp only [Finset.mem_filter, mem_interval, hprod, hPrefix,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨hm1, hmN, hqm | h2qm⟩
    · exact ⟨⟨hm1, hmN⟩, hqm⟩
    · exact ⟨⟨hm1, hmN⟩, (dvd_mul_left q 2).trans h2qm⟩
  · rintro ⟨⟨hm1, hmN⟩, hqm⟩
    exact ⟨hm1, hmN, Or.inl hqm⟩

lemma primePrefix_eq_single_of_card_one {N q : ℕ}
    (hq : q ∈ N.primeFactors) (hcard : (primePrefix N q).card = 1) :
    primePrefix N q = {q} := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hqMem := mem_primePrefix_self hq
  have hqp : q = p := by simpa [hp] using hqMem
  simpa [hqp] using hp

lemma QOptimal.eq_candidate_of_prefix_card_one
    {N q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hN : 2 ≤ N) (hNodd : ¬2 ∣ N) (hq : q ∈ N.primeFactors)
    (hcard : (primePrefix N q).card = 1)
    (hSupport : PrimitiveSupportedOn (insert 2 (primePrefix N q)) A) :
    A = candidate N q := by
  have hPrefix := primePrefix_eq_single_of_card_one hq hcard
  have hsubFilter : A ⊆ (interval N).filter (q ∣ ·) := by
    intro a ha
    refine Finset.mem_filter.mpr ⟨hA.1.1 ha, ?_⟩
    obtain ⟨g, hg, hga⟩ := exists_primitive_dvd hA.1.1 ha
    obtain ⟨p, hpPrime, hpg, hpN⟩ :=
      exists_prime_dvd_both_of_one_lt_gcd (hA.primitive_meets_N hg)
    have hg0 : g ≠ 0 := by
      have hgA := (mem_primitive.mp hg).1
      have := (mem_interval.mp (hA.1.1 hgA)).1
      omega
    have hpG : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hg0⟩
    rcases Finset.mem_insert.mp (hSupport g hg hpG) with hpTwo | hpPrefix
    · exact (hNodd (hpTwo ▸ hpN)).elim
    · have hpq : p = q := by simpa [hPrefix] using hpPrefix
      exact hpq ▸ hpg.trans hga
  have hsub : A ⊆ candidate N q := by
    simpa [candidate_eq_filter_dvd_of_primePrefix_eq_single hPrefix] using hsubFilter
  apply Finset.eq_of_subset_of_card_le hsub
  exact hA.2 (candidate N q)
    (QAdmissible.of_admissible (by omega) (candidate_admissible hq))

lemma QOptimal.topGenerator_has_other_endpoint
    {N c q : ℕ} {A : Finset ℕ} (hA : QOptimal N A)
    (hfix : ∀ p q, p.Prime → q.Prime → p < q → AllowedShift N p q →
      leftCompress p q A = A)
    (hNodd : ¬2 ∣ N) (hcN : c ∈ N.primeFactors)
    (hqN : q ∈ N.primeFactors) (hcq : c < q)
    (hSupport : PrimitiveSupportedOn (insert 2 (primePrefix N q)) A)
    (htop : 2 * q ∉ A) {g : ℕ} (hg : g ∈ primitive A)
    (hqg : q ∣ g) :
    ∃ p ∈ N.primeFactors, p ≠ q ∧ p ∣ g := by
  classical
  by_contra hOther
  have hc := Nat.prime_of_mem_primeFactors hcN
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hgA := (mem_primitive.mp hg).1
  have hg0 : g ≠ 0 := by
    have := (mem_interval.mp (hA.1.1 hgA)).1
    omega
  have hqG : q ∈ g.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hqg, hg0⟩
  have hprimeSupport : g.primeFactors ⊆ {2, q} := by
    intro p hp
    rcases Finset.mem_insert.mp (hSupport g hg hp) with hpTwo | hpPrefix
    · simp [hpTwo]
    · have hpN := primePrefix_subset N q hpPrefix
      have hpq : p = q := by
        by_contra hpq
        exact hOther ⟨p, hpN, hpq, Nat.dvd_of_mem_primeFactors hp⟩
      simp [hpq]
  have hqTwo : q ≠ 2 := by
    intro h
    exact hNodd (h ▸ Nat.dvd_of_mem_primeFactors hqN)
  have hsq := hA.squarefree_of_mem_primitive hg
  have hTwoNotG : 2 ∉ g.primeFactors := by
    intro hTwoG
    have hpfEq : g.primeFactors = {2, q} := by
      apply Finset.Subset.antisymm hprimeSupport
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
      rcases hp with rfl | rfl
      · exact hTwoG
      · exact hqG
    have hgEq : g = 2 * q := by
      calc
        g = ∏ p ∈ g.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hsq).symm
        _ = ∏ p ∈ ({2, q} : Finset ℕ), p := by rw [hpfEq]
        _ = 2 * q := by
          rw [Finset.prod_insert (by simpa [eq_comm] using hqTwo)]
          simp
    exact htop (hgEq ▸ hgA)
  have hpfEq : g.primeFactors = {q} := by
    apply Finset.Subset.antisymm
    · intro p hp
      have hp' := hprimeSupport hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp' ⊢
      rcases hp' with hpTwo | hpq
      · exact (hTwoNotG (hpTwo ▸ hp)).elim
      · exact hpq
    · intro p hp
      have hpq : p = q := by simpa using hp
      simpa [hpq] using hqG
  have hgEq : g = q := by
    calc
      g = ∏ p ∈ g.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ = ∏ p ∈ ({q} : Finset ℕ), p := by rw [hpfEq]
      _ = q := by simp
  have hcNotDvdQ : ¬c ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hcOne | hcEq
    · exact hc.ne_one hcOne
    · exact hcq.ne hcEq
  have hcMem : c ∈ A := by
    have hrep := hA.primePowerReplace_mem hfix hc hq hcq
      (Or.inl ⟨hcN, hqN⟩) (hgEq ▸ hgA) (by simp [hgEq]) hcNotDvdQ
    have hrepEq : primePowerReplace c q q = c := by
      rw [primePowerReplace_eq_ordCompl_mul_of_squarefree hq hq.squarefree]
      · have hcompl : ordCompl[q] q = 1 := by
          simpa using (Nat.ordCompl_self_pow (p := q) (k := 1) hq)
        simp [hcompl]
      · exact dvd_rfl
    simpa [hrepEq] using hrep
  have hpair := hA.1.2.2 hcMem (hgEq ▸ hgA) hcq.ne
  have hcCoprimeQ : Nat.Coprime c q :=
    hc.coprime_iff_not_dvd.mpr hcNotDvdQ
  change 1 < Nat.gcd c q at hpair
  rw [hcCoprimeQ.gcd_eq_one] at hpair
  omega

lemma prefixSupport_subset_coreScope (N q : ℕ) (hq2 : 2 ≤ q) :
    insert 2 (primePrefix N q) ⊆ coreScope N q := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hpPrefix
  · exact mem_coreScope.mpr (Or.inl ⟨Nat.prime_two, hq2⟩)
  · exact mem_coreScope.mpr (Or.inr (primePrefix_subset N q hpPrefix))

/-- For an odd endpoint, some Ahlswede--Khachatrian displayed candidate is
an auxiliary optimum.  The least support prefix either has one endpoint
prime, or the internal pull forces all doubled prefix primes and hence the
full displayed structure. -/
theorem exists_qOptimal_candidate_of_odd {N : ℕ}
    (hN : 2 ≤ N) (hNodd : ¬2 ∣ N) :
    ∃ q ∈ N.primeFactors, QOptimal N (candidate N q) := by
  classical
  have hN0 : N ≠ 0 := by omega
  obtain ⟨A₀, hA₀, hA₀Core⟩ :=
    exists_qOptimal_supported_on_coreScope_two N hN0
  let Good : ℕ → Prop := fun s ↦
    ∃ A, QOptimal N A ∧
      PrimitiveSupportedOn (insert 2 (primePrefix N s)) A
  have hGood : ∃ s, Good s := by
    refine ⟨N, A₀, hA₀, ?_⟩
    exact primitiveSupportedOn_prefixSupport_self hN0 hA₀Core
  let q := Nat.find hGood
  have hqGood : Good q := Nat.find_spec hGood
  have hqPos : 0 < q := by
    by_contra hq0
    have hqEq : q = 0 := by omega
    obtain ⟨A, hA, hASupport⟩ := hqGood
    exact no_qOptimal_supported_on_prefixSupport_zero hN hNodd hA
      (hqEq ▸ hASupport)
  have hqUsed : ∃ g ∈ primitive (Classical.choose hqGood),
      q ∈ g.primeFactors := by
    by_contra hnone
    push_neg at hnone
    have hPred : Good (q - 1) := by
      refine ⟨Classical.choose hqGood, (Classical.choose_spec hqGood).1, ?_⟩
      exact primitiveSupportedOn_prefixSupport_pred_of_absent
        (Classical.choose_spec hqGood).2 hnone
    have hmin := Nat.find_min' hGood hPred
    omega
  obtain ⟨g, hgPrim, hqG⟩ := hqUsed
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqG
  have hqTwo : q ≠ 2 := by
    intro hqEq
    obtain ⟨p, hpPrime, hpg, hpN⟩ := exists_prime_dvd_both_of_one_lt_gcd
      ((Classical.choose_spec hqGood).1.primitive_meets_N hgPrim)
    have hgA := (mem_primitive.mp hgPrim).1
    have hg0 : g ≠ 0 := by
      have := (mem_interval.mp ((Classical.choose_spec hqGood).1.1.1 hgA)).1
      omega
    have hpG : p ∈ g.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpg, hg0⟩
    rcases Finset.mem_insert.mp
        ((Classical.choose_spec hqGood).2 g hgPrim hpG) with hpTwo | hpPrefix
    · exact hNodd (hpTwo ▸ hpN)
    · have hple : p ≤ 2 := by
        simpa [hqEq] using (mem_primePrefix.mp hpPrefix).2
      have hpEq : p = 2 := Nat.le_antisymm hple hpPrime.two_le
      exact hNodd (hpEq ▸ hpN)
  have hqPrefix : q ∈ primePrefix N q := by
    rcases Finset.mem_insert.mp
        ((Classical.choose_spec hqGood).2 g hgPrim hqG) with h | h
    · exact (hqTwo h).elim
    · exact h
  have hqN : q ∈ N.primeFactors := primePrefix_subset N q hqPrefix
  have hq3 : 3 ≤ q := by
    have := hqPrime.two_le
    omega
  obtain ⟨A, hA, hASupport, hfix⟩ :=
    exists_supported_leftCompressed_qOptimal hqGood
      (fun p r hp hr hpr hallow hrSupport ↦
        prefixSupport_closed_under_allowed_shift hp hr hpr hallow hrSupport)
  have hprefixPos : 0 < (primePrefix N q).card :=
    Finset.card_pos.mpr ⟨q, hqPrefix⟩
  by_cases hprefixOne : (primePrefix N q).card = 1
  · refine ⟨q, hqN, ?_⟩
    have hEq := hA.eq_candidate_of_prefix_card_one hN hNodd hqN
      hprefixOne hASupport
    simpa [hEq] using hA
  · have hprefixTwo : 2 ≤ (primePrefix N q).card := by omega
    have hcExists : ∃ c ∈ primePrefix N q, c ≠ q := by
      by_contra hnone
      have hsub : primePrefix N q ⊆ {q} := by
        intro p hp
        have hpq : p = q := by
          by_contra hpq
          exact hnone ⟨p, hp, hpq⟩
        simpa [hpq]
      have hcard := Finset.card_le_card hsub
      simp at hcard
      omega
    obtain ⟨c, hcPrefix, hcqNe⟩ := hcExists
    have hcN : c ∈ N.primeFactors := primePrefix_subset N q hcPrefix
    have hcPrime : c.Prime := Nat.prime_of_mem_primeFactors hcN
    have hcq : c < q := by
      have := (mem_primePrefix.mp hcPrefix).2
      omega
    have htop : 2 * q ∈ A := by
      by_contra htop
      have hRWith : topGeneratorsWith q c A ⊆ primitive A := by
        intro x hx
        exact (mem_topGeneratorsWith.mp hx).1
      have hRWithout : topGeneratorsWithout q c A ⊆ primitive A := by
        intro x hx
        exact (mem_topGeneratorsWithout.mp hx).1
      have hqRWith : ∀ x ∈ topGeneratorsWith q c A, q ∣ x := by
        intro x hx
        exact (mem_topGeneratorsWith.mp hx).2.1
      have hqRWithout : ∀ x ∈ topGeneratorsWithout q c A, q ∣ x := by
        intro x hx
        exact (mem_topGeneratorsWithout.mp hx).2.1
      have hMeetWith : ∀ x ∈ pullGenerators q (topGeneratorsWith q c A),
          1 < Nat.gcd x N := by
        apply pullGenerators_meets_endpoint_of_other_prime hqPrime
        · intro x hx
          have hxA := (mem_primitive.mp (hRWith hx)).1
          have := (mem_interval.mp (hA.1.1 hxA)).1
          omega
        · intro x hx
          exact hA.topGenerator_has_other_endpoint hfix hNodd hcN hqN hcq
            hASupport htop (hRWith hx) (hqRWith x hx)
      have hMeetWithout :
          ∀ x ∈ pullGenerators q (topGeneratorsWithout q c A),
            1 < Nat.gcd x N := by
        apply pullGenerators_meets_endpoint_of_other_prime hqPrime
        · intro x hx
          have hxA := (mem_primitive.mp (hRWithout hx)).1
          have := (mem_interval.mp (hA.1.1 hxA)).1
          omega
        · intro x hx
          exact hA.topGenerator_has_other_endpoint hfix hNodd hcN hqN hcq
            hASupport htop (hRWithout hx) (hqRWithout x hx)
      have hCore : PrimitiveSupportedOn (coreScope N q) A := by
        intro x hx p hp
        exact prefixSupport_subset_coreScope N q hqPrime.two_le (hASupport x hx hp)
      have hDoubleWith := generatedRemainder_pull_doubling_of_supported
        (R := topGeneratorsWith q c A) hN0 hA hqPrime hq3
        (fun x hx ↦ (mem_lowerGenerators.mp hx).1) hRWith
        (fun x hx ↦ (mem_lowerGenerators.mp hx).2) hqRWith hCore
      have hDoubleWithout := generatedRemainder_pull_doubling_of_supported
        (R := topGeneratorsWithout q c A) hN0 hA hqPrime hq3
        (fun x hx ↦ (mem_lowerGenerators.mp hx).1) hRWithout
        (fun x hx ↦ (mem_lowerGenerators.mp hx).2) hqRWithout hCore
      have hPulled := hA.optimal_internal_pull_of_doubling hfix hcPrime
        hqPrime hcq hcN hqN hMeetWith hMeetWithout
        hDoubleWith hDoubleWithout
      rcases hPulled with hPulled | hPulled
      · have hPred : Good (q - 1) := ⟨_, hPulled,
          pulled_optimal_supported_on_prefixSupport_pred hA hqPrime hqTwo
            hASupport hRWith hqRWith hPulled⟩
        have hmin := Nat.find_min' hGood hPred
        omega
      · have hPred : Good (q - 1) := ⟨_, hPulled,
          pulled_optimal_supported_on_prefixSupport_pred hA hqPrime hqTwo
            hASupport hRWithout hqRWithout hPulled⟩
        have hmin := Nat.find_min' hGood hPred
        omega
    have htwo := hA.two_mul_mem_of_compressed_top hfix hNodd hqN htop
    have hEq : A = candidate N q := hA.eq_candidate_of_support hqN hNodd
      hprefixTwo
      (fun x hx p hp ↦ Finset.mem_insert.mp (hASupport x hx hp)) htwo
    refine ⟨q, hqN, ?_⟩
    simpa [hEq] using hA

/-- **Erdős Problem 534 (Ahlswede--Khachatrian).**  For every `N ≥ 2`,
one of the displayed prefix candidates is admissible and has cardinality at
least that of every admissible subset of `[1,N]` containing `N`. -/
theorem erdos_534_aux (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      Admissible N (candidate N q) ∧
        ∀ A, Admissible N A → A.card ≤ (candidate N q).card := by
  by_cases hEven : 2 ∣ N
  · have hTwo : 2 ∈ N.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hEven, by omega⟩
    exact ⟨2, hTwo, erdos_534_even hN hEven⟩
  · obtain ⟨q, hq, hopt⟩ := exists_qOptimal_candidate_of_odd hN hEven
    exact ⟨q, hq, erdos_534_of_qOptimal_candidate hN hq hopt⟩

end Erdos534
