import ErdosProblems.Erdos587.GAPImageSums
import ErdosProblems.Erdos587.StableHighFoldModels

/-!
Subgroup-stable high-fold GAP models constructed from interval containment.
The density and finite-index hypotheses of the abstract removal mechanism
are supplied by centered coordinates and the robust high-fold model.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem exists_subset_stable_centeredCoordinates
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (h r M d₀ : ℕ) (hM : 1 ≤ M) (hdim : P.rank ≤ d₀)
    (hwidth : ∀ i, M ≤ h * P.length i + 1)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + (M ^ d₀ + 1) * r →
      2 * (P.dilate h).boxCard < M * (h • insert 0 D).card) :
    ∃ B ⊆ A, A.card ≤ B.card + M ^ d₀ * r ∧
      (generatedSubgroup P.centeredCoordinates B).FiniteIndex ∧
      (generatedSubgroup P.centeredCoordinates B).index ≤ M ^ d₀ ∧
      ∀ D ⊆ B, B.card ≤ D.card + r →
        generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates B := by
  let φ : Unit → ℤ → (Fin P.rank → ℤ) := fun _ => P.centeredCoordinates
  have hindex (D : Finset ℤ) (hDA : D ⊆ A)
      (hcost : A.card ≤ D.card + (M ^ d₀ + 1) * r) :
      (generatedSubgroup P.centeredCoordinates D).FiniteIndex ∧
        (generatedSubgroup P.centeredCoordinates D).index ≤ M ^ d₀ := by
    obtain ⟨hfin, hidx⟩ := P.finiteIndex_of_highFold_density D hzero (hDA.trans hA)
      h M (hdense D hDA hcost) hwidth
    exact ⟨hfin, hidx.trans (pow_le_pow_right₀ hM hdim)⟩
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_generatedSubgroups
    φ A r (M ^ d₀) (fun D hDA hcost _i => hindex D hDA (by
      simpa only [Fintype.card_unit, one_mul] using hcost))
  simp only [Fintype.card_unit, one_mul] at hcost
  have hbudget : A.card ≤ B.card + (M ^ d₀ + 1) * r := by
    exact hcost.trans (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_right r (Nat.le_succ _)))
  obtain ⟨hfin, hidx⟩ := hindex B hBA hbudget
  refine ⟨B, hBA, hcost, hfin, hidx, ?_⟩
  intro D hDB hremove
  exact hstable D hDB hremove ()

/-- An interval input gives a genuinely constructed large subset whose
centered coordinate subgroup is unchanged by every permitted further
deletion. All constants are explicit functions of the polynomial exponent. -/
theorem exists_subgroupStable_highFold_model (A : Finset ℤ) (L b t r : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) (ht : 0 < t)
    (hwindow : t + t ≤ L) (hambient : L ≤ t * b)
    (hscale : 4 * freimanTSizeFactor (2 ^ (b + 3)) 2 ≤ 2 ^ t) :
    let F := freimanTSizeFactor (2 ^ (b + 3)) 2
    let M := 4 * F
    let K := M ^ (b + 1)
    ∃ B ⊆ A, A.card ≤ B.card + ((6 * (L + 1) ^ 2 + 3) * (K + 1) + K) * r ∧
      ∃ k, t ≤ k ∧ k < t + t ∧
        ∃ Q : GeneralizedAP, Q.rank ≤ b + 1 ∧
          (∀ i, 0 < Q.length i) ∧ Q.TProper (2 ^ k) ∧
          (0 : ℤ) ∈ Q.carrier ∧ insert 0 B ⊆ Q.carrier ∧
          (∀ i, M ≤ 2 ^ k * Q.length i + 1) ∧
          (generatedSubgroup Q.centeredCoordinates B).FiniteIndex ∧
          (generatedSubgroup Q.centeredCoordinates B).index ≤ K ∧
          (∀ D ⊆ B, B.card ≤ D.card + r →
            generatedSubgroup Q.centeredCoordinates D = generatedSubgroup Q.centeredCoordinates B) ∧
          ∀ D ⊆ B, B.card ≤ D.card + r →
            2 * (Q.dilate (2 ^ k)).boxCard < M * (dyadicSumsetWithZero D k).card := by
  let F := freimanTSizeFactor (2 ^ (b + 3)) 2
  let M := 4 * F
  let K := M ^ (b + 1)
  obtain ⟨C, hCA, hcostC, k, htk, hkt, Q, hrank, hpos, hproper, hzero,
      hCQ, hbox, hwidth, hdense⟩ :=
    exists_stable_highFold_model A L b t ((K + 1) * r) hA ht hwindow hambient hscale
  have hF : 0 < F := by
    have hposBox : 0 < (Q.dilate (2 ^ k)).boxCard :=
      Finset.prod_pos (fun i _hi => Nat.succ_pos _)
    by_contra hnot
    have hz : F = 0 := by omega
    change (Q.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero C k).card at hbox
    rw [hz, zero_mul] at hbox
    omega
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hCQ' : C ⊆ Q.carrier := (Finset.subset_insert 0 C).trans hCQ
  obtain ⟨B, hBC, hcostB, hfinite, hindex, hstable⟩ :=
    exists_subset_stable_centeredCoordinates Q C hzero hCQ' (2 ^ k) r M (b + 1)
      hM hrank hwidth (fun D hDC hremove => hdense D hDC hremove)
  have hcost : A.card ≤ B.card + ((6 * (L + 1) ^ 2 + 3) * (K + 1) + K) * r := by
    calc
      A.card ≤ C.card + (6 * (L + 1) ^ 2 + 3) * ((K + 1) * r) := hcostC
      _ ≤ (B.card + K * r) + (6 * (L + 1) ^ 2 + 3) * ((K + 1) * r) :=
        Nat.add_le_add_right hcostB _
      _ = B.card + ((6 * (L + 1) ^ 2 + 3) * (K + 1) + K) * r := by ring
  have hBQ : insert 0 B ⊆ Q.carrier := (Finset.insert_subset_insert 0 hBC).trans hCQ
  refine ⟨B, hBC.trans hCA, hcost, k, htk, hkt, Q, hrank, hpos, hproper, hzero,
    hBQ, hwidth, hfinite, hindex, hstable, ?_⟩
  intro D hDB hremove
  apply hdense D (hDB.trans hBC)
  calc
    C.card ≤ B.card + K * r := hcostB
    _ ≤ (D.card + r) + K * r := Nat.add_le_add_right hremove _
    _ = D.card + (K + 1) * r := by ring

end Erdos587.CFP
