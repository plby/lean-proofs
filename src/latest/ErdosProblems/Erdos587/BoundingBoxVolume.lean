import ErdosProblems.Erdos587.NVDevelopment
import ErdosProblems.Erdos587.VolumeStability

/-!
Minimum coefficient-box volumes of GAPs covering a finite natural set and zero.
The index `d` allows rank at most `d+1`; collapsed coordinates need not be padded.
No properness is assumed in this minimization.
-/

namespace Erdos587.CFP

def IsBoundingGAP (d : ℕ) (A : Finset ℕ) (Q : GeneralizedAP) : Prop :=
  Q.rank ≤ d + 1 ∧ (0 : ℤ) ∈ Q.carrier ∧ ∀ a ∈ A, (a : ℤ) ∈ Q.carrier

theorem interval_isBoundingGAP (d N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, a ≤ N) :
    IsBoundingGAP d A (GeneralizedAP.ofNatAP 0 1 N) := by
  have hmem (a : ℕ) (ha : a ≤ N) :
      (a : ℤ) ∈ (GeneralizedAP.ofNatAP 0 1 N).carrier := by
    apply GeneralizedAP.natCast_mem_carrier_ofNatAP.mpr
    exact Erdos13Additive.mem_natAP.mpr ⟨a, by omega, by simp⟩
  exact ⟨by simp, hmem 0 (Nat.zero_le _), fun a ha => hmem a (hA a ha)⟩

theorem exists_boundingGAP_volume (d : ℕ) (A : Finset ℕ) :
    ∃ v : ℕ, ∃ Q : GeneralizedAP, IsBoundingGAP d A Q ∧ Q.boxCard = v := by
  refine ⟨A.sup id + 1, GeneralizedAP.ofNatAP 0 1 (A.sup id), ?_,
    GeneralizedAP.boxCard_ofNatAP 0 1 (A.sup id)⟩
  exact interval_isBoundingGAP d (A.sup id) A (fun a ha => Finset.le_sup (f := id) ha)

noncomputable def boundingBoxVolume (d : ℕ) (A : Finset ℕ) : ℕ := by
  classical
  exact Nat.find (exists_boundingGAP_volume d A)

theorem exists_minimal_boundingGAP (d : ℕ) (A : Finset ℕ) :
    ∃ Q : GeneralizedAP, IsBoundingGAP d A Q ∧ Q.boxCard = boundingBoxVolume d A := by
  classical
  exact Nat.find_spec (exists_boundingGAP_volume d A)

theorem boundingBoxVolume_le {d : ℕ} {A : Finset ℕ} {Q : GeneralizedAP}
    (hQ : IsBoundingGAP d A Q) : boundingBoxVolume d A ≤ Q.boxCard := by
  classical
  exact Nat.find_min' (exists_boundingGAP_volume d A) ⟨Q, hQ, rfl⟩

theorem boundingBoxVolume_pos (d : ℕ) (A : Finset ℕ) : 0 < boundingBoxVolume d A := by
  obtain ⟨Q, _hQ, hvol⟩ := exists_minimal_boundingGAP d A
  rw [← hvol]
  exact Finset.prod_pos (fun i _hi => Nat.succ_pos (Q.length i))

theorem boundingBoxVolume_mono (d : ℕ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    boundingBoxVolume d A ≤ boundingBoxVolume d B := by
  obtain ⟨Q, hQ, hvol⟩ := exists_minimal_boundingGAP d B
  have hQA : IsBoundingGAP d A Q := ⟨hQ.1, hQ.2.1, fun a ha => hQ.2.2 a (hAB ha)⟩
  exact (boundingBoxVolume_le hQA).trans hvol.le

theorem boundingBoxVolume_le_of_bound (d N : ℕ) (A : Finset ℕ)
    (hA : ∀ a ∈ A, a ≤ N) : boundingBoxVolume d A ≤ N + 1 := by
  have hh := boundingBoxVolume_le (interval_isBoundingGAP d N A hA)
  simpa only [GeneralizedAP.boxCard_ofNatAP] using hh

theorem boundingBoxVolume_antitone_rank {d e : ℕ} (hde : d ≤ e) (A : Finset ℕ) :
    boundingBoxVolume e A ≤ boundingBoxVolume d A := by
  obtain ⟨Q, hQ, hvol⟩ := exists_minimal_boundingGAP d A
  have hQE : IsBoundingGAP e A Q :=
    ⟨hQ.1.trans (Nat.add_le_add_right hde 1), hQ.2⟩
  exact (boundingBoxVolume_le hQE).trans hvol.le

theorem boundingGAP_card_le_boxCard {d : ℕ} {A : Finset ℕ} {Q : GeneralizedAP}
    (hQ : IsBoundingGAP d A Q) : (insert 0 A).card ≤ Q.boxCard := by
  have hcard : (insert 0 A).card ≤ Q.carrier.card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ => (a : ℤ))
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hQ.2.1
      · exact hQ.2.2 a ha
    · intro a _ha b _hb hab
      change (a : ℤ) = (b : ℤ) at hab
      exact_mod_cast hab
  have hupper : Q.carrier.card ≤ Q.boxCard := by
    calc
      Q.carrier.card ≤ (Finset.univ : Finset Q.Param).card := Finset.card_image_le
      _ = Q.boxCard := by simp [GeneralizedAP.Param, GeneralizedAP.boxCard]
  exact hcard.trans hupper

theorem boundingBoxVolume_card_lower (d : ℕ) (A : Finset ℕ) :
    (insert 0 A).card ≤ boundingBoxVolume d A := by
  obtain ⟨Q, hQ, hvol⟩ := exists_minimal_boundingGAP d A
  exact (boundingGAP_card_le_boxCard hQ).trans hvol.le

/-- A genuinely constructed large subset has stable minimum GAP volumes,
simultaneously for all ranks up to `d₀`. -/
theorem exists_subset_stable_boundingBoxVolumes (A : Finset ℕ) (r N d₀ : ℕ)
    (hA : ∀ a ∈ A, a ≤ N) :
    ∃ B ⊆ A, A.card ≤ B.card + (3 * (d₀ * (Nat.log 2 (N + 1) + 1) + 1)) * r ∧
      ∀ D ⊆ B, B.card ≤ D.card + r →
        ∀ d < d₀, 3 * boundingBoxVolume d B < 4 * boundingBoxVolume d D := by
  let V : Fin d₀ → Finset ℕ → ℕ := fun i => boundingBoxVolume i.val
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_volumes_log_bound V A r (N + 1)
    (fun B _hBA i => boundingBoxVolume_pos i.val B)
    (fun _B _hBA _D hDB i => boundingBoxVolume_mono i.val hDB)
    (fun i => boundingBoxVolume_le_of_bound i.val N A hA)
  refine ⟨B, hBA, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hcost
  · intro D hDB hremove d hd
    exact hstable D hDB hremove ⟨d, hd⟩

end Erdos587.CFP
