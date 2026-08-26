/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.CertificateExhaustionBridge
import ErdosProblems.Erdos76.PackedBucketCertificate

/-!
# Packed strong certificates and graph exhaustions

This module joins independently checked packed-natural certificates to the
generic missing-edge exhaustion.  Coverage mentions only a packed blob and
its decoded graph mask; the generated development never constructs one large
list of decoded `PackingCert` values.
-/

namespace Erdos76
namespace CertificateChecker
namespace PackedBucketCertificate

open CertificateExhaustion

/-- Every final missing-edge representative has a packed certificate whose
decoded dense graph is its complement.  Extra blobs are harmless. -/
def MasksCover {n : ℕ} (reps : Array (BitVec (edgeCount n)))
    (records : List Blob) : Prop :=
  ∀ k : Fin reps.size, ∃ blob ∈ records,
    ∃ entry : BucketCertificate.Entry n,
      decode n blob = some entry ∧
        CertificateExhaustion.ComplementMasks entry.1 reps[k]

/-- Validate the strong bucket certificate and its intended missing-edge mask
in one decoder pass. -/
def checkStrongFor {n : ℕ} (a : ℕ) (missing : BitVec (edgeCount n))
    (blob : Blob) : Bool :=
  match decode n blob with
  | none => false
  | some entry =>
      BucketCertificate.checkStrong (graphOfBits entry.1) a entry.2 &&
        decide (CertificateExhaustion.ComplementMasks entry.1 missing)

/-- Cheap alignment-only leaf.  Strong-record modules may reuse an already
proved `checkStrong` fact and check only this decoded mask condition. -/
def checkMaskFor {n : ℕ} (missing : BitVec (edgeCount n))
    (blob : Blob) : Bool :=
  match decode n blob with
  | none => false
  | some entry =>
      decide (CertificateExhaustion.ComplementMasks entry.1 missing)

theorem checkStrongFor_of_checkStrong_of_checkMask {n : ℕ} (a : ℕ)
    (missing : BitVec (edgeCount n)) (blob : Blob)
    (hstrong : checkStrong n a blob = true)
    (hmask : checkMaskFor missing blob = true) :
    checkStrongFor a missing blob = true := by
  cases hdecode : decode n blob with
  | none => simp [PackedBucketCertificate.checkStrong, hdecode] at hstrong
  | some entry =>
      have hs : BucketCertificate.checkStrong
          (graphOfBits entry.1) a entry.2 = true := by
        simpa [PackedBucketCertificate.checkStrong, hdecode] using hstrong
      have hm : decide (CertificateExhaustion.ComplementMasks
          entry.1 missing) = true := by
        simpa [checkMaskFor, hdecode] using hmask
      simp [checkStrongFor, hdecode, hs, hm]

theorem checkStrongFor_sound {n : ℕ} (a : ℕ)
    (missing : BitVec (edgeCount n)) (blob : Blob)
    (hpairs : PackingCert.PairIndexValid n)
    (h : checkStrongFor a missing blob = true) :
    ∃ entry : BucketCertificate.Entry n,
      decode n blob = some entry ∧
        HasStrongFractionalPacking (graphOfBits entry.1) (a : ℝ) ∧
          CertificateExhaustion.ComplementMasks entry.1 missing := by
  cases hdecode : decode n blob with
  | none => simp [checkStrongFor, hdecode] at h
  | some entry =>
      have hh : BucketCertificate.checkStrong
            (graphOfBits entry.1) a entry.2 = true ∧
          decide (CertificateExhaustion.ComplementMasks
            entry.1 missing) = true := by
        simpa [checkStrongFor, hdecode] using h
      refine ⟨entry, rfl, ?_, by simpa using hh.2⟩
      exact BucketCertificate.checkStrong_sound hpairs a entry.2 hh.1

/-- Order-aligned proof-only aggregate.  Production generators emit records
in the same order as the final exhaustion representatives, so each leaf is
checked once and internal nodes perform no search or decoding. -/
inductive AlignedValid (n a : ℕ) :
    List (BitVec (edgeCount n)) → List Blob → Prop where
  | nil : AlignedValid n a [] []
  | cons {missing : BitVec (edgeCount n)} {blob : Blob}
      {missingTail : List (BitVec (edgeCount n))} {blobTail : List Blob}
      (head : checkStrongFor a missing blob = true)
      (tail : AlignedValid n a missingTail blobTail) :
      AlignedValid n a (missing :: missingTail) (blob :: blobTail)

theorem AlignedValid.cons_of_checks {n a : ℕ}
    {missing : BitVec (edgeCount n)} {blob : Blob}
    {missingTail : List (BitVec (edgeCount n))} {blobTail : List Blob}
    (hstrong : checkStrong n a blob = true)
    (hmask : checkMaskFor missing blob = true)
    (tail : AlignedValid n a missingTail blobTail) :
    AlignedValid n a (missing :: missingTail) (blob :: blobTail) :=
  AlignedValid.cons
    (checkStrongFor_of_checkStrong_of_checkMask a missing blob hstrong hmask) tail

theorem AlignedValid.append {n a : ℕ}
    {missingLeft missingRight : List (BitVec (edgeCount n))}
    {blobLeft blobRight : List Blob}
    (hleft : AlignedValid n a missingLeft blobLeft)
    (hright : AlignedValid n a missingRight blobRight) :
    AlignedValid n a (missingLeft ++ missingRight)
      (blobLeft ++ blobRight) := by
  induction hleft with
  | nil => exact hright
  | cons head tail ih => exact AlignedValid.cons head ih

theorem AlignedValid.recordsValid {n a : ℕ}
    {missing : List (BitVec (edgeCount n))} {records : List Blob}
    (h : AlignedValid n a missing records) : RecordsValid n a records := by
  induction h with
  | nil => exact recordsValid_nil n a
  | @cons missing blob missingTail blobTail head tail ih =>
      apply RecordsValid.cons
      · cases hdecode : decode n blob with
        | none => simp [checkStrongFor, hdecode] at head
        | some entry =>
            have hh : BucketCertificate.checkStrong
                (graphOfBits entry.1) a entry.2 = true := by
              have hpair : BucketCertificate.checkStrong
                    (graphOfBits entry.1) a entry.2 = true ∧
                  decide (CertificateExhaustion.ComplementMasks
                    entry.1 missing) = true := by
                simpa [checkStrongFor, hdecode] using head
              exact hpair.1
            simpa [PackedBucketCertificate.checkStrong, hdecode] using hh
      · exact ih

theorem AlignedValid.listMasksCover {n a : ℕ}
    {missing : List (BitVec (edgeCount n))} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (h : AlignedValid n a missing records) :
    ∀ mask ∈ missing, ∃ blob ∈ records,
      ∃ entry : BucketCertificate.Entry n,
        decode n blob = some entry ∧
          CertificateExhaustion.ComplementMasks entry.1 mask := by
  induction h with
  | nil => simp
  | @cons first blob missingTail blobTail head tail ih =>
      intro mask hmask
      simp only [List.mem_cons] at hmask
      rcases hmask with rfl | hmask
      · obtain ⟨entry, hdecode, hw, hmasks⟩ :=
          checkStrongFor_sound a _ blob hpairs head
        exact ⟨blob, by simp, entry, hdecode, hmasks⟩
      · obtain ⟨next, hnext, entry, hdecode, hmasks⟩ := ih mask hmask
        exact ⟨next, by simp [hnext], entry, hdecode, hmasks⟩

theorem AlignedValid.masksCover {n a : ℕ}
    {reps : Array (BitVec (edgeCount n))} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (h : AlignedValid n a reps.toList records) :
    MasksCover reps records := by
  intro k
  apply h.listMasksCover hpairs reps[k]
  simpa using Array.getElem_mem_toList (xs := reps) k.isLt

/-- A checked collection of packed bucket certificates, together with mask
coverage, supplies the strong packing required for every graph represented by
an accepted exhaustion. -/
theorem recordsValid_exhaustion_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n} {a : ℕ} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (hd : d.check = true)
    (hcover : MasksCover (d.level d.steps.size) records)
    (hvalid : RecordsValid n a records)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = d.steps.size) :
    HasStrongFractionalPacking G (a : ℝ) := by
  have hfinal : ∀ k : Fin (d.level d.steps.size).size,
      HasStrongFractionalPacking
        ((graphOfBits (d.level d.steps.size)[k])ᶜ) (a : ℝ) := by
    intro k
    obtain ⟨blob, hblob, entry, hdecode, hmasks⟩ := hcover k
    obtain ⟨decoded, hdecoded, hw⟩ :=
      checkStrong_sound n a blob hpairs (hvalid blob hblob)
    have hentry : decoded = entry := by
      rw [hdecode] at hdecoded
      exact (Option.some.inj hdecoded).symm
    subst decoded
    have hgraph := hmasks.graphOfBits_eq_compl
    simpa only [hgraph] using hw
  have hmissing := d.check_transport_atTarget hd
    (fun H ↦ HasStrongFractionalPacking Hᶜ (a : ℝ)) hfinal (by
      intro A B ⟨f⟩ hB
      exact HasStrongFractionalPacking.transportIso hB
        (CertificateExhaustion.complIso f))
    Gᶜ hcard
  simpa using hmissing

/-- Intermediate-level form used by the five values of `a` at each order.
One checked exhaustion through its largest target supplies every earlier
level; no prefix data or transition proof is duplicated. -/
theorem recordsValid_level_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n} {target a : ℕ} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (hd : d.Valid) (htarget : target ≤ d.steps.size)
    (hcover : MasksCover (d.level target) records)
    (hvalid : RecordsValid n a records)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = target) :
    HasStrongFractionalPacking G (a : ℝ) := by
  have hfinal : ∀ k : Fin (d.level target).size,
      HasStrongFractionalPacking
        ((graphOfBits (d.level target)[k])ᶜ) (a : ℝ) := by
    intro k
    obtain ⟨blob, hblob, entry, hdecode, hmasks⟩ := hcover k
    obtain ⟨decoded, hdecoded, hw⟩ :=
      checkStrong_sound n a blob hpairs (hvalid blob hblob)
    have hentry : decoded = entry := by
      rw [hdecode] at hdecoded
      exact (Option.some.inj hdecoded).symm
    subst decoded
    have hgraph := hmasks.graphOfBits_eq_compl
    simpa only [hgraph] using hw
  have hrepresented : IsRepresented (d.level target) Gᶜ := by
    have h := hd.representsGraph Gᶜ (by simpa [hcard] using htarget)
    simpa only [hcard] using h
  obtain ⟨k, ⟨f⟩⟩ := hrepresented
  have hw := hfinal k
  simpa using HasStrongFractionalPacking.transportIso hw
    (CertificateExhaustion.complIso f)

/-- Linear, order-aligned production endpoint. -/
theorem alignedValid_exhaustion_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n} {a : ℕ} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (hd : d.check = true)
    (hvalid : AlignedValid n a (d.level d.steps.size).toList records)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = d.steps.size) :
    HasStrongFractionalPacking G (a : ℝ) :=
  recordsValid_exhaustion_sound hpairs hd (hvalid.masksCover hpairs)
    hvalid.recordsValid G hcard

/-- Linear, order-aligned endpoint at any intermediate exhaustion level. -/
theorem alignedValid_level_sound {n : ℕ} [NeZero n]
    {d : ExhaustionData n} {target a : ℕ} {records : List Blob}
    (hpairs : PackingCert.PairIndexValid n)
    (hd : d.Valid) (htarget : target ≤ d.steps.size)
    (hvalid : AlignedValid n a (d.level target).toList records)
    (G : SimpleGraph (Fin n))
    (hcard : Gᶜ.edgeSet.ncard = target) :
    HasStrongFractionalPacking G (a : ℝ) :=
  recordsValid_level_sound hpairs hd htarget (hvalid.masksCover hpairs)
    hvalid.recordsValid G hcard

end PackedBucketCertificate
end CertificateChecker
end Erdos76
