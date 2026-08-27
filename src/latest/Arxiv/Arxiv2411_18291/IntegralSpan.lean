import Arxiv.Arxiv2411_18291.LocalDecoderOn
import Mathlib.Algebra.BigOperators.Pi

/-!
# Integral generation and lifting with local decoders

This is the integer-linear-algebra step at the end of the integral absorber
proof (Section 6). Local decoders turn a coordinatewise multiple of
`N = r! * choose q r` into a clique vector supported on a prescribed family.
Thus a representation modulo `N` can be corrected to an exact representation.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

theorem boundary_sum {ι R : Type*} [AddCommMonoid R]
    (s : Finset ι) (Φ : ι → Block V q → R) :
    boundary r (∑ i ∈ s, Φ i) = ∑ i ∈ s, boundary r (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [sum_insert hi, boundary_add, ih]

theorem boundary_mul {R : Type*} [Semiring R] (c : R) (Φ : Block V q → R) :
    boundary r (fun Q => c * Φ Q) = fun e => c * boundary r Φ e := by
  funext e
  unfold boundary
  rw [mul_sum]
  apply sum_congr rfl
  intro Q _
  split_ifs <;> simp

/-- The boundary vectors generated over the integers by a prescribed clique
family. Witnesses have no coefficients outside that family. -/
def GeneratedBy (F : Finset (Block V q)) (J : Block V r → ℤ) : Prop :=
  ∃ Φ : Block V q → ℤ, boundary r Φ = J ∧ ∀ Q, Q ∉ F → Φ Q = 0

theorem GeneratedBy.integrallyDecomposable {F : Finset (Block V q)}
    {J : Block V r → ℤ} (h : GeneratedBy F J) : IntegrallyDecomposable q J := by
  obtain ⟨Φ, hΦ, _⟩ := h
  exact ⟨Φ, hΦ⟩

theorem GeneratedBy.zero (F : Finset (Block V q)) :
    GeneratedBy (r := r) F 0 := ⟨0, boundary_zero, fun _ _ => rfl⟩

theorem GeneratedBy.mono {F F' : Finset (Block V q)} {J : Block V r → ℤ}
    (h : GeneratedBy F J) (hF : F ⊆ F') : GeneratedBy F' J := by
  obtain ⟨Φ, hΦ, hs⟩ := h
  exact ⟨Φ, hΦ, fun Q hQ => hs Q (fun hQF => hQ (hF hQF))⟩

theorem GeneratedBy.add {F : Finset (Block V q)} {J K : Block V r → ℤ}
    (hJ : GeneratedBy F J) (hK : GeneratedBy F K) : GeneratedBy F (J + K) := by
  obtain ⟨Φ, hΦ, hsΦ⟩ := hJ
  obtain ⟨Ψ, hΨ, hsΨ⟩ := hK
  refine ⟨Φ + Ψ, by rw [boundary_add, hΦ, hΨ], ?_⟩
  intro Q hQ
  simp [hsΦ Q hQ, hsΨ Q hQ]

theorem GeneratedBy.sub {F : Finset (Block V q)} {J K : Block V r → ℤ}
    (hJ : GeneratedBy F J) (hK : GeneratedBy F K) : GeneratedBy F (J - K) := by
  obtain ⟨Φ, hΦ, hsΦ⟩ := hJ
  obtain ⟨Ψ, hΨ, hsΨ⟩ := hK
  refine ⟨Φ - Ψ, by rw [boundary_sub, hΦ, hΨ], ?_⟩
  intro Q hQ
  simp [hsΦ Q hQ, hsΨ Q hQ]

theorem GeneratedBy.mul {F : Finset (Block V q)} {J : Block V r → ℤ}
    (h : GeneratedBy F J) (c : ℤ) : GeneratedBy F (fun e => c * J e) := by
  obtain ⟨Φ, hΦ, hs⟩ := h
  refine ⟨fun Q => c * Φ Q, by rw [boundary_mul, hΦ], ?_⟩
  intro Q hQ
  simp [hs Q hQ]

theorem GeneratedBy.sum {ι : Type*} {F : Finset (Block V q)}
    (s : Finset ι) (J : ι → Block V r → ℤ) (h : ∀ i ∈ s, GeneratedBy F (J i)) :
    GeneratedBy F (∑ i ∈ s, J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GeneratedBy.zero F
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add
      (ih fun j hj => h j (mem_insert_of_mem hj))

/-- If the family decodes every edge in `E` with multiplier `N`, it generates
every `N`-divisible signed edge vector supported on `E`. -/
theorem generatedBy_of_edge_decoders {F : Finset (Block V q)} (E : Hypergraph V r)
    (N : ℤ) (hdecode : ∀ e ∈ E,
      GeneratedBy F (fun e' => if e' = e then N else 0))
    (J : Block V r → ℤ) (hsupport : ∀ e, e ∉ E → J e = 0)
    (hdiv : ∀ e, N ∣ J e) : GeneratedBy F J := by
  let c : Block V r → ℤ := fun e => Classical.choose (hdiv e)
  have hc (e : Block V r) : J e = N * c e := Classical.choose_spec (hdiv e)
  have hgen : GeneratedBy F
      (∑ e ∈ E, fun e' => c e * (if e' = e then N else 0)) :=
    GeneratedBy.sum E _ (fun e he => (hdecode e he).mul (c e))
  have heq : (∑ e ∈ E, fun e' => c e * (if e' = e then N else 0)) = J := by
    funext e'
    simp only [sum_apply, mul_ite, mul_zero]
    rw [sum_ite_eq]
    by_cases he : e' ∈ E
    · rw [if_pos he, mul_comm, ← hc]
    · rw [if_neg he, hsupport e' he]
  rwa [heq] at hgen

/-- Local complete `(q+r)`-sets provide the decoders required by the
integer-generation step of the absorber proof. -/
theorem generatedBy_of_local_decoders (hqr : r ≤ q)
    (F : Finset (Block V q)) (E : Hypergraph V r) (Z : Block V r → Finset V)
    (hZ : ∀ e ∈ E, (Z e).card = q + r)
    (heZ : ∀ e ∈ E, e.val ⊆ Z e)
    (hF : ∀ e ∈ E, ∀ Q : Block V q, Q.val ⊆ Z e → Q ∈ F)
    (J : Block V r → ℤ) (hsupport : ∀ e, e ∉ E → J e = 0)
    (hdiv : ∀ e, ((r.factorial * q.choose r : ℕ) : ℤ) ∣ J e) : GeneratedBy F J := by
  apply generatedBy_of_edge_decoders E ((r.factorial * q.choose r : ℕ) : ℤ) _ J hsupport hdiv
  intro e he
  obtain ⟨Ψ, hΨ, hsΨ, _⟩ := local_decoder_on (Z e) (hZ e he) hqr e (heZ e he)
  refine ⟨Ψ, hΨ, ?_⟩
  intro Q hQ
  exact hsΨ Q (fun hQZ => hQ (hF e he Q hQZ))

/-- Correct an integer representation modulo `N` using local edge decoders.
This records the exact correction argument; the existence of the sparse
generating family remains a separate construction. -/
theorem GeneratedBy.lift_modulo {F : Finset (Block V q)} (E : Hypergraph V r)
    (N : ℤ) (hdecode : ∀ e ∈ E,
      GeneratedBy F (fun e' => if e' = e then N else 0))
    {J K : Block V r → ℤ} (hK : GeneratedBy F K)
    (hsupport : ∀ e, e ∉ E → J e - K e = 0)
    (hmod : ∀ e, N ∣ J e - K e) : GeneratedBy F J := by
  have hJK := generatedBy_of_edge_decoders E N hdecode (J - K) hsupport hmod
  simpa only [sub_add_cancel] using hJK.add hK

end Arxiv2411_18291
