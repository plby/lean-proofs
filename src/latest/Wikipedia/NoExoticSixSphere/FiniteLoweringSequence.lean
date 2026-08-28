import Wikipedia.NoExoticSixSphere.FiniteLoweringStep

/-!
# A finite controlled lowering homotopy

The induction constructs every endpoint family and its native relative
homotopy. The cover and energy budgets then rule out a high-energy final
point: it must have been selected by one of the lowering steps and cannot
recover enough energy in the remaining steps.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [PseudoMetricSpace Y]

namespace Prefix

variable {energy : Y → ℝ} {admissible : Set Y} {p₀ : C(M, Y)}
  {F : ℕ → Set Y} {k : ℕ → ℝ} {floor A cap ξ ζ ρ : ℝ} {n : ℕ}
  (P : Prefix energy admissible p₀ F k floor A cap ξ ζ ρ n)

theorem endpoint_lt_of_cover (hξ : 0 ≤ ξ) (target : ℝ)
    (hgap : A + (n : ℝ) * ξ ≤ target)
    (hthreshold : ∀ j < n, k j + (n : ℝ) * ξ ≤ target)
    (hcover : ∀ x, A ≤ energy (p₀ x) → ∃ j < n, p₀ x ∈ F j) :
    ∀ x, energy (P.family n x) < target := by
  intro x
  by_contra hh
  have hfinish : target ≤ energy (P.family n x) := le_of_not_gt hh
  have hback (j : ℕ) (hj : j ≤ n) :
      energy (P.family n x) ≤ energy (P.family j x) + (n : ℝ) * ξ := by
    have he := FiniteEnergyMovement.energy_le_after energy (fun j ↦ P.family j x) n ξ
      (fun j hj ↦ P.gain j hj x) hj le_rfl
    have hnum : ((n - j : ℕ) : ℝ) * ξ ≤ (n : ℝ) * ξ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n j) hξ
    exact he.trans (add_le_add le_rfl hnum)
  have hhigh (j : ℕ) (hj : j ≤ n) : A ≤ energy (P.family j x) := by
    have he := hback j hj
    linarith
  have hstart : A ≤ energy (p₀ x) := by
    simpa only [P.initial] using hhigh 0 (Nat.zero_le n)
  obtain ⟨j, hj, hx⟩ := hcover x hstart
  have hlow := P.lowered j hj x hx (hhigh j hj.le)
  have hraise : energy (P.family (j + 1) x) + (n : ℝ) * ξ < k j + (n : ℝ) * ξ := by
    linarith
  have hend := (hback (j + 1) (Nat.succ_le_of_lt hj)).trans_lt
    (hraise.trans_le (hthreshold j hj))
  exact (not_lt_of_ge hfinish) hend

end Prefix

variable [CompactSpace M] [T2Space Y]

theorem nonempty_prefix (energy : Y → ℝ) (admissible : Set Y)
    (henergy : ContinuousOn energy admissible) (p₀ : C(M, Y))
    (hp₀ : ∀ x, p₀ x ∈ admissible) (n : ℕ) (F V : ℕ → Set Y) (k : ℕ → ℝ)
    (floor A B cap ξ ζ ρ : ℝ) (hξ : 0 ≤ ξ) (hρ : 0 ≤ ρ)
    (hstart : ∀ x, energy (p₀ x) ≤ B) (hbudget : B - A + 2 * (n : ℝ) * ξ ≤ 2 * ζ)
    (hF : ∀ j < n, IsCompact (F j))
    (hfit : ∀ j < n, ∀ y ∈ F j, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ V j)
    (hstep : ∀ j < n, StepProperty (M := M) energy admissible (V j) floor (k j) cap ξ ζ ρ) :
    Nonempty (Prefix energy admissible p₀ F k floor A cap ξ ζ ρ n) := by
  have hall : ∀ i ≤ n, Nonempty (Prefix energy admissible p₀ F k floor A cap ξ ζ ρ i) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨initialPrefix energy admissible p₀ F k floor A cap ξ ζ ρ hp₀⟩
    | succ i ih =>
      intro hi
      have hin : i < n := Nat.lt_of_succ_le hi
      obtain ⟨P⟩ := ih hin.le
      exact P.nonempty_succ hin hξ hρ henergy B hstart hbudget
        (V i) (hF i hin) (hfit i hin) (hstep i hin)
  exact hall n le_rfl

theorem exists_finite_lowering (energy : Y → ℝ) (admissible : Set Y)
    (henergy : ContinuousOn energy admissible) (p₀ : C(M, Y))
    (hp₀ : ∀ x, p₀ x ∈ admissible) (n : ℕ) (F V : ℕ → Set Y) (k : ℕ → ℝ)
    (floor A B cap ξ ζ ρ target : ℝ) (hξ : 0 ≤ ξ) (hρ : 0 ≤ ρ)
    (hstart : ∀ x, energy (p₀ x) ≤ B) (hbudget : B - A + 2 * (n : ℝ) * ξ ≤ 2 * ζ)
    (hF : ∀ j < n, IsCompact (F j))
    (hfit : ∀ j < n, ∀ y ∈ F j, ∀ z, dist z y ≤ (n : ℝ) * ρ → z ∈ V j)
    (hstep : ∀ j < n, StepProperty (M := M) energy admissible (V j) floor (k j) cap ξ ζ ρ)
    (hgap : A + (n : ℝ) * ξ ≤ target)
    (hthreshold : ∀ j < n, k j + (n : ℝ) * ξ ≤ target)
    (hcover : ∀ x, A ≤ energy (p₀ x) → ∃ j < n, p₀ x ∈ F j) :
    ∃ q : C(M, Y), (∀ x, energy (q x) < target) ∧
      ∃ G : ContinuousMap.HomotopyRel p₀ q {x | energy (p₀ x) ≤ floor},
        ∀ t x, G (t, x) ∈ admissible ∧ energy (G (t, x)) ≤ max (energy (p₀ x)) cap := by
  obtain ⟨P⟩ := nonempty_prefix energy admissible henergy p₀ hp₀ n F V k
    floor A B cap ξ ζ ρ hξ hρ hstart hbudget hF hfit hstep
  exact ⟨P.family n, P.endpoint_lt_of_cover hξ target hgap hthreshold hcover,
    P.homotopy, P.control⟩

end NoExoticSixSphere.FiniteControlledLowering
