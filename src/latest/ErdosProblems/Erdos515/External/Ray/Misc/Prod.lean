module
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Set.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic

/-!
## Lemmas about `A × B`
-/

open Function (uncurry curry)
open Prod (swap)
open Metric (ball)
open scoped Topology
noncomputable section

variable {A B C : Type}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `swap` is an involution -/
public theorem swap_swap (s : Set (A × B)) : swap '' (swap '' s) = s := by
  ext x; simp only [Set.mem_image, Prod.exists]; constructor
  · intro ⟨a,b,⟨⟨c,d,e,f⟩,g⟩⟩; rw [←g, ←f]; simpa only [swap]
  · intro m; exact ⟨x.2,x.1,⟨x.1,x.2,m,rfl⟩,rfl⟩

public theorem flip_swap (f : A → B → C) : uncurry (flip f) = uncurry f ∘ swap := rfl

public theorem differentiable_swap [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedSpace 𝕜 A]
    [NormedSpace 𝕜 B] : Differentiable 𝕜 (swap : A × B → B × A) := fun _ ↦
  DifferentiableAt.prodMk (differentiable_snd _) (differentiable_fst _)

public theorem differentiableOn_swap {s : Set (A × B)} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 A] [NormedSpace 𝕜 B] : DifferentiableOn 𝕜 swap s :=
  differentiable_swap.differentiableOn

/-- `swap` is an open map -/
public theorem isOpen_swap {s : Set (A × B)} [TopologicalSpace A] [TopologicalSpace B] :
    IsOpen s → IsOpen (swap '' s) := by
  rw [Set.image_swap_eq_preimage_swap]; exact IsOpen.preimage continuous_swap

public theorem swap_mem {a : A} {b : B} {s : Set (A × B)} : (b, a) ∈ swap '' s ↔ (a, b) ∈ s := by
  aesop

public theorem swap_mem' {x : A × B} {s : Set (B × A)} : x ∈ swap '' s ↔ swap x ∈ s := by
  have h := @swap_mem _ _ x.snd x.fst s; simp at h ⊢; exact h

public theorem ball_prod_same' [PseudoMetricSpace A] [PseudoMetricSpace B] (x : A × B) (r : ℝ) :
    ball x r = ball x.fst r ×ˢ ball x.snd r := by
  have s := ball_prod_same x.fst x.snd r
  simp only [Prod.mk.eta] at s; exact s.symm

public theorem ball_swap [PseudoMetricSpace A] [PseudoMetricSpace B] {x : A × B} {r : ℝ} :
    ball x.swap r = swap '' ball x r := by
  apply Set.ext; intro y
  rw [swap_mem', Metric.mem_ball, Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
  simp only [max_lt_iff, Prod.fst_swap, Prod.snd_swap, and_comm]

public theorem dist_swap [PseudoMetricSpace A] [PseudoMetricSpace B] {x y : A × B} :
    dist x.swap y.swap = dist x y := by
  rw [Prod.dist_eq, Prod.dist_eq]; simp only [Prod.fst_swap, Prod.snd_swap, max_comm]
