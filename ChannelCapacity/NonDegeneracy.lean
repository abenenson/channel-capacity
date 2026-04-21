/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.Basic

/-!
# ChannelCapacity.NonDegeneracy

Correct non-degeneracy conditions for uniqueness in the prior variable.

- `Kernel.priorPushforward`
- `Kernel.InjectivePriorPushforward`
- `Kernel.RowSeparating`
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

/-- The output prior map `p ↦ Σ_x p(x) k(x, ·)`. -/
noncomputable def priorPushforward (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : ProbabilityMeasure β :=
  outputPrior k p

/-- Pairwise-distinct rows of a kernel. This is weaker than injective prior pushforward. -/
def RowSeparating (k : Kernel α β) : Prop :=
  ∀ ⦃a a' : α⦄, a ≠ a' → k a ≠ k a'

/-- The correct non-degeneracy hypothesis for uniqueness in the prior variable. -/
def InjectivePriorPushforward (k : Kernel α β) [IsMarkovKernel k] : Prop :=
  Function.Injective (priorPushforward k)

/-- Measure-theoretic non-degeneracy bundle for the capacity theorem. Each prior's rows are
absolutely continuous with respect to the induced output marginal, and the joint KL divergence is
finite against any reference measure that dominates the rows for that prior. -/
structure WellConditionedForCapacity (k : Kernel α β) [IsMarkovKernel k] : Prop where
  hRowAC : ∀ p : ProbabilityMeasure α,
    ∀ᵐ x ∂p.toMeasure, k x ≪ (outputPrior k p).toMeasure
  hFiniteRefKL : ∀ (p : ProbabilityMeasure α) (ν : Measure β),
    (∀ᵐ x ∂p.toMeasure, k x ≪ ν) →
      InformationTheory.klDiv (p.toMeasure ⊗ₘ k) (p.toMeasure ⊗ₘ Kernel.const _ ν) ≠ ∞

@[simp]
theorem priorPushforward_dirac (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    Kernel.priorPushforward k (ProbabilityMeasure.dirac a) =
      (⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩ :
        ProbabilityMeasure β) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simpa [priorPushforward, outputPrior] using
    congrArg (fun μ : Measure β => μ s) (Measure.dirac_bind k.measurable a)

theorem priorPushforward_convexCombination (k : Kernel α β) [IsMarkovKernel k]
    (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    Kernel.priorPushforward k (ProbabilityMeasure.convexCombination p q t ht) =
      ProbabilityMeasure.convexCombination
        (Kernel.priorPushforward k p)
        (Kernel.priorPushforward k q)
        t ht := by
  apply ProbabilityMeasure.toMeasure_injective
  change k ∘ₘ (ProbabilityMeasure.convexCombination p q t ht).toMeasure =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [ProbabilityMeasure.convexCombination_toMeasure, Measure.comp_add]
  change k ∘ₘ ((t : ENNReal) • p.toMeasure) +
      k ∘ₘ ((((1 : NNReal) - t : NNReal) : ENNReal) • q.toMeasure) =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [Measure.comp_smul, Measure.comp_smul, ProbabilityMeasure.convexCombination_toMeasure]
  simp [Kernel.priorPushforward, outputPrior]
  change ((((1 : NNReal) - t : NNReal) : ENNReal) • (k ∘ₘ q.toMeasure)) =
    ((((1 : NNReal) - t : NNReal) : ENNReal) • (k ∘ₘ q.toMeasure))
  rfl

@[simp]
theorem priorPushforward_id (p : ProbabilityMeasure α) :
    Kernel.priorPushforward (Kernel.id : Kernel α α) p = p := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simp [priorPushforward, outputPrior]

theorem id_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward (Kernel.id : Kernel α α) := by
  intro p q hpq
  simpa using hpq

end Kernel

end ChannelCapacity
