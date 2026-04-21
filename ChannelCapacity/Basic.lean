/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# ChannelCapacity.Basic

Measure-theoretic primitives for Shannon mutual information over a Markov kernel.

This file keeps the surface small:

- `ProbabilityMeasure.convexCombination`
- `ProbabilityMeasure.dirac`
- `jointLaw`
- `outputPrior`
- `independentJointLaw`
- `mutualInformation`

The mutual information is defined directly from Mathlib's `klDiv`.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Convex combination of two probability measures. -/
noncomputable def convexCombination (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) :
    ProbabilityMeasure Ω :=
  ⟨t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure, by
    refine ⟨?_⟩
    calc
      (t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure) Set.univ =
          (t • μ.toMeasure) Set.univ + (((1 : NNReal) - t) • ν.toMeasure) Set.univ := by
            rw [Measure.add_apply]
      _ = t • (μ.toMeasure Set.univ) + ((1 : NNReal) - t) • (ν.toMeasure Set.univ) := by
            simp [Measure.smul_apply]
      _ = t • (1 : ENNReal) + ((1 : NNReal) - t) • (1 : ENNReal) := by simp
      _ = 1 := by
            change (t : ENNReal) * 1 + (((1 : NNReal) - t : NNReal) : ENNReal) * 1 = 1
            simp
            exact_mod_cast add_tsub_cancel_of_le ht⟩

@[simp]
theorem convexCombination_toMeasure (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) :
    (convexCombination μ ν t ht).toMeasure =
      t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure :=
  rfl

@[simp]
theorem convexCombination_apply (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal))
    {s : Set Ω} (hs : MeasurableSet s) :
    (convexCombination μ ν t ht).toMeasure s =
      (t : ENNReal) * μ.toMeasure s + (((1 : NNReal) - t : NNReal) : ENNReal) * ν.toMeasure s := by
  simpa [convexCombination_toMeasure, Measure.add_apply, Measure.smul_apply, hs]

/-- Dirac probability measure. -/
noncomputable def dirac (x : Ω) : ProbabilityMeasure Ω :=
  ⟨Measure.dirac x, by infer_instance⟩

@[simp]
theorem dirac_toMeasure (x : Ω) : (dirac x).toMeasure = Measure.dirac x :=
  rfl

end ProbabilityMeasure

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The output prior induced by pushing a prior through a Markov kernel. -/
noncomputable def outputPrior (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ProbabilityMeasure β :=
  ⟨k ∘ₘ p.toMeasure, by infer_instance⟩

@[simp]
theorem outputPrior_toMeasure (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = k ∘ₘ p.toMeasure :=
  rfl

/-- The joint law `p ⊗ k` on `α × β`. -/
noncomputable def jointLaw (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ProbabilityMeasure (α × β) :=
  ⟨p.toMeasure ⊗ₘ k, by infer_instance⟩

@[simp]
theorem jointLaw_toMeasure (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    (jointLaw k p).toMeasure = p.toMeasure ⊗ₘ k :=
  rfl

/-- The independent coupling with the same input prior and induced output prior. -/
noncomputable def independentJointLaw (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : ProbabilityMeasure (α × β) :=
  let q := outputPrior k p
  ⟨p.toMeasure ⊗ₘ Kernel.const α q.toMeasure, by infer_instance⟩

@[simp]
theorem independentJointLaw_toMeasure (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) :
    (independentJointLaw k p).toMeasure =
      p.toMeasure ⊗ₘ Kernel.const α (outputPrior k p).toMeasure :=
  rfl

noncomputable def mutualInformation (p : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] : ℝ :=
  (InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure).toReal

end ChannelCapacity
