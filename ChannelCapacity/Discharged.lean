/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.NonDegeneracy

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.WithDensity

/-!
# ChannelCapacity.Discharged

Concrete density-regularity hypotheses for discharging the generic capacity theorem.

This module introduces the compact-Polish density class used by the discharged theorem program:
rows admit a common reference density, the density is jointly continuous, and it is strictly
positive everywhere.

## WIP note

Milestone 3 is blocked at the current abstraction boundary. The field
`Kernel.WellConditionedForCapacity.hFiniteRefKL` quantifies over every reference measure `ν` that
dominates the relevant rows. Under the concrete class in this file, we can control KL against the
fixed dominating reference from the class, and against output marginals that are themselves
equivalent to that reference. What does not follow from the present assumptions is finiteness
against an arbitrary dominating `ν`: the class gives `ν₀ ≪ ν`, but not the extra integrability
needed to control the Radon-Nikodym correction from `ν₀` to `ν`.

Attempts made:
- reduce the joint KL to a rowwise integral via `klDiv_compProd_right`
- use compactness of `α × β` and continuity of the density to obtain a uniform bound on the
  fixed-reference `klFun` integrand
- inspect the Radon-Nikodym / chain-rule API to lift that bound to arbitrary dominating references;
  this is where the missing control on the reference change appears
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]

namespace Kernel

/-- A concrete compact-Polish regularity class for a Markov kernel: all rows have a common density
with respect to `ν`, this density is jointly continuous, and it is strictly positive. -/
structure ContinuousPositiveDensity
    (k : Kernel α β) (ν : Measure β) [IsMarkovKernel k] where
  density : α → β → NNReal
  continuous_density : Continuous (Function.uncurry density)
  eq_withDensity : ∀ a, k a = ν.withDensity (fun b => (density a b : ℝ≥0∞))
  density_pos : ∀ a b, 0 < density a b

namespace ContinuousPositiveDensity

variable {k : Kernel α β} [IsMarkovKernel k] {ν : Measure β}

theorem row_eq_withDensity (h : ContinuousPositiveDensity k ν) (a : α) :
    k a = ν.withDensity (fun b => (h.density a b : ENNReal)) :=
  h.eq_withDensity a

theorem row_absolutelyContinuous_ref (h : ContinuousPositiveDensity k ν) (a : α) :
    k a ≪ ν := by
  rw [h.row_eq_withDensity a]
  simpa using MeasureTheory.withDensity_absolutelyContinuous ν
    (fun b => (h.density a b : ENNReal))

theorem density_ne_zero (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    h.density a b ≠ 0 :=
  ne_of_gt (h.density_pos a b)

theorem density_ennreal_pos (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    0 < (h.density a b : ENNReal) :=
  ENNReal.coe_pos.mpr (h.density_pos a b)

theorem density_ennreal_ne_zero (h : ContinuousPositiveDensity k ν) (a : α) (b : β) :
    (h.density a b : ENNReal) ≠ 0 :=
  ne_of_gt (h.density_ennreal_pos a b)

section OutputPrior

variable [CompactSpace α] [PolishSpace α] [PolishSpace β] [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace α] [OpensMeasurableSpace β] [IsFiniteMeasure ν]

noncomputable def outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    β → ENNReal :=
  fun b => ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure

omit [CompactSpace α] [BorelSpace α] [BorelSpace β] in
theorem aemeasurable_outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    AEMeasurable (h.outputDensity p) ν := by
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod ν) := by
    simpa [Function.uncurry] using (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  exact hbase.lintegral_prod_left (μ := p.toMeasure) (ν := ν)

omit [CompactSpace α] [BorelSpace α] [BorelSpace β] in
theorem outputPrior_eq_withDensity_outputDensity
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    (outputPrior k p).toMeasure = ν.withDensity (h.outputDensity p) := by
  ext s hs
  rw [outputPrior_toMeasure, Measure.bind_apply hs k.aemeasurable,
    MeasureTheory.withDensity_apply _ hs]
  simp_rw [h.row_eq_withDensity]
  simp_rw [MeasureTheory.withDensity_apply _ hs]
  have hbase :
      AEMeasurable
        (Function.uncurry fun a b => (h.density a b : ENNReal))
        (p.toMeasure.prod (ν.restrict s)) := by
    simpa [Function.uncurry] using (ENNReal.continuous_coe.comp h.continuous_density).aemeasurable
  simpa [Function.uncurry] using
    (lintegral_lintegral_swap (μ := p.toMeasure) (ν := ν.restrict s)
      (f := fun a b => (h.density a b : ENNReal)) hbase)

omit [PolishSpace α] [PolishSpace β] [BorelSpace α] [BorelSpace β]
  [OpensMeasurableSpace α] [OpensMeasurableSpace β] [IsFiniteMeasure ν] in
theorem outputDensity_pos (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) (b : β) :
    0 < h.outputDensity p b := by
  letI : Nonempty α := p.nonempty
  have hcont : Continuous fun a : α => h.density a b := by
    have hpair : Continuous fun a : α => (a, b) := by
      fun_prop
    simpa [Function.uncurry] using h.continuous_density.comp hpair
  obtain ⟨a0, -, ha0⟩ := IsCompact.exists_isMinOn (α := NNReal)
    (β := α) isCompact_univ Set.univ_nonempty hcont.continuousOn
  have ha0' : ∀ a : α, h.density a0 b ≤ h.density a b :=
    isMinOn_univ_iff.mp ha0
  have hle : ∀ a : α, (h.density a0 b : ENNReal) ≤ (h.density a b : ENNReal) := by
    intro a
    exact_mod_cast ha0' a
  have hconst_le :
      (h.density a0 b : ENNReal) ≤ h.outputDensity p b := by
    calc
      (h.density a0 b : ENNReal) = ∫⁻ a, (h.density a0 b : ENNReal) ∂p.toMeasure := by simp
      _ ≤ ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure := lintegral_mono hle
      _ = h.outputDensity p b := rfl
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (h.density_pos a0 b)) hconst_le

omit [BorelSpace α] [BorelSpace β] in
theorem ae_row_absolutelyContinuous_outputPrior
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∀ᵐ a ∂p.toMeasure, k a ≪ (outputPrior k p).toMeasure := by
  have hν_ac_out :
      ν ≪ (outputPrior k p).toMeasure := by
    have hν_ac_withDensity :
        ν ≪ ν.withDensity (h.outputDensity p) :=
      MeasureTheory.withDensity_absolutelyContinuous'
        (h.aemeasurable_outputDensity p)
        (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using hν_ac_withDensity
  exact Filter.Eventually.of_forall fun a =>
    (h.row_absolutelyContinuous_ref a).trans hν_ac_out

end OutputPrior

end ContinuousPositiveDensity

end Kernel

end ChannelCapacity
