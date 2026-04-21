/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.NonDegeneracy

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.WithDensity

/-!
# ChannelCapacity.Discharged

Concrete density-regularity hypotheses for discharging the generic capacity theorem.

This module introduces the compact-Polish density class used by the discharged theorem program:
rows admit a common reference density, the density is jointly continuous, and it is strictly
positive everywhere.
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

end ContinuousPositiveDensity

end Kernel

end ChannelCapacity
