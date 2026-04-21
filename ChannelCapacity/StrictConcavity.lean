/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.NonDegeneracy

/-!
# ChannelCapacity.StrictConcavity

Strict concavity infrastructure on the simplex of probability measures.

This file uses an explicit convex-combination operation on `ProbabilityMeasure α`, rather than
`StrictConcaveOn`, because the ambient type of probability measures is not itself a vector space.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- A strict concavity predicate tailored to probability measures. -/
def StrictlyConcave (f : ProbabilityMeasure α → ℝ) : Prop :=
  ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
    (ht_pos : 0 < t) (ht_lt_one : t < 1),
    f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
      (t : ℝ) * f p + (1 - (t : ℝ)) * f q

/-- Global maximizer of a function on probability measures. -/
def IsMaximizer (f : ProbabilityMeasure α → ℝ) (p : ProbabilityMeasure α) : Prop :=
  ∀ q, f q ≤ f p

theorem eq_of_isMaximizer_of_strictlyConcave {f : ProbabilityMeasure α → ℝ}
    (hStrict : StrictlyConcave f) {p q : ProbabilityMeasure α}
    (hp : IsMaximizer f p) (hq : IsMaximizer f q) : p = q := by
  by_contra hne
  let t : NNReal := 1 / 2
  have ht_pos : 0 < t := by norm_num [t]
  have ht_lt_one : t < 1 := by norm_num [t]
  have hMixLe :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) ≤ f p :=
    hp _
  have hpq : f p = f q := le_antisymm (hq p) (hp q)
  have hMixGt :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) >
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q := by
    simpa [t] using hStrict p q hne t ht_pos ht_lt_one
  have hMixGt' :
      f (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) > f p := by
    have hRewrite :
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q = f p := by
      calc
        (t : ℝ) * f p + (1 - (t : ℝ)) * f q =
            (t : ℝ) * f p + (1 - (t : ℝ)) * f p := by simp [hpq]
        _ = ((t : ℝ) + (1 - (t : ℝ))) * f p := by ring
        _ = f p := by ring
    simpa [hRewrite] using hMixGt
  exact (not_lt_of_ge hMixLe) hMixGt'

end ProbabilityMeasure

namespace ChannelCapacity

open ProbabilityMeasure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

def StrictlyConcaveMutualInformation (k : Kernel α β) [IsMarkovKernel k]
    (_h : Kernel.InjectivePriorPushforward k) : Prop :=
  ProbabilityMeasure.StrictlyConcave fun p => mutualInformation p k

end Kernel

end ChannelCapacity
