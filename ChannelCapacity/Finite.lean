/- 
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import ChannelCapacity.Capacity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# ChannelCapacity.Finite

Finite-alphabet capacity-achieving prior uniqueness.

This file specializes the general development to finite measurable alphabets. In that setting,
Shannon entropy gives an explicit formula for mutual information, so continuity and strict
concavity can be proved internally without passing abstract topology or semicontinuity hypotheses
through the public theorem statement.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace ChannelCapacity

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

namespace ProbabilityMeasure

/-- Shannon entropy on a finite measurable alphabet, in nats. -/
noncomputable def entropy (μ : ProbabilityMeasure α) : ℝ :=
  ∑ a, Real.negMulLog ((μ.toMeasure {a}).toReal)

end ProbabilityMeasure

namespace Kernel

/-- A concrete finite non-degeneracy condition: the row matrix has trivial kernel over `ℝ`. -/
def RowMatrixFullRank (k : Kernel α β) : Prop :=
  Function.Injective fun w : α → ℝ =>
    fun b => ∑ a, w a * (k a {b}).toReal

end Kernel

section DiscreteKL

omit [Fintype α] in
theorem toMeasure_eq_count_withDensity (μ : ProbabilityMeasure α) :
    [Countable α] → μ.toMeasure = Measure.count.withDensity (fun a => μ.toMeasure {a}) := by
  intro _instCountable
  ext s hs
  rw [MeasureTheory.withDensity_apply _ hs, ← MeasureTheory.lintegral_indicator hs,
    MeasureTheory.lintegral_count]
  simpa using (μ.toMeasure.tsum_indicator_apply_singleton s hs).symm

omit [Fintype α] in
theorem rnDeriv_count_ae (μ : ProbabilityMeasure α) :
    [Countable α] →
      μ.toMeasure.rnDeriv Measure.count =ᵐ[Measure.count] fun a => μ.toMeasure {a} := by
  intro _instCountable
  have hcount :
      Measure.count.withDensity (fun a : α => μ.toMeasure {a}) = μ.toMeasure :=
    (toMeasure_eq_count_withDensity (μ := μ)).symm
  simpa [hcount] using
    (Measure.rnDeriv_withDensity
      (ν := Measure.count)
      (f := fun a : α => μ.toMeasure {a})
      (measurable_of_countable (fun a : α => μ.toMeasure {a})))

omit [Fintype α] [MeasurableSingletonClass α] in
theorem klFun_singletonMass (μ : ProbabilityMeasure α) (a : α) :
    InformationTheory.klFun ((μ.toMeasure {a}).toReal) =
      1 - (μ.toMeasure {a}).toReal - Real.negMulLog ((μ.toMeasure {a}).toReal) := by
  rw [InformationTheory.klFun, Real.negMulLog]
  ring

theorem toReal_klDiv_count (μ : ProbabilityMeasure α) :
    (InformationTheory.klDiv μ.toMeasure Measure.count).toReal =
      (Fintype.card α : ℝ) - 1 - ProbabilityMeasure.entropy μ := by
  let _instCountable : Countable α := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := by
    rw [toMeasure_eq_count_withDensity (μ := μ)]
    exact withDensity_absolutelyContinuous _ _
  have h_rn : ∀ a : α, μ.toMeasure.rnDeriv Measure.count a = μ.toMeasure {a} := by
    simpa using (Measure.ae_count_iff.mp (rnDeriv_count_ae (μ := μ)))
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun h_ac, MeasureTheory.integral_count]
  simp_rw [h_rn, klFun_singletonMass (μ := μ)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  have hprob : ∑ a, (μ.toMeasure {a}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]
  rw [ProbabilityMeasure.entropy, hprob, Finset.card_univ]
  ring

end DiscreteKL

end ChannelCapacity
