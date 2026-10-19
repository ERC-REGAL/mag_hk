import MagHK.ParameterContinuity
import MagHK.NormLimits

/-!
Continuity and actual equal-norm existence for the bounded example. All
integrals below use the concrete orbital defined in Noninteracting.lean.
The domination, endpoint limits, and positivity are proved in NormLimits.
-/

noncomputable section
namespace MagHK.Noninteracting

open Set Filter MeasureTheory MagHK.ParameterContinuity
open scoped Topology

theorem radialNormF_continuousOn : ContinuousOn radialNormF (Ici (0 : ℝ)) := by
  intro t ht
  change 0 ≤ t at ht
  change Tendsto radialNormF (𝓝[Ici (0 : ℝ)] t) (𝓝 (radialNormF t))
  apply tendsto_integral_filter_of_dominated_convergence (radialDensityF 0)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (radialDensityF_integrable s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold radialDensityF; positivity)]
    exact (radial_integrand_bounds s r hs hr.le).2.1
  · exact base_density_integrable
  · exact Eventually.of_forall (fun r =>
      ((profileF_parameter_tendsto r t ht).pow 2).mul_const r)

theorem radialNormG_continuousOn : ContinuousOn radialNormG (Ici (0 : ℝ)) := by
  intro t ht
  change 0 ≤ t at ht
  change Tendsto radialNormG (𝓝[Ici (0 : ℝ)] t) (𝓝 (radialNormG t))
  have hbound : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] t, s < t + 1 :=
    (eventually_lt_nhds (show t < t + 1 by linarith)).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r => (t + 1) * weightedBaseDensity r)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (radialNormG_integrable s hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hbound] with s hs hst
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs0 : 0 ≤ s := hs
    have hr0 : 0 ≤ r := hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      s * profileR r ^ 2 * profileF s r ^ 2 * r ≤ s * weightedBaseDensity r := by
        simpa only [weightedBaseDensity, mul_assoc] using
          (radial_integrand_bounds s r hs hr.le).2.2
      _ ≤ (t + 1) * weightedBaseDensity r :=
        mul_le_mul_of_nonneg_right (le_of_lt hst) (by unfold weightedBaseDensity; positivity)
  · exact weighted_base_density_integrable.const_mul (t + 1)
  · apply Eventually.of_forall
    intro r
    have hs : Tendsto (fun s : ℝ => s) (𝓝[Ici (0 : ℝ)] t) (𝓝 t) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    exact ((hs.mul_const (profileR r ^ 2)).mul
      ((profileF_parameter_tendsto r t ht).pow 2)).mul_const r

theorem radialNormG_at_zero : radialNormG 0 = 0 := by
  simp [radialNormG]

/-- The parameter whose existence is asserted in the bounded construction.
No continuity, sign, or limiting assertion is left as a hypothesis. -/
theorem exists_bounded_parameter :
    ∃ t : ℝ, 0 < t ∧ radialNormF t = radialNormG t ∧ 0 < radialNormF t := by
  obtain ⟨b, hb, hright⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and radialNorms_order_atTop).exists
  have hb0 : 0 ≤ b := by linarith
  have hF : ContinuousOn radialNormF (Icc 0 b) :=
    radialNormF_continuousOn.mono Icc_subset_Ici_self
  have hG : ContinuousOn radialNormG (Icc 0 b) :=
    radialNormG_continuousOn.mono Icc_subset_Ici_self
  have hzero : 0 < radialNormF 0 := radialNormF_pos 0 (by norm_num)
  have hz : (0 : ℝ) ∈ Icc ((radialNormF - radialNormG) b)
      ((radialNormF - radialNormG) 0) := by
    simp only [Pi.sub_apply, mem_Icc, radialNormG_at_zero]
    constructor <;> linarith
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hb0 (hF.sub hG) hz
  have hequal : radialNormF t = radialNormG t := by
    simpa only [Pi.sub_apply, sub_eq_zero] using heq
  have htne : t ≠ 0 := by
    intro h
    subst t
    rw [radialNormG_at_zero] at hequal
    linarith
  exact ⟨t, lt_of_le_of_ne ht.1 (Ne.symm htne), hequal, radialNormF_pos t ht.1⟩

theorem exists_bounded_parameter_integrals :
    ∃ t : ℝ, 0 < t ∧
      (∫ r in Ioi (0 : ℝ), profileF t r ^ 2 * r) =
        (∫ r in Ioi (0 : ℝ), t * profileR r ^ 2 * profileF t r ^ 2 * r) ∧
      0 < ∫ r in Ioi (0 : ℝ), profileF t r ^ 2 * r := by
  simpa only [radialNormF, radialNormG, radialDensityF] using exists_bounded_parameter

end MagHK.Noninteracting
