import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The Gaussian normalization parameter is proved to exist from its actual
improper integral. No continuity or endpoint-limit assertion is assumed.
The max functions extend the integrand continuously to all real parameters.
They disappear for the positive parameters used in the manuscript.
-/

namespace MagHK.GaussianNormalization

open MeasureTheory Set Filter Real
open scoped Topology

noncomputable def kernel (t s : ℝ) : ℝ :=
  exp (-s) / (1 + max t 0 * max s 0)

noncomputable def normIntegral (t : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), kernel t s

theorem denominator_pos (t s : ℝ) : 0 < 1 + max t 0 * max s 0 := by
  positivity

theorem kernel_continuous_s (t : ℝ) : Continuous (kernel t) := by
  unfold kernel
  exact (continuous_exp.comp continuous_neg).div
    (continuous_const.add (continuous_const.mul (continuous_id.max continuous_const)))
    (fun s => ne_of_gt (denominator_pos t s))

theorem kernel_continuous_t (s : ℝ) : Continuous (fun t => kernel t s) := by
  unfold kernel
  exact continuous_const.div
    (continuous_const.add ((continuous_id.max continuous_const).mul continuous_const))
    (fun t => ne_of_gt (denominator_pos t s))

theorem kernel_bound (t s : ℝ) : ‖kernel t s‖ ≤ exp (-s) := by
  have h : 0 ≤ max t 0 * max s 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hp : 0 < exp (-s) := exp_pos _
  unfold kernel
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hp (denominator_pos t s))]
  exact (div_le_self hp.le (by linarith))

theorem kernel_integrable (t : ℝ) : IntegrableOn (kernel t) (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
    (kernel_continuous_s t).aestronglyMeasurable
  exact ae_of_all _ (kernel_bound t)

theorem normIntegral_continuous : Continuous normIntegral := by
  apply continuous_of_dominated
    (fun t => (kernel_continuous_s t).aestronglyMeasurable)
    (fun t => ae_of_all _ (kernel_bound t)) (integrableOn_exp_neg_Ioi 0)
  exact ae_of_all _ kernel_continuous_t

theorem normIntegral_zero : normIntegral 0 = 1 := by
  simpa [normIntegral, kernel] using integral_exp_neg_Ioi_zero

theorem kernel_strictAnti (a b s : ℝ) (ha : 0 ≤ a) (hab : a < b) (hs : 0 < s) :
    kernel b s < kernel a s := by
  have hb : 0 ≤ b := le_trans ha hab.le
  unfold kernel
  rw [max_eq_left ha, max_eq_left hb, max_eq_left hs.le]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have h := mul_pos (exp_pos (-s)) (mul_pos (sub_pos.mpr hab) hs)
  nlinarith

theorem normIntegral_strictAnti : StrictAntiOn normIntegral (Ici 0) := by
  intro a ha b hb hab
  have hi := (kernel_integrable a).sub (kernel_integrable b)
  have hp : 0 < ∫ s in Ioi (0 : ℝ), kernel a s - kernel b s := by
    apply (integral_pos_iff_support_of_nonneg_ae _ hi).mpr
    · have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun s => kernel a s - kernel b s) := by
        intro s hs
        exact ne_of_gt (sub_pos.mpr (kernel_strictAnti a b s ha hab hs))
      have hm : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) := by
        simp [Measure.restrict_apply measurableSet_Ioi, Real.volume_Ioi]
      exact lt_of_lt_of_le hm (measure_mono hsub)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (sub_pos.mpr (kernel_strictAnti a b s ha hab hs)).le
  rw [integral_sub (kernel_integrable a) (kernel_integrable b)] at hp
  exact sub_pos.mp hp

theorem parameter_unique (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haeq : normIntegral a = 1 / 2) (hbeq : normIntegral b = 1 / 2) : a = b :=
  normIntegral_strictAnti.injOn ha hb (haeq.trans hbeq.symm)

/-- The complementary radial norm. This is the identity used to normalize
both Gaussian orbitals with the same prefactor. -/
theorem complementary_integral (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Ioi (0 : ℝ), t * s * exp (-s) / (1 + t * s)) = 1 - normIntegral t := by
  have heq : (∫ s in Ioi (0 : ℝ), t * s * exp (-s) / (1 + t * s)) =
      ∫ s in Ioi (0 : ℝ), exp (-s) - kernel t s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hspos : 0 < s := mem_Ioi.mp hs
    have hd : 1 + t * s ≠ 0 := ne_of_gt (by positivity)
    simp only [kernel, max_eq_left ht, max_eq_left (le_of_lt (mem_Ioi.mp hs))]
    field_simp
    ring
  rw [heq, integral_sub (integrableOn_exp_neg_Ioi 0) (kernel_integrable t),
    integral_exp_neg_Ioi_zero]
  rfl

theorem kernel_tendsto_zero (s : ℝ) (hs : 0 < s) :
    Tendsto (fun t => kernel t s) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => max t 0) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_max_left _ _) tendsto_id
  have hden : Tendsto (fun t : ℝ => 1 + max t 0 * max s 0) atTop atTop := by
    rw [max_eq_left hs.le]
    exact tendsto_const_nhds.add_atTop (ht.atTop_mul_const hs)
  exact tendsto_const_nhds.div_atTop hden

theorem normIntegral_tendsto_zero : Tendsto normIntegral atTop (𝓝 0) := by
  change Tendsto (fun t => ∫ s in Ioi (0 : ℝ), kernel t s) atTop (𝓝 0)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := atTop) (F := kernel) (f := fun _ => (0 : ℝ))
    (fun s => exp (-s))
    (Eventually.of_forall (fun t => (kernel_continuous_s t).aestronglyMeasurable))
    (Eventually.of_forall (fun t => ae_of_all _ (kernel_bound t)))
    (integrableOn_exp_neg_Ioi 0) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact kernel_tendsto_zero s hs

/-- Existence of the manuscript's normalization parameter, for its literal integral. -/
theorem exists_parameter : ∃ t : ℝ, 0 < t ∧
    (∫ s in Ioi (0 : ℝ), exp (-s) / (1 + t * s)) = 1 / 2 := by
  have hevent : ∀ᶠ t : ℝ in atTop, normIntegral t < 1 / 2 :=
    normIntegral_tendsto_zero.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨b, hbpos, hblt⟩ := (eventually_gt_atTop (0 : ℝ)).and hevent |>.exists
  have hy : (1 / 2 : ℝ) ∈ Icc (normIntegral b) (normIntegral 0) := by
    rw [normIntegral_zero]
    exact ⟨hblt.le, by norm_num⟩
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hbpos.le
    normIntegral_continuous.continuousOn hy
  have htpos : 0 < t := by
    have htne : t ≠ 0 := by
      intro htzero
      rw [htzero, normIntegral_zero] at heq
      norm_num at heq
    exact lt_of_le_of_ne ht.1 (Ne.symm htne)
  refine ⟨t, htpos, ?_⟩
  rw [← heq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [kernel, max_eq_left htpos.le, max_eq_left (le_of_lt (mem_Ioi.mp hs))]

theorem normIntegral_eq_literal (t : ℝ) (ht : 0 ≤ t) :
    normIntegral t = ∫ s in Ioi (0 : ℝ), exp (-s) / (1 + t * s) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  simp only [kernel, max_eq_left ht, max_eq_left (le_of_lt (mem_Ioi.mp hs))]

/-- Existence and uniqueness for the exact normalization equation in the draft. -/
theorem existsUnique_parameter : ∃! t : ℝ, 0 < t ∧
    (∫ s in Ioi (0 : ℝ), exp (-s) / (1 + t * s)) = 1 / 2 := by
  obtain ⟨t, ht, heq⟩ := exists_parameter
  refine ⟨t, ⟨ht, heq⟩, ?_⟩
  rintro s ⟨hs, hseq⟩
  exact parameter_unique s t hs.le ht.le
    ((normIntegral_eq_literal s hs.le).trans hseq)
    ((normIntegral_eq_literal t ht.le).trans heq)

end MagHK.GaussianNormalization
