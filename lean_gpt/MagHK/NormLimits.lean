import MagHK.Noninteracting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace MagHK.Noninteracting

open Set Filter MeasureTheory
open scoped Topology

theorem profileF_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (profileF t) :=
  continuous_iff_continuousAt.2 fun r => (profileF_hasDerivAt t r ht).continuousAt

theorem profileR_continuous : Continuous profileR :=
  continuous_iff_continuousAt.2 fun r => (profileR_hasDerivAt_regular r).continuousAt

theorem profileF_base_global_bound (r : ℝ) (hr : 0 ≤ r) :
    profileF 0 r ≤ Real.exp (5 - 5 * r) := by
  by_cases hsmall : r ≤ 1
  · exact (profileF_le_one 0 r (by norm_num) hr).trans
      (Real.one_le_exp_iff.2 (by linarith))
  · have h := profileF_base_tail r (le_of_not_ge hsmall)
    calc
      profileF 0 r ≤ Real.exp 5 * Real.exp (-5 * r) := h
      _ = Real.exp (5 - 5 * r) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem profileR_exp_bound (r : ℝ) (hr : 0 ≤ r) : profileR r ≤ Real.exp (2 * r) := by
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  calc
    profileR r ≤ r * Real.exp r := profileR_upper r hr
    _ ≤ Real.exp r * Real.exp r := mul_le_mul_of_nonneg_right hre (Real.exp_pos _).le
    _ = Real.exp (2 * r) := by rw [← Real.exp_add]; congr 1; ring

def radialDensityF (t r : ℝ) : ℝ := profileF t r ^ 2 * r
def weightedBaseDensity (r : ℝ) : ℝ := profileR r ^ 2 * profileF 0 r ^ 2 * r

theorem base_density_exponential_bound (r : ℝ) (hr : 0 ≤ r) :
    radialDensityF 0 r ≤ Real.exp (10 - 9 * r) := by
  have hf := profileF_base_global_bound r hr
  have hsq : profileF 0 r ^ 2 ≤ Real.exp (5 - 5 * r) ^ 2 :=
    pow_le_pow_left₀ (profileF_pos 0 r).le hf _
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  calc
    radialDensityF 0 r ≤ Real.exp (5 - 5 * r) ^ 2 * Real.exp r :=
      mul_le_mul hsq hre hr (sq_nonneg _)
    _ = Real.exp (10 - 9 * r) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem weighted_density_exponential_bound (r : ℝ) (hr : 0 ≤ r) :
    weightedBaseDensity r ≤ Real.exp (10 - 5 * r) := by
  have hf := profileF_base_global_bound r hr
  have hsq : profileF 0 r ^ 2 ≤ Real.exp (5 - 5 * r) ^ 2 :=
    pow_le_pow_left₀ (profileF_pos 0 r).le hf _
  have hR : 0 ≤ profileR r := by unfold profileR; positivity
  have hRsq : profileR r ^ 2 ≤ Real.exp (2 * r) ^ 2 :=
    pow_le_pow_left₀ hR (profileR_exp_bound r hr) _
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  calc
    weightedBaseDensity r ≤
        (Real.exp (2 * r) ^ 2 * Real.exp (5 - 5 * r) ^ 2) * Real.exp r :=
      mul_le_mul (mul_le_mul hRsq hsq (sq_nonneg _) (sq_nonneg _)) hre hr (by positivity)
    _ = Real.exp (10 - 5 * r) := by
      simp only [pow_two, ← Real.exp_add]
      congr 1
      ring

theorem exponential_majorant_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => Real.exp (10 - c * r)) (Ioi 0) := by
  have hi := (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul (Real.exp 10)
  simpa only [← Real.exp_add, neg_mul, sub_eq_add_neg] using! hi

theorem radialDensityF_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (radialDensityF t) :=
  ((profileF_continuous t ht).pow 2).mul continuous_id

theorem base_density_integrable : IntegrableOn (radialDensityF 0) (Ioi (0 : ℝ)) := by
  apply (exponential_majorant_integrable 9 (by norm_num)).mono'
    (radialDensityF_continuous 0 (by norm_num)).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold radialDensityF; positivity)]
  exact base_density_exponential_bound r hr.le

theorem weighted_base_density_integrable : IntegrableOn weightedBaseDensity (Ioi (0 : ℝ)) := by
  apply (exponential_majorant_integrable 5 (by norm_num)).mono'
    (((profileR_continuous.pow 2).mul ((profileF_continuous 0 (by norm_num)).pow 2)).mul
      continuous_id).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  change ‖weightedBaseDensity r‖ ≤ Real.exp (10 - 5 * r)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold weightedBaseDensity; positivity)]
  exact weighted_density_exponential_bound r hr.le

theorem radialDensityF_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (radialDensityF t) (Ioi (0 : ℝ)) := by
  apply base_density_integrable.mono' (radialDensityF_continuous t ht).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold radialDensityF; positivity)]
  exact (radial_integrand_bounds t r ht hr.le).2.1

def radialNormF (t : ℝ) : ℝ := ∫ r in Ioi (0 : ℝ), radialDensityF t r
def radialNormG (t : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), t * profileR r ^ 2 * profileF t r ^ 2 * r

theorem radialNormF_pos (t : ℝ) (ht : 0 ≤ t) : 0 < radialNormF t := by
  unfold radialNormF
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (radialDensityF_integrable t ht)).2
  · have he : Function.support (radialDensityF t) ∩ Ioi (0 : ℝ) = Ioi 0 := by
      apply inter_eq_right.2
      intro r hr
      change radialDensityF t r ≠ 0
      exact ne_of_gt (mul_pos (sq_pos_of_pos (profileF_pos t r)) hr)
    rw [he, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg (sq_nonneg _) hr.le

theorem radialNormF_tendsto_zero :
    Tendsto radialNormF (𝓝[Ici (0 : ℝ)] 0) (𝓝 (radialNormF 0)) := by
  apply tendsto_integral_filter_of_dominated_convergence (radialDensityF 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (radialDensityF_integrable t ht).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold radialDensityF; positivity)]
    exact (radial_integrand_bounds t r ht hr.le).2.1
  · exact base_density_integrable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact ((profileF_tendsto_zero r hr.le).pow 2).mul_const r

theorem radialNormF_tendsto_atTop : Tendsto radialNormF atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter ℝ)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := radialDensityF) (f := fun _ => (0 : ℝ))
    (radialDensityF 0)
  have hlim : Tendsto (fun t => ∫ r in Ioi (0 : ℝ), radialDensityF t r)
      atTop (𝓝 (∫ _ in Ioi (0 : ℝ), (0 : ℝ))) := by
    apply h
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (radialDensityF_integrable t ht).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : 0 ≤ r := hr.le
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold radialDensityF; positivity)]
      exact (radial_integrand_bounds t r ht hr.le).2.1
    · exact base_density_integrable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      simpa only [radialDensityF, zero_pow (by norm_num : 2 ≠ 0), zero_mul] using!
        ((profileF_tendsto_atTop r hr).pow 2).mul_const r
  unfold radialNormF
  simpa only [integral_zero] using! hlim

theorem radialNormG_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ radialNormG t := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  positivity

theorem radialNormG_upper (t : ℝ) (ht : 0 ≤ t) :
    radialNormG t ≤ t * ∫ r in Ioi (0 : ℝ), weightedBaseDensity r := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    positivity
  · exact weighted_base_density_integrable.const_mul t
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    simpa only [weightedBaseDensity, mul_assoc] using
      (radial_integrand_bounds t r ht hr.le).2.2

theorem radialNormG_tendsto_zero : Tendsto radialNormG (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => t * ∫ r in Ioi (0 : ℝ), weightedBaseDensity r)
      (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Ici (0 : ℝ)] 0) (𝓝 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hid.mul_const
      (∫ r in Ioi (0 : ℝ), weightedBaseDensity r)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact radialNormG_nonneg t ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact radialNormG_upper t ht

theorem radialNormG_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => t * profileR r ^ 2 * profileF t r ^ 2 * r) (Ioi (0 : ℝ)) := by
  apply (weighted_base_density_integrable.const_mul t).mono'
    ((((continuous_const.mul (profileR_continuous.pow 2)).mul
      ((profileF_continuous t ht).pow 2)).mul continuous_id).aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr0 : 0 ≤ r := hr.le
  change ‖t * profileR r ^ 2 * profileF t r ^ 2 * r‖ ≤ t * weightedBaseDensity r
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [weightedBaseDensity, mul_assoc] using
    (radial_integrand_bounds t r ht hr.le).2.2

def lowerDensityG (t r : ℝ) : ℝ :=
  (t * profileR r ^ 2 / (1 + t * profileR r ^ 2)) * radialDensityF 0 r

def lowerNormG (t : ℝ) : ℝ := ∫ r in Ioi (0 : ℝ), lowerDensityG t r

theorem lowerDensityG_bounds (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    0 ≤ lowerDensityG t r ∧ lowerDensityG t r ≤ radialDensityF 0 r := by
  have hden : 0 < 1 + t * profileR r ^ 2 := by positivity
  have hratio : t * profileR r ^ 2 / (1 + t * profileR r ^ 2) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  unfold lowerDensityG
  constructor
  · unfold radialDensityF
    positivity
  · simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hratio (show 0 ≤ radialDensityF 0 r by
        unfold radialDensityF; positivity)

theorem lowerDensityG_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (lowerDensityG t) := by
  have hnum : Continuous (fun r => t * profileR r ^ 2) :=
    continuous_const.mul (profileR_continuous.pow 2)
  exact (hnum.div (continuous_const.add hnum)
    (fun r => ne_of_gt (by positivity : 0 < 1 + t * profileR r ^ 2))).mul
      (radialDensityF_continuous 0 (by norm_num))

theorem lowerDensityG_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (lowerDensityG t) (Ioi (0 : ℝ)) := by
  apply base_density_integrable.mono' (lowerDensityG_continuous t ht).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (lowerDensityG_bounds t r ht hr.le).1]
  exact (lowerDensityG_bounds t r ht hr.le).2

theorem lowerDensityG_le (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    lowerDensityG t r ≤ t * profileR r ^ 2 * profileF t r ^ 2 * r := by
  have hden : 0 < 1 + t * profileR r ^ 2 := by positivity
  have hf := (profileF_two_sided t r ht hr).1
  have hs : (profileF 0 r / Real.sqrt (1 + t * profileR r ^ 2)) ^ 2 ≤
      profileF t r ^ 2 := pow_le_pow_left₀
        (div_nonneg (profileF_pos 0 r).le (Real.sqrt_nonneg _)) hf _
  rw [div_pow, Real.sq_sqrt hden.le] at hs
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (show 0 ≤ t * profileR r ^ 2 by positivity)) hr
  simpa only [lowerDensityG, radialDensityF, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hmul

theorem lowerNormG_le (t : ℝ) (ht : 0 ≤ t) : lowerNormG t ≤ radialNormG t := by
  apply integral_mono_ae (lowerDensityG_integrable t ht) (radialNormG_integrable t ht)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  exact lowerDensityG_le t r ht hr.le

theorem lowerDensityG_tendsto_atTop (r : ℝ) (hr : 0 < r) :
    Tendsto (fun t => lowerDensityG t r) atTop (𝓝 (radialDensityF 0 r)) := by
  have hlin : Tendsto (fun t : ℝ => t * profileR r ^ 2) atTop atTop :=
    tendsto_id.atTop_mul_const (sq_pos_of_pos (profileR_pos r hr))
  have harg : Tendsto (fun t : ℝ => 1 + t * profileR r ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun t => by linarith) hlin
  have hrat : Tendsto (fun t : ℝ => t * profileR r ^ 2 / (1 + t * profileR r ^ 2))
      atTop (𝓝 1) := by
    have hlim : Tendsto (fun t : ℝ => 1 - (1 + t * profileR r ^ 2)⁻¹)
        atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp harg)
    have heq : (1 : ℝ) - 0 = 1 := by ring
    rw [heq] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hden : 1 + t * profileR r ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  simpa only [lowerDensityG, one_mul] using hrat.mul_const (radialDensityF 0 r)

theorem lowerNormG_tendsto_atTop : Tendsto lowerNormG atTop (𝓝 (radialNormF 0)) := by
  apply tendsto_integral_filter_of_dominated_convergence (radialDensityF 0)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (lowerDensityG_integrable t ht).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (lowerDensityG_bounds t r ht hr.le).1]
    exact (lowerDensityG_bounds t r ht hr.le).2
  · exact base_density_integrable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact lowerDensityG_tendsto_atTop r hr

theorem radialNorms_order_near_zero :
    ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, radialNormG t < radialNormF t :=
  radialNormG_tendsto_zero.eventually_lt radialNormF_tendsto_zero
    (radialNormF_pos 0 (by norm_num))

theorem radialNorms_order_atTop : ∀ᶠ t in atTop, radialNormF t < radialNormG t := by
  have h := radialNormF_tendsto_atTop.eventually_lt lowerNormG_tendsto_atTop
    (radialNormF_pos 0 (by norm_num))
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with t ht htpos
  exact ht.trans_le (lowerNormG_le t htpos)

end MagHK.Noninteracting
