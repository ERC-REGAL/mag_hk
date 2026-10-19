import MagHK.PotentialInfinity
import MagHK.CylindricalOrbitals
import MagHK.SecondOrbital

/-! Actual radial form integrability for the bounded orbitals. -/
noncomputable section
namespace MagHK.OrbitalDomains
open MeasureTheory Set
open MagHK.Noninteracting MagHK.SecondOrbital MagHK.RadialEndpoints MagHK.PotentialInfinity
open MagHK.CylindricalOrbitals
open scoped ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem profileF_contDiff (t : ℝ) (ht : 0 ≤ t) : ContDiff ℝ ∞ (profileF t) := by
  let primitive : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, profileU t u
  have hd (r : ℝ) : HasDerivAt primitive (profileU t r) r := by
    have hc := profileU_continuous t ht
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have heq : deriv primitive = profileU t := funext (fun r => (hd r).deriv)
  have hp : ContDiff ℝ ∞ primitive := contDiff_infty_iff_deriv.mpr
    ⟨fun r => (hd r).differentiableAt, by
      rw [heq]
      exact (profileU_contDiff t ht).of_le le_top⟩
  exact hp.neg.exp

theorem growth_contDiff :
    ContDiff ℝ ∞ (fun r : ℝ => Real.exp (Real.sqrt (1 + r ^ 2) - 1)) :=
  (((contDiff_const.add (contDiff_id.pow 2)).sqrt
    (fun r => ne_of_gt (by positivity))).sub contDiff_const).exp

theorem profileR_contDiff : ContDiff ℝ ∞ profileR := contDiff_id.mul growth_contDiff

theorem boundedProduct_contDiff (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (boundedProduct t) := profileR_contDiff.mul (profileF_contDiff t ht)

theorem profileF_contDiffOn_two (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ 2 (profileF t) (Ioi 0) :=
  ((profileF_contDiff t ht).of_le (by simp)).contDiffOn

theorem boundedProduct_contDiffOn_two (t : ℝ) (ht : 0 ≤ t) :
    ContDiffOn ℝ 2 (boundedProduct t) (Ioi 0) :=
  ((boundedProduct_contDiff t ht).of_le (by simp)).contDiffOn

theorem profileU_bounded (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 0 ≤ r → |profileU t r| ≤ C := by
  obtain ⟨C, hC⟩ := continuous_halfline_bounded_of_tendsto
    (profileU_continuous t ht.le).continuousOn (profileU_tendsto_atTop t ht)
  exact ⟨max C 0, le_max_right _ _, fun r hr => (hC r hr).trans (le_max_left _ _)⟩

def boundedQuotient (t r : ℝ) : ℝ :=
  Real.exp (Real.sqrt (1 + r ^ 2) - 1) * profileF t r

theorem boundedQuotient_continuous (t : ℝ) (ht : 0 ≤ t) : Continuous (boundedQuotient t) :=
  growth_contDiff.continuous.mul (profileF_continuous t ht)

theorem boundedProduct_eq_radius_quotient (t r : ℝ) :
    boundedProduct t r = r * boundedQuotient t r := by
  unfold boundedProduct profileR boundedQuotient
  ring

theorem growth_exp_bound (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (Real.sqrt (1 + r ^ 2) - 1) ≤ Real.exp r := by
  have hs : Real.sqrt (1 + r ^ 2) ≤ 1 + r :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith)
  exact Real.exp_le_exp.mpr (by linarith)

theorem boundedQuotient_bound (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    boundedQuotient t r ≤ Real.exp (5 - 4 * r) := by
  have hf := (profileF_le_base t r ht hr).trans (profileF_base_global_bound r hr)
  calc
    boundedQuotient t r ≤ Real.exp r * Real.exp (5 - 5 * r) :=
      mul_le_mul (growth_exp_bound r hr) hf (profileF_pos t r).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem boundedQuotient_density_bound (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    boundedQuotient t r ^ 2 * r ≤ Real.exp (10 - 7 * r) := by
  have hq : 0 ≤ boundedQuotient t r := mul_nonneg (Real.exp_pos _).le (profileF_pos t r).le
  have hs := pow_le_pow_left₀ hq (boundedQuotient_bound t r ht hr) 2
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  calc
    boundedQuotient t r ^ 2 * r ≤ Real.exp (5 - 4 * r) ^ 2 * Real.exp r :=
      mul_le_mul hs hre hr (sq_nonneg _)
    _ = _ := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem boundedQuotient_sq_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => boundedQuotient t r ^ 2 * r) (Ioi (0 : ℝ)) := by
  apply (exponential_majorant_integrable 7 (by norm_num)).mono'
    (((boundedQuotient_continuous t ht).pow 2).mul continuous_id).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr.le)]
  exact boundedQuotient_density_bound t r ht hr.le

theorem boundedProduct_sq_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => boundedProduct t r ^ 2 * r) (Ioi (0 : ℝ)) := by
  apply weighted_base_density_integrable.mono'
    ((((boundedProduct_contDiff t ht).continuous).pow 2).mul continuous_id).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr.le)]
  have hs := pow_le_pow_left₀ (profileF_pos t r).le (profileF_le_base t r ht hr.le) 2
  change boundedProduct t r ^ 2 * r ≤ weightedBaseDensity r
  unfold boundedProduct weightedBaseDensity
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hr.le

theorem boundedProduct_angular_integrable (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun r => boundedProduct t r ^ 2 / r) (Ioi (0 : ℝ)) := by
  apply (boundedQuotient_sq_integrable t ht).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [boundedProduct_eq_radius_quotient]
  field_simp

theorem profileF_deriv_sq_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun r => deriv (profileF t) r ^ 2 * r) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := profileU_bounded t ht
  have hb : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ‖profileU t r ^ 2‖ ≤ C ^ 2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (profileU t r))]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (profileU t r)) (hC r hr.le) 2
  have hi := (radialDensityF_integrable t ht.le).bdd_mul
    ((profileU_continuous t ht.le).pow 2).aestronglyMeasurable hb
  apply hi.congr
  apply ae_of_all
  intro r
  change profileU t r ^ 2 * radialDensityF t r = deriv (profileF t) r ^ 2 * r
  rw [(profileF_hasDerivAt t r ht.le).deriv]
  unfold radialDensityF
  ring

theorem boundedProduct_deriv_formula (t r : ℝ) (ht : 0 ≤ t) :
    deriv (boundedProduct t) r = boundedQuotient t r +
      (profileH r - profileU t r) * boundedProduct t r := by
  rw [(boundedProduct_hasDerivAt t r ht).deriv]
  unfold boundedProductPrime growthPrime boundedProduct boundedQuotient profileR
  ring

theorem boundedProduct_deriv_sq_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun r => deriv (boundedProduct t) r ^ 2 * r) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := profileU_bounded t ht
  have hi := ((boundedQuotient_sq_integrable t ht.le).const_mul 2).add
    ((boundedProduct_sq_integrable t ht.le).const_mul (2 * (1 + C) ^ 2))
  apply hi.mono'
    ((((boundedProduct_contDiff t ht.le).continuous_deriv (by simp)).pow 2).mul
      continuous_id).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hH := profileH_bounds r hr.le
  have hb : |profileH r - profileU t r| ≤ 1 + C :=
    (abs_sub _ _).trans (add_le_add
      (by simpa only [abs_of_nonneg hH.1] using hH.2) (hC r hr.le))
  have hsq : (profileH r - profileU t r) ^ 2 ≤ (1 + C) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsq (sq_nonneg (boundedProduct t r))) hr.le
  change ‖deriv (boundedProduct t) r ^ 2 * r‖ ≤
    2 * (boundedQuotient t r ^ 2 * r) + 2 * (1 + C) ^ 2 * (boundedProduct t r ^ 2 * r)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr.le),
    boundedProduct_deriv_formula t r ht.le]
  have hs : (boundedQuotient t r + (profileH r - profileU t r) * boundedProduct t r) ^ 2 ≤
      2 * boundedQuotient t r ^ 2 +
        2 * ((profileH r - profileU t r) * boundedProduct t r) ^ 2 := by
    nlinarith [sq_nonneg (boundedQuotient t r -
      (profileH r - profileU t r) * boundedProduct t r)]
  have hs' := mul_le_mul_of_nonneg_right hs hr.le
  nlinarith

theorem bounded_weighted_multiplier_integrable (u w : ℝ → ℝ)
    (hw : Continuous w) (hb : ∃ C : ℝ, ∀ r, 0 ≤ r → |w r| ≤ C)
    (hu : IntegrableOn (fun r => u r ^ 2 * r) (Ioi (0 : ℝ))) :
    IntegrableOn (fun r => w r * u r ^ 2 * r) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := hb
  have hbound : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), ‖w r‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs] using hC r hr.le
  have hi : IntegrableOn (fun r => w r * (u r ^ 2 * r)) (Ioi (0 : ℝ)) :=
    hu.bdd_mul hw.aestronglyMeasurable hbound
  apply hi.congr
  exact ae_of_all _ (fun r => by simp only [mul_assoc])

theorem profileA_energy_integrable (t : ℝ) (ht : 0 < t) (u : ℝ → ℝ)
    (hu : IntegrableOn (fun r => u r ^ 2 * r) (Ioi (0 : ℝ))) :
    IntegrableOn (fun r => profileA t r ^ 2 * u r ^ 2 * r) (Ioi (0 : ℝ)) := by
  apply bounded_weighted_multiplier_integrable u _ ((profileA_continuous t ht.le).pow 2)
  · exact continuous_halfline_bounded_of_tendsto
      ((profileA_continuous t ht.le).pow 2).continuousOn
      ((profileA_tendsto_atTop t ht).pow 2)
  · exact hu

theorem profileV_abs_energy_integrable (t : ℝ) (ht : 0 < t) (u : ℝ → ℝ)
    (hu : IntegrableOn (fun r => u r ^ 2 * r) (Ioi (0 : ℝ))) :
    IntegrableOn (fun r => |regularProfileV t r| * u r ^ 2 * r) (Ioi (0 : ℝ)) := by
  apply bounded_weighted_multiplier_integrable u _
    (regularProfileV_contDiff t ht.le).continuous.abs
  · obtain ⟨C, hC⟩ := regularProfileV_bounded t ht
    exact ⟨C, fun r hr => by simpa only [abs_abs] using hC r hr⟩
  · exact hu

theorem boundedProduct_magnetic_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun r => (-1 / r + profileA t r) ^ 2 * boundedProduct t r ^ 2 * r)
      (Ioi (0 : ℝ)) := by
  have hA := profileA_energy_integrable t ht _ (boundedProduct_sq_integrable t ht.le)
  have hi := ((boundedProduct_angular_integrable t ht.le).const_mul 2).add (hA.const_mul 2)
  have hm : Measurable (fun r : ℝ =>
      (-1 / r + profileA t r) ^ 2 * boundedProduct t r ^ 2 * r) := by
    have ha := (profileA_continuous t ht.le).measurable
    have hg := (boundedProduct_contDiff t ht.le).continuous.measurable
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hr.le)]
  simp only [Pi.add_apply]
  have hs : (-1 / r + profileA t r) ^ 2 ≤ 2 * (-1 / r) ^ 2 + 2 * profileA t r ^ 2 := by
    nlinarith [sq_nonneg (-1 / r - profileA t r)]
  calc
    _ ≤ (2 * (-1 / r) ^ 2 + 2 * profileA t r ^ 2) * boundedProduct t r ^ 2 * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) hr.le
    _ = _ := by field_simp [ne_of_gt (show 0 < r from hr)]

theorem profileF_form_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun r => deriv (profileF t) r ^ 2 +
      ((0 / r + profileA t r) ^ 2 + |regularProfileV t r|) * profileF t r ^ 2)
      radialMeasure := by
  rw [radial_integrable_iff]
  have hmass : IntegrableOn (fun r => profileF t r ^ 2 * r) (Ioi (0 : ℝ)) :=
    radialDensityF_integrable t ht.le
  have hi := (profileF_deriv_sq_integrable t ht).add
    ((profileA_energy_integrable t ht _ hmass).add (profileV_abs_energy_integrable t ht _ hmass))
  apply hi.congr
  apply ae_of_all
  intro r
  change deriv (profileF t) r ^ 2 * r +
      (profileA t r ^ 2 * profileF t r ^ 2 * r +
        |regularProfileV t r| * profileF t r ^ 2 * r) =
    r * (deriv (profileF t) r ^ 2 +
      ((0 / r + profileA t r) ^ 2 + |regularProfileV t r|) * profileF t r ^ 2)
  simp only [zero_div, zero_add]
  ring

theorem boundedProduct_form_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun r => deriv (boundedProduct t) r ^ 2 +
      ((-1 / r + profileA t r) ^ 2 + |regularProfileV t r|) * boundedProduct t r ^ 2)
      radialMeasure := by
  rw [radial_integrable_iff]
  have hi := (boundedProduct_deriv_sq_integrable t ht).add
    ((boundedProduct_magnetic_integrable t ht).add
      (profileV_abs_energy_integrable t ht _ (boundedProduct_sq_integrable t ht.le)))
  apply hi.congr
  apply ae_of_all
  intro r
  change deriv (boundedProduct t) r ^ 2 * r +
      ((-1 / r + profileA t r) ^ 2 * boundedProduct t r ^ 2 * r +
        |regularProfileV t r| * boundedProduct t r ^ 2 * r) =
    r * (deriv (boundedProduct t) r ^ 2 +
      ((-1 / r + profileA t r) ^ 2 + |regularProfileV t r|) * boundedProduct t r ^ 2)
  ring

theorem profileF_bounded_near_zero (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |profileF t r| ≤ C := by
  refine ⟨1, fun r hr _ => ?_⟩
  rw [abs_of_pos (profileF_pos t r)]
  exact profileF_le_one t r ht hr.le

theorem boundedProduct_positive (t r : ℝ) (hr : 0 < r) : 0 < boundedProduct t r :=
  mul_pos (profileR_pos r hr) (profileF_pos t r)

theorem boundedProduct_origin_growth (t r : ℝ) (ht : 0 ≤ t) (hr : 0 < r) (hr1 : r ≤ 1) :
    |boundedProduct t r| ≤ Real.exp 1 * r := by
  rw [abs_of_pos (boundedProduct_positive t r hr), boundedProduct_eq_radius_quotient]
  have hq : boundedQuotient t r ≤ Real.exp 1 := by
    calc
      boundedQuotient t r ≤ Real.exp (Real.sqrt (1 + r ^ 2) - 1) * 1 :=
        mul_le_mul_of_nonneg_left (profileF_le_one t r ht hr.le) (Real.exp_pos _).le
      _ ≤ Real.exp 1 := by
        simpa only [mul_one] using (growth_exp_bound r hr.le).trans (Real.exp_le_exp.mpr hr1)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq hr.le

theorem boundedProduct_bounded_near_zero (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → |boundedProduct t r| ≤ C := by
  refine ⟨Real.exp 1, fun r hr hr1 => ?_⟩
  exact (boundedProduct_origin_growth t r ht hr hr1).trans
    (by simpa using mul_le_mul_of_nonneg_left hr1 (Real.exp_pos 1).le)

theorem boundedProduct_mass_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun r => boundedProduct t r ^ 2) radialMeasure := by
  rw [radial_integrable_iff]
  simpa only [mul_comm] using boundedProduct_sq_integrable t ht

theorem profileF_mass_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < ∫ r, profileF t r ^ 2 ∂radialMeasure := by
  change 0 < ∫ r, radialZero t r ^ 2 ∂radialMeasure
  rw [radialZero_sq_integral]
  exact radialNormF_pos t ht

theorem boundedProduct_mass_positive (t : ℝ) (ht : 0 ≤ t) :
    0 < ∫ r, boundedProduct t r ^ 2 ∂radialMeasure := by
  rw [radial_integral]
  have hi : IntegrableOn (fun r => r * boundedProduct t r ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [mul_comm] using boundedProduct_sq_integrable t ht
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).2
  · have he : Function.support (fun r => r * boundedProduct t r ^ 2) ∩ Ioi (0 : ℝ) = Ioi 0 := by
      apply inter_eq_right.2
      intro r hr
      change r * boundedProduct t r ^ 2 ≠ 0
      exact ne_of_gt (mul_pos hr (sq_pos_of_pos (boundedProduct_positive t r hr)))
    rw [he, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (sq_nonneg _)

end MagHK.OrbitalDomains
