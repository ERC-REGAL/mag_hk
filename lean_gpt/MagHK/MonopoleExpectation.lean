import MagHK.MonopolePairLaw

/-! The Coulomb expectation is an integrable function of the actual product state. -/
noncomputable section
namespace MagHK.MonopoleExpectation

open MeasureTheory Set Filter
open MagHK.Monopole MagHK.MonopoleTrial
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem angularCoulomb_integrable (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Integrable (fun p : Angle × Angle =>
      Complex.normSq (angularDet p.1 p.2) / pairDistance s t p)
      (sphereMeasure.prod sphereMeasure) := by
  let f : ℝ → ℝ := fun μ => (1 - μ) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * μ)
  have hi : IntervalIntegrable f volume (-1) 1 := by
    by_cases hst : s = t
    · subst t
      exact diagonal_angular_integrand_integrable s hs
    · exact angular_integrand_integrable_of_ne s t hs ht hst
  have hic : Integrable f cosineMeasure :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hi
  have hmap : Integrable f (Measure.map pairDot (sphereMeasure.prod sphereMeasure)) := by
    rw [MagHK.MonopolePairLaw.sphericalPairQuadrature]
    exact hic.smul_measure (by finiteness)
  have hcomp := (hmap.comp_measurable pairDot_continuous.measurable).const_mul
    (1 / (16 * Real.pi ^ 2))
  apply hcomp.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae angle_ae,
    Measure.quasiMeasurePreserving_snd.ae angle_ae] with p hp hq
  rw [angularDet_probability p.1 p.2 hp hq, pairDistance_eq s t p hp hq]
  dsimp only [Function.comp_def, f]
  ring

theorem radialVolume_ae : ∀ᵐ r ∂radialVolume, 0 < r :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

@[fun_prop] theorem radialOrbital_measurable : Measurable radialOrbital := by
  unfold radialOrbital
  fun_prop

theorem angularDet_continuous : Continuous (fun p : Angle × Angle => angularDet p.1 p.2) := by
  unfold angularDet MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  exact continuous_const.mul (((Yplus_continuous.comp continuous_fst).mul
    (Yminus_continuous.comp continuous_snd)).sub
    ((Yminus_continuous.comp continuous_fst).mul (Yplus_continuous.comp continuous_snd)))

@[fun_prop] theorem direction_continuous (i : Fin 3) : Continuous (fun p : Angle => direction p i) := by
  have hp : Continuous spinorPlus := by unfold spinorPlus; fun_prop
  have hm : Continuous spinorMinus := by
    unfold spinorMinus
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      ((continuous_const.sub continuous_fst).div_const 2))).mul
      (MagHK.CylindricalOrbitals.phase_continuous.comp continuous_snd)
  fin_cases i <;> simp [direction] <;> fun_prop

def coulombIntegrand (x : TrialCoordinates) : ℝ :=
  Complex.normSq (trial x) / pairDistance x.1.1 x.1.2 x.2

theorem coulombIntegrand_nonneg (x : TrialCoordinates) : 0 ≤ coulombIntegrand x :=
  div_nonneg (Complex.normSq_nonneg _) (Real.sqrt_nonneg _)

theorem coulombIntegrand_measurable : Measurable coulombIntegrand := by
  have ht : Measurable trial := by
    unfold trial
    exact (Complex.measurable_ofReal.comp ((radialOrbital_measurable.comp measurable_fst.fst).mul
      (radialOrbital_measurable.comp measurable_fst.snd))).mul
      (angularDet_continuous.measurable.comp measurable_snd)
  have hd : Continuous (fun x : TrialCoordinates => pairDistance x.1.1 x.1.2 x.2) := by
    unfold pairDistance
    fun_prop
  exact (Complex.continuous_normSq.measurable.comp ht).div hd.measurable

theorem radialOrbital_inverse_integrable :
    Integrable (fun r => radialOrbital r ^ 2 / r) radialVolume := by
  have hm : Measurable (fun r : ℝ => Real.toNNReal (r ^ 2)) := by fun_prop
  apply (integrable_withDensity_iff_integrable_coe_smul hm).mpr
  apply radial_inverse_integrable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have he : radialDensity r / r = r ^ 2 * (radialOrbital r ^ 2 / r) := by
    rw [← radialOrbital_squared_density r hr]
    ring
  simpa only [Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul] using he

theorem radialKernel_integrable :
    Integrable (fun p : ℝ × ℝ =>
      (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2) * angularKernel p.1 p.2)
      (radialVolume.prod radialVolume) := by
  have hmajor := radialOrbital_inverse_integrable.mul_prod radialOrbital_integrable_radialVolume
  have hm : Measurable (fun p : ℝ × ℝ =>
      (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2) * angularKernel p.1 p.2) := by
    unfold angularKernel
    fun_prop
  apply hmajor.mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae radialVolume_ae,
    Measure.quasiMeasurePreserving_snd.ae radialVolume_ae] with p hp hq
  have hnonneg : 0 ≤ (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2) * angularKernel p.1 p.2 :=
    mul_nonneg (by positivity) (angularKernel_bounds p.1 p.2 hp hq).1.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2) * (1 / p.1) :=
      mul_le_mul_of_nonneg_left ((angularKernel_bounds p.1 p.2 hp hq).2.1.trans
        (angularKernel_bounds p.1 p.2 hp hq).2.2) (by positivity)
    _ = _ := by ring

theorem angular_average (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (∫ p : Angle × Angle, coulombIntegrand ((s, t), p) ∂sphereMeasure.prod sphereMeasure) =
      (radialOrbital s ^ 2 * radialOrbital t ^ 2) * angularKernel s t := by
  have he (p : Angle × Angle) : coulombIntegrand ((s, t), p) =
      (radialOrbital s ^ 2 * radialOrbital t ^ 2) *
        (Complex.normSq (angularDet p.1 p.2) / pairDistance s t p) := by
    unfold coulombIntegrand
    rw [trial_probability]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  exact congrArg ((radialOrbital s ^ 2 * radialOrbital t ^ 2) * ·)
    (MagHK.MonopolePairLaw.angularCoulomb_eq_kernel s t hs ht)

theorem trialCoulomb_integrable : Integrable coulombIntegrand trialMeasure := by
  apply (integrable_prod_iff coulombIntegrand_measurable.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae radialVolume_ae,
      Measure.quasiMeasurePreserving_snd.ae radialVolume_ae] with p hp hq
    apply ((angularCoulomb_integrable p.1 p.2 hp hq).const_mul
      (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2)).congr
    exact Eventually.of_forall (fun q => by
      unfold coulombIntegrand
      dsimp only
      rw [trial_probability]
      ring)
  · apply radialKernel_integrable.congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae radialVolume_ae,
      Measure.quasiMeasurePreserving_snd.ae radialVolume_ae] with p hp hq
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (coulombIntegrand_nonneg _)]
    exact (angular_average p.1 p.2 hp hq).symm

/-- Actual product-measure Coulomb expectation of the normalized determinant. -/
def trialCoulomb : ℝ := ∫ x, coulombIntegrand x ∂trialMeasure

theorem trialCoulomb_eq : trialCoulomb = radialCoulombExpectation := by
  unfold trialCoulomb
  rw [trialMeasure, integral_prod _ trialCoulomb_integrable]
  have he : (fun p : ℝ × ℝ => ∫ q, coulombIntegrand (p, q) ∂sphereMeasure.prod sphereMeasure) =ᵐ[
      radialVolume.prod radialVolume] (fun p =>
      (radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2) * angularKernel p.1 p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae radialVolume_ae,
      Measure.quasiMeasurePreserving_snd.ae radialVolume_ae] with p hp hq
    exact angular_average p.1 p.2 hp hq
  rw [integral_congr_ae he, integral_prod _ radialKernel_integrable, radialVolume_integral]
  unfold radialCoulombExpectation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [radialVolume_integral, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← radialOrbital_squared_density s hs, ← radialOrbital_squared_density t ht]
  ring

theorem trialCoulomb_bound : trialCoulomb ≤ coulombBound ∧ trialCoulomb < freeGap := by
  rw [trialCoulomb_eq]
  exact ⟨radialCoulombExpectation_bound, radialCoulombExpectation_bound.trans_lt coulomb_bound_lt_gap⟩

end MagHK.MonopoleExpectation
