import MagHK.MonopoleTrial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Literal angular derivatives and finite magnetic energy of the north-patch
charge-one spinor doublet. -/
noncomputable section
namespace MagHK.MonopoleAngular
open MeasureTheory Set Filter
open MagHK.MonopoleTrial
open scoped ComplexConjugate ContDiff Topology
set_option maxHeartbeats 1000000

def Dμ (Y : Angle → ℂ) (p : Angle) : ℂ := deriv (fun μ => Y (μ, p.2)) p.1
def Dφ (Y : Angle → ℂ) (p : Angle) : ℂ := deriv (fun φ => Y (p.1, φ)) p.2

def angularExpression (g : ℝ) (Y : Angle → ℂ) (p : Angle) : ℂ :=
  -(1 - p.1 ^ 2 : ℝ) * Dμ (Dμ Y) p + 2 * p.1 * Dμ Y p +
    (-Dφ (Dφ Y) p - 2 * Complex.I * (g * (1 - p.1) : ℝ) * Dφ Y p +
      ((g * (1 - p.1)) ^ 2 : ℝ) * Y p) / (1 - p.1 ^ 2 : ℝ)

def angularEnergy (g : ℝ) (Y : Angle → ℂ) (p : Angle) : ℝ :=
  (1 - p.1 ^ 2) * ‖Dμ Y p‖ ^ 2 +
    ‖-Complex.I * Dφ Y p + (g * (1 - p.1) : ℝ) * Y p‖ ^ 2 / (1 - p.1 ^ 2)

private theorem plus_hasDerivAt (μ : ℝ) (hμ : -1 < μ) :
    HasDerivAt plusAmplitude (plusAmplitude μ / (2 * (1 + μ))) μ := by
  have hx : 0 < (1 + μ) / 2 := by linarith
  have hs : 0 < Real.sqrt ((1 + μ) / 2) := Real.sqrt_pos.2 hx
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h := ((((hasDerivAt_id μ).const_add 1).div_const 2).sqrt (ne_of_gt hx)).div_const
    (Real.sqrt (2 * Real.pi))
  apply h.congr_deriv
  simp only [id_eq]
  unfold plusAmplitude
  field_simp [ne_of_gt hs, ne_of_gt hπ, ne_of_gt (show 0 < 1 + μ by linarith)]
  nlinarith [Real.sq_sqrt hx.le]

private theorem minus_hasDerivAt (μ : ℝ) (hμ : μ < 1) :
    HasDerivAt minusAmplitude (-minusAmplitude μ / (2 * (1 - μ))) μ := by
  have hx : 0 < (1 - μ) / 2 := by linarith
  have hs : 0 < Real.sqrt ((1 - μ) / 2) := Real.sqrt_pos.2 hx
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h := ((((hasDerivAt_id μ).const_sub 1).div_const 2).sqrt (ne_of_gt hx)).div_const
    (Real.sqrt (2 * Real.pi))
  apply h.congr_deriv
  simp only [id_eq]
  unfold minusAmplitude
  field_simp [ne_of_gt hs, ne_of_gt hπ, ne_of_gt (show 0 < 1 - μ by linarith)]
  nlinarith [Real.sq_sqrt hx.le]

private theorem plus_second (μ : ℝ) (hμ : -1 < μ) :
    HasDerivAt (deriv plusAmplitude) (-plusAmplitude μ / (4 * (1 + μ) ^ 2)) μ := by
  have hp := plus_hasDerivAt μ hμ
  have hd := hp.div (((hasDerivAt_id μ).const_add 1).const_mul 2)
    (by linarith : 2 * (1 + μ) ≠ 0)
  have he : deriv plusAmplitude =ᶠ[𝓝 μ] (fun x => plusAmplitude x / (2 * (1 + x))) := by
    filter_upwards [Ioi_mem_nhds hμ] with x hx
    exact (plus_hasDerivAt x hx).deriv
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [id_eq]
  field_simp [ne_of_gt (show 0 < 1 + μ by linarith)]
  ring

private theorem minus_second (μ : ℝ) (hμ : μ < 1) :
    HasDerivAt (deriv minusAmplitude) (-minusAmplitude μ / (4 * (1 - μ) ^ 2)) μ := by
  have hp := minus_hasDerivAt μ hμ
  have hd := hp.neg.div (((hasDerivAt_id μ).const_sub 1).const_mul 2)
    (by linarith : 2 * (1 - μ) ≠ 0)
  have he : deriv minusAmplitude =ᶠ[𝓝 μ] (fun x => -minusAmplitude x / (2 * (1 - x))) := by
    filter_upwards [Iio_mem_nhds hμ] with x hx
    exact (minus_hasDerivAt x hx).deriv
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [id_eq, Pi.neg_apply]
  field_simp [ne_of_gt (show 0 < 1 - μ by linarith)]
  ring

private theorem phase_hasDerivAt (φ : ℝ) :
    HasDerivAt MagHK.CylindricalOrbitals.phase
      (-Complex.I * MagHK.CylindricalOrbitals.phase φ) φ := by
  have h := (((hasDerivAt_id φ).ofReal_comp.neg).mul_const Complex.I).cexp
  simp only [id_eq, Pi.neg_apply, Complex.ofReal_one, neg_mul, one_mul] at h
  convert! h using 1
  · funext x
    simpa only [neg_mul] using MagHK.CylindricalOrbitals.phase_eq_negative_exp x
  · rw [MagHK.CylindricalOrbitals.phase_eq_negative_exp]
    ring

theorem Yplus_Dμ (p : Angle) (hp : -1 < p.1) :
    Dμ Yplus p = Yplus p / (2 * (1 + p.1) : ℝ) := by
  simpa only [Dμ, Yplus, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_one] using!
    (plus_hasDerivAt p.1 hp).ofReal_comp.deriv

theorem Yminus_Dμ (p : Angle) (hp : p.1 < 1) :
    Dμ Yminus p = -Yminus p / (2 * (1 - p.1) : ℝ) := by
  have h := ((minus_hasDerivAt p.1 hp).ofReal_comp.mul_const
    (MagHK.CylindricalOrbitals.phase p.2)).deriv
  change Dμ Yminus p = _ at h
  rw [h]
  simp only [Yminus, Complex.ofReal_div, Complex.ofReal_neg]
  ring

theorem Yplus_Dμμ (p : Angle) (hp : -1 < p.1) :
    Dμ (Dμ Yplus) p = -Yplus p / (4 * (1 + p.1) ^ 2 : ℝ) := by
  have he : (fun μ => Dμ Yplus (μ, p.2)) =ᶠ[𝓝 p.1]
      (fun μ => ((deriv plusAmplitude μ : ℝ) : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hp] with μ hμ
    rw [(plus_hasDerivAt μ hμ).deriv, Yplus_Dμ (μ, p.2) hμ]
    simp [Yplus]
  have h := (plus_second p.1 hp).ofReal_comp.congr_of_eventuallyEq he
  simpa only [Dμ, Yplus, Complex.ofReal_div, Complex.ofReal_neg] using! h.deriv

theorem Yminus_Dμμ (p : Angle) (hp : p.1 < 1) :
    Dμ (Dμ Yminus) p = -Yminus p / (4 * (1 - p.1) ^ 2 : ℝ) := by
  have he : (fun μ => Dμ Yminus (μ, p.2)) =ᶠ[𝓝 p.1]
      (fun μ => ((deriv minusAmplitude μ : ℝ) : ℂ) * MagHK.CylindricalOrbitals.phase p.2) := by
    filter_upwards [Iio_mem_nhds hp] with μ hμ
    rw [(minus_hasDerivAt μ hμ).deriv, Yminus_Dμ (μ, p.2) hμ]
    simp only [Yminus, Complex.ofReal_div, Complex.ofReal_neg]
    ring
  have h := ((minus_second p.1 hp).ofReal_comp.mul_const
    (MagHK.CylindricalOrbitals.phase p.2)).congr_of_eventuallyEq he
  have hd := h.deriv
  change Dμ (Dμ Yminus) p = _ at hd
  rw [hd]
  simp only [Yminus, Complex.ofReal_div, Complex.ofReal_neg]
  ring

@[simp] theorem Yplus_Dφ (p : Angle) : Dφ Yplus p = 0 := by simp [Dφ, Yplus]
@[simp] theorem Yplus_Dφφ (p : Angle) : Dφ (Dφ Yplus) p = 0 := by
  change deriv (fun φ => Dφ Yplus (p.1, φ)) p.2 = 0
  simp only [Yplus_Dφ, deriv_const]

theorem Yminus_Dφ (p : Angle) : Dφ Yminus p = -Complex.I * Yminus p := by
  have h := ((phase_hasDerivAt p.2).const_mul (minusAmplitude p.1 : ℂ)).deriv
  change Dφ Yminus p = _ at h
  rw [h]
  unfold Yminus
  ring

theorem Yminus_Dφφ (p : Angle) : Dφ (Dφ Yminus) p = -Yminus p := by
  change deriv (fun φ => Dφ Yminus (p.1, φ)) p.2 = -Yminus p
  simp only [Yminus_Dφ]
  rw [deriv_const_mul_field]
  change -Complex.I * Dφ Yminus p = -Yminus p
  rw [Yminus_Dφ]
  calc
    _ = (Complex.I * Complex.I) * Yminus p := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem Yplus_equation (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularExpression (1 / 2) Yplus p = (1 / 2 : ℂ) * Yplus p := by
  have ha : (1 + p.1 : ℝ) ≠ 0 := by linarith [hp.1]
  have hb : (1 - p.1 ^ 2 : ℝ) ≠ 0 := by nlinarith [hp.1, hp.2]
  simp only [angularExpression, Yplus_Dμμ p hp.1, Yplus_Dμ p hp.1, Yplus_Dφφ,
    Yplus_Dφ, mul_zero, neg_zero, zero_add, sub_zero]
  push_cast
  have hca : (1 + (p.1 : ℂ)) ≠ 0 := by exact_mod_cast ha
  have hcb : (1 - (p.1 : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hb
  field_simp [hca, hcb]
  ring

theorem Yminus_equation (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularExpression (1 / 2) Yminus p = (1 / 2 : ℂ) * Yminus p := by
  have ha : (1 - p.1 : ℝ) ≠ 0 := by linarith [hp.2]
  have hb : (1 - p.1 ^ 2 : ℝ) ≠ 0 := by nlinarith [hp.1, hp.2]
  simp only [angularExpression, Yminus_Dμμ p hp.2, Yminus_Dμ p hp.2,
    Yminus_Dφφ, Yminus_Dφ, neg_neg]
  push_cast
  have hca : (1 - (p.1 : ℂ)) ≠ 0 := by exact_mod_cast ha
  have hcb : (1 - (p.1 : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hb
  field_simp [hca, hcb]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem Yplus_contDiffOn : ContDiffOn ℝ 2 Yplus (Ioo (-1 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  unfold Yplus plusAmplitude
  apply Complex.ofRealCLM.contDiff.contDiffAt.comp p
  exact (((contDiffAt_const.add contDiff_fst.contDiffAt).div_const 2).sqrt
    (by linarith [hp.1.1] : (1 + p.1) / 2 ≠ 0)).div_const (Real.sqrt (2 * Real.pi))

theorem Yminus_contDiffOn : ContDiffOn ℝ 2 Yminus (Ioo (-1 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  unfold Yminus minusAmplitude
  apply ContDiffAt.mul
  · apply Complex.ofRealCLM.contDiff.contDiffAt.comp p
    exact (((contDiffAt_const.sub contDiff_fst.contDiffAt).div_const 2).sqrt
      (by linarith [hp.1.2] : (1 - p.1) / 2 ≠ 0)).div_const (Real.sqrt (2 * Real.pi))
  · unfold MagHK.CylindricalOrbitals.phase
    exact Complex.conjCLE.contDiff.contDiffAt.comp p
      (Complex.contDiff_exp.contDiffAt.comp p
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp p contDiff_snd.contDiffAt).mul
          contDiffAt_const))

theorem Yplus_periodic (μ : ℝ) : Function.Periodic (fun φ => Yplus (μ, φ)) (2 * Real.pi) := by
  intro φ
  rfl

theorem Yminus_periodic (μ : ℝ) : Function.Periodic (fun φ => Yminus (μ, φ)) (2 * Real.pi) := by
  intro φ
  simp only [Yminus, MagHK.CylindricalOrbitals.phase, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat, add_mul]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem Yplus_energy (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularEnergy (1 / 2) Yplus p = (1 - p.1) / (8 * Real.pi) := by
  have ha : 1 + p.1 ≠ 0 := by linarith [hp.1]
  have hb : 1 - p.1 ^ 2 ≠ 0 := by
    have hm := mul_pos (show 0 < 1 - p.1 by linarith [hp.2])
      (show 0 < 1 + p.1 by linarith [hp.1])
    nlinarith
  simp only [angularEnergy, Yplus_Dμ p hp.1, Yplus_Dφ, mul_zero, zero_add]
  simp only [Yplus, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [div_pow, mul_pow, plusAmplitude_square p.1 ⟨hp.1.le, hp.2.le⟩]
  field_simp [ha, hb, ne_of_gt Real.pi_pos]
  ring

theorem Yminus_energy (p : Angle) (hp : p.1 ∈ Ioo (-1 : ℝ) 1) :
    angularEnergy (1 / 2) Yminus p = (1 + p.1) / (8 * Real.pi) := by
  have ha : 1 - p.1 ≠ 0 := by linarith [hp.2]
  have hb : 1 - p.1 ^ 2 ≠ 0 := by
    have hm := mul_pos (show 0 < 1 - p.1 by linarith [hp.2])
      (show 0 < 1 + p.1 by linarith [hp.1])
    nlinarith
  have hv : -Complex.I * Dφ Yminus p + ((1 / 2 : ℝ) * (1 - p.1) : ℝ) * Yminus p =
      (((1 / 2 : ℝ) * (1 - p.1) - 1 : ℝ) : ℂ) * Yminus p := by
    rw [Yminus_Dφ]
    calc
      _ = (Complex.I * Complex.I + ((1 / 2 : ℝ) * (1 - p.1) : ℝ)) * Yminus p := by ring
      _ = _ := by rw [Complex.I_mul_I]; push_cast; ring
  unfold angularEnergy
  rw [hv, Yminus_Dμ p hp.2]
  simp only [norm_div, norm_neg, norm_mul, Yminus, norm_mul,
    MagHK.CylindricalOrbitals.phase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, div_pow, mul_pow, sq_abs]
  rw [minusAmplitude_square p.1 ⟨hp.1.le, hp.2.le⟩]
  field_simp [ha, hb, ne_of_gt Real.pi_pos]
  ring

private theorem ae_interior : ∀ᵐ p ∂sphereMeasure, p.1 ∈ Ioo (-1 : ℝ) 1 := by
  have h : ∀ᵐ μ ∂cosineMeasure, μ ∈ Ioo (-1 : ℝ) 1 := by
    rw [cosineMeasure, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  exact Measure.quasiMeasurePreserving_fst.ae h

private theorem plus_model_integrable :
    Integrable (fun p : Angle => (1 - p.1) / (8 * Real.pi)) sphereMeasure := by
  have h : Integrable (fun μ : ℝ => (1 - μ) / (8 * Real.pi)) cosineMeasure :=
    (by fun_prop : Continuous (fun μ : ℝ => (1 - μ) / (8 * Real.pi))).continuousOn.integrableOn_Icc
  simpa only [sphereMeasure, mul_one] using! h.mul_prod (integrable_const (1 : ℝ) (μ := azimuthMeasure))

private theorem minus_model_integrable :
    Integrable (fun p : Angle => (1 + p.1) / (8 * Real.pi)) sphereMeasure := by
  have h : Integrable (fun μ : ℝ => (1 + μ) / (8 * Real.pi)) cosineMeasure :=
    (by fun_prop : Continuous (fun μ : ℝ => (1 + μ) / (8 * Real.pi))).continuousOn.integrableOn_Icc
  simpa only [sphereMeasure, mul_one] using! h.mul_prod (integrable_const (1 : ℝ) (μ := azimuthMeasure))

theorem Yplus_energy_integrable : Integrable (angularEnergy (1 / 2) Yplus) sphereMeasure := by
  apply plus_model_integrable.congr
  filter_upwards [ae_interior] with p hp
  exact (Yplus_energy p hp).symm

theorem Yminus_energy_integrable : Integrable (angularEnergy (1 / 2) Yminus) sphereMeasure := by
  apply minus_model_integrable.congr
  filter_upwards [ae_interior] with p hp
  exact (Yminus_energy p hp).symm

private theorem model_integral (s : ℝ) :
    (∫ p : Angle, (1 + s * p.1) / (8 * Real.pi) ∂sphereMeasure) = 1 / 2 := by
  have he : (fun p : Angle => (1 + s * p.1) / (8 * Real.pi)) =
      fun p => ((1 + s * p.1) / (8 * Real.pi)) * (1 : ℝ) := by simp
  rw [he, sphereMeasure, integral_prod_mul (fun μ : ℝ => (1 + s * μ) / (8 * Real.pi))
    (fun _ : ℝ => (1 : ℝ))]
  have hμ : (∫ μ, (1 + s * μ) / (8 * Real.pi) ∂cosineMeasure) = 1 / (4 * Real.pi) := by
    rw [cosineMeasure, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_div,
      intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
        (g := fun x : ℝ => s * x) intervalIntegrable_const
        ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    norm_num
    ring
  have hφ : (∫ _ : ℝ, (1 : ℝ) ∂azimuthMeasure) = 2 * Real.pi := by
    rw [azimuthMeasure, MagHK.CylindricalOrbitals.angularMeasure,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simp
    ring
  rw [hμ, hφ]
  field_simp [ne_of_gt Real.pi_pos]
  norm_num

theorem Yplus_energy_integral : (∫ p, angularEnergy (1 / 2) Yplus p ∂sphereMeasure) = 1 / 2 := by
  have h := model_integral (-1)
  rw [integral_congr_ae (ae_interior.mono (fun p hp => Yplus_energy p hp))]
  simpa only [neg_one_mul, sub_eq_add_neg] using h

theorem Yminus_energy_integral : (∫ p, angularEnergy (1 / 2) Yminus p ∂sphereMeasure) = 1 / 2 := by
  have h := model_integral 1
  rw [integral_congr_ae (ae_interior.mono (fun p hp => Yminus_energy p hp))]
  simpa using h

end MagHK.MonopoleAngular
