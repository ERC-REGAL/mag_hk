import MagHK.Monopole
import MagHK.MonopoleOrbital
import MagHK.AngularIntegral
import MagHK.CylindricalOrbitals

/-!
The explicit north-patch monopole doublet in the equal-area angular chart
μ = cos θ, with angular measure dμ dφ. The radial and angular trial
integrals are kept explicit. Any use of rotational quadrature is recorded
as a separate geometric hypothesis, never as an assumed Coulomb expectation.
-/

noncomputable section
namespace MagHK.MonopoleTrial

open MeasureTheory Set Filter
open MagHK.Monopole
open scoped ComplexConjugate ENNReal NNReal
set_option maxHeartbeats 1000000

abbrev Angle := ℝ × ℝ
def cosineMeasure : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 1)
def azimuthMeasure : Measure ℝ := MagHK.CylindricalOrbitals.angularMeasure
def sphereMeasure : Measure Angle := cosineMeasure.prod azimuthMeasure

instance : IsFiniteMeasure cosineMeasure := by unfold cosineMeasure; infer_instance
instance : IsFiniteMeasure azimuthMeasure := by unfold azimuthMeasure; infer_instance
instance : IsFiniteMeasure sphereMeasure := by unfold sphereMeasure; infer_instance

def plusAmplitude (μ : ℝ) : ℝ := Real.sqrt ((1 + μ) / 2) / Real.sqrt (2 * Real.pi)
def minusAmplitude (μ : ℝ) : ℝ := Real.sqrt ((1 - μ) / 2) / Real.sqrt (2 * Real.pi)

def Yplus (p : Angle) : ℂ := (plusAmplitude p.1 : ℂ)
def Yminus (p : Angle) : ℂ := (minusAmplitude p.1 : ℂ) * MagHK.CylindricalOrbitals.phase p.2

def angularDet (p q : Angle) : ℂ := MagHK.Slater.slaterSlice (Yplus p) (Yminus p) Yplus Yminus q

theorem amplitudes_continuous : Continuous plusAmplitude ∧ Continuous minusAmplitude := by
  constructor
  · unfold plusAmplitude
    fun_prop
  · unfold minusAmplitude
    fun_prop

theorem Yplus_continuous : Continuous Yplus :=
  Complex.continuous_ofReal.comp (amplitudes_continuous.1.comp continuous_fst)

theorem Yminus_continuous : Continuous Yminus :=
  (Complex.continuous_ofReal.comp (amplitudes_continuous.2.comp continuous_fst)).mul
    (MagHK.CylindricalOrbitals.phase_continuous.comp continuous_snd)

theorem plusAmplitude_square (μ : ℝ) (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    plusAmplitude μ ^ 2 = (1 + μ) / (4 * Real.pi) := by
  unfold plusAmplitude
  rw [div_pow, Real.sq_sqrt (by linarith [hμ.1]), Real.sq_sqrt (by positivity)]
  ring

theorem minusAmplitude_square (μ : ℝ) (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    minusAmplitude μ ^ 2 = (1 - μ) / (4 * Real.pi) := by
  unfold minusAmplitude
  rw [div_pow, Real.sq_sqrt (by linarith [hμ.2]), Real.sq_sqrt (by positivity)]
  ring

theorem plus_square_integral : (∫ μ, plusAmplitude μ ^ 2 ∂cosineMeasure) = 1 / (2 * Real.pi) := by
  have he : (∫ μ, plusAmplitude μ ^ 2 ∂cosineMeasure) =
      ∫ μ in Icc (-1 : ℝ) 1, (1 + μ) / (4 * Real.pi) :=
    setIntegral_congr_fun measurableSet_Icc plusAmplitude_square
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num
  ring

theorem minus_square_integral : (∫ μ, minusAmplitude μ ^ 2 ∂cosineMeasure) = 1 / (2 * Real.pi) := by
  have he : (∫ μ, minusAmplitude μ ^ 2 ∂cosineMeasure) =
      ∫ μ in Icc (-1 : ℝ) 1, (1 - μ) / (4 * Real.pi) :=
    setIntegral_congr_fun measurableSet_Icc minusAmplitude_square
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num
  ring

private theorem amplitudes_integrable (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f cosineMeasure := hf.continuousOn.integrableOn_Icc

theorem doublet_pairing_plus (p : Angle) :
    star (Yplus p) * Yplus p = ((plusAmplitude p.1 ^ 2 : ℝ) : ℂ) * 1 := by
  simp [Yplus, pow_two]

theorem doublet_pairing_minus (p : Angle) :
    star (Yminus p) * Yminus p = ((minusAmplitude p.1 ^ 2 : ℝ) : ℂ) * 1 := by
  simp only [Yminus, star_mul, Complex.star_def, Complex.conj_ofReal]
  have h := MagHK.CylindricalOrbitals.phase_pairing p.2
  change conj (MagHK.CylindricalOrbitals.phase p.2) * MagHK.CylindricalOrbitals.phase p.2 = 1 at h
  calc
    _ = (minusAmplitude p.1 : ℂ) ^ 2 *
        (conj (MagHK.CylindricalOrbitals.phase p.2) * MagHK.CylindricalOrbitals.phase p.2) := by ring
    _ = _ := by rw [h]; simp

theorem doublet_pairing_cross (p : Angle) :
    star (Yplus p) * Yminus p =
      ((plusAmplitude p.1 * minusAmplitude p.1 : ℝ) : ℂ) * MagHK.CylindricalOrbitals.phase p.2 := by
  simp [Yplus, Yminus, mul_assoc]

theorem doublet_pairing_reverse (p : Angle) :
    star (Yminus p) * Yplus p =
      ((plusAmplitude p.1 * minusAmplitude p.1 : ℝ) : ℂ) *
        conj (MagHK.CylindricalOrbitals.phase p.2) := by
  simp [Yplus, Yminus]
  ring

theorem doublet_orthonormal : MagHK.Slater.OrthonormalPair sphereMeasure Yplus Yminus := by
  have hp : Integrable (fun μ => ((plusAmplitude μ ^ 2 : ℝ) : ℂ)) cosineMeasure :=
    (amplitudes_integrable _ (amplitudes_continuous.1.pow 2)).ofReal
  have hm : Integrable (fun μ => ((minusAmplitude μ ^ 2 : ℝ) : ℂ)) cosineMeasure :=
    (amplitudes_integrable _ (amplitudes_continuous.2.pow 2)).ofReal
  have hc : Integrable (fun μ => ((plusAmplitude μ * minusAmplitude μ : ℝ) : ℂ)) cosineMeasure :=
    (amplitudes_integrable _
    (amplitudes_continuous.1.mul amplitudes_continuous.2)).ofReal
  have hphase : Integrable MagHK.CylindricalOrbitals.phase azimuthMeasure :=
    MagHK.CylindricalOrbitals.phase_integrable
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) azimuthMeasure := integrable_const 1
  constructor
  · simpa only [doublet_pairing_plus, sphereMeasure] using! hp.mul_prod hone
  · simpa only [doublet_pairing_minus, sphereMeasure] using! hm.mul_prod hone
  · simpa only [doublet_pairing_cross, sphereMeasure] using! hc.mul_prod hphase
  · simp_rw [doublet_pairing_reverse]
    simpa only [sphereMeasure, azimuthMeasure, Complex.star_def] using!
      hc.mul_prod MagHK.CylindricalOrbitals.star_phase_integrable
  · simp_rw [doublet_pairing_plus]
    rw [sphereMeasure, integral_prod_mul (fun μ => ((plusAmplitude μ ^ 2 : ℝ) : ℂ))
      (fun _ : ℝ => (1 : ℂ)), integral_complex_ofReal,
      plus_square_integral, azimuthMeasure, MagHK.CylindricalOrbitals.angular_one_integral]
    push_cast
    field_simp [ne_of_gt Real.pi_pos]
  · simp_rw [doublet_pairing_minus]
    rw [sphereMeasure, integral_prod_mul (fun μ => ((minusAmplitude μ ^ 2 : ℝ) : ℂ))
      (fun _ : ℝ => (1 : ℂ)), integral_complex_ofReal,
      minus_square_integral, azimuthMeasure, MagHK.CylindricalOrbitals.angular_one_integral]
    push_cast
    field_simp [ne_of_gt Real.pi_pos]
  · simp_rw [doublet_pairing_cross]
    rw [sphereMeasure, integral_prod_mul (fun μ => ((plusAmplitude μ * minusAmplitude μ : ℝ) : ℂ))
      MagHK.CylindricalOrbitals.phase, azimuthMeasure, MagHK.CylindricalOrbitals.phase_integral, mul_zero]
  · simp_rw [doublet_pairing_reverse]
    rw [sphereMeasure, integral_prod_mul (fun μ => ((plusAmplitude μ * minusAmplitude μ : ℝ) : ℂ))
      (fun θ => conj (MagHK.CylindricalOrbitals.phase θ)), integral_conj, azimuthMeasure,
      MagHK.CylindricalOrbitals.phase_integral, map_zero, mul_zero]

theorem angularDet_antisymmetric (p q : Angle) : angularDet p q = -angularDet q p :=
  MagHK.Slater.slater_antisymmetry _ _ p q

theorem angularDet_normalized_iterated :
    (∫ p, ∫ q, Complex.normSq (angularDet p q) ∂sphereMeasure ∂sphereMeasure) = 1 :=
  MagHK.Slater.slater_iterated_normalization sphereMeasure Yplus Yminus doublet_orthonormal

def spinorPlus (p : Angle) : ℂ := (Real.sqrt ((1 + p.1) / 2) : ℂ)
def spinorMinus (p : Angle) : ℂ :=
  (Real.sqrt ((1 - p.1) / 2) : ℂ) * MagHK.CylindricalOrbitals.phase p.2

theorem spinorPlus_normSq (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (spinorPlus p) = (1 + p.1) / 2 := by
  rw [spinorPlus, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by linarith [hp.1])]

theorem spinorMinus_normSq (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (spinorMinus p) = (1 - p.1) / 2 := by
  have hphase : Complex.normSq (MagHK.CylindricalOrbitals.phase p.2) = 1 := by
    rw [Complex.normSq_eq_norm_sq, MagHK.CylindricalOrbitals.phase_norm]
    norm_num
  rw [spinorMinus, Complex.normSq_mul, hphase, mul_one,
    Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (by linarith [hp.2])]

theorem spinor_normalized (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (spinorPlus p) + Complex.normSq (spinorMinus p) = 1 := by
  rw [spinorPlus_normSq p hp, spinorMinus_normSq p hp]
  ring

def direction (p : Angle) : Fin 3 → ℝ :=
  ![2 * (spinorPlus p * star (spinorMinus p)).re,
    2 * (spinorPlus p * star (spinorMinus p)).im,
    Complex.normSq (spinorPlus p) - Complex.normSq (spinorMinus p)]

def pairDot (p : Angle × Angle) : ℝ :=
  blochDot (spinorPlus p.1) (spinorMinus p.1) (spinorPlus p.2) (spinorMinus p.2)

theorem direction_third (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) : direction p 2 = p.1 := by
  change Complex.normSq (spinorPlus p) - Complex.normSq (spinorMinus p) = p.1
  rw [spinorPlus_normSq p hp, spinorMinus_normSq p hp]
  ring

theorem direction_norm_squared (p : Angle) (hp : p.1 ∈ Icc (-1 : ℝ) 1) :
    direction p 0 ^ 2 + direction p 1 ^ 2 + direction p 2 ^ 2 = 1 := by
  have h := spinor_normalized p hp
  have he (a b : ℂ) : (2 * (a * star b).re) ^ 2 + (2 * (a * star b).im) ^ 2 +
      (Complex.normSq a - Complex.normSq b) ^ 2 = (Complex.normSq a + Complex.normSq b) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  simpa [direction, he, h] using he (spinorPlus p) (spinorMinus p)

theorem pairDot_eq_dot (p q : Angle) :
    pairDot (p, q) = direction p 0 * direction q 0 +
      direction p 1 * direction q 1 + direction p 2 * direction q 2 := by
  simp [pairDot, direction, blochDot]

theorem Yplus_eq_spinor (p : Angle) :
    Yplus p = spinorPlus p / (Real.sqrt (2 * Real.pi) : ℂ) := by
  simp [Yplus, plusAmplitude, spinorPlus]

theorem Yminus_eq_spinor (p : Angle) :
    Yminus p = spinorMinus p / (Real.sqrt (2 * Real.pi) : ℂ) := by
  simp [Yminus, minusAmplitude, spinorMinus]
  ring

theorem angularDet_scaled (p q : Angle) :
    angularDet p q = MagHK.Slater.scale *
      ((spinorPlus p * spinorMinus q - spinorMinus p * spinorPlus q) /
        ((2 * Real.pi : ℝ) : ℂ)) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = ((2 * Real.pi : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  simp only [angularDet, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice,
    Yplus_eq_spinor, Yminus_eq_spinor, div_mul_div_comm, ← sub_div]
  rw [← pow_two, hs]

theorem angularDet_probability (p q : Angle)
    (hp : p.1 ∈ Icc (-1 : ℝ) 1) (hq : q.1 ∈ Icc (-1 : ℝ) 1) :
    Complex.normSq (angularDet p q) = (1 - pairDot (p, q)) / (16 * Real.pi ^ 2) := by
  have hscale : Complex.normSq MagHK.Slater.scale = (1 / 2 : ℝ) := by
    rw [MagHK.Slater.scale, Complex.normSq_inv, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt (by norm_num)]
    norm_num
  rw [angularDet_scaled, Complex.normSq_mul, hscale, Complex.normSq_div, Complex.normSq_ofReal]
  have h := normalized_angular_pair_probability
    (spinorPlus p) (spinorMinus p) (spinorPlus q) (spinorMinus q)
    (spinor_normalized p hp) (spinor_normalized q hq)
  change _ = (1 - blochDot _ _ _ _) / (16 * Real.pi ^ 2)
  rw [← h]
  ring

theorem cosine_ae : ∀ᵐ μ ∂cosineMeasure, μ ∈ Icc (-1 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

theorem angle_ae : ∀ᵐ p ∂sphereMeasure, p.1 ∈ Icc (-1 : ℝ) 1 :=
  Measure.quasiMeasurePreserving_fst.ae cosine_ae

theorem angularDet_probability_ae :
    ∀ᵐ p ∂sphereMeasure.prod sphereMeasure,
      Complex.normSq (angularDet p.1 p.2) = (1 - pairDot p) / (16 * Real.pi ^ 2) := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae angle_ae,
    Measure.quasiMeasurePreserving_snd.ae angle_ae] with p hp hq
  exact angularDet_probability p.1 p.2 hp hq

private theorem integrable_normSq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℂ) (h : Integrable (fun x => star (f x) * f x) μ) :
    Integrable (fun x => Complex.normSq (f x)) μ := by
  have hi : Integrable (fun x => (star (f x) * f x).re) μ := h.re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using hi

theorem angularDet_product_integrable :
    Integrable (fun p : Angle × Angle => Complex.normSq (angularDet p.1 p.2))
      (sphereMeasure.prod sphereMeasure) := by
  have hc : Continuous (fun p : Angle × Angle => angularDet p.1 p.2) := by
    unfold angularDet MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
    exact continuous_const.mul (((Yplus_continuous.comp continuous_fst).mul
      (Yminus_continuous.comp continuous_snd)).sub
      ((Yminus_continuous.comp continuous_fst).mul (Yplus_continuous.comp continuous_snd)))
  apply (integrable_prod_iff (Complex.continuous_normSq.comp hc).aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro p
    exact integrable_normSq sphereMeasure (angularDet p)
      (MagHK.Slater.integrable_slater_pairing sphereMeasure Yplus Yminus doublet_orthonormal
        (Yplus p) (Yminus p) (Yplus p) (Yminus p))
  · have hi := ((integrable_normSq sphereMeasure Yplus doublet_orthonormal.integrable_ff).add
      (integrable_normSq sphereMeasure Yminus doublet_orthonormal.integrable_gg)).div_const 2
    have heq (p : Angle) : (∫ q, ‖Complex.normSq (angularDet p q)‖ ∂sphereMeasure) =
        (Complex.normSq (Yplus p) + Complex.normSq (Yminus p)) / 2 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
      have h := MagHK.Slater.slater_density_marginal sphereMeasure Yplus Yminus
        doublet_orthonormal (Yplus p) (Yminus p)
      change 2 * (∫ q, Complex.normSq (angularDet p q) ∂sphereMeasure) = _ at h
      linarith
    change Integrable (fun p => ∫ q, ‖Complex.normSq (angularDet p q)‖ ∂sphereMeasure) sphereMeasure
    simp_rw [heq]
    exact hi

theorem angularDet_normalized :
    (∫ p : Angle × Angle, Complex.normSq (angularDet p.1 p.2)
      ∂sphereMeasure.prod sphereMeasure) = 1 := by
  rw [integral_prod _ angularDet_product_integrable]
  exact angularDet_normalized_iterated

def radialVolume : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => (Real.toNNReal (r ^ 2) : ℝ≥0∞))

instance : SFinite radialVolume := by unfold radialVolume; infer_instance

theorem radialVolume_integral (f : ℝ → ℝ) :
    (∫ r, f r ∂radialVolume) = ∫ r in Ioi (0 : ℝ), r ^ 2 * f r := by
  have hm : Measurable (fun r : ℝ => Real.toNNReal (r ^ 2)) := by fun_prop
  have he := integral_withDensity_eq_integral_smul (μ := volume.restrict (Ioi (0 : ℝ)))
    (g := f) hm
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Real.toNNReal (r ^ 2) : ℝ) • f r := by
      simpa only [radialVolume] using! he
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun r => by simp [Real.coe_toNNReal, sq_nonneg r])

theorem radialOrbital_integrable_radialVolume :
    Integrable (fun r => radialOrbital r ^ 2) radialVolume := by
  have hm : Measurable (fun r : ℝ => Real.toNNReal (r ^ 2)) := by fun_prop
  have hi : Integrable (fun r => (Real.toNNReal (r ^ 2) : ℝ) • radialOrbital r ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul] using! radialOrbital_squared_integrable
  simpa only [radialVolume] using! (integrable_withDensity_iff_integrable_smul hm).mpr hi

theorem radialOrbital_normalized_radialVolume :
    (∫ r, radialOrbital r ^ 2 ∂radialVolume) = 1 := by
  rw [radialVolume_integral, radialOrbital_normalized]

abbrev TrialCoordinates := (ℝ × ℝ) × (Angle × Angle)
def trialMeasure : Measure TrialCoordinates :=
  (radialVolume.prod radialVolume).prod (sphereMeasure.prod sphereMeasure)

def trial (x : TrialCoordinates) : ℂ :=
  ((radialOrbital x.1.1 * radialOrbital x.1.2 : ℝ) : ℂ) * angularDet x.2.1 x.2.2

def orbitalPlus (x : ℝ × Angle) : ℂ := (radialOrbital x.1 : ℂ) * Yplus x.2
def orbitalMinus (x : ℝ × Angle) : ℂ := (radialOrbital x.1 : ℂ) * Yminus x.2

theorem trial_is_determinant (s t : ℝ) (p q : Angle) :
    trial ((s, t), (p, q)) =
      MagHK.Slater.slaterSlice (orbitalPlus (s, p)) (orbitalMinus (s, p))
        orbitalPlus orbitalMinus (t, q) := by
  unfold trial angularDet orbitalPlus orbitalMinus MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
  push_cast
  ring

theorem trial_probability (x : TrialCoordinates) :
    Complex.normSq (trial x) =
      (radialOrbital x.1.1 ^ 2 * radialOrbital x.1.2 ^ 2) *
        Complex.normSq (angularDet x.2.1 x.2.2) := by
  rw [trial, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem trial_integrable_normSq : Integrable (fun x => Complex.normSq (trial x)) trialMeasure := by
  simp_rw [trial_probability]
  exact (radialOrbital_integrable_radialVolume.mul_prod radialOrbital_integrable_radialVolume).mul_prod
    angularDet_product_integrable

theorem trial_normalized : (∫ x, Complex.normSq (trial x) ∂trialMeasure) = 1 := by
  simp_rw [trial_probability]
  rw [trialMeasure, integral_prod_mul (fun p : ℝ × ℝ => radialOrbital p.1 ^ 2 * radialOrbital p.2 ^ 2)
    (fun p : Angle × Angle => Complex.normSq (angularDet p.1 p.2)),
    integral_prod_mul (fun r : ℝ => radialOrbital r ^ 2) (fun r : ℝ => radialOrbital r ^ 2),
    radialOrbital_normalized_radialVolume, angularDet_normalized]
  norm_num

/-- The Euclidean distance of the two explicit unit directions, scaled by their radii. -/
def pairDistance (s t : ℝ) (p : Angle × Angle) : ℝ :=
  Real.sqrt ((s * direction p.1 0 - t * direction p.2 0) ^ 2 +
    (s * direction p.1 1 - t * direction p.2 1) ^ 2 +
    (s * direction p.1 2 - t * direction p.2 2) ^ 2)

theorem pairDistance_eq (s t : ℝ) (p : Angle × Angle)
    (hp : p.1.1 ∈ Icc (-1 : ℝ) 1) (hq : p.2.1 ∈ Icc (-1 : ℝ) 1) :
    pairDistance s t p = Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * pairDot p) := by
  unfold pairDistance
  congr 1
  have h1 := direction_norm_squared p.1 hp
  have h2 := direction_norm_squared p.2 hq
  rw [pairDot_eq_dot]
  calc
    _ = s ^ 2 * (direction p.1 0 ^ 2 + direction p.1 1 ^ 2 + direction p.1 2 ^ 2) +
      t ^ 2 * (direction p.2 0 ^ 2 + direction p.2 1 ^ 2 + direction p.2 2 ^ 2) -
      2 * s * t * (direction p.1 0 * direction p.2 0 +
        direction p.1 1 * direction p.2 1 + direction p.1 2 * direction p.2 2) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem pairDot_continuous : Continuous pairDot := by
  have hp : Continuous spinorPlus := by unfold spinorPlus; fun_prop
  have hm : Continuous spinorMinus := by
    unfold spinorMinus
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      ((continuous_const.sub continuous_fst).div_const 2))).mul
      (MagHK.CylindricalOrbitals.phase_continuous.comp continuous_snd)
  unfold pairDot blochDot
  fun_prop

/-- Remaining geometric input. This is the uniform dot-product pushforward law
for two independent surface elements dμ dφ, not a trial-state expectation.
No instance or axiom of this proposition is supplied by this file. -/
def SphericalPairQuadrature : Prop :=
  Measure.map pairDot (sphereMeasure.prod sphereMeasure) =
    ENNReal.ofReal (8 * Real.pi ^ 2) • volume.restrict (Icc (-1 : ℝ) 1)

def angularCoulomb (s t : ℝ) : ℝ :=
  ∫ p : Angle × Angle, Complex.normSq (angularDet p.1 p.2) / pairDistance s t p
    ∂sphereMeasure.prod sphereMeasure

theorem angularCoulomb_eq_kernel (hquad : SphericalPairQuadrature)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : angularCoulomb s t = angularKernel s t := by
  have hf : StronglyMeasurable (fun μ : ℝ =>
      (1 - μ) / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * μ)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  have hmap := integral_map_of_stronglyMeasurable
    (μ := sphereMeasure.prod sphereMeasure) pairDot_continuous.measurable hf
  change Measure.map pairDot (sphereMeasure.prod sphereMeasure) = _ at hquad
  rw [hquad, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hmap
  have he : angularCoulomb s t = (1 / (16 * Real.pi ^ 2)) *
      ∫ p : Angle × Angle, (1 - pairDot p) /
        Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * pairDot p)
        ∂sphereMeasure.prod sphereMeasure := by
    rw [angularCoulomb, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae angle_ae,
      Measure.quasiMeasurePreserving_snd.ae angle_ae] with p hp hq
    rw [angularDet_probability p.1 p.2 hp hq, pairDistance_eq s t p hp hq]
    ring
  rw [he, ← hmap]
  have hscalar : (1 / (16 * Real.pi ^ 2)) * (8 * Real.pi ^ 2) = (1 / 2 : ℝ) := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [← mul_assoc, hscalar]
  exact angular_integral s t hs ht

/-- Literal iterated Coulomb integral of the normalized trial, retaining both
angular variables and the radial Jacobians s²t². -/
def trialCoulombIterated : ℝ :=
  ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
    ∫ p : Angle × Angle, s ^ 2 * t ^ 2 * Complex.normSq (trial ((s, t), p)) /
      pairDistance s t p ∂sphereMeasure.prod sphereMeasure

theorem trialCoulombIterated_eq (hquad : SphericalPairQuadrature) :
    trialCoulombIterated = radialCoulombExpectation := by
  unfold trialCoulombIterated radialCoulombExpectation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have he (p : Angle × Angle) :
      s ^ 2 * t ^ 2 * Complex.normSq (trial ((s, t), p)) / pairDistance s t p =
      (s ^ 2 * radialOrbital s ^ 2) * (t ^ 2 * radialOrbital t ^ 2) *
        (Complex.normSq (angularDet p.1 p.2) / pairDistance s t p) := by
    rw [trial_probability]
    ring
  simp_rw [he]
  rw [integral_const_mul, radialOrbital_squared_density s hs,
    radialOrbital_squared_density t ht]
  change radialDensity s * radialDensity t * angularCoulomb s t = _
  rw [angularCoulomb_eq_kernel hquad s t hs ht]
  ring

theorem trialCoulombIterated_bound (hquad : SphericalPairQuadrature) :
    trialCoulombIterated ≤ coulombBound ∧ trialCoulombIterated < freeGap := by
  rw [trialCoulombIterated_eq hquad]
  exact ⟨radialCoulombExpectation_bound, radialCoulombExpectation_bound.trans_lt coulomb_bound_lt_gap⟩

theorem conjugate_trial_probability (x : TrialCoordinates) :
    Complex.normSq (conj (trial x)) = Complex.normSq (trial x) := by simp

end MagHK.MonopoleTrial
