import MagHK.CartesianOrbitals
import MagHK.ConstructionData
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual Cartesian two-orbital determinant, its normalization, positive
density, and cancellation of the physical current. -/

noncomputable section
namespace MagHK.ConcreteSlater

open MeasureTheory Set Filter
open MagHK.Noninteracting MagHK.Axial MagHK.CylindricalOrbitals
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

abbrev Space := ℂ × ℝ

def amplitudeZero (t c : ℝ) (x : Space) : ℝ :=
  normalization t * profileF t ‖x.1‖ * chi c x.2

def amplitudeMinus (t c : ℝ) (x : Space) : ℝ :=
  normalization t * Real.sqrt t * Real.exp (Real.sqrt (1 + ‖x.1‖ ^ 2) - 1) *
    profileF t ‖x.1‖ * chi c x.2

def wave (t c : ℝ) (x y : Space) : ℂ :=
  MagHK.Slater.slaterSlice (MagHK.CartesianOrbitals.orbitalZero t c x)
    (MagHK.CartesianOrbitals.orbitalMinus t c x)
    (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) y

def density (t c : ℝ) (x : Space) : ℝ :=
  Complex.normSq (MagHK.CartesianOrbitals.orbitalZero t c x) +
    Complex.normSq (MagHK.CartesianOrbitals.orbitalMinus t c x)

theorem normalization_pos (t : ℝ) (ht : 0 ≤ t) : 0 < normalization t := by
  unfold normalization
  exact inv_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (radialNormF_pos t ht)))

theorem amplitudeZero_pos (t c : ℝ) (ht : 0 ≤ t) (hc : 0 < c) (x : Space) :
    0 < amplitudeZero t c x :=
  mul_pos (mul_pos (normalization_pos t ht) (profileF_pos t ‖x.1‖)) (chi_pos c x.2 hc)

theorem density_pos (t c : ℝ) (ht : 0 ≤ t) (hc : 0 < c) (x : Space) :
    0 < density t c x := by
  have h : 0 < Complex.normSq (MagHK.CartesianOrbitals.orbitalZero t c x) := by
    change 0 < Complex.normSq ((amplitudeZero t c x : ℝ) : ℂ)
    simpa using ne_of_gt (amplitudeZero_pos t c ht hc x)
  exact add_pos_of_pos_of_nonneg h (Complex.normSq_nonneg _)

theorem wave_antisymmetric (t c : ℝ) (x y : Space) : wave t c x y = -wave t c y x :=
  MagHK.Slater.slater_antisymmetry _ _ x y

theorem wave_density_marginal (t c : ℝ)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c))
    (x : Space) : 2 * (∫ y, Complex.normSq (wave t c x y)) = density t c x :=
  MagHK.Slater.slater_density_marginal volume _ _ h _ _

private theorem normSq_integrable {f : Space → ℂ}
    (h : Integrable (fun x => star (f x) * f x)) :
    Integrable (fun x => Complex.normSq (f x)) := by
  have hi : Integrable (fun x => (star (f x) * f x).re) := h.re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re] using hi

theorem density_integrable (t c : ℝ)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    Integrable (density t c) :=
  (normSq_integrable h.integrable_ff).add (normSq_integrable h.integrable_gg)

theorem wave_normSq_integrable (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    Integrable (fun p : Space × Space => Complex.normSq (wave t c p.1 p.2)) := by
  have hf := MagHK.CartesianOrbitals.orbitalZero_continuous t c ht
  have hg := MagHK.CartesianOrbitals.orbitalMinus_continuous t c ht
  have hw : Continuous (fun p : Space × Space => wave t c p.1 p.2) := by
    unfold wave MagHK.Slater.slaterSlice MagHK.Slater.determinantSlice
    exact continuous_const.mul (((hf.comp continuous_fst).mul (hg.comp continuous_snd)).sub
      ((hg.comp continuous_fst).mul (hf.comp continuous_snd)))
  apply (integrable_prod_iff (Complex.continuous_normSq.comp hw).aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro x
    exact normSq_integrable (MagHK.Slater.integrable_slater_pairing volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) h
      (MagHK.CartesianOrbitals.orbitalZero t c x) (MagHK.CartesianOrbitals.orbitalMinus t c x)
      (MagHK.CartesianOrbitals.orbitalZero t c x) (MagHK.CartesianOrbitals.orbitalMinus t c x))
  · have heq : (fun x => ∫ y, ‖Complex.normSq (wave t c x y)‖) =
        (fun x => density t c x / 2) := by
      funext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
      linarith [wave_density_marginal t c h x]
    change Integrable (fun x => ∫ y, ‖Complex.normSq (wave t c x y)‖)
    rw [heq]
    exact (density_integrable t c h).div_const 2

theorem wave_normalized (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    (∫ p : Space × Space, Complex.normSq (wave t c p.1 p.2)) = 1 := by
  rw [Measure.volume_eq_prod Space Space]
  rw [integral_prod _ (wave_normSq_integrable t c ht h)]
  exact MagHK.Slater.slater_iterated_normalization volume _ _ h

theorem exists_normalized_positive_density (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      (∫ p : Space × Space, Complex.normSq (wave t c p.1 p.2)) = 1 ∧
      (∀ x y, wave t c x y = -wave t c y x) ∧
      (∀ x, 0 < 2 * ∫ y, Complex.normSq (wave t c x y)) := by
  obtain ⟨t, ht, h⟩ := MagHK.CartesianOrbitals.exists_bounded_orthonormal c hc
  refine ⟨t, ht, wave_normalized t c ht.le h, wave_antisymmetric t c, ?_⟩
  intro x
  rw [wave_density_marginal t c h x]
  exact density_pos t c ht.le hc x

def realCoordinates (x : Space) : MagHK.ConstructionData.Space := ((x.1.re, x.1.im), x.2)

/-- Pairing a Cartesian direction with the actual constructed vector potential. -/
def fieldPairing (t : ℝ) (x d : Space) : ℝ :=
  let A := MagHK.ConstructionData.bounded3Vector t (realCoordinates x)
  A.1.1 * d.1.re + A.1.2 * d.1.im + A.2 * d.2

theorem amplitudeZero_differentiableAt (t c : ℝ) (ht : 0 ≤ t)
    (x : Space) (hx : x.1 ≠ 0) : DifferentiableAt ℝ (amplitudeZero t c) x := by
  have hn : DifferentiableAt ℝ (fun y : Space => ‖y.1‖) x :=
    differentiableAt_fst.norm ℝ hx
  have hf := (profileF_hasDerivAt t ‖x.1‖ ht).differentiableAt.comp x hn
  have hc := (chi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  exact ((differentiableAt_const (normalization t)).mul hf).mul hc

theorem amplitudeMinus_differentiableAt (t c : ℝ) (ht : 0 ≤ t)
    (x : Space) (hx : x.1 ≠ 0) : DifferentiableAt ℝ (amplitudeMinus t c) x := by
  have hn : DifferentiableAt ℝ (fun y : Space => ‖y.1‖) x :=
    differentiableAt_fst.norm ℝ hx
  have hf := (profileF_hasDerivAt t ‖x.1‖ ht).differentiableAt.comp x hn
  have hc := (chi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  have he : DifferentiableAt ℝ (fun y : Space =>
      Real.exp (Real.sqrt (1 + ‖y.1‖ ^ 2) - 1)) x :=
    ((((differentiableAt_const (1 : ℝ)).add (hn.pow 2)).sqrt
      (show 1 + ‖x.1‖ ^ 2 ≠ 0 from ne_of_gt (by positivity))).sub_const 1).exp
  exact (((differentiableAt_const (normalization t * Real.sqrt t)).mul he).mul hf).mul hc

theorem orbitalZero_differentiableAt (t c : ℝ) (ht : 0 ≤ t)
    (x : Space) (hx : x.1 ≠ 0) :
    DifferentiableAt ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x :=
  Complex.ofRealCLM.differentiableAt.comp x (amplitudeZero_differentiableAt t c ht x hx)

theorem orbitalMinus_differentiableAt (t c : ℝ) (ht : 0 ≤ t)
    (x : Space) (hx : x.1 ≠ 0) :
    DifferentiableAt ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x :=
  (Complex.ofRealCLM.differentiableAt.comp x
    (amplitudeMinus_differentiableAt t c ht x hx)).mul
      (Complex.conjCLE.differentiableAt.comp x differentiableAt_fst)

theorem real_amplitude_current (B : Space → ℝ) (x d : Space)
    (hB : DifferentiableAt ℝ B x) :
    (star (B x : ℂ) * fderiv ℝ (fun y => (B y : ℂ)) x d).im = 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hB.hasFDerivAt
  change HasFDerivAt (fun y => (B y : ℂ)) _ x at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply]

theorem conjugate_amplitude_current (B : Space → ℝ) (x d : Space)
    (hB : DifferentiableAt ℝ B x) :
    (star ((B x : ℂ) * conj x.1) *
      fderiv ℝ (fun y : Space => (B y : ℂ) * conj y.1) x d).im =
      B x ^ 2 * (x.1.im * d.1.re - x.1.re * d.1.im) := by
  have hreal := Complex.ofRealCLM.hasFDerivAt.comp x hB.hasFDerivAt
  have hconj := Complex.conjCLE.hasFDerivAt.comp x
    (hasFDerivAt_fst : HasFDerivAt (fun y : Space => y.1)
      (ContinuousLinearMap.fst ℝ ℂ ℝ) x)
  have h := hreal.mul hconj
  change HasFDerivAt (fun y : Space => (B y : ℂ) * conj y.1) _ x at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem radiusSq_eq_norm (z : ℂ) : MagHK.Cartesian.radiusSq (z.re, z.im) = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [MagHK.Cartesian.radiusSq, pow_two]

theorem density_formula (t c : ℝ) (x : Space) :
    density t c x = amplitudeZero t c x ^ 2 + amplitudeMinus t c x ^ 2 * ‖x.1‖ ^ 2 := by
  change Complex.normSq (amplitudeZero t c x : ℂ) +
    Complex.normSq ((amplitudeMinus t c x : ℂ) * conj x.1) = _
  rw [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal,
    Complex.normSq_ofReal, Complex.normSq_eq_norm_sq]
  ring

theorem density_times_coefficient (t c : ℝ) (ht : 0 ≤ t) (x : Space) :
    density t c x * MagHK.Cartesian.boundedCoefficient t (x.1.re, x.1.im) =
      amplitudeMinus t c x ^ 2 := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hD : 1 + t * ‖x.1‖ ^ 2 *
      Real.exp (Real.sqrt (1 + ‖x.1‖ ^ 2) - 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [density_formula]
  unfold MagHK.Cartesian.boundedCoefficient MagHK.Cartesian.radialExponential
  rw [radiusSq_eq_norm]
  unfold amplitudeZero amplitudeMinus
  simp only [mul_pow, hs]
  field_simp
  <;> ring

theorem orbital_current_cancels (t c : ℝ) (ht : 0 ≤ t) (x d : Space)
    (hx : x.1 ≠ 0) :
    (star (MagHK.CartesianOrbitals.orbitalZero t c x) *
      fderiv ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x d).im +
    (star (MagHK.CartesianOrbitals.orbitalMinus t c x) *
      fderiv ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x d).im +
      density t c x * fieldPairing t x d = 0 := by
  have hz := real_amplitude_current (amplitudeZero t c) x d
    (amplitudeZero_differentiableAt t c ht x hx)
  have hg := conjugate_amplitude_current (amplitudeMinus t c) x d
    (amplitudeMinus_differentiableAt t c ht x hx)
  change (star (amplitudeZero t c x : ℂ) *
      fderiv ℝ (fun y => (amplitudeZero t c y : ℂ)) x d).im +
    (star ((amplitudeMinus t c x : ℂ) * conj x.1) *
      fderiv ℝ (fun y : Space => (amplitudeMinus t c y : ℂ) * conj y.1) x d).im +
      density t c x * fieldPairing t x d = 0
  rw [hz, hg]
  have hc := density_times_coefficient t c ht x
  unfold fieldPairing MagHK.ConstructionData.bounded3Vector realCoordinates MagHK.Cartesian.boundedVector
  dsimp
  calc
    _ = (amplitudeMinus t c x ^ 2 - density t c x *
        MagHK.Cartesian.boundedCoefficient t (x.1.re, x.1.im)) *
        (x.1.im * d.1.re - x.1.re * d.1.im) := by ring
    _ = 0 := by rw [hc]; ring

theorem wave_fderiv_apply (t c : ℝ) (ht : 0 ≤ t) (x y d : Space) (hx : x.1 ≠ 0) :
    fderiv ℝ (fun z => wave t c z y) x d =
      MagHK.Slater.slaterSlice
        (fderiv ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x d)
        (fderiv ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x d)
        (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) y := by
  have hf := (orbitalZero_differentiableAt t c ht x hx).hasFDerivAt
  have hg := (orbitalMinus_differentiableAt t c ht x hx).hasFDerivAt
  have h := ((hf.mul_const (MagHK.CartesianOrbitals.orbitalMinus t c y)).sub
    (hg.mul_const (MagHK.CartesianOrbitals.orbitalZero t c y))).const_mul MagHK.Slater.scale
  change HasFDerivAt (fun z => MagHK.Slater.scale *
    (MagHK.CartesianOrbitals.orbitalZero t c z * MagHK.CartesianOrbitals.orbitalMinus t c y -
      MagHK.CartesianOrbitals.orbitalMinus t c z * MagHK.CartesianOrbitals.orbitalZero t c y)) _ x at h
  change fderiv ℝ (fun z => MagHK.Slater.scale *
    (MagHK.CartesianOrbitals.orbitalZero t c z * MagHK.CartesianOrbitals.orbitalMinus t c y -
      MagHK.CartesianOrbitals.orbitalMinus t c z * MagHK.CartesianOrbitals.orbitalZero t c y)) x d = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  ring

/-- Directional physical current, using the actual derivative of the determinant
and the actual Cartesian vector potential. -/
def physicalCurrent (t c : ℝ) (x d : Space) : ℝ :=
  2 * (∫ y, (star (wave t c x y) * fderiv ℝ (fun z => wave t c z y) x d).im) +
    (2 * ∫ y, Complex.normSq (wave t c x y)) * fieldPairing t x d

theorem physicalCurrent_zero_off_axis (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c))
    (x d : Space) (hx : x.1 ≠ 0) : physicalCurrent t c x d = 0 := by
  unfold physicalCurrent
  simp_rw [wave_fderiv_apply t c ht x _ d hx]
  rw [wave_density_marginal t c h x]
  have hm := MagHK.Slater.slater_current_marginal volume
    (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) h
    (MagHK.CartesianOrbitals.orbitalZero t c x) (MagHK.CartesianOrbitals.orbitalMinus t c x)
    (fderiv ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x d)
    (fderiv ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x d)
  change 2 * (∫ y, (star (MagHK.Slater.slaterSlice
    (MagHK.CartesianOrbitals.orbitalZero t c x) (MagHK.CartesianOrbitals.orbitalMinus t c x)
    (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) y) * _).im) + _ = 0
  rw [hm]
  exact orbital_current_cancels t c ht x d hx

theorem off_axis_ae : ∀ᵐ x : Space, x.1 ≠ 0 :=
  Measure.quasiMeasurePreserving_fst.ae ((volume : Measure ℂ).ae_ne 0)

theorem physicalCurrent_zero_ae (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) :
    ∀ᵐ x : Space, ∀ d : Space, physicalCurrent t c x d = 0 := by
  filter_upwards [off_axis_ae] with x hx
  exact fun d => physicalCurrent_zero_off_axis t c ht h x d hx

theorem exists_normalized_zero_current_slater (c : ℝ) (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧
      (∫ p : Space × Space, Complex.normSq (wave t c p.1 p.2)) = 1 ∧
      (∀ x y, wave t c x y = -wave t c y x) ∧
      (∀ x, 0 < 2 * ∫ y, Complex.normSq (wave t c x y)) ∧
      (∀ᵐ x : Space, ∀ d : Space, physicalCurrent t c x d = 0) := by
  obtain ⟨t, ht, h⟩ := MagHK.CartesianOrbitals.exists_bounded_orthonormal c hc
  refine ⟨t, ht, wave_normalized t c ht.le h, wave_antisymmetric t c, ?_,
    physicalCurrent_zero_ae t c ht.le h⟩
  intro x
  rw [wave_density_marginal t c h x]
  exact density_pos t c ht.le hc x

end MagHK.ConcreteSlater
