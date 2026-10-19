import MagHK.GeneralGaugeWeak
import MagHK.GaussianSlater
import MagHK.NoninteractingTheorem

/-! Current transport with explicit integrability, and the axis in the concrete
noninteracting constructions. No kinetic estimate is inferred merely from the
semiboundedness of a total closed form. -/
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate ContDiff Topology
namespace MagHK.CurrentCompletion

/-- A radial function with zero derivative at the origin is differentiable
there after composition with the norm. -/
theorem radial_hasFDerivAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (hf : HasDerivAt f 0 0) :
    HasFDerivAt (fun x : E => f ‖x‖) (0 : E →L[ℝ] ℝ) 0 := by
  have h : (fun r : ℝ => f r - f 0) =o[𝓝 0] (fun r => r) := by
    simpa using (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf.hasFDerivAt)
  have hn : Tendsto (fun x : E => ‖x‖) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, norm_zero] using
      (continuous_norm.continuousAt : ContinuousAt (fun x : E => ‖x‖) 0)
  have hc := h.comp_tendsto hn
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  simpa only [Function.comp_def, zero_add, norm_zero, zero_apply, sub_zero] using hc.of_norm_right

abbrev Space := ℂ × ℝ

theorem bounded_radial_differentiable (t : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (fun z : ℂ => Noninteracting.profileF t ‖z‖) := by
  intro z
  by_cases hz : z = 0
  · subst z
    apply (radial_hasFDerivAt_zero _ ?_).differentiableAt
    simpa [Noninteracting.profileU, Noninteracting.boundedU,
      Noninteracting.profileH, Noninteracting.profileHPrime,
      Noninteracting.profileA, Noninteracting.boundedA, Noninteracting.profileR]
      using Noninteracting.profileF_hasDerivAt t 0 ht
  · exact (Noninteracting.profileF_hasDerivAt t ‖z‖ ht).differentiableAt.comp z
      (differentiableAt_id.norm ℝ hz)

theorem gaussian_radial_differentiable (t : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (fun z : ℂ => Noninteracting.gaussianF t ‖z‖) := by
  intro z
  by_cases hz : z = 0
  · subst z
    apply (radial_hasFDerivAt_zero _ ?_).differentiableAt
    simpa [Noninteracting.gaussianA] using Noninteracting.gaussianF_hasDerivAt t 0 ht
  · exact (Noninteracting.gaussianF_hasDerivAt t ‖z‖ ht).differentiableAt.comp z
      (differentiableAt_id.norm ℝ hz)

end MagHK.CurrentCompletion

namespace MagHK.CurrentCompletion.Bounded
open MagHK.ConcreteSlater

theorem amplitudeZero_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (amplitudeZero t c) := by
  intro x
  have hf := (bounded_radial_differentiable t ht).differentiableAt.comp x differentiableAt_fst
  have hc := (Axial.chi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  exact ((differentiableAt_const (CylindricalOrbitals.normalization t)).mul hf).mul hc

theorem amplitudeMinus_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (amplitudeMinus t c) := by
  intro x
  have hf := (bounded_radial_differentiable t ht).differentiableAt.comp x differentiableAt_fst
  have hc := (Axial.chi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  have he : DifferentiableAt ℝ (fun y : Space =>
      Real.exp (Real.sqrt (1 + ‖y.1‖ ^ 2) - 1)) x :=
    ((((differentiableAt_const (1 : ℝ)).add (differentiableAt_fst.norm_sq ℝ)).sqrt
      (show 1 + ‖x.1‖ ^ 2 ≠ 0 from ne_of_gt (by positivity))).sub_const 1).exp
  exact (((differentiableAt_const (CylindricalOrbitals.normalization t * Real.sqrt t)).mul he).mul hf).mul hc

theorem orbitalZero_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (MagHK.CartesianOrbitals.orbitalZero t c) := by
  intro x
  exact Complex.ofRealCLM.differentiableAt.comp x (amplitudeZero_differentiable t c ht x)

theorem orbitalMinus_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) := by
  intro x
  exact (Complex.ofRealCLM.differentiableAt.comp x
    (amplitudeMinus_differentiable t c ht x)).mul
      (Complex.conjCLE.differentiableAt.comp x differentiableAt_fst)

theorem orbital_current_cancels (t c : ℝ) (ht : 0 ≤ t) (x d : Space)
    :
    (star (MagHK.CartesianOrbitals.orbitalZero t c x) *
      fderiv ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x d).im +
    (star (MagHK.CartesianOrbitals.orbitalMinus t c x) *
      fderiv ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x d).im +
      density t c x * fieldPairing t x d = 0 := by
  have hz := real_amplitude_current (amplitudeZero t c) x d
    (amplitudeZero_differentiable t c ht x)
  have hg := conjugate_amplitude_current (amplitudeMinus t c) x d
    (amplitudeMinus_differentiable t c ht x)
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

theorem wave_fderiv_apply (t c : ℝ) (ht : 0 ≤ t) (x y d : Space) :
    fderiv ℝ (fun z => wave t c z y) x d =
      MagHK.Slater.slaterSlice
        (fderiv ℝ (MagHK.CartesianOrbitals.orbitalZero t c) x d)
        (fderiv ℝ (MagHK.CartesianOrbitals.orbitalMinus t c) x d)
        (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c) y := by
  have hf := (orbitalZero_differentiable t c ht x).hasFDerivAt
  have hg := (orbitalMinus_differentiable t c ht x).hasFDerivAt
  have h := ((hf.mul_const (MagHK.CartesianOrbitals.orbitalMinus t c y)).sub
    (hg.mul_const (MagHK.CartesianOrbitals.orbitalZero t c y))).const_mul MagHK.Slater.scale
  change HasFDerivAt (fun z => MagHK.Slater.scale *
    (MagHK.CartesianOrbitals.orbitalZero t c z * MagHK.CartesianOrbitals.orbitalMinus t c y -
      MagHK.CartesianOrbitals.orbitalMinus t c z * MagHK.CartesianOrbitals.orbitalZero t c y)) _ x at h
  change fderiv ℝ (fun z => MagHK.Slater.scale *
    (MagHK.CartesianOrbitals.orbitalZero t c z * MagHK.CartesianOrbitals.orbitalMinus t c y -
      MagHK.CartesianOrbitals.orbitalMinus t c z * MagHK.CartesianOrbitals.orbitalZero t c y)) x d = _
  rw [h.fderiv]
  simp only [smul_apply, sub_apply,
    smul_eq_mul, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  ring

theorem physicalCurrent_zero (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c))
    (x d : Space) : physicalCurrent t c x d = 0 := by
  unfold physicalCurrent
  simp_rw [wave_fderiv_apply t c ht x _ d]
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
  exact orbital_current_cancels t c ht x d

theorem current_slice_integrable (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.CartesianOrbitals.orbitalZero t c) (MagHK.CartesianOrbitals.orbitalMinus t c)) (x d : Space) :
    Integrable (fun y => (star (wave t c x y) *
      fderiv ℝ (fun z => wave t c z y) x d).im) := by
  simp_rw [wave_fderiv_apply t c ht x _ d]
  exact (MagHK.Slater.integrable_slater_pairing volume _ _ h _ _ _ _).im

end MagHK.CurrentCompletion.Bounded

namespace MagHK.CurrentCompletion.Gaussian
open MagHK.GaussianSlater

theorem amplitudeZero_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (amplitudeZero t c) := by
  intro x
  have hf := (gaussian_radial_differentiable t ht).differentiableAt.comp x differentiableAt_fst
  have hc := (GaussianIntegrals.axialChi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  exact ((differentiableAt_const (GaussianOrbitals.normalization)).mul hf).mul hc

theorem amplitudeMinus_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (amplitudeMinus t c) := by
  intro x
  have hf := (gaussian_radial_differentiable t ht).differentiableAt.comp x differentiableAt_fst
  have hc := (GaussianIntegrals.axialChi_hasDerivAt c x.2).differentiableAt.comp x differentiableAt_snd
  exact ((differentiableAt_const (GaussianOrbitals.normalization * Real.sqrt t)).mul hf).mul hc

theorem orbitalZero_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (MagHK.GaussianOrbitals.orbitalZero t c) := by
  intro x
  exact Complex.ofRealCLM.differentiableAt.comp x (amplitudeZero_differentiable t c ht x)

theorem orbitalMinus_differentiable (t c : ℝ) (ht : 0 ≤ t) :
    Differentiable ℝ (MagHK.GaussianOrbitals.orbitalMinus t c) := by
  intro x
  exact (Complex.ofRealCLM.differentiableAt.comp x
    (amplitudeMinus_differentiable t c ht x)).mul
      (Complex.conjCLE.differentiableAt.comp x differentiableAt_fst)

open MagHK.ConcreteSlater (real_amplitude_current conjugate_amplitude_current)

theorem orbital_current_cancels (t c : ℝ) (ht : 0 ≤ t) (x d : Space)
    :
    (star (MagHK.GaussianOrbitals.orbitalZero t c x) *
      fderiv ℝ (MagHK.GaussianOrbitals.orbitalZero t c) x d).im +
    (star (MagHK.GaussianOrbitals.orbitalMinus t c x) *
      fderiv ℝ (MagHK.GaussianOrbitals.orbitalMinus t c) x d).im +
      density t c x * fieldPairing t x d = 0 := by
  have hz := real_amplitude_current (amplitudeZero t c) x d
    (amplitudeZero_differentiable t c ht x)
  have hg := conjugate_amplitude_current (amplitudeMinus t c) x d
    (amplitudeMinus_differentiable t c ht x)
  change (star (amplitudeZero t c x : ℂ) *
      fderiv ℝ (fun y => (amplitudeZero t c y : ℂ)) x d).im +
    (star ((amplitudeMinus t c x : ℂ) * conj x.1) *
      fderiv ℝ (fun y : Space => (amplitudeMinus t c y : ℂ) * conj y.1) x d).im +
      density t c x * fieldPairing t x d = 0
  rw [hz, hg]
  have hc := density_times_coefficient t c ht x
  unfold fieldPairing MagHK.ConstructionData.gaussian3Vector realCoordinates MagHK.Cartesian.gaussianVector
  dsimp
  calc
    _ = (amplitudeMinus t c x ^ 2 - density t c x *
        MagHK.Cartesian.gaussianCoefficient t (x.1.re, x.1.im)) *
        (x.1.im * d.1.re - x.1.re * d.1.im) := by ring
    _ = 0 := by rw [hc]; ring

theorem wave_fderiv_apply (t c : ℝ) (ht : 0 ≤ t) (x y d : Space) :
    fderiv ℝ (fun z => wave t c z y) x d =
      MagHK.Slater.slaterSlice
        (fderiv ℝ (MagHK.GaussianOrbitals.orbitalZero t c) x d)
        (fderiv ℝ (MagHK.GaussianOrbitals.orbitalMinus t c) x d)
        (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c) y := by
  have hf := (orbitalZero_differentiable t c ht x).hasFDerivAt
  have hg := (orbitalMinus_differentiable t c ht x).hasFDerivAt
  have h := ((hf.mul_const (MagHK.GaussianOrbitals.orbitalMinus t c y)).sub
    (hg.mul_const (MagHK.GaussianOrbitals.orbitalZero t c y))).const_mul MagHK.Slater.scale
  change HasFDerivAt (fun z => MagHK.Slater.scale *
    (MagHK.GaussianOrbitals.orbitalZero t c z * MagHK.GaussianOrbitals.orbitalMinus t c y -
      MagHK.GaussianOrbitals.orbitalMinus t c z * MagHK.GaussianOrbitals.orbitalZero t c y)) _ x at h
  change fderiv ℝ (fun z => MagHK.Slater.scale *
    (MagHK.GaussianOrbitals.orbitalZero t c z * MagHK.GaussianOrbitals.orbitalMinus t c y -
      MagHK.GaussianOrbitals.orbitalMinus t c z * MagHK.GaussianOrbitals.orbitalZero t c y)) x d = _
  rw [h.fderiv]
  simp only [smul_apply, sub_apply,
    smul_eq_mul, MagHK.Slater.slaterSlice, MagHK.Slater.determinantSlice]
  ring

theorem physicalCurrent_zero (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c))
    (x d : Space) : physicalCurrent t c x d = 0 := by
  unfold physicalCurrent
  simp_rw [wave_fderiv_apply t c ht x _ d]
  rw [wave_density_marginal t c h x]
  have hm := MagHK.Slater.slater_current_marginal volume
    (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c) h
    (MagHK.GaussianOrbitals.orbitalZero t c x) (MagHK.GaussianOrbitals.orbitalMinus t c x)
    (fderiv ℝ (MagHK.GaussianOrbitals.orbitalZero t c) x d)
    (fderiv ℝ (MagHK.GaussianOrbitals.orbitalMinus t c) x d)
  change 2 * (∫ y, (star (MagHK.Slater.slaterSlice
    (MagHK.GaussianOrbitals.orbitalZero t c x) (MagHK.GaussianOrbitals.orbitalMinus t c x)
    (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c) y) * _).im) + _ = 0
  rw [hm]
  exact orbital_current_cancels t c ht x d

theorem current_slice_integrable (t c : ℝ) (ht : 0 ≤ t)
    (h : MagHK.Slater.OrthonormalPair volume
      (MagHK.GaussianOrbitals.orbitalZero t c) (MagHK.GaussianOrbitals.orbitalMinus t c)) (x d : Space) :
    Integrable (fun y => (star (wave t c x y) *
      fderiv ℝ (fun z => wave t c z y) x d).im) := by
  simp_rw [wave_fderiv_apply t c ht x _ d]
  exact (MagHK.Slater.integrable_slater_pairing volume _ _ h _ _ _ _).im

end MagHK.CurrentCompletion.Gaussian

namespace MagHK.CurrentCompletion
open MagHK.ManyBodyTimeReversal
open MagHK.GeneralGauge

/-- The displayed marginal current is an actual integral for almost every
spatial point. This is weaker than globally square-integrable momentum. -/
def CurrentSlices (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) : Prop :=
  ∀ᵐ x : Point, ∀ k, Integrable (fun y : Configuration N =>
    (conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)).re)

theorem currentSlices_conjugate (N : ℕ) (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) (h : CurrentSlices N f p) :
    CurrentSlices N (fun x => conj (f x)) (fun i k x => -conj (p i k x)) := by
  filter_upwards [h] with x hx
  intro k
  have he : (fun y : Configuration N =>
      (conj (conj (f (Fin.cons x y))) * -conj (p 0 k (Fin.cons x y))).re) =
      fun y => -(conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)).re := by
    funext y
    simp [Complex.mul_re]
  rw [he]
  exact (hx k).neg

theorem currentSlices_gauge (N : ℕ) (η : Point → ℝ)
    (f : Configuration (N + 1) → ℂ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ) (h : CurrentSlices N f p) :
    CurrentSlices N (wave (N + 1) η f) (fun i k => wave (N + 1) η (p i k)) := by
  filter_upwards [h] with x hx
  intro k
  have he (y : Configuration N) :
      conj (wave (N + 1) η f (Fin.cons x y)) * wave (N + 1) η (p 0 k) (Fin.cons x y) =
        conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y) := by
    dsimp only [wave]
    rw [map_mul]
    calc
      _ = (conj (phase (N + 1) η (Fin.cons x y)) * phase (N + 1) η (Fin.cons x y)) *
          (conj (f (Fin.cons x y)) * p 0 k (Fin.cons x y)) := by ring
      _ = _ := by rw [phase_conj_mul, one_mul]
  simpa only [he] using hx k

/-- Time reversal for every actual weak current with integrable marginal
slices. No global kinetic regularity is presumed from total-form semiboundedness. -/
theorem time_reversal_wellDefined
    (forms : StandardClosedFormLibrary) (spectral : StandardAntiunitaryLibrary)
    (N : ℕ) (H : System (N + 1)) (A : Point → Point)
    (V : Configuration (N + 1) → ℝ) (b E : ℝ)
    (hH : Facts (N + 1) H A V b) (ψ : State (N + 1)) (hψ : GroundState (N + 1) H E ψ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ)
    (hw : WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p)
    (hs : CurrentSlices N (ψ : FullState (N + 1)) p) :
    Facts (N + 1) (reverseOperator (N + 1) H) (-A) V b ∧
    GroundState (N + 1) (reverseOperator (N + 1) H) E (conjugation (N + 1) ψ) ∧
    WeakMomentum (N + 1) (-A) (fun x => conj ((ψ : FullState (N + 1)) x))
      (fun i k x => -conj (p i k x)) ∧
    CurrentSlices N (fun x => conj ((ψ : FullState (N + 1)) x))
      (fun i k x => -conj (p i k x)) ∧
    density N (fun x => conj ((ψ : FullState (N + 1)) x)) = density N (ψ : FullState (N + 1)) ∧
    weakCurrent N (fun x => conj ((ψ : FullState (N + 1)) x)) (fun i k x => -conj (p i k x)) =
      -weakCurrent N (ψ : FullState (N + 1)) p := by
  obtain ⟨hF, hg, _⟩ := time_reversal forms spectral (N + 1) H A V b E hH ψ hψ
  exact ⟨hF, hg, weakMomentum_conjugate _ _ _ _ hw,
    currentSlices_conjugate _ _ _ hs, density_conjugate _ _, weakCurrent_conjugate _ _ _⟩

/-- Smooth gauge transport with the same minimal well-posedness requirement. -/
theorem gauge_wellDefined
    (multipliers : StandardPhaseMultiplierLibrary) (transport : StandardUnitaryFormLibrary)
    (N : ℕ) (η : Point → ℝ) (hη : ContDiff ℝ ∞ η)
    (H : System (N + 1)) (A : Point → Point) (V : Configuration (N + 1) → ℝ) (b E : ℝ)
    (hH : Facts (N + 1) H A V b) (ψ : State (N + 1)) (hψ : GroundState (N + 1) H E ψ)
    (p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ)
    (hw : WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p)
    (hs : CurrentSlices N (ψ : FullState (N + 1)) p) :
    ∃ U : PhaseUnitary (N + 1) η,
      Facts (N + 1) (gaugeOperator (N + 1) U.map H) (A + gradient η) V b ∧
      GroundState (N + 1) (gaugeOperator (N + 1) U.map H) E (U.map ψ) ∧
      WeakMomentum (N + 1) (A + gradient η) (wave (N + 1) η (ψ : FullState (N + 1)))
        (fun i k => wave (N + 1) η (p i k)) ∧
      CurrentSlices N (wave (N + 1) η (ψ : FullState (N + 1)))
        (fun i k => wave (N + 1) η (p i k)) ∧
      density N (wave (N + 1) η (ψ : FullState (N + 1))) = density N (ψ : FullState (N + 1)) ∧
      weakCurrent N (wave (N + 1) η (ψ : FullState (N + 1)))
        (fun i k => wave (N + 1) η (p i k)) = weakCurrent N (ψ : FullState (N + 1)) p := by
  obtain ⟨U, hU, he, hm⟩ := gauge_realization multipliers transport (N + 1) η hη H A V b hH
  have hg : GroundState (N + 1) (gaugeOperator (N + 1) U.map H) E (U.map ψ) := by
    refine ⟨gauge_eigen (N + 1) U.map H E ψ hψ.1, ?_, ?_⟩
    · simpa only [he] using hψ.2.1
    · simpa only [hm] using hψ.2.2
  exact ⟨U, hU, hg, weakMomentum_gauge _ η hη A _ p hw,
    currentSlices_gauge _ η _ p hs, density_gauge _ η _, weakCurrent_gauge _ η _ p⟩

end MagHK.CurrentCompletion

namespace MagHK.FermionRealization
open MeasureTheory Set
open MagHK.Ordering MagHK.TensorRealization
open scoped ContDiff ComplexConjugate
theorem bounded_ground_state_pointwise
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : AxialRealization.StandardAxialLibrary)
    (tensor : StandardTensorLibrary) (fermion : StandardFermionLibrary)
    (c : ℝ) (hc : 0 < c) (hgap : 20 < c ^ 2) :
    ∃ t : ℝ, 0 < t ∧ ∃ T : TensorRealization.System, ∃ F : System,
      OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential c) ∧
      (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 20 ↔ E = 0 ∨ E = 20) ∧
      OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 20 = 1 ∧
      Facts F (Cartesian.boundedVector t) (Cartesian.boundedScalar t) (Axial.potential c) ∧
      GroundState F 20 (fun p => ConcreteSlater.wave t c p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (ConcreteSlater.wave t c p.1 p.2)) = 1 ∧
      (∀ x, 0 < 2 * ∫ y, Complex.normSq (ConcreteSlater.wave t c x y)) ∧
      (∀ x d : Space, ConcreteSlater.physicalCurrent t c x d = 0) := by
  obtain ⟨t, ht, heq, _⟩ := MagHK.Noninteracting.exists_bounded_parameter
  obtain ⟨P, hP, hlevels, hp0, hp20, hpgap⟩ :=
    PlanarSpectralLibrary.bounded_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := AxialRealization.bounded_axial_realization axial c hc
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (PlanarSpectralLibrary.bounded_planar_coefficients t ht)
    (AxialRealization.bounded_coefficients c).V_smooth hP hZ
    (spectrum_nonnegative P.spectrum hlevels) hZ.nonnegative
  have h1 : OneBodyRealization T (Cartesian.boundedVector t) (Cartesian.boundedScalar t)
      (Axial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm20, htg⟩ := bounded_tensor_levels T P Z _ _ _ hT c hgap
    hlevels hp0 hp20 hpgap hz0 hzm hzgap
  have hzero := bounded_zero_eigenfunction t c ht hc P Z T hP hz hT
  have hminus := bounded_minus_eigenfunction t c ht hc P Z T hP hz hT
  have ho := CartesianOrbitals.bounded_orthonormal t c ht hc heq
  obtain ⟨F, hF, hg⟩ := fermion T _ _ _ h1 0 20 _ _ (by norm_num)
    hle hm0 hm20 htg hzero hminus ho
  refine ⟨t, ht, T, F, h1, hle, hm0, hm20, hF, ?_,
    ConcreteSlater.wave_normalized t c ht.le ho, ?_,
    MagHK.CurrentCompletion.Bounded.physicalCurrent_zero t c ht.le ho⟩
  · simpa only [zero_add] using! hg
  · intro x
    rw [ConcreteSlater.wave_density_marginal t c ho x]
    exact ConcreteSlater.density_pos t c ht.le hc x


end MagHK.FermionRealization

namespace MagHK.GaussianFermion
open MeasureTheory Set
open MagHK.Noninteracting MagHK.RadialEndpoints MagHK.Cartesian
open MagHK.GaussianIntegrals MagHK.GaussianDomains MagHK.GaussianRealization
open MagHK.TensorRealization
open scoped ContDiff ComplexConjugate
theorem gaussian_ground_state_pointwise
    (planar : PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : GaussianAxial.StandardOscillatorLibrary)
    (tensor : StandardTensorLibrary) (fermion : FermionRealization.StandardFermionLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, 0 < t ∧ ∃ T : System, ∃ F : FermionRealization.System,
      FermionRealization.OneBodyRealization T (gaussianVector t) (gaussianScalar t)
        (GaussianAxial.potential c) ∧
      (∀ E, E ∈ OperatorModel.spectrum T ∧ E ≤ 2 ↔ E = 0 ∨ E = 2) ∧
      OperatorModel.multiplicity T 0 = 1 ∧ OperatorModel.multiplicity T 2 = 1 ∧
      FermionRealization.Facts F (gaussianVector t) (gaussianScalar t) (GaussianAxial.potential c) ∧
      FermionRealization.GroundState F 2 (fun p => GaussianSlater.wave t c p.1 p.2) ∧
      (∫ p : Space × Space, Complex.normSq (GaussianSlater.wave t c p.1 p.2)) = 1 ∧
      (∀ x, 2 * ∫ y, Complex.normSq (GaussianSlater.wave t c x y) =
        (2 / Real.pi) * Real.sqrt (c / Real.pi) * Real.exp (-‖x.1‖ ^ 2 - c * x.2 ^ 2)) ∧
      (∀ x d : Space, GaussianSlater.physicalCurrent t c x d = 0) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨t, ht, hn0, hn1⟩ := exists_gaussian_equal_norms
  obtain ⟨P, hP, hlevels, hp0, hp2, hpgap⟩ :=
    GaussianPlanar.gaussian_planar_realization planar t ht
  obtain ⟨Z, hZ, hz, hz0, hzm, hzgap⟩ := GaussianAxial.gaussian_axial_realization axial c hc0
  have hpnon : ∀ E ∈ P.spectrum, 0 ≤ E := by
    intro E hE
    by_cases he : E ≤ 2
    · rcases (hlevels E).mp ⟨hE, he⟩ with rfl | rfl <;> norm_num
    · linarith
  obtain ⟨T, hT⟩ := tensor P Z _ _ _ _ _ _ _
    (GaussianPlanar.gaussian_planar_coefficients t ht.le) (GaussianAxial.potential_smooth c)
    hP hZ hpnon hZ.nonnegative
  have h1 : FermionRealization.OneBodyRealization T (gaussianVector t) (gaussianScalar t)
      (GaussianAxial.potential c) := ⟨hT.selfadjoint, hT.test_action, hT.weak_equation⟩
  obtain ⟨hle, hm0, hm2, htg⟩ := tensor_levels T P Z _ _ _ hT 2 (2 * c)
    (by norm_num) (by linarith) hlevels hp0 hp2 hpgap hz0 hzm hzgap
  have hzero := gaussian_zero_eigenfunction t c ht hc0 P Z T hP hz hT
  have hminus := gaussian_minus_eigenfunction t c ht hc0 P Z T hP hz hT
  have ho := GaussianOrbitals.gaussian_orthonormal t c ht hc0 hn0 hn1
  obtain ⟨F, hF, hg⟩ := fermion T _ _ _ h1 0 2 _ _ (by norm_num)
    hle hm0 hm2 htg hzero hminus ho
  refine ⟨t, ht, T, F, h1, hle, hm0, hm2, hF, ?_,
    GaussianSlater.wave_normalized t c ht.le ho, ?_,
    MagHK.CurrentCompletion.Gaussian.physicalCurrent_zero t c ht.le ho⟩
  · simpa only [zero_add] using! hg
  · intro x
    rw [GaussianSlater.wave_density_marginal t c ho x, gaussian_density t c ht.le x]


end MagHK.GaussianFermion

namespace MagHK.CurrentCompletion
open MagHK.NoninteractingTheorem MagHK.CounterexamplePair MagHK.PotentialSpaces MagHK.ConstructionData

theorem bounded_counterexample_pointwise
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.AxialRealization.StandardAxialLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (fermion : MagHK.FermionRealization.StandardFermionLibrary)
    (reversal : MagHK.OperatorTimeReversal.StandardAntiunitaryLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary) :
    ∃ t : ℝ, BoundedResult t ∧ ∀ x d : Space,
      current (MagHK.Cartesian.boundedVector t) (fun p => MagHK.ConcreteSlater.wave t 5 p.1 p.2) x d = 0 ∧
      current (-MagHK.Cartesian.boundedVector t)
        (fun p => conj (MagHK.ConcreteSlater.wave t 5 p.1 p.2)) x d = 0 := by
  obtain ⟨t, ht, T, F, _, _, _, _, hF, hg, hn, hρ, hj⟩ :=
    MagHK.FermionRealization.bounded_ground_state_pointwise planar axial tensor fermion
      5 (by norm_num) (by norm_num)
  have hjp (x d : Space) : current (MagHK.Cartesian.boundedVector t)
      (fun p => MagHK.ConcreteSlater.wave t 5 p.1 p.2) x d = 0 := by
    rw [bounded_current_eq]
    exact hj x d
  have pair := paired_ground_states reversal F _ _ _ _ _ hF hg hn hρ
    (Eventually.of_forall hjp) (bounded_opposite_not_gauge t ht)
  obtain ⟨hVs, hAs⟩ := bounded_sum_spaces t 5 ht
  have hAb := bounded_vector_memLp t ht.le
  refine ⟨t, ⟨ht, bounded3Vector_smooth t ht.le, (bounded3Vector_smooth t ht.le).neg,
    bounded3Scalar_smooth t 5 ht.le, bounded_scalar_memLp t 5 ht, hAb, hAb.neg,
    hVs, hAs, ⟨0, -bounded3Vector t, MemLp.zero, hAb.neg, fun x => by simp⟩,
    MagHK.Cartesian.bounded_curl_nonzero t ht, pair,
    MagHK.WeakGauge.bounded_opposite_not_weak_gauge regularity t ht⟩, fun x d => ?_⟩
  exact ⟨hjp x d, by rw [current_conjugate, hjp x d, neg_zero]⟩

theorem gaussian_counterexample_pointwise
    (planar : MagHK.PlanarSpectralLibrary.StandardPlanarLibrary)
    (axial : MagHK.GaussianAxial.StandardOscillatorLibrary)
    (tensor : MagHK.TensorRealization.StandardTensorLibrary)
    (fermion : MagHK.FermionRealization.StandardFermionLibrary)
    (reversal : MagHK.OperatorTimeReversal.StandardAntiunitaryLibrary)
    (compactness : MagHK.GaussianCompactness.StandardConfiningLibrary)
    (regularity : MagHK.WeakGauge.StandardGradientRegularityLibrary)
    (c : ℝ) (hc : 1 < c) :
    ∃ t : ℝ, GaussianResult t c ∧ ∀ x d : Space,
      current (MagHK.Cartesian.gaussianVector t) (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) x d = 0 ∧
      current (-MagHK.Cartesian.gaussianVector t)
        (fun p => conj (MagHK.GaussianSlater.wave t c p.1 p.2)) x d = 0 := by
  obtain ⟨t, ht, T, F, _, _, _, _, hF, hg, hn, hρ, hj⟩ :=
    MagHK.GaussianFermion.gaussian_ground_state_pointwise planar axial tensor fermion c hc
  have hjp (x d : Space) : current (MagHK.Cartesian.gaussianVector t)
      (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) x d = 0 := by
    rw [gaussian_current_eq]
    exact hj x d
  have hpos (x : Space) : 0 < density (fun p => MagHK.GaussianSlater.wave t c p.1 p.2) x := by
    change 0 < 2 * ∫ y, Complex.normSq (MagHK.GaussianSlater.wave t c x y)
    rw [hρ x]
    have hc0 : 0 < c := by linarith
    positivity
  have pair := paired_ground_states reversal F _ _ _ _ _ hF hg hn hpos
    (Eventually.of_forall hjp) (gaussian_opposite_not_gauge t ht)
  have hAb := gaussian_vector_memLp t ht.le
  refine ⟨t, ⟨ht, gaussian3Vector_smooth t ht.le, (gaussian3Vector_smooth t ht.le).neg,
    gaussian3Scalar_smooth t c ht.le, hAb, hAb.neg,
    MagHK.GaussianOutside.gaussian_scalar_outside t c ht.le hc,
    MagHK.Cartesian.gaussian_curl_nonzero t ht,
    MagHK.GaussianCompactness.gaussian_pair_compact compactness t c 2 ht.le hc _ pair, hρ,
    MagHK.WeakGauge.gaussian_opposite_not_weak_gauge regularity t ht⟩, fun x d => ?_⟩
  exact ⟨hjp x d, by rw [current_conjugate, hjp x d, neg_zero]⟩

end MagHK.CurrentCompletion

namespace MagHK.CurrentCompletion
open MagHK.ManyBodyTimeReversal
open scoped Topology

abbrev MomentumState (N : ℕ) := Fin N → Fin 3 → FullState N

def MomentumGraph (N : ℕ) (A : Point → Point) : Set (FullState N × MomentumState N) :=
  {z | WeakMomentum N A z.1 (fun i k => z.2 i k)}

/-- Actual core representatives and their literal magnetic derivatives. -/
def CoreMomenta (N : ℕ) (A : Point → Point) (f : Configuration N → ℂ)
    (u : FullState N) (p : MomentumState N) : Prop :=
  (u : Configuration N → ℂ) =ᵐ[volume] f ∧
    ∀ i k, (p i k : Configuration N → ℂ) =ᵐ[volume] momentum N A f i k

/-- Standard first-order magnetic Sobolev graph theorem, for arbitrary smooth
coefficients and arbitrary L² vectors. The graph is defined by the literal
distributional integration-by-parts identity, not by a chosen eigenstate. -/
structure StandardMagneticGraphLibrary : Prop where
  closed : ∀ N A, ContDiff ℝ ∞ A → IsClosed (MomentumGraph N A)
  core : ∀ N A, ContDiff ℝ ∞ A → ∀ f, Core N f → ∀ u : FullState N,
    (u : Configuration N → ℂ) =ᵐ[volume] f →
    ∃ p : MomentumState N, CoreMomenta N A f u p ∧ (u, p) ∈ MomentumGraph N A

/-- A precise kinetic-control hypothesis on the actual form core. The finite
product L² norm is equivalent to the sum of kinetic energies. Adding the L²
term permits any semibounded form shift that controls the magnetic kinetic
form. Semiboundedness without this estimate is deliberately insufficient. -/
def KineticControl (N : ℕ) (A : Point → Point) (V : Configuration N → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f g, Core N f → Core N g →
    ∀ (u v : FullState N) (p q : MomentumState N),
      CoreMomenta N A f u p → CoreMomenta N A g v q →
      ‖p - q‖ ^ 2 ≤ C * ((form N A V (f - g) (f - g)).re + ‖u - v‖ ^ 2)

/-- Form-norm approximation and kinetic control produce an actual L² weak
momentum. The limit is proved using completeness and the closed magnetic graph. -/
theorem form_approximation_momentum (library : StandardMagneticGraphLibrary)
    (N : ℕ) (A : Point → Point) (hA : ContDiff ℝ ∞ A)
    (V : Configuration N → ℝ) (hkin : KineticControl N A V)
    (ψ : FullState N) (f : ℕ → Configuration N → ℂ) (u : ℕ → FullState N)
    (ha : MagHK.MonopoleRealization.FormApproximation volume (Core N) (form N A V) ψ f u) :
    ∃ p : MomentumState N, WeakMomentum N A ψ (fun i k => p i k) := by
  classical
  obtain ⟨hcore, hre, hu, hq⟩ := ha
  choose p hp hg using fun n => library.core N A hA (f n) (hcore n) (u n) (hre n)
  obtain ⟨C, hC, hbound⟩ := hkin
  have hpc : CauchySeq p := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ : ℝ := ε ^ 2 / (2 * C)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨nq, hnq⟩ := hq δ hδ
    obtain ⟨nu, hnu⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq (Real.sqrt δ) (Real.sqrt_pos.mpr hδ)
    refine ⟨max nq nu, fun n hn m hm => ?_⟩
    have hqu := hnq n (le_trans (le_max_left _ _) hn) m (le_trans (le_max_left _ _) hm)
    have huu := hnu n (le_trans (le_max_right _ _) hn) m (le_trans (le_max_right _ _) hm)
    rw [dist_eq_norm] at huu ⊢
    have huu2 : ‖u n - u m‖ ^ 2 < δ := by
      nlinarith [Real.sq_sqrt hδ.le, norm_nonneg (u n - u m), Real.sqrt_nonneg δ]
    have hb := hbound (f n) (f m) (hcore n) (hcore m) (u n) (u m) (p n) (p m) (hp n) (hp m)
    have hsum : (form N A V (f n - f m) (f n - f m)).re + ‖u n - u m‖ ^ 2 < 2 * δ := by
      linarith
    have hstrict := lt_of_le_of_lt hb (mul_lt_mul_of_pos_left hsum hC)
    have hδid : C * (2 * δ) = ε ^ 2 := by dsimp [δ]; field_simp
    rw [hδid] at hstrict
    nlinarith [norm_nonneg (p n - p m)]
  obtain ⟨p₀, hp₀⟩ := cauchySeq_tendsto_of_complete hpc
  have hclosed := library.closed N A hA
  exact ⟨p₀, hclosed.mem_of_tendsto (hu.prodMk_nhds hp₀) (Eventually.of_forall hg)⟩

/-- The bridge starts at the actual operator domain in Facts, using its
Friedrichs graph characterization. It applies to every domain vector. -/
theorem operator_domain_momentum (library : StandardMagneticGraphLibrary)
    (N : ℕ) (H : System N) (A : Point → Point) (V : Configuration N → ℝ) (b : ℝ)
    (hH : Facts N H A V b) (hA : ContDiff ℝ ∞ A)
    (hkin : KineticControl N A (fun x => V x + b))
    (ψ : State N) (hψ : ψ ∈ H.domain) :
    ∃ p : MomentumState N, WeakMomentum N A (ψ : FullState N) (fun i k => p i k) := by
  obtain ⟨f, u, ha, _⟩ := (hH.2.2.2 ψ (H.map ⟨ψ, hψ⟩)).mp ⟨hψ, rfl⟩
  exact form_approximation_momentum library N A hA _ hkin _ f u ha

/-- Fubini and the L² product estimate discharge current-slice integrability
for every state with square-integrable magnetic momentum. -/
theorem currentSlices_lp (N : ℕ) (ψ : FullState (N + 1)) (p : MomentumState (N + 1)) :
    CurrentSlices N ψ (fun i k => p i k) := by
  apply (ae_all_iff).mpr
  intro k
  have hi : Integrable (fun x => (conj (ψ x) * p 0 k x).re) := by
    simpa only [RCLike.inner_apply'] using! (L2.integrable_inner (𝕜 := ℂ) ψ (p 0 k)).re
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => Point) 0).symm
  have hj := hm.integrable_comp_of_integrable hi
  have he : (fun x : Point × Configuration N =>
      (conj (ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Point) 0).symm x)) *
        p 0 k ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Point) 0).symm x)).re) =
      fun x => (conj (ψ (Fin.cons x.1 x.2)) * p 0 k (Fin.cons x.1 x.2)).re := by
    funext x
    congr 4 <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
  change Integrable _ (volume : Measure (Point × Configuration N)) at hj
  simp only [Function.comp_def] at hj
  rw [he] at hj
  exact hj.prod_right_ae

/-- Every eigenstate in the kinetic-controlled regime has the well-defined
weak current needed by the general time-reversal and gauge theorems above. -/
theorem domain_has_wellDefined_current (library : StandardMagneticGraphLibrary)
    (N : ℕ) (H : System (N + 1)) (A : Point → Point)
    (V : Configuration (N + 1) → ℝ) (b : ℝ)
    (hH : Facts (N + 1) H A V b) (hA : ContDiff ℝ ∞ A)
    (hkin : KineticControl (N + 1) A (fun x => V x + b))
    (ψ : State (N + 1)) (hψ : ψ ∈ H.domain) :
    ∃ p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ,
      (∀ i k, MemLp (p i k) 2) ∧ WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p ∧
      CurrentSlices N (ψ : FullState (N + 1)) p := by
  obtain ⟨p, hp⟩ := operator_domain_momentum library (N + 1) H A V b hH hA hkin ψ hψ
  exact ⟨fun i k => p i k, fun i k => Lp.memLp (p i k), hp, currentSlices_lp N _ p⟩

end MagHK.CurrentCompletion

namespace MagHK.CurrentCompletion
open MagHK.ManyBodyTimeReversal

/-- Complete time-reversal assembly in the kinetic-controlled form regime.
The current data are obtained from the operator domain, rather than supplied
as an eigenstate-specific hypothesis. -/
theorem time_reversal_from_kinetic
    (graphs : StandardMagneticGraphLibrary)
    (forms : StandardClosedFormLibrary) (spectral : StandardAntiunitaryLibrary)
    (N : ℕ) (H : System (N + 1)) (A : Point → Point)
    (V : Configuration (N + 1) → ℝ) (b E : ℝ)
    (hH : Facts (N + 1) H A V b) (hA : ContDiff ℝ ∞ A)
    (hkin : KineticControl (N + 1) A (fun x => V x + b))
    (ψ : State (N + 1)) (hψ : GroundState (N + 1) H E ψ) :
    ∃ p : Fin (N + 1) → Fin 3 → Configuration (N + 1) → ℂ,
      (∀ i k, MemLp (p i k) 2) ∧ WeakMomentum (N + 1) A (ψ : FullState (N + 1)) p ∧
      CurrentSlices N (ψ : FullState (N + 1)) p ∧
      Facts (N + 1) (reverseOperator (N + 1) H) (-A) V b ∧
      GroundState (N + 1) (reverseOperator (N + 1) H) E (conjugation (N + 1) ψ) ∧
      WeakMomentum (N + 1) (-A) (fun x => conj ((ψ : FullState (N + 1)) x))
        (fun i k x => -conj (p i k x)) ∧
      CurrentSlices N (fun x => conj ((ψ : FullState (N + 1)) x))
        (fun i k x => -conj (p i k x)) ∧
      density N (fun x => conj ((ψ : FullState (N + 1)) x)) = density N (ψ : FullState (N + 1)) ∧
      weakCurrent N (fun x => conj ((ψ : FullState (N + 1)) x)) (fun i k x => -conj (p i k x)) =
        -weakCurrent N (ψ : FullState (N + 1)) p := by
  obtain ⟨p, hp, hw, hs⟩ := domain_has_wellDefined_current graphs N H A V b hH hA hkin ψ hψ.1.1
  exact ⟨p, hp, hw, hs, time_reversal_wellDefined forms spectral N H A V b E hH ψ hψ p hw hs⟩

end MagHK.CurrentCompletion
